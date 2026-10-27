module

public import CFSG.LocalAnalysis.UniquenessCase.UCFrontExt

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K148

open CFSG.Open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) G V}

@[expose] def subRep (ρ : Representation (ZMod 2) G V) (W : Submodule (ZMod 2) V)
    (hW : ∀ g : G, ∀ w ∈ W, ρ g w ∈ W) : Representation (ZMod 2) G ↥W where
  toFun g := (ρ g).restrict (hW g)
  map_one' := by ext w; simp
  map_mul' g h := by ext w; simp

variable {W : Submodule (ZMod 2) V} (hW : ∀ g : G, ∀ w ∈ W, ρ g w ∈ W)

namespace SubAux

theorem isElemAbelianOn_of_isElemAbelian {A : Subgroup G} (hA : IsElemAbelian 2 A)
    (U : Submodule (ZMod 2) V) : IsElemAbelianOn ρ A U := by
  intro a ha b hb
  have hc : a * b = b * a := congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have h1 : a * b * a⁻¹ * b⁻¹ = 1 := by rw [hc]; group
  have h2 : a * a = 1 := by rw [← pow_two]; exact hA.2 a ha
  exact ⟨fun u _ => by rw [h1, map_one, Module.End.one_apply],
    fun u _ => by rw [h2, map_one, Module.End.one_apply]⟩

end SubAux

theorem map_fixSub_subRep (X : Subgroup G) :
    (fixSub (subRep ρ W hW) X).map W.subtype = fixOn ρ X W := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.2, mem_fixSub.2 fun a ha => congrArg Subtype.val (hw a ha)⟩
  · rintro ⟨hv, h⟩
    exact ⟨⟨v, hv⟩, mem_fixSub.2 fun a ha => Subtype.ext (h a ha), rfl⟩

theorem card_fixSub_subRep (X : Subgroup G) :
    Nat.card ↥(fixSub (subRep ρ W hW) X) = Nat.card ↥(fixOn ρ X W) := by
  rw [← map_fixSub_subRep hW X]
  exact Nat.card_congr (Submodule.equivMapOfInjective _ W.injective_subtype _).toEquiv

theorem mem_calP_subRep_iff (A : Subgroup G) :
    A ∈ calP (subRep ρ W hW) ↔ A ≠ ⊥ ∧ IsElemAbelian 2 A ∧ IsBestOffenderOn ρ A W := by
  simp only [calP, Set.mem_setOf_eq, IsBestOffender, IsBestOffenderOn, card_fixSub_subRep hW]
  exact and_congr_right fun _ =>
    ⟨fun ⟨hE, h⟩ => ⟨hE, SubAux.isElemAbelianOn_of_isElemAbelian hE W, h⟩,
      fun ⟨hE, _, h⟩ => ⟨hE, h⟩⟩

theorem injective_subRep_iff :
    Function.Injective (subRep ρ W hW) ↔ ∀ g : G, (∀ w ∈ W, ρ g w = w) → g = 1 := by
  rw [injective_iff_map_eq_one]
  refine forall_congr' fun g => imp_congr_left ⟨fun h w hw => ?_, fun h => ?_⟩
  · exact congrArg Subtype.val (LinearMap.congr_fun h ⟨w, hw⟩)
  · exact LinearMap.ext fun w => Subtype.ext (h w w.2)

end CFSG.LocalAnalysis.UniquenessCase.UC22.K148
