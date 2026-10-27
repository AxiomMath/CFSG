module

public import CFSG.Quasithin.Background.B2FactorizationBridge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Quasithin CFSG.Open

section Act

variable {G : Type} [Group G] {V : Subgroup G} [V.Normal] (hV : IsElemAbelian 2 V)

theorem mem_normalizer_of_normal (g : G) : g ∈ Subgroup.normalizer (V : Set G) := by
  rw [Subgroup.normalizer_eq_top]
  exact Subgroup.mem_top g

@[expose] noncomputable def actHom : G →* MulAut (IntMod V hV) where
  toFun g := convI hV ⟨g, mem_normalizer_of_normal g⟩
  map_one' := (convI hV).map_one
  map_mul' a b := (convI hV).map_mul ⟨a, mem_normalizer_of_normal a⟩ ⟨b, mem_normalizer_of_normal b⟩

theorem actHom_apply_val (g : G) (v : IntMod V hV) : (actHom hV g v).val = g * v.val * g⁻¹ :=
  convI_apply_val hV ⟨g, mem_normalizer_of_normal g⟩ v

theorem actHom_eq_one_iff (g : G) : actHom hV g = 1 ↔ g ∈ Subgroup.centralizer (V : Set G) :=
  convI_eq_one_iff hV ⟨g, mem_normalizer_of_normal g⟩

theorem ker_actHom : (actHom hV).ker = Subgroup.centralizer (V : Set G) := by
  ext g
  rw [MonoidHom.mem_ker, actHom_eq_one_iff]

theorem actHom_mem_autI (g : G) : actHom hV g ∈ autI hV (⊤ : Subgroup G) :=
  convI_mem_autI hV (Subgroup.mem_top g) (mem_normalizer_of_normal g)

theorem exists_actHom_eq {a : MulAut (IntMod V hV)} (ha : a ∈ autI hV (⊤ : Subgroup G)) :
    ∃ g : G, actHom hV g = a := by
  obtain ⟨g, -, rfl⟩ := (mem_autI hV).1 ha
  exact ⟨g, rfl⟩

@[expose] noncomputable def actA : G →* ↥(autI hV (⊤ : Subgroup G)) :=
  (actHom hV).codRestrict (autI hV (⊤ : Subgroup G)) (actHom_mem_autI hV)

theorem coe_actA (g : G) : ((actA hV g : ↥(autI hV (⊤ : Subgroup G))) : MulAut (IntMod V hV)) = actHom hV g :=
  rfl

theorem actA_surjective : Function.Surjective (actA hV) := by
  intro a
  obtain ⟨g, hg⟩ := exists_actHom_eq hV a.2
  exact ⟨g, Subtype.ext hg⟩

theorem ker_actA : (actA hV).ker = Subgroup.centralizer (V : Set G) := by
  rw [← ker_actHom hV]
  ext g
  simp only [MonoidHom.mem_ker]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

end Act

end CFSG.LocalAnalysis.UniquenessCase.UC22
