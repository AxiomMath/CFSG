module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.ParabolicCover
import CFSG.Adapters.LieModelSimple
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.Lie.GL32
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGroupFactsL2Seven
public import CFSG.Quasithin.Background.B6Sections

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsLThreeTwo)

@[expose] def GenSeven (Q : Type) [Group Q] (X : Subgroup Q) : Prop :=
  ∀ W : Subgroup Q, X ≤ W →
    (∀ D : Subgroup Q, D ≤ X → Nat.card D = 3 → normalizer (D : Set Q) ≤ W) →
    (∀ A : Subgroup Q, A ≤ X → Nat.card A = 7 → ∀ x ∈ centralizer (A : Set Q),
      Nat.Coprime (orderOf x) 7 → x ∈ W) →
    W = ⊤

theorem GenSeven.map_equiv {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q') {X : Subgroup Q}
    (h : GenSeven Q X) : GenSeven Q' (X.map e.toMonoidHom) := by
  intro W' hXW' hD' hA'
  have hW : W'.comap e.toMonoidHom = ⊤ := by
    refine h _ (fun x hx => hXW' ⟨x, hx, rfl⟩) (fun D hDX hD n hn => ?_)
      (fun A hAX hA x hx hxo => ?_)
    · have hn' : e n ∈ normalizer ((D.map e.toMonoidHom : Subgroup Q') : Set Q') := by
        rw [← Subgroup.map_equiv_normalizer_eq]
        exact ⟨n, hn, rfl⟩
      exact hD' _ (Subgroup.map_mono hDX)
        (by rw [Subgroup.card_map_of_injective e.injective, hD]) hn'
    · refine hA' _ (Subgroup.map_mono hAX)
        (by rw [Subgroup.card_map_of_injective e.injective, hA]) (e x) ?_
        (by rwa [MulEquiv.orderOf_eq])
      rw [Subgroup.mem_centralizer_iff] at hx ⊢
      rintro _ ⟨a, ha, rfl⟩
      simpa [map_mul] using congrArg e (hx a ha)
  rw [eq_top_iff]
  intro y _
  have hy : e.symm y ∈ W'.comap e.toMonoidHom := hW ▸ Subgroup.mem_top _
  simpa using hy

theorem genSeven_map_equiv_iff {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q') (X : Subgroup Q) :
    GenSeven Q' (X.map e.toMonoidHom) ↔ GenSeven Q X := by
  refine ⟨fun h => ?_, GenSeven.map_equiv e⟩
  have hX : (X.map e.toMonoidHom).map e.symm.toMonoidHom = X := by
    ext x
    simp
  have h' := h.map_equiv e.symm
  rwa [hX] at h'

theorem isLThreeTwo_of_isL2Odd_seven {Y : Type} [Group Y] (h : IsL2Odd Y 7) : IsLThreeTwo Y :=
  CFSG.AGLEmbeddingD2.McLaughlin.Lie.isLThreeTwo_of_statedClassicalModel
    (CFSG.Blueprint.LieModel.statedClassicalModel h (by decide))

theorem exists_orderOf_eq_three_of_isL2Odd_seven {Q : Type} [Group Q] [Finite Q] {X : Subgroup Q}
    (hX : IsL2Odd (Bar2 X) 7) : ∃ y : ↥X, orderOf y = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h168 : 168 ∣ Nat.card ↥X := by
    rw [← PartTwo.Inputs1719.card_of_isL2Odd_seven hX]
    exact Subgroup.card_dvd_of_surjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥X))
  exact exists_prime_orderOf_dvd_card' 3 (dvd_trans (by norm_num) h168)

theorem exists_le_card_eq_three_of_isL2Odd_seven {Q : Type} [Group Q] [Finite Q]
    {X : Subgroup Q} (hX : IsL2Odd (Bar2 X) 7) : ∃ D : Subgroup Q, D ≤ X ∧ Nat.card D = 3 := by
  obtain ⟨y, hy⟩ := exists_orderOf_eq_three_of_isL2Odd_seven hX
  refine ⟨zpowers (y : Q), (zpowers_le).mpr y.2, ?_⟩
  rw [Nat.card_zpowers, Subgroup.orderOf_coe, hy]

theorem not_isSolvable_of_isL2Odd_seven {Q : Type} [Group Q] {X : Subgroup Q}
    (hX : IsL2Odd (Bar2 X) 7) {W : Subgroup Q} (hXW : X ≤ W) : ¬ Group.IsSolvable ↥W := by
  intro hW
  have : Group.IsSolvable ↥X :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hXW)
  have : IsSimpleGroup (Bar2 X) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hX
  have : IsMulCommutative (Bar2 X) := ⟨⟨IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance⟩⟩
  have hp := (Group.is_simple_iff_prime_card (α := Bar2 X)).mp inferInstance
  rw [PartTwo.Inputs1719.card_of_isL2Odd_seven hX] at hp
  norm_num at hp

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9
