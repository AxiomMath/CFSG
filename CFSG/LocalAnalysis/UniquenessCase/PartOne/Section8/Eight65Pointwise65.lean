module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65Final
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight64Clause4Implication
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65X0
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65TMemGamma
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup
open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem eight65_pointwise_false
    {D : Data G} {L X P Q Z : Subgroup G} {t : G}
    (hZU : Z ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet D.M)
    (hΓ : CFSG.Open.rankThreeGamma 1 3 Q ≤ D.M)
    (hLMle : L ≤ D.M) (hLM : (L.subgroupOf D.M).Normal)
    (hQP : Q ≤ P) (hZQ : Z ≤ Q) (hZcard : Nat.card Z = 3)
    (hXcard : Nat.card X = 3)
    (h64 : List864 L X P)
    (hXnotM : ¬ Subgroup.normalizer (X : Set G) ≤ D.M)
    (hZbar : Subgroup.center (Bar2 L) = ⊥) (hZL : Z ≤ L)
    (hX0card : Nat.card (centralizerBar (X ⊔ Z) L) = 3)
    (htX : ∀ x ∈ X, t * x * t⁻¹ = x)
    (htZ : ∀ z ∈ Z, t * z * t⁻¹ = z⁻¹)
    (hnot : ¬ ⁅L, X⁆ ≤ CFSG.Open.pCoreOf 2 L) : False := by
  classical
  have hQX : ⁅Q, X⁆ = ⊥ := commutator_eq_bot_of_list864 h64 hnot hQP
  have hQcent : Q ≤ Subgroup.centralizer (X : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hQX
  have hcomm : ∀ x ∈ X, ∀ z ∈ Z, x * z = z * x := by
    intro x hx z hz
    exact Subgroup.mem_centralizer_iff.mp (hQcent (hZQ hz)) x hx
  have hZ3 : ∀ z ∈ Z, z ^ 3 = 1 := by
    intro z hz
    have h := pow_card_eq_one' (G := ↥Z) (x := ⟨z, hz⟩)
    rw [hZcard] at h
    simpa using congrArg Subtype.val h
  have hXneZ : X ≠ Z := by
    intro hEq
    apply hXnotM
    rw [hEq]
    exact CFSG.LocalAnalysis.RankThreeUC.normalizer_le_of_mem_uniqueSet D.maxLocal hZU
  have hZnotle : ¬ Z ≤ centralizerBar (X ⊔ Z) L :=
    not_le_centralizerBar_of_center_bar_eq_bot hZbar hZL hZcard
      (le_sup_right : Z ≤ X ⊔ Z)
  have hX0ne : centralizerBar (X ⊔ Z) L ≠ Z := by
    intro hEq
    exact hZnotle (le_of_eq hEq.symm)
  have htL : L.map (MulAut.conj t).toMonoidHom = L :=
    (t_mem_and_map_conj_of_inverts_of_gamma hZQ hZcard hΓ hLMle hLM htZ).2
  exact eight65_false_of_inverting_element hcomm hZ3 hXcard hZcard hXneZ htX htZ
    hX0card hX0ne rfl htL hnot

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
