module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsNineteenN
import CFSG.GroupTheory.CoprimeSupPCore
import CFSG.RankThree.PartTwo.Sec17.Item17Res3ProofMeet
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsEightCaseTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsNine

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9 (R920odd)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem oddN_normalizer_ne_top_of_isPGroup (D : Data G) {Z : Subgroup G} {r : ℕ}
    (hr : r.Prime) (hZ : IsPGroup r Z) (hZ1 : Z ≠ ⊥) :
    Subgroup.normalizer (Z : Set G) ≠ ⊤ := by
  intro htop
  haveI : IsSimpleGroup G := D.standing.simple
  haveI : Fact r.Prime := ⟨hr⟩
  haveI hnorm : Z.Normal := Subgroup.normalizer_eq_top_iff.1 htop
  have hZtop : Z = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Z with h | h
    · exact absurd h hZ1
    · exact h
  have hP : IsPGroup r G := by
    have hZ' : IsPGroup r ↥(⊤ : Subgroup G) := hZtop ▸ hZ
    exact IsPGroup.of_equiv hZ' Subgroup.topEquiv
  haveI : Group.IsNilpotent G := hP.isNilpotent
  haveI : IsMulCommutative G :=
    Group.IsNilpotent.nilpotencyClass_le_one_iff.mp
      (Group.nilpotencyClass_le_one_of_isSimple_of_isNilpotent (G := G))
  obtain ⟨x, y, hxy⟩ := D.standing.nonab
  exact hxy (mul_comm x y)

private theorem oddN_false_of_r847 (D : Data G) (h847 : F08.R847 D) (hsig : D.sig.Nonempty)
    {L K : Subgroup G} (hL : L ∈ calC D.M) (hK : K ∈ calC D.M) (hLK : L ≠ K)
    {p : ℕ} (hp5 : 5 < p) (hLp : IsL2Odd (Bar2 L) p) {A : Subgroup G}
    (hAL : A ≤ L) (hAcard : (Nat.card A).Prime) (hAodd : Odd (Nat.card A))
    (hAnM : ¬ normalizer (A : Set G) ≤ D.M) : False := by
  have hpprime : p.Prime := hLp.admissible.1
  have hp2 : p ≠ 2 := by omega
  have hthin : F08.Thin8 L := thin8_of_isL2Odd_bar2 hpprime hp2 hLp
  have hq2 : Nat.card A ≠ 2 := by
    intro h2
    rw [h2] at hAodd
    exact (by decide : ¬ Odd 2) hAodd
  obtain ⟨p₀, hp₀⟩ := hsig
  have hmain := h847 L hL A hAL (Nat.card A) hAcard hq2 rfl p₀ hp₀ (Or.inl hthin)
  rcases hmain with h1 | h2 | h3
  · exact hAnM h1
  · obtain ⟨n, hSU3, -⟩ := h2
    exact not_lieModel_psl2_of_isSU3 hSU3 hLp
  · obtain ⟨ℓ, f, -, -, -, -, -, -, A', hGrpA, hLieA, hnf⟩ := h3
    letI : Group A' := hGrpA
    letI : IsSimpleGroup A' :=
      CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSL) (by decide) hLieA
    exact not_nonempty_mulEquiv_fstar_of_ne D hL hK hLK
      (A := A') (B := Multiplicative (ZMod 3) × Multiplicative (ZMod 3))
      (fun a b => mul_comm a b) hnf

private theorem oddN_hyp919c_of_commutator_le (D : Data G) {L D₃ Z : Subgroup G} {r : ℕ}
    (hL : L ∈ calC D.M) (hD₃L : D₃ ≤ L) (hD₃ : Nat.card D₃ = 3)
    (hD₃U : D₃ ∈ uniqueSet D.M) (hr : r.Prime) (hr2 : r ≠ 2) (hZr : IsPGroup r Z)
    (hZ1 : Z ≠ ⊥) (hZL : ⁅Z, L⁆ ≤ pCoreOf 2 L)
    (hHM : ¬ normalizer (Z : Set G) ≤ D.M) :
    PartTwo.Hyp919c D L D₃ (L ⊓ centralizer (Z : Set G)) (normalizer (Z : Set G)) := by
  have hYL : L ⊓ centralizer (Z : Set G) ≤ L := inf_le_left
  have hYM : L ⊓ centralizer (Z : Set G) ≤ D.M := hYL.trans hL.1.le
  have hYH : L ⊓ centralizer (Z : Set G) ≤ normalizer (Z : Set G) :=
    (inf_le_right : L ⊓ centralizer (Z : Set G) ≤ centralizer (Z : Set G)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hsup : L = (L ⊓ centralizer (Z : Set G)) ⊔ pCoreOf 2 L :=
    (CFSG.GroupTheory.inf_centralizer_sup_pCoreOf_eq_of_commutator_le hr hr2 hZr hZL).symm
  have hsup' : L = (L ⊓ (L ⊓ centralizer (Z : Set G))) ⊔ pCoreOf 2 L := by
    rw [inf_eq_right.mpr hYL]
    exact hsup
  have hN : ((L ⊓ (L ⊓ centralizer (Z : Set G))).subgroupOf
      (L ⊓ centralizer (Z : Set G))).Normal := by
    rw [inf_eq_right.mpr hYL, Subgroup.subgroupOf_self]
    exact inferInstance
  have hidx : ((L ⊓ (L ⊓ centralizer (Z : Set G))).subgroupOf
      (L ⊓ centralizer (Z : Set G))).index = 2 ^ 0 := by
    rw [inf_eq_right.mpr hYL, Subgroup.subgroupOf_self, Subgroup.index_top, pow_zero]
  exact ⟨hL, hD₃L, hD₃, hD₃U, hYM, hsup', hN, ⟨0, hidx⟩,
    oddN_normalizer_ne_top_of_isPGroup D hr hZr hZ1, hYH, hHM⟩

theorem normalizer_le_of_commutator_le_pCoreOf_r920odd (D : Data G) (h920 : R920odd D)
    (h847 : F08.R847 D) (hsig : D.sig.Nonempty) {L K : Subgroup G} (hL : L ∈ calC D.M)
    (hK : K ∈ calC D.M) (hLK : L ≠ K) {p : ℕ} (hp5 : 5 < p) (hLp : IsL2Odd (Bar2 L) p)
    {D₃ : Subgroup G} (hD₃L : D₃ ≤ L) (hD₃ : Nat.card D₃ = 3) (hD₃U : D₃ ∈ uniqueSet D.M)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {Z : Subgroup G} (hZr : IsPGroup r Z) (hZ1 : Z ≠ ⊥)
    (hZL : ⁅Z, L⁆ ≤ CFSG.Open.pCoreOf 2 L) : Subgroup.normalizer (Z : Set G) ≤ D.M := by
  by_contra hHM
  have hc := oddN_hyp919c_of_commutator_le D hL hD₃L hD₃ hD₃U hr hr2 hZr hZ1 hZL hHM
  have hsup : L = (L ⊓ centralizer (Z : Set G)) ⊔ pCoreOf 2 L :=
    (CFSG.GroupTheory.inf_centralizer_sup_pCoreOf_eq_of_commutator_le hr hr2 hZr hZL).symm
  obtain ⟨e⟩ := CFSG.RankThree.PartTwo.Sec17.Proof17Res3.nonempty_quotient_pCore_two_equiv
    (inf_le_left : L ⊓ centralizer (Z : Set G) ≤ L) hsup
  obtain ⟨A, hAY, hAcard, hAodd, hAnM⟩ := h920 L D₃ (L ⊓ centralizer (Z : Set G))
    (normalizer (Z : Set G)) hc inf_le_left p hLp.admissible.1 hp5
    (CFSG.Blueprint.LieModel.of_mulEquiv e hLp)
  exact oddN_false_of_r847 D h847 hsig hL hK hLK hp5 hLp (hAY.trans inf_le_left) hAcard hAodd
    hAnM

end CFSG.LocalAnalysis.UniquenessCase.UC22
