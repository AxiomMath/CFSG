module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.InP11OfStrongly
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SylowCentralOuter
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OutPRankBound
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs13
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07
public import CFSG.LocalAnalysis.UniquenessCase.UCR638
public import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
public import CFSG.GroupTheory.TPermutingTorus
public import CFSG.LocalAnalysis.SectionRank.TwoGenerators
public import CFSG.GroupTheory.ElemAbelianRank
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1517B
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsHyp13
public import CFSG.Quasithin.Background.SmithC27Star

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

local notation "pRank" => CFSG.Open.pRank

theorem not_isStronglyPEmbedded_of_le_normalizer {D : Data G} {V₀ V : Subgroup G}
    {hV : Hyp125 D V₀ V} (h1 : R17_1At D V₀ V hV) (hk : D.k = 1) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) {R : Subgroup G} (hRM : R ≤ D.M) (hRT : R ≤ normalizer (D.T : Set G))
    (hRel : IsElemAbelian r R) (hRcard : Nat.card R = r ^ 2) :
    ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded r D.M := by
  intro hstr
  have hnc : ¬ IsCyclic ↥R := by
    intro hcyc
    have h2 : 2 ≤ pRank r R := CFSG.SectionRank.le_pRank hr.one_lt le_rfl hRel hRcard
    have h1' : pRank r R ≤ 1 := CFSG.SectionRank.pRank_le_one_of_isCyclic hr hcyc
    omega
  have hperm : Permutes R D.T :=
    (CFSG.GroupTheory.set_mul_comm_of_le_normalizer (H := D.T) (T := R) hRT).symm
  have hin : F11.InP11 D R :=
    inP11_of_strongly hr hr2 hstr hRM hRel.isPGroup hRel.2 hnc hperm
  have hk2 : D.k = 2 := (h1.2 ⟨R, hin⟩).2.1
  omega

theorem not_rankThreeGamma_le_of_is3D4 {D : Data G} {V₀ V : Subgroup G}
    {hV : Hyp125 D V₀ V} (h1 : R17_1At D V₀ V hV) (hk : D.k = 1) {L : Subgroup G}
    (hL : L ∈ calC D.M) (hN : (L.subgroupOf D.M).Normal) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hab : ∀ P : Sylow r (Bar2 L), IsMulCommutative (P : Subgroup (Bar2 L)))
    (hout : ¬ r ∣ Nat.card (Outer (Bar2 L))) {R : Subgroup G} (hRL : R ≤ L)
    (hRT : R ≤ normalizer (D.T : Set G)) (hRel : IsElemAbelian r R)
    (hRcard : Nat.card R = r ^ 2) : ¬ rankThreeGamma 1 r R ≤ D.M := by
  intro hΓ
  have hLM : L ≤ D.M := hL.1.le
  have hMN : D.M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).1 hN
  have hRM : R ≤ D.M := hRL.trans hLM
  have hnc : ¬ IsCyclic ↥R := by
    intro hcyc
    have h2 : 2 ≤ pRank r R := CFSG.SectionRank.le_pRank hr.one_lt le_rfl hRel hRcard
    have h1' : pRank r R ≤ 1 := CFSG.SectionRank.pRank_le_one_of_isCyclic hr hcyc
    omega
  have hperm : Permutes R D.T :=
    (CFSG.GroupTheory.set_mul_comm_of_le_normalizer (H := D.T) (T := R) hRT).symm
  have hrelIndex : ¬ r ∣ (L ⊔ F08.CentOverO2 D.M L).relIndex D.M := by
    have hdvd := relIndex_centOverO2_dvd_card_outer hLM hMN
    exact fun h => hout (h.trans hdvd)
  obtain ⟨Q, hQ, hRQ⟩ :=
    exists_sylow_le_centralizer_of_isMulCommutative hr hr2 hLM hMN hab hrelIndex hRL
      hRel.isPGroup
  have hRQ' : R ≤ Q := fun x hx => (hRQ hx).1
  have hQN : Q ≤ Subgroup.normalizer (R : Set G) := by
    have hQcent : Q ≤ Subgroup.centralizer (R : Set G) := by
      intro q hq
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (Subgroup.mem_centralizer_iff.mp (hRQ hx).2 q hq).symm
    exact hQcent.trans (Subgroup.centralizer_le_normalizer (R : Set G))
  have hin : F11.InP11 D R :=
    ⟨r, hr, hr2, hRM, hRel.isPGroup, hRel.2, hnc, hperm, hΓ,
      Or.inr ⟨R, hnc, ⟨Q, hQ, hRQ', hQN⟩, hΓ⟩⟩
  have hk2 : D.k = 2 := (h1.2 ⟨R, hin⟩).2.1
  omega

theorem pRank_eq_three_of_is3D4 {D : Data G} (hSg : UC6S846.SigmaStd D) (h76 : F07.R76 D)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hN : (L.subgroupOf D.M).Normal)
    (hZ : Subgroup.center (Bar2 L) = ⊥) (hOut : IsCyclic (Outer (Bar2 L)))
    (hbar : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p (⊤ : Subgroup (Bar2 L)) ≤ 2)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrsig : r ∉ D.sig) {R : Subgroup G} (hRL : R ≤ L)
    (hRel : IsElemAbelian r R) (hRcard : Nat.card R = r ^ 2)
    (hΓ : ¬ rankThreeGamma 1 r R ≤ D.M) {p : ℕ} (hp : p ∈ D.sig) :
    CFSG.Open.pRank p D.M = 3 ∧ CFSG.Open.pRank p L = 2 ∧
      CFSG.Open.pRank p (F08.CentOverO2 D.M L) = 1 := by
  obtain ⟨hp', hp2⟩ := D.sig_prime p hp
  have hns : ¬ Group.IsSolvable ↥D.M := UC6S846.not_solvable_of_mem_calC hL
  have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M :=
    UC6S846.sp_of_mem_sig hSg hns hp
  have hOp : UC22.F10.OpRes p D.M = D.M :=
    UC6.opRes_eq_of_stronglyEmbedded_uc6 D.standing.simple D.standing.nonab hp' hsp
  have hLM : L ≤ D.M := hL.1.le
  have hMN : D.M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).1 hN
  have hRM : R ≤ D.M := hRL.trans hLM
  have hcentR : pRank p (D.M ⊓ Subgroup.centralizer (R : Set G)) ≤ 1 := by
    by_contra hcon
    have h2 : 2 ≤ pRank p (D.M ⊓ Subgroup.centralizer (R : Set G)) := by omega
    have hnorm : ∀ X : Subgroup G, X ≤ R → Nat.card X = r →
        1 < pRank p (D.M ⊓ Subgroup.normalizer (X : Set G)) := by
      intro X hXR hXcard
      have hCRX : Subgroup.centralizer (R : Set G) ≤ Subgroup.centralizer (X : Set G) := by
        intro z hz
        rw [Subgroup.mem_centralizer_iff] at hz ⊢
        intro y hy
        exact hz y (hXR hy)
      have hle : D.M ⊓ Subgroup.centralizer (R : Set G) ≤
          D.M ⊓ Subgroup.normalizer (X : Set G) :=
        inf_le_inf_left _ (hCRX.trans (Subgroup.centralizer_le_normalizer (X : Set G)))
      exact lt_of_lt_of_le (by omega) (CFSG.SectionRank.pRank_mono hp'.one_lt hle)
    exact hΓ (h76 p hp' hp2 hsp r hr R hRM hRel hRcard (by omega) hnorm)
  have hrp : r ≠ p := fun h => hrsig (h ▸ hp)
  have hcover :=
    pRank_centOverO2_le_pRank_inf_centralizer hLM hMN hp' hp2 hr hr2 hrp hRL hRel.isPGroup
  have hcentC : pRank p (F08.CentOverO2 D.M L) ≤ 1 := hcover.trans hcentR
  have hbound := pRank_le_pRank_bar2_add_pRank_centOverO2 hLM hMN hZ hOut hp' hp2 hOp
  rw [UC22.pRank_bar2_eq_of_odd (Y := L) hp' hp2] at hbound
  have hbarL : pRank p L ≤ 2 := by
    rw [← UC22.pRank_bar2_eq_of_odd (Y := L) hp' hp2]
    exact hbar p hp' hp2
  have hmM : pRank p D.M = 3 := by
    have h3 := hSg.three_le p hp
    omega
  have hmL : pRank p L = 2 := by omega
  have hmC : pRank p (F08.CentOverO2 D.M L) = 1 := by omega
  exact ⟨hmM, hmL, hmC⟩

theorem pRank_le_two_of_not_mem_sig {D : Data G} (hSg : UC6S846.SigmaStd D)
    (h13 : SigmaRankThree13 D) {p : ℕ} (hp : p ∈ D.sig) (hp3 : CFSG.Open.pRank p D.M = 3)
    {r : ℕ} (hr : r.Prime) (hr7 : 7 ≤ r) (hrsig : r ∉ D.sig) :
    CFSG.Open.pRank r D.M ≤ 2 := by
  by_contra hcon
  exact hrsig (h13 ⟨p, hp, hp3⟩ r hr hr7 (by omega))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
