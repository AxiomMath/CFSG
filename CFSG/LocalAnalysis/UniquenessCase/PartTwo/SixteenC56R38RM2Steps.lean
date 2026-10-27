module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.WeakClosure81.SixFour

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem r38_m2_false_of_steps' (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h76 : F07.R76Sig D) (h614 : UC6.R6_14 D) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : Case167_5 D V₀ V hV L) {n : ℕ} {g : G} (hO : InCalOStar n D.M V₀ V g)
    (hA : ∃ R Q : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 R D.M ∧
      Q ≤ R ⊓ centralizer (R : Set G) ∧ IsElemAbelian 3 Q ∧ Nat.card Q = 3 ^ 2 ∧
      1 < CFSG.Open.pRank 5 (D.M ⊓ centralizer (Q : Set G)))
    (hBC : IsStronglyPEmbedded 3 D.M →
      ∃ v ∈ NOf D.M V g, v ≠ 1 ∧ centralizer ({v} : Set G) ≤ D.M) : False := by
  obtain ⟨R, Q, hRsyl, hQR, hQel, hQcard, hQrank⟩ := hA
  have h5sig : 5 ∈ D.sig := by rw [hc.2.2]; exact Set.mem_singleton 5
  have hsp5 : IsStronglyPEmbedded 5 D.M := hSg.sig1_sp 5 (by rw [← h1219]; exact h5sig)
  have hQM : Q ≤ D.M := hQR.trans (inf_le_left.trans hRsyl.le)
  have hlast : ∀ X : Subgroup G, X ≤ Q → Nat.card X = 3 →
      1 < CFSG.Open.pRank 5 (D.M ⊓ normalizer (X : Set G)) := by
    intro X hXQ _
    have hcent : centralizer (Q : Set G) ≤ normalizer (X : Set G) :=
      (Subgroup.centralizer_le
        (show (X : Set G) ⊆ (Q : Set G) from fun x hx => hXQ hx)).trans
        (Subgroup.centralizer_le_normalizer (X : Set G))
    have hle : D.M ⊓ centralizer (Q : Set G) ≤ D.M ⊓ normalizer (X : Set G) :=
      le_inf inf_le_left (inf_le_right.trans hcent)
    exact lt_of_lt_of_le hQrank (CFSG.SectionRank.pRank_mono (by norm_num : 1 < 5) hle)
  have hQpos : 0 < CFSG.Open.pRank 5 (D.M ⊓ centralizer (Q : Set G)) := by omega
  have hΓ : rankThreeGamma 1 3 Q ≤ D.M :=
    h76 5 h5sig (by norm_num) hsp5 3 Nat.prime_three Q hQM hQel hQcard hQpos hlast
  have hsp3 : IsStronglyPEmbedded 3 D.M :=
    h614 h1219.le 3 Nat.prime_three (by norm_num) (by rw [hc.2.2]; simp) R hRsyl Q hQR hQel
      hQcard hΓ
  obtain ⟨v, hvN, _hv1, hvC⟩ := hBC hsp3
  have hVgC : conjSubgroup V g ≤ centralizer (NOf D.M V g : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact B2F.isElemAbelian_comm (E3.isElemAbelian_conjSubgroup hV g) hy.2.1 hx
  have hUC : ¬ centralizer (NOf D.M V g : Set G) ≤ D.M := fun hle =>
    hO.1.1.1 (hVgC.trans hle)
  have hle : centralizer (NOf D.M V g : Set G) ≤ centralizer ({v} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hvN)
  exact hUC (hle.trans hvC)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
