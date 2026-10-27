module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Defs
public import CFSG.GroupTheory.ConjActionModPCore
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CComponents
import CFSG.GH74.Uniqueness.SU.SU1Basic
import CFSG.LocalAnalysis.StronglyEmbedded.GammaOne
import CFSG.GroupTheory.CoprimeCentralizerCover
import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer
import CFSG.GroupTheory.PGroup.ElemAbelianSq

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.Open
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

structure Case811Sylow (c : Counterexample4 G) where
  P : Subgroup G
  A : Subgroup G
  sylow : CFSG.ABGLocalTools.IsSylowOf 3 P c.S.M
  P_le_L : P ≤ c.L
  A_le : A ≤ P
  elemAbelian : CFSG.Open.IsElemAbelian 3 A
  card_A : Nat.card A = 27
  unique : ∀ B : Subgroup G, B ≤ P → CFSG.Open.IsElemAbelian 3 B → Nat.card B = 27 → B = A
  cover : ∀ x ∈ c.S.M, orderOf x = 3 → ∃ m ∈ c.S.M, m * x * m⁻¹ ∈ A

namespace Case811Sylow

theorem not_rankThreeGamma_le {c : Counterexample4 G} (h : Case811Sylow c) :
    ¬ CFSG.Open.rankThreeGamma 1 3 h.A ≤ c.S.M := by
  intro hΓ
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hA1 : h.A ≠ ⊥ := by
    intro hbot
    have hcard := h.card_A
    rw [hbot, Subgroup.card_bot] at hcard
    norm_num at hcard
  refine c.not_strong
    (CFSG.RankThree.PartOne.isStronglyPEmbedded_of_rankThreeGamma_le
      (q := 3) (M := c.S.M) (P := h.P) (A := h.A) c.M_ne_top h.sylow h.A_le
      h.elemAbelian hA1 ?_ h.cover hΓ)
  intro B hBP hBab hBcard
  exact h.unique B hBP hBab (by rw [hBcard, h.card_A])

theorem false_of_rank_conditions {c : Counterexample4 G} (h : Case811Sylow c) {p : ℕ}
    (hp : p ∈ CFSG.Open.uniqueFourSigma c.S.M)
    (h76 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 c.S.M p)
    (hcent : ∀ E : Subgroup G, E ≤ h.A → CFSG.Open.IsElemAbelian 3 E → Nat.card E = 9 →
      0 < CFSG.Open.pRank p (c.S.M ⊓ Subgroup.centralizer (E : Set G)))
    (hN : ∀ E X : Subgroup G, X ≤ E → E ≤ h.A → CFSG.Open.IsElemAbelian 3 E →
      Nat.card E = 9 → Nat.card X = 3 →
      1 < CFSG.Open.pRank p (c.S.M ⊓ Subgroup.normalizer (X : Set G)))
    (hdvd : ∀ X : Subgroup G, X ≤ h.A → Nat.card X = 3 →
      p ∣ Nat.card (Subgroup.normalizer (X : Set G))) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hp_prime : p.Prime := hp.1.1
  haveI : Fact p.Prime := ⟨hp_prime⟩
  have hA_gamma : CFSG.Open.rankThreeGamma 1 3 h.A ≤ c.S.M := by
    refine CFSG.RankThree.PartOne.IsStronglyPEmbedded.rankThreeGamma_one_le
      (p := p) (q := 3) (M := c.S.M) (A := h.A)
      (c.isStronglyPEmbedded_of_mem_sigma hp) h.elemAbelian.isPGroup ?_
    intro X hXA hXcard
    obtain ⟨E, hXE, hEA, hEab, hEcard⟩ :=
      CFSG.GroupTheory.exists_isElemAbelian_card_sq_of_le_of_card_prime h.elemAbelian.isPGroup
        ((show 2 ≤ 3 by norm_num).trans (CFSG.SectionRank.le_pRank (by norm_num) le_rfl
          h.elemAbelian (by rw [h.card_A]; norm_num))) hXA hXcard
    have hEcard9 : Nat.card E = 9 := by rw [hEcard]; norm_num
    have hEM : E ≤ c.S.M := hEA.trans (h.A_le.trans (h.P_le_L.trans c.hyp81.1))
    have hΓE : CFSG.Open.rankThreeGamma 1 3 E ≤ c.S.M :=
      h76 3 (by norm_num) E hEM hEab (by rw [hEcard9]; norm_num)
        (hcent E hEA hEab hEcard9)
        (fun Y hYE hYcard => hN E Y hYE hEA hEab hEcard9 hYcard)
    have hNX_le_ΓE : Subgroup.normalizer (X : Set G) ≤ CFSG.Open.rankThreeGamma 1 3 E := by
      have hXab : CFSG.Open.IsElemAbelian 3 X := h.elemAbelian.mono hXA
      have h1 : 1 ≤ CFSG.Open.pRank 3 X :=
        CFSG.SectionRank.le_pRank (p := 3) (by norm_num) (le_refl X) hXab
          (by rw [hXcard]; norm_num)
      have hcore := CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore
        (p := 3) (k := 1) (P := E) (Q := X) hXE h1
      simpa [CFSG.Open.rankThreeGamma] using hcore
    exact ⟨hNX_le_ΓE.trans hΓE, hdvd X hXA hXcard⟩
  exact h.not_rankThreeGamma_le hA_gamma

theorem false_of_le_centralizer_A {c : Counterexample4 G} (h : Case811Sylow c) {p : ℕ}
    (hp : p ∈ CFSG.Open.uniqueFourSigma c.S.M)
    (h76 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 c.S.M p)
    {R : Subgroup G} (hRM : R ≤ c.S.M) (hRA : R ≤ Subgroup.centralizer (h.A : Set G))
    (hR : CFSG.Open.IsElemAbelian p R) (hRcard : Nat.card R = p ^ 2) : False := by
  have hp_prime : p.Prime := hp.1.1
  haveI : Fact p.Prime := ⟨hp_prime⟩
  refine false_of_rank_conditions h hp h76 ?_ ?_ ?_
  · intro E hEA hEab hEcard
    have hle : R ≤ c.S.M ⊓ Subgroup.centralizer (E : Set G) :=
      le_inf hRM (hRA.trans (Subgroup.centralizer_le (fun x hx => hEA hx)))
    have h2 : 2 ≤ CFSG.Open.pRank p (c.S.M ⊓ Subgroup.centralizer (E : Set G)) :=
      CFSG.SectionRank.le_pRank hp_prime.one_lt hle hR hRcard
    omega
  · intro E X hXE hEA hEab hEcard hXcard
    have hcentE : Subgroup.centralizer (h.A : Set G) ≤ Subgroup.normalizer (X : Set G) :=
      (Subgroup.centralizer_le (fun x hx => hEA (hXE hx))).trans
        (Subgroup.centralizer_le_normalizer (X : Set G))
    have hle : R ≤ c.S.M ⊓ Subgroup.normalizer (X : Set G) :=
      le_inf hRM (hRA.trans hcentE)
    have h2 : 2 ≤ CFSG.Open.pRank p (c.S.M ⊓ Subgroup.normalizer (X : Set G)) :=
      CFSG.SectionRank.le_pRank hp_prime.one_lt hle hR hRcard
    omega
  · intro X hXA hXcard
    have hle : R ≤ Subgroup.normalizer (X : Set G) :=
      hRA.trans ((Subgroup.centralizer_le (fun x hx => hXA hx)).trans
        (Subgroup.centralizer_le_normalizer (X : Set G)))
    have hdvd : p ∣ Nat.card R := by
      rw [hRcard]
      exact dvd_pow_self p (by norm_num)
    exact hdvd.trans (Subgroup.card_dvd_of_le hle)

theorem false_of_commutator_le {c : Counterexample4 G} (h : Case811Sylow c) {p : ℕ}
    (hp : p ∈ CFSG.Open.uniqueFourSigma c.S.M)
    (h76 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 c.S.M p)
    (hLM : c.S.M ≤ Subgroup.normalizer (c.L : Set G))
    {R : Subgroup G} (hRM : R ≤ c.S.M) (hR : CFSG.Open.IsElemAbelian p R)
    (hRcard : Nat.card R = p ^ 2)
    (hcomm : ⁅c.L, R⁆ ≤ CFSG.Open.pCoreOf 2 c.L) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hp_prime : p.Prime := hp.1.1
  haveI : Fact p.Prime := ⟨hp_prime⟩
  have hp5 : 5 ≤ p := c.five_le_of_mem_sigma hp
  have hp2 : p ≠ 2 := by omega
  have hR_le_NL : R ≤ Subgroup.normalizer (c.L : Set G) := hRM.trans hLM
  have hRN : R ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 c.L : Set G) :=
    hR_le_NL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 c.L)
  have hN2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 c.L) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 c.L
  have hN_not_dvd_p : ¬ p ∣ Nat.card (CFSG.Open.pCoreOf 2 c.L) := by
    obtain ⟨n, hn⟩ := hN2.exists_card_eq
    intro hdvd
    rw [hn] at hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp_prime Nat.prime_two).mp
      (hp_prime.dvd_of_dvd_pow hdvd))
  have hN_not_dvd_3 : ¬ 3 ∣ Nat.card (CFSG.Open.pCoreOf 2 c.L) := by
    obtain ⟨n, hn⟩ := hN2.exists_card_eq
    intro hdvd
    rw [hn] at hdvd
    have h32 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow hdvd
    norm_num at h32
  obtain ⟨S, hS_sylow, hS_cent⟩ :=
    CFSG.GroupTheory.exists_isSylowOf_le_centralizer_of_commutator_le
      (p := p) (q := 3) (X := c.L) (N := CFSG.Open.pCoreOf 2 c.L) (R := R)
      (CFSG.LieType.BorelTits.pCoreOf_le 2 c.L) hR_le_NL hRN hR.isPGroup hN_not_dvd_p
      hcomm hN_not_dvd_3
  have hP_sylow_L : CFSG.ABGLocalTools.IsSylowOf 3 h.P c.L :=
    h.sylow.of_le h.P_le_L c.hyp81.1
  obtain ⟨k, hkL, hkconj⟩ := hS_sylow.exists_mem_conj hP_sylow_L
  have hkM : k ∈ c.S.M := c.hyp81.1 hkL
  have hkconj_apply : ∀ y : G, (MulAut.conj k).toMonoidHom y = k * y * k⁻¹ := fun _ => rfl
  let R' : Subgroup G := R.map (MulAut.conj k).toMonoidHom
  have hR'_elem : CFSG.Open.IsElemAbelian p R' := hR.map (MulAut.conj k).toMonoidHom
  have hR'_card : Nat.card R' = p ^ 2 := by
    change Nat.card (R.map (MulAut.conj k).toMonoidHom) = p ^ 2
    rw [Subgroup.card_map_of_injective (MulAut.conj k).injective, hRcard]
  have hR'_le_M : R' ≤ c.S.M := by
    rintro x ⟨r, hr, rfl⟩
    rw [hkconj_apply]
    exact c.S.M.mul_mem (c.S.M.mul_mem hkM (hRM hr)) (c.S.M.inv_mem hkM)
  have hR'_centP : R' ≤ Subgroup.centralizer (h.P : Set G) := by
    rintro x ⟨r, hr, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    rw [hkconj_apply]
    have hsq : k⁻¹ * q * k ∈ S := (hkconj q).mp hq
    have hrs : r * (k⁻¹ * q * k) = (k⁻¹ * q * k) * r :=
      Subgroup.mem_centralizer_iff.mp (hS_cent hsq) r hr
    calc
      q * (k * r * k⁻¹) = k * ((k⁻¹ * q * k) * r) * k⁻¹ := by group
      _ = k * (r * (k⁻¹ * q * k)) * k⁻¹ := by rw [← hrs]
      _ = (k * r * k⁻¹) * q := by group
  have hR'_centA : R' ≤ Subgroup.centralizer (h.A : Set G) :=
    hR'_centP.trans (Subgroup.centralizer_le (fun x hx => h.A_le hx))
  exact h.false_of_le_centralizer_A hp h76 hR'_le_M hR'_centA hR'_elem hR'_card

theorem pRank_map_ker_le_one {c : Counterexample4 G} (h : Case811Sylow c) {p : ℕ}
    (hp : p ∈ CFSG.Open.uniqueFourSigma c.S.M)
    (h76 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 c.S.M p) :
    CFSG.Open.pRank p ((CFSG.GroupTheory.conjModPCore 2 c.L c.S.M c.le_normalizer_L).ker.map
      c.S.M.subtype) ≤ 1 := by
  by_contra hle
  have h2 : 2 ≤ CFSG.Open.pRank p
      ((CFSG.GroupTheory.conjModPCore 2 c.L c.S.M c.le_normalizer_L).ker.map
        c.S.M.subtype) := by omega
  obtain ⟨R, hR_le, hR, hRcard⟩ :=
    CFSG.GH74.Uniqueness.SU.SU1.exists_isElemAbelian_of_le_pRank (p := p) hp.1.1 (k := 2) h2
  have hRM : R ≤ c.S.M := hR_le.trans (Subgroup.map_subtype_le _)
  have hcomm : ⁅c.L, R⁆ ≤ CFSG.Open.pCoreOf 2 c.L :=
    (CFSG.GroupTheory.le_map_ker_conjModPCore_iff_commutator 2 c.L c.S.M R
      c.le_normalizer_L hRM).mp hR_le
  exact h.false_of_commutator_le hp h76 c.le_normalizer_L hRM hR hRcard hcomm

theorem three_le_pRank_range {c : Counterexample4 G} (h : Case811Sylow c) {p : ℕ}
    (hp : p ∈ CFSG.Open.uniqueFourSigma c.S.M)
    (h76 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 c.S.M p) :
    3 ≤ CFSG.Open.pRank p
      (CFSG.GroupTheory.conjModPCore 2 c.L c.S.M c.le_normalizer_L).range := by
  have hrank := CFSG.GroupTheory.pRank_le_pRank_map_ker_add_pRank_range
    (p := 2) (q := p) hp.1.1 c.L c.S.M c.le_normalizer_L
  have hM4 : 4 ≤ CFSG.Open.pRank p c.S.M := c.four_le_pRank_of_mem_sigma hp
  have hker : CFSG.Open.pRank p
      ((CFSG.GroupTheory.conjModPCore 2 c.L c.S.M c.le_normalizer_L).ker.map
        c.S.M.subtype) ≤ 1 := h.pRank_map_ker_le_one hp h76
  omega

end Case811Sylow

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
