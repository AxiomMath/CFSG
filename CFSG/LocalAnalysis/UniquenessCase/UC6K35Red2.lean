module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.CyclicOuterTools
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Gls3Input
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.RankThree.PartOne.CTP.StrongPGlue
public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

section Reduction

variable {Y : Type} [Group Y] [Finite Y] {p : ℕ} [hp : Fact p.Prime]

theorem ne_bot_of_one_le_pRank {Q : Subgroup Y} (h : 1 ≤ CFSG.Open.pRank p Q) : Q ≠ ⊥ := by
  rintro rfl
  have h0 : CFSG.Open.pRank p (⊥ : Subgroup Y) ≤ 0 :=
    CFSG.SectionRank.pRank_le hp.out.one_lt fun E hE _ => by
      rw [le_bot_iff.mp hE, Subgroup.card_bot, pow_zero]
  omega

theorem glbCore_le_of_isStronglyPEmbedded {N P : Subgroup Y} (hN : IsStronglyPEmbedded p N)
    (hP : IsPGroup p P) (hPN : P ≤ N) : GLBCore p 1 P ≤ N := by
  refine sSup_le ?_
  rintro M ⟨Q, hQP, hQ, rfl⟩
  exact hN.normalizer_le (ne_bot_of_one_le_pRank hQ) (hP.to_le hQP) (hQP.trans hPN)

theorem gammaCore_le_of_isStronglyPEmbedded {N P A : Subgroup Y} (hN : IsStronglyPEmbedded p N)
    (hP : IsPGroup p P) (hPN : P ≤ N) :
    CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.gammaCore p 1 A P ≤ N := by
  refine (Subgroup.closure_le N).2 ?_
  rintro x ⟨-, R, hRP, hR, hx⟩
  exact hN.normalizer_le (ne_bot_of_one_le_pRank hR) (hP.to_le hRP) (hRP.trans hPN) hx

theorem inf_ne_bot_of_pPrimeCore (hO : CFSG.pPrimeCore p Y = ⊥) {K : Subgroup Y} [hKn : K.Normal]
    (hK1 : K ≠ ⊥) (P : Sylow p Y) : (P : Subgroup Y) ⊓ K ≠ ⊥ := by
  intro h
  apply hK1
  obtain ⟨T, hT⟩ := CFSG.Glauberman.sylow_inf_normal P (N := K)
  have hT1 : Nat.card (T : Subgroup ↥K) = 1 := by
    rw [hT, h]
    simp
  have hfac : (Nat.card K).factorization p = 0 := by
    have h2 := Sylow.card_eq_multiplicity T
    rw [hT1] at h2
    exact (Nat.pow_eq_one.mp h2.symm).resolve_left hp.out.one_lt.ne'
  have hcop : Nat.Coprime p (Nat.card K) :=
    (Nat.Prime.coprime_iff_not_dvd hp.out).2 fun hd =>
      (Nat.Prime.factorization_pos_of_dvd hp.out Nat.card_pos.ne' hd).ne' hfac
  have hle : K ≤ CFSG.pPrimeCore p Y := le_sSup ⟨hKn, hcop⟩
  rw [hO] at hle
  exact le_bot_iff.mp hle

theorem not_le_of_isStronglyPEmbedded {N K : Subgroup Y} [K.Normal] (hN : IsStronglyPEmbedded p N)
    (P : Sylow p Y) (hPN : (P : Subgroup Y) ≤ N) (hPK : (P : Subgroup Y) ⊓ K ≠ ⊥) (T : Sylow p ↥K)
    (hT : (T : Subgroup ↥K) = ((P : Subgroup Y) ⊓ K).subgroupOf K) : ¬ K ≤ N := by
  intro hKN
  have hTmap : (T : Subgroup ↥K).map K.subtype = (P : Subgroup Y) ⊓ K := by
    rw [hT, Subgroup.subgroupOf_map_subtype, inf_of_le_left inf_le_right]
  apply hN.1
  rw [eq_top_iff, ← Sylow.normalizer_sup_eq_top T, hTmap]
  exact sup_le (hN.normalizer_le hPK P.isPGroup'.to_inf_left (inf_le_left.trans hPN)) hKN

theorem glbCore_sylow_ne_top {N K : Subgroup Y} [K.Normal] (hN : IsStronglyPEmbedded p N)
    (P : Sylow p Y) (hPN : (P : Subgroup Y) ≤ N) (hPK : (P : Subgroup Y) ⊓ K ≠ ⊥) (T : Sylow p ↥K)
    (hT : (T : Subgroup ↥K) = ((P : Subgroup Y) ⊓ K).subgroupOf K) :
    GLBCore p 1 (T : Subgroup ↥K) ≠ ⊤ := by
  have hTmap : (T : Subgroup ↥K).map K.subtype = (P : Subgroup Y) ⊓ K := by
    rw [hT, Subgroup.subgroupOf_map_subtype, inf_of_le_left inf_le_right]
  have hle : GLBCore p 1 (T : Subgroup ↥K) ≤ N.subgroupOf K := by
    refine sSup_le ?_
    rintro M ⟨Q, hQT, hQ, rfl⟩ k hk
    rw [Subgroup.mem_subgroupOf]
    have hQne : Q.map K.subtype ≠ ⊥ := fun h =>
      ne_bot_of_one_le_pRank hQ ((Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective).1 h)
    have hQp : IsPGroup p ↥(Q.map K.subtype) := (T.isPGroup'.to_le hQT).map K.subtype
    have hQN : Q.map K.subtype ≤ N :=
      (Subgroup.map_mono hQT).trans (by rw [hTmap]; exact inf_le_left.trans hPN)
    exact hN.normalizer_le hQne hQp hQN
      (Subgroup.le_normalizer_map K.subtype (Subgroup.mem_map_of_mem K.subtype hk))
  intro htop
  rw [htop] at hle
  refine not_le_of_isStronglyPEmbedded hN P hPN hPK T hT fun k hk => ?_
  have h := hle (Subgroup.mem_top (⟨k, hk⟩ : ↥K))
  rwa [Subgroup.mem_subgroupOf] at h

theorem pRank_le_pRank_mulAut (K : Subgroup Y) [K.Normal] (hKC : centralizer (K : Set Y) = ⊥) :
    CFSG.Open.pRank p (⊤ : Subgroup Y) ≤ CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥K)) :=
  CFSG.SectionRank.pRank_top_le_of_injective hp.out.one_lt MulAut.conjNormal
    (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.CyclicOuter.conjNormal_injective K hKC)

theorem mem_of_forall_inner (K : Subgroup Y) [K.Normal] (hKC : centralizer (K : Set Y) = ⊥)
    (hinn : ∀ f : MulAut ↥K, (∃ n : ℕ, f ^ p ^ n = 1) → f ∈ (MulAut.conj : ↥K →* MulAut ↥K).range)
    {x : Y} {n : ℕ} (hx : x ^ p ^ n = 1) : x ∈ K := by
  obtain ⟨c, hc⟩ := hinn (MulAut.conjNormal x) ⟨n, by rw [← map_pow, hx, map_one]⟩
  have key : ∀ y : ↥K, (c : Y) * y * (c : Y)⁻¹ = x * y * x⁻¹ := by
    intro y
    have := congrArg (fun a : MulAut ↥K => ((a y : ↥K) : Y)) hc
    simpa [MulAut.conj_apply, MulAut.conjNormal_apply] using this
  have hcen : (c : Y)⁻¹ * x ∈ centralizer (K : Set Y) := by
    rw [mem_centralizer_iff]
    intro y hy
    have h1 : (c : Y) * y * (c : Y)⁻¹ = x * y * x⁻¹ := key ⟨y, hy⟩
    have h2 : (c : Y)⁻¹ * x * y * ((c : Y)⁻¹ * x)⁻¹ = y := by
      calc (c : Y)⁻¹ * x * y * ((c : Y)⁻¹ * x)⁻¹ = (c : Y)⁻¹ * (x * y * x⁻¹) * c := by group
        _ = (c : Y)⁻¹ * ((c : Y) * y * (c : Y)⁻¹) * c := by rw [h1]
        _ = y := by group
    calc y * ((c : Y)⁻¹ * x) = (c : Y)⁻¹ * x * y * ((c : Y)⁻¹ * x)⁻¹ * ((c : Y)⁻¹ * x) := by
          rw [h2]
      _ = (c : Y)⁻¹ * x * y := by group
  rw [hKC, Subgroup.mem_bot] at hcen
  have hxc : x = c := by
    calc x = (c : Y) * ((c : Y)⁻¹ * x) := by group
      _ = c := by rw [hcen, mul_one]
  exact hxc ▸ c.2

theorem mem_of_not_dvd_index (K : Subgroup Y) [K.Normal] (hK : ¬ p ∣ K.index) {x : Y} {n : ℕ}
    (hx : x ^ p ^ n = 1) : x ∈ K := by
  have h1 : (QuotientGroup.mk' K x) ^ p ^ n = 1 := by rw [← map_pow, hx, map_one]
  have h2 : orderOf (QuotientGroup.mk' K x) ∣ p ^ n := orderOf_dvd_of_pow_eq_one h1
  have h3 : orderOf (QuotientGroup.mk' K x) ∣ K.index := by
    rw [Subgroup.index_eq_card]
    exact orderOf_dvd_natCard _
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp.out).1 h2
  have h4 : orderOf (QuotientGroup.mk' K x) = 1 := by
    rcases k with _ | k
    · simpa using hk
    · exfalso
      rw [hk] at h3
      exact hK ((dvd_pow_self p (Nat.succ_ne_zero k)).trans h3)
  rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h4
  exact h4

theorem opp_le_of_forall {K : Subgroup Y} (h : ∀ (x : Y) (n : ℕ), x ^ p ^ n = 1 → x ∈ K) :
    UC22.Opp p (⊤ : Subgroup Y) ≤ K := by
  unfold UC22.Opp CFSG.RankThree.PartOne.pElementSubgroup
  refine (Subgroup.closure_le K).2 ?_
  rintro x ⟨-, k, hk⟩
  exact h x k (by rw [← hk]; exact pow_orderOf_eq_one x)

def mulEquivOfEqTop {K : Subgroup Y} (hK : K = ⊤) : ↥K ≃* Y :=
  (MulEquiv.subgroupCongr hK).trans Subgroup.topEquiv

end Reduction

end CFSG.LocalAnalysis.UniquenessCase.UCK
