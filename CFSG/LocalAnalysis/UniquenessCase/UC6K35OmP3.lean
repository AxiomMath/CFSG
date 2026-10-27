module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K35Red2
public import CFSG.LocalAnalysis.UniquenessCase.UC6K35OmRows
public import CFSG.LocalAnalysis.UniquenessCase.UC6K35OmAut
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Gls3Plus
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.RankThree.PartOne.S12.Sec1511SPEFStar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree

theorem blueprintLieModel_of_models_classical {G : Type} [Group G] {t : StatedLieTag} {n p f : ℕ}
    (hm : CFSG.Models.LieModel G t n p f) (ht : t = .PSL ∨ t = .PSU) (hn : n ≠ 0) :
    LieModel G t n p f := by
  obtain ⟨-, hcl | ⟨h0, -⟩⟩ := hm
  · exact Or.inl ⟨by rcases ht with rfl | rfl <;> decide, hcl⟩
  · exact absurd h0 hn

theorem lieModel_psl_of_isoLie {G : Type} [Group G] {r : ℕ} {q : TauCeti.PrimePower}
    (h : CFSG.RankThree.PartOne.Census3.IsoLie G (.A r q)) :
    LieModel G .PSL (r + 1) q.p q.exponent := by
  obtain ⟨hv, ⟨e⟩⟩ := h
  exact blueprintLieModel_of_models_classical (CFSG.Models.lieModel_A r q hv e) (Or.inl rfl)
    (Nat.succ_ne_zero r)

theorem k35Ω_three (hG : Gls3StronglyThreeEmbeddedPlus)
    (hbr : ∀ s : TauCeti.SporadicName,
      Nonempty (CFSG.Blueprint.NativeSporadic.Carrier s ≃* (TauCeti.CFSGIndex.sporadic s).Group))
    {X : Type} [Group X] [Finite X] (hX : CFSG.Open.IsKGroup X) {p : ℕ} (hp3 : p = 3)
    (hopp : Opp p (⊤ : Subgroup X) = ⊤) (hO : CFSG.pPrimeCore p X = ⊥) {N : Subgroup X}
    (hN : IsStronglyPEmbedded p N) {S B : Subgroup X} (hS : CFSG.ABGLocalTools.IsSylowOf p S ⊤)
    (hBS : B ≤ S) (hB : CFSG.Open.IsElemAbelian p B) (hBcard : Nat.card B = p ^ 2)
    (hΩ : ∀ x ∈ S, x ^ p = 1 → x ∈ B) (hBc : ∀ b ∈ B, ∀ y ∈ S, b * y = y * b) :
    IsSimpleGroup X ∧ (LieModel X .PSL 2 p 2 ∨ IsAlt X (2 * p) ∨
      (p = 3 ∧ (IsSpor X .M11 ∨ LieModel X .PSL 3 2 2)) ∨
      (p = 5 ∧ (LieModel X .Tits 0 2 1 ∨ IsSpor X .Fi22))) := by
  subst hp3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hKs, hKnab, hKn, hKC⟩ := CFSG.RankThree.PartOne.Sec1511.spe_fstar Nat.prime_three hO hN
  set K := CFSG.generalizedFitting X with hKdef
  haveI : K.Normal := hKn
  haveI : IsSimpleGroup ↥K := hKs
  obtain ⟨U, hU⟩ := exists_sylow_coe_eq hS
  obtain ⟨g, hg⟩ := hN.exists_conj_ge (CFSG.ABGLocalTools.isSylowOf_iff.1 hS)
  have hN' := hN.conj g
  have hrk : 2 ≤ CFSG.Open.pRank 3 (U : Subgroup X) := by
    rw [hU]
    exact CFSG.SectionRank.le_pRank (by norm_num) hBS hB hBcard
  have hΓ : gammaCore 3 1 ⊤ (U : Subgroup X) < ⊤ := by
    refine lt_top_iff_ne_top.2 fun h => hN'.1 (top_le_iff.1 ?_)
    rw [← h]
    exact gammaCore_le_of_isStronglyPEmbedded hN' U.isPGroup' (by rw [hU]; exact hg)
  obtain ⟨-, -, hrows⟩ := hG X hX K hKn hKs hKnab hKC U hrk hΓ
  rw [hU] at hrows
  have hXK : ¬ 3 ∣ K.index → K = ⊤ := fun hidx => by
    have h := opp_le_of_forall (p := 3) (K := K) fun x n hx => mem_of_not_dvd_index K hidx hx
    rw [hopp] at h
    exact top_le_iff.1 h
  have hSK : ¬ 3 ∣ K.index → S ≤ K := fun hidx x hx => by
    obtain ⟨n, hn⟩ := hS.isPGroup ⟨x, hx⟩
    exact mem_of_not_dvd_index K hidx (n := n) (by simpa using congrArg Subtype.val hn)
  have hsimp : K = ⊤ → IsSimpleGroup X := fun hK => (mulEquivOfEqTop hK).symm.isSimpleGroup
  have hE9 : ∀ {E : Subgroup X}, CFSG.Open.IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 2 :=
    fun hE => card_le_sq_of_omega hS hBcard hΩ hE
  have hab27 : Nat.card S = 27 → ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := fun h27 =>
    comm_of_central_index_prime (p := 3) hBS hBc (by rw [h27, hBcard]; norm_num)
  rcases hrows with ⟨q, hq3, hiso, hidx, -, -, hel, hcard⟩ |
      ⟨q, hq3, -, hidx, -, -, hnc, hcard, E, -, hE, hEcard⟩ | ⟨m, hiso, -, -, -, E, -, hE, hEcard⟩ |
      ⟨-, -, -, -, -, -, h27, hnc⟩ | ⟨⟨φ, -⟩, hidx, -⟩ | ⟨hiso, ⟨k, hk⟩, -⟩ | ⟨⟨f⟩, hKtop, -⟩
  ·
    have hK := hXK hidx
    have hL := lieModel_psl_of_isoLie hiso
    obtain ⟨-, he1, -, -, h23⟩ := hL.admissible
    have hqc : q.card = 3 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hq3]
    have h9 : 3 ^ q.exponent ≤ 3 ^ 2 := by rw [← hqc, ← hcard]; exact hE9 hel
    have he3 : q.exponent < 3 := by
      by_contra h
      have h' := (Nat.pow_le_pow_right (by norm_num : 0 < 3) (not_lt.mp h)).trans h9
      norm_num at h'
    have he : q.exponent = 2 := by
      rw [hq3] at h23
      interval_cases hqe : q.exponent
      · exact (h23 rfl).elim
      · rfl
    refine ⟨hsimp hK, Or.inl ?_⟩
    rw [hq3, he] at hL
    exact hL.of_mulEquiv (mulEquivOfEqTop hK)
  ·
    exfalso
    have hSK' := hSK hidx
    have hq2 : q.card ^ 2 ≤ 3 ^ 2 := by rw [← hEcard]; exact hE9 hE
    have hq : q.card = 3 := by
      have h1 : q.card ≤ 3 := by
        by_contra h
        exact absurd ((Nat.pow_lt_pow_left (not_le.mp h) (by norm_num : (2 : ℕ) ≠ 0)).trans_le hq2)
          (lt_irrefl _)
      have h2 : 3 ≤ q.card := by
        rw [TauCeti.PrimePower.card_def, hq3]
        exact Nat.le_self_pow q.exponent_pos.ne' 3
      omega
    have h27 : Nat.card S = 27 := by
      rw [← inf_of_le_left hSK', hcard, hq]
      norm_num
    exact hnc fun a ha b hb => hab27 h27 a ha.1 b hb.1
  ·
    exfalso
    obtain ⟨hv, -⟩ := hiso
    have hm : 1 ≤ m := by
      have h := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
      simpa only [TauCeti.LieTypeIndex.inStandardRange_iff] using h
    have h1 := hE9 hE
    rw [hEcard] at h1
    have h' := (Nat.pow_le_pow_right (by norm_num : 0 < 3) (by omega : 3 ≤ 2 * m + 1)).trans h1
    norm_num at h'
  ·
    exact absurd (fun a ha b hb => hab27 h27 a ha b hb) hnc
  ·
    have hK := hXK hidx
    exact ⟨hsimp hK, Or.inr (Or.inl
      (show Nonempty (X ≃* alternatingGroup (Fin (2 * 3))) from ⟨(mulEquivOfEqTop hK).symm.trans φ⟩))⟩
  ·
    have hidx : ¬ 3 ∣ K.index := fun h => by
      rw [hk] at h
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h) (by norm_num)
    have hK := hXK hidx
    exact ⟨hsimp hK, Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr
      ((lieModel_psl_of_isoLie hiso).of_mulEquiv (mulEquivOfEqTop hK))⟩))⟩
  ·
    exact ⟨hsimp hKtop, Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl
      (show Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11) from
        ⟨(mulEquivOfEqTop hKtop).symm.trans (f.trans (hbr .M11).some.symm)⟩)⟩))⟩

end CFSG.LocalAnalysis.UniquenessCase.UCK
