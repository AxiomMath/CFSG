module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ui
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs11G
public import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem s11_TenP_pRank_bot {p : ℕ} (hp : 1 < p) :
    CFSG.Open.pRank p (⊥ : Subgroup G) = 0 := by
  apply Nat.eq_zero_of_le_zero
  refine CFSG.SectionRank.pRank_le hp ?_
  intro E hE _
  have hE' : E = ⊥ := le_bot_iff.1 hE
  simp [hE']

theorem s11_TenP_inf_normalizer_le {M P X : Subgroup G} {p : ℕ}
    (hXn : M ≤ normalizer (X : Set G)) :
    M ⊓ normalizer (P : Set G) ≤
      M ⊓ normalizer ((F11.Omega1p p (P ⊓ ⁅M, M⁆ ⊓ X) : Subgroup G) : Set G) := by
  refine le_inf inf_le_left fun g hg => ?_
  have hgT : g ∈ normalizer ((P ⊓ ⁅M, M⁆ ⊓ X : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨⟨hxP, hxc⟩, hxX⟩
      exact ⟨⟨(mem_normalizer_iff.1 hg.2 x).1 hxP,
          (mem_normalizer_iff.1 (uc22p22u_mem_normalizer_commutator hg.1) x).1 hxc⟩,
        (mem_normalizer_iff.1 (hXn hg.1) x).1 hxX⟩
    · rintro ⟨⟨hxP, hxc⟩, hxX⟩
      exact ⟨⟨(mem_normalizer_iff.1 hg.2 x).2 hxP,
          (mem_normalizer_iff.1 (uc22p22u_mem_normalizer_commutator hg.1) x).2 hxc⟩,
        (mem_normalizer_iff.1 (hXn hg.1) x).2 hxX⟩
  exact uc22p22u_mem_normalizer_Omega1p hgT

theorem s11_TenP_exists_mul {M P : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hP : CFSG.ABGLocalTools.IsSylowOf p P (F11.O2p p M)) :
    ∀ m ∈ M, ∃ u ∈ pCoreOf 2 M, ∃ n ∈ M ⊓ normalizer (P : Set G), m = u * n := by
  haveI : Fact p.Prime := ⟨hp⟩
  set O : Subgroup G := F11.O2p p M
  set H : Subgroup G := M ⊓ normalizer (P : Set G)
  have hOM : O ≤ M := uc22p21c_barPreimage_le M (CFSG.pCore p (Bar2 M))
  haveI : (CFSG.pCore p (Bar2 M)).Normal := CFSG.pCore_normal
  have hOn : M ≤ normalizer (O : Set G) := uc22p22u_barPreimage_normalizes
  have hHO : H ≤ normalizer (O : Set G) := inf_le_left.trans hOn
  have hbar : barImage M P = CFSG.pCore p (Bar2 M) := (uc22p22u_sylow_O2p hp hp2 hP).2.1
  have hPM : P ≤ M := (uc22p22u_sylow_O2p hp hp2 hP).1
  have hFr : M ≤ O ⊔ H := uc22p22t_frattini_sup hOM hOn hP
  intro m hm
  have hm' : m ∈ ((O ⊔ H : Subgroup G) : Set G) := hFr hm
  rw [Subgroup.coe_mul_of_right_le_normalizer_left O H hHO] at hm'
  rcases hm' with ⟨x, hxO, n, hnH, rfl⟩
  obtain ⟨hxM, hxbar⟩ := uc22p21c_mem_barPreimage.1 hxO
  rw [← hbar] at hxbar
  obtain ⟨y, hyP, hyx⟩ := uc22p21c_mem_barImage.1 hxbar
  have hdiff : (⟨x, hxM⟩ * y⁻¹ : ↥M) ∈ CFSG.pCore 2 ↥M := by
    refine (QuotientGroup.eq_one_iff _).1 ?_
    change uc22p21cPi M (⟨x, hxM⟩ * y⁻¹) = 1
    rw [map_mul, map_inv, hyx, mul_inv_cancel]
  have huO : x * (y : G)⁻¹ ∈ pCoreOf 2 M := ⟨⟨x, hxM⟩ * y⁻¹, hdiff, rfl⟩
  refine ⟨x * (y : G)⁻¹, huO, (y : G) * n, ?_, by group⟩
  refine ⟨M.mul_mem (hPM hyP) hnH.1, ?_⟩
  exact Subgroup.mul_mem _ (Subgroup.le_normalizer hyP) hnH.2

theorem s11_TenP_relIndex_eq_two_pow {M P : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hP : CFSG.ABGLocalTools.IsSylowOf p P (F11.O2p p M)) :
    ∃ k : ℕ, (M ⊓ normalizer (P : Set G)).relIndex M = 2 ^ k := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup G := M ⊓ normalizer (P : Set G)
  set O : Subgroup G := pCoreOf 2 M
  have hHM : H ≤ M := inf_le_left
  have hOM : O ≤ M := uc22p21c_pCoreOf_le M
  have hHOn : H ≤ normalizer (O : Set G) := hHM.trans fun m hm => by
    rw [mem_normalizer_iff]
    intro x
    constructor
    · exact uc22p21c_conj_mem_pCoreOf_self hm
    · intro hx
      have h := uc22p21c_conj_mem_pCoreOf_self (M.inv_mem hm) hx
      convert h using 1
      group
  have hMeq : H ⊔ O = M := by
    refine le_antisymm (sup_le hHM hOM) fun m hm => ?_
    obtain ⟨u, huO, n, hnH, rfl⟩ := s11_TenP_exists_mul hp hp2 hP m hm
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right huO) (Subgroup.mem_sup_left hnH)
  have hcard := CFSG.LocalAnalysis.EvenBN.Tits.N.card_sup_mul_card_inf' (H := H) (N := O) hHOn
  rw [hMeq] at hcard
  have hri : H.relIndex M * Nat.card H = Nat.card M := by
    have h := Subgroup.relIndex_mul_card H M
    rwa [inf_eq_left.2 hHM] at h
  have hkey : H.relIndex M * Nat.card ↥(H ⊓ O) = Nat.card O := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥H))
    calc (H.relIndex M * Nat.card ↥(H ⊓ O)) * Nat.card H
        = (H.relIndex M * Nat.card H) * Nat.card ↥(H ⊓ O) := by ring
      _ = Nat.card M * Nat.card ↥(H ⊓ O) := by rw [hri]
      _ = Nat.card H * Nat.card O := hcard
      _ = Nat.card O * Nat.card H := by ring
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 (uc22p21c_isPGroup_pCoreOf M)
  have hdvd : H.relIndex M ∣ 2 ^ a := by
    refine ⟨Nat.card ↥(H ⊓ O), ?_⟩
    rw [← ha]
    exact hkey.symm
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  exact ⟨k, hk⟩

theorem s11_TenP_exists_isSylowOf_le {M P : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hP : CFSG.ABGLocalTools.IsSylowOf p P (F11.O2p p M)) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    ∃ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf r S M ∧ S ≤ M ⊓ normalizer (P : Set G) := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨k, hk⟩ := s11_TenP_relIndex_eq_two_pow hp hp2 hP
  obtain ⟨S, hS⟩ := CFSG.ABGLocalTools.exists_isSylowOf r (M ⊓ normalizer (P : Set G))
  have hSH : S ≤ M ⊓ normalizer (P : Set G) := hS.le
  have hHM : M ⊓ normalizer (P : Set G) ≤ M := inf_le_left
  have hri : S.relIndex M = S.relIndex (M ⊓ normalizer (P : Set G)) *
      (M ⊓ normalizer (P : Set G)).relIndex M :=
    (Subgroup.relIndex_mul_relIndex S (M ⊓ normalizer (P : Set G)) M hSH hHM).symm
  have hSnot : ¬ r ∣ S.relIndex (M ⊓ normalizer (P : Set G)) :=
    (CFSG.ABGLocalTools.isSylowOf_iff.1 hS).2.2
  have hHnot : ¬ r ∣ (M ⊓ normalizer (P : Set G)).relIndex M := by
    rw [hk]
    intro hd
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow hd))
  refine ⟨S, CFSG.ABGLocalTools.isSylowOf_iff.2 ⟨hSH.trans hHM, hS.isPGroup, ?_⟩, hSH⟩
  rw [hri]
  intro hd
  rcases (Nat.Prime.dvd_mul hr).1 hd with h | h
  · exact hSnot h
  · exact hHnot h

theorem s11_TenP_pRank_inf_normalizer {M P X : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hP : CFSG.ABGLocalTools.IsSylowOf p P (F11.O2p p M)) (hXn : M ≤ normalizer (X : Set G))
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    CFSG.Open.pRank r
        (M ⊓ normalizer ((F11.Omega1p p (P ⊓ ⁅M, M⁆ ⊓ X) : Subgroup G) : Set G)) =
      CFSG.Open.pRank r M := by
  refine le_antisymm (CFSG.SectionRank.pRank_mono hr.one_lt inf_le_left) ?_
  obtain ⟨S, hS, hSH⟩ := s11_TenP_exists_isSylowOf_le hp hp2 hP hr hr2
  haveI : Fact r.Prime := ⟨hr⟩
  calc CFSG.Open.pRank r M ≤ CFSG.Open.pRank r S := uc22p22q_pRank_le_sylow hS
    _ ≤ CFSG.Open.pRank r (M ⊓ normalizer
          ((F11.Omega1p p (P ⊓ ⁅M, M⁆ ⊓ X) : Subgroup G) : Set G)) :=
        CFSG.SectionRank.pRank_mono hr.one_lt (hSH.trans (s11_TenP_inf_normalizer_le hXn))

theorem s11_TenP_exists_isSylowOf_le_normalizer {M P X : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hP : CFSG.ABGLocalTools.IsSylowOf p P (F11.O2p p M))
    (hXn : M ≤ normalizer (X : Set G)) :
    ∃ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p S M ∧
      F11.Omega1p p (P ⊓ ⁅M, M⁆ ⊓ X) ≤ S ∧
      S ≤ normalizer ((F11.Omega1p p (P ⊓ ⁅M, M⁆ ⊓ X) : Subgroup G) : Set G) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set Y : Subgroup G := F11.Omega1p p (P ⊓ ⁅M, M⁆ ⊓ X)
  set H : Subgroup G := M ⊓ normalizer (P : Set G)
  have hPM : P ≤ M := (uc22p22u_sylow_O2p hp hp2 hP).1
  obtain ⟨S, hSM, hSH⟩ := s11_TenP_exists_isSylowOf_le hp hp2 hP hp hp2
  have hHM : H ≤ M := inf_le_left
  have hSylH : CFSG.ABGLocalTools.IsSylowOf p S H := hSM.of_le hSH hHM
  have hPH : P ≤ H := le_inf hPM Subgroup.le_normalizer
  haveI : (P.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPH).2 inf_le_right
  have hPsub : IsPGroup p (P.subgroupOf H) := hP.isPGroup.comap_subtype
  obtain ⟨S₀, hS₀⟩ := hSylH.exists_sylow_eq_subgroupOf
  have hle : P.subgroupOf H ≤ (S₀ : Subgroup ↥H) := IsPGroup.le_sylow_of_normal hPsub S₀
  have hPS : P ≤ S := by
    intro x hx
    have hx' : (⟨x, hPH hx⟩ : ↥H) ∈ P.subgroupOf H := Subgroup.mem_subgroupOf.2 hx
    have h1 := hle hx'
    rw [hS₀] at h1
    exact Subgroup.mem_subgroupOf.1 h1
  have hYT : Y ≤ P ⊓ ⁅M, M⁆ ⊓ X :=
    (Subgroup.closure_le (P ⊓ ⁅M, M⁆ ⊓ X)).2 fun x hx => hx.1
  have hTP : (P ⊓ ⁅M, M⁆ ⊓ X : Subgroup G) ≤ P := by
    calc P ⊓ ⁅M, M⁆ ⊓ X ≤ P ⊓ ⁅M, M⁆ := inf_le_left
      _ ≤ P := inf_le_left
  refine ⟨S, hSM, hYT.trans (hTP.trans hPS), ?_⟩
  exact (hSH.trans (s11_TenP_inf_normalizer_le hXn)).trans inf_le_right

theorem s11_TenP_permutes {M P X T : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hP : CFSG.ABGLocalTools.IsSylowOf p P (F11.O2p p M)) (hXn : M ≤ normalizer (X : Set G))
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) :
    Permutes (F11.Omega1p p (P ⊓ ⁅M, M⁆ ⊓ X)) T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y : Subgroup G := F11.Omega1p p (P ⊓ ⁅M, M⁆ ⊓ X)
  have hYT : Y ≤ P ⊓ ⁅M, M⁆ ⊓ X :=
    (Subgroup.closure_le (P ⊓ ⁅M, M⁆ ⊓ X)).2 fun x hx => hx.1
  have hTP : (P ⊓ ⁅M, M⁆ ⊓ X : Subgroup G) ≤ P := by
    calc P ⊓ ⁅M, M⁆ ⊓ X ≤ P ⊓ ⁅M, M⁆ := inf_le_left
      _ ≤ P := inf_le_left
  have hYP : Y ≤ P := hYT.trans hTP
  have hYM : Y ≤ M := hYP.trans (uc22p22u_sylow_O2p hp hp2 hP).1
  have hOT : pCoreOf 2 M ≤ T := by
    obtain ⟨S, hS⟩ := hT.exists_sylow_eq_subgroupOf
    have h := CFSG.fitting_pCore_le_sylow S
    rw [hS] at h
    exact Subgroup.map_le_iff_le_comap.2 h
  have hFirst : (Y : Set G) * (T : Set G) ⊆ (T : Set G) * (Y : Set G) := by
    rintro z ⟨y, hy, t, ht, rfl⟩
    have hyM : y ∈ M := hYM hy
    have htM : t ∈ M := hT.le ht
    obtain ⟨u, huO, n, hnH, htn⟩ := s11_TenP_exists_mul hp hp2 hP t⁻¹ (M.inv_mem htM)
    have hnY : n ∈ normalizer (Y : Set G) := (s11_TenP_inf_normalizer_le hXn hnH).2
    have hy' : n * y * n⁻¹ ∈ Y := (mem_normalizer_iff.1 hnY y).1 hy
    have hy'M : n * y * n⁻¹ ∈ M := hYM hy'
    have ht' : t = (u * n)⁻¹ := by rw [← htn]; group
    have hconj : t⁻¹ * y * t = u * (n * y * n⁻¹) * u⁻¹ := by
      rw [ht']
      group
    have hkO : u * ((n * y * n⁻¹) * u⁻¹ * (n * y * n⁻¹)⁻¹) ∈ pCoreOf 2 M :=
      (pCoreOf 2 M).mul_mem huO
        (uc22p21c_conj_mem_pCoreOf_self hy'M ((pCoreOf 2 M).inv_mem huO))
    have hkT : u * ((n * y * n⁻¹) * u⁻¹ * (n * y * n⁻¹)⁻¹) ∈ T := hOT hkO
    have hgoal : (t * (u * ((n * y * n⁻¹) * u⁻¹ * (n * y * n⁻¹)⁻¹))) *
        (n * y * n⁻¹) = y * t := by
      have h1 : t⁻¹ * y * t =
          (u * ((n * y * n⁻¹) * u⁻¹ * (n * y * n⁻¹)⁻¹)) * (n * y * n⁻¹) := by
        rw [hconj]; group
      have h2 := congrArg (fun w => t * w) h1
      simpa [mul_assoc] using h2.symm
    exact ⟨t * (u * ((n * y * n⁻¹) * u⁻¹ * (n * y * n⁻¹)⁻¹)), T.mul_mem ht hkT,
      n * y * n⁻¹, hy', hgoal⟩
  have hSecond : (T : Set G) * (Y : Set G) ⊆ (Y : Set G) * (T : Set G) := by
    rintro z ⟨t, ht, y, hy, rfl⟩
    have hmem : (t * y)⁻¹ ∈ (Y : Set G) * (T : Set G) :=
      ⟨y⁻¹, Y.inv_mem hy, t⁻¹, T.inv_mem ht, by group⟩
    obtain ⟨t', ht', y', hy', heq⟩ := hFirst hmem
    have hEq : y'⁻¹ * t'⁻¹ = t * y := by
      have h := congrArg Inv.inv heq
      have h' : (t' * y')⁻¹ = t * y := by simpa using h
      rwa [mul_inv_rev] at h'
    exact ⟨y'⁻¹, Y.inv_mem hy', t'⁻¹, T.inv_mem ht', hEq⟩
  unfold Permutes
  exact Set.Subset.antisymm hFirst hSecond

theorem s11_TenP_rankThreeGamma_le (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) (h77 : F07.R77Eq D) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Y : Subgroup G} (hYM : Y ≤ D.M) (hYp : IsPGroup p Y) (hYnc : ¬ IsCyclic Y)
    (hYexp : ∀ x ∈ Y, x ^ p = 1) (hYcl : ⁅⁅Y, Y⁆, Y⁆ = ⊥)
    (hrk : ∀ q ∈ D.sig, CFSG.Open.pRank q (D.M ⊓ normalizer (Y : Set G)) =
      CFSG.Open.pRank q D.M) :
    rankThreeGamma 1 p Y ≤ D.M := by
  by_cases hpσ : p ∈ D.sig
  · haveI : Fact p.Prime := ⟨hp⟩
    have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M :=
      hSg.sig1_sp p (h1219 ▸ hpσ)
    unfold rankThreeGamma
    refine CFSG.HardMathSupport.Solomon.Proving.GLBCore_le_of_forall fun Q hQY hQ1 => ?_
    have hQne : Q ≠ ⊥ := by
      intro hb
      rw [hb, s11_TenP_pRank_bot hp.one_lt] at hQ1
      omega
    exact CFSG.RankThree.PartOne.IsStronglyPEmbedded.normalizer_le hsp hQne (hYp.to_le hQY)
      (hQY.trans hYM)
  · obtain ⟨q, hq⟩ := hSg.nonempty
    have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded q D.M :=
      hSg.sig1_sp q (h1219 ▸ hq)
    obtain ⟨-, hq2⟩ := D.sig_prime q hq
    have h2 : 2 < CFSG.Open.pRank q (D.M ⊓ normalizer (Y : Set G)) := by
      rw [hrk q hq]
      exact lt_of_lt_of_le (by norm_num) (hSg.three_le q hq)
    exact h77 h1219.subset q hq hq2 hsp p hp hp2 hpσ Y hYM hYp hYnc hYexp hYcl h2 (hrk q hq).symm

theorem s11_TenP_inP11 (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h1110 : R1110G D) (h77 : F07.R77Eq D) {V₀ V : Subgroup G} (h11 : F11.Hyp11 D V₀ V)
    [((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {n : ℕ} (hn : 1 < n) (Xbar : Subgroup (F11.MBar11 D.M V₀ V)) (hXn : Xbar.Normal)
    (hXe : IsElemAbelian p Xbar) (hXc : Nat.card Xbar = p ^ n)
    (hXd : Xbar ≤ ⁅(⊤ : Subgroup (F11.MBar11 D.M V₀ V)), ⊤⁆) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf p P (F11.O2p p D.M)) :
    F11.InP11 D (F11.Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M V₀ V Xbar)) := by
  haveI := hXn
  set Y : Subgroup G := F11.Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M V₀ V Xbar)
  have hXn' : D.M ≤ normalizer ((F11.barPreimage11 D.M V₀ V Xbar : Subgroup G) : Set G) :=
    fun g hg => uc22p22u_mem_normalizer_barPreimage11 hg
  obtain ⟨hexp, hcl, hcard, hrk⟩ :=
    ((h1110 V₀ V h11 p hp hp2 P hP).2.2 n hn Xbar hXn hXe hXc hXd).1
  have hPM : P ≤ D.M := (uc22p22u_sylow_O2p hp hp2 hP).1
  have hYT : Y ≤ P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M V₀ V Xbar :=
    (Subgroup.closure_le (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M V₀ V Xbar)).2 fun x hx => hx.1
  have hTP : (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M V₀ V Xbar : Subgroup G) ≤ P := by
    calc P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M V₀ V Xbar ≤ P ⊓ ⁅D.M, D.M⁆ := inf_le_left
      _ ≤ P := inf_le_left
  have hYP : Y ≤ P := hYT.trans hTP
  have hYM : Y ≤ D.M := hYP.trans hPM
  have hYp : IsPGroup p Y := hP.isPGroup.to_le hYP
  have hYnc : ¬ IsCyclic ↥Y := by
    intro hc
    haveI := hc
    have h1 : Monoid.exponent ↥Y ∣ p :=
      Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext (hexp g.1 g.2)
    rw [IsCyclic.exponent_eq_card] at h1
    have h2 : Nat.card ↥Y ≤ p := Nat.le_of_dvd hp.pos h1
    have h3 : p ^ 2 ≤ Nat.card ↥Y := (Nat.pow_le_pow_right hp.pos (by omega : 2 ≤ n)).trans hcard
    have h4 : p < p ^ 2 := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  have hYcl : ⁅⁅Y, Y⁆, Y⁆ = ⊥ := by
    rcases hcl with hcomm | ⟨-, hle⟩
    · have hb : ⁅Y, Y⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2
        ((Subgroup.le_centralizer_iff_isMulCommutative).2 hcomm)
      rw [hb, Subgroup.commutator_bot_left]
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 (hle.trans inf_le_right)
  have hΓ : rankThreeGamma 1 p Y ≤ D.M :=
    s11_TenP_rankThreeGamma_le D hSg h1219 h77 hp hp2 hYM hYp hYnc hexp hYcl
      (fun q hq => s11_TenP_pRank_inf_normalizer hp hp2 hP hXn' (D.sig_prime q hq).1
        (D.sig_prime q hq).2)
  refine ⟨p, hp, hp2, hYM, hYp, hexp, hYnc, ?_, hΓ, Or.inr ?_⟩
  · exact s11_TenP_permutes hp hp2 hP hXn' D.sylowM
  · exact ⟨Y, hYnc, s11_TenP_exists_isSylowOf_le_normalizer hp hp2 hP hXn', hΓ⟩

theorem s11_TenP_card_lt_eight (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h1110 : R1110G D) (h77 : F07.R77Eq D) {V₀ V : Subgroup G} (h11 : F11.Hyp11 D V₀ V)
    [((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {n : ℕ} (hn : 1 < n) (Xbar : Subgroup (F11.MBar11 D.M V₀ V)) (hXn : Xbar.Normal)
    (hXe : IsElemAbelian p Xbar) (hXc : Nat.card Xbar = p ^ n)
    (hXd : Xbar ≤ ⁅(⊤ : Subgroup (F11.MBar11 D.M V₀ V)), ⊤⁆) :
    Nat.card V₀ < 8 := by
  by_contra h8
  rw [not_lt] at h8
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf p (F11.O2p p D.M)
  exact (h11.2.2 h8).2 _
    (s11_TenP_inP11 D hSg h1219 h1110 h77 h11 hp hp2 hn Xbar hXn hXe hXc hXd hP)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
