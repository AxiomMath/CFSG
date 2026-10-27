module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsFitting
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsComponents
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsRootModule
public import CFSG.GroupTheory.OddPGroupNoncyclicChar
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ug
public import CFSG.LocalAnalysis.UniquenessCase.UC6Mod2
public import CFSG.LocalAnalysis.UniquenessCase.UC22BarLemmas
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private def uc22s2343_Pq (D : Data G) (q : ℕ) : Subgroup G :=
  barPreimage D.M (CFSG.pCore q (Bar2 D.M))

private theorem uc22s2343_Pq_le_M (D : Data G) (q : ℕ) : uc22s2343_Pq D q ≤ D.M :=
  uc22p21c_barPreimage_le D.M _

private theorem uc22s2343_Pq_normalizes (D : Data G) (q : ℕ) :
    D.M ≤ normalizer ((uc22s2343_Pq D q : Subgroup G) : Set G) := by
  unfold uc22s2343_Pq
  exact uc22p22u_barPreimage_normalizes

private theorem uc22s2343_Pq_normal (D : Data G) (q : ℕ) :
    ((uc22s2343_Pq D q).subgroupOf D.M).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (uc22s2343_Pq_le_M D q)).2
    (uc22s2343_Pq_normalizes D q)

private theorem uc22s2343_Pq_le_oTwoFOf (D : Data G) (q : ℕ) [Fact q.Prime] :
    uc22s2343_Pq D q ≤ oTwoFOf D.M := by
  unfold uc22s2343_Pq oTwoFOf
  exact barPreimage_mono (CFSG.pCore_le_fitting (Bar2 D.M) q)

private theorem uc22s2343_Pq_le_N (D : Data G) (Ch : Choice2011 G) (h42 : S23_42 D Ch)
    (h1930 : H1930 D) (c : Ctx23L D Ch) (q : ℕ) [Fact q.Prime] :
    uc22s2343_Pq D q ≤ c.N :=
  (uc22s2343_Pq_le_oTwoFOf D q).trans (h42 h1930 c)

private theorem uc22s2343_sylow_barImage (D : Data G) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {Q0 : Subgroup G} (hQ0 : CFSG.ABGLocalTools.IsSylowOf q Q0 (uc22s2343_Pq D q)) :
    barImage D.M Q0 = CFSG.pCore q (Bar2 D.M) ∧ Q0 ⊓ pCoreOf 2 D.M = ⊥ := by
  unfold uc22s2343_Pq at hQ0
  exact uc22p22u_sylow_barPreimage hq hq2 (CFSG.pCore_isPGroup (p := q)) hQ0

private theorem uc22s2343_pCoreOf_le_Pq (D : Data G) (q : ℕ) :
    pCoreOf 2 D.M ≤ uc22s2343_Pq D q :=
  pCoreOf_le_barPreimage D.M _

private theorem uc22s2343_Pq_eq_sup (D : Data G) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {Q0 : Subgroup G} (hQ0 : CFSG.ABGLocalTools.IsSylowOf q Q0 (uc22s2343_Pq D q)) :
    uc22s2343_Pq D q = pCoreOf 2 D.M ⊔ Q0 := by
  have hbar := (uc22s2343_sylow_barImage D hq hq2 hQ0).1
  have hQ0M : Q0 ≤ D.M := hQ0.le.trans (uc22s2343_Pq_le_M D q)
  refine le_antisymm ?_ (sup_le (uc22s2343_pCoreOf_le_Pq D q) hQ0.le)
  intro x hx
  obtain ⟨hxM, hxY⟩ := uc22p21c_mem_barPreimage.1 hx
  have hxbar : uc22p21cPi D.M ⟨x, hxM⟩ ∈ barImage D.M Q0 := by
    rw [hbar]; exact hxY
  obtain ⟨y, hyQ0, hyx⟩ := uc22p21c_mem_barImage.1 hxbar
  have ho : x * (y : G)⁻¹ ∈ pCoreOf 2 D.M := by
    change ((⟨x, hxM⟩ * (y : ↥D.M)⁻¹ : ↥D.M) : G) ∈ pCoreOf 2 D.M
    rw [CFSG.mem_openPCoreOf_iff]
    exact (QuotientGroup.eq_one_iff (⟨x, hxM⟩ * (y : ↥D.M)⁻¹)).1 (by
      change uc22p21cPi D.M (⟨x, hxM⟩ * (y : ↥D.M)⁻¹) = 1
      rw [map_mul, map_inv, hyx, mul_inv_cancel])
  have hx' : x = (x * (y : G)⁻¹) * (y : G) := by group
  rw [hx']
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ho) (Subgroup.mem_sup_right hyQ0)

open CFSG.LocalAnalysis.UniquenessCase.UC6 in
private theorem uc22s2343_T_eq_sup (D : Data G) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {Q0 : Subgroup G} (hQ0 : CFSG.ABGLocalTools.IsSylowOf q Q0 (uc22s2343_Pq D q)) :
    D.T = pCoreOf 2 D.M ⊔ (D.T ⊓ Subgroup.normalizer (Q0 : Set G)) := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hPqM : uc22s2343_Pq D q ≤ D.M := uc22s2343_Pq_le_M D q
  have hPqNorm : D.M ≤ Subgroup.normalizer ((uc22s2343_Pq D q : Subgroup G) : Set G) :=
    uc22s2343_Pq_normalizes D q
  have hFr : D.M = uc22s2343_Pq D q ⊔ (D.M ⊓ Subgroup.normalizer (Q0 : Set G)) :=
    UC6.frattini_of_isSylowOf hPqM hPqNorm hQ0
  have hPqEq : uc22s2343_Pq D q = pCoreOf 2 D.M ⊔ Q0 :=
    uc22s2343_Pq_eq_sup D hq hq2 hQ0
  have hQ0M : Q0 ≤ D.M := hQ0.le.trans hPqM
  have hM : D.M = pCoreOf 2 D.M ⊔ (D.M ⊓ Subgroup.normalizer (Q0 : Set G)) := by
    calc D.M = uc22s2343_Pq D q ⊔ (D.M ⊓ Subgroup.normalizer (Q0 : Set G)) := hFr
      _ = (pCoreOf 2 D.M ⊔ Q0) ⊔ (D.M ⊓ Subgroup.normalizer (Q0 : Set G)) := by rw [hPqEq]
      _ = pCoreOf 2 D.M ⊔ (Q0 ⊔ (D.M ⊓ Subgroup.normalizer (Q0 : Set G))) := sup_assoc _ _ _
      _ = pCoreOf 2 D.M ⊔ (D.M ⊓ Subgroup.normalizer (Q0 : Set G)) := by
        rw [sup_eq_right.mpr (le_inf hQ0M (show Q0 ≤ Subgroup.normalizer (Q0 : Set G) from
          Subgroup.le_normalizer))]
  have hOT : pCoreOf 2 D.M ≤ D.T := uc22p22e_pCoreOf_le_T D
  have hMnormO : D.M ≤ Subgroup.normalizer (pCoreOf 2 D.M : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M
  set O : Subgroup G := pCoreOf 2 D.M with hO
  set N' : Subgroup G := D.M ⊓ Subgroup.normalizer (Q0 : Set G) with hN'
  have hN'O : N' ≤ Subgroup.normalizer (O : Set G) := inf_le_left.trans hMnormO
  have hMset : (D.M : Set G) = (O : Set G) * (N' : Set G) := by
    rw [hM, hO, hN']
    exact Subgroup.coe_mul_of_right_le_normalizer_left O N' hN'O
  have hTN' : D.T = O ⊔ (D.T ⊓ N') := by
    apply le_antisymm
    · intro x hx
      have hxM : x ∈ D.M := D.sylowM.le hx
      change x ∈ (D.M : Set G) at hxM
      rw [hMset] at hxM
      obtain ⟨o, ho, n, hn, hxeq⟩ := Set.mem_mul.1 hxM
      have hnT : n ∈ D.T := by
        have h1 : o⁻¹ * (o * n) ∈ D.T :=
          D.T.mul_mem (D.T.inv_mem (hOT ho)) (hxeq ▸ hx)
        simpa using h1
      rw [← hxeq]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ho)
        (Subgroup.mem_sup_right (Subgroup.mem_inf.2 ⟨hnT, hn⟩))
    · exact sup_le hOT inf_le_left
  rwa [hO, hN', ← inf_assoc, inf_eq_left.mpr D.sylowM.le] at hTN'

private theorem uc22s2343_permutes (D : Data G) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {Q0 Q : Subgroup G} (hQ0 : CFSG.ABGLocalTools.IsSylowOf q Q0 (uc22s2343_Pq D q))
    (hQle : Q ≤ Q0) (hNQG : Subgroup.normalizer (Q0 : Set G) ≤
      Subgroup.normalizer (Q : Set G)) :
    Permutes D.T Q := by
  set O : Subgroup G := pCoreOf 2 D.M with hO
  set N : Subgroup G := D.T ⊓ Subgroup.normalizer (Q0 : Set G) with hN
  have hT : D.T = O ⊔ N := uc22s2343_T_eq_sup D hq hq2 hQ0
  have hMnormO : D.M ≤ Subgroup.normalizer (O : Set G) := by
    rw [hO]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M
  have hNT : N ≤ D.T := hN ▸ inf_le_left
  have hNO : N ≤ Subgroup.normalizer (O : Set G) := hNT.trans (D.sylowM.le.trans hMnormO)
  have hQO : Q ≤ Subgroup.normalizer (O : Set G) :=
    (hQle.trans hQ0.le).trans ((uc22s2343_Pq_le_M D q).trans hMnormO)
  have hNQ0 : N ≤ Subgroup.normalizer (Q0 : Set G) := inf_le_right
  have hNQ : N ≤ Subgroup.normalizer (Q : Set G) := hNQ0.trans hNQG
  have hTset : (D.T : Set G) = (N : Set G) * (O : Set G) := by
    rw [hT, sup_comm]
    exact Subgroup.coe_mul_of_left_le_normalizer_right N O hNO
  have hOQ : (O : Set G) * (Q : Set G) = (Q : Set G) * (O : Set G) := by
    calc (O : Set G) * (Q : Set G) = ((O ⊔ Q : Subgroup G) : Set G) :=
          (Subgroup.coe_mul_of_right_le_normalizer_left O Q hQO).symm
      _ = ((Q ⊔ O : Subgroup G) : Set G) := by rw [sup_comm]
      _ = (Q : Set G) * (O : Set G) := Subgroup.coe_mul_of_left_le_normalizer_right Q O hQO
  have hNQset : (N : Set G) * (Q : Set G) = (Q : Set G) * (N : Set G) := by
    calc (N : Set G) * (Q : Set G) = ((N ⊔ Q : Subgroup G) : Set G) :=
          (Subgroup.coe_mul_of_left_le_normalizer_right N Q hNQ).symm
      _ = ((Q ⊔ N : Subgroup G) : Set G) := by rw [sup_comm]
      _ = (Q : Set G) * (N : Set G) := Subgroup.coe_mul_of_right_le_normalizer_left Q N hNQ
  unfold Permutes
  calc (D.T : Set G) * (Q : Set G) = ((N : Set G) * (O : Set G)) * (Q : Set G) := by rw [hTset]
    _ = (N : Set G) * ((O : Set G) * (Q : Set G)) := mul_assoc _ _ _
    _ = (N : Set G) * ((Q : Set G) * (O : Set G)) := by rw [hOQ]
    _ = ((N : Set G) * (Q : Set G)) * (O : Set G) := (mul_assoc _ _ _).symm
    _ = ((Q : Set G) * (N : Set G)) * (O : Set G) := by rw [hNQset]
    _ = (Q : Set G) * ((N : Set G) * (O : Set G)) := mul_assoc _ _ _
    _ = (Q : Set G) * (D.T : Set G) := by rw [hTset]

private theorem uc22s2343_permutes_omegaCenter (D : Data G) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {Q0 : Subgroup G} (hQ0 : CFSG.ABGLocalTools.IsSylowOf q Q0 (uc22s2343_Pq D q)) :
    Permutes D.T (CFSG.LocalAnalysis.UniquenessCase.UC6.omegaCenter q Q0) :=
  uc22s2343_permutes D hq hq2 hQ0
    (CFSG.LocalAnalysis.UniquenessCase.UC6.omegaCenter_le q Q0)
    (CFSG.LocalAnalysis.UniquenessCase.UC6.normalizer_le_normalizer_omegaCenter q Q0)

private theorem uc22s2343_coprime_card_Pq (D : Data G) {q p : ℕ} (hq : q.Prime)
    (hp : p.Prime) (hpq : p ≠ q) (hp2 : p ≠ 2) :
    Nat.Coprime p (Nat.card ↥(uc22s2343_Pq D q)) := by
  rw [Nat.Prime.coprime_iff_not_dvd hp]
  intro hdvd
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hPqM : uc22s2343_Pq D q ≤ D.M := uc22s2343_Pq_le_M D q
  let φ : ↥(uc22s2343_Pq D q) →* Bar2 D.M :=
    (uc22p21cPi D.M).comp (Subgroup.inclusion hPqM)
  have hφx : φ x ∈ CFSG.pCore q (Bar2 D.M) :=
    (uc22p21c_mem_barPreimage.1 x.2).2
  let z : ↥(CFSG.pCore q (Bar2 D.M)) := ⟨φ x, hφx⟩
  have hzord : orderOf z ∣ p := by
    rw [← hxord]
    have := orderOf_map_dvd φ x
    simpa [z] using this
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 (CFSG.pCore_isPGroup (p := q) (G := Bar2 D.M))) z
  have hzord' : orderOf z = q ^ k := hk
  have hqk_dvd_p : q ^ k ∣ p := hzord' ▸ hzord
  cases k with
  | zero =>
      have hz1 : z = 1 := orderOf_eq_one_iff.1 (by simpa using hzord')
      have hxO : (x : G) ∈ pCoreOf 2 D.M := by
        refine ⟨Subgroup.inclusion hPqM x, ?_, rfl⟩
        exact (QuotientGroup.eq_one_iff _).1 (by simpa [z, φ] using congrArg Subtype.val hz1)
      let w : ↥(pCoreOf 2 D.M) := ⟨(x : G), hxO⟩
      have hxG : orderOf (x : G) = p := by
        rw [Subgroup.orderOf_coe]; exact hxord
      have hword : orderOf w = p := by
        rw [← Subgroup.orderOf_coe w]
        exact hxG
      obtain ⟨n, hn⟩ :=
        (IsPGroup.iff_orderOf.1 (uc22p21c_isPGroup_pCoreOf D.M)) w
      have hp2' : p = 2 ^ n := by rw [← hword, hn]
      cases n with
      | zero => exact hp.ne_one (by simpa using hp2')
      | succ n =>
          have h2dvd : 2 ∣ p := hp2' ▸ dvd_pow_self 2 (Nat.succ_ne_zero n)
          exact hp2 ((Nat.Prime.dvd_iff_eq hp Nat.prime_two.ne_one).1 h2dvd)
  | succ k =>
      have hq_dvd_p : q ∣ p :=
        (dvd_pow_self q (Nat.succ_ne_zero k)).trans hqk_dvd_p
      exact hpq ((Nat.Prime.dvd_iff_eq hp hq.ne_one).1 hq_dvd_p)

private theorem uc22s2343_pCore_sig_eq_bot (D : Data G) (Ch : Choice2011 G)
    (h42 : S23_42 D Ch) (h72s : S23_7_2_sig D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    {q : ℕ} (hq : q.Prime) (hqsig : q ∈ D.sig) : CFSG.pCore q (Bar2 D.M) = ⊥ := by
  by_contra hne
  haveI : Fact q.Prime := ⟨hq⟩
  have hq2 : q ≠ 2 := (D.sig_prime q hqsig).2
  obtain ⟨Q0, hQ0⟩ := CFSG.ABGLocalTools.exists_isSylowOf q (uc22s2343_Pq D q)
  have hbar : barImage D.M Q0 = CFSG.pCore q (Bar2 D.M) :=
    (uc22s2343_sylow_barImage D hq hq2 hQ0).1
  have hQ0ne : Q0 ≠ ⊥ := by
    intro hbot
    apply hne
    rw [← hbar, hbot]
    simp [barImage]
  set W : Subgroup G := CFSG.LocalAnalysis.UniquenessCase.UC6.omegaCenter q Q0 with hW
  have hWne : W ≠ ⊥ :=
    CFSG.LocalAnalysis.UniquenessCase.UC6.omegaCenter_ne_bot hQ0.isPGroup hQ0ne
  have hWQ0 : W ≤ Q0 := CFSG.LocalAnalysis.UniquenessCase.UC6.omegaCenter_le q Q0
  have hWp : IsPGroup q W := hQ0.isPGroup.to_le hWQ0
  have hWexp : ∀ x ∈ W, x ^ q = 1 := fun x hx => hx.2.1
  have hWcomm : ⁅⁅W, W⁆, W⁆ = ⊥ := by
    have hle : W ≤ Subgroup.centralizer (W : Set G) := by
      haveI : IsMulCommutative ↥W :=
        (CFSG.LocalAnalysis.UniquenessCase.UC6.isElemAbelian_omegaCenter q Q0).1
      letI : CommGroup ↥W := IsMulCommutative.instCommGroup
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val (mul_comm (⟨y, hy⟩ : ↥W) ⟨x, hx⟩)
    have hab : ⁅W, W⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hle
    rw [hab, Subgroup.commutator_bot_left]
  have hWM : W ≤ D.M :=
    hWQ0.trans (hQ0.le.trans (uc22s2343_Pq_le_M D q))
  have hperm : Permutes D.T W := uc22s2343_permutes_omegaCenter D hq hq2 hQ0
  have hdisj : W ⊓ c.N = ⊥ :=
    h72s h1930 c q hqsig W hWM hWp hWexp hWcomm c.N
      c.N_mem_calMOf_T c.N_ne_M hperm
  have hWN : W ≤ c.N :=
    hWQ0.trans (hQ0.le.trans (uc22s2343_Pq_le_N D Ch h42 h1930 c q))
  exact hWne (by rw [inf_eq_left.mpr hWN] at hdisj; exact hdisj)

private theorem uc22s2343_sylow_cyclic_of_not_sig (D : Data G) (Ch : Choice2011 G)
    (h42 : S23_42 D Ch) (h72 : S23_7_2 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    (hsig : D.sig.Nonempty) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hqnot : q ∉ D.sig)
    {Q0 : Subgroup G} (hQ0 : CFSG.ABGLocalTools.IsSylowOf q Q0 (uc22s2343_Pq D q)) :
    IsCyclic ↥Q0 := by
  by_contra hcyc
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨Q, hQle, hQne, hQncyc, hQexp, hQcomm, hQnorm⟩ :=
    CFSG.GroupTheory.exists_noncyclic_exponent_classTwo_normalized hq2 hQ0.isPGroup hcyc
  obtain ⟨p, hp_sig⟩ := hsig
  have hp : p.Prime := (D.sig_prime p hp_sig).1
  have hp2 : p ≠ 2 := (D.sig_prime p hp_sig).2
  have hpq : p ≠ q := fun h => hqnot (h ▸ hp_sig)
  haveI : Fact p.Prime := ⟨hp⟩
  have hPqM : uc22s2343_Pq D q ≤ D.M := uc22s2343_Pq_le_M D q
  have hPqN : ((uc22s2343_Pq D q).subgroupOf D.M).Normal := uc22s2343_Pq_normal D q
  have hPqRel : uc22s2343_Pq D q ≤ relPPrimeCore p D.M := by
    refine le_sSup ⟨hPqM, hPqN, ?_⟩
    exact uc22s2343_coprime_card_Pq D hq hp hpq hp2
  have hQM : Q ≤ D.M := hQle.trans (hQ0.le.trans hPqM)
  have hQp : IsPGroup q ↥Q := hQ0.isPGroup.to_le hQle
  have hQinf : Q ≤ D.M ⊓ Subgroup.normalizer (Q0 : Set G) :=
    le_inf hQM (hQle.trans (Subgroup.le_normalizer))
  have hQnormal : (Q.subgroupOf (D.M ⊓ Subgroup.normalizer (Q0 : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQinf).2 (by
      rw [Subgroup.le_normalizer_iff]
      intro y hy x hx
      exact (Subgroup.mem_normalizer_iff.1 (hQnorm hy.2) x).1 hx)
  have hperm : Permutes D.T Q := uc22s2343_permutes D hq hq2 hQ0 hQle hQnorm
  have hdisj : Q ⊓ c.N = ⊥ :=
    h72 h1930 c q hq hq2 Q hQM hQp hQncyc hQexp hQcomm p hp_sig
      (uc22s2343_Pq D q) hPqM hPqN hPqRel Q0 hQ0 hQinf hQnormal c.N
      c.N_mem_calMOf_T c.N_ne_M hperm
  have hQN : Q ≤ c.N := hQle.trans (hQ0.le.trans (uc22s2343_Pq_le_N D Ch h42 h1930 c q))
  exact hQne (by rw [inf_eq_left.mpr hQN] at hdisj; exact hdisj)

private theorem uc22s2343_pCore_cyclic (D : Data G) (Ch : Choice2011 G)
    (h42 : S23_42 D Ch) (h72 : S23_7_2 D Ch)
    (h72s : S23_7_2_sig D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch) (hsig : D.sig.Nonempty)
    (r : ℕ) (hr : r.Prime) : IsCyclic ↥(CFSG.pCore r (Bar2 D.M)) := by
  by_cases hr2 : r = 2
  · subst hr2
    have hbot : CFSG.pCore 2 (Bar2 D.M) = ⊥ := by
      simpa [Bar2] using
        (CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot (H := ↥D.M) (p := 2))
    rw [hbot]
    infer_instance
  · by_cases hrsig : r ∈ D.sig
    · rw [uc22s2343_pCore_sig_eq_bot D Ch h42 h72s h1930 c hr hrsig]
      infer_instance
    · haveI : Fact r.Prime := ⟨hr⟩
      by_cases hbot : CFSG.pCore r (Bar2 D.M) = ⊥
      · rw [hbot]
        infer_instance
      · obtain ⟨Q0, hQ0⟩ := CFSG.ABGLocalTools.exists_isSylowOf r (uc22s2343_Pq D r)
        have hQ0cyc : IsCyclic ↥Q0 :=
          uc22s2343_sylow_cyclic_of_not_sig D Ch h42 h72 h1930 c hsig hr hr2 hrsig hQ0
        have hQ0M : Q0 ≤ D.M := hQ0.le.trans (uc22s2343_Pq_le_M D r)
        have hbar : barImage D.M Q0 = CFSG.pCore r (Bar2 D.M) :=
          (uc22s2343_sylow_barImage D hr hr2 hQ0).1
        rw [← hbar]
        have hQ0'cyc : IsCyclic ↥(Q0.subgroupOf D.M) :=
          (Subgroup.subgroupOfEquivOfLe hQ0M).isCyclic.2 hQ0cyc
        exact isCyclic_of_surjective
          (f := (uc22p21cPi D.M).subgroupMap (Q0.subgroupOf D.M))
          (MonoidHom.subgroupMap_surjective _ _)

private theorem uc22s2343_fitting_cyclic (D : Data G) (Ch : Choice2011 G)
    (h42 : S23_42 D Ch) (h72 : S23_7_2 D Ch)
    (h72s : S23_7_2_sig D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch) (hsig : D.sig.Nonempty) :
    IsCyclic ↥(CFSG.fittingSubgroup (Bar2 D.M)) := by
  let F := CFSG.fittingSubgroup (Bar2 D.M)
  have hZ : IsZGroup ↥F := by
    rw [isZGroup_iff]
    intro r hr P
    haveI : Fact r.Prime := ⟨hr⟩
    have hPmap_le : ((P : Subgroup ↥F).map F.subtype) ≤ CFSG.pCore r (Bar2 D.M) :=
      Sylow.map_le_pCore (inferInstance : F.Normal) (inferInstance : Group.IsNilpotent ↥F) r P
    haveI : IsCyclic ↥(CFSG.pCore r (Bar2 D.M)) :=
      uc22s2343_pCore_cyclic D Ch h42 h72 h72s h1930 c hsig r hr
    have hcyc_map : IsCyclic ↥((P : Subgroup ↥F).map F.subtype) := isCyclic_of_le hPmap_le
    exact (MulEquiv.isCyclic
      (Subgroup.equivMapOfInjective (P : Subgroup ↥F) F.subtype F.subtype_injective)).mpr hcyc_map
  haveI : IsZGroup ↥F := hZ
  exact inferInstance

private theorem uc22s2343_sig_not_dvd_fitting (D : Data G) (Ch : Choice2011 G)
    (h42 : S23_42 D Ch) (h72s : S23_7_2_sig D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch) :
    ∀ p ∈ D.sig, ¬ p ∣ Nat.card ↥(CFSG.fittingSubgroup (Bar2 D.M)) := by
  intro p hp_sig hdvd
  let F := CFSG.fittingSubgroup (Bar2 D.M)
  have hp : p.Prime := (D.sig_prime p hp_sig).1
  haveI : Fact p.Prime := ⟨hp⟩
  have hbot : CFSG.pCore p (Bar2 D.M) = ⊥ :=
    uc22s2343_pCore_sig_eq_bot D Ch h42 h72s h1930 c hp hp_sig
  have hfac : 0 < (Nat.card ↥F).factorization p :=
    hp.factorization_pos_of_dvd (Nat.card_pos (α := ↥F)).ne' hdvd
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p ↥F))
  have hPcard : Nat.card ↥(P : Subgroup ↥F) = p ^ (Nat.card ↥F).factorization p :=
    Sylow.card_eq_multiplicity P
  have hPgt1 : 1 < Nat.card ↥(P : Subgroup ↥F) := by
    rw [hPcard]
    exact Nat.one_lt_pow hfac.ne' hp.one_lt
  have hPne : (P : Subgroup ↥F) ≠ ⊥ :=
    (Subgroup.one_lt_card_iff_ne_bot _).1 hPgt1
  have hmap_le : ((P : Subgroup ↥F).map F.subtype) ≤ CFSG.pCore p (Bar2 D.M) :=
    Sylow.map_le_pCore (inferInstance : F.Normal) (inferInstance : Group.IsNilpotent ↥F) p P
  rw [hbot] at hmap_le
  have hmap_bot : ((P : Subgroup ↥F).map F.subtype) = ⊥ := le_bot_iff.1 hmap_le
  have hPbot : (P : Subgroup ↥F) = ⊥ := by
    apply Subgroup.map_injective F.subtype_injective
    rw [hmap_bot, Subgroup.map_bot]
  exact hPne hPbot

theorem s23_43_of (D : Data G) (Ch : Choice2011 G) (h42 : S23_42 D Ch) (h72 : S23_7_2 D Ch)
    (h72s : S23_7_2_sig D Ch) (hsig : D.sig.Nonempty) : S23_43 D Ch := by
  intro h1930 c
  exact ⟨uc22s2343_fitting_cyclic D Ch h42 h72 h72s h1930 c hsig,
    uc22s2343_sig_not_dvd_fitting D Ch h42 h72s h1930 c⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
