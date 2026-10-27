module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148BPSConj
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatLat
public import CFSG.RankThree.PartTwo.Sec14.Ronan148BJ2V
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.J2Inspect
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.SigHJ
public import CFSG.LocalAnalysis.ComponentInitial.FourGroupCommuting
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatPt
public import CFSG.RankThree.PartTwo.KFacts.KS116LinBasic
public import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PerfectResiduals
public import CFSG.CharacterTheory.Burnside
public import Certificates.Certificate148014
public import CFSG.Certificates.CosetTableShort
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.RankThree.PartTwo.Sec11.Data
public import CFSG.RankThree.PartTwo.Sec14.Item148StepCases
public import CFSG.RankThree.PartTwo.Sec14.Item148StepOne
public import CFSG.RankThree.PartTwo.Sec14.Ronan148BPoint
public import CFSG.RankThree.PartTwo.Sec16.Item164Proof
public import CFSG.RankThree.PartTwo.Sec16.Item169HJ
public import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
public import CFSG.RankThree.PartTwo.Sec4.Item47Diag
public import CFSG.RankThree.PartTwo.Sec4.Item47LThree
public import CFSG.RankThree.PartTwo.Sec4.Item47SpFour
public import CFSG.RankThree.PartTwo.Sec4.Item47Statement
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.RankThree.S4Free.SuzukiEight
public import CFSG.Sporadic.Co1Block.TwoBTri
public import Certificates.Certificate2202
public import Certificates.Certificate2326
public import Certificates.Certificate3171
public import Certificates.Certificate3171Base
public import Certificates.Certificate8166
public import Certificates.Certificate8169

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148B.J2

open Subgroup CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.J2 CFSG.ComponentClassification.J2Cover CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.LocalAnalysis.ComponentInitial.FourGroup (kleinFourOf mem_kleinFourOf card_kleinFourOf
  kleinFourOf_le)
open scoped commutatorElement

theorem pPrimeCoreOf_eq_self {G : Type*} [Group G] [Finite G] {H : Subgroup G}
    (h3 : ¬ 3 ∣ Nat.card H) : CFSG.GH74.GLS.pPrimeCoreOf 3 H = H := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have htop : CFSG.pPrimeCore 3 ↥H = ⊤ := by
    rw [eq_top_iff]
    exact le_sSup ⟨inferInstance, by
      rw [Subgroup.card_top]
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3⟩
  rw [CFSG.GH74.GLS.pPrimeCoreOf, htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem perfect_centralizes {G : Type*} [Group G] {K : Subgroup G} (hKp : Group.IsPerfect K)
    {S : Set G} (hSf : S.Finite) (hS4 : Nat.card S ≤ 4) (hKS : ∀ k ∈ K, ∀ s ∈ S, k * s * k⁻¹ ∈ S)
    {e : G} (he : e ∈ S) : ∀ k ∈ K, k * e = e * k := by
  have : Finite S := hSf.to_subtype
  let act : ↥K → ↥S → ↥S := fun k s => ⟨k * s * (k : G)⁻¹, hKS k k.2 s s.2⟩
  have h1 : ∀ s, act 1 s = s := fun s => Subtype.ext (by simp [act])
  have hmul : ∀ m m' s, act (m * m') s = act m (act m' s) := fun m m' s =>
    Subtype.ext (by simp [act, mul_assoc])
  have hK : ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ = ⊤ := by
    haveI := hKp
    haveI : Group.IsPerfect (⊤ : Subgroup ↥K) := Group.IsPerfect.top_iff.mpr hKp
    exact Subgroup.commutator_eq_self
  intro k hk
  have := CFSG.RankThree.PartTwo.KFacts.NDC.perfect_act_trivial hS4 act h1 hmul hK
    (mem_top ⟨k, hk⟩) ⟨e, he⟩
  have h2 : k * e * k⁻¹ = e := congrArg Subtype.val this
  calc k * e = k * e * k⁻¹ * k := by group
    _ = e * k := by rw [h2]

theorem isSolvable_of_card_dvd_2_3 {H : Type*} [Group H] [Finite H]
    (h : Nat.card H ∣ 2 ^ 7 * 3 ^ 3) : Group.IsSolvable H := by
  obtain ⟨k₁, k₂, hk₁, hk₂, hk⟩ := Nat.dvd_mul.1 h
  obtain ⟨i₁, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hk₁
  obtain ⟨i₂, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hk₂
  have : Fintype H := Fintype.ofFinite H
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, ← hk])

section Elts

set_option linter.unusedSectionVars false

theorem VJ_mem_inv {j : ℕ} (hj : j < 6) : VJ j ∈ invariantPiSubgroups ⊤ (Ej 0) (piCompl 3) :=
  ⟨le_top, (isPiSubgroup_piCompl_iff Nat.prime_three _).2 (by rw [card_VJ hj]; norm_num),
    E0_le_normalizer_VJ hj⟩

theorem sup_VJ_eq_top : VJ 0 ⊔ VJ 1 ⊔ VJ 2 = ⊤ := by
  apply eq_top_of_gen (s := 3) (by norm_num)
  intro j hj q hq
  simp only [genSets, List.getD_cons_succ, List.getD_cons_zero, List.mem_cons, List.not_mem_nil,
    or_false] at hj
  rcases hj with rfl | rfl | rfl
  · exact mem_sup_left (mem_sup_left (tJ_mem_VJ 0 hq))
  · exact mem_sup_left (mem_sup_right (tJ_mem_VJ 1 hq))
  · exact mem_sup_right (tJ_mem_VJ 2 hq)

theorem sigGenConcl_top : SigGenConcl (Ej 0) ⊤ := by
  have hsig : ∀ j < 6, VJ j ≤ sSup {W : Subgroup GJ | W ≤ ⊤ ∧
      W ∈ invariantPiSubgroups ⊤ (Ej 0) (piCompl 3) ∧ W = ⁅W, Ej 0⁆} := fun j hj =>
    le_sSup ⟨le_top, VJ_mem_inv hj, VJ_eq_commutator hj⟩
  unfold SigGenConcl
  calc (⊤ : Subgroup GJ) = VJ 0 ⊔ VJ 1 ⊔ VJ 2 := sup_VJ_eq_top.symm
    _ ≤ _ := sup_le (sup_le (hsig 0 (by norm_num)) (hsig 1 (by norm_num))) (hsig 2 (by norm_num))

@[expose] def nextJ (j : ℕ) : ℕ := (j + 1) % 3 + 3 * (j / 3)

theorem exists_cJ : ∃ c : GJ, c * xJ * c⁻¹ = xJ * zJ ∧ c * zJ * c⁻¹ = zJ ∧
    ∀ j < 6, ∀ p < 3, ∃ q < 3, c * tJ (3 * j + p) * c⁻¹ = tJ (3 * nextJ j + q) :=
  Certificates.certificate148014.2.2

@[expose] noncomputable def cJ : GJ := exists_cJ.choose

theorem cJ_conj_x : cJ * xJ * cJ⁻¹ = xJ * zJ := exists_cJ.choose_spec.1

theorem cJ_conj_z : cJ * zJ * cJ⁻¹ = zJ := exists_cJ.choose_spec.2.1

theorem cJ_conj_tJ {j p : ℕ} (hj : j < 6) (hp : p < 3) :
    ∃ q < 3, cJ * tJ (3 * j + p) * cJ⁻¹ = tJ (3 * nextJ j + q) :=
  exists_cJ.choose_spec.2.2 j hj p hp

theorem map_E0_cJ : (Ej 0).map (MulAut.conj cJ).toMonoidHom = Ej 0 := by
  have hle : (Ej 0).map (MulAut.conj cJ).toMonoidHom ≤ Ej 0 := by
    rintro _ ⟨g, hg, rfl⟩
    rw [Ej_zero] at hg
    induction hg using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with rfl | rfl
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [cJ_conj_z]
        exact zJ_mem_E0
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [cJ_conj_x]
        exact mul_mem xJ_mem_E0 zJ_mem_E0
    | one => simp
    | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
    | inv a _ ha => rw [map_inv]; exact inv_mem ha
  exact Subgroup.eq_of_le_of_card_ge hle
    (by rw [Subgroup.card_map_of_injective (MulAut.conj cJ).injective])

theorem map_VJ_cJ {j : ℕ} (hj : j < 6) :
    (VJ j).map (MulAut.conj cJ).toMonoidHom = VJ (nextJ j) := by
  have hn : nextJ j < 6 := by unfold nextJ; omega
  have hle : (VJ j).map (MulAut.conj cJ).toMonoidHom ≤ VJ (nextJ j) := by
    rintro _ ⟨v, hv, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rcases mem_VJ.1 hv with rfl | ⟨p, hp, rfl⟩
    · rw [mul_one, mul_inv_cancel]
      exact one_mem _
    · obtain ⟨q, hq, h⟩ := cJ_conj_tJ hj hp
      rw [h]
      exact tJ_mem_VJ _ hq
  exact Subgroup.eq_of_le_of_card_ge hle
    (by rw [Subgroup.card_map_of_injective (MulAut.conj cJ).injective, card_VJ hj, card_VJ hn])

theorem eq_top_of_lat {H : Subgroup GJ}
    (hlat : ∀ Z : Subgroup GJ, H ≤ Z → Z = ⊤ ∨ Nat.card Z ∣ 2 ^ 7 * 3 ^ 3 ∨
      ∃ S : Set GJ, zJ ∈ S ∧ Nat.card S ≤ 4 ∧ ∀ y ∈ Z, ∀ s ∈ S, y * s * y⁻¹ ∈ S)
    {K : Subgroup GJ} (hN : H ≤ normalizer (K : Set GJ)) (hKp : Group.IsPerfect K)
    (h3 : 3 ∣ Nat.card K) (hf : ∀ e ∈ Ej 0, (∀ k ∈ K, e * k = k * e) → e = 1) : K = ⊤ := by
  have hK1 : K ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at h3
    norm_num at h3
  have hKN : K ≤ normalizer (K : Set GJ) := Subgroup.le_normalizer
  rcases hlat _ hN with hZ | hdvd | ⟨S, hzS, hS4, hS⟩
  · haveI : K.Normal := normalizer_eq_top_iff.mp hZ
    haveI : IsSimpleGroup GJ := isSimpleGroup_P
    exact (IsSimpleGroup.eq_bot_or_eq_top_of_normal K).resolve_left hK1
  · exfalso
    haveI : Group.IsSolvable (normalizer (K : Set GJ)) := isSolvable_of_card_dvd_2_3 hdvd
    have hKs : Group.IsSolvable K :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hKN)
    haveI : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).mpr hK1
    haveI := hKp
    exact Group.IsPerfect.not_isSolvable K hKs
  · exfalso
    have hcomm := perfect_centralizes hKp (Set.toFinite _) hS4 (fun k hk => hS k (hKN hk)) hzS
    have hz1 : zJ ≠ 1 := by
      rw [CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.z_eq]
      exact CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.z_ne_one
    exact hz1 (hf _ zJ_mem_E0 fun k hk => (hcomm k hk).symm)

theorem sigGenConcl_base {j0 : ℕ} (hj0 : j0 = 0 ∨ j0 = 3)
    {K Q D : Subgroup GJ} (hh : SigGenHyp (Ej 0) K Q D) (hV : VJ j0 ≤ Q) :
    SigGenConcl (Ej 0) K := by
  have hN : Ej 0 ⊔ VJ j0 ≤ normalizer (K : Set GJ) := sup_le hh.normK (hV.trans hh.normQ)
  have hf : ∀ e ∈ Ej 0, (∀ k ∈ K, e * k = k * e) → e = 1 := fun e he hc =>
    hh.faith e he fun k hk => by
      rw [hc k hk, mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _
  have hK : K = ⊤ := by
    rcases hj0 with rfl | rfl
    · exact eq_top_of_lat Certificates.certificate148014.1 hN hh.perf hh.three hf
    · exact eq_top_of_lat Certificates.certificate148014.2.1 hN hh.perf hh.three hf
  rw [hK]
  exact sigGenConcl_top

theorem sigGenConcl_step {j : ℕ} (hj : j < 6)
    (h : ∀ K Q D : Subgroup GJ, SigGenHyp (Ej 0) K Q D → VJ (nextJ j) ≤ Q →
      SigGenConcl (Ej 0) K)
    {K Q D : Subgroup GJ} (hh : SigGenHyp (Ej 0) K Q D) (hV : VJ j ≤ Q) :
    SigGenConcl (Ej 0) K := by
  refine sigGenConcl_of_map (MulAut.conj cJ) (fun hh' => ?_) hh
  rw [map_E0_cJ] at hh' ⊢
  exact h _ _ _ hh' (by rw [← map_VJ_cJ hj]; exact Subgroup.map_mono hV)

theorem sigGenConcl_of_VJ {j : ℕ} (hj : j < 6)
    {K Q D : Subgroup GJ} (hh : SigGenHyp (Ej 0) K Q D) (hV : VJ j ≤ Q) :
    SigGenConcl (Ej 0) K := by
  have b0 : ∀ K Q D : Subgroup GJ, SigGenHyp (Ej 0) K Q D → VJ 0 ≤ Q → SigGenConcl (Ej 0) K :=
    fun _ _ _ hh hV => sigGenConcl_base (Or.inl rfl) hh hV
  have b3 : ∀ K Q D : Subgroup GJ, SigGenHyp (Ej 0) K Q D → VJ 3 ≤ Q → SigGenConcl (Ej 0) K :=
    fun _ _ _ hh hV => sigGenConcl_base (Or.inr rfl) hh hV
  have b2 : ∀ K Q D : Subgroup GJ, SigGenHyp (Ej 0) K Q D → VJ 2 ≤ Q → SigGenConcl (Ej 0) K :=
    fun _ _ _ hh hV => sigGenConcl_step (j := 2) (by norm_num) b0 hh hV
  have b5 : ∀ K Q D : Subgroup GJ, SigGenHyp (Ej 0) K Q D → VJ 5 ≤ Q → SigGenConcl (Ej 0) K :=
    fun _ _ _ hh hV => sigGenConcl_step (j := 5) (by norm_num) b3 hh hV
  interval_cases j
  · exact b0 _ _ _ hh hV
  · exact sigGenConcl_step (j := 1) (by norm_num) b2 hh hV
  · exact b2 _ _ _ hh hV
  · exact b3 _ _ _ hh hV
  · exact sigGenConcl_step (j := 4) (by norm_num) b5 hh hV
  · exact b5 _ _ _ hh hV

theorem sigGenConcl_E0 {K Q D : Subgroup GJ}
    (hh : SigGenHyp (Ej 0) K Q D) : SigGenConcl (Ej 0) K := by
  have hQ3 : ¬ 3 ∣ Nat.card Q := fun h3 => (hh.inv.2.1 ⟨3, Nat.prime_three⟩ h3) rfl
  have hQN : Ej 0 ≤ normalizer (Q : Set GJ) := hh.inv.2.2
  have hQ1 : Q ≠ ⊥ := by
    rintro rfl
    apply hh.nontriv
    rw [Subgroup.commutator_bot_right]
    exact bot_le
  obtain ⟨d, hdD, hd1⟩ : ∃ d ∈ D, d ≠ 1 := by
    rcases Subgroup.bot_or_exists_ne_one D with h | h
    · exfalso
      have := hh.hyp.2
      rw [h, Subgroup.card_bot, card_E0] at this
      norm_num at this
    · exact h
  have hQd : Q ≤ centralizer ({d} : Set GJ) :=
    hh.cent.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hdD))
  obtain ⟨u, huQ, hu1⟩ : ∃ u ∈ Q, u ≠ 1 := (Subgroup.bot_or_exists_ne_one Q).resolve_left hQ1
  have hcore : ∀ {w : GJ}, Q ≤ centralizer ({w} : Set GJ) →
      CFSG.GH74.GLS.pPrimeCoreOf 3 (Q ⊓ centralizer ({w} : Set GJ)) = Q := fun hw => by
    rw [inf_eq_left.2 hw]
    exact pPrimeCoreOf_eq_self hQ3
  have hall : ∀ {j p : ℕ}, j < 6 → p < 3 → tJ (3 * j + p) ∈ Q → VJ j ≤ Q := by
    intro j p hj hp ht v hv
    rcases mem_VJ.1 hv with rfl | ⟨q, hq, rfl⟩
    · exact one_mem _
    · exact all_mem hj hp (hQN (actJ_mem_E0 j)) ht q hq
  rcases centralizer_of_mem_E0 (hh.hyp.1 hdD) hd1 with hC | ⟨k, hk, hC⟩
  · rw [hC] at hQd
    have hU : ∀ v ∈ CFSG.GH74.GLS.pPrimeCoreOf 3 (Q ⊓ centralizer ({zJ} : Set GJ)),
        xJ * v * xJ⁻¹ ∈ CFSG.GH74.GLS.pPrimeCoreOf 3 (Q ⊓ centralizer ({zJ} : Set GJ)) := by
      rw [hcore hQd]
      intro v hv
      exact (mem_normalizer_iff.mp (hQN xJ_mem_E0) v).mp hv
    obtain ⟨j0, -, hj06, hZ⟩ := core_z_single hU
    rw [hcore hQd] at hZ
    rcases hZ u huQ with h | ⟨p, hp, rfl⟩
    · exact absurd h hu1
    · exact sigGenConcl_of_VJ hj06 hh (hall hj06 hp huQ)
  · rw [hC] at hQd
    rcases core_w (K := Q) hk (u := u) (by rw [hcore hQd]; exact huQ) with h | ⟨p, hp, rfl⟩
    · exact absurd h hu1
    · exact sigGenConcl_of_VJ (by omega) hh (hall (by omega) hp huQ)

theorem sigGenIn_GJ : SigGenIn148 GJ := by
  intro P K Q D _ hP9 hh
  obtain ⟨g, hg⟩ := exists_map_conj_eq_E0 hP9
  refine sigGenConcl_of_map (MulAut.conj g) (fun hh' => ?_) hh
  rw [hg] at hh' ⊢
  exact sigGenConcl_E0 hh'

theorem threeSolvIn_GJ : ThreeSolvIn148 GJ := by
  intro P V hP hP9 hV3 hPV
  by_contra hns
  set R := CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf V with hR
  have hRp : Group.IsPerfect R :=
    CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidualOf_isPerfect V
  have hR1 : R ≠ ⊥ := by
    intro h
    apply hns
    obtain ⟨n, hn⟩ := CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_eq_derivedSeries
      (G := ↥V)
    have h0 : CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual ↥V = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have : (x : GJ) ∈ R := ⟨x, hx, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      rw [Subgroup.mem_bot]
      exact Subtype.ext this
    exact ⟨n, by rw [← hn, h0]⟩
  have hRV : R ≤ V := Subgroup.map_subtype_le _
  have hPR : P ≤ normalizer (R : Set GJ) :=
    hPV.trans (CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf_normalizer_contains V)
  have hR3 : Nat.Coprime 3 (Nat.card R) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hRV) hV3
  have hgen : R ≤ ⨆ (x : GJ) (_ : x ∈ P) (_ : x ≠ 1),
      CFSG.GH74.GLS.pPrimeCoreOf 3 (R ⊓ centralizer ({x} : Set GJ)) := by
    refine CFSG.RankThree.PartTwo.Sec5.le_of_forall_inf_centralizer_le Nat.prime_three hP
      (by rw [hP9]; norm_num) hPR hR3 fun v hv hv1 => ?_
    have h3 : ¬ 3 ∣ Nat.card (R ⊓ centralizer ({v} : Set GJ) : Subgroup GJ) := fun h =>
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hR3
        (h.trans (Subgroup.card_dvd_of_le inf_le_left))
    rw [← pPrimeCoreOf_eq_self h3]
    exact le_iSup_of_le v (le_iSup_of_le hv (le_iSup_of_le hv1 le_rfl))
  have htop := inspectSig148_GJ P R hP9 hP.2 hPR hRp hR1 hgen
  rw [htop, Subgroup.card_top, card_GJ] at hR3
  norm_num at hR3

theorem rankTwo_GJ : RankTwo148 GJ := by
  intro E hE hE27
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEp : IsPGroup 3 E := IsPGroup.of_card (n := 3) (by rw [hE27]; norm_num)
  have hP3 : Nat.card P3 = 3 ^ (Nat.card GJ).factorization 3 := by
    rw [card_P3, card_GJ, show (604800 : ℕ) = 3 ^ 3 * 22400 by norm_num,
      CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.factorization_three_pow_mul 3 (by norm_num)]
    norm_num
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.exists_le_map_conj_of_card hP3 hEp
  have heq : E = P3.map (MulAut.conj g).toMonoidHom :=
    Subgroup.eq_of_le_of_card_ge hg (by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, card_P3, hE27])
  apply not_comm_P3
  refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  have ha : MulAut.conj g (a : GJ) ∈ E := heq ▸ Subgroup.mem_map_of_mem _ a.2
  have hb : MulAut.conj g (b : GJ) ∈ E := heq ▸ Subgroup.mem_map_of_mem _ b.2
  have := congrArg Subtype.val (hE.1.is_comm.comm ⟨_, ha⟩ ⟨_, hb⟩)
  simp only [Subgroup.coe_mul] at this
  rw [← map_mul, ← map_mul] at this
  exact (MulAut.conj g).injective this

theorem inspIn148_GJ : InspIn148 GJ := by
  refine ⟨center_P, fun α hα => ?_, threeSolvIn_GJ, rankTwo_GJ, sigGenIn_GJ⟩
  have hodd : Odd (orderOf α) :=
    Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hα)
  obtain ⟨g, rfl⟩ := CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.oddInner_GJ α hodd
  exact ⟨g, rfl⟩

theorem inspIn148_j2 : InspIn148 CFSG.Blueprint.NativeSporadic.J2 :=
  InspIn148.of_mulEquiv nativeEquivP inspIn148_GJ

end Elts

end CFSG.RankThree.PartTwo.Sec14.Ronan148B.J2
