module

public import CFSG.LocalAnalysis.StandardType.GGPumpTwLabDefs
public import CFSG.LocalAnalysis.StandardType.GGPumpTwLabRigid
public import CFSG.LocalAnalysis.StandardType.GGPumpTwLabCompNe
public import CFSG.LocalAnalysis.StandardType.GGKacK1
public import CFSG.LocalAnalysis.StandardType.GGKacExcB2
public import CFSG.LocalAnalysis.StandardType.GGTCJHolds
import CFSG.LocalAnalysis.StandardType.GGKGSmallA
import CFSG.LocalAnalysis.StandardType.GGKGSmallB
import CFSG.LocalAnalysis.StandardType.GGKGSmall
import CFSG.Timmesfeld.Orders.Distinct
import CFSG.Timmesfeld.Orders.Bang
import CFSG.GF2Type.Smith1979.W4InspOrdA

public section

namespace CFSG.StandardType

open CFSG.Assembly

private theorem l04fHL6_ordTwistedD_four (q : ℕ) (hq : Even q) :
    CFSG.Open.ordTwistedD 4 q = q ^ 12 * (q ^ 4 + 1) * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1)) := by
  have hodd : Odd (q ^ 4 + 1) := (Nat.even_pow.mpr ⟨hq, by norm_num⟩).add_odd odd_one
  have hcop : Nat.Coprime 4 (q ^ 4 + 1) := by
    simpa using (Nat.coprime_two_left.mpr hodd).pow_left 2
  rw [CFSG.Open.ordTwistedD, hcop.gcd_eq_one, Nat.div_one]
  rw [show (4 - 1 : ℕ) = 3 from rfl]
  rw [Finset.prod_Icc_succ_top (a := 1) (b := 2) (by norm_num)]
  rw [Finset.prod_Icc_succ_top (a := 1) (b := 1) (by norm_num)]
  rw [Finset.prod_Icc_succ_top (a := 1) (b := 0) (by norm_num)]
  simp only [Finset.Icc_eq_empty_of_lt (by norm_num : (1 : ℕ) > 0), Finset.prod_empty, one_mul]
private theorem l04fHL6_ordTwistedF4_eq (q : ℕ) :
    CFSG.Open.ordTwistedF4 q = q ^ 12 * (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) * (q - 1) := by
  unfold CFSG.Open.ordTwistedF4
  ring
private theorem l04fHL6_ordTrialityD4_eq (q : ℕ) :
    CFSG.Open.ordTrialityD4 q = q ^ 12 * (q ^ 8 + q ^ 4 + 1) * ((q ^ 6 - 1) * (q ^ 2 - 1)) := by
  unfold CFSG.Open.ordTrialityD4
  ring
private theorem l04fHL6_le_of_two_pow_dvd_profile {m N a : ℕ} {Z : ℕ → Prop}
    (h : CFSG.Timmesfeld.Orders.Profile m N Z) (ha : 2 ^ a ∣ m) : a ≤ N := by
  obtain ⟨r, hr, hm⟩ := h.two
  rw [hm] at ha
  have hcop : Nat.Coprime (2 ^ a) r := (Nat.coprime_two_left.mpr hr).pow_left a
  have h2 : 2 ^ a ∣ 2 ^ N := hcop.dvd_of_dvd_mul_right ha
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp h2
private theorem l04fHL6_eight_mul_not_dvd {n f k : ℕ} (hn : 1 ≤ n) (hf : 1 ≤ f)
    (hdiv : n ∣ f) (hk : k ≤ 12) (h8 : ¬ 8 ∣ k) : ¬ 8 * f ∣ n * k := by
  intro h
  obtain ⟨c, rfl⟩ := hdiv
  have hnpos : 0 < n := by omega
  have h' : 8 * c ∣ k := by
    have h2 : n * (8 * c) ∣ n * k := by convert h using 1; ring
    exact (Nat.mul_dvd_mul_iff_left hnpos).mp h2
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · exact absurd (hk0 ▸ dvd_zero 8) h8
    · exact hk0
  have hc1 : c = 1 := by
    have hle : 8 * c ≤ k := Nat.le_of_dvd hkpos h'
    by_contra hc
    have hc0 : c = 0 := by omega
    subst hc0
    omega
  subst hc1
  exact h8 h'
private theorem l04fHL6_p_dvd_twD4 {f p : ℕ} (hf : 1 ≤ f)
    (hp : CFSG.Timmesfeld.IsPrimitivePrimeDivisor p (8 * f)) : p ∣ CFSG.Open.ordTwistedD 4 (2 ^ f) := by
  have hp_add : p ∣ (2 ^ f) ^ 4 + 1 := by
    have h := hp.dvd
    rw [show 8 * f = 2 * (4 * f) by ring, CFSG.Timmesfeld.IsPrimitivePrimeDivisor.two_pow_two_mul_sub_one] at h
    rcases hp.prime.dvd_mul.mp h with h | h
    · exfalso
      have hle := Nat.le_of_dvd (by positivity : 0 < 4 * f)
        ((hp.dvd_sub_one_iff (by omega) (4 * f)).mp h)
      omega
    · rwa [show 2 ^ (4 * f) = (2 ^ f) ^ 4 by rw [← pow_mul]; congr 1; ring] at h
  have hdvd : (2 ^ f) ^ 4 + 1 ∣ CFSG.Open.ordTwistedD 4 (2 ^ f) := by
    rw [l04fHL6_ordTwistedD_four (2 ^ f) (Nat.even_pow.mpr ⟨even_two, by omega⟩)]
    exact ⟨(2 ^ f) ^ 12 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 4 - 1) * ((2 ^ f) ^ 6 - 1)),
      by ring⟩
  exact hp_add.trans hdvd
private theorem l04fHL6_not_dvd_twD4_triD4 {n f : ℕ} (hn : 1 ≤ n) (hf : 1 ≤ f)
    (hdiv : n ∣ f) : ¬ CFSG.Open.ordTwistedD 4 (2 ^ f) ∣ CFSG.Open.ordTrialityD4 (2 ^ n) := by
  intro hdvd
  obtain ⟨p, hp⟩ := CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor (k := 8 * f) (by omega) (by omega)
  have hpT : p ∣ CFSG.Open.ordTrialityD4 (2 ^ n) := (l04fHL6_p_dvd_twD4 hf hp).trans hdvd
  rw [l04fHL6_ordTrialityD4_eq] at hpT
  have h2 : ¬ p ∣ 2 ^ (12 * n) := by
    intro h
    exact hp.ne_two (by omega) ((Nat.prime_dvd_prime_iff_eq hp.prime Nat.prime_two).mp
      (hp.prime.dvd_of_dvd_pow h))
  have htri : ¬ p ∣ 2 ^ (8 * n) + 2 ^ (4 * n) + 1 := by
    intro h
    have h' : p ∣ (2 ^ n) ^ 8 + (2 ^ n) ^ 4 + 1 := by
      rwa [show (2 ^ n) ^ 8 = 2 ^ (8 * n) by rw [← pow_mul]; congr 1; ring,
        show (2 ^ n) ^ 4 = 2 ^ (4 * n) by rw [← pow_mul]; congr 1; ring]
    rcases CFSG.Timmesfeld.Orders.PrimDiv.index_of_dvd_triality hp (by omega) n h' with ⟨h1, -⟩ | h1
    · exact l04fHL6_eight_mul_not_dvd hn hf hdiv (by norm_num) (by norm_num) h1
    · omega
  have h6 : ¬ p ∣ 2 ^ (6 * n) - 1 := by
    intro h
    have hh := (hp.dvd_sub_one_iff (by omega) (6 * n)).mp h
    rw [show 6 * n = n * 6 by ring] at hh
    exact l04fHL6_eight_mul_not_dvd hn hf hdiv (by norm_num) (by norm_num) hh
  have h22 : ¬ p ∣ 2 ^ (2 * n) - 1 := by
    intro h
    have hh := (hp.dvd_sub_one_iff (by omega) (2 * n)).mp h
    rw [show 2 * n = n * 2 by ring] at hh
    exact l04fHL6_eight_mul_not_dvd hn hf hdiv (by norm_num) (by norm_num) hh
  rw [show (2 ^ n) ^ 12 = 2 ^ (12 * n) by rw [← pow_mul]; congr 1; ring,
    show (2 ^ n) ^ 8 = 2 ^ (8 * n) by rw [← pow_mul]; congr 1; ring,
    show (2 ^ n) ^ 4 = 2 ^ (4 * n) by rw [← pow_mul]; congr 1; ring,
    show (2 ^ n) ^ 6 = 2 ^ (6 * n) by rw [← pow_mul]; congr 1; ring,
    show (2 ^ n) ^ 2 = 2 ^ (2 * n) by rw [← pow_mul]; congr 1; ring] at hpT
  rcases hp.prime.dvd_mul.mp hpT with h | h
  · rcases hp.prime.dvd_mul.mp h with h | h
    · exact h2 h
    · exact htri h
  · rcases hp.prime.dvd_mul.mp h with h | h
    · exact h6 h
    · exact h22 h
private theorem l04fHL6_not_dvd_twD4_twF4 {n f : ℕ} (hn : 1 ≤ n) (hf : 1 ≤ f)
    (hdiv : n ∣ f) : ¬ CFSG.Open.ordTwistedD 4 (2 ^ f) ∣ CFSG.Open.ordTwistedF4 (2 ^ n) := by
  intro hdvd
  obtain ⟨p, hp⟩ := CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor (k := 8 * f) (by omega) (by omega)
  have hpF : p ∣ CFSG.Open.ordTwistedF4 (2 ^ n) := (l04fHL6_p_dvd_twD4 hf hp).trans hdvd
  rw [l04fHL6_ordTwistedF4_eq] at hpF
  have h2 : ¬ p ∣ 2 ^ (12 * n) := by
    intro h
    exact hp.ne_two (by omega) ((Nat.prime_dvd_prime_iff_eq hp.prime Nat.prime_two).mp
      (hp.prime.dvd_of_dvd_pow h))
  have h6 : ¬ p ∣ 2 ^ (6 * n) + 1 := by
    intro h
    have hh := ((hp.dvd_add_one_iff (by omega) (6 * n)).mp h).1
    rw [show 2 * (6 * n) = n * 12 by ring] at hh
    exact l04fHL6_eight_mul_not_dvd hn hf hdiv (by norm_num) (by norm_num) hh
  have h4 : ¬ p ∣ 2 ^ (4 * n) - 1 := by
    intro h
    have hh := (hp.dvd_sub_one_iff (by omega) (4 * n)).mp h
    rw [show 4 * n = n * 4 by ring] at hh
    exact l04fHL6_eight_mul_not_dvd hn hf hdiv (by norm_num) (by norm_num) hh
  have h3 : ¬ p ∣ 2 ^ (3 * n) + 1 := by
    intro h
    have hh := ((hp.dvd_add_one_iff (by omega) (3 * n)).mp h).1
    rw [show 2 * (3 * n) = n * 6 by ring] at hh
    exact l04fHL6_eight_mul_not_dvd hn hf hdiv (by norm_num) (by norm_num) hh
  have h1 : ¬ p ∣ 2 ^ n - 1 := by
    intro h
    have hle := Nat.le_of_dvd (by positivity) ((hp.dvd_sub_one_iff (by omega) n).mp h)
    have hnf : n ≤ f := Nat.le_of_dvd (by omega) hdiv
    omega
  rw [show (2 ^ n) ^ 12 = 2 ^ (12 * n) by rw [← pow_mul]; congr 1; ring,
    show (2 ^ n) ^ 6 = 2 ^ (6 * n) by rw [← pow_mul]; congr 1; ring,
    show (2 ^ n) ^ 4 = 2 ^ (4 * n) by rw [← pow_mul]; congr 1; ring,
    show (2 ^ n) ^ 3 = 2 ^ (3 * n) by rw [← pow_mul]; congr 1; ring] at hpF
  rcases hp.prime.dvd_mul.mp hpF with h | h
  · rcases hp.prime.dvd_mul.mp h with h | h
    · rcases hp.prime.dvd_mul.mp h with h | h
      · rcases hp.prime.dvd_mul.mp h with h | h
        · exact h2 h
        · exact h6 h
      · exact h4 h
    · exact h3 h
  · exact h1 h
private theorem l04fHL6_two_part_contra {cY cR a N : ℕ} {Z : ℕ → Prop}
    (hY : 2 ^ a ∣ cY) (hdvd : cY ∣ cR) (hprof : CFSG.Timmesfeld.Orders.Profile cR N Z)
    (hgt : N < a) : False := by
  have hR : 2 ^ a ∣ cR := hY.trans hdvd
  have := l04fHL6_le_of_two_pow_dvd_profile hprof hR
  omega
private theorem l04fHL6_card_dvd {L' R : Type} [Group L'] [Finite L'] [Group R]
    (ψ : L' →* R) (_hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (J : Subgroup L') : Nat.card (J ⧸ Subgroup.center J) ∣ Nat.card R := by
  let f : ↥J →* R := ψ.comp J.subtype
  have hfker : f.ker = ψ.ker.comap J.subtype := by
    rw [← MonoidHom.comap_ker ψ J.subtype]
  have hZC : ψ.ker.comap J.subtype ≤ Subgroup.center ↥J := by
    intro j hj
    rw [Subgroup.mem_comap] at hj
    rw [Subgroup.mem_center_iff]
    intro k
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hker hj) (k : L'))
  have hdvd1 : Nat.card (↥J ⧸ Subgroup.center ↥J) ∣
      Nat.card (↥J ⧸ ψ.ker.comap J.subtype) := by
    rw [← Subgroup.index_eq_card (Subgroup.center ↥J),
      ← Subgroup.index_eq_card (ψ.ker.comap J.subtype)]
    exact Subgroup.index_dvd_of_le hZC
  have hiso : Nat.card (↥J ⧸ ψ.ker.comap J.subtype) = Nat.card f.range := by
    rw [← hfker]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  exact hdvd1.trans (hiso ▸ Subgroup.card_subgroup_dvd_card f.range)
private theorem l04fHL6_markedModel_twisted {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : lab.tag = .twA ∨ lab.tag = .twD) :
    LargeEvenLabelAll lab fun R _ _ _ => MarkedModel lab R := by
  intro Q hQ
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, hl⟩ := hlab
  dsimp only at h hn hl
  rcases h with rfl | rfl
  · obtain ⟨hl1, hl2⟩ := hl
    dsimp only [LargeEvenRawDatum, MarkedModel, markTag, markRank, markChar, markDeg] at hQ ⊢
    refine recipeUnitary_imp (fun K _ _ hK I F hq => ⟨hq, ?_⟩) hQ
    refine Or.inl ⟨by decide, statedClassicalModel_unitary (l + 1) n hK
      ⟨Nat.prime_two, hn, by omega, fun h => ?_⟩⟩
    simp only [Prod.mk.injEq] at h
    have := four_le_two_pow (hl2 (by omega))
    omega
  · dsimp only [LargeEvenRawDatum, MarkedModel, markTag, markRank, markChar, markDeg] at hQ ⊢
    split_ifs at hQ ⊢ with h2 h3
    · refine recipeLinear_imp (fun K _ _ hK I F hq => ⟨hq, ?_⟩) hQ
      have hK' : Nat.card K = 2 ^ (2 * n) := by rw [hK, ← pow_mul, mul_comm]
      have h4 := four_le_two_pow (n := 2 * n) (by omega)
      exact Or.inl ⟨by decide, statedClassicalModel_linear 2 (2 * n) hK'
        ⟨Nat.prime_two, by omega, le_rfl, fun h => by simp only [Prod.mk.injEq] at h; omega,
          fun h => by simp only [Prod.mk.injEq] at h; omega⟩⟩
    · refine recipeUnitary_imp (fun K _ _ hK I F hq => ⟨hq, ?_⟩) hQ
      exact Or.inl ⟨by decide, statedClassicalModel_unitary 4 n hK
        ⟨Nat.prime_two, hn, by omega, by simp⟩⟩
    · refine recipeOmegaMinus_imp (fun K _ _ hK b c hbc I F hq => ⟨hq, ?_⟩) hQ
      exact Or.inl ⟨by decide, statedClassicalModel_omegaMinus l n hK b c hbc
        ⟨Nat.prime_two, hn, by omega⟩⟩
private theorem l04fHL6_markedModel_A {f : ℕ} (hf : 1 ≤ f) {Y : Type} [Group Y]
    (h : GGHasLabel ⟨.A, 5, f⟩ Y) : MarkedModel ⟨.A, 5, f⟩ Y := by
  obtain ⟨R, _, I, F, ⟨e⟩, hM⟩ := largeEvenRawDatum_exists
    ((SCFourCover.largeEvenLabelAll_markedModel_classical (lab := ⟨.A, 5, f⟩)
      (by simp [LargeEvenInLambda2, hf]) (Or.inl rfl)) (fun R' _ _ _ => Nonempty (Y ≃* R')) h)
  exact MarkedModel.of_mulEquiv e.symm hM
private theorem l04fHL6_markedModel_twA {f : ℕ} (hf : 1 ≤ f) {Y : Type} [Group Y]
    (h : GGHasLabel ⟨.twA, 5, f⟩ Y) : MarkedModel ⟨.twA, 5, f⟩ Y := by
  obtain ⟨R, _, I, F, ⟨e⟩, hM⟩ := largeEvenRawDatum_exists
    ((l04fHL6_markedModel_twisted (lab := ⟨.twA, 5, f⟩) (by simp [LargeEvenInLambda2, hf])
      (Or.inl rfl)) (fun R' _ _ _ => Nonempty (Y ≃* R')) h)
  exact MarkedModel.of_mulEquiv e.symm hM
private theorem l04fHL6_markedModel_twD {f : ℕ} (hf : 1 ≤ f) {Y : Type} [Group Y]
    (h : GGHasLabel ⟨.twD, 4, f⟩ Y) : MarkedModel ⟨.twD, 4, f⟩ Y := by
  obtain ⟨R, _, I, F, ⟨e⟩, hM⟩ := largeEvenRawDatum_exists
    ((l04fHL6_markedModel_twisted (lab := ⟨.twD, 4, f⟩) (by simp [LargeEvenInLambda2, hf])
      (Or.inr rfl)) (fun R' _ _ _ => Nonempty (Y ≃* R')) h)
  exact MarkedModel.of_mulEquiv e.symm hM
private theorem l04fHL6_centerQuot_nonabelian {H : Type*} [Group H] [IsSimpleGroup H]
    (hna : ∃ a b : H, a * b ≠ b * a) : ∃ a b : H ⧸ Subgroup.center H, a * b ≠ b * a :=
  nonabelian_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq (center_eq_bot_of_simple_nonabelian hna)).trans
      QuotientGroup.quotientBot).symm hna
private theorem l04fHL6_sz_nonabelian {a : ℕ} (ha : 1 ≤ a)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∃ x y : LargeEvenCenterQuot (LargeEvenSzGroup a K), x * y ≠ y * x := by
  have hsimple := CFSG.LieType.Ree.suzuki_simple (a := a) (K := K) ha hK
  have hperfect := CFSG.LieType.Ree.suzuki_perfect (a := a) (K := K) ha hK
  have hna : ∃ g h : CFSG.Blueprint.suzukiGroup a K, g * h ≠ h * g := by
    by_contra h
    push Not at h
    have : Nontrivial (CFSG.Blueprint.suzukiGroup a K) := hsimple.2.1
    have : Group.IsPerfect (CFSG.Blueprint.suzukiGroup a K) := hperfect.2
    have : IsMulCommutative (CFSG.Blueprint.suzukiGroup a K) := ⟨Std.Commutative.mk h⟩
    exact not_subsingleton (CFSG.Blueprint.suzukiGroup a K) Group.IsPerfect.subsingleton_of_isMulCommutative
  have : IsSimpleGroup (CFSG.Blueprint.suzukiGroup a K) := hsimple.2.2
  have hq : ∃ x y : LargeEvenCenterQuot (CFSG.Blueprint.suzukiGroup a K), x * y ≠ y * x :=
    l04fHL6_centerQuot_nonabelian hna
  obtain ⟨e⟩ := nonempty_centerQuot_congr (largeEvenSzGroup_eq a K)
  exact nonabelian_of_mulEquiv e.symm hq
private theorem l04fHL6_g2der_nonabelian
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2) :
    ∃ x y : LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanG2 K true), x * y ≠ y * x := by
  obtain ⟨e₁⟩ := centerQuot_commutator_chevGroup_equiv K .G2
  have hna : ∃ a b : CFSG.Blueprint.DerivedCentralQuotient (CFSG.Blueprint.Chevalley.adjointGroup .G2 K), a * b ≠ b * a := by
    have hL := CFSG.Quasithin.EmptyFaithfulMultiple.g2TwoDerivedUnitaryTransport_holds K hK
    have hC : CFSG.Open.StatedClassicalModel ↥⁅CFSG.Blueprint.Chevalley.adjointGroup .G2 K, CFSG.Blueprint.Chevalley.adjointGroup .G2 K⁆ .PSU 3 3 1 := by
      rcases hL with ⟨-, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
      · exact h
      · simp [CFSG.Blueprint.chevalleyExceptionalTags] at ht
      · simp [CFSG.Blueprint.reeTitsTags] at ht
      · cases ht
    have hsimple : IsSimpleGroup ↥⁅CFSG.Blueprint.Chevalley.adjointGroup .G2 K, CFSG.Blueprint.Chevalley.adjointGroup .G2 K⁆ :=
      (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ 3 3 1 hC).2
    have hcard : Nat.card ↥⁅CFSG.Blueprint.Chevalley.adjointGroup .G2 K, CFSG.Blueprint.Chevalley.adjointGroup .G2 K⁆ = 6048 :=
      CFSG.Blueprint.LieModel.card_psu_three_three hL
    have hneq : ∃ a b : ↥⁅CFSG.Blueprint.Chevalley.adjointGroup .G2 K, CFSG.Blueprint.Chevalley.adjointGroup .G2 K⁆, a * b ≠ b * a := by
      by_contra hnab
      have hcomm : ∀ a b : ↥⁅CFSG.Blueprint.Chevalley.adjointGroup .G2 K, CFSG.Blueprint.Chevalley.adjointGroup .G2 K⁆, a * b = b * a := by
        intro a b
        by_contra h
        exact hnab ⟨a, b, h⟩
      have : IsMulCommutative ↥⁅CFSG.Blueprint.Chevalley.adjointGroup .G2 K, CFSG.Blueprint.Chevalley.adjointGroup .G2 K⁆ :=
        IsMulCommutative.of_comm hcomm
      have hp : (Nat.card ↥⁅CFSG.Blueprint.Chevalley.adjointGroup .G2 K, CFSG.Blueprint.Chevalley.adjointGroup .G2 K⁆).Prime :=
        Group.is_simple_iff_prime_card.mp hsimple
      rw [hcard] at hp
      norm_num at hp
    exact l04fHL6_centerQuot_nonabelian hneq
  exact nonabelian_of_mulEquiv e₁.symm hna
private theorem l04fHL6_markedModel_small
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hsmall : lab.tag = .triD4 ∨ lab.tag = .G2 ∨ lab.tag = .G2der ∨ lab.tag = .twB2 ∨
      lab.tag = .twF4 ∨ lab.tag = .twF4der ∨ lab.tag = .B2der) :
    LargeEvenLabelAll lab fun R _ _ _ => MarkedModel lab R := by
  intro Q hQ
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, hl⟩ := hlab
  dsimp only at hQ hn hl
  rcases hsmall with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · dsimp only [LargeEvenRawDatum, MarkedModel, markTag, markRank, markChar, markDeg] at hQ ⊢
    refine recipeTwisted_imp (fun K _ _ hK I F hq => ⟨hq, ?_⟩) hQ
    exact Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, hn, rfl⟩,
      twistedChevalleyModel_largeEven .D4 hK⟩)
  · obtain ⟨-, hn2⟩ := hl
    dsimp only [LargeEvenRawDatum, MarkedModel, markTag, markRank, markChar, markDeg] at hQ ⊢
    refine recipeChevalley_imp (fun K _ _ hK I F hq => ⟨hq, ?_⟩) hQ
    exact Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, hn, rfl, by
      have := four_le_two_pow hn2; omega⟩, untwistedChevalleyModel_largeEven .G2 hK⟩)
  · dsimp only [LargeEvenRawDatum, MarkedModel, markTag, markRank, markChar, markDeg] at hQ ⊢
    refine recipeChevalley_imp (fun K _ _ hK I F hq => ⟨hq, ?_⟩) hQ
    exact lieModel_g2der K hK (l04fHL6_g2der_nonabelian K hK)
  · obtain ⟨-, ⟨k, hk⟩, hn3⟩ := hl
    have hn' : n = 2 * ((n - 1) / 2) + 1 := by
      subst hk
      rw [show 2 * k + 1 - 1 = 2 * k by omega, Nat.mul_div_cancel_left k (by norm_num)]
    dsimp only [LargeEvenRawDatum, MarkedModel, markTag, markRank, markChar, markDeg] at hQ ⊢
    refine recipeSuzuki_imp (fun K _ _ hK I F hq => ⟨hq, ?_⟩) hQ
    refine Or.inr (Or.inr (Or.inr ⟨rfl, rfl, ?_⟩))
    have ha : 1 ≤ (n - 1) / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]; omega
    have hSz := suzukiModel_largeEvenSz (a := (n - 1) / 2) ha K hK
      (l04fHL6_sz_nonabelian (a := (n - 1) / 2) ha K hK)
    rwa [← hn'] at hSz
  · obtain ⟨-, ⟨k, hk⟩, hn3⟩ := hl
    have hn' : n = 2 * ((n - 1) / 2) + 1 := by
      subst hk
      rw [show 2 * k + 1 - 1 = 2 * k by omega, Nat.mul_div_cancel_left k (by norm_num)]
    dsimp only [LargeEvenRawDatum, MarkedModel, markTag, markRank, markChar, markDeg] at hQ ⊢
    refine recipeTwF4_imp (fun K _ _ hK I F hq => ⟨hq, ?_⟩) hQ
    have hRee := reeTitsRelationModel_largeEven ((n - 1) / 2) hK
    rw [← hn'] at hRee
    exact Or.inr (Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, hn, rfl, rfl, ⟨k, hk⟩, hn3⟩,
      (n - 1) / 2, hn', hRee⟩))
  · obtain ⟨-, rfl⟩ := hl
    dsimp only [LargeEvenRawDatum, MarkedModel, markTag, markRank, markChar, markDeg] at hQ ⊢
    refine recipeTwF4_imp (fun K _ _ hK I F hq => ⟨hq, ?_⟩) hQ
    exact Or.inr (Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, le_rfl, rfl, rfl, rfl⟩,
      0, rfl, reeTitsRelationModel_largeEven 0 hK⟩))
  · dsimp only [LargeEvenRawDatum, MarkedModel, markTag, markRank, markChar, markDeg] at hQ ⊢
    refine recipeSymplectic_imp (fun K _ _ hK I F hq => ⟨hq, ?_⟩) hQ
    exact Or.inl ⟨by decide, statedClassicalModel_b2der hK⟩
theorem ggPumpTwLab_laneSmall
    (lab : LargeEvenLabel) (hlab : LargeEvenInLambda2 lab)
    (hF : lab.tag = .triD4 ∨ lab.tag = .G2 ∨ lab.tag = .G2der ∨ lab.tag = .twB2 ∨ lab.tag = .twF4 ∨
      lab.tag = .twF4der ∨ lab.tag = .B2der) : GGPumpTwLabAt lab := by
  have hmarked := l04fHL6_markedModel_small hlab hF
  have hTCJ := TCJ.ggTCJKnown_holds 3 (by norm_num) (by norm_num) lab hlab
  intro Q hQ
  refine largeEvenRawDatum_mono ?_ ((largeEvenLabelAll_and hmarked hTCJ) Q hQ)
  rintro R _ I F ⟨hq, hM, hTCJprop⟩
  refine ⟨hq, ?_⟩
  intro L' _ _ ψ hψ hker hperf e J f he1 he3 hφ hJ hJlab
  obtain ⟨labJ, hlabJ, hdvd, hhas⟩ := hTCJprop L' ψ hψ hker hperf e he3 hφ J hJ
  have hrig := ggPumpTwJLab_rigid hJlab hlabJ hhas
  have hfn : labJ.n = f := by rcases hrig with ⟨h, -⟩ | ⟨h, -⟩ | h <;> rw [h]
  have hnf : lab.n ∣ f := hfn ▸ hdvd
  have hf1 : 1 ≤ f := hfn ▸ hlabJ.1
  have hnf_le : lab.n ≤ f := Nat.le_of_dvd (by omega) hnf
  have hcd : Nat.card (J ⧸ Subgroup.center J) ∣ Nat.card R := l04fHL6_card_dvd ψ hψ hker J
  have hJ15 : (GGHasLabel ⟨.A, 5, f⟩ (J ⧸ Subgroup.center J) ∨
      GGHasLabel ⟨.twA, 5, f⟩ (J ⧸ Subgroup.center J)) →
      2 ^ (f * 15) ∣ Nat.card (J ⧸ Subgroup.center J) := by
    rintro (h | h)
    · have hMY := l04fHL6_markedModel_A hf1 h
      have hc : Nat.card (J ⧸ Subgroup.center J) = CFSG.Open.ordA 5 (2 ^ f) := by
        rw [CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder
          (show CFSG.Blueprint.LieModel (J ⧸ Subgroup.center J) .PSL 6 2 f from hMY)]; rfl
      rw [hc]
      exact CFSG.GF2Type.Smith1979.W4Insp.Survivors.two_pow_dvd_of_profile
        (CFSG.Timmesfeld.Orders.profile_ordA (n := 5) (by norm_num) hf1)
    · have hMY := l04fHL6_markedModel_twA hf1 h
      have hc : Nat.card (J ⧸ Subgroup.center J) = CFSG.Open.ordTwistedA 5 (2 ^ f) := by
        rw [CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder
          (show CFSG.Blueprint.LieModel (J ⧸ Subgroup.center J) .PSU 6 2 f from hMY)]; rfl
      rw [hc]
      exact CFSG.GF2Type.Smith1979.W4Insp.Survivors.two_pow_dvd_of_profile
        (CFSG.Timmesfeld.Orders.profile_ordTwistedA (n := 5) (by norm_num) hf1)
  have h12 : 2 ^ (f * 12) ∣ Nat.card (J ⧸ Subgroup.center J) := by
    rcases hJlab with ⟨-, h⟩ | ⟨-, h⟩ | h
    · exact (pow_dvd_pow 2 (by omega : f * 12 ≤ f * 15)).trans (hJ15 (Or.inr h))
    · exact (pow_dvd_pow 2 (by omega : f * 12 ≤ f * 15)).trans (hJ15 (Or.inl h))
    · have hMY := l04fHL6_markedModel_twD hf1 h
      have hc : Nat.card (J ⧸ Subgroup.center J) = CFSG.Open.ordTwistedD 4 (2 ^ f) := by
        rw [CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder
          (show CFSG.Blueprint.LieModel (J ⧸ Subgroup.center J) .POmegaMinus 4 2 f from hMY)]; rfl
      rw [hc]
      exact CFSG.GF2Type.Smith1979.W4Insp.Survivors.two_pow_dvd_of_profile
        (CFSG.Timmesfeld.Orders.profile_ordTwistedD (n := 4) (by norm_num) hf1)
  rcases hF with ht | ht | ht | ht | ht | ht | ht
  · have hM' : CFSG.Blueprint.LieModel R .trialityD4 0 2 lab.n := by
      simpa only [MarkedModel, markTag, markRank, markChar, markDeg, ht] using hM
    have hcR : Nat.card R = CFSG.Open.ordTrialityD4 (2 ^ lab.n) := by
      rw [CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM']; rfl
    rcases hrig with hA | hA | hA
    · rw [hA.1] at hhas
      have h15 := hJ15 (Or.inl hhas)
      have hcd' : Nat.card (J ⧸ Subgroup.center J) ∣ CFSG.Open.ordTrialityD4 (2 ^ lab.n) := by
        rw [hcR] at hcd; exact hcd
      exact False.elim (l04fHL6_two_part_contra h15 hcd'
        (CFSG.Timmesfeld.Orders.profile_ordTrialityD4 hlab.1)
        (lt_of_le_of_lt (Nat.mul_le_mul_right 12 hnf_le)
          (Nat.mul_lt_mul_of_pos_left (by norm_num : 12 < 15) (by omega))))
    · rw [hA.1] at hhas
      have h15 := hJ15 (Or.inr hhas)
      have hcd' : Nat.card (J ⧸ Subgroup.center J) ∣ CFSG.Open.ordTrialityD4 (2 ^ lab.n) := by
        rw [hcR] at hcd; exact hcd
      exact False.elim (l04fHL6_two_part_contra h15 hcd'
        (CFSG.Timmesfeld.Orders.profile_ordTrialityD4 hlab.1)
        (lt_of_le_of_lt (Nat.mul_le_mul_right 12 hnf_le)
          (Nat.mul_lt_mul_of_pos_left (by norm_num : 12 < 15) (by omega))))
    · rw [hA] at hhas
      have hMY := l04fHL6_markedModel_twD hf1 hhas
      have hc : Nat.card (J ⧸ Subgroup.center J) = CFSG.Open.ordTwistedD 4 (2 ^ f) := by
        rw [CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder
          (show CFSG.Blueprint.LieModel (J ⧸ Subgroup.center J) .POmegaMinus 4 2 f from hMY)]; rfl
      exact absurd (by rwa [← hc, ← hcR] : CFSG.Open.ordTwistedD 4 (2 ^ f) ∣
        CFSG.Open.ordTrialityD4 (2 ^ lab.n)) (l04fHL6_not_dvd_twD4_triD4 hlab.1 hf1 hnf)
  · have hM' : CFSG.Blueprint.LieModel R .G2 0 2 lab.n := by
      simpa only [MarkedModel, markTag, markRank, markChar, markDeg, ht] using hM
    have hcR : Nat.card R = CFSG.Open.ordG2 (2 ^ lab.n) := by
      rw [CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM']; rfl
    have hcd' : Nat.card (J ⧸ Subgroup.center J) ∣ CFSG.Open.ordG2 (2 ^ lab.n) := by
      rw [hcR] at hcd; exact hcd
    exact False.elim (l04fHL6_two_part_contra h12 hcd'
      (CFSG.Timmesfeld.Orders.profile_ordG2 hlab.1)
      (lt_of_le_of_lt (Nat.mul_le_mul_right 6 hnf_le)
        (Nat.mul_lt_mul_of_pos_left (by norm_num : 6 < 12) (by omega))))
  · have hM' : MarkedModel ⟨.G2der, 0, 1⟩ R := by
      simpa only [MarkedModel, markTag, markRank, markChar, markDeg, ht] using hM
    have hcR : Nat.card R = 6048 := CFSG.LocalAnalysis.GLTheoremA.card_of_G2der hM'
    have hR : 2 ^ (f * 12) ∣ Nat.card R := h12.trans hcd
    rw [hcR] at hR
    exact absurd ((pow_dvd_pow 2 (by omega : 12 ≤ f * 12)).trans hR) (by norm_num)
  · have hM' : CFSG.Blueprint.LieModel R .twistedB2 0 2 lab.n := by
      simpa only [MarkedModel, markTag, markRank, markChar, markDeg, ht] using hM
    have hcR : Nat.card R = CFSG.Open.ordSuzuki (2 ^ lab.n) := by
      rw [CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM']; rfl
    have hcd' : Nat.card (J ⧸ Subgroup.center J) ∣ CFSG.Open.ordSuzuki (2 ^ lab.n) := by
      rw [hcR] at hcd; exact hcd
    exact False.elim (l04fHL6_two_part_contra h12 hcd'
      (CFSG.Timmesfeld.Orders.profile_ordSuzuki hlab.1)
      (lt_of_le_of_lt (Nat.mul_le_mul_right 2 hnf_le)
        (Nat.mul_lt_mul_of_pos_left (by norm_num : 2 < 12) (by omega))))
  · have hM' : CFSG.Blueprint.LieModel R .twistedF4 0 2 lab.n := by
      simpa only [MarkedModel, markTag, markRank, markChar, markDeg, ht] using hM
    have hcR : Nat.card R = CFSG.Open.ordTwistedF4 (2 ^ lab.n) := by
      rw [CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM']; rfl
    rcases hrig with hA | hA | hA
    · rw [hA.1] at hhas
      have h15 := hJ15 (Or.inl hhas)
      have hcd' : Nat.card (J ⧸ Subgroup.center J) ∣ CFSG.Open.ordTwistedF4 (2 ^ lab.n) := by
        rw [hcR] at hcd; exact hcd
      exact False.elim (l04fHL6_two_part_contra h15 hcd'
        (CFSG.Timmesfeld.Orders.profile_ordTwistedF4 hlab.1)
        (lt_of_le_of_lt (Nat.mul_le_mul_right 12 hnf_le)
          (Nat.mul_lt_mul_of_pos_left (by norm_num : 12 < 15) (by omega))))
    · rw [hA.1] at hhas
      have h15 := hJ15 (Or.inr hhas)
      have hcd' : Nat.card (J ⧸ Subgroup.center J) ∣ CFSG.Open.ordTwistedF4 (2 ^ lab.n) := by
        rw [hcR] at hcd; exact hcd
      exact False.elim (l04fHL6_two_part_contra h15 hcd'
        (CFSG.Timmesfeld.Orders.profile_ordTwistedF4 hlab.1)
        (lt_of_le_of_lt (Nat.mul_le_mul_right 12 hnf_le)
          (Nat.mul_lt_mul_of_pos_left (by norm_num : 12 < 15) (by omega))))
    · rw [hA] at hhas
      have hMY := l04fHL6_markedModel_twD hf1 hhas
      have hc : Nat.card (J ⧸ Subgroup.center J) = CFSG.Open.ordTwistedD 4 (2 ^ f) := by
        rw [CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder
          (show CFSG.Blueprint.LieModel (J ⧸ Subgroup.center J) .POmegaMinus 4 2 f from hMY)]; rfl
      exact absurd (by rwa [← hc, ← hcR] : CFSG.Open.ordTwistedD 4 (2 ^ f) ∣
        CFSG.Open.ordTwistedF4 (2 ^ lab.n)) (l04fHL6_not_dvd_twD4_twF4 hlab.1 hf1 hnf)
  · have hl := hlab.2
    rw [ht] at hl
    obtain ⟨-, hn1⟩ := hl
    have hM' : CFSG.Blueprint.LieModel R .Tits 0 2 1 := by
      simpa only [MarkedModel, markTag, markRank, markChar, markDeg, ht, hn1] using hM
    have hcR : Nat.card R = CFSG.Open.ordTits := by
      rw [CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM']; rfl
    have hR : 2 ^ (f * 12) ∣ Nat.card R := h12.trans hcd
    rw [hcR, CFSG.Open.ordTits] at hR
    exact absurd ((pow_dvd_pow 2 (by omega : 12 ≤ f * 12)).trans hR) (by norm_num)
  · have hM' : MarkedModel ⟨.B2der, 0, 1⟩ R := by
      simpa only [MarkedModel, markTag, markRank, markChar, markDeg, ht] using hM
    have hcR : Nat.card R = 360 := CFSG.LocalAnalysis.GLTheoremA.card_of_B2der hM'
    have hR : 2 ^ (f * 12) ∣ Nat.card R := h12.trans hcd
    rw [hcR] at hR
    exact absurd ((pow_dvd_pow 2 (by omega : 12 ≤ f * 12)).trans hR) (by norm_num)
end CFSG.StandardType
end
