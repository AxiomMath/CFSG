module

public import CFSG.LocalAnalysis.WeakClosure81.W16LPU3Cover
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveTwoSplitSmall
public import CFSG.LocalAnalysis.WeakClosure81.SevenSixteenL2
public import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
public import CFSG.LocalAnalysis.EvenBN.GMSK.U3Facts
public import CFSG.ClassicalGroups.Unitary.ThreeEven

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.WeakClosure81.SevenK

private theorem w16l_two_pow_sq (n : ℕ) : (2 ^ n) ^ 2 = 4 ^ n := by
  have h1 : (2 ^ n) ^ 2 = 2 ^ (2 * n) := by rw [← pow_mul, mul_comm]
  have h2 : 4 ^ n = 2 ^ (2 * n) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, pow_mul]
  rw [h1, h2]

private theorem w16l_ordA_one_two_pow (n : ℕ) (hn : 1 ≤ n) :
    ordA 1 (2 ^ n) = 2 ^ n * (4 ^ n - 1) := by
  rw [ordA]
  rw [show Finset.Icc 2 (1 + 1) = {2} by decide, Finset.prod_singleton]
  rw [show Nat.gcd (1 + 1) (2 ^ n - 1) = 1 by
    rw [show 1 + 1 = 2 by norm_num]
    exact Nat.coprime_two_left.mpr
      (Nat.Even.sub_odd Nat.one_le_two_pow (Even.pow_of_ne_zero even_two (by omega)) odd_one)]
  rw [Nat.div_one]
  rw [show (1 : ℕ) * (1 + 1) / 2 = 1 by norm_num, pow_one, w16l_two_pow_sq n]

private theorem w16l_card_of_isL2 {X : Type} [Group X] {n : ℕ} (hn : 1 ≤ n)
    (h : IsL2 X n) : Nat.card X = 2 ^ n * (4 ^ n - 1) := by
  have hcard := CFSG.GH74.card_of_lieModel_PSL (n := 2) (p := 2) (f := n)
    (by norm_num : (2 : ℕ) ≠ 0) h
  rw [show (2 - 1 : ℕ) = 1 by norm_num] at hcard
  rw [hcard, w16l_ordA_one_two_pow n hn]

private theorem w16l_card_of_isSpGp_two {X : Type} [Group X] {n : ℕ} (h : IsSpGp X 2 n) :
    Nat.card X = 2 ^ n * (4 ^ n - 1) :=
  card_eq_of_isL2Gp (isL2Gp_of_isSpGp_two h)

private theorem w16l_isL2OrSz_of_isL2_or_isSz {X : Type} [Group X] {n : ℕ}
    (h : IsL2 X n ∨ IsSz X n) : IsL2OrSz X n := by
  rcases h with h | h
  · exact Or.inl (CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) h)
  · exact Or.inr (CFSG.Blueprint.LieModel.suzukiModel h).2

private theorem w16l_center_eq_bot_of_isSimpleGroup_of_perfect {X : Type} [Group X]
    [IsSimpleGroup X] (hperf : commutator X = ⊤) : Subgroup.center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    have hbot : commutator X = ⊥ := (commutator_eq_bot_iff_center_eq_top X).mpr h
    rw [hbot] at hperf
    exact bot_ne_top hperf

private theorem w16l_not_isPGroup_two_of_isSimpleGroup_of_perfect {X : Type} [Group X] [Finite X]
    (hsimple : IsSimpleGroup X) (hperf : commutator X = ⊤) : ¬ IsPGroup 2 X := by
  intro h2
  haveI : IsSimpleGroup X := hsimple
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  haveI : Group.IsNilpotent X := IsPGroup.isNilpotent h2
  have hlt := IsSolvable.commutator_lt_top_of_nontrivial X
  rw [hperf] at hlt
  exact absurd hlt (lt_irrefl ⊤)

private theorem w16l_eq_bot_of_normal_isPGroup_of_isL2OrSz {X : Type} [Group X] [Finite X]
    {n : ℕ} (hn : 1 < n) (h : IsL2OrSz X n) {N : Subgroup X} (hN : N.Normal)
    (hN2 : IsPGroup 2 N) : N = ⊥ := by
  have hsimple : IsSimpleGroup X := CFSG.Quasithin.E2.isSimpleGroup_of_psl_or_sz h
  have hperf : commutator X = ⊤ := CFSG.Quasithin.E2.commutator_eq_top_of_psl_or_sz hn h
  rcases hsimple.eq_bot_or_eq_top_of_normal N with h0 | h1
  · exact h0
  · exfalso
    have hX2 : IsPGroup 2 X := (h1 ▸ hN2).of_equiv Subgroup.topEquiv
    exact w16l_not_isPGroup_two_of_isSimpleGroup_of_perfect hsimple hperf hX2

private theorem w16l_ker_pair_eq_bot {L S₀ : Type} [Group L] [Group S₀] {n : ℕ} (hn : 1 < n)
    (ψ : L →* S₀) (hker : ψ.ker ≤ Subgroup.center L) {J : Subgroup L}
    (hJO : IsL2OrSz ↥J n) : (ψ.comp J.subtype).ker = ⊥ := by
  have hsimpleJ : IsSimpleGroup ↥J := CFSG.Quasithin.E2.isSimpleGroup_of_psl_or_sz hJO
  have hperfJ : commutator ↥J = ⊤ :=
    CFSG.Quasithin.E2.commutator_eq_top_of_psl_or_sz hn hJO
  have hcenterJ : Subgroup.center ↥J = ⊥ :=
    w16l_center_eq_bot_of_isSimpleGroup_of_perfect hperfJ
  rcases hsimpleJ.eq_bot_or_eq_top_of_normal (ψ.comp J.subtype).ker with h | h
  · exact h
  · exfalso
    have hcenter_top : Subgroup.center ↥J = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [Subgroup.mem_center_iff]
      intro y
      have hx1 : ψ (x : L) = 1 := by
        have hx : x ∈ (ψ.comp J.subtype).ker := by rw [h]; exact Subgroup.mem_top x
        simpa using hx
      have hxc : (x : L) ∈ Subgroup.center L := hker (MonoidHom.mem_ker.mpr hx1)
      exact Subtype.ext (Subgroup.mem_center_iff.mp hxc (y : L))
    rw [hcenterJ] at hcenter_top
    exact bot_ne_top hcenter_top

private theorem w16l_conj_mem_pair_of_map_eq_top {L S₀ : Type} [Group L] [Group S₀]
    (ψ : L →* S₀) (hker : ψ.ker ≤ Subgroup.center L) {A : Subgroup L} {l : L} {J : Subgroup L}
    (hJdef : J = A ⊔ A.map (MulAut.conj l).toMonoidHom) (hmap : J.map ψ = ⊤) :
    ∀ c : L, ∀ a ∈ A, c * a * c⁻¹ ∈ J := by
  intro c a ha
  have hmem : ψ c ∈ J.map ψ := by rw [hmap]; exact Subgroup.mem_top _
  obtain ⟨j, hj, hjc⟩ := Subgroup.mem_map.mp hmem
  have hz : j⁻¹ * c ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hjc, inv_mul_cancel]
  have hzc : j⁻¹ * c ∈ Subgroup.center L := hker hz
  have hcomm : (j⁻¹ * c) * a * (j⁻¹ * c)⁻¹ = a := by
    rw [← Subgroup.mem_center_iff.mp hzc a]
    group
  have hca : c = j * (j⁻¹ * c) := by group
  rw [hca]
  have hconj : (j * (j⁻¹ * c)) * a * (j * (j⁻¹ * c))⁻¹ = j * a * j⁻¹ := by
    calc (j * (j⁻¹ * c)) * a * (j * (j⁻¹ * c))⁻¹
        = j * ((j⁻¹ * c) * a * (j⁻¹ * c)⁻¹) * j⁻¹ := by group
      _ = j * a * j⁻¹ := by rw [hcomm]
  rw [hconj]
  exact J.mul_mem (J.mul_mem hj (by rw [hJdef]; exact Subgroup.mem_sup_left ha)) (J.inv_mem hj)

private theorem w16l_pair_eq_top {L S₀ : Type} [Group L] [Group S₀] [Finite S₀]
    (ψ : L →* S₀) (hker : ψ.ker ≤ Subgroup.center L) {A : Subgroup L} {l : L} {J : Subgroup L}
    (hJdef : J = A ⊔ A.map (MulAut.conj l).toMonoidHom)
    (hgen : Subgroup.normalClosure (A : Set L) = ⊤)
    (hkerJ : (ψ.comp J.subtype).ker = ⊥) (hcard_eq : Nat.card ↥J = Nat.card S₀) :
    J = ⊤ := by
  have hf : Function.Injective (ψ.comp J.subtype) := (MonoidHom.ker_eq_bot_iff _).mp hkerJ
  have hrange : (ψ.comp J.subtype).range = J.map ψ := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hcardmap : Nat.card (J.map ψ) = Nat.card ↥J := by
    rw [← hrange]
    exact (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm
  have hmap : J.map ψ = ⊤ :=
    Subgroup.eq_top_of_card_eq (J.map ψ) (by rw [hcardmap, hcard_eq])
  rw [eq_top_iff, ← hgen, Subgroup.normalClosure, Subgroup.closure_le]
  intro x hx
  obtain ⟨a, ha, hconj⟩ := (Group.mem_conjugatesOfSet_iff).mp hx
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  rw [← hc]
  exact w16l_conj_mem_pair_of_map_eq_top ψ hker hJdef hmap c a ha

private theorem w16l_card_pair_dvd {L S₀ : Type} [Group L] [Group S₀] {J : Subgroup L}
    (ψ : L →* S₀) (hkerJ : (ψ.comp J.subtype).ker = ⊥) :
    Nat.card ↥J ∣ Nat.card S₀ := by
  have hf : Function.Injective (ψ.comp J.subtype) := (MonoidHom.ker_eq_bot_iff _).mp hkerJ
  have hrange : (ψ.comp J.subtype).range = J.map ψ := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hcard : Nat.card ↥J = Nat.card (J.map ψ) := by
    rw [← hrange]
    exact Nat.card_congr (MonoidHom.ofInjective hf).toEquiv
  rw [hcard]
  exact Subgroup.card_subgroup_dvd_card (J.map ψ)

private theorem w16l_sq_add_one_not_dvd_sq_sub_one (q : ℕ) (hq1 : 1 ≤ q) (hq : Even q) :
    ¬ q ^ 2 + 1 ∣ q * (q ^ 2 - 1) := by
  intro h
  have hcop_self : Nat.Coprime (q ^ 2 + 1) q := by
    have h : q ^ 2 + 1 = 1 + q * q := by ring
    rw [h]
    exact (Nat.coprime_add_mul_left_left 1 q q).mpr (Nat.coprime_one_left q)
  have hq2odd : Odd (q ^ 2 - 1) := by
    have h2 : Even (q ^ 2) := by
      obtain ⟨r, rfl⟩ := hq
      exact ⟨2 * r ^ 2, by ring⟩
    have hle : 1 ≤ q ^ 2 := by
      calc 1 = 1 ^ 2 := by norm_num
        _ ≤ q ^ 2 := Nat.pow_le_pow_left hq1 2
    exact Nat.Even.sub_odd hle h2 odd_one
  have hcop_sub : Nat.Coprime (q ^ 2 + 1) (q ^ 2 - 1) := by
    have hle : 1 ≤ q ^ 2 := by
      calc 1 = 1 ^ 2 := by norm_num
        _ ≤ q ^ 2 := Nat.pow_le_pow_left hq1 2
    have h : q ^ 2 + 1 = 2 + (q ^ 2 - 1) := by omega
    rw [h, Nat.coprime_add_self_left]
    exact (Nat.coprime_two_left).mpr hq2odd
  have hcop : Nat.Coprime (q ^ 2 + 1) (q * (q ^ 2 - 1)) := hcop_self.mul_right hcop_sub
  have h1 : q ^ 2 + 1 ∣ 1 := (hcop.dvd_mul_right).mp (by simpa using h)
  have h2 : q ^ 2 + 1 = 1 := Nat.dvd_one.mp h1
  have hge : 2 ≤ q ^ 2 + 1 := by
    have : 1 ≤ q ^ 2 := by
      calc 1 = 1 ^ 2 := by norm_num
        _ ≤ q ^ 2 := Nat.pow_le_pow_left hq1 2
    omega
  omega

private theorem w16l_add_one_not_dvd_ordSuzuki (q : ℕ) (hq1 : 1 ≤ q) (hq : Even q) :
    ¬ q + 1 ∣ ordSuzuki q := by
  intro h2
  have hsq : q ^ 2 - 1 = (q + 1) * (q - 1) := by simpa using Nat.sq_sub_sq q 1
  have hcopq : Nat.Coprime (q + 1) q := by
    rw [add_comm]
    exact (Nat.coprime_add_self_left).mpr (Nat.coprime_one_left q)
  have hcopm1 : Nat.Coprime (q + 1) (q - 1) := by
    have h : q + 1 = 2 + (q - 1) := by omega
    rw [h, Nat.coprime_add_self_left]
    exact (Nat.coprime_two_left).mpr (Nat.Even.sub_odd hq1 hq odd_one)
  have hcopq2 : Nat.Coprime (q + 1) (q ^ 2 + 1) := by
    have hle : 1 ≤ q ^ 2 := by
      calc 1 = 1 ^ 2 := by norm_num
        _ ≤ q ^ 2 := Nat.pow_le_pow_left hq1 2
    have h : q ^ 2 + 1 = 2 + (q + 1) * (q - 1) := by omega
    rw [h, Nat.coprime_add_mul_left_right]
    exact ((Nat.coprime_two_left).mpr (hq.add_odd odd_one)).symm
  have hcop : Nat.Coprime (q + 1) (q ^ 2 * (q ^ 2 + 1) * (q - 1)) := by
    have h := (hcopq.pow_right 2).mul_right (hcopq2.mul_right hcopm1)
    simpa [mul_assoc] using h
  have h3 : q + 1 ∣ 1 := (hcop.dvd_mul_right).mp (by simpa [ordSuzuki] using h2)
  have h4 : q + 1 = 1 := Nat.dvd_one.mp h3
  have hge : 2 ≤ q + 1 := by omega
  omega

private theorem w16l_ordSuzuki_not_dvd_L2 {n : ℕ} (hn : 1 ≤ n) :
    ¬ ordSuzuki (2 ^ n) ∣ 2 ^ n * (4 ^ n - 1) := by
  intro h
  set q := 2 ^ n with hq
  have hqsq : q ^ 2 = 4 ^ n := by rw [hq, w16l_two_pow_sq n]
  rw [← hqsq] at h
  have hqeven : Even q := by
    rw [hq]
    exact Even.pow_of_ne_zero even_two (by omega)
  have hq1 : 1 ≤ q := by rw [hq]; exact Nat.one_le_two_pow
  have h1 : q ^ 2 + 1 ∣ ordSuzuki q := ⟨q ^ 2 * (q - 1), by rw [ordSuzuki]; ring⟩
  have h2 : q ^ 2 + 1 ∣ q * (q ^ 2 - 1) := h1.trans h
  exact w16l_sq_add_one_not_dvd_sq_sub_one q hq1 hqeven h2

private theorem w16l_L2_not_dvd_ordSuzuki {n : ℕ} (hn : 1 ≤ n) :
    ¬ 2 ^ n * (4 ^ n - 1) ∣ ordSuzuki (2 ^ n) := by
  intro h
  set q := 2 ^ n with hq
  have hqsq : q ^ 2 = 4 ^ n := by rw [hq, w16l_two_pow_sq n]
  rw [← hqsq] at h
  have hqeven : Even q := by
    rw [hq]
    exact Even.pow_of_ne_zero even_two (by omega)
  have hq1 : 1 ≤ q := by rw [hq]; exact Nat.one_le_two_pow
  have h1 : q + 1 ∣ q * (q ^ 2 - 1) := by
    have hsq : q ^ 2 - 1 = (q + 1) * (q - 1) := by simpa using Nat.sq_sub_sq q 1
    rw [hsq]
    exact ⟨q * (q - 1), by ring⟩
  have h2 : q + 1 ∣ ordSuzuki q := h1.trans h
  exact w16l_add_one_not_dvd_ordSuzuki q hq1 hqeven h2

section Certified


private theorem w16l_card_of_isSz {X : Type} [Group X] {n : ℕ} (h : IsSz X n) :
    Nat.card X = ordSuzuki (2 ^ n) := by
  have hsz : CFSG.Blueprint.SuzukiModel X 2 n :=
    (CFSG.Blueprint.LieModel.suzukiModel h).2
  obtain ⟨-, a, ha, hf, hcard⟩ := CFSG.GH74.card_of_suzukiModel hsz
  exact hcard

private theorem w16l_card_of_isSzGp {X : Type} [Group X] {n : ℕ} (h : IsSzGp X n) :
    Nat.card X = ordSuzuki (2 ^ n) := by
  obtain ⟨-, a, ha, hf, hcard⟩ := CFSG.GH74.card_of_suzukiModel h
  exact hcard

theorem w16l_lift_L2 {L S₀ : Type} [Group L] [Finite L] [Group S₀] {n : ℕ} (hn : 1 < n)
    (ψ : L →* S₀) (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L)
    (hS : IsSpGp S₀ 2 n) {A : Subgroup L} (hcard : Nat.card A = 2 ^ n)
    (hgen : Subgroup.normalClosure (A : Set L) = ⊤) {l : L}
    (hJ : IsL2 ↥(A ⊔ A.map (MulAut.conj l).toMonoidHom) n ∨
      IsSz ↥(A ⊔ A.map (MulAut.conj l).toMonoidHom) n) :
    CFSG.Quasithin.IsPSL 2 2 n L ∧ ∀ N : Subgroup L, N.Normal → IsPGroup 2 N → N = ⊥ := by
  set J : Subgroup L := A ⊔ A.map (MulAut.conj l).toMonoidHom with hJdef
  have hJO : IsL2OrSz ↥J n := w16l_isL2OrSz_of_isL2_or_isSz hJ
  have hkerJ : (ψ.comp J.subtype).ker = ⊥ := w16l_ker_pair_eq_bot hn ψ hker hJO
  haveI : Finite S₀ := finite_of_isL2Gp (isL2Gp_of_isSpGp_two hS)
  have hcardS : Nat.card S₀ = 2 ^ n * (4 ^ n - 1) := w16l_card_of_isSpGp_two hS
  rcases hJ with hJl2 | hJsz
  · have hcardJ : Nat.card ↥J = 2 ^ n * (4 ^ n - 1) := w16l_card_of_isL2 (by omega) hJl2
    have hcard_eq : Nat.card ↥J = Nat.card S₀ := hcardJ.trans hcardS.symm
    have htop : J = ⊤ := w16l_pair_eq_top ψ hker hJdef hgen hkerJ hcard_eq
    have e : ↥J ≃* L := (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
    have hLl2 : IsL2 L n := CFSG.Blueprint.LieModel.of_mulEquiv e hJl2
    have hPSL : CFSG.Quasithin.IsPSL 2 2 n L :=
      CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hLl2
    exact ⟨hPSL, fun N hN hN2 =>
      w16l_eq_bot_of_normal_isPGroup_of_isL2OrSz hn (Or.inl hPSL) hN hN2⟩
  · exfalso
    have hcardJ : Nat.card ↥J = ordSuzuki (2 ^ n) := w16l_card_of_isSz hJsz
    have hdvd : Nat.card ↥J ∣ Nat.card S₀ := w16l_card_pair_dvd ψ hkerJ
    rw [hcardJ, hcardS] at hdvd
    exact w16l_ordSuzuki_not_dvd_L2 (by omega) hdvd

theorem w16l_lift_Sz {L S₀ : Type} [Group L] [Finite L] [Group S₀] {n : ℕ} (hn : 1 < n)
    (ψ : L →* S₀) (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L)
    (hS : IsSzGp S₀ n) {A : Subgroup L} (hcard : Nat.card A = 2 ^ n)
    (hgen : Subgroup.normalClosure (A : Set L) = ⊤) {l : L}
    (hJ : IsL2 ↥(A ⊔ A.map (MulAut.conj l).toMonoidHom) n ∨
      IsSz ↥(A ⊔ A.map (MulAut.conj l).toMonoidHom) n) :
    CFSG.Quasithin.IsSz n L ∧ ∀ N : Subgroup L, N.Normal → IsPGroup 2 N → N = ⊥ := by
  set J : Subgroup L := A ⊔ A.map (MulAut.conj l).toMonoidHom with hJdef
  have hJO : IsL2OrSz ↥J n := w16l_isL2OrSz_of_isL2_or_isSz hJ
  have hkerJ : (ψ.comp J.subtype).ker = ⊥ := w16l_ker_pair_eq_bot hn ψ hker hJO
  haveI : Finite S₀ :=
    CFSG.LocalAnalysis.EvenBN.GMSK.finite_of_lieModel_twistedB2 (n := n)
      ((CFSG.Blueprint.LieModel.twistedB2_iff (G := S₀) (n := 0) (p := 2) (f := n)).mpr
        ⟨rfl, hS⟩)
  have hcardS : Nat.card S₀ = ordSuzuki (2 ^ n) := w16l_card_of_isSzGp hS
  rcases hJ with hJl2 | hJsz
  · exfalso
    have hcardJ : Nat.card ↥J = 2 ^ n * (4 ^ n - 1) := w16l_card_of_isL2 (by omega) hJl2
    have hdvd : Nat.card ↥J ∣ Nat.card S₀ := w16l_card_pair_dvd ψ hkerJ
    rw [hcardJ, hcardS] at hdvd
    exact w16l_L2_not_dvd_ordSuzuki (by omega) hdvd
  · have hcardJ : Nat.card ↥J = ordSuzuki (2 ^ n) := w16l_card_of_isSz hJsz
    have hcard_eq : Nat.card ↥J = Nat.card S₀ := hcardJ.trans hcardS.symm
    have htop : J = ⊤ := w16l_pair_eq_top ψ hker hJdef hgen hkerJ hcard_eq
    have e : ↥J ≃* L := (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
    have hLsz : IsSz L n := CFSG.Blueprint.LieModel.of_mulEquiv e hJsz
    have hSzq : CFSG.Quasithin.IsSz n L := (CFSG.Blueprint.LieModel.suzukiModel hLsz).2
    exact ⟨hSzq, fun N hN hN2 =>
      w16l_eq_bot_of_normal_isPGroup_of_isL2OrSz hn (Or.inr hSzq) hN hN2⟩

theorem w16l_lift_U3 {L S₀ : Type} [Group L] [Finite L] [Group S₀] {n : ℕ} (hn : 1 < n)
    (ψ : L →* S₀) (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L)
    (hS : IsPSUGp S₀ 3 n) {A : Subgroup L} (hcard : Nat.card A = 2 ^ n)
    (hgen : Subgroup.normalClosure (A : Set L) = ⊤) {l : L}
    (hJ : IsL2 ↥(A ⊔ A.map (MulAut.conj l).toMonoidHom) n ∨
      IsSz ↥(A ⊔ A.map (MulAut.conj l).toMonoidHom) n) :
    IsU3Shape L n ∧ ∀ N : Subgroup L, N.Normal → IsPGroup 2 N → N = ⊥ := by
  set J : Subgroup L := A ⊔ A.map (MulAut.conj l).toMonoidHom with hJdef
  have hJO : IsL2OrSz ↥J n := w16l_isL2OrSz_of_isL2_or_isSz hJ
  have hperfJ : commutator ↥J = ⊤ :=
    CFSG.Quasithin.E2.commutator_eq_top_of_psl_or_sz hn hJO
  have hkerJ : (ψ.comp J.subtype).ker = ⊥ := w16l_ker_pair_eq_bot hn ψ hker hJO
  have hJle : J ≤ commutator L := by
    have hmap := Subgroup.map_subtype_commutator J
    rw [hperfJ, Subgroup.map_top] at hmap
    have hmap' : J = ⁅J, J⁆ := by simpa using hmap
    rw [hmap']
    exact Subgroup.commutator_mono le_top le_top
  have hperfL : commutator L = ⊤ := by
    rw [eq_top_iff, ← hgen]
    exact Subgroup.normalClosure_le_normal (fun a ha => hJle (Subgroup.mem_sup_left ha))
  haveI : Finite S₀ := CFSG.LocalAnalysis.EvenBN.GMSK.finite_of_lieModel_PSU3 hS
  have hsimpleS : IsSimpleGroup S₀ :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hS
  haveI : Group.IsPerfect S₀ := CFSG.ClassicalGroups.Unitary.isPerfect_of_lieModel_psu3 hS
  have hperfS : commutator S₀ = ⊤ := Group.IsPerfect.commutator_eq_top
  have hcenterS : Subgroup.center S₀ = ⊥ :=
    w16l_center_eq_bot_of_isSimpleGroup_of_perfect hperfS
  have hcenter_le : Subgroup.center L ≤ ψ.ker := MonoidHom.center_le_ker ψ hψ hcenterS
  have hcenter_eq : Subgroup.center L = ψ.ker := le_antisymm hcenter_le hker
  have hPSUquot : IsPSUGp (L ⧸ Subgroup.center L) 3 n := by
    have e : L ⧸ Subgroup.center L ≃* S₀ :=
      (QuotientGroup.quotientMulEquivOfEq hcenter_eq).trans
        (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)
    exact CFSG.Blueprint.LieModel.of_mulEquiv e.symm hS
  have hU3 : IsU3Shape L n := w16l_isU3Shape_of_perfect hperfL hPSUquot
  refine ⟨hU3, ?_⟩
  intro N hN hN2
  have hmapN_2 : IsPGroup 2 (N.map ψ) := hN2.map ψ
  have hmapN_bot : N.map ψ = ⊥ := by
    haveI : (N.map ψ).Normal := hN.map ψ hψ
    rcases hsimpleS.eq_bot_or_eq_top_of_normal (N.map ψ) with h | h
    · exact h
    · exfalso
      have hX2 : IsPGroup 2 S₀ := (h ▸ hmapN_2).of_equiv Subgroup.topEquiv
      exact w16l_not_isPGroup_two_of_isSimpleGroup_of_perfect hsimpleS hperfS hX2
  have hNle : N ≤ Subgroup.center L := by
    intro n hn
    exact hker (MonoidHom.mem_ker.mpr (by
      have hmem : ψ n ∈ N.map ψ := Subgroup.mem_map_of_mem ψ hn
      rw [hmapN_bot, Subgroup.mem_bot] at hmem
      exact hmem))
  have hdvd : Nat.card N ∣ 3 := (Subgroup.card_dvd_of_le hNle).trans hU3.2.2
  have hcardN : Nat.card N = 1 := by
    haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hN2
    have hdvd' : 2 ^ k ∣ 3 := by rw [← hk]; exact hdvd
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd' with h1 | h3
    · rw [hk, h1]
    · exfalso
      have hp : (2 ^ k).Prime := h3 ▸ Nat.prime_three
      have hk1 : k = 1 := hp.eq_one_of_pow
      rw [hk1] at h3
      omega
  exact Subgroup.eq_bot_of_card_eq N hcardN

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
