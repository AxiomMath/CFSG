module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyL3Top
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.RankThree.PartOne.KF.RankGL
public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyU3Outer
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Exclusion

public section

namespace CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.QuasithinUnique.Setup.X1
  CFSG.QuasithinUnique.Setup.Family CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag Matrix

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem card_le_eight_of_cards {G : Type*} [Group G] [Finite G] (L B : Subgroup G)
    (hcard : ∀ T : Subgroup G, T ≤ B → T ≤ L → Nat.card T ≤ 4)
    (hidx : ∀ a ∈ B, ∀ a' ∈ B, a ∉ L → a' ∉ L → a * a' ∈ L) : Nat.card B ≤ 8 := by
  classical
  by_cases hBL : ∀ a ∈ B, a ∈ L
  · have := hcard B le_rfl hBL
    omega
  · push Not at hBL
    obtain ⟨a₀, ha₀B, ha₀L⟩ := hBL
    set T : Subgroup G := B ⊓ L with hT
    have hT4 : Nat.card T ≤ 4 := hcard T inf_le_left inf_le_right
    have hBT : Nat.card B ≤ 2 * Nat.card T := by
      let f : B → T ⊕ T := fun x =>
        if hx : (x : G) ∈ L then Sum.inl ⟨x, x.2, hx⟩
        else Sum.inr ⟨a₀ * x, B.mul_mem ha₀B x.2, hidx a₀ ha₀B x x.2 ha₀L hx⟩
      have hf : Function.Injective f := by
        intro x y hxy
        by_cases hx : (x : G) ∈ L <;> by_cases hy : (y : G) ∈ L
        · simp only [f, hx, hy, dite_true, Sum.inl.injEq] at hxy
          exact Subtype.ext (congrArg (fun z : T => (z : G)) hxy)
        · simp [f, hx, hy] at hxy
        · simp [f, hx, hy] at hxy
        · simp only [f, hx, hy, dite_false, Sum.inr.injEq] at hxy
          exact Subtype.ext (mul_left_cancel (congrArg (fun z : T => (z : G)) hxy))
      have := Nat.card_le_card_of_injective f hf
      rwa [Nat.card_sum, ← two_mul] at this
    omega

theorem card_le_eight_L3 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {Lb : Subgroup (MulAut W)} (hperf : Group.IsPerfect ↥Lb)
    (hirr : IsIrrOn Lb) (hmod : StatedClassicalModel (CQ Lb) .PSL 3 p 1)
    {B : Subgroup (MulAut W)} (hBN : B ≤ Subgroup.normalizer (Lb : Set (MulAut W)))
    (hB2 : IsElemAbelian2 B) : Nat.card B ≤ 8 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (∀ w : W, w * w = 1) := ⟨hW⟩
  have : Nontrivial W := hirr.1
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have hodd := odd_card_center_of_irreducible hW hirr.2
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
  have hKp : Nat.card K = p := by rw [hK, pow_one]
  have : Fintype K := Fintype.ofFinite K
  have hKcard : Fintype.card K = p := by rw [← Nat.card_eq_fintype_card]; exact hKp
  have : CharP K p := charP_of_card_eq_prime_pow (p := p) (f := 1) (by rw [pow_one]; exact hKcard)
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K p] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h')
  have hKprime : ∀ k : K, ∃ n : ℕ, (n : K) = k := exists_natCast_of_card_prime hKp
  have hσ : ∀ σ : K ≃+* K, σ = 1 := fun σ => RingEquiv.ext fun k => by
    obtain ⟨n, rfl⟩ := hKprime k
    simp
  have hperfSL : Group.IsPerfect (SpecialLinearGroup (Fin 3) K) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect le_rfl
  obtain ⟨D⟩ := exists_coverData3 hp hp2 hperf hodd hKp e
  have hkerodd : Odd (Nat.card D.φ.ker) :=
    odd_card_of_pow_three fun g => Subtype.ext (by simpa using center_cube (D.ker_central g.1 g.2))
  have hB2' : ∀ a ∈ B, a * a = 1 := fun a ha => by
    have := hB2.2 a ha
    rwa [pow_two] at this
  have hbN : ∀ a ∈ B, a ∈ Subgroup.normalizer (Lb : Set (MulAut W)) := fun a ha => hBN ha
  have hcard : ∀ T : Subgroup (MulAut W), T ≤ B → T ≤ Lb → Nat.card T ≤ 4 := by
    intro T hTB hTL
    have hcT : Nat.card (T.subgroupOf Lb) ≤ 4 := by
      refine card_le_of_lifts D.φ (fun g hg h => ?_) hkerodd 4
        (fun T' hT' => card_le_four_SL3 h2 T' hT') (T.subgroupOf Lb)
        (fun x _ => MonoidHom.mem_range.2 (D.surj x)) (fun x hx => ?_) (fun x hx y hy => ?_)
      · exact (Subgroup.mem_center_iff.1 (D.ker_central g hg) h).symm
      · exact Subtype.ext (hB2' _ (hTB hx))
      · exact Subtype.ext (hB2.1 _ (hTB hx) _ (hTB hy))
    have : Nat.card (T.subgroupOf Lb) = Nat.card T :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTL).toEquiv
    omega
  have hidx : ∀ a ∈ B, ∀ a' ∈ B, a ∉ Lb → a' ∉ Lb → a * a' ∈ Lb := by
    intro a haB a' ha'B haL ha'L
    rcases D.dichotomy h2 hσ hperfSL hW hirr.2 hodd (hbN a haB) (hB2' a haB) with h | ⟨A, -, hβ⟩
    · exact absurd h haL
    rcases D.dichotomy h2 hσ hperfSL hW hirr.2 hodd (hbN a' ha'B) (hB2' a' ha'B) with
      h' | ⟨A', -, hβ'⟩
    · exact absurd h' ha'L
    have hsq : a * a' * (a * a') = 1 := by
      calc a * a' * (a * a') = a * (a' * a) * a' := by group
        _ = a * (a * a') * a' := by rw [hB2.1 a' ha'B a haB]
        _ = (a * a) * (a' * a') := by group
        _ = 1 := by rw [hB2' a haB, hB2' a' ha'B, one_mul]
    exact D.mul_mem_of_dual hperfSL hW hirr.2 hodd (hbN a haB) (hbN a' ha'B) hβ hβ' hsq
  exact card_le_eight_of_cards Lb B hcard hidx

open CFSG.SectionRank.OddCover in
theorem card_le_eight_U3 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {Lb : Subgroup (MulAut W)} (hperf : Group.IsPerfect ↥Lb)
    (hirr : IsIrrOn Lb) (hmod : StatedClassicalModel (CQ Lb) .PSU 3 p 1)
    {B : Subgroup (MulAut W)} (hBN : B ≤ Subgroup.normalizer (Lb : Set (MulAut W)))
    (hB2 : IsElemAbelian2 B) : Nat.card B ≤ 8 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (∀ w : W, w * w = 1) := ⟨hW⟩
  have : Nontrivial W := hirr.1
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have hp2 : p ≠ 2 := by omega
  have hodd := odd_card_center_of_irreducible hW hirr.2
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
  have hK2 : Nat.card K = p ^ 2 := by rw [hK, pow_one]
  have : Fintype K := Fintype.ofFinite K
  have hKcard : Fintype.card K = p ^ 2 := by rw [← Nat.card_eq_fintype_card]; exact hK2
  have : CharP K p := charP_of_card_eq_prime_pow (p := p) (f := 2) hKcard
  have h : UnitaryFieldData p 1 K := ⟨hp, le_rfl, by rw [hK]; ring⟩
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K p]; exact hp2)
  have hH : ((-1 : ℤ) = 1 ∧ Nat.card K = p ∧ StatedSU 3 (p ^ 1) K = StatedSL 3 K) ∨
      ((-1 : ℤ) = -1 ∧ Nat.card K = p ^ 2 ∧ StatedSU 3 (p ^ 1) K = StatedSU 3 p K) :=
    Or.inr ⟨rfl, hK2, by rw [pow_one]⟩
  obtain ⟨φ, hφs, hφc, hφk⟩ := exists_cover_hom (ε := -1) (H := StatedSU 3 (p ^ 1) K) hp hp2 hH
    hperf hodd e
  have hperfSU : Group.IsPerfect ↥(StatedSU 3 (p ^ 1) K) := isPerfect_prime_three hp hp2 hH
  have hperfSUI : Group.IsPerfect ↥(SUI h) :=
    Group.IsPerfect.ofSurjective (f := (eSU h).toMonoidHom) (eSU h).surjective
  let D : CoverDataU h Lb := coverDataU_of_cover h e φ hφs hφc hφk
  have hkerodd : Odd (Nat.card φ.ker) := by
    have hdvd := Subgroup.card_dvd_of_le hφk
    rw [(CFSG.LinearGroups.unitary_scalar_kernel hp hK (n := 3) (by norm_num)).2.2] at hdvd
    exact Odd.of_dvd_nat (by decide : Odd 3) (hdvd.trans (Nat.gcd_dvd_left 3 _))
  have hkerc : ∀ g ∈ φ.ker, ∀ x : ↥(StatedSU 3 (p ^ 1) K), g * x = x * g := by
    intro g hg x
    have h1 := hφk hg
    rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at h1
    obtain ⟨r, hr⟩ := h1
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hr]
    exact ((commute_scalar r (x : GL (Fin 3) K)).eq).symm
  have hB2' : ∀ a ∈ B, a * a = 1 := fun a ha => by
    have := hB2.2 a ha
    rwa [pow_two] at this
  have hbN : ∀ a ∈ B, a ∈ Subgroup.normalizer (Lb : Set (MulAut W)) := fun a ha => hBN ha
  have hcard : ∀ T : Subgroup (MulAut W), T ≤ B → T ≤ Lb → Nat.card T ≤ 4 := by
    intro T hTB hTL
    have hcT : Nat.card (T.subgroupOf Lb) ≤ 4 := by
      refine card_le_of_lifts φ hkerc hkerodd 4
        (fun T' hT' => card_le_four_of_det_one h2 (H := StatedSU 3 (p ^ 1) K)
          (fun x hx => CFSG.LieType.Universal.Unitary.det_eq_one_of_mem_statedSU hx) T' hT')
        (T.subgroupOf Lb) (fun x _ => MonoidHom.mem_range.2 (hφs x)) (fun x hx => ?_)
        (fun x hx y hy => ?_)
      · exact Subtype.ext (hB2' _ (hTB hx))
      · exact Subtype.ext (hB2.1 _ (hTB hx) _ (hTB hy))
    have : Nat.card (T.subgroupOf Lb) = Nat.card T :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTL).toEquiv
    omega
  have hidx : ∀ a ∈ B, ∀ a' ∈ B, a ∉ Lb → a' ∉ Lb → a * a' ∈ Lb := by
    intro a haB a' ha'B haL ha'L
    rcases D.dichotomy hp5 hperfSUI hW hirr.2 hodd (hbN a haB) (hB2' a haB) with
      h' | ⟨A, -, -, hβ⟩
    · exact absurd h' haL
    rcases D.dichotomy hp5 hperfSUI hW hirr.2 hodd (hbN a' ha'B) (hB2' a' ha'B) with
      h'' | ⟨A', -, -, hβ'⟩
    · exact absurd h'' ha'L
    have hsq : a * a' * (a * a') = 1 := by
      calc a * a' * (a * a') = a * (a' * a) * a' := by group
        _ = a * (a * a') * a' := by rw [hB2.1 a' ha'B a haB]
        _ = (a * a) * (a' * a') := by group
        _ = 1 := by rw [hB2' a haB, hB2' a' ha'B, one_mul]
    exact D.mul_mem hperfSUI hW hirr.2 hodd (hbN a haB) (hbN a' ha'B) hβ hβ' hsq
  exact card_le_eight_of_cards Lb B hcard hidx

theorem prod_GL_two_dvd {d : ℕ} (hd : d ≤ 8) :
    ∏ i : Fin d, (2 ^ d - 2 ^ (i : ℕ)) ∣ 2 ^ 28 * 3 ^ 5 * (5 ^ 2 * 7 ^ 2 * 17 * 31 * 127) := by
  interval_cases d <;> simp [Fin.prod_univ_succ]

theorem not_cube_dvd_prod_GL_two {p d : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hd : d ≤ 8) :
    ¬ p ^ 3 ∣ ∏ i : Fin d, (2 ^ d - 2 ^ (i : ℕ)) := by
  intro h
  have h1 := h.trans (prod_GL_two_dvd hd)
  have hcop : Nat.Coprime (p ^ 3) (2 ^ 28 * 3 ^ 5) := by
    refine Nat.Coprime.pow_left 3 ?_
    refine Nat.Coprime.mul_right (Nat.Coprime.pow_right _ ?_) (Nat.Coprime.pow_right _ ?_)
    · exact (Nat.coprime_primes hp Nat.prime_two).2 (by omega)
    · exact (Nat.coprime_primes hp Nat.prime_three).2 (by omega)
  have h2 : p ^ 3 ∣ 5 ^ 2 * 7 ^ 2 * 17 * 31 * 127 := hcop.dvd_of_dvd_mul_left h1
  have h3 : p ^ 3 ≤ 5 ^ 2 * 7 ^ 2 * 17 * 31 * 127 := Nat.le_of_dvd (by norm_num) h2
  have h4 : p ≤ 434 := by
    by_contra hcon
    push Not at hcon
    have : 435 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left hcon 3
    omega
  have h5 : ∀ q ∈ Finset.Icc 5 434, ¬ q ^ 3 ∣ 5 ^ 2 * 7 ^ 2 * 17 * 31 * 127 := by decide +kernel
  exact h5 p (Finset.mem_Icc.2 ⟨hp5, h4⟩) h2

theorem natCard_GLV [Finite V] :
    Nat.card (GLV V) = ∏ i : Fin (Module.finrank (ZMod 2) V),
      (2 ^ Module.finrank (ZMod 2) V - 2 ^ (i : ℕ)) := by
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have := CFSG.RankThree.PartOne.LIT.card_linearEquiv_eq (K := ZMod 2) (V := V)
    (Module.finrank (ZMod 2) V) rfl
  rw [Nat.card_zmod] at this
  exact this

theorem nine_le_finrank_of_cube_dvd [Finite V] (L : Subgroup (GLV V)) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (h : p ^ 3 ∣ Nat.card L) : 9 ≤ Module.finrank (ZMod 2) V := by
  by_contra hlt
  push Not at hlt
  have h1 : p ^ 3 ∣ Nat.card (GLV V) := h.trans (Subgroup.card_subgroup_dvd_card L)
  rw [natCard_GLV] at h1
  exact not_cube_dvd_prod_GL_two hp hp5 (by omega) h1

theorem p_cube_dvd_card_psl_three {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hK : Nat.card K = p) : p ^ 3 ∣ Nat.card (StatedProj (StatedSL 3 K)) := by
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num), hK]
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hg : Nat.gcd 3 (p - 1) ∣ ∏ j ∈ Finset.Icc 2 3, (p ^ j - 1) := by
    refine (Nat.gcd_dvd_right 3 (p - 1)).trans ?_
    refine (show p - 1 ∣ p ^ 2 - 1 by
      have := Nat.sub_dvd_pow_sub_pow p 1 2
      simpa using this).trans ?_
    exact Finset.dvd_prod_of_mem (fun j => p ^ j - 1) (by decide : 2 ∈ Finset.Icc 2 3)
  rw [Nat.mul_div_assoc _ hg]
  exact Dvd.dvd.mul_right (pow_dvd_pow p (by norm_num)) _

theorem p_cube_dvd_card_psu_three {K : Type} [Field K] {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hK : Nat.card K = (ℓ ^ 1) ^ 2) :
    ℓ ^ 3 ∣ Nat.card (StatedProj (StatedSU 3 (ℓ ^ 1) K)) := by
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU hℓ le_rfl hK (by norm_num)]
  have hp1 : 1 ≤ ℓ := hℓ.one_lt.le
  have hg : Nat.gcd 3 (ℓ ^ 1 + 1) ∣
      ∏ i ∈ Finset.Icc 2 3, ((((ℓ ^ 1 : ℕ) : ℤ) ^ i - (-1) ^ i).toNat) := by
    refine (Nat.gcd_dvd_right 3 (ℓ ^ 1 + 1)).trans ?_
    have h2 : (ℓ ^ 1 + 1) ∣ ((((ℓ ^ 1 : ℕ) : ℤ) ^ 2 - (-1) ^ 2).toNat) := by
      have : ((((ℓ ^ 1 : ℕ) : ℤ) ^ 2 - (-1) ^ 2).toNat) = (ℓ ^ 1 + 1) * (ℓ - 1) := by
        rw [pow_one]
        have h3 : (((ℓ : ℤ) ^ 2 - (-1) ^ 2) : ℤ) = ((ℓ + 1) * (ℓ - 1) : ℕ) := by
          push_cast [Nat.cast_sub hp1]
          ring
        rw [h3, Int.toNat_natCast]
      exact ⟨ℓ - 1, this⟩
    exact h2.trans (Finset.dvd_prod_of_mem (fun i => ((((ℓ ^ 1 : ℕ) : ℤ) ^ i - (-1) ^ i).toNat))
      (by decide : 2 ∈ Finset.Icc 2 3))
  rw [Nat.mul_div_assoc _ hg]
  refine Dvd.dvd.mul_right ?_ _
  rw [pow_one]

theorem thirteen_dvd_card_psl_three_three {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3) :
    13 ∣ Nat.card (StatedProj (StatedSL 3 K)) := by
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num), hK]
  decide

theorem orderOf_two_zmod_13 : orderOf (2 : ZMod 13) = 12 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide

variable [Finite V]

omit [Finite V] in
theorem model_PSL_toMulSub {p : ℕ} {L : Subgroup (GLV V)}
    (hX : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 3 p 1) :
    StatedClassicalModel (CQ (toMulSub L)) .PSL 3 p 1 := by
  obtain ⟨hadm, K, i1, i2, hK, ⟨e⟩⟩ := hX
  exact ⟨hadm, K, i1, i2, hK, ⟨cqEquiv_toMulSub_comp e⟩⟩

omit [Finite V] in
theorem model_PSU_toMulSub {p : ℕ} {L : Subgroup (GLV V)}
    (hX : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSU 3 p 1) :
    StatedClassicalModel (CQ (toMulSub L)) .PSU 3 p 1 := by
  obtain ⟨hadm, K, i1, i2, hK, ⟨e⟩⟩ := hX
  exact ⟨hadm, K, i1, i2, hK, ⟨cqEquiv_toMulSub_comp e⟩⟩

theorem m_le_three_of_card_le_eight {Γ A L : Subgroup (GLV V)} {m : ℕ} (h : G93Hyp Γ A L L m)
    (hc : toMulSub A ≤ Subgroup.normalizer (toMulSub L : Set (MulAut (Multiplicative V))) →
      IsElemAbelian2 (toMulSub A) →
      Nat.card (toMulSub A) ≤ 8) : m ≤ 3 := by
  obtain ⟨hAN, hAel, hAcard, -⟩ := exists_mulaut_data
    (fun γ hγ l hl => h.H_normal γ hγ l hl) h.A_le h.A_elem h.A_card h.H_irr
  have h8 := hc hAN hAel
  rw [hAcard] at h8
  have : 2 ^ m ≤ 2 ^ 3 := h8
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this

theorem false_of_oddL3 {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Γ A L : Subgroup (GLV V)} {m : ℕ}
    (h : G93Hyp Γ A L L m)
    (hX : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 3 p 1) : False := by
  have hp : p.Prime := Fact.out
  have hmod0 := hX
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := hX
  obtain ⟨hAN, hAel, hAcard, hirr⟩ := exists_mulaut_data
    (fun γ hγ l hl => h.H_normal γ hγ l hl) h.A_le h.A_elem h.A_card h.H_irr
  have hW : ∀ w : Multiplicative V, w * w = 1 := mul_self_eq_one_multiplicative
  have hq := isQuasisimple_toMulSub h.L_comp.2.2
  have : Nontrivial (Multiplicative V) := hirr.1
  have hmod : StatedClassicalModel (CQ (toMulSub L)) .PSL 3 p 1 := model_PSL_toMulSub hmod0
  have hm : m ≤ 3 :=
    m_le_three_of_card_le_eight h fun hAN' hAel' =>
      card_le_eight_L3 hp hp2 hW hq.1 hirr hmod hAN' hAel'
  have hd : Module.finrank (ZMod 2) V ≤ 8 := by
    have hb := h.bound
    omega
  have hKp : Nat.card K = p := by rw [hK, pow_one]
  have : Finite K := ‹_›
  by_cases hp3 : p = 3
  · subst hp3
    have h13 : 13 ∣ Nat.card (StatedProj (StatedSL 3 K)) :=
      thirteen_dvd_card_psl_three_three hKp
    have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
    have h1 := orderOf_two_le_finrank_of_dvd_card_quotient e (p := 13) (by norm_num) h13
    rw [orderOf_two_zmod_13] at h1
    omega
  · have hp5 : 5 ≤ p := by
      have := hp.two_le
      have hp4 : p ≠ 4 := by rintro rfl; exact absurd hp (by norm_num)
      omega
    have hcube := p_cube_dvd_card_psl_three hp hKp
    have h1 : p ^ 3 ∣ Nat.card L := by
      refine hcube.trans ?_
      rw [← Nat.card_congr e.toEquiv]
      exact (Subgroup.card_quotient_dvd_card _)
    have := nine_le_finrank_of_cube_dvd L hp hp5 h1
    omega

theorem oddU3_reduce {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Γ A L : Subgroup (GLV V)} {m : ℕ}
    (h : G93Hyp Γ A L L m)
    (hX : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSU 3 p 1) : p = 3 := by
  have hp : p.Prime := Fact.out
  by_contra hp3
  have hp5 : 5 ≤ p := by
    have := hp.two_le
    have hp4 : p ≠ 4 := by rintro rfl; exact absurd hp (by norm_num)
    omega
  have hmod0 := hX
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := hX
  obtain ⟨hAN, hAel, hAcard, hirr⟩ := exists_mulaut_data
    (fun γ hγ l hl => h.H_normal γ hγ l hl) h.A_le h.A_elem h.A_card h.H_irr
  have hW : ∀ w : Multiplicative V, w * w = 1 := mul_self_eq_one_multiplicative
  have hq := isQuasisimple_toMulSub h.L_comp.2.2
  have : Nontrivial (Multiplicative V) := hirr.1
  have hmod : StatedClassicalModel (CQ (toMulSub L)) .PSU 3 p 1 := model_PSU_toMulSub hmod0
  have hm : m ≤ 3 :=
    m_le_three_of_card_le_eight h fun hAN' hAel' =>
      card_le_eight_U3 hp hp5 hW hq.1 hirr hmod hAN' hAel'
  have hd : Module.finrank (ZMod 2) V ≤ 8 := by
    have hb := h.bound
    omega
  have hcube := p_cube_dvd_card_psu_three hp hK
  have h1 : p ^ 3 ∣ Nat.card L := by
    refine hcube.trans ?_
    rw [← Nat.card_congr e.toEquiv]
    exact (Subgroup.card_quotient_dvd_card _)
  have := nine_le_finrank_of_cube_dvd L hp hp5 h1
  omega

end CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
