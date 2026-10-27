module

public import CFSG.LocalAnalysis.StandardType.GGSixTrialityL613KGField
public import CFSG.Timmesfeld.Orders.Bang
public import CFSG.LinearAlgebra.SL2MinimalFaithfulZsigmondy

public section

namespace CFSG.StandardType

open Module CFSG.StandardType.Triality CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.LieType.Universal.Spin
  CFSG.RankThree.PartOne.AUTSL CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.StandardType.D4Rank Polynomial
open scoped Matrix

namespace L613KG

section Charpoly

variable {K : Type} [Field K] [CharP K 2]

theorem eval_pow_of_coeff {L : Type} [Field L] [CharP L 2] {p : L[X]} {m : ℕ}
    (hp : ∀ i, p.coeff i ^ 2 ^ m = p.coeff i) (ζ : L) :
    p.eval (ζ ^ 2 ^ m) = p.eval ζ ^ 2 ^ m := by
  rw [eval_eq_sum_range, eval_eq_sum_range, sum_pow_char_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_pow, hp, ← pow_mul, ← pow_mul]
  ring

theorem matrix_eq_one_of_charpoly {M : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K} {ℓ m : ℕ}
    (hℓ : ℓ.Prime) (hM : M ^ ℓ = 1) (hcoeff : ∀ i, M.charpoly.coeff i ^ 2 ^ m = M.charpoly.coeff i)
    (hppd : ∀ k, 0 < k → k < 9 → ¬ ℓ ∣ (2 ^ m) ^ k - 1) (hℓ2 : ℓ ≠ 2) : M = 1 := by
  classical
  set L := AlgebraicClosure K
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  set ML := M.map (algebraMap K L) with hML
  set pL := ML.charpoly with hpL
  have hpLmap : pL = M.charpoly.map (algebraMap K L) := Matrix.charpoly_map M (algebraMap K L)
  have hMLℓ : ML ^ ℓ = 1 := by
    rw [hML, ← Matrix.map_pow, hM, Matrix.map_one _ (map_zero _) (map_one _)]
  have hcoeffL : ∀ i, pL.coeff i ^ 2 ^ m = pL.coeff i := fun i => by
    rw [hpLmap, coeff_map, ← map_pow, hcoeff]
  have hpL0 : pL ≠ 0 := (Matrix.charpoly_monic ML).ne_zero
  have hdeg : pL.natDegree = 8 := by
    rw [hpL, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hroot : ∀ ζ : L, pL.IsRoot ζ → ζ ^ ℓ = 1 := by
    intro ζ hζ
    have hdet : (Matrix.scalar (Fin (2 * 4)) ζ - ML).det = 0 := by
      rw [← Matrix.eval_charpoly]
      exact hζ
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    have hMv : ML *ᵥ v = ζ • v := by
      rw [Matrix.sub_mulVec, sub_eq_zero] at hv
      rw [← hv]
      funext i
      simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
    have hpow : ∀ n : ℕ, (ML ^ n) *ᵥ v = ζ ^ n • v := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ, ← Matrix.mulVec_mulVec, hMv, Matrix.mulVec_smul, ih, smul_smul,
          pow_succ']
    have h1 := hpow ℓ
    rw [hMLℓ, Matrix.one_mulVec] at h1
    have h2 : (ζ ^ ℓ - 1) • v = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact sub_eq_zero.mp h3
    · exact absurd h3 hv0
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hone : ∀ ζ ∈ pL.roots, ζ = 1 := by
    intro ζ hζ
    by_contra hζ1
    have hζr : pL.IsRoot ζ := (mem_roots hpL0).mp hζ
    have hζ0 : ζ ≠ 0 := by
      rintro rfl
      have h := hroot 0 hζr
      rw [zero_pow hℓ.ne_zero] at h
      exact zero_ne_one h
    set u : Lˣ := Units.mk0 ζ hζ0 with hu
    have hu3 : u ^ ℓ = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hroot ζ hζr,
      Units.val_one])
    have hu1 : u ≠ 1 := fun h => hζ1 (by rw [← Units.val_mk0 hζ0, ← hu, h, Units.val_one])
    have hζo : orderOf u = ℓ := orderOf_eq_prime hu3 hu1
    have hroots : ∀ i : ℕ, pL.IsRoot (ζ ^ (2 ^ m) ^ i) := by
      intro i
      induction i with
      | zero => simpa using hζr
      | succ i ih =>
        rw [pow_succ, pow_mul, IsRoot, eval_pow_of_coeff hcoeffL, ih.eq_zero, zero_pow]
        exact pow_ne_zero _ two_ne_zero
    have hinj : Function.Injective fun i : Fin 9 => ζ ^ (2 ^ m) ^ (i : ℕ) := by
      intro i j hij
      simp only at hij
      have hij' : u ^ (2 ^ m) ^ (i : ℕ) = u ^ (2 ^ m) ^ (j : ℕ) := Units.ext (by
        rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, Units.val_mk0]
        exact hij)
      by_contra hne
      have hcop : Nat.Coprime ℓ (2 ^ m) :=
        Nat.Coprime.pow_right _ ((Nat.coprime_primes hℓ Nat.prime_two).mpr hℓ2)
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
      · have hmod := (pow_eq_pow_iff_modEq.mp hij')
        rw [hζo] at hmod
        have hd := (Nat.modEq_iff_dvd' (Nat.pow_le_pow_right (by positivity) hlt.le)).mp hmod
        have e : (2 ^ m) ^ (j : ℕ) - (2 ^ m) ^ (i : ℕ) =
            (2 ^ m) ^ (i : ℕ) * ((2 ^ m) ^ ((j : ℕ) - i) - 1) := by
          rw [Nat.mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' hlt.le]
        rw [e] at hd
        exact hppd ((j : ℕ) - i) (by omega) (by omega)
          ((Nat.Coprime.pow_right _ hcop).dvd_of_dvd_mul_left hd)
      · have hmod := (pow_eq_pow_iff_modEq.mp hij'.symm)
        rw [hζo] at hmod
        have hd := (Nat.modEq_iff_dvd' (Nat.pow_le_pow_right (by positivity) hlt.le)).mp hmod
        have e : (2 ^ m) ^ (i : ℕ) - (2 ^ m) ^ (j : ℕ) =
            (2 ^ m) ^ (j : ℕ) * ((2 ^ m) ^ ((i : ℕ) - j) - 1) := by
          rw [Nat.mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' hlt.le]
        rw [e] at hd
        exact hppd ((i : ℕ) - j) (by omega) (by omega)
          ((Nat.Coprime.pow_right _ hcop).dvd_of_dvd_mul_left hd)
    have hsub : (Finset.univ.image fun i : Fin 9 => ζ ^ (2 ^ m) ^ (i : ℕ)) ⊆ pL.roots.toFinset := by
      intro y hy
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
      exact Multiset.mem_toFinset.mpr ((mem_roots hpL0).mpr (hroots i))
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin] at hcard
    have := (Multiset.toFinset_card_le pL.roots).trans (card_roots' pL)
    omega
  have hsplit : pL.roots.card = pL.natDegree :=
    splits_iff_card_roots.mp (IsAlgClosed.splits pL)
  have hrep : pL.roots = Multiset.replicate 8 1 :=
    Multiset.eq_replicate.mpr ⟨hsplit.trans hdeg, hone⟩
  have hprod := prod_multiset_X_sub_C_of_monic_of_roots_card_eq (Matrix.charpoly_monic ML) hsplit
  rw [hrep, Multiset.map_replicate, Multiset.prod_replicate] at hprod
  have hCH : aeval ML ((X - C 1) ^ 8 : L[X]) = 0 := by
    rw [hprod]
    exact Matrix.aeval_self_charpoly ML
  rw [map_pow, map_sub, aeval_X, aeval_C, map_one] at hCH
  have h8 : ML ^ 8 = 1 := by
    have e : ML = (ML - 1) + 1 := by abel
    have h := add_pow_char_pow_of_commute (R := Matrix (Fin (2 * 4)) (Fin (2 * 4)) L) (p := 2)
      (n := 3) (Commute.one_right (ML - 1))
    rw [← e] at h
    rw [show (8 : ℕ) = 2 ^ 3 from rfl, h, show (2 : ℕ) ^ 3 = 8 by norm_num, hCH, zero_add,
      one_pow]
  have hML1 : ML = 1 := by
    have hg := (pow_gcd_eq_one (a := ML) (m := 8) (n := ℓ)).mpr ⟨h8, hMLℓ⟩
    have hc : Nat.gcd 8 ℓ = 1 := by
      have : Nat.Coprime 2 ℓ := (Nat.coprime_primes Nat.prime_two hℓ).mpr (Ne.symm hℓ2)
      exact Nat.Coprime.pow_left 3 this
    rwa [hc, pow_one] at hg
  ext i j
  have h := congrFun (congrFun hML1 i) j
  rw [hML, Matrix.map_apply, Matrix.one_apply] at h
  rw [Matrix.one_apply]
  split_ifs at h ⊢ with hij
  · exact (algebraMap K L).injective (h.trans (map_one _).symm)
  · exact (algebraMap K L).injective (h.trans (map_zero _).symm)

end Charpoly

section Main

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem charpoly_coeff_fixed {γ : Om8 K} {σ : K ≃+* K} {x : Om8 K}
    (hx : (MulAut.conj γ * AutOm.fieldAutP 4 σ) x = x) (i : ℕ) :
    σ ((x : GL (Fin (2 * 4)) K).val.charpoly.coeff i) =
      (x : GL (Fin (2 * 4)) K).val.charpoly.coeff i := by
  rw [MulAut.mul_apply, MulAut.conj_apply] at hx
  have hφ : AutOm.fieldAutP 4 σ x = γ⁻¹ * x * γ := by
    calc AutOm.fieldAutP 4 σ x = γ⁻¹ * (γ * AutOm.fieldAutP 4 σ x * γ⁻¹) * γ := by group
      _ = γ⁻¹ * x * γ := by rw [hx]
  have h1 := congrArg (fun y : Om8 K => (y : GL (Fin (2 * 4)) K).val.charpoly) hφ
  rw [fieldAutP_val] at h1
  have e1 : (CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldAut (Fin (2 * 4)) K σ
      (x : GL (Fin (2 * 4)) K)).val = (x : GL (Fin (2 * 4)) K).val.map σ := by
    ext a b
    rfl
  have e2 : ((γ⁻¹ * x * γ : Om8 K) : GL (Fin (2 * 4)) K).val =
      ((γ : GL (Fin (2 * 4)) K)⁻¹ : GL (Fin (2 * 4)) K).val * (x : GL (Fin (2 * 4)) K).val *
        (γ : GL (Fin (2 * 4)) K).val := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
  rw [e1, e2, Matrix.coe_units_inv, Matrix.charpoly_units_conj', ← RingEquiv.coe_toRingHom,
    Matrix.charpoly_map] at h1
  have h2 := congrArg (fun p : Polynomial K => p.coeff i) h1
  simp only [coeff_map] at h2
  exact h2

theorem _root_.CFSG.StandardType.ggD4SemilinearLayerInput_holds : GGD4SemilinearLayerInput := by
  intro K _ _ _ f hKc α hα3 hin hsl X hfix hperf hlie
  obtain ⟨γ, σ, hσ, rfl⟩ := exists_field_form hα3 hin hsl
  set R := FixedPoints.subfield (Subgroup.zpowers σ) K with hR
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hσfin : IsOfFinOrder σ := isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, hσ3⟩
  have hmemR : ∀ c : K, σ c = c → c ∈ R := by
    intro c hc
    rintro ⟨τ, hτ⟩
    obtain ⟨n, rfl⟩ := Submonoid.mem_powers_iff _ _ |>.mp (hσfin.mem_powers_iff_mem_zpowers.mpr hτ)
    change (σ ^ n) c = c
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ]
      change (σ ^ n) (σ c) = c
      rw [hc]
      exact ih (Subgroup.pow_mem _ (Subgroup.mem_zpowers σ) n)
  have hcardK : Nat.card K = Nat.card R ^ 3 := by
    have h := CFSG.GorensteinWalter.nat_card_eq_fixedSubfield_card_pow_orderOf K σ
    rwa [hσ] at h
  have : CharP R 2 := ⟨fun x => by
    rw [← CharP.cast_eq_zero_iff K 2 x, ← map_natCast (algebraMap R K) x,
      map_eq_zero_iff _ (algebraMap R K).injective]⟩
  have : Fintype R := Fintype.ofFinite R
  obtain ⟨m, -, hm⟩ := FiniteField.card R 2
  have hRc : Nat.card R = 2 ^ (m : ℕ) := by rw [Nat.card_eq_fintype_card, hm]
  have hm1 : 1 ≤ (m : ℕ) := m.2
  have hpowR : ∀ c : K, σ c = c → c ^ 2 ^ (m : ℕ) = c := by
    intro c hc
    have h := FiniteField.pow_card (⟨c, hmemR c hc⟩ : R)
    rw [hm] at h
    exact congrArg Subtype.val h
  obtain ⟨ℓ, hℓ, hℓdvd, hℓppd⟩ : ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ (2 ^ (m : ℕ)) ^ 9 - 1 ∧
      ∀ k : ℕ, 0 < k → k < 9 → ¬ ℓ ∣ (2 ^ (m : ℕ)) ^ k - 1 := by
    by_cases hm2 : (m : ℕ) = 1
    · rw [hm2, pow_one]
      exact CFSG.Timmesfeld.exists_primitive_prime_dvd_two_pow_sub_one 9 (by norm_num) (by norm_num)
    · have h4 : 3 ≤ 2 ^ (m : ℕ) := by
        calc 3 ≤ 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (m : ℕ) := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact CFSG.SL2MinimalFaithful.exists_primitive_prime_dvd_pow_sub_one h4 (by norm_num)
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hℓ2 : ℓ ≠ 2 := by
    rintro rfl
    have hodd : Odd ((2 ^ (m : ℕ)) ^ 9 - 1) := by
      have h0 : 0 < (2 ^ (m : ℕ)) ^ 9 := by positivity
      have he : Even ((2 ^ (m : ℕ)) ^ 9) := by
        rw [← pow_mul]
        exact (Nat.even_pow.mpr ⟨even_two, by positivity⟩)
      exact Nat.Even.sub_odd h0 he odd_one
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hℓdvd)
  have hℓ3 : ℓ ≠ 3 := by
    rintro rfl
    refine hℓppd 2 (by norm_num) (by norm_num) ?_
    have e : (2 ^ (m : ℕ)) ^ 2 = 4 ^ (m : ℕ) := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [e]
    exact Nat.sub_one_dvd_pow_sub_one 4 (m : ℕ)
  have hcardX := card_eq_of_lieModel_psl3 hlie hKc
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num)] at hcardX
  set q := Nat.card K with hq
  have hqr : q = (2 ^ (m : ℕ)) ^ 3 := by rw [hcardK, hRc]
  have hprod : ∏ j ∈ Finset.Icc 2 3, (q ^ j - 1) = (q ^ 2 - 1) * (q ^ 3 - 1) := by
    rw [show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)]
  rw [hprod] at hcardX
  have hd : Nat.gcd 3 (q - 1) ∣ q ^ (3 * (3 - 1) / 2) * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
    refine (Nat.gcd_dvd_right 3 (q - 1)).trans (Dvd.dvd.mul_left ?_ _)
    exact (Nat.sub_one_dvd_pow_sub_one q 2).mul_right _
  have hℓA : ℓ ∣ q ^ (3 * (3 - 1) / 2) * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
    refine Dvd.dvd.mul_left (Dvd.dvd.mul_left ?_ _) _
    rw [hqr, ← pow_mul]
    exact hℓdvd
  have hℓX : ℓ ∣ Nat.card (↥X ⧸ Subgroup.center ↥X) := by
    rw [hcardX]
    obtain ⟨c, hc⟩ := hd
    rw [hc] at hℓA ⊢
    rw [Nat.mul_div_cancel_left _ (Nat.gcd_pos_of_pos_left _ (by norm_num))]
    rcases (Nat.Prime.dvd_mul hℓ).mp hℓA with h | h
    · exfalso
      have h3 := h.trans (Nat.gcd_dvd_left 3 (q - 1))
      exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).mp h3)
    · exact h
  obtain ⟨hbar, hhbar⟩ := exists_prime_orderOf_dvd_card' ℓ hℓX
  obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective hbar
  have hdvd₀ : ℓ ∣ orderOf x₀ := by
    rw [← hhbar]
    exact orderOf_map_dvd (QuotientGroup.mk' (Subgroup.center ↥X)) x₀
  have ho0 : orderOf x₀ ≠ 0 := (orderOf_pos x₀).ne'
  set x := x₀ ^ (orderOf x₀ / ℓ) with hx
  have hxo : orderOf x = ℓ := by
    rw [hx, orderOf_pow_of_dvd (Nat.div_ne_zero_iff_of_dvd hdvd₀ |>.mpr ⟨ho0, hℓ.ne_zero⟩)
      (Nat.div_dvd_of_dvd hdvd₀), Nat.div_div_self hdvd₀ ho0]
  have hxfix := hfix (x : Om8 K) x.2
  have hM : ((x : Om8 K) : GL (Fin (2 * 4)) K).val ^ ℓ = 1 := by
    have h : x ^ ℓ = 1 := by rw [← hxo]; exact pow_orderOf_eq_one x
    have h' : ((x : Om8 K) : GL (Fin (2 * 4)) K) ^ ℓ = 1 := by
      rw [← Subgroup.coe_pow, ← Subgroup.coe_pow, h, Subgroup.coe_one, Subgroup.coe_one]
    rw [← Units.val_pow_eq_pow_val, h', Units.val_one]
  have hcoeff : ∀ i, ((x : Om8 K) : GL (Fin (2 * 4)) K).val.charpoly.coeff i ^ 2 ^ (m : ℕ) =
      ((x : Om8 K) : GL (Fin (2 * 4)) K).val.charpoly.coeff i :=
    fun i => hpowR _ (charpoly_coeff_fixed hxfix i)
  have hone := matrix_eq_one_of_charpoly hℓ hM hcoeff hℓppd hℓ2
  have hx1 : x = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    exact hone
  rw [hx1, orderOf_one] at hxo
  exact hℓ.one_lt.ne hxo

end Main

end L613KG

section Assembly

theorem ggD4TrialityCentralInput_of_classThree (h4 : GGD4ClassThreeLayerInput) :
    GGD4TrialityCentralInput :=
  ggD4TrialityCentralInput_of_layer ggD4SemilinearLayerInput_holds h4

theorem ggSixTrialityInput_of_classThree (h611 : GGSixLSixElevenInput)
    (h4 : GGD4ClassThreeLayerInput) (h5 : GGD4ClassThreeCentralInput)
    (h6 : GGSixTrialityDClassThreeInput) : GGSixTrialityInput :=
  ggSixTrialityInput_of_lSixEleven_central h611 (ggD4TrialityCentralInput_of_classThree h4)
    (ggSixTrialityDCentralInput_of_om8 h6 h5)

end Assembly

end CFSG.StandardType
