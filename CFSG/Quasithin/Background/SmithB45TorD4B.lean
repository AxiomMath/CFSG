module

public import CFSG.Quasithin.Background.SmithB45TorD4W
public import CFSG.Quasithin.Background.SmithB42D4Main
public import Certificates.Certificate3951
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117

public section

namespace CFSG.Quasithin.B45Tor

open scoped commutatorElement
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Quasithin.B42D4

theorem card_SL2_field (F : Type*) [Field F] [Finite F] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  classical
  have := Fintype.ofFinite F
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  rw [Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    Nat.card_eq_fintype_card, show Fintype.card F ^ 2 - Fintype.card F =
      Fintype.card F * (Fintype.card F - 1) by rw [Nat.mul_sub_one, sq], ← mul_assoc,
    Nat.mul_div_cancel _ (by omega), mul_comm]

theorem not_dvd_two_pow_mul {f : ℕ} {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {d : ℕ}
    (hd : (d : ℤ) = ((2 ^ f : ℕ) : ℤ) ^ 2 + ε * (2 ^ f : ℕ) + 1) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpd : p ∣ d) : ¬ p ∣ 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
  intro h
  rcases (Nat.Prime.dvd_mul hp).1 h with h1 | h1
  · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h1)
    omega
  · have hq1 : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    have h1' : (p : ℤ) ∣ ((2 ^ f : ℕ) : ℤ) ^ 2 - 1 := by
      have := Int.natCast_dvd_natCast.2 h1
      rwa [Nat.cast_sub hq1, Nat.cast_pow, Nat.cast_one] at this
    have hpd' : (p : ℤ) ∣ ((2 ^ f : ℕ) : ℤ) ^ 2 + ε * (2 ^ f : ℕ) + 1 := by
      rw [← hd]
      exact Int.natCast_dvd_natCast.2 hpd
    have h3 : (p : ℤ) ∣ 3 := by
      rcases hε with rfl | rfl
      · have := dvd_sub h1' (dvd_mul_of_dvd_right (dvd_sub hpd' h1') (((2 ^ f : ℕ) : ℤ) - 2))
        convert this using 1
        ring
      · have := dvd_add h1' (dvd_mul_of_dvd_right (dvd_sub hpd' h1') (((2 ^ f : ℕ) : ℤ) + 2))
        convert this using 1
        ring
    have h3' : p ∣ 3 := Int.natCast_dvd_natCast.1 h3
    have := Nat.le_of_dvd (by norm_num) h3'
    omega

section SL2

variable {K : Type} [Field K] [CharP K 2]

local notation "Xr" => pinnedX TwistTag.D4.tag K

theorem orderOf_C_negC_dvd_of_mem [Finite K] (k : Subfield K) {μ lam : K} (hμ : μ ∈ k)
    (hlam : lam ∈ k) :
    orderOf (Xr d4C μ * Xr (-d4C) lam) ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) k) := by
  have hk : TwistTag.D4.tag.cartan ⟨2, by decide⟩ ⟨0, by decide⟩ = -1 := by decide
  obtain ⟨φ, hφ, hup, hlow⟩ :=
    CFSG.LieType.Steinberg.Adjoint.exists_sl2_hom (K := K) (rootOperatorFamily TwistTag.D4.tag) hk
  have hC : d4C = Pi.single (⟨2, by decide⟩ : Fin TwistTag.D4.tag.rank) 1 := by decide
  have e1 : Xr d4C μ = ((φ (CFSG.LieType.Steinberg.sl2Upper μ) :
      adjointGroup TwistTag.D4.tag K) : ModGL TwistTag.D4.tag K) := by
    rw [hup, RootOperatorFamily.coe_eltElement, hC, pinnedX_eq_eltUnit_two]
    rfl
  have e2 : Xr (-d4C) lam = ((φ (CFSG.LieType.Steinberg.sl2Lower lam) :
      adjointGroup TwistTag.D4.tag K) : ModGL TwistTag.D4.tag K) := by
    rw [hlow, RootOperatorFamily.coe_eltElement, hC, pinnedX_eq_eltUnit_two]
    rfl
  set ι := Matrix.SpecialLinearGroup.map (n := Fin 2) k.subtype with hι
  have hιinj : Function.Injective ι := by
    intro A B hAB
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    have h := congrArg (fun C : Matrix.SpecialLinearGroup (Fin 2) K =>
      (C : Matrix (Fin 2) (Fin 2) K) i j) hAB
    simp only [hι, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply, Subfield.subtype_apply] at h
    exact Subtype.ext h
  have eU : ι (CFSG.LieType.Steinberg.sl2Upper (⟨μ, hμ⟩ : k)) =
      CFSG.LieType.Steinberg.sl2Upper μ := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  have eL : ι (CFSG.LieType.Steinberg.sl2Lower (⟨lam, hlam⟩ : k)) =
      CFSG.LieType.Steinberg.sl2Lower lam := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [e1, e2, ← Subgroup.coe_mul, ← map_mul, Subgroup.orderOf_coe, orderOf_injective φ hφ, ← eU,
    ← eL, ← map_mul, orderOf_injective ι hιinj]
  exact orderOf_dvd_natCard _

end SL2

section Bruhat

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ3 : σ.toRingHom ^ 3 = 1)

local notation "τ₀" => σ.toRingHom
local notation "Xr" => pinnedX TwistTag.D4.tag K
local notation "C₀" => graphFixedRootGroup TwistTag.D4 K σ.toRingHom
local notation "k₀" => trialityFixedField K σ.toRingHom

omit [Finite K] in
theorem fixed_of_H_mem {μ : K} (hμ : Xr d4H μ ∈ C₀) : σ μ = μ := by
  have hΓ := graphFixedRootGroup_le TwistTag.D4 K τ₀ hμ
  have hF : twistHom TwistTag.D4 K τ₀ (Xr d4H μ) = Xr d4H μ :=
    ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 hΓ).2
  have hroot : IsRoot TwistTag.D4.tag d4H := isRoot_of_d4 (by decide +kernel)
  obtain ⟨ε, hε, hconj⟩ := diagramMap_conj_pinnedX (K := K) TwistTag.D4 hroot
  have hε1 : ε = 1 := by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have h0 : (ε + 1) * (ε + 1) = 0 := by linear_combination hε + (ε + 1) * h2
    rw [eq_neg_of_add_eq_zero_left (mul_self_eq_zero.1 h0), CharTwo.neg_eq]
  have hρ : permLattice TwistTag.D4.perm d4H = d4H := by decide
  have hσ' : Units.map (entrywiseHom τ₀) (Xr d4H μ) = Xr d4H (τ₀ μ) :=
    Units.ext (entrywise_pinnedX τ₀ d4H μ)
  rw [twistHom_apply, hσ', hconj, hρ, hε1, one_mul] at hF
  exact pinnedX_injective _ _ _ hF

include hσ3 in
theorem borel_conj_H_one {b : ModGL TwistTag.D4.tag K}
    (hb : b ∈ graphFixedRootBorel TwistTag.D4 K τ₀) :
    ∃ y : K, σ y = y ∧ b * Xr d4H 1 * b⁻¹ = Xr d4H y := by
  obtain ⟨y, hy⟩ := borel_conj_H σ hσ3 hb 1
  refine ⟨y, fixed_of_H_mem σ ?_, hy⟩
  rw [← hy]
  have hbC := graphFixedRootBorel_le TwistTag.D4 K τ₀ hb
  exact mul_mem (mul_mem hbC (Xr_H_mem_C0 σ hσ3 (map_one σ))) (inv_mem hbC)

theorem orderOf_H_negH_dvd_fixed {μ lam : K} (hμ : σ μ = μ) (hlam : σ lam = lam) :
    orderOf (Xr d4H μ * Xr (-d4H) lam) ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) k₀) := by
  set n := canonicalRep (coxeterSystem TwistTag.D4.tag) K (rB * rA)
  have hC : (rB * rA) • d4C = d4H := by rw [mul_smul, rA_C, rB_P]
  have h1 : n * Xr d4C μ * n⁻¹ = Xr d4H μ := by
    rw [canonicalRep_conj_charTwo' _ (isRoot_of_d4 (by decide +kernel)), hC]
  have h2 : n * Xr (-d4C) lam * n⁻¹ = Xr (-d4H) lam := by
    rw [canonicalRep_conj_charTwo' _ (isRoot_of_d4 (by decide +kernel)), smul_neg, hC]
  rw [← h1, ← h2, ← conj_mul2, orderOf_conj']
  exact orderOf_C_negC_dvd_of_mem _ (mem_trialityFixedField.2 hμ)
    (mem_trialityFixedField.2 hlam)

include hσ3 in
theorem order_mul_conj_fixed {g : ModGL TwistTag.D4.tag K} (hg : g ∈ C₀) :
    orderOf (Xr d4H 1 * (g * Xr d4H 1 * g⁻¹)) ∣ 4 ∨
      orderOf (Xr d4H 1 * (g * Xr d4H 1 * g⁻¹)) ∣
        Nat.card (Matrix.SpecialLinearGroup (Fin 2) k₀) := by
  have hg' : g ∈ (C₀ : Set (ModGL TwistTag.D4.tag K)) := hg
  rw [graphFixedRootGroup_eq_iUnion σ.surjective] at hg'
  obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hg'
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_graphFixedRootBruhatCell.1 hw
  obtain ⟨lam, hlamσ, hlam⟩ := borel_conj_H_one σ hσ3 hb'
  obtain ⟨μ, hμσ, hμ⟩ := borel_conj_H_one σ hσ3 (inv_mem hb)
  have hroot : IsRoot TwistTag.D4.tag ((w : WeylGroup TwistTag.D4.tag) • d4H) :=
    IsRoot.smul (isRoot_of_d4 (by decide +kernel)) _
  have hfixw : permLattice TwistTag.D4.perm ((w : WeylGroup TwistTag.D4.tag) • d4H) =
      (w : WeylGroup TwistTag.D4.tag) • d4H := by
    rw [← weylTwist_smul_permLattice, (mem_relWeylTwist TwistTag.D4).1 w.2]
    congr 1
    exact List.ofFn_injective (by decide +kernel)
  have e1 : (b * canonicalRep (coxeterSystem TwistTag.D4.tag) K (w : WeylGroup TwistTag.D4.tag) *
      b') * Xr d4H 1 * (b * canonicalRep (coxeterSystem TwistTag.D4.tag) K
        (w : WeylGroup TwistTag.D4.tag) * b')⁻¹ =
      b * Xr ((w : WeylGroup TwistTag.D4.tag) • d4H) lam * b⁻¹ := by
    rw [← canonicalRep_conj_charTwo' _ (isRoot_of_d4 (by decide +kernel)) lam, ← hlam]
    group
  have e2 : Xr d4H 1 * (b * Xr ((w : WeylGroup TwistTag.D4.tag) • d4H) lam * b⁻¹) =
      b * (Xr d4H μ * Xr ((w : WeylGroup TwistTag.D4.tag) • d4H) lam) * b⁻¹ := by
    rw [← hμ, inv_inv]; group
  rw [e1, e2, orderOf_conj']
  rcases rho_fixed_roots hroot hfixw with h | h | h | h | h | h <;> rw [h]
  · exact Or.inl ((orderOf_dvd_of_pow_eq_one
      (pow_two_of_comm (by decide +kernel) μ lam)).trans (by norm_num))
  · exact Or.inl ((orderOf_dvd_of_pow_eq_one
      (pow_two_of_comm (by decide +kernel) μ lam)).trans (by norm_num))
  · exact Or.inl ((orderOf_dvd_of_pow_eq_one (pow_two_HH μ lam)).trans (by norm_num))
  · exact Or.inl (orderOf_dvd_of_pow_eq_one (pow_four_of_sum (γ := d4P) (by decide +kernel) μ lam))
  · exact Or.inl (orderOf_dvd_of_pow_eq_one (pow_four_of_sum (γ := d4C) (by decide +kernel) μ lam))
  · exact Or.inr (orderOf_H_negH_dvd_fixed σ hμσ hlamσ)

include hσ3 in
theorem not_conj_H_of_inverts_fixed {y t : C₀} (hyt : y * t * y⁻¹ = t⁻¹) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpk : ¬ p ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) k₀))
    (hdvd : p ∣ orderOf t) : ¬ ConjC σ (y : ModGL TwistTag.D4.tag K) (Xr d4H 1) := by
  rintro ⟨c, hc, hcy⟩
  have hyt' : (y : ModGL TwistTag.D4.tag K) * t * (y : ModGL TwistTag.D4.tag K)⁻¹ =
      (t : ModGL TwistTag.D4.tag K)⁻¹ := by
    have h := congrArg Subtype.val hyt
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h
  have ht'C : c * (t : ModGL TwistTag.D4.tag K) * c⁻¹ ∈ C₀ :=
    mul_mem (mul_mem hc t.2) (inv_mem hc)
  have hz : Xr d4H 1 * (c * t * c⁻¹) * (Xr d4H 1)⁻¹ = (c * t * c⁻¹)⁻¹ := by
    rw [← hcy]
    calc c * y * c⁻¹ * (c * t * c⁻¹) * (c * y * c⁻¹)⁻¹ =
        c * ((y : ModGL TwistTag.D4.tag K) * t * (y : ModGL TwistTag.D4.tag K)⁻¹) * c⁻¹ := by
          group
      _ = (c * t * c⁻¹)⁻¹ := by rw [hyt']; group
  have hprod : Xr d4H 1 * ((c * t * c⁻¹) * Xr d4H 1 * (c * t * c⁻¹)⁻¹) =
      (c * (t : ModGL TwistTag.D4.tag K) * c⁻¹)⁻¹ *
        (c * (t : ModGL TwistTag.D4.tag K) * c⁻¹)⁻¹ := by
    have hzinv : (Xr d4H (1 : K))⁻¹ = Xr d4H 1 := Xr_inv _ _
    calc Xr d4H 1 * ((c * t * c⁻¹) * Xr d4H 1 * (c * t * c⁻¹)⁻¹) =
        (Xr d4H 1 * (c * t * c⁻¹) * (Xr d4H 1)⁻¹) * (c * t * c⁻¹)⁻¹ := by rw [hzinv]; group
      _ = _ := by rw [hz]
  have hot : orderOf (c * (t : ModGL TwistTag.D4.tag K) * c⁻¹) = orderOf t := by
    rw [orderOf_conj', Subgroup.orderOf_coe]
  have hdvd' : p ∣ orderOf (Xr d4H 1 * ((c * t * c⁻¹) * Xr d4H 1 * (c * t * c⁻¹)⁻¹)) := by
    rw [hprod, ← sq]
    exact B42Disp.dvd_orderOf_sq hp hp2 (by rw [orderOf_inv, hot]; exact hdvd)
  rcases order_mul_conj_fixed σ hσ3 ht'C with h4 | hSL
  · have h2 : p ∣ 2 ^ 2 := hdvd'.trans h4
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2))
  · exact hpk (hdvd'.trans hSL)

end Bruhat

section Class

variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] (hK : Nat.card K = (2 ^ f) ^ 3)
  (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))

local notation "C₀" => graphFixedRootGroup TwistTag.D4 K σ.toRingHom

include hf hK hσ in
theorem conjC_ox₁_of_inverts {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {d : ℕ}
    (hd : (d : ℤ) = ((2 ^ f : ℕ) : ℤ) ^ 2 + ε * (2 ^ f : ℕ) + 1) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpd : p ∣ d) {y t : C₀} (hy : y * y = 1) (hy1 : y ≠ 1)
    (hyt : y * t * y⁻¹ = t⁻¹) (hdvd : p ∣ orderOf t) :
    ConjC σ (y : ModGL TwistTag.D4.tag K) (ox₁ σ 1) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have := charP_two_of_card hf hK
  have hσ3 := sigma_cube hK σ hσ
  have hpk :
      ¬ p ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) (trialityFixedField K σ.toRingHom)) := by
    rw [card_SL2_field, card_fixedField hf hK σ hσ]
    exact not_dvd_two_pow_mul hε hd hp hp3 hpd
  rcases involution_conj σ hσ3 y hy hy1 with hH | hx
  · exact absurd hH (not_conj_H_of_inverts_fixed σ hσ3 hyt hp (by omega) hpk hdvd)
  · exact hx

include hf hK hσ in
theorem exists_threeSix_classB {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {d : ℕ}
    (hd : (d : ℤ) = ((2 ^ f : ℕ) : ℤ) ^ 2 + ε * (2 ^ f : ℕ) + 1) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpd : p ∣ d) :
    ∃ (R : Subgroup C₀) (i j h : C₀),
      (∀ a ∈ R, ∀ b ∈ R, a * b = b * a) ∧ (∀ r ∈ R, r ^ p = 1) ∧ Nat.card R = p ^ 2 ∧
      IsQ8Data R i j h ∧ i * i * (i * i) = 1 ∧
      ConjC σ ((i * i : C₀) : ModGL TwistTag.D4.tag K) (ox₁ σ 1) ∧
      ∀ x : C₀, orderOf x = p → ∃ c : C₀, c * x * c⁻¹ ∈ R := by
  obtain ⟨R, i, j, h, hRc, hRp, hRcard, hq, hii, hconj⟩ :=
    exists_threeSix_q8 hf hK σ hσ hε hd hp hp3 hpd
  refine ⟨R, i, j, h, hRc, hRp, hRcard, hq, hii, ?_, hconj⟩
  have : Fact p.Prime := ⟨hp⟩
  have hRne : R ≠ ⊥ := by
    intro hR
    rw [hR, Subgroup.card_bot] at hRcard
    have := hp.one_lt
    have : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero this
    omega
  obtain ⟨⟨t, htR⟩, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hRne
  have ht1' : t ≠ 1 := fun h' => ht1 (Subtype.ext h')
  have hto : orderOf t = p := orderOf_eq_prime (hRp t htR) ht1'
  have hyt : i * i * t * (i * i)⁻¹ = t⁻¹ := hq.inv_ii t htR
  have hy1 : i * i ≠ 1 := by
    intro h1
    rw [h1, one_mul, inv_one, mul_one] at hyt
    have h2 : t ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 1 [hyt]
      exact inv_mul_cancel t
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [hto] at h3
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  exact conjC_ox₁_of_inverts hf hK σ hσ hε hd hp hp3 hpd hii hy1 hyt (by rw [hto])

end Class

end CFSG.Quasithin.B45Tor
