module

public import CFSG.LocalAnalysis.StandardType.GGSixTrialityL613KG
public import CFSG.LocalAnalysis.StandardType.GGHypSixD4RankClass
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalOrthogonalShearCModel

public section

namespace CFSG.StandardType

namespace L613KG

open Module CFSG.StandardType.Triality CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.LieType.Universal.Spin
  CFSG.RankThree.PartOne.AUTSL CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.StandardType.D4Rank QuadraticMap
open scoped Matrix

variable {K : Type} [Field K]

section Coord

noncomputable abbrev ie (k : Fin 4) : Fin (2 * 4) := plusIndexEquiv 4 (.inl k)

noncomputable abbrev jf (k : Fin 4) : Fin (2 * 4) := plusIndexEquiv 4 (.inr k)

theorem ie_ne_jf (k l : Fin 4) : ie k ≠ jf l :=
  (plusIndexEquiv 4).injective.ne Sum.inl_ne_inr

theorem ie_injective : Function.Injective ie :=
  fun _ _ h => Sum.inl_injective ((plusIndexEquiv 4).injective h)

theorem jf_injective : Function.Injective jf :=
  fun _ _ h => Sum.inr_injective ((plusIndexEquiv 4).injective h)

theorem ie_or_jf (i : Fin (2 * 4)) : (∃ k, i = ie k) ∨ ∃ k, i = jf k := by
  obtain ⟨s, rfl⟩ := (plusIndexEquiv 4).surjective i
  rcases s with k | k
  · exact Or.inl ⟨k, rfl⟩
  · exact Or.inr ⟨k, rfl⟩

theorem coordQ_apply (v : Fin (2 * 4) → K) :
    coordinateQuadPlus 4 K v = ∑ k, v (ie k) * v (jf k) :=
  coordinateQuadPlus_apply 4 K v

theorem polar_single_ie_jf (k : Fin 4) :
    polar (coordinateQuadPlus 4 K) (Pi.single (ie k) 1) (Pi.single (jf k) 1) = 1 := by
  rw [← AutOm.pvec_true, ← AutOm.pvec_false]
  exact AutOm.polar_pvec_not k true

theorem odd_card_units_charTwo [Finite K] [CharP K 2] : Odd (Nat.card Kˣ) := by
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hu2 : (u : K) * u = 1 := by
    rw [← Units.val_mul, ← pow_two, ← hu, pow_orderOf_eq_one, Units.val_one]
  have hu1 : u ≠ 1 := fun h => by
    rw [h, orderOf_one] at hu
    exact absurd hu (by norm_num)
  have h0 : ((u : K) - 1) ^ 2 = 0 := by
    have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination hu2 + (1 - (u : K)) * h2K
  exact hu1 (Units.ext (by rw [Units.val_one]; exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero
    |>.mp h0)))

end Coord

section Lin

variable [Finite K] [CharP K 2]

theorem mem_om8_of_lin (L : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K))
    (hL : ∀ v, coordinateQuadPlus 4 K (L v) = coordinateQuadPlus 4 K v)
    (hodd : Odd (orderOf L)) : matrixLinearIso.symm L ∈ matrixDerived (coordinateQuadPlus 4 K) := by
  have hreg := regular_coordinateQuadPlus 4 K (by norm_num)
  refine CFSG.SeitzReduction.OrthogonalShearC.mem_matrixDerived_of_odd hreg.1 hreg.2 ?_ ?_
  · rw [mem_matrixIsometries_iff]
    intro v
    rw [← matrixLinearIso_apply_eq, MulEquiv.apply_symm_apply]
    exact hL v
  · rwa [MulEquiv.orderOf_eq]

@[expose] noncomputable def om8OfLin (L : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K))
    (hL : ∀ v, coordinateQuadPlus 4 K (L v) = coordinateQuadPlus 4 K v)
    (hodd : Odd (orderOf L)) : Om8 K :=
  ⟨matrixLinearIso.symm L, mem_om8_of_lin L hL hodd⟩

theorem act_om8OfLin (L : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K))
    (hL : ∀ v, coordinateQuadPlus 4 K (L v) = coordinateQuadPlus 4 K v)
    (hodd : Odd (orderOf L)) (v : Fin (2 * 4) → K) : act (om8OfLin L hL hodd) v = L v := by
  change (matrixLinearIso.symm L).val *ᵥ v = L v
  rw [← matrixLinearEquiv_apply, ← matrixLinearIso_apply_eq, MulEquiv.apply_symm_apply]

omit [Finite K] [CharP K 2] in
theorem om8_ext {x y : Om8 K} (h : ∀ v, act x v = act y v) : x = y :=
  Subtype.ext (gl_eq_of_mulVec h)

end Lin

section Torus

@[expose] noncomputable def diagHom :
    (Fin (2 * 4) → Kˣ) →* ((Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) where
  toFun μ := LinearEquiv.piCongrRight fun i => LinearEquiv.smulOfUnit (μ i)
  map_one' := by
    ext v i
    change (((1 : Fin (2 * 4) → Kˣ) i : Kˣ) : K) * v i = v i
    simp
  map_mul' μ ν := by
    ext v i
    change (((μ * ν) i : Kˣ) : K) * v i = (μ i : K) * ((ν i : K) * v i)
    simp [mul_assoc]

theorem diagHom_apply (μ : Fin (2 * 4) → Kˣ) (v : Fin (2 * 4) → K) (i : Fin (2 * 4)) :
    diagHom μ v i = (μ i : K) * v i := rfl

@[expose] noncomputable def twHom : (Fin 4 → Kˣ) →* (Fin (2 * 4) → Kˣ) where
  toFun c i := Sum.elim c (fun k => (c k)⁻¹) ((plusIndexEquiv 4).symm i)
  map_one' := by
    funext i
    obtain ⟨s, rfl⟩ := (plusIndexEquiv 4).surjective i
    rcases s with k | k <;> simp
  map_mul' c d := by
    funext i
    obtain ⟨s, rfl⟩ := (plusIndexEquiv 4).surjective i
    rcases s with k | k
    · simp
    · simp only [Equiv.symm_apply_apply, Sum.elim_inr, Pi.mul_apply, mul_inv_rev]
      exact mul_comm _ _

theorem twHom_ie (c : Fin 4 → Kˣ) (k : Fin 4) : twHom c (ie k) = c k := by
  simp [twHom]

theorem twHom_jf (c : Fin 4 → Kˣ) (k : Fin 4) : twHom c (jf k) = (c k)⁻¹ := by
  simp [twHom]

theorem coordQ_diag_tw (c : Fin 4 → Kˣ) (v : Fin (2 * 4) → K) :
    coordinateQuadPlus 4 K (diagHom (twHom c) v) = coordinateQuadPlus 4 K v := by
  rw [coordQ_apply, coordQ_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [diagHom_apply, diagHom_apply, twHom_ie, twHom_jf]
  have h : (c k : K) * ((c k)⁻¹ : Kˣ) = 1 := Units.mul_inv (c k)
  calc (c k : K) * v (ie k) * (((c k)⁻¹ : Kˣ) * v (jf k))
      = ((c k : K) * ((c k)⁻¹ : Kˣ)) * (v (ie k) * v (jf k)) := by ring
    _ = v (ie k) * v (jf k) := by rw [h, one_mul]

variable [Finite K] [CharP K 2]

theorem odd_orderOf_diagHom (μ : Fin (2 * 4) → Kˣ) : Odd (orderOf (diagHom μ)) := by
  refine Odd.of_dvd_nat (odd_card_units_charTwo (K := K)) (orderOf_dvd_of_pow_eq_one ?_)
  rw [← map_pow]
  have h : μ ^ Nat.card Kˣ = 1 := by
    funext i
    simp [pow_card_eq_one']
  rw [h, map_one]

@[expose] noncomputable def dg (c : Fin 4 → Kˣ) : Om8 K :=
  om8OfLin (diagHom (twHom c)) (coordQ_diag_tw c) (odd_orderOf_diagHom _)

theorem act_dg (c : Fin 4 → Kˣ) (v : Fin (2 * 4) → K) :
    act (dg c) v = fun i => (twHom c i : K) * v i :=
  act_om8OfLin _ _ _ v

@[expose] noncomputable def dgHom : (Fin 4 → Kˣ) →* Om8 K where
  toFun := dg
  map_one' := om8_ext fun v => by
    rw [act_dg, act_one, map_one]
    funext i
    simp
  map_mul' c d := om8_ext fun v => by
    rw [act_mul, act_dg, act_dg, act_dg, map_mul]
    funext i
    simp only [Pi.mul_apply, Units.val_mul]
    ring

theorem dgHom_apply (c : Fin 4 → Kˣ) : dgHom c = dg (K := K) c := rfl

end Torus

section Perm

@[expose] noncomputable def sig3 : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 1 2

theorem sig3_zero : sig3 0 = 1 := by decide
theorem sig3_one : sig3 1 = 2 := by decide
theorem sig3_two : sig3 2 = 0 := by decide
theorem sig3_three : sig3 3 = 3 := by decide

theorem sig3_cube_apply (k : Fin 4) : sig3 (sig3 (sig3 k)) = k := by
  fin_cases k <;> decide

@[expose] noncomputable def pi3 : Equiv.Perm (Fin (2 * 4)) :=
  ((plusIndexEquiv 4).symm.trans (Equiv.sumCongr sig3 sig3)).trans (plusIndexEquiv 4)

theorem pi3_ie (k : Fin 4) : pi3 (ie k) = ie (sig3 k) := by
  simp [pi3]

theorem pi3_jf (k : Fin 4) : pi3 (jf k) = jf (sig3 k) := by
  simp [pi3]

theorem pi3_cube_apply (i : Fin (2 * 4)) : pi3 (pi3 (pi3 i)) = i := by
  rcases ie_or_jf i with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [pi3_ie, pi3_ie, pi3_ie, sig3_cube_apply]
  · rw [pi3_jf, pi3_jf, pi3_jf, sig3_cube_apply]

@[expose] noncomputable def permLin : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K) :=
  LinearEquiv.funCongrLeft K K pi3

theorem permLin_apply (v : Fin (2 * 4) → K) : permLin v = v ∘ pi3 := rfl

theorem coordQ_permLin (v : Fin (2 * 4) → K) :
    coordinateQuadPlus 4 K (permLin v) = coordinateQuadPlus 4 K v := by
  rw [coordQ_apply, coordQ_apply, permLin_apply]
  simp only [Function.comp_apply, pi3_ie, pi3_jf]
  exact Equiv.sum_comp sig3 (fun k => v (ie k) * v (jf k))

theorem permLin_cube : (permLin (K := K)) ^ 3 = 1 := by
  refine LinearEquiv.ext fun v => funext fun i => ?_
  rw [pow_succ, pow_succ, pow_one, LinearEquiv.mul_apply, LinearEquiv.mul_apply, permLin_apply,
    permLin_apply, permLin_apply]
  simp only [Function.comp_apply]
  rw [pi3_cube_apply]
  rfl

theorem odd_orderOf_permLin : Odd (orderOf (permLin (K := K))) :=
  Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one permLin_cube)

variable [Finite K] [CharP K 2]

@[expose] noncomputable def wg : Om8 K := om8OfLin permLin coordQ_permLin odd_orderOf_permLin

theorem act_wg (v : Fin (2 * 4) → K) : act (wg (K := K)) v = v ∘ pi3 :=
  act_om8OfLin _ _ _ v

theorem wg_cube : (wg (K := K)) ^ 3 = 1 := om8_ext fun v => by
  rw [pow_succ, pow_succ, pow_one, act_mul, act_mul, act_wg, act_wg, act_wg, act_one]
  funext i
  simp only [Function.comp_apply]
  rw [pi3_cube_apply]

theorem wg_mul_dg (c : Fin 4 → Kˣ) : wg * dg c = dg (fun k => c (sig3 k)) * wg := by
  refine om8_ext fun v => ?_
  rw [act_mul, act_mul, act_wg, act_dg, act_dg, act_wg]
  funext i
  simp only [Function.comp_apply]
  congr 1
  rcases ie_or_jf i with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [pi3_ie, twHom_ie, twHom_ie]
  · rw [pi3_jf, twHom_jf, twHom_jf]

end Perm

section PZero

variable [Finite K] [CharP K 2]

@[expose] noncomputable def eTorus : Subgroup (Om8 K) :=
  ((powMonoidHom 3 : (Fin 4 → Kˣ) →* (Fin 4 → Kˣ)).ker).map dgHom

theorem dg_mem_eTorus {c : Fin 4 → Kˣ} (hc : c ^ 3 = 1) : dg c ∈ eTorus (K := K) :=
  ⟨c, by rw [SetLike.mem_coe, MonoidHom.mem_ker, powMonoidHom_apply, hc], rfl⟩

theorem isPGroup_eTorus : IsPGroup 3 (eTorus (K := K)) := by
  rintro ⟨_, c, hc, rfl⟩
  refine ⟨1, Subtype.ext ?_⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker, powMonoidHom_apply] at hc
  rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, ← map_pow, hc, map_one]

theorem isPGroup_zpowers_wg : IsPGroup 3 (Subgroup.zpowers (wg (K := K))) := by
  rintro ⟨_, k, rfl⟩
  refine ⟨1, Subtype.ext ?_⟩
  rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
  change (wg ^ k) ^ 3 = 1
  rw [← zpow_natCast, ← zpow_mul, mul_comm k, zpow_mul, zpow_natCast, wg_cube, one_zpow]

theorem wg_mem_normalizer : wg ∈ Subgroup.normalizer ((eTorus (K := K)) : Set (Om8 K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨c, hc, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, powMonoidHom_apply] at hc
    have e : wg * dgHom c * wg⁻¹ = dg (fun k => c (sig3 k)) := by
      rw [dgHom_apply, wg_mul_dg, mul_inv_cancel_right]
    rw [e]
    refine dg_mem_eTorus ?_
    funext k
    have := congrFun hc (sig3 k)
    simpa using this
  · rintro ⟨c, hc, hce⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, powMonoidHom_apply] at hc
    have e1 : wg * dg (fun k => c (sig3.symm k)) = dg c * wg := by
      rw [wg_mul_dg]
      congr 2
      funext k
      rw [Equiv.symm_apply_apply]
    have e2 : h = dg (fun k => c (sig3.symm k)) := by
      have h1 : dg (fun k => c (sig3.symm k)) = wg⁻¹ * (dg c * wg) := by
        rw [← e1, inv_mul_cancel_left]
      rw [h1, ← dgHom_apply, hce]
      group
    rw [e2]
    refine dg_mem_eTorus ?_
    funext k
    have := congrFun hc (sig3.symm k)
    simpa using this

@[expose] noncomputable def pZero : Subgroup (Om8 K) := eTorus ⊔ Subgroup.zpowers wg

theorem isPGroup_pZero : IsPGroup 3 (pZero (K := K)) :=
  isPGroup_eTorus.to_sup_of_normal_left' isPGroup_zpowers_wg
    (Subgroup.zpowers_le.mpr wg_mem_normalizer)

theorem dg_mem_pZero {c : Fin 4 → Kˣ} (hc : c ^ 3 = 1) : dg c ∈ pZero (K := K) :=
  Subgroup.mem_sup_left (dg_mem_eTorus hc)

theorem wg_mem_pZero : wg ∈ pZero (K := K) :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

end PZero

end L613KG

end CFSG.StandardType
