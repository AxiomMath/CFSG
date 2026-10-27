module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian
public import CFSG.RankThree.PartTwo.Sec19.Step1914MoreProofMat

public section

namespace CFSG.RankThree.PartTwo.Sec12

namespace Hering129KM2

open scoped Matrix
open CFSG.RankThree.PartTwo.Sec19.Step1914MoreProof (SL23 qOne tOne tTwo zNeg sl23_eq_word)

theorem closure_qOne_tOne : Subgroup.closure ({qOne, tOne} : Set SL23) = ⊤ := by
  have hq : qOne ∈ Subgroup.closure ({qOne, tOne} : Set SL23) :=
    Subgroup.subset_closure (by simp)
  have ht : tOne ∈ Subgroup.closure ({qOne, tOne} : Set SL23) :=
    Subgroup.subset_closure (by simp)
  have ht2 : tTwo ∈ Subgroup.closure ({qOne, tOne} : Set SL23) := by
    have h : tTwo * qOne = qOne * tOne ^ 2 := by decide +kernel
    rw [← eq_mul_inv_iff_mul_eq] at h
    rw [h]
    exact mul_mem (mul_mem hq (pow_mem ht 2)) (inv_mem hq)
  have hz : zNeg ∈ Subgroup.closure ({qOne, tOne} : Set SL23) :=
    pow_mem (mul_mem (mul_mem ht (pow_mem ht2 2)) ht) 2
  refine eq_top_iff.mpr fun g _ => ?_
  obtain ⟨i, a, b, c, rfl⟩ := sl23_eq_word g
  exact mul_mem (mul_mem (mul_mem (pow_mem hz _) (pow_mem ht _)) (pow_mem ht2 _)) (pow_mem ht _)

theorem mulVec_mulVec_sl (γ δ : SL23) (w : Fin 2 → ZMod 3) :
    (γ : Matrix (Fin 2) (Fin 2) (ZMod 3)) *ᵥ ((δ : Matrix (Fin 2) (Fin 2) (ZMod 3)) *ᵥ w) =
      ((γ * δ : SL23) : Matrix (Fin 2) (Fin 2) (ZMod 3)) *ᵥ w := by
  rw [Matrix.mulVec_mulVec]
  rfl

theorem one_mulVec_sl (w : Fin 2 → ZMod 3) :
    ((1 : SL23) : Matrix (Fin 2) (Fin 2) (ZMod 3)) *ᵥ w = w := by
  rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

@[expose] def matAut : SL23 →* MulAut (Multiplicative (Fin 2 → ZMod 3)) where
  toFun γ :=
    { toFun := fun v => Multiplicative.ofAdd ((γ : Matrix (Fin 2) (Fin 2) (ZMod 3)) *ᵥ v.toAdd)
      invFun := fun v =>
        Multiplicative.ofAdd (((γ⁻¹ : SL23) : Matrix (Fin 2) (Fin 2) (ZMod 3)) *ᵥ v.toAdd)
      left_inv := fun v => by
        change Multiplicative.ofAdd (((γ⁻¹ : SL23) : Matrix (Fin 2) (Fin 2) (ZMod 3)) *ᵥ
          ((γ : Matrix (Fin 2) (Fin 2) (ZMod 3)) *ᵥ v.toAdd)) = v
        rw [mulVec_mulVec_sl, inv_mul_cancel, one_mulVec_sl, ofAdd_toAdd]
      right_inv := fun v => by
        change Multiplicative.ofAdd ((γ : Matrix (Fin 2) (Fin 2) (ZMod 3)) *ᵥ
          (((γ⁻¹ : SL23) : Matrix (Fin 2) (Fin 2) (ZMod 3)) *ᵥ v.toAdd)) = v
        rw [mulVec_mulVec_sl, mul_inv_cancel, one_mulVec_sl, ofAdd_toAdd]
      map_mul' := fun v w => by
        change Multiplicative.ofAdd ((γ : Matrix (Fin 2) (Fin 2) (ZMod 3)) *ᵥ
          (v.toAdd + w.toAdd)) = _
        rw [Matrix.mulVec_add, ofAdd_add] }
  map_one' := by
    refine MulEquiv.ext fun v => ?_
    change Multiplicative.ofAdd (((1 : SL23) : Matrix (Fin 2) (Fin 2) (ZMod 3)) *ᵥ v.toAdd) = v
    rw [one_mulVec_sl, ofAdd_toAdd]
  map_mul' γ δ := by
    refine MulEquiv.ext fun v => ?_
    change Multiplicative.ofAdd (((γ * δ : SL23) : Matrix (Fin 2) (Fin 2) (ZMod 3)) *ᵥ v.toAdd) =
      Multiplicative.ofAdd ((γ : Matrix (Fin 2) (Fin 2) (ZMod 3)) *ᵥ
        ((δ : Matrix (Fin 2) (Fin 2) (ZMod 3)) *ᵥ v.toAdd))
    rw [mulVec_mulVec_sl]

theorem matAut_injective : Function.Injective matAut := by
  intro γ δ h
  apply Subtype.ext
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
  exact congrArg (fun σ : MulAut (Multiplicative (Fin 2 → ZMod 3)) =>
    Multiplicative.toAdd (σ (Multiplicative.ofAdd v))) h

variable {G : Type} [Group G] {x₁ x₂ : G}

theorem zpow_val_intCast {x : G} (h : x ^ 3 = 1) (k : ℤ) :
    x ^ (((k : ZMod 3).val : ℕ) : ℤ) = x ^ k := by
  rw [ZMod.val_intCast, Nat.cast_ofNat, ← Sec4.zpow_emod_three h k]

@[expose] def pt (x₁ x₂ : G) (v : Fin 2 → ZMod 3) : G := x₁ ^ ((v 0).val : ℤ) * x₂ ^ ((v 1).val : ℤ)

theorem pt_mem (x₁ x₂ : G) (v : Fin 2 → ZMod 3) :
    pt x₁ x₂ v ∈ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ :=
  mul_mem (Subgroup.mem_sup_left (zpow_mem (Subgroup.mem_zpowers x₁) _))
    (Subgroup.mem_sup_right (zpow_mem (Subgroup.mem_zpowers x₂) _))

theorem pt_eq (h1 : x₁ ^ 3 = 1) (h2 : x₂ ^ 3 = 1) {v : Fin 2 → ZMod 3} {i j : ℤ}
    (hi : v 0 = i) (hj : v 1 = j) : pt x₁ x₂ v = x₁ ^ i * x₂ ^ j := by
  rw [pt, hi, hj, zpow_val_intCast h1, zpow_val_intCast h2]

theorem mul_nf (h12 : x₁ * x₂ = x₂ * x₁) (i j k l : ℤ) :
    x₁ ^ i * x₂ ^ j * (x₁ ^ k * x₂ ^ l) = x₁ ^ (i + k) * x₂ ^ (j + l) := by
  have hc : x₂ ^ j * x₁ ^ k = x₁ ^ k * x₂ ^ j := ((Commute.zpow_zpow h12 k j).eq).symm
  rw [_root_.zpow_add, _root_.zpow_add, mul_assoc, ← mul_assoc (x₂ ^ j), hc]
  simp only [mul_assoc]

theorem nf_zpow (h12 : x₁ * x₂ = x₂ * x₁) (a c n : ℤ) :
    (x₁ ^ a * x₂ ^ c) ^ n = x₁ ^ (a * n) * x₂ ^ (c * n) := by
  rw [(Commute.zpow_zpow h12 a c).mul_zpow, ← _root_.zpow_mul, ← _root_.zpow_mul]

theorem pt_add (h12 : x₁ * x₂ = x₂ * x₁) (h1 : x₁ ^ 3 = 1) (h2 : x₂ ^ 3 = 1)
    (v w : Fin 2 → ZMod 3) : pt x₁ x₂ (v + w) = pt x₁ x₂ v * pt x₁ x₂ w := by
  rw [pt_eq h1 h2 (i := ((v 0).val : ℤ) + ((w 0).val : ℤ))
    (j := ((v 1).val : ℤ) + ((w 1).val : ℤ)) (by simp) (by simp), pt, pt, mul_nf h12]

theorem mulVec_fin_two_zero (p q r s : ZMod 3) (v : Fin 2 → ZMod 3) :
    (!![p, q; r, s] *ᵥ v) 0 = p * v 0 + q * v 1 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem mulVec_fin_two_one (p q r s : ZMod 3) (v : Fin 2 → ZMod 3) :
    (!![p, q; r, s] *ᵥ v) 1 = r * v 0 + s * v 1 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem conj_pt (h12 : x₁ * x₂ = x₂ * x₁) (h1 : x₁ ^ 3 = 1) (h2 : x₂ ^ 3 = 1) {m : G}
    {a b c d : ℤ} (hm1 : m * x₁ * m⁻¹ = x₁ ^ a * x₂ ^ c) (hm2 : m * x₂ * m⁻¹ = x₁ ^ b * x₂ ^ d)
    (v : Fin 2 → ZMod 3) :
    m * pt x₁ x₂ v * m⁻¹ = pt x₁ x₂ (!![(a : ZMod 3), b; c, d] *ᵥ v) := by
  rw [pt_eq h1 h2 (v := !![(a : ZMod 3), b; c, d] *ᵥ v)
    (i := a * ((v 0).val : ℤ) + b * ((v 1).val : ℤ))
    (j := c * ((v 0).val : ℤ) + d * ((v 1).val : ℤ))
    (by rw [mulVec_fin_two_zero]; simp) (by rw [mulVec_fin_two_one]; simp)]
  calc m * pt x₁ x₂ v * m⁻¹
      = m * (x₁ ^ ((v 0).val : ℤ) * x₂ ^ ((v 1).val : ℤ)) * m⁻¹ := rfl
    _ = (m * x₁ * m⁻¹) ^ ((v 0).val : ℤ) * (m * x₂ * m⁻¹) ^ ((v 1).val : ℤ) := by
      rw [conj_zpow, conj_zpow]
      group
    _ = (x₁ ^ a * x₂ ^ c) ^ ((v 0).val : ℤ) * (x₁ ^ b * x₂ ^ d) ^ ((v 1).val : ℤ) := by
      rw [hm1, hm2]
    _ = _ := by rw [nf_zpow h12, nf_zpow h12, mul_nf h12]

@[expose] def ptHom (h12 : x₁ * x₂ = x₂ * x₁) (h1 : x₁ ^ 3 = 1) (h2 : x₂ ^ 3 = 1) :
    Multiplicative (Fin 2 → ZMod 3) →* (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ : Subgroup G)
    where
  toFun v := ⟨pt x₁ x₂ v.toAdd, pt_mem x₁ x₂ v.toAdd⟩
  map_one' := Subtype.ext (by simp [pt])
  map_mul' v w := Subtype.ext (pt_add h12 h1 h2 v.toAdd w.toAdd)

theorem ptHom_surjective (h12 : x₁ * x₂ = x₂ * x₁) (h1 : x₁ ^ 3 = 1) (h2 : x₂ ^ 3 = 1) :
    Function.Surjective (ptHom h12 h1 h2) := by
  rintro ⟨u, hu⟩
  obtain ⟨i, j, rfl⟩ := Sec4.exists_zpow_mul_of_mem_sup h12 hu
  exact ⟨Multiplicative.ofAdd ![(i : ZMod 3), (j : ZMod 3)], Subtype.ext (pt_eq h1 h2 rfl rfl)⟩

@[expose] noncomputable def coordEquiv (h12 : x₁ * x₂ = x₂ * x₁) (h1 : x₁ ^ 3 = 1) (h2 : x₂ ^ 3 = 1)
    (hcard : Nat.card (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ : Subgroup G) = 9) :
    Multiplicative (Fin 2 → ZMod 3) ≃* (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ : Subgroup G) :=
  MulEquiv.ofBijective (ptHom h12 h1 h2)
    ((ptHom_surjective h12 h1 h2).bijective_of_nat_card_le (by rw [hcard]; simp))

theorem coordEquiv_apply_coe (h12 : x₁ * x₂ = x₂ * x₁) (h1 : x₁ ^ 3 = 1) (h2 : x₂ ^ 3 = 1)
    (hcard : Nat.card (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ : Subgroup G) = 9)
    (v : Multiplicative (Fin 2 → ZMod 3)) :
    ((coordEquiv h12 h1 h2 hcard v : (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ : Subgroup G)) :
      G) = pt x₁ x₂ v.toAdd :=
  rfl

@[expose] noncomputable def theta (h12 : x₁ * x₂ = x₂ * x₁) (h1 : x₁ ^ 3 = 1) (h2 : x₂ ^ 3 = 1)
    (hcard : Nat.card (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ : Subgroup G) = 9) :
    SL23 →* MulAut (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ : Subgroup G) :=
  (MulAut.congr (coordEquiv h12 h1 h2 hcard)).toMonoidHom.comp matAut

theorem theta_apply_coord (h12 : x₁ * x₂ = x₂ * x₁) (h1 : x₁ ^ 3 = 1) (h2 : x₂ ^ 3 = 1)
    (hcard : Nat.card (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ : Subgroup G) = 9)
    (γ : SL23) (v : Multiplicative (Fin 2 → ZMod 3)) :
    ((theta h12 h1 h2 hcard γ (coordEquiv h12 h1 h2 hcard v) :
      (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ : Subgroup G)) : G) =
      pt x₁ x₂ ((γ : Matrix (Fin 2) (Fin 2) (ZMod 3)) *ᵥ v.toAdd) := by
  change ((coordEquiv h12 h1 h2 hcard (matAut γ ((coordEquiv h12 h1 h2 hcard).symm
    (coordEquiv h12 h1 h2 hcard v))) : (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ : Subgroup G)) :
      G) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

theorem theta_injective (h12 : x₁ * x₂ = x₂ * x₁) (h1 : x₁ ^ 3 = 1) (h2 : x₂ ^ 3 = 1)
    (hcard : Nat.card (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ : Subgroup G) = 9) :
    Function.Injective (theta h12 h1 h2 hcard) := by
  intro γ δ h
  apply matAut_injective
  apply (MulAut.congr (coordEquiv h12 h1 h2 hcard)).injective
  exact h

theorem normalizerMonoidHom_eq_theta (h12 : x₁ * x₂ = x₂ * x₁) (h1 : x₁ ^ 3 = 1)
    (h2 : x₂ ^ 3 = 1)
    (hcard : Nat.card (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ : Subgroup G) = 9) {m : G}
    (hmN : m ∈ Subgroup.normalizer
      ((Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ : Subgroup G) : Set G))
    {a b c d : ℤ} (hm1 : m * x₁ * m⁻¹ = x₁ ^ a * x₂ ^ c) (hm2 : m * x₂ * m⁻¹ = x₁ ^ b * x₂ ^ d)
    (γ : SL23) (hγ : (γ : Matrix (Fin 2) (Fin 2) (ZMod 3)) = !![(a : ZMod 3), b; c, d]) :
    (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂).normalizerMonoidHom ⟨m, hmN⟩ =
      theta h12 h1 h2 hcard γ := by
  ext u
  obtain ⟨v, rfl⟩ := (coordEquiv h12 h1 h2 hcard).surjective u
  rw [Sec4.normalizerMonoidHom_apply_coe, theta_apply_coord, coordEquiv_apply_coe, hγ]
  exact conj_pt h12 h1 h2 hm1 hm2 v.toAdd

theorem mem_normalizer_of_conj (h12 : x₁ * x₂ = x₂ * x₁)
    [Finite (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ : Subgroup G)] {m : G}
    (hm1 : m * x₁ * m⁻¹ ∈ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂)
    (hm2 : m * x₂ * m⁻¹ ∈ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂) :
    m ∈ Subgroup.normalizer
      ((Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ : Subgroup G) : Set G) := by
  set E := Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ with hE
  have hfwd : ∀ u ∈ E, m * u * m⁻¹ ∈ E := by
    intro u hu
    obtain ⟨i, j, rfl⟩ := Sec4.exists_zpow_mul_of_mem_sup h12 hu
    have e1 : m * (x₁ ^ i * x₂ ^ j) * m⁻¹ = (m * x₁ * m⁻¹) ^ i * (m * x₂ * m⁻¹) ^ j := by
      rw [conj_zpow, conj_zpow]
      group
    rw [e1]
    exact mul_mem (zpow_mem hm1 i) (zpow_mem hm2 j)
  let f : E → E := fun u => ⟨m * u * m⁻¹, hfwd u u.2⟩
  have hf : Function.Injective f := by
    intro u w h
    have h' : m * (u : G) * m⁻¹ = m * (w : G) * m⁻¹ := congrArg Subtype.val h
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h'))
  have hs : Function.Surjective f := Finite.injective_iff_surjective.mp hf
  refine Subgroup.mem_normalizer_iff.mpr fun u => ⟨hfwd u, fun hu => ?_⟩
  obtain ⟨w, hw⟩ := hs ⟨_, hu⟩
  have hw' : m * (w : G) * m⁻¹ = m * u * m⁻¹ := congrArg Subtype.val hw
  have hwu : (w : G) = u := mul_left_cancel (mul_right_cancel hw')
  rw [← hwu]
  exact w.2

end Hering129KM2

open Hering129KM2 in
open CFSG.RankThree.PartTwo.Sec19.Step1914MoreProof (qOne tOne) in
theorem nonempty_autIn_sl23 {G : Type} [Group G] (M : Subgroup G) {x₁ x₂ n₁ t : G}
    (h12 : x₁ * x₂ = x₂ * x₁) (h1 : x₁ ^ 3 = 1) (h2 : x₂ ^ 3 = 1)
    (hcard : Nat.card (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ : Subgroup G) = 9)
    (hn₁ : n₁ ∈ M) (hF1 : n₁ * x₁ * n₁⁻¹ = x₂⁻¹) (hF2 : n₁ * x₂ * n₁⁻¹ = x₁)
    (ht : t ∈ M) (ht1 : t * x₁ * t⁻¹ = x₁) (ht2 : t * x₂ * t⁻¹ = x₂ * x₁)
    (hdet : ∀ m ∈ M ⊓ Subgroup.normalizer
        ((Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ : Subgroup G) : Set G),
      ∃ a b c d : ℤ, (a * d - b * c) % 3 = 1 ∧ m * x₁ * m⁻¹ = x₁ ^ a * x₂ ^ c ∧
        m * x₂ * m⁻¹ = x₁ ^ b * x₂ ^ d) :
    Nonempty (Sec4.autIn M (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) := by
  have hfin : Finite (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ : Subgroup G) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hx₁E : x₁ ∈ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers x₁)
  have hx₂E : x₂ ∈ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers x₂)
  have hN₁ := mem_normalizer_of_conj h12 (m := n₁) (by rw [hF1]; exact inv_mem hx₂E)
    (by rw [hF2]; exact hx₁E)
  have hNt := mem_normalizer_of_conj h12 (m := t) (by rw [ht1]; exact hx₁E)
    (by rw [ht2]; exact mul_mem hx₂E hx₁E)
  have hS : theta h12 h1 h2 hcard qOne ∈ Sec4.autIn M (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂) :=
    Sec4.mem_autIn_iff.mpr ⟨n₁, hN₁, hn₁, normalizerMonoidHom_eq_theta h12 h1 h2 hcard hN₁
      (a := 0) (b := 1) (c := -1) (d := 0) (by rw [hF1]; simp) (by rw [hF2]; simp) qOne
      (by decide +kernel)⟩
  have hT : theta h12 h1 h2 hcard tOne ∈ Sec4.autIn M (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂) :=
    Sec4.mem_autIn_iff.mpr ⟨t, hNt, ht, normalizerMonoidHom_eq_theta h12 h1 h2 hcard hNt
      (a := 1) (b := 1) (c := 0) (d := 1) (by rw [ht1]; simp)
      (by rw [ht2, zpow_one, zpow_one, h12]) tOne (by decide +kernel)⟩
  have hrange : (theta h12 h1 h2 hcard).range =
      Sec4.autIn M (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂) := by
    apply le_antisymm
    · rw [MonoidHom.range_eq_map, ← closure_qOne_tOne, MonoidHom.map_closure,
        Subgroup.closure_le]
      rintro _ ⟨γ, hγ, rfl⟩
      rcases hγ with rfl | rfl
      · exact hS
      · exact hT
    · intro σ hσ
      obtain ⟨m, hmN, hmM, rfl⟩ := Sec4.mem_autIn_iff.mp hσ
      obtain ⟨a, b, c, d, hd, hm1, hm2⟩ := hdet m (Subgroup.mem_inf.mpr ⟨hmM, hmN⟩)
      have h3 : ((a * d - b * c : ℤ) : ZMod 3) = 1 := by
        rw [← ZMod.intCast_mod, Nat.cast_ofNat, hd, Int.cast_one]
      push_cast at h3
      exact ⟨⟨!![(a : ZMod 3), b; c, d], by rw [Matrix.det_fin_two_of]; exact h3⟩,
        (normalizerMonoidHom_eq_theta h12 h1 h2 hcard hmN hm1 hm2 _ rfl).symm⟩
  exact ⟨((MonoidHom.ofInjective (theta_injective h12 h1 h2 hcard)).trans
    (MulEquiv.subgroupCongr hrange)).symm⟩

end CFSG.RankThree.PartTwo.Sec12
