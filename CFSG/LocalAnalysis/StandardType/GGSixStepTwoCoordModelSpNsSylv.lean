module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSpNsFrame

public section

open Polynomial Module

namespace CFSG.StandardType

namespace CoordSpNs

section Sylv

variable {K : Type} [Field K] [Finite K] {g : K[X]} [Fact (Irreducible g)] {p : ℕ}
  [Fact p.Prime]

theorem galExp_le_galSigns (hζ : AdjoinRoot.root g ^ p = 1)
    (hprim : IsPrimitiveRoot (AdjoinRoot.root g) p) :
    CoordSL.galExp g hζ ≤ galSigns p (Nat.card K) := by
  rintro u ⟨σ, hσ⟩
  have : Finite (AdjoinRoot g) := CoordSL.finite_adjoinRoot
  obtain ⟨ℓ, hℓ⟩ := CharP.exists K
  have hℓp : ℓ.Prime := (CharP.char_is_prime_or_zero K ℓ).resolve_right
    (CharP.char_ne_zero_of_finite K ℓ)
  have : Fact ℓ.Prime := ⟨hℓp⟩
  obtain ⟨i, hi⟩ := FiniteField.exists_forall_apply_eq_pow K ℓ (AdjoinRoot g) σ
  have h1 : AdjoinRoot.root g ^ (u : ZMod p).val = AdjoinRoot.root g ^ (Nat.card K ^ i) := by
    rw [← hσ, hi]
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have h2 : (u : ZMod p).val % p = (Nat.card K ^ i) % p :=
    hprim.pow_inj (Nat.mod_lt _ hp0) (Nat.mod_lt _ hp0)
      (by rw [← pow_eq_pow_mod _ hζ, ← pow_eq_pow_mod _ hζ]; exact h1)
  have h3 : (u : ZMod p) = (Nat.card K : ZMod p) ^ i := by
    rw [← ZMod.natCast_zmod_val (u : ZMod p), (ZMod.natCast_eq_natCast_iff' _ _ _).mpr h2,
      Nat.cast_pow]
  by_cases hq : (Nat.card K : ZMod p) = 0
  · have hi0 : i = 0 := by
      by_contra hi0
      rw [hq, zero_pow hi0] at h3
      exact u.ne_zero h3
    have hu1 : u = 1 := Units.ext (by rw [h3, hi0, pow_zero, Units.val_one])
    rw [hu1]
    exact (galSigns p (Nat.card K)).one_mem
  · have hv : Units.mk0 _ hq ∈ galSigns p (Nat.card K) :=
      Subgroup.subset_closure (Or.inl (Units.val_mk0 hq))
    have hu : u = Units.mk0 _ hq ^ i :=
      Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, h3])
    rw [hu]
    exact (galSigns p (Nat.card K)).pow_mem hv i

omit [Finite K] in
theorem root_pow_val_ne_one (hprim : IsPrimitiveRoot (AdjoinRoot.root g) p) {a : ZMod p}
    (ha : a ≠ 0) : AdjoinRoot.root g ^ a.val ≠ 1 := by
  intro h
  apply ha
  have h1 := (hprim.pow_eq_one_iff_dvd _).mp h
  rw [← ZMod.natCast_zmod_val a, (ZMod.natCast_eq_zero_iff _ _).mpr h1]

omit [Finite K] in
theorem sd_sylvester [Finite K] (hζ : AdjoinRoot.root g ^ p = 1)
    (hprim : IsPrimitiveRoot (AdjoinRoot.root g) p) {a b : ZMod p}
    (hab : ∀ u ∈ galSigns p (Nat.card K), a ≠ u * b) (h0 : a ≠ 0 ∨ b ≠ 0)
    {f : AdjoinRoot g →ₗ[K] AdjoinRoot g}
    (hf : ∀ x, f (AdjoinRoot.root g ^ b.val * x) = AdjoinRoot.root g ^ a.val * f x) : f = 0 := by
  by_cases hb : b = 0
  · have ha : a ≠ 0 := h0.resolve_right (not_not.mpr hb)
    refine LinearMap.ext fun x => ?_
    have h1 := hf x
    rw [hb, ZMod.val_zero, pow_zero, one_mul] at h1
    have h2 : (AdjoinRoot.root g ^ a.val - 1) * f x = 0 := by rw [sub_mul, one_mul, ← h1, sub_self]
    rw [LinearMap.zero_apply]
    exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr (root_pow_val_ne_one hprim ha))
  · exact CoordSL.eq_zero_of_intertwine hζ hprim hb
      (fun u hu => hab u (galExp_le_galSigns hζ hprim hu)) hf

end Sylv

section Block

variable {K : Type} [Field K] {g : K[X]} [Fact (Irreducible g)] {p : ℕ}
  {D : Type} [AddCommGroup D] [Module K D] {c : D ≃ₗ[K] D}

theorem sd_e_pow {e : D ≃ₗ[K] AdjoinRoot g} (he : ∀ x, e (c x) = AdjoinRoot.root g * e x)
    (m : ℕ) (x : D) : e ((c ^ m) x) = AdjoinRoot.root g ^ m * e x := by
  induction m generalizing x with
  | zero => simp
  | succ m ih => rw [pow_apply_succ, he, ih, pow_succ', mul_assoc]

theorem pr_e_pow {e : D ≃ₗ[K] AdjoinRoot g × AdjoinRoot g}
    (he : ∀ x, e (c x) = (AdjoinRoot.root g * (e x).1, AdjoinRoot.root g ^ (p - 1) * (e x).2))
    (m : ℕ) (x : D) : e ((c ^ m) x) =
      (AdjoinRoot.root g ^ m * (e x).1, (AdjoinRoot.root g ^ (p - 1)) ^ m * (e x).2) := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
    rw [pow_apply_succ, he, ih]
    refine Prod.ext ?_ ?_
    · dsimp only
      rw [pow_succ', mul_assoc]
    · dsimp only
      rw [pow_succ' (AdjoinRoot.root g ^ (p - 1)) m, mul_assoc]

variable [Finite K] [Fact p.Prime]

omit [Finite K] in
theorem root_pred_pow_eq (hζ : AdjoinRoot.root g ^ p = 1) (b : ZMod p) :
    (AdjoinRoot.root g ^ (p - 1)) ^ b.val =
      AdjoinRoot.root g ^ ((((-1 : (ZMod p)ˣ) : ZMod p)) * b).val := by
  have hv : (((-1 : (ZMod p)ˣ) : ZMod p)).val = p - 1 := by
    rw [Units.val_neg, Units.val_one]
    exact val_neg_one_eq (Fact.out : p.Prime).one_lt.le
  rw [← CoordSL.pow_val_pow_val hζ, hv]

theorem block_sylvester (hbt : NsBlockType g p D c) (hζ : AdjoinRoot.root g ^ p = 1)
    (hprim : IsPrimitiveRoot (AdjoinRoot.root g) p) {a b : ZMod p}
    (hab : ∀ u ∈ galSigns p (Nat.card K), a ≠ u * b) (h0 : a ≠ 0 ∨ b ≠ 0) {f : D →ₗ[K] D}
    (hf : ∀ x, f ((c ^ b.val) x) = (c ^ a.val) (f x)) : f = 0 := by
  rcases hbt with ⟨-, e, he⟩ | ⟨-, e, he⟩
  · set f' := e.toLinearMap ∘ₗ f ∘ₗ e.symm.toLinearMap with hf'
    have hsymm : ∀ (m : ℕ) (y : AdjoinRoot g),
        e.symm (AdjoinRoot.root g ^ m * y) = (c ^ m) (e.symm y) := fun m y => by
      apply e.injective
      rw [LinearEquiv.apply_symm_apply, sd_e_pow he, LinearEquiv.apply_symm_apply]
    have h0' : f' = 0 := sd_sylvester hζ hprim hab h0 fun y => by
      simp only [hf', LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [hsymm, hf, sd_e_pow he]
    refine LinearMap.ext fun x => ?_
    have h1 := LinearMap.congr_fun h0' (e x)
    simp only [hf', LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearMap.zero_apply, LinearEquiv.map_eq_zero_iff] at h1
    rw [h1, LinearMap.zero_apply]
  · set m1 : ZMod p := ((-1 : (ZMod p)ˣ) : ZMod p) with hm1
    have hm1m1 : m1 * m1 = 1 := by
      rw [hm1, ← Units.val_mul, neg_one_mul, neg_neg, Units.val_one]
    have hm1ne : m1 ≠ 0 := Units.ne_zero _
    have hneg : ∀ u ∈ galSigns p (Nat.card K), u * (-1) ∈ galSigns p (Nat.card K) :=
      fun u hu => (galSigns p (Nat.card K)).mul_mem hu (neg_one_mem_galSigns _ _)
    set f' := e.toLinearMap ∘ₗ f ∘ₗ e.symm.toLinearMap with hf'
    have hsymm : ∀ (m : ℕ) (x y : AdjoinRoot g), e.symm (AdjoinRoot.root g ^ m * x,
        (AdjoinRoot.root g ^ (p - 1)) ^ m * y) = (c ^ m) (e.symm (x, y)) := fun m x y => by
      apply e.injective
      rw [LinearEquiv.apply_symm_apply, pr_e_pow he, LinearEquiv.apply_symm_apply]
    have hf'eq : ∀ x y,
        f' (AdjoinRoot.root g ^ b.val * x, (AdjoinRoot.root g ^ (p - 1)) ^ b.val * y) =
          (AdjoinRoot.root g ^ a.val * (f' (x, y)).1,
          (AdjoinRoot.root g ^ (p - 1)) ^ a.val * (f' (x, y)).2) := fun x y => by
      simp only [hf', LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [hsymm, hf, pr_e_pow he]
    have h₁₁ : (LinearMap.fst K _ _ ∘ₗ f' ∘ₗ LinearMap.inl K _ (AdjoinRoot g)) = 0 :=
      sd_sylvester hζ hprim hab h0 fun x => by
        have := congrArg Prod.fst (hf'eq x 0)
        rw [mul_zero] at this
        exact this
    have h₁₂ : (LinearMap.fst K _ _ ∘ₗ f' ∘ₗ LinearMap.inr K (AdjoinRoot g) _) = 0 :=
      sd_sylvester (b := m1 * b) hζ hprim (fun u hu h => hab (u * (-1)) (hneg u hu) (by
          rw [Units.val_mul, hm1.symm, mul_assoc]
          exact h))
        (h0.imp id fun hb => mul_ne_zero hm1ne hb) fun y => by
        have := congrArg Prod.fst (hf'eq 0 y)
        rw [mul_zero, root_pred_pow_eq hζ] at this
        exact this
    have h₂₁ : (LinearMap.snd K _ _ ∘ₗ f' ∘ₗ LinearMap.inl K _ (AdjoinRoot g)) = 0 :=
      sd_sylvester (a := m1 * a) hζ hprim (fun u hu h => hab (u * (-1)) (hneg u hu) (by
          rw [Units.val_mul, hm1.symm]
          linear_combination m1 * h - a * hm1m1))
        (h0.imp (fun ha => mul_ne_zero hm1ne ha) id) fun x => by
        have := congrArg Prod.snd (hf'eq x 0)
        rw [mul_zero, root_pred_pow_eq hζ] at this
        exact this
    have h₂₂ : (LinearMap.snd K _ _ ∘ₗ f' ∘ₗ LinearMap.inr K (AdjoinRoot g) _) = 0 :=
      sd_sylvester (a := m1 * a) (b := m1 * b) hζ hprim (fun u hu h => hab u hu (by
          linear_combination m1 * h + ((u : ZMod p) * b - a) * hm1m1))
        (h0.imp (fun ha => mul_ne_zero hm1ne ha) fun hb => mul_ne_zero hm1ne hb) fun y => by
        have := congrArg Prod.snd (hf'eq 0 y)
        rw [mul_zero, root_pred_pow_eq hζ, root_pred_pow_eq hζ] at this
        exact this
    have hzero : f' = 0 := by
      refine LinearMap.ext fun v => ?_
      obtain ⟨x, y⟩ := v
      have hsplit : f' (x, y) = f' (x, 0) + f' (0, y) := by
        rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
      have e₁₁ := LinearMap.congr_fun h₁₁ x
      have e₁₂ := LinearMap.congr_fun h₁₂ y
      have e₂₁ := LinearMap.congr_fun h₂₁ x
      have e₂₂ := LinearMap.congr_fun h₂₂ y
      simp only [LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply,
        LinearMap.inl_apply, LinearMap.inr_apply, LinearMap.zero_apply] at e₁₁ e₁₂ e₂₁ e₂₂
      rw [hsplit, LinearMap.zero_apply]
      exact Prod.ext (by rw [Prod.fst_add, e₁₁, e₁₂, add_zero]; rfl)
        (by rw [Prod.snd_add, e₂₁, e₂₂, add_zero]; rfl)
    refine LinearMap.ext fun x => ?_
    have h1 := LinearMap.congr_fun hzero (e x)
    simp only [hf', LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearMap.zero_apply, LinearEquiv.map_eq_zero_iff] at h1
    rw [h1, LinearMap.zero_apply]

omit [Finite K] in
theorem block_pow_fix (hbt : NsBlockType g p D c) (hζ : AdjoinRoot.root g ^ p = 1)
    (hprim : IsPrimitiveRoot (AdjoinRoot.root g) p) {a : ZMod p} (ha : a ≠ 0) {x : D}
    (hx : (c ^ a.val) x = x) : x = 0 := by
  rcases hbt with ⟨-, e, he⟩ | ⟨-, e, he⟩
  · have h1 : AdjoinRoot.root g ^ a.val * e x = e x := by rw [← sd_e_pow he, hx]
    have h2 : (AdjoinRoot.root g ^ a.val - 1) * e x = 0 := by rw [sub_mul, one_mul, h1, sub_self]
    have h3 := (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr (root_pow_val_ne_one hprim ha))
    exact e.map_eq_zero_iff.mp h3
  · have h1 := pr_e_pow he a.val x
    rw [hx, root_pred_pow_eq hζ] at h1
    have hm : (((-1 : (ZMod p)ˣ) : ZMod p)) * a ≠ 0 := mul_ne_zero (Units.ne_zero _) ha
    have hz : ∀ (μ : AdjoinRoot g), μ ≠ 1 → ∀ y : AdjoinRoot g, y = μ * y → y = 0 := by
      intro μ hμ y hy
      have h2 : (μ - 1) * y = 0 := by rw [sub_mul, one_mul, ← hy, sub_self]
      exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hμ)
    have e1 := hz _ (root_pow_val_ne_one hprim ha) _ (congrArg Prod.fst h1)
    have e2 := hz _ (root_pow_val_ne_one hprim hm) _ (congrArg Prod.snd h1)
    exact e.map_eq_zero_iff.mp (Prod.ext e1 e2)

end Block

end CoordSpNs

end CFSG.StandardType
