module

public import CFSG.Quasithin.Vol2.KGFactL34Uni
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.H13.KGL34A

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {k : Type} [Field k] [Finite k]

@[expose] noncomputable def slTwo [CharP k 2] :
    SpecialLinearGroup (Fin 3) (ZMod 2) →* SpecialLinearGroup (Fin 3) k :=
  SpecialLinearGroup.map (ZMod.castHom (dvd_refl 2) k)

omit [Finite k] in
theorem slTwo_injective [CharP k 2] : Function.Injective (slTwo (k := k)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro a b hab
  apply Subtype.ext
  ext i j
  have := congrFun (congrFun (congrArg (fun g : SpecialLinearGroup (Fin 3) k =>
    (g : Matrix (Fin 3) (Fin 3) k)) hab) i) j
  exact (ZMod.castHom (dvd_refl 2) k).injective this

omit [Finite k] in
theorem mem_range_slTwo [CharP k 2] {y : SpecialLinearGroup (Fin 3) k}
    (h : ∀ i j, (y : Matrix (Fin 3) (Fin 3) k) i j = 0 ∨ (y : Matrix (Fin 3) (Fin 3) k) i j = 1) :
    y ∈ (slTwo (k := k)).range := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f := ZMod.castHom (dvd_refl 2) k
  set Y : Matrix (Fin 3) (Fin 3) k := (y : Matrix (Fin 3) (Fin 3) k) with hY
  let M₀ : Matrix (Fin 3) (Fin 3) (ZMod 2) := Matrix.of fun i j => if Y i j = 0 then 0 else 1
  have hmap : M₀.map f = Y := by
    ext i j
    show f (if Y i j = 0 then 0 else 1) = Y i j
    rcases h i j with h0 | h1
    · rw [ite_eq_left h0, map_zero, h0]
    · rw [ite_eq_right (show ¬ Y i j = 0 by rw [h1]; exact one_ne_zero), map_one, h1]
  have hdet : M₀.det = 1 := by
    apply f.injective
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hmap, map_one]
    exact y.2
  exact ⟨⟨M₀, hdet⟩, Subtype.ext hmap⟩

omit [Finite k] in
theorem card_le_four_of_entries [CharP k 2] {F : Subgroup (SpecialLinearGroup (Fin 3) k)}
    (hc : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x) (hs : ∀ x ∈ F, x * x = 1)
    (h01 : ∀ y ∈ F, ∀ i j,
      (y : Matrix (Fin 3) (Fin 3) k) i j = 0 ∨ (y : Matrix (Fin 3) (Fin 3) k) i j = 1) :
    Nat.card F ≤ 4 := by
  set F₀ := F.comap (slTwo (k := k)) with hF₀
  have hrange : F ≤ (slTwo (k := k)).range := fun y hy => mem_range_slTwo (h01 y hy)
  have hcard : Nat.card F₀ = Nat.card F := by
    conv_rhs => rw [← Subgroup.map_comap_eq_self hrange]
    rw [Subgroup.card_map_of_injective slTwo_injective]
  have hc₀ : ∀ x ∈ F₀, ∀ y ∈ F₀, x * y = y * x := by
    intro x hx y hy
    apply slTwo_injective (k := k)
    rw [map_mul, map_mul]
    exact hc _ hx _ hy
  have hs₀ : ∀ x ∈ F₀, x * x = 1 := by
    intro x hx
    apply slTwo_injective (k := k)
    rw [map_mul, map_one]
    exact hs _ hx
  have h := card_le_of_elemAb (K := ZMod 2) hc₀ hs₀
  rw [Nat.card_zmod] at h
  rw [← hcard]
  exact h

omit [Finite k] in
theorem eq_zero_or_one_of_sigma {σ : k ≃+* k} (hσ : ∀ a, σ a = a ^ 2) {a : k} (h : σ a = a) :
    a = 0 ∨ a = 1 := by
  rw [hσ] at h
  have h2 : a * (a - 1) = 0 := by linear_combination h
  rcases mul_eq_zero.1 h2 with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.1 h1)

omit [Finite k] in
theorem transpose_inv_mul_self {y : SpecialLinearGroup (Fin 3) k} (hy : y * y = 1) :
    (y⁻¹).transpose * (y⁻¹).transpose = 1 := by
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  rw [hyi]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_transpose,
    ← Matrix.transpose_mul, ← Matrix.SpecialLinearGroup.coe_mul, hy,
    Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one]

theorem card_le_four_of_field (hk : Nat.card k = 4) {σ : k ≃+* k} (hσ : ∀ a, σ a = a ^ 2)
    {E : Subgroup (projectiveSL 3 k)} (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hs : ∀ x ∈ E, x * x = 1) (hfix : ∀ x ∈ E, fieldAut 3 k σ x = x) : Nat.card E ≤ 4 := by
  have : CharP k 2 := LinearFieldFour.charP_two_of_card_eq_four hk
  rw [← card_liftSub hk hc hs]
  refine card_le_four_of_entries liftSub_comm (fun _ hx => hx.2) fun y hy i j => ?_
  have hyE := (mem_liftSub.1 hy).1
  have hy2 := (mem_liftSub.1 hy).2
  have hσy : SpecialLinearGroup.map σ.toRingHom y = y := by
    refine eq_of_proj_eq hk ?_ hy2 ?_
    · rw [← map_mul, hy2, map_one]
    · rw [← fieldAut_proj, hfix _ hyE]
  have := congrFun (congrFun (congrArg (fun g : SpecialLinearGroup (Fin 3) k =>
    (g : Matrix (Fin 3) (Fin 3) k)) hσy) i) j
  simp only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] at this
  exact eq_zero_or_one_of_sigma hσ this

theorem card_ne_sixteen_of_dual (hk : Nat.card k = 4) {E : Subgroup (projectiveSL 3 k)}
    (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hs : ∀ x ∈ E, x * x = 1)
    (hfix : ∀ x ∈ E, dualAut 3 k x = x) : Nat.card E ≠ 16 := by
  have : CharP k 2 := LinearFieldFour.charP_two_of_card_eq_four hk
  rw [← card_liftSub hk hc hs]
  have h := card_ne_of_twisted (RingEquiv.refl k) (F := liftSub hk E hc) liftSub_comm
    (fun _ hx => hx.2) fun y hy => ?_
  · rwa [hk] at h
  · have hyE := (mem_liftSub.1 hy).1
    have hy2 := (mem_liftSub.1 hy).2
    have hδy : (y⁻¹).transpose = y := by
      refine eq_of_proj_eq hk (transpose_inv_mul_self hy2) hy2 ?_
      rw [← dualAut_proj, hfix _ hyE]
    have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
    rw [hyi] at hδy
    have := congrArg (fun g : SpecialLinearGroup (Fin 3) k => (g : Matrix (Fin 3) (Fin 3) k)) hδy
    simp only [Matrix.SpecialLinearGroup.coe_transpose] at this
    rw [RingEquiv.coe_refl, Matrix.map_id]
    exact this

theorem card_ne_sixteen_of_beta (hk : Nat.card k = 4) {σ : k ≃+* k}
    {E : Subgroup (projectiveSL 3 k)} (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hs : ∀ x ∈ E, x * x = 1) (hfix : ∀ x ∈ E, (fieldAut 3 k σ * dualAut 3 k) x = x) :
    Nat.card E ≠ 16 := by
  have : CharP k 2 := LinearFieldFour.charP_two_of_card_eq_four hk
  rw [← card_liftSub hk hc hs]
  have h := card_ne_of_twisted σ (F := liftSub hk E hc) liftSub_comm (fun _ hx => hx.2)
    fun y hy => ?_
  · rwa [hk] at h
  · have hyE := (mem_liftSub.1 hy).1
    have hy2 := (mem_liftSub.1 hy).2
    have hβy : SpecialLinearGroup.map σ.toRingHom (y⁻¹).transpose = y := by
      refine eq_of_proj_eq hk ?_ hy2 ?_
      · rw [← map_mul, transpose_inv_mul_self hy2, map_one]
      · rw [← fieldAut_proj, ← dualAut_proj, ← MulAut.mul_apply, hfix _ hyE]
    have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
    rw [hyi] at hβy
    have := congrArg (fun g : SpecialLinearGroup (Fin 3) k => (g : Matrix (Fin 3) (Fin 3) k)) hβy
    simp only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.SpecialLinearGroup.coe_transpose, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom] at this
    rw [← Matrix.transpose_map]
    exact this

end CFSG.Quasithin.H13.KGL34A
