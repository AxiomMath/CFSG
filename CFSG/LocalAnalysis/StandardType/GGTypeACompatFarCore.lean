module

public import CFSG.LocalAnalysis.StandardType.GGTypeAEndInputs

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal.SpecialLinear Matrix

section DiagConj

variable {m : ℕ} {F : Type} [Field F]

theorem diagonal_inv_mul_diagonal (t : Fin m → Fˣ) :
    diagonal (fun i => (((t i)⁻¹ : Fˣ) : F)) * diagonal (fun i => (t i : F)) = 1 := by
  rw [diagonal_mul_diagonal]
  simp

@[expose] noncomputable def ggDiagUnit (t : Fin m → Fˣ) : GL (Fin m) F :=
  ⟨diagonal (fun i => (t i : F)), diagonal (fun i => (((t i)⁻¹ : Fˣ) : F)),
    by rw [diagonal_mul_diagonal]; simp, diagonal_inv_mul_diagonal t⟩

@[expose] noncomputable def ggDiagConj (t : Fin m → Fˣ) :
    SpecialLinearGroup (Fin m) F →* SpecialLinearGroup (Fin m) F :=
  (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation m F
    (ggDiagUnit t)).toMonoidHom

theorem coe_ggDiagConj (t : Fin m → Fˣ) (s : SpecialLinearGroup (Fin m) F) :
    ((ggDiagConj t s : SpecialLinearGroup (Fin m) F) : Matrix (Fin m) (Fin m) F) =
      diagonal (fun i => (t i : F)) * (s : Matrix (Fin m) (Fin m) F) *
        diagonal (fun i => (((t i)⁻¹ : Fˣ) : F)) :=
  CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix m F _ s

theorem ggDiagConj_apply (t : Fin m → Fˣ) (s : SpecialLinearGroup (Fin m) F) (i j : Fin m) :
    (ggDiagConj t s : Matrix (Fin m) (Fin m) F) i j =
      (t i : F) * (s : Matrix (Fin m) (Fin m) F) i j * (((t j)⁻¹ : Fˣ) : F) := by
  rw [coe_ggDiagConj, mul_diagonal, diagonal_mul]

theorem ggDiagConj_transvection (t : Fin m → Fˣ) {i j : Fin m} (hij : i ≠ j) (c : F) :
    ggDiagConj t (SpecialLinearGroup.transvection hij c) =
      SpecialLinearGroup.transvection hij ((t i : F) * c * (((t j)⁻¹ : Fˣ) : F)) := by
  apply Subtype.ext
  ext a b
  rw [ggDiagConj_apply]
  simp only [SpecialLinearGroup.transvection_coe, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]
  by_cases hab : a = b
  · subst hab
    have hai : ¬ (i = a ∧ j = a) := fun h => hij (h.1.trans h.2.symm)
    simp [hai]
  · by_cases h : i = a ∧ j = b
    · obtain ⟨rfl, rfl⟩ := h
      simp [hab]
    · simp [hab, h]

theorem ggDiagConj_eq_self_of_const {t : Fin m → Fˣ} (ht : ∀ i j, t i = t j)
    (s : SpecialLinearGroup (Fin m) F) : ggDiagConj t s = s := by
  apply Subtype.ext
  ext a b
  rw [ggDiagConj_apply, ht a b, mul_comm (((t b) : Fˣ) : F), mul_assoc]
  simp

theorem ggDiagConj_ggDiagConj (t t' : Fin m → Fˣ) (s : SpecialLinearGroup (Fin m) F) :
    ggDiagConj t (ggDiagConj t' s) = ggDiagConj (t * t') s := by
  apply Subtype.ext
  ext a b
  rw [ggDiagConj_apply, ggDiagConj_apply, ggDiagConj_apply]
  simp only [Pi.mul_apply, Units.val_mul, _root_.mul_inv_rev, Units.val_inv_eq_inv_val]
  have := (t a).ne_zero
  have := (t' a).ne_zero
  ring

theorem eq_zero_of_transvection_mem_center {i j : Fin m} (hij : i ≠ j) {c : F}
    (h : SpecialLinearGroup.transvection hij c ∈
      Subgroup.center (SpecialLinearGroup (Fin m) F)) : c = 0 := by
  have hc := Subgroup.mem_center_iff.mp h (SpecialLinearGroup.transvection hij.symm 1)
  obtain ⟨h1, -⟩ := apply_eq_zero_of_commute_transvection_one hij.symm
    (g := SpecialLinearGroup.transvection hij c) hc.symm
  have h3 := h1 i hij
  simpa [SpecialLinearGroup.transvection_coe, Matrix.one_apply, hij] using h3

theorem ratio_eq_of_ggDiagConj {X : Type*} [Group X] {φ : SpecialLinearGroup (Fin m) F →* X}
    (hker : φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin m) F)) {t t' : Fin m → Fˣ}
    (h : ∀ s, φ (ggDiagConj t s) = φ (ggDiagConj t' s)) (k l : Fin m) :
    t k * (t' k)⁻¹ = t l * (t' l)⁻¹ := by
  by_cases hkl : k = l
  · rw [hkl]
  have h1 := h (SpecialLinearGroup.transvection hkl 1)
  rw [ggDiagConj_transvection, ggDiagConj_transvection] at h1
  set c := (t k : F) * 1 * (((t l)⁻¹ : Fˣ) : F)
  set c' := (t' k : F) * 1 * (((t' l)⁻¹ : Fˣ) : F)
  have h2 : SpecialLinearGroup.transvection hkl (c' - c) ∈ φ.ker := by
    rw [MonoidHom.mem_ker]
    have e : SpecialLinearGroup.transvection hkl (c' - c) =
        (SpecialLinearGroup.transvection hkl c)⁻¹ * SpecialLinearGroup.transvection hkl c' := by
      rw [eq_inv_mul_iff_mul_eq, ← Matrix.SpecialLinearGroup.transvection_add, add_sub_cancel]
    rw [e, map_mul, map_inv, h1, inv_mul_cancel]
  have h3 := eq_zero_of_transvection_mem_center hkl (hker h2)
  rw [sub_eq_zero] at h3
  apply Units.ext
  simp only [Units.val_mul, Units.val_inv_eq_inv_val] at h3 ⊢
  simp only [c, c', mul_one, Units.val_inv_eq_inv_val] at h3
  have hk := (t' k).ne_zero
  have hl := (t l).ne_zero
  have hl' := (t' l).ne_zero
  field_simp
  field_simp at h3
  linear_combination -h3

theorem eq_of_sq_eq_sq_of_odd {M : Type*} [CommGroup M] [Finite M] (hM : Odd (Nat.card M))
    {x y : M} (h : x ^ 2 = y ^ 2) : x = y := by
  have h1 : (x * y⁻¹) ^ 2 = 1 := by rw [mul_pow, h, inv_pow, mul_inv_cancel]
  have h2 : orderOf (x * y⁻¹) ∣ Nat.gcd 2 (Nat.card M) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_natCard _)
  have hcop : Nat.gcd 2 (Nat.card M) = 1 := (Odd.coprime_two_right hM).symm
  rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at h2
  exact mul_inv_eq_one.mp h2

end DiagConj

section Blocks

variable {F : Type} [Field F]

theorem weylRep_mul_ggDiagConj (h2 : (2 : F) = 0) {m : ℕ} (k : Fin m) (t : Fin (m + 1) → Fˣ)
    (s : SpecialLinearGroup (Fin (m + 1)) F) :
    weylRep m F k * ggDiagConj t s * weylRep m F k =
      ggDiagConj (t ∘ Equiv.swap k.castSucc k.succ) (weylRep m F k * s * weylRep m F k) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_ggDiagConj,
    coe_ggDiagConj, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    coe_weylRep_of_two m h2 k]
  set π := Equiv.swap k.castSucc k.succ
  have hP : ∀ d : Fin (m + 1) → F, signedPerm π 1 * diagonal d =
      diagonal (d ∘ π) * signedPerm π 1 := fun d => by
    rw [signedPerm_mul_diagonal]
    rfl
  have hP' : ∀ d : Fin (m + 1) → F, diagonal d * signedPerm π 1 =
      signedPerm π 1 * diagonal (d ∘ π) := fun d => by
    rw [hP (d ∘ π)]
    congr 2
    funext r
    simp [π, Equiv.swap_apply_self]
  have e1 := hP (fun i => (t i : F))
  have e2 := hP' (fun i => (((t i)⁻¹ : Fˣ) : F))
  calc signedPerm π 1 * (diagonal (fun i => (t i : F)) * (s : Matrix _ _ F) *
        diagonal (fun i => (((t i)⁻¹ : Fˣ) : F))) * signedPerm π 1
      = (signedPerm π 1 * diagonal (fun i => (t i : F))) * (s : Matrix _ _ F) *
          (diagonal (fun i => (((t i)⁻¹ : Fˣ) : F)) * signedPerm π 1) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [e1, e2]
        simp only [Matrix.mul_assoc]
        rfl

theorem ggDiagConj_slLowerBlockHom {n : ℕ} (t : Fin (n + 1) → Fˣ)
    (g : SpecialLinearGroup (Fin n) F) :
    ggDiagConj t (slLowerBlockHom n F g) = slLowerBlockHom n F (ggDiagConj (t ∘ Fin.succ) g) := by
  have e : (ggDiagConj t).comp (slLowerBlockHom n F) =
      (slLowerBlockHom n F).comp (ggDiagConj (t ∘ Fin.succ)) := by
    refine MonoidHom.eq_of_eqOn_dense
      (SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field (ι := Fin n) (K := F))
      ?_
    rintro _ ⟨⟨a, b, hab, c⟩, rfl⟩
    simp only [TransvectionStruct.toSpecialLinearGroup_mk, MonoidHom.comp_apply,
      slLowerBlockHom_transvection, ggDiagConj_transvection, Function.comp_apply]
  exact DFunLike.congr_fun e g

theorem ggDiagConj_slUpperBlockHom {n : ℕ} (t : Fin (n + 1) → Fˣ)
    (g : SpecialLinearGroup (Fin n) F) :
    ggDiagConj t (slUpperBlockHom n F g) =
      slUpperBlockHom n F (ggDiagConj (t ∘ Fin.castSucc) g) := by
  have e : (ggDiagConj t).comp (slUpperBlockHom n F) =
      (slUpperBlockHom n F).comp (ggDiagConj (t ∘ Fin.castSucc)) := by
    refine MonoidHom.eq_of_eqOn_dense
      (SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field (ι := Fin n) (K := F))
      ?_
    rintro _ ⟨⟨a, b, hab, c⟩, rfl⟩
    simp only [TransvectionStruct.toSpecialLinearGroup_mk, MonoidHom.comp_apply,
      slUpperBlockHom_transvection, ggDiagConj_transvection, Function.comp_apply]
  exact DFunLike.congr_fun e g

end Blocks


section Core

variable {X : Type*} [Group X] {n : ℕ} {F : Type} [Field F]

theorem ggDiagConj_swap_eq_inv (h2 : (2 : F) = 0) {m : ℕ}
    {φ : SpecialLinearGroup (Fin (m + 1)) F →* X} (k : Fin m) {u : X}
    (hau : φ (weylRep m F k) * u * φ (weylRep m F k) = u⁻¹) {h : Fin (m + 1) → Fˣ}
    (hu : ∀ s, u * φ s * u⁻¹ = φ (ggDiagConj h s)) (s : SpecialLinearGroup (Fin (m + 1)) F) :
    φ (ggDiagConj (h ∘ Equiv.swap k.castSucc k.succ) s) = φ (ggDiagConj h⁻¹ s) := by
  set a := φ (weylRep m F k) with ha_def
  have ha2 : a * a = 1 := by rw [ha_def, ← map_mul, weylRep_mul_self m h2, map_one]
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hu_eq : a * u⁻¹ * a = u := by
    calc a * u⁻¹ * a = (a⁻¹ * u * a⁻¹)⁻¹ := by group
      _ = (a * u * a)⁻¹ := by rw [ha']
      _ = u := by rw [hau, inv_inv]
  have hinv : u⁻¹ * φ s * u = φ (ggDiagConj h⁻¹ s) := by
    have e := hu (ggDiagConj h⁻¹ s)
    rw [ggDiagConj_ggDiagConj, mul_inv_cancel,
      ggDiagConj_eq_self_of_const (t := (1 : Fin (m + 1) → Fˣ)) (fun _ _ => rfl)] at e
    rw [← e]
    group
  have hn2 : weylRep m F k * weylRep m F k = 1 := weylRep_mul_self m h2 k
  have hconj : ∀ x, a * φ x * a = φ (weylRep m F k * x * weylRep m F k) := fun x => by
    rw [ha_def, map_mul, map_mul]
  calc φ (ggDiagConj (h ∘ Equiv.swap k.castSucc k.succ) s)
      = φ (weylRep m F k * ggDiagConj h (weylRep m F k * s * weylRep m F k) * weylRep m F k) := by
        rw [weylRep_mul_ggDiagConj h2]
        congr 2
        calc s = (weylRep m F k * weylRep m F k) * s * (weylRep m F k * weylRep m F k) := by
              rw [hn2, one_mul, mul_one]
          _ = _ := by group
    _ = a * (u * φ (weylRep m F k * s * weylRep m F k) * u⁻¹) * a := by
        rw [hu, hconj]
    _ = (a * u * a) * φ s * (a * u⁻¹ * a) := by
        rw [← hconj]
        group
    _ = u⁻¹ * φ s * u := by rw [hau, hu_eq]
    _ = φ (ggDiagConj h⁻¹ s) := hinv

theorem commute_of_ggDiagConj [Finite F] (h2 : (2 : F) = 0) (hF : Odd (Nat.card Fˣ))
    (hn : 3 ≤ n) {φ₁ φ₂ : SpecialLinearGroup (Fin (n + 1)) F →* X}
    (hker₁ : φ₁.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) F))
    (hker₂ : φ₂.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) F))
    (hc : φ₁.comp (slLowerBlockHom n F) = φ₂.comp (slUpperBlockHom n F))
    {i j : Fin n} (hi : i.val = 0) (hj : j.val + 1 = n) {u : X}
    (hu : u = φ₁ (weylRep n F i) * φ₂ (weylRep n F j) * φ₁ (weylRep n F i) *
      φ₂ (weylRep n F j))
    {h h' : Fin (n + 1) → Fˣ} (hu₁ : ∀ s, u * φ₁ s * u⁻¹ = φ₁ (ggDiagConj h s))
    (hu₂ : ∀ s, u * φ₂ s * u⁻¹ = φ₂ (ggDiagConj h' s))
    (hodd : (∀ s, u * φ₁ s = φ₁ s * u) → u * u = 1 → u = 1) :
    Commute (φ₂ (weylRep n F j)) (φ₁ (weylRep n F i)) := by
  set a := φ₁ (weylRep n F i) with ha_def
  set b := φ₂ (weylRep n F j) with hb_def
  have ha2 : a * a = 1 := by rw [ha_def, ← map_mul, weylRep_mul_self n h2, map_one]
  have hb2 : b * b = 1 := by rw [hb_def, ← map_mul, weylRep_mul_self n h2, map_one]
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hau : a * u * a = u⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, hu]
    calc a * (a * b * a * b) * a * (a * b * a * b)
        = (a * a) * b * a * b * (a * a) * b * a * b := by group
      _ = b * a * (b * b) * a * b := by rw [ha2]; group
      _ = b * (a * a) * b := by rw [hb2]; group
      _ = 1 := by rw [ha2, mul_one, hb2]
  have hbu : b * u * b = u⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, hu]
    calc b * (a * b * a * b) * b * (a * b * a * b)
        = b * a * b * a * (b * b) * a * b * a * b := by group
      _ = b * a * b * (a * a) * b * a * b := by rw [hb2]; group
      _ = b * a * (b * b) * a * b := by rw [ha2]; group
      _ = b * (a * a) * b := by rw [hb2]; group
      _ = 1 := by rw [ha2, mul_one, hb2]
  have hA := ratio_eq_of_ggDiagConj hker₁ (ggDiagConj_swap_eq_inv h2 i hau hu₁)
  have hB := ratio_eq_of_ggDiagConj hker₂ (ggDiagConj_swap_eq_inv h2 j hbu hu₂)
  have hθ : (φ₁.comp (slLowerBlockHom n F)).ker ≤
      Subgroup.center (SpecialLinearGroup (Fin n) F) := by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr (injective_comp_slLowerBlockHom hker₁)]
    exact bot_le
  have hJ : ∀ g : SpecialLinearGroup (Fin n) F,
      (φ₁.comp (slLowerBlockHom n F)) (ggDiagConj (h ∘ Fin.succ) g) =
        (φ₁.comp (slLowerBlockHom n F)) (ggDiagConj (h' ∘ Fin.castSucc) g) := by
    intro g
    have e₁ := hu₁ (slLowerBlockHom n F g)
    have e₂ := hu₂ (slUpperBlockHom n F g)
    rw [ggDiagConj_slLowerBlockHom] at e₁
    rw [ggDiagConj_slUpperBlockHom] at e₂
    have hcx : ∀ x, φ₁ (slLowerBlockHom n F x) = φ₂ (slUpperBlockHom n F x) := fun x =>
      DFunLike.congr_fun hc x
    simp only [MonoidHom.comp_apply]
    rw [← e₁, hcx, e₂, ← hcx]
  have hC := ratio_eq_of_ggDiagConj hθ hJ
  have h0 : 0 < n := by omega
  set e0 : Fin (n + 1) := ⟨0, by omega⟩
  set e1 : Fin (n + 1) := ⟨1, by omega⟩
  set e2 : Fin (n + 1) := ⟨2, by omega⟩
  have hπ0 : Equiv.swap i.castSucc i.succ e0 = e1 := by
    rw [show e0 = i.castSucc from Fin.ext (by simp [e0, hi]),
      show e1 = i.succ from Fin.ext (by simp [e1, hi]), Equiv.swap_apply_left]
  have hπk : ∀ k : Fin (n + 1), 2 ≤ k.val → Equiv.swap i.castSucc i.succ k = k := by
    intro k hk
    exact Equiv.swap_apply_of_ne_of_ne (Fin.ne_of_val_ne (by simp; omega))
      (Fin.ne_of_val_ne (by simp; omega))
  have hπ'k : ∀ k : Fin (n + 1), k.val + 2 ≤ n → Equiv.swap j.castSucc j.succ k = k := by
    intro k hk
    exact Equiv.swap_apply_of_ne_of_ne (Fin.ne_of_val_ne (by simp; omega))
      (Fin.ne_of_val_ne (by simp; omega))
  have hsq : ∀ x y : Fˣ, x * x = y * y → x = y := fun x y hxy =>
    eq_of_sq_eq_sq_of_odd hF (by rw [pow_two, pow_two, hxy])
  have hB2 : ∀ k : Fin (n + 1), 2 ≤ k.val → h k = h e2 := by
    intro k hk
    have e := hA k e2
    simp only [Function.comp_apply, Pi.inv_apply, inv_inv, hπk k hk, hπk e2 le_rfl] at e
    exact hsq _ _ e
  have hA0 : h e2 * h e2 = h e1 * h e0 := by
    have e := hA e2 e0
    simp only [Function.comp_apply, Pi.inv_apply, inv_inv, hπk e2 le_rfl, hπ0] at e
    exact e
  have hC01 : h' e0 = h' e1 := by
    have e := hB e0 e1
    simp only [Function.comp_apply, Pi.inv_apply, inv_inv, hπ'k e0 (by simp [e0]; omega),
      hπ'k e1 (by simp [e1]; omega)] at e
    exact hsq _ _ e
  have hD : h e1 = h e2 := by
    have e := hC ⟨0, h0⟩ ⟨1, by omega⟩
    simp only [Function.comp_apply] at e
    rw [show (Fin.succ ⟨0, h0⟩ : Fin (n + 1)) = e1 from rfl,
      show (Fin.succ ⟨1, by omega⟩ : Fin (n + 1)) = e2 from rfl,
      show (Fin.castSucc ⟨0, h0⟩ : Fin (n + 1)) = e0 from rfl,
      show (Fin.castSucc ⟨1, by omega⟩ : Fin (n + 1)) = e1 from rfl, hC01] at e
    exact mul_right_cancel e
  have hE : h e0 = h e2 := by
    rw [hD] at hA0
    exact (mul_left_cancel hA0).symm
  have hconst : ∀ k l : Fin (n + 1), h k = h l := by
    have hall : ∀ k : Fin (n + 1), h k = h e2 := by
      intro k
      by_cases hk0 : k.val = 0
      · rw [show k = e0 from Fin.ext (by simp [e0, hk0]), hE]
      by_cases hk1 : k.val = 1
      · rw [show k = e1 from Fin.ext (by simp [e1, hk1]), hD]
      exact hB2 k (by omega)
    intro k l
    rw [hall k, hall l]
  have hcent : ∀ s, u * φ₁ s = φ₁ s * u := by
    intro s
    have e := hu₁ s
    rw [ggDiagConj_eq_self_of_const hconst] at e
    calc u * φ₁ s = u * φ₁ s * u⁻¹ * u := by group
      _ = φ₁ s * u := by rw [e]
  have hua : u * a = a * u := hcent (weylRep n F i)
  have huu : u * u = 1 := by
    have e : u⁻¹ = u := by
      rw [← hau, ← hua, mul_assoc, ha2, mul_one]
    calc u * u = u * u⁻¹ := by rw [e]
      _ = 1 := mul_inv_cancel u
  have hu1 := hodd hcent huu
  have hab : (a * b) * (a * b) = 1 := by
    rw [← hu1, hu]
    group
  have hab' : a * b = b * a := by
    calc a * b = (a * b)⁻¹ := eq_inv_of_mul_eq_one_left hab
      _ = b * a := by rw [_root_.mul_inv_rev, ha', hb']
  exact hab'.symm

end Core

end CFSG.StandardType
