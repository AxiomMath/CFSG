module

public import CFSG.CharacterTheory.SteinbergBYFieldFour
public import CFSG.Quasithin.Vol2.Ch12Sec2GlueHatA6

public section

namespace CFSG.Quasithin.HatA6

open CFSG.CharacterTheory.SteinbergBY
open scoped Matrix

theorem ff_add_re (x y : FieldFour) : (x + y).re = xor x.re y.re := rfl
theorem ff_add_im (x y : FieldFour) : (x + y).im = xor x.im y.im := rfl
theorem ff_mul_re (x y : FieldFour) : (x * y).re = xor (x.re && y.re) (x.im && y.im) := rfl
theorem ff_mul_im (x y : FieldFour) :
    (x * y).im = xor (xor (x.re && y.im) (x.im && y.re)) (x.im && y.im) := rfl
theorem ff_one_re : (1 : FieldFour).re = true := rfl
theorem ff_one_im : (1 : FieldFour).im = false := rfl
theorem ff_zero_re : (0 : FieldFour).re = false := rfl
theorem ff_zero_im : (0 : FieldFour).im = false := rfl
theorem ff_ω_re : FieldFour.ω.re = false := rfl
theorem ff_ω_im : FieldFour.ω.im = true := rfl

variable {V : Type} [CommGroup V]

@[expose] def fsmul (z : MulAut V) (c : FieldFour) (v : V) : V :=
  (if c.re then v else 1) * (if c.im then z v else 1)

variable (z : MulAut V)

theorem fsmul_mul_right (c : FieldFour) (v w : V) :
    fsmul z c (v * w) = fsmul z c v * fsmul z c w := by
  rcases c with ⟨_ | _, _ | _⟩ <;> simp [fsmul, map_mul, mul_comm, mul_left_comm, mul_assoc]

theorem fsmul_one (v : V) : fsmul z 1 v = v := by
  simp [fsmul, ff_one_re, ff_one_im]

theorem fsmul_zero (v : V) : fsmul z 0 v = 1 := by
  simp [fsmul, ff_zero_re, ff_zero_im]

theorem fsmul_ω (v : V) : fsmul z FieldFour.ω v = z v := by
  simp [fsmul, ff_ω_re, ff_ω_im]

theorem fsmul_one_right (c : FieldFour) : fsmul z c (1 : V) = 1 := by
  rcases c with ⟨_ | _, _ | _⟩ <;> simp [fsmul]

variable {z}

theorem map_fsmul {x : MulAut V} (hx : ∀ v, x (z v) = z (x v)) (c : FieldFour) (v : V) :
    x (fsmul z c v) = fsmul z c (x v) := by
  rcases c with ⟨_ | _, _ | _⟩ <;> simp [fsmul, map_mul, hx]

theorem fsmul_add (hsq : ∀ v : V, v * v = 1) (c d : FieldFour) (v : V) :
    fsmul z (c + d) v = fsmul z c v * fsmul z d v := by
  have h2 : ∀ w u : V, w * (w * u) = u := fun w u => by rw [← mul_assoc, hsq, one_mul]
  rcases c with ⟨_ | _, _ | _⟩ <;> rcases d with ⟨_ | _, _ | _⟩ <;>
    simp [fsmul, ff_add_re, ff_add_im, mul_comm, mul_left_comm, hsq, h2]

theorem fsmul_mul (hsq : ∀ v : V, v * v = 1) (hzz : ∀ v, z (z v) = v * z v)
    (c d : FieldFour) (v : V) : fsmul z (c * d) v = fsmul z c (fsmul z d v) := by
  have h2 : ∀ w u : V, w * (w * u) = u := fun w u => by rw [← mul_assoc, hsq, one_mul]
  rcases c with ⟨_ | _, _ | _⟩ <;> rcases d with ⟨_ | _, _ | _⟩ <;>
    simp [fsmul, ff_mul_re, ff_mul_im, map_mul, hzz, mul_comm, mul_left_comm, hsq, h2]

@[expose] def coordHom (hsq : ∀ v : V, v * v = 1) (z : MulAut V) (v : Fin 3 → V) :
    Multiplicative (Fin 3 → FieldFour) →* V where
  toFun c := fsmul z (Multiplicative.toAdd c 0) (v 0) * fsmul z (Multiplicative.toAdd c 1) (v 1) *
    fsmul z (Multiplicative.toAdd c 2) (v 2)
  map_one' := by simp [fsmul_zero]
  map_mul' c d := by
    simp only [toAdd_mul, Pi.add_apply, fsmul_add hsq]
    simp only [mul_left_comm, mul_assoc]

theorem coordHom_apply (hsq : ∀ v : V, v * v = 1) (z : MulAut V) (v : Fin 3 → V)
    (c : Multiplicative (Fin 3 → FieldFour)) :
    coordHom hsq z v c = fsmul z (Multiplicative.toAdd c 0) (v 0) *
      fsmul z (Multiplicative.toAdd c 1) (v 1) * fsmul z (Multiplicative.toAdd c 2) (v 2) := rfl

theorem coordHom_smul (hsq : ∀ v : V, v * v = 1) (hzz : ∀ v, z (z v) = v * z v)
    (v : Fin 3 → V) (k : FieldFour) (c : Multiplicative (Fin 3 → FieldFour)) :
    coordHom hsq z v (Multiplicative.ofAdd (k • Multiplicative.toAdd c)) =
      fsmul z k (coordHom hsq z v c) := by
  simp only [coordHom_apply, toAdd_ofAdd, Pi.smul_apply, smul_eq_mul, fsmul_mul hsq hzz,
    fsmul_mul_right]

theorem coordHom_ω (hsq : ∀ v : V, v * v = 1) (hzz : ∀ v, z (z v) = v * z v)
    (v : Fin 3 → V) (c : Multiplicative (Fin 3 → FieldFour)) :
    coordHom hsq z v (Multiplicative.ofAdd (FieldFour.ω • Multiplicative.toAdd c)) =
      z (coordHom hsq z v c) := by
  rw [coordHom_smul hsq hzz, fsmul_ω]

section Exists

variable [Finite V]

theorem card_cases_of_inv (hV : Nat.card V = 2 ^ 6) (h3 : z ^ 3 = 1)
    (hfp : ∀ v, z v = v → v = 1) {S : Subgroup V} (hzS : ∀ s ∈ S, z s ∈ S) :
    Nat.card S = 1 ∨ Nat.card S = 4 ∨ Nat.card S = 16 ∨ Nat.card S = 64 := by
  have hd : Nat.card S ∣ 64 := by
    rw [show (64 : ℕ) = 2 ^ 6 from rfl, ← hV]
    exact Subgroup.card_subgroup_dvd_card S
  exact H13.card_cases_of_dvd hd (H13.card_mod_three_of_sub h3 hzS fun s _ hs => hfp s hs)

omit [Finite V] in
theorem coordHom_range_inv (hsq : ∀ v : V, v * v = 1) (hzz : ∀ v, z (z v) = v * z v)
    (v : Fin 3 → V) : ∀ s ∈ (coordHom hsq z v).range, z s ∈ (coordHom hsq z v).range := by
  rintro _ ⟨c, rfl⟩
  exact ⟨_, coordHom_ω hsq hzz v c⟩

theorem card_coords : Nat.card (Multiplicative (Fin 3 → FieldFour)) = 64 := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, FieldFour.natCard_eq, Nat.card_fin]
  norm_num

theorem exists_coord (hsq : ∀ v : V, v * v = 1) (hV : Nat.card V = 2 ^ 6) (h3 : z ^ 3 = 1)
    (hfp : ∀ v, z v = v → v = 1) : ∃ v : Fin 3 → V, Function.Bijective (coordHom hsq z v) := by
  have hsq2 : ∀ v : V, v ^ 2 = 1 := fun v => by rw [pow_two]; exact hsq v
  have hzz : ∀ v, z (z v) = v * z v := fun v =>
    H13.zz_eq_of_fpf hsq2 h3 (W := ⊤) (fun _ _ => trivial) (fun w _ hw => hfp w hw) trivial
  have hcases := fun v => card_cases_of_inv hV h3 hfp (coordHom_range_inv hsq hzz v)
  have hntV : Nontrivial V := by
    rw [← Finite.one_lt_card_iff_nontrivial, hV]; norm_num
  obtain ⟨v₀, hv₀⟩ := exists_ne (1 : V)
  set u₁ : Fin 3 → V := ![v₀, 1, 1] with hu₁
  have hR₁le : Nat.card (coordHom hsq z u₁).range ≤ 4 := by
    have hs : Function.Surjective (fun k : FieldFour => (⟨coordHom hsq z u₁
        (Multiplicative.ofAdd ![k, 0, 0]), ⟨_, rfl⟩⟩ : (coordHom hsq z u₁).range)) := by
      rintro ⟨_, ⟨c, rfl⟩⟩
      refine ⟨Multiplicative.toAdd c 0, Subtype.ext ?_⟩
      simp [coordHom_apply, hu₁, fsmul_one_right]
    calc _ ≤ Nat.card FieldFour := Nat.card_le_card_of_surjective _ hs
      _ = 4 := FieldFour.natCard_eq
  have hR₁v : v₀ ∈ (coordHom hsq z u₁).range :=
    ⟨Multiplicative.ofAdd ![1, 0, 0], by simp [coordHom_apply, hu₁, fsmul_zero, fsmul_one]⟩
  have hR₁ : Nat.card (coordHom hsq z u₁).range = 4 := by
    rcases hcases u₁ with h | h | h | h
    · exfalso
      rw [Subgroup.card_eq_one] at h
      rw [h] at hR₁v
      exact hv₀ hR₁v
    · exact h
    · omega
    · omega
  obtain ⟨v₁, hv₁⟩ : ∃ v₁ : V, v₁ ∉ (coordHom hsq z u₁).range := by
    by_contra hcon
    push Not at hcon
    have htop : (coordHom hsq z u₁).range = ⊤ := eq_top_iff.2 fun x _ => hcon x
    rw [htop, Subgroup.card_top, hV] at hR₁
    norm_num at hR₁
  set u₂ : Fin 3 → V := ![v₀, v₁, 1] with hu₂
  have hR₂le : Nat.card (coordHom hsq z u₂).range ≤ 16 := by
    have hs : Function.Surjective (fun k : FieldFour × FieldFour => (⟨coordHom hsq z u₂
        (Multiplicative.ofAdd ![k.1, k.2, 0]), ⟨_, rfl⟩⟩ : (coordHom hsq z u₂).range)) := by
      rintro ⟨_, ⟨c, rfl⟩⟩
      refine ⟨(Multiplicative.toAdd c 0, Multiplicative.toAdd c 1), Subtype.ext ?_⟩
      simp [coordHom_apply, hu₂, fsmul_one_right]
    calc _ ≤ Nat.card (FieldFour × FieldFour) := Nat.card_le_card_of_surjective _ hs
      _ = 16 := by rw [Nat.card_prod, FieldFour.natCard_eq]
  have hR₁₂ : (coordHom hsq z u₁).range ≤ (coordHom hsq z u₂).range := by
    rintro _ ⟨c, rfl⟩
    exact ⟨Multiplicative.ofAdd ![Multiplicative.toAdd c 0, 0, 0], by
      simp [coordHom_apply, hu₁, hu₂, fsmul_zero, fsmul_one_right]⟩
  have hR₂v : v₁ ∈ (coordHom hsq z u₂).range :=
    ⟨Multiplicative.ofAdd ![0, 1, 0], by simp [coordHom_apply, hu₂, fsmul_zero, fsmul_one]⟩
  have hR₂ : Nat.card (coordHom hsq z u₂).range = 16 := by
    have hlt : (coordHom hsq z u₁).range < (coordHom hsq z u₂).range :=
      lt_of_le_of_ne hR₁₂ fun h => hv₁ (h ▸ hR₂v)
    have hclt := Subgroup.card_lt_of_lt hlt
    rcases hcases u₂ with h | h | h | h <;> omega
  obtain ⟨v₂, hv₂⟩ : ∃ v₂ : V, v₂ ∉ (coordHom hsq z u₂).range := by
    by_contra hcon
    push Not at hcon
    have htop : (coordHom hsq z u₂).range = ⊤ := eq_top_iff.2 fun x _ => hcon x
    rw [htop, Subgroup.card_top, hV] at hR₂
    norm_num at hR₂
  set u₃ : Fin 3 → V := ![v₀, v₁, v₂] with hu₃
  have hR₂₃ : (coordHom hsq z u₂).range ≤ (coordHom hsq z u₃).range := by
    rintro _ ⟨c, rfl⟩
    exact ⟨Multiplicative.ofAdd ![Multiplicative.toAdd c 0, Multiplicative.toAdd c 1, 0], by
      simp [coordHom_apply, hu₂, hu₃, fsmul_zero, fsmul_one_right]⟩
  have hR₃v : v₂ ∈ (coordHom hsq z u₃).range :=
    ⟨Multiplicative.ofAdd ![0, 0, 1], by simp [coordHom_apply, hu₃, fsmul_zero, fsmul_one]⟩
  have hR₃ : (coordHom hsq z u₃).range = ⊤ := by
    have hlt : (coordHom hsq z u₂).range < (coordHom hsq z u₃).range :=
      lt_of_le_of_ne hR₂₃ fun h => hv₂ (h ▸ hR₃v)
    have hclt := Subgroup.card_lt_of_lt hlt
    refine Subgroup.eq_top_of_card_eq _ ?_
    rw [hV]
    rcases hcases u₃ with h | h | h | h <;> omega
  refine ⟨u₃, ?_⟩
  have hsurj : Function.Surjective (coordHom hsq z u₃) := MonoidHom.range_eq_top.1 hR₃
  exact hsurj.bijective_of_nat_card_le (by rw [card_coords, hV]; norm_num)

end Exists

section Linear

variable {hsq : ∀ v : V, v * v = 1} {v : Fin 3 → V} (hb : Function.Bijective (coordHom hsq z v))

@[expose] noncomputable def coordEquiv : Multiplicative (Fin 3 → FieldFour) ≃* V :=
  MulEquiv.ofBijective _ hb

theorem coordEquiv_apply (c : Multiplicative (Fin 3 → FieldFour)) :
    coordEquiv hb c = coordHom hsq z v c := rfl

variable (hzz : ∀ w, z (z w) = w * z w)
include hzz

theorem coordEquiv_smul (k : FieldFour) (c : Fin 3 → FieldFour) :
    coordEquiv hb (Multiplicative.ofAdd (k • c)) =
      fsmul z k (coordEquiv hb (Multiplicative.ofAdd c)) :=
  coordHom_smul hsq hzz v k (Multiplicative.ofAdd c)

theorem coordEquiv_symm_fsmul (k : FieldFour) (w : V) :
    (coordEquiv hb).symm (fsmul z k w) =
      Multiplicative.ofAdd (k • Multiplicative.toAdd ((coordEquiv hb).symm w)) := by
  apply (coordEquiv hb).injective
  rw [MulEquiv.apply_symm_apply, coordEquiv_smul hb hzz, ofAdd_toAdd, MulEquiv.apply_symm_apply]

@[expose] noncomputable def linOf {x : MulAut V} (hx : ∀ w, x (z w) = z (x w)) :
    (Fin 3 → FieldFour) →ₗ[FieldFour] (Fin 3 → FieldFour) where
  toFun c :=
    Multiplicative.toAdd ((coordEquiv hb).symm (x (coordEquiv hb (Multiplicative.ofAdd c))))
  map_add' c d := by
    rw [ofAdd_add, map_mul, map_mul, map_mul, toAdd_mul]
  map_smul' k c := by
    rw [coordEquiv_smul hb hzz, map_fsmul hx, coordEquiv_symm_fsmul hb hzz, toAdd_ofAdd]
    rfl

theorem coordEquiv_linOf {x : MulAut V} (hx : ∀ w, x (z w) = z (x w)) (c : Fin 3 → FieldFour) :
    coordEquiv hb (Multiplicative.ofAdd (linOf hb hzz hx c)) =
      x (coordEquiv hb (Multiplicative.ofAdd c)) := by
  change coordEquiv hb (Multiplicative.ofAdd (Multiplicative.toAdd _)) = _
  rw [ofAdd_toAdd, MulEquiv.apply_symm_apply]

theorem symm_apply_eq_linOf {x : MulAut V} (hx : ∀ w, x (z w) = z (x w)) (w : V) :
    (coordEquiv hb).symm (x w) =
      Multiplicative.ofAdd (linOf hb hzz hx (Multiplicative.toAdd ((coordEquiv hb).symm w))) := by
  apply (coordEquiv hb).injective
  rw [MulEquiv.apply_symm_apply, coordEquiv_linOf hb hzz, ofAdd_toAdd, MulEquiv.apply_symm_apply]

theorem linOf_mul {x y : MulAut V} (hx : ∀ w, x (z w) = z (x w)) (hy : ∀ w, y (z w) = z (y w))
    (hxy : ∀ w, (x * y) (z w) = z ((x * y) w)) :
    linOf hb hzz hxy = (linOf hb hzz hx).comp (linOf hb hzz hy) := by
  refine LinearMap.ext fun c => ?_
  apply Multiplicative.ofAdd.injective
  apply (coordEquiv hb).injective
  rw [LinearMap.comp_apply, coordEquiv_linOf, coordEquiv_linOf, coordEquiv_linOf]
  rfl

theorem linOf_one (h1 : ∀ w, (1 : MulAut V) (z w) = z ((1 : MulAut V) w)) :
    linOf hb hzz h1 = LinearMap.id := by
  refine LinearMap.ext fun c => ?_
  apply Multiplicative.ofAdd.injective
  apply (coordEquiv hb).injective
  rw [coordEquiv_linOf, LinearMap.id_apply]
  rfl

theorem linOf_eq_id {x : MulAut V} (hx : ∀ w, x (z w) = z (x w)) (h : x = 1) :
    linOf hb hzz hx = LinearMap.id := by
  subst h
  exact linOf_one hb hzz hx

theorem linOf_z (hz : ∀ w, z (z w) = z (z w)) :
    linOf hb hzz hz = FieldFour.ω • LinearMap.id := by
  refine LinearMap.ext fun c => ?_
  apply Multiplicative.ofAdd.injective
  apply (coordEquiv hb).injective
  rw [coordEquiv_linOf, LinearMap.smul_apply, LinearMap.id_apply, coordEquiv_smul hb hzz,
    fsmul_ω]

theorem eq_of_linOf_eq {x y : MulAut V} (hx : ∀ w, x (z w) = z (x w))
    (hy : ∀ w, y (z w) = z (y w)) (h : linOf hb hzz hx = linOf hb hzz hy) : x = y := by
  ext w
  obtain ⟨c, rfl⟩ := (coordEquiv hb).surjective w
  rw [← ofAdd_toAdd c, ← coordEquiv_linOf hb hzz hx, ← coordEquiv_linOf hb hzz hy, h]

@[expose] noncomputable def matOf {x : MulAut V} (hx : ∀ w, x (z w) = z (x w)) :
    Matrix (Fin 3) (Fin 3) FieldFour :=
  LinearMap.toMatrix' (linOf hb hzz hx)

theorem matOf_mulVec {x : MulAut V} (hx : ∀ w, x (z w) = z (x w)) (c : Fin 3 → FieldFour) :
    matOf hb hzz hx *ᵥ c = linOf hb hzz hx c := by
  rw [matOf, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']

@[expose] noncomputable def glOf (X : Subgroup (MulAut V))
    (hX : ∀ x ∈ X, ∀ w, x (z w) = z (x w)) : ↥X →* GL (Fin 3) FieldFour where
  toFun x :=
    { val := matOf hb hzz (hX x x.2)
      inv := matOf hb hzz (hX _ (x⁻¹).2)
      val_inv := by
        rw [matOf, matOf, ← LinearMap.toMatrix'_comp,
          ← linOf_mul hb hzz (hX x x.2) (hX _ (x⁻¹).2) (hX _ (x * x⁻¹).2),
          linOf_eq_id hb hzz _ (by rw [← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one]),
          LinearMap.toMatrix'_id]
      inv_val := by
        rw [matOf, matOf, ← LinearMap.toMatrix'_comp,
          ← linOf_mul hb hzz (hX _ (x⁻¹).2) (hX x x.2) (hX _ (x⁻¹ * x).2),
          linOf_eq_id hb hzz _ (by rw [← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one]),
          LinearMap.toMatrix'_id] }
  map_one' := by
    refine Units.ext ?_
    change matOf hb hzz _ = 1
    rw [matOf, linOf_eq_id hb hzz _ rfl, LinearMap.toMatrix'_id]
  map_mul' x y := by
    refine Units.ext ?_
    change matOf hb hzz _ = matOf hb hzz _ * matOf hb hzz _
    rw [matOf, matOf, matOf, ← LinearMap.toMatrix'_comp]
    congr 1
    exact linOf_mul hb hzz _ _ _

theorem glOf_mulVec (X : Subgroup (MulAut V)) (hX : ∀ x ∈ X, ∀ w, x (z w) = z (x w)) (x : ↥X)
    (c : Fin 3 → FieldFour) :
    ((glOf hb hzz X hX x : GL (Fin 3) FieldFour) : Matrix (Fin 3) (Fin 3) FieldFour) *ᵥ c =
      linOf hb hzz (hX x x.2) c :=
  matOf_mulVec hb hzz _ c

theorem glOf_injective (X : Subgroup (MulAut V)) (hX : ∀ x ∈ X, ∀ w, x (z w) = z (x w)) :
    Function.Injective (glOf hb hzz X hX) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h1 : ∀ w, (1 : MulAut V) (z w) = z ((1 : MulAut V) w) := fun w => rfl
  have h := congrArg (fun g : GL (Fin 3) FieldFour => Matrix.toLin' (g : Matrix (Fin 3) (Fin 3)
    FieldFour)) hx
  change Matrix.toLin' (matOf hb hzz (hX x x.2)) = Matrix.toLin' (1 : Matrix (Fin 3) (Fin 3)
    FieldFour) at h
  rw [matOf, Matrix.toLin'_toMatrix', Matrix.toLin'_one, ← linOf_one hb hzz h1] at h
  exact Subtype.ext (eq_of_linOf_eq hb hzz (hX x x.2) h1 h)

end Linear

end CFSG.Quasithin.HatA6
