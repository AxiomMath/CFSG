module

public import CFSG.LocalAnalysis.StandardType.GGTBTorRelDMinusDefs
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelCoordinates
public import CFSG.Timmesfeld.Orders.ClassicalAnisotropic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataConjugation
public import CFSG.Quasithin.Vol2.KGFactC31LieSylEig
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular

public section

namespace CFSG.StandardType

namespace RelDMinus

open CFSG.Assembly Matrix TableBSymp
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.Quasithin.KGC31

variable {K : Type} [Field K] [Finite K] [CharP K 2]
variable {m p : ℕ} [Fact p.Prime] {ζ : Kˣ}
variable {b c : K}

@[expose] def blockInrMat :
    Matrix (Fin 2) (Fin 2) K →* Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K where
  toFun A := Matrix.fromBlocks 1 0 0 A
  map_one' := by rw [Matrix.fromBlocks_one]
  map_mul' A B := by
    rw [Matrix.fromBlocks_multiply]
    simp

@[expose] noncomputable def blockInrGL : GL (Fin 2) K →* GL (LargeEvenMinusIdx m) K :=
  Units.map blockInrMat

theorem coe_blockInrGL (g : GL (Fin 2) K) :
    ((blockInrGL g : GL (LargeEvenMinusIdx m) K) :
      Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) =
      Matrix.fromBlocks 1 0 0 (g : Matrix (Fin 2) (Fin 2) K) :=
  rfl

@[expose] def anisoN (b c : K) (w : Fin 2 → K) : K :=
  w 0 ^ 2 + b * w 0 * w 1 + c * w 1 ^ 2

theorem anisoN_eq_minusTailForm (b c : K) (w : Fin 2 → K) :
    anisoN b c w = minusTailForm K b c w := by
  rw [anisoN, minusTailForm_apply]

theorem coe_torusGL_eq_diagonal (x : Fin m → Kˣ) :
    ((torusGL K m x : GL (LargeEvenMinusIdx m) K) :
      Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) =
      Matrix.diagonal (fun r => match r with
        | Sum.inl (Sum.inl i) => (x i : K)
        | Sum.inl (Sum.inr i) => ((x i)⁻¹ : K)
        | Sum.inr _ => 1) := by
  rw [torusGL_apply, coe_blockInl, TauCeti.diagGL_coe,
    show (1 : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal (fun _ => 1) from
      Matrix.diagonal_one.symm,
    Matrix.fromBlocks_diagonal]
  congr 1
  funext r
  rcases r with (i | i) | j <;> simp [pairedUnits]

@[simp] theorem torusGL_apply_inl_inl (x : Fin m → Kˣ) (i : Fin m) :
    ((torusGL K m x : GL (LargeEvenMinusIdx m) K) :
      Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K)
      (Sum.inl (Sum.inl i)) (Sum.inl (Sum.inl i)) = (x i : K) := by
  simp [coe_torusGL_eq_diagonal]

@[simp] theorem torusGL_apply_inl_inr (x : Fin m → Kˣ) (i : Fin m) :
    ((torusGL K m x : GL (LargeEvenMinusIdx m) K) :
      Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K)
      (Sum.inl (Sum.inr i)) (Sum.inl (Sum.inr i)) = ((x i)⁻¹ : K) := by
  simp [coe_torusGL_eq_diagonal]

@[simp] theorem torusGL_apply_inr (x : Fin m → Kˣ) (i : Fin 2) :
    ((torusGL K m x : GL (LargeEvenMinusIdx m) K) :
      Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K)
      (Sum.inr i) (Sum.inr i) = 1 := by
  simp [coe_torusGL_eq_diagonal]

theorem torusGL_mem_primeTorusGL {x : Fin m → Kˣ} (hx : x ^ p = 1) :
    torusGL K m x ∈ primeTorusGL K m p :=
  (mem_primeTorusGL K m).mpr ⟨x, hx, rfl⟩

theorem eq_one_of_isometry_pow_card_sub_one_eq_one {h : GL (Fin 2) K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hiso : ∀ w : Fin 2 → K,
      minusTailForm K b c ((h : Matrix (Fin 2) (Fin 2) K) *ᵥ w) = minusTailForm K b c w)
    (hpow : h ^ (Nat.card K - 1) = 1) : h = 1 := by
  classical
  let Q : QuadraticForm K (Fin 2 → K) := minusTailForm K b c
  have hQani : Q.Anisotropic := anisotropic_minusTailForm hirr
  have hmem : h ∈ matrixIsometries Q := by
    rw [mem_matrixIsometries_iff]
    intro v
    rw [matrixLinearEquiv_apply]
    exact hiso v
  have hdvd₁ : orderOf h ∣ Nat.card (matrixIsometries Q) :=
    Subgroup.orderOf_dvd_natCard _ hmem
  have hcard : Nat.card (matrixIsometries Q) ∣
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) :=
    Subgroup.card_comap_dvd_of_injective _ _ (MulEquiv.injective _)
  have hcardQ : Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) =
      2 * (Nat.card K + 1) :=
    CFSG.Timmesfeld.ClassicalOrders.card_orthogonalGroup_of_anisotropic
      (A := Fin 2 → K) (Q := Q) finrank_fin_two_fun
      (fun x hx h => hx (hQani x h))
  have hdvd₂ : orderOf h ∣ 2 * (Nat.card K + 1) := by
    rw [← hcardQ]
    exact hdvd₁.trans hcard
  have hdvd₃ : orderOf h ∣ Nat.card K - 1 := orderOf_dvd_of_pow_eq_one hpow
  letI : Fintype K := Fintype.ofFinite K
  have hqpos : 1 ≤ Nat.card K := Nat.card_pos
  have h2dvd : 2 ∣ Nat.card K := by
    rw [Nat.card_eq_fintype_card]
    exact Nat.dvd_of_mod_eq_zero
      (FiniteField.even_card_of_char_two (F := K) (ringChar.eq K 2))
  have hOdd : Odd (Nat.card K - 1) := by
    obtain ⟨k, hk⟩ := h2dvd
    rw [odd_iff_exists_bit1]
    exact ⟨k - 1, by omega⟩
  have hdvd₄ : orderOf h ∣ 4 := by
    have h2 : orderOf h ∣ 2 * (Nat.card K - 1) := dvd_mul_of_dvd_right hdvd₃ 2
    have h4 : 2 * (Nat.card K + 1) = 2 * (Nat.card K - 1) + 4 := by omega
    rw [h4] at hdvd₂
    exact (Nat.dvd_add_iff_right h2).mpr hdvd₂
  have hcop : Nat.Coprime 4 (Nat.card K - 1) := by
    simpa using hOdd.coprime_two_left.pow_left 2
  have horder : orderOf h = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd₄ hdvd₃
  exact orderOf_eq_one_iff.mp horder

@[expose] def pairOf : Fin m ⊕ Fin m → Fin m := Sum.elim (fun i => i) (fun i => i)

theorem zeta_pow_eq_one {ζ : Kˣ} (hζ : orderOf ζ = p) : ζ ^ p = 1 := by
  rw [← hζ]
  exact pow_orderOf_eq_one ζ

theorem zeta_ne_one {ζ : Kˣ} (hζ : orderOf ζ = p) : ζ ≠ 1 := by
  intro h
  rw [h, orderOf_one] at hζ
  exact (Fact.out : p.Prime).one_lt.ne hζ

theorem zeta_ne_inv {ζ : Kˣ} (hp2 : p ≠ 2) (hζ : orderOf ζ = p) : ζ ≠ ζ⁻¹ := by
  intro h
  have h2 : ζ ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 2 [h]
    exact mul_inv_cancel ζ
  have hpdvd : p ∣ 2 := by
    rw [← hζ]
    exact orderOf_dvd_of_pow_eq_one h2
  have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hpdvd
  have hge : 2 ≤ p := (Fact.out : p.Prime).two_le
  omega

theorem primeTorus_mulVec_single {x : GL (LargeEvenMinusIdx m) K}
    (hx : x ∈ primeTorusGL K m p) (r : LargeEvenMinusIdx m) :
    (x : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) *ᵥ Pi.single r 1 =
      ((x : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) r r) • Pi.single r 1 := by
  obtain ⟨u, -, rfl⟩ := (mem_primeTorusGL K m).mp hx
  rw [coe_torusGL_eq_diagonal, Matrix.diagonal_mulVec_single, ← Pi.single_smul']
  simp

theorem mulSingle_zeta_mem_primeTorus {ζ : Kˣ} (hζ : orderOf ζ = p) (i : Fin m) :
    torusGL K m (Pi.mulSingle i ζ) ∈ primeTorusGL K m p := by
  apply torusGL_mem_primeTorusGL
  funext j
  rw [Pi.pow_apply]
  by_cases hj : j = i
  · subst hj
    simpa using zeta_pow_eq_one hζ
  · simp [Pi.mulSingle, Function.update_apply, hj]

theorem exists_torus_char_ne {ζ : Kˣ} (hp2 : p ≠ 2) (hζ : orderOf ζ = p)
    {d₁ d₂ : Fin m ⊕ Fin m} (h : d₁ ≠ d₂) :
    ∃ x ∈ primeTorusGL K m p,
      ((x : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) (Sum.inl d₁) (Sum.inl d₁)) ≠
        ((x : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) (Sum.inl d₂) (Sum.inl d₂)) := by
  classical
  have hζ1 := zeta_ne_one hζ
  have hζi : ζ⁻¹ ≠ 1 := inv_ne_one.mpr hζ1
  have hζni := zeta_ne_inv (p := p) hp2 hζ
  let i : Fin m := pairOf d₁
  refine ⟨torusGL K m (Pi.mulSingle i ζ), mulSingle_zeta_mem_primeTorus hζ i, ?_⟩
  rcases d₁ with i₁ | i₁ <;> rcases d₂ with i₂ | i₂
  · have hii : i₁ ≠ i₂ := by
      intro h12
      exact h (by rw [h12])
    rw [show i = i₁ from rfl]
    simp only [torusGL_apply_inl_inl, Pi.mulSingle, Function.update_apply, if_pos rfl,
      if_neg hii.symm]
    simpa using hζ1
  · by_cases hii : i₂ = i₁
    · rw [hii, show i = i₁ from rfl]
      simp only [torusGL_apply_inl_inl, torusGL_apply_inl_inr, Pi.mulSingle,
        Function.update_apply, if_pos rfl]
      intro hh
      exact hζni (Units.ext (by simpa using hh))
    · rw [show i = i₁ from rfl]
      simp only [torusGL_apply_inl_inl, torusGL_apply_inl_inr, Pi.mulSingle,
        Function.update_apply, if_pos rfl, if_neg hii]
      simpa using hζ1
  · by_cases hii : i₂ = i₁
    · rw [hii, show i = i₁ from rfl]
      simp only [torusGL_apply_inl_inr, torusGL_apply_inl_inl, Pi.mulSingle,
        Function.update_apply, if_pos rfl]
      intro hh
      exact hζni (Units.ext (by simpa using hh.symm))
    · rw [show i = i₁ from rfl]
      simp only [torusGL_apply_inl_inr, torusGL_apply_inl_inl, Pi.mulSingle,
        Function.update_apply, if_pos rfl, if_neg hii]
      simpa using hζi
  · have hii : i₁ ≠ i₂ := by
      intro h12
      exact h (by rw [h12])
    rw [show i = i₁ from rfl]
    simp only [torusGL_apply_inl_inr, Pi.mulSingle, Function.update_apply, if_pos rfl,
      if_neg hii.symm]
    simpa using hζi

theorem exists_torus_char_ne_one {ζ : Kˣ} (hζ : orderOf ζ = p)
    (c : Fin m ⊕ Fin m) :
    ∃ x ∈ primeTorusGL K m p,
      ((x : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) (Sum.inl c) (Sum.inl c)) ≠ 1 := by
  classical
  have hζ1 := zeta_ne_one hζ
  have hζi : ζ⁻¹ ≠ 1 := inv_ne_one.mpr hζ1
  let i : Fin m := pairOf c
  refine ⟨torusGL K m (Pi.mulSingle i ζ), mulSingle_zeta_mem_primeTorus hζ i, ?_⟩
  rcases c with i₁ | i₁
  · rw [torusGL_apply_inl_inl, show i = i₁ from rfl]
    simp only [Pi.mulSingle, Function.update_apply, if_pos rfl]
    simpa using hζ1
  · rw [torusGL_apply_inl_inr, show i = i₁ from rfl]
    simp only [Pi.mulSingle, Function.update_apply, if_pos rfl]
    simpa [Units.val_inv_eq_inv_val] using hζi

theorem support_inl_of_commute_primeTorus {ζ : Kˣ} (hp2 : p ≠ 2) (hζ : orderOf ζ = p)
    {g : GL (LargeEvenMinusIdx m) K}
    (hc : ∀ e ∈ primeTorusGL K m p, g * e = e * g)
    (c : Fin m ⊕ Fin m) :
    ∀ r : LargeEvenMinusIdx m,
      (g : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) r (Sum.inl c) ≠ 0 →
        r = Sum.inl c := by
  classical
  let T := primeTorusGL K m p
  let ρ : GL (LargeEvenMinusIdx m) K →* Module.End K (LargeEvenMinusIdx m → K) :=
    ((Matrix.toLinAlgEquiv' :
        Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K ≃ₐ[K]
          (LargeEvenMinusIdx m → K) →ₗ[K] (LargeEvenMinusIdx m → K)).toAlgHom.toMonoidHom).comp
      (Units.coeHom (Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K))
  let χ : LargeEvenMinusIdx m → GL (LargeEvenMinusIdx m) K → K :=
    fun r x => (x : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) r r
  have hχ : ∀ x ∈ T, ∀ r, ρ x (Pi.basisFun K (LargeEvenMinusIdx m) r) =
      χ r x • Pi.basisFun K (LargeEvenMinusIdx m) r := by
    intro x hx r
    simpa [ρ, χ, Pi.basisFun_apply] using primeTorus_mulVec_single hx r
  let v : LargeEvenMinusIdx m → K :=
    ρ g (Pi.basisFun K (LargeEvenMinusIdx m) (Sum.inl c))
  have hv_coord : ∀ r, v r =
      (g : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) r (Sum.inl c) := by
    intro r
    simp [v, ρ, Pi.basisFun_apply, Matrix.mulVec_single]
  have hψ : ∀ x ∈ T, ρ x v = χ (Sum.inl c) x • v := by
    intro x hx
    have hcomm : x * g = g * x := (hc x hx).symm
    calc ρ x v = ρ (x * g) (Pi.basisFun K (LargeEvenMinusIdx m) (Sum.inl c)) := by
          rw [map_mul, Module.End.mul_apply]
      _ = ρ (g * x) (Pi.basisFun K (LargeEvenMinusIdx m) (Sum.inl c)) := by rw [hcomm]
      _ = ρ g (ρ x (Pi.basisFun K (LargeEvenMinusIdx m) (Sum.inl c))) := by
          rw [map_mul, Module.End.mul_apply]
      _ = ρ g (χ (Sum.inl c) x • Pi.basisFun K (LargeEvenMinusIdx m) (Sum.inl c)) := by
          rw [hχ x hx]
      _ = χ (Sum.inl c) x • v := by rw [map_smul]
  intro r hr
  have hchar : ∀ x ∈ T, χ r x = χ (Sum.inl c) x :=
    eigen_support hχ hψ (by rw [Pi.basisFun_repr, hv_coord r]; exact hr)
  rcases r with d | j
  · by_contra hdc
    have hdc' : d ≠ c := fun h' => hdc (by rw [h'])
    obtain ⟨x, hxT, hxne⟩ := exists_torus_char_ne (p := p) (m := m)
      (d₁ := d) (d₂ := c) hp2 hζ hdc'
    exact hxne (by simpa [χ] using hchar x hxT)
  · obtain ⟨x, hxT, hx1⟩ := exists_torus_char_ne_one (p := p) (m := m) hζ c
    obtain ⟨u, -, rfl⟩ := (mem_primeTorusGL K m).mp hxT
    have h := hchar (torusGL K m u) hxT
    have h1 : χ (Sum.inr j) (torusGL K m u) = 1 := by
      change ((torusGL K m u : GL (LargeEvenMinusIdx m) K) :
        Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) (Sum.inr j) (Sum.inr j) = 1
      exact torusGL_apply_inr u j
    rw [h1] at h
    exact absurd h.symm hx1

theorem support_inr_of_commute_primeTorus {ζ : Kˣ} (hζ : orderOf ζ = p)
    {g : GL (LargeEvenMinusIdx m) K}
    (hc : ∀ e ∈ primeTorusGL K m p, g * e = e * g)
    (j : Fin 2) :
    ∀ r : LargeEvenMinusIdx m,
      (g : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) r (Sum.inr j) ≠ 0 →
        r = Sum.inr 0 ∨ r = Sum.inr 1 := by
  classical
  let T := primeTorusGL K m p
  let ρ : GL (LargeEvenMinusIdx m) K →* Module.End K (LargeEvenMinusIdx m → K) :=
    ((Matrix.toLinAlgEquiv' :
        Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K ≃ₐ[K]
          (LargeEvenMinusIdx m → K) →ₗ[K] (LargeEvenMinusIdx m → K)).toAlgHom.toMonoidHom).comp
      (Units.coeHom (Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K))
  let χ : LargeEvenMinusIdx m → GL (LargeEvenMinusIdx m) K → K :=
    fun r x => (x : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) r r
  have hχ : ∀ x ∈ T, ∀ r, ρ x (Pi.basisFun K (LargeEvenMinusIdx m) r) =
      χ r x • Pi.basisFun K (LargeEvenMinusIdx m) r := by
    intro x hx r
    simpa [ρ, χ, Pi.basisFun_apply] using primeTorus_mulVec_single hx r
  let v : LargeEvenMinusIdx m → K :=
    ρ g (Pi.basisFun K (LargeEvenMinusIdx m) (Sum.inr j))
  have hv_coord : ∀ r, v r =
      (g : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) r (Sum.inr j) := by
    intro r
    simp [v, ρ, Pi.basisFun_apply, Matrix.mulVec_single]
  have hχinr : ∀ x ∈ T, χ (Sum.inr j) x = 1 := by
    intro x hx
    obtain ⟨u, -, rfl⟩ := (mem_primeTorusGL K m).mp hx
    change ((torusGL K m u : GL (LargeEvenMinusIdx m) K) :
      Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) (Sum.inr j) (Sum.inr j) = 1
    exact torusGL_apply_inr u j
  have hψ : ∀ x ∈ T, ρ x v = (fun _ => (1 : K)) x • v := by
    intro x hx
    have hcomm : x * g = g * x := (hc x hx).symm
    calc ρ x v = ρ (x * g) (Pi.basisFun K (LargeEvenMinusIdx m) (Sum.inr j)) := by
          rw [map_mul, Module.End.mul_apply]
      _ = ρ (g * x) (Pi.basisFun K (LargeEvenMinusIdx m) (Sum.inr j)) := by rw [hcomm]
      _ = ρ g (ρ x (Pi.basisFun K (LargeEvenMinusIdx m) (Sum.inr j))) := by
          rw [map_mul, Module.End.mul_apply]
      _ = ρ g (χ (Sum.inr j) x • Pi.basisFun K (LargeEvenMinusIdx m) (Sum.inr j)) := by
          rw [hχ x hx]
      _ = ρ g ((1 : K) • Pi.basisFun K (LargeEvenMinusIdx m) (Sum.inr j)) := by
          rw [hχinr x hx]
      _ = (fun _ => (1 : K)) x • v := by
          simp [v]
  intro r hr
  have hchar : ∀ x ∈ T, χ r x = 1 := by
    intro x hx
    simpa using eigen_support hχ hψ
      (by rw [Pi.basisFun_repr, hv_coord r]; exact hr) x hx
  rcases r with d | j'
  · obtain ⟨x, hxT, hx1⟩ := exists_torus_char_ne_one (p := p) (m := m) hζ d
    exfalso
    exact hx1 (by simpa [χ] using hchar x hxT)
  · fin_cases j' <;> simp

theorem largeEvenQMinus_vec_pair (b c : K) (i : Fin m) (a d : K) :
    LargeEvenQMinus m b c
      (a • Pi.single (Sum.inl (Sum.inl i)) 1 +
        d • Pi.single (Sum.inl (Sum.inr i)) 1) = a * d := by
  have h1 : ∀ k : Fin m,
      (a • Pi.single (Sum.inl (Sum.inl i)) 1 +
        d • Pi.single (Sum.inl (Sum.inr i)) 1 : LargeEvenMinusIdx m → K)
        (Sum.inl (Sum.inl k)) = if k = i then a else 0 := by
    intro k
    by_cases hk : k = i <;> simp [hk]
  have h2 : ∀ k : Fin m,
      (a • Pi.single (Sum.inl (Sum.inl i)) 1 +
        d • Pi.single (Sum.inl (Sum.inr i)) 1 : LargeEvenMinusIdx m → K)
        (Sum.inl (Sum.inr k)) = if k = i then d else 0 := by
    intro k
    by_cases hk : k = i <;> simp [hk]
  have h3 : (a • Pi.single (Sum.inl (Sum.inl i)) 1 +
      d • Pi.single (Sum.inl (Sum.inr i)) 1 : LargeEvenMinusIdx m → K)
      (Sum.inr 0) = 0 := by simp
  have h4 : (a • Pi.single (Sum.inl (Sum.inl i)) 1 +
      d • Pi.single (Sum.inl (Sum.inr i)) 1 : LargeEvenMinusIdx m → K)
      (Sum.inr 1) = 0 := by simp
  simp only [LargeEvenQMinus, h1, h2, h3, h4]
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk
    simp [hk]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem coe_torusGL_fromBlocks (x : Fin m → Kˣ) :
    ((torusGL K m x : GL (LargeEvenMinusIdx m) K) :
      Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) =
      Matrix.fromBlocks (TauCeti.diagGL (pairedUnits x) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) 0 0 1 := by
  rw [torusGL_apply, coe_blockInl]

@[expose] def basisVec (r : LargeEvenMinusIdx m) : LargeEvenMinusIdx m → K := Pi.single r 1

theorem largeEvenQMinus_basisVec_pair (b c : K) (i : Fin m) (a d : K) :
    LargeEvenQMinus m b c
      (a • basisVec (Sum.inl (Sum.inl i)) + d • basisVec (Sum.inl (Sum.inr i))) = a * d := by
  simpa [basisVec] using largeEvenQMinus_vec_pair b c i a d

theorem isometry_of_mem_largeEvenOrthGroup {Q : (LargeEvenMinusIdx m → K) → K}
    {g : GL (LargeEvenMinusIdx m) K}
    (hg : g ∈ LargeEvenOrthGroup Q) (v : LargeEvenMinusIdx m → K) :
    Q ((g : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) *ᵥ v) = Q v := by
  rw [largeEvenOrthGroup_def] at hg
  induction hg using Subgroup.closure_induction generalizing v with
  | mem x hx => exact hx v
  | one => simp
  | mul x y _ _ hx hy => rw [Units.val_mul, ← Matrix.mulVec_mulVec, hx, hy]
  | inv x _ hx =>
      have h1 := hx (((x⁻¹ : GL (LargeEvenMinusIdx m) K) :
        Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) *ᵥ v)
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel x, Units.val_one,
        Matrix.one_mulVec] at h1
      exact h1.symm

theorem largeEvenQMinus_basisVec_pair_ne_zero {b c : K} {a d : K} (ha : a ≠ 0) (hd : d ≠ 0)
    {p q : Fin m ⊕ Fin m}
    (h : LargeEvenQMinus m b c
      (a • basisVec (Sum.inl p) + d • basisVec (Sum.inl q)) ≠ 0) :
    (∃ j, p = Sum.inl j ∧ q = Sum.inr j) ∨
      (∃ j, p = Sum.inr j ∧ q = Sum.inl j) := by
  by_contra hpair
  push Not at hpair
  rcases p with j | j <;> rcases q with k | k
  · apply h
    simp [largeEvenQMinus_eq, largeEvenQPlus_def, basisVec, Pi.single_apply]
  · have hjk : j ≠ k := by
      intro hjk
      exact hpair.1 j rfl (by rw [hjk])
    apply h
    rw [largeEvenQMinus_eq]
    simp [largeEvenQPlus_def, basisVec, Pi.single_apply, hjk, Ne.symm hjk]
  · have hjk : j ≠ k := by
      intro hjk
      exact hpair.2 j rfl (by rw [hjk])
    apply h
    rw [largeEvenQMinus_eq]
    simp [largeEvenQPlus_def, basisVec, Pi.single_apply, hjk, Ne.symm hjk]
  · apply h
    simp [largeEvenQMinus_eq, largeEvenQPlus_def, basisVec, Pi.single_apply]

theorem column_inl_eq_of_commute_primeTorus {ζ : Kˣ} (hp2 : p ≠ 2) (hζ : orderOf ζ = p)
    {g : GL (LargeEvenMinusIdx m) K}
    (hc : ∀ e ∈ primeTorusGL K m p, g * e = e * g) (c : Fin m ⊕ Fin m) :
    (g : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) *ᵥ basisVec (Sum.inl c) =
      ((g : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K)
        (Sum.inl c) (Sum.inl c)) • basisVec (Sum.inl c) := by
  rw [basisVec, Matrix.mulVec_single_one]
  funext r
  by_cases hr : r = Sum.inl c
  · subst hr
    simp [basisVec]
  · have hz : (g : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K)
        r (Sum.inl c) = 0 := by
      by_contra hne
      exact hr (support_inl_of_commute_primeTorus (p := p) (m := m) hp2 hζ hc c r hne)
    simp [hz, hr, basisVec]

theorem column_inl_ne_zero_of_commute_primeTorus {ζ : Kˣ} (hp2 : p ≠ 2)
    (hζ : orderOf ζ = p) {g : GL (LargeEvenMinusIdx m) K}
    (hc : ∀ e ∈ primeTorusGL K m p, g * e = e * g) (c : Fin m ⊕ Fin m) :
    (g : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) (Sum.inl c) (Sum.inl c) ≠ 0 := by
  intro h0
  have hcol : (g : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) *ᵥ
      basisVec (Sum.inl c) = 0 := by
    rw [column_inl_eq_of_commute_primeTorus (p := p) (m := m) hp2 hζ hc c, h0]
    simp
  have h1 : ((g⁻¹ : GL (LargeEvenMinusIdx m) K) :
      Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) *ᵥ
      ((g : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) *ᵥ
        basisVec (Sum.inl c)) = basisVec (Sum.inl c) := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel g, Units.val_one,
      Matrix.one_mulVec]
  rw [hcol, Matrix.mulVec_zero] at h1
  have hsingle : basisVec (K := K) (m := m) (Sum.inl c) ≠ 0 := by
    intro h
    have hc : (1 : K) = 0 := by
      simpa [basisVec] using congrFun h (Sum.inl c)
    exact one_ne_zero hc
  exact hsingle h1.symm

theorem exists_block_diag_of_commute_primeTorus {b c : K} {ζ : Kˣ} (hp2 : p ≠ 2)
    (hζ : orderOf ζ = p) {g : GL (LargeEvenMinusIdx m) K}
    (hg : g ∈ LargeEvenOrthGroup (LargeEvenQMinus m b c))
    (hc : ∀ e ∈ primeTorusGL K m p, g * e = e * g) :
    ∃ (a d : Fin m → K) (hmat : Matrix (Fin 2) (Fin 2) K),
      (∀ i, a i ≠ 0) ∧ (∀ i, d i ≠ 0) ∧ (∀ i, a i * d i = 1) ∧
      (g : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) =
        Matrix.fromBlocks (Matrix.diagonal (Sum.elim a d)) 0 0 hmat ∧
      Nonempty (Invertible hmat) ∧
      (∀ v : LargeEvenMinusIdx m → K,
        LargeEvenQMinus m b c
          ((g : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) *ᵥ v) =
          LargeEvenQMinus m b c v) := by
  classical
  let A : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K :=
    (g : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K)
  let a : Fin m → K := fun i => A (Sum.inl (Sum.inl i)) (Sum.inl (Sum.inl i))
  let d : Fin m → K := fun i => A (Sum.inl (Sum.inr i)) (Sum.inl (Sum.inr i))
  have ha : ∀ i, a i ≠ 0 := fun i =>
    column_inl_ne_zero_of_commute_primeTorus (p := p) (m := m) hp2 hζ hc (Sum.inl i)
  have hd : ∀ i, d i ≠ 0 := fun i =>
    column_inl_ne_zero_of_commute_primeTorus (p := p) (m := m) hp2 hζ hc (Sum.inr i)
  have isometry_of_mem : ∀ {w : GL (LargeEvenMinusIdx m) K},
      w ∈ LargeEvenOrthGroup (LargeEvenQMinus m b c) → ∀ v : LargeEvenMinusIdx m → K,
        LargeEvenQMinus m b c
          ((w : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) *ᵥ v) =
        LargeEvenQMinus m b c v := by
    intro w hw v
    induction hw using Subgroup.closure_induction generalizing v with
    | mem x hx => exact hx v
    | one => simp
    | mul x y _ _ hx hy => rw [Units.val_mul, ← Matrix.mulVec_mulVec, hx, hy]
    | inv x _ hx =>
        have h1 := hx (((x⁻¹ : GL (LargeEvenMinusIdx m) K) :
          Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) *ᵥ v)
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel x, Units.val_one,
          Matrix.one_mulVec] at h1
        exact h1.symm
  have hiso_all : ∀ v : LargeEvenMinusIdx m → K,
      LargeEvenQMinus m b c
        ((g : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) *ᵥ v) =
        LargeEvenQMinus m b c v := fun v => isometry_of_mem hg v
  have hamul : ∀ i, a i * d i = 1 := by
    intro i
    have hiso := hiso_all (basisVec (Sum.inl (Sum.inl i)) + basisVec (Sum.inl (Sum.inr i)))
    rw [Matrix.mulVec_add,
      column_inl_eq_of_commute_primeTorus (p := p) (m := m) hp2 hζ hc (Sum.inl i),
      column_inl_eq_of_commute_primeTorus (p := p) (m := m) hp2 hζ hc (Sum.inr i)] at hiso
    have hQv : LargeEvenQMinus m b c
        (basisVec (Sum.inl (Sum.inl i)) + basisVec (Sum.inl (Sum.inr i))) = 1 := by
      simpa [one_smul] using largeEvenQMinus_basisVec_pair b c i (1 : K) (1 : K)
    rw [hQv, largeEvenQMinus_basisVec_pair] at hiso
    simpa [a, d] using hiso
  let hmat : Matrix (Fin 2) (Fin 2) K := fun r s => A (Sum.inr r) (Sum.inr s)
  have hAeq : A = Matrix.fromBlocks (Matrix.diagonal (Sum.elim a d)) 0 0 hmat := by
    ext r s
    rcases r with w | j <;> rcases s with w' | j'
    · rw [Matrix.fromBlocks_apply₁₁]
      by_cases hww : w = w'
      · subst hww
        rcases w with i | i <;> simp [a, d]
      · have hz : A (Sum.inl w) (Sum.inl w') = 0 := by
          by_contra hne
          exact hww (Sum.inl_injective
            (support_inl_of_commute_primeTorus (p := p) (m := m) hp2 hζ hc w'
              (Sum.inl w) hne))
        rw [hz]
        simp [hww]
    · rw [Matrix.fromBlocks_apply₁₂]
      have hz : A (Sum.inl w) (Sum.inr j') = 0 := by
        by_contra hne
        rcases support_inr_of_commute_primeTorus (p := p) (m := m) hζ hc j' (Sum.inl w) hne
          with h | h <;> cases h
      rw [hz]
      simp
    · rw [Matrix.fromBlocks_apply₂₁]
      have hz : A (Sum.inr j) (Sum.inl w') = 0 := by
        by_contra hne
        have h := support_inl_of_commute_primeTorus (p := p) (m := m) hp2 hζ hc w'
          (Sum.inr j) hne
        cases h
      rw [hz]
      simp
    · rw [Matrix.fromBlocks_apply₂₂]
  refine ⟨a, d, hmat, ha, hd, hamul, hAeq, ?_⟩
  have hAinv : Invertible A := Units.invertible g
  have hAinv' : Invertible
      (Matrix.fromBlocks (Matrix.diagonal (Sum.elim a d)) 0 0 hmat) := hAeq ▸ hAinv
  exact ⟨⟨((Matrix.fromBlocksZero₁₂InvertibleEquiv (Matrix.diagonal (Sum.elim a d)) 0 hmat)
    hAinv').2⟩, hiso_all⟩

theorem centralizer_primeTorusGL {b c : K} {ζ : Kˣ} (hp2 : p ≠ 2) (hζ : orderOf ζ = p)
    {g : GL (LargeEvenMinusIdx m) K}
    (hg : g ∈ LargeEvenOrthGroup (LargeEvenQMinus m b c))
    (hc : ∀ e ∈ primeTorusGL K m p, g * e = e * g) :
    ∃ x : Fin m → Kˣ, ∃ h : GL (Fin 2) K,
      (∀ w : Fin 2 → K,
        anisoN b c ((h : Matrix (Fin 2) (Fin 2) K) *ᵥ w) = anisoN b c w) ∧
      g = torusGL K m x * blockInrGL h := by
  classical
  obtain ⟨a, d, hmat, ha, hd, hamul, hAeq, hInv, hiso_all⟩ :=
    exists_block_diag_of_commute_primeTorus (p := p) (m := m) hp2 hζ hg hc
  obtain ⟨hInv⟩ := hInv
  let x : Fin m → Kˣ := fun i => Units.mk0 (a i) (ha i)
  let h : GL (Fin 2) K := unitOfInvertible hmat
  have hcoe : ((h : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = hmat := rfl
  have hD : (Matrix.diagonal (Sum.elim a d) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) = TauCeti.diagGL (pairedUnits x) := by
    rw [TauCeti.diagGL_coe]
    congr 1
    funext w
    rcases w with i | i
    · simp [x, pairedUnits]
    · have hdi : d i = (a i)⁻¹ := eq_inv_of_mul_eq_one_right (hamul i)
      simp [x, pairedUnits, hdi]
  have hg_eq : g = torusGL K m x * blockInrGL h := by
    apply Units.ext
    rw [hAeq, hD, Units.val_mul, coe_torusGL_fromBlocks, coe_blockInrGL,
      Matrix.fromBlocks_multiply]
    simp [hcoe]
  have hiso_h : ∀ w : Fin 2 → K, anisoN b c (hmat *ᵥ w) = anisoN b c w := by
    intro w
    let v : LargeEvenMinusIdx m → K := Sum.elim (fun _ => 0) w
    have hAv : (g : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) *ᵥ v =
        Sum.elim (fun _ => 0) (hmat *ᵥ w) := by
      rw [hAeq, Matrix.fromBlocks_mulVec]
      have hz : (fun _ : Fin m ⊕ Fin m => (0 : K)) = 0 := rfl
      simp [v, hz, Matrix.mulVec_zero, Matrix.zero_mulVec]
    have hQ := hiso_all v
    rw [hAv] at hQ
    have h1 : LargeEvenQMinus m b c (Sum.elim (fun _ => 0) (hmat *ᵥ w)) =
        anisoN b c (hmat *ᵥ w) := by
      rw [largeEvenQMinus_eq]
      simp [anisoN, largeEvenQPlus_def]
    have h2 : LargeEvenQMinus m b c (Sum.elim (fun _ => 0) w) = anisoN b c w := by
      rw [largeEvenQMinus_eq]
      simp [anisoN, largeEvenQPlus_def]
    rw [h1, h2] at hQ
    exact hQ
  refine ⟨x, h, ?_, hg_eq⟩
  intro w
  simpa [hcoe] using hiso_h w

theorem blockInl_commute_blockInr (A : GL (Fin m ⊕ Fin m) K) (h : GL (Fin 2) K) :
    blockInl A * blockInrGL h = blockInrGL h * blockInl A := by
  apply Units.ext
  simp [Units.val_mul, coe_blockInl, coe_blockInrGL, Matrix.fromBlocks_multiply]

theorem blockInr_pow_eq_one_of_mul_pow_eq_one {A : GL (Fin m ⊕ Fin m) K} {h : GL (Fin 2) K}
    {N : ℕ} (hcomm : Commute (blockInl A) (blockInrGL h))
    (hpow : (blockInl A * blockInrGL h) ^ N = 1) : h ^ N = 1 := by
  have hprod : (blockInl A * blockInrGL h) ^ N =
      blockInl (A ^ N) * blockInrGL (h ^ N) := by
    rw [hcomm.mul_pow, map_pow, map_pow]
  have hmatrix := congrArg (fun g : GL (LargeEvenMinusIdx m) K =>
    (g : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K)) hpow
  rw [hprod, Units.val_mul, coe_blockInl, coe_blockInrGL, Matrix.fromBlocks_multiply,
    Units.val_one] at hmatrix
  apply Units.ext
  ext r s
  have h := congrFun (congrFun hmatrix (Sum.inr r)) (Sum.inr s)
  simpa [Matrix.fromBlocks_apply₂₂, Matrix.one_apply] using h

theorem eq_torusGL_of_pow_card_sub_one_eq_one {b c : K} {ζ : Kˣ} (hp2 : p ≠ 2)
    (hζ : orderOf ζ = p) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {g : GL (LargeEvenMinusIdx m) K}
    (hg : g ∈ LargeEvenOrthGroup (LargeEvenQMinus m b c))
    (hc : ∀ e ∈ primeTorusGL K m p, g * e = e * g)
    (hpow : g ^ (Nat.card K - 1) = 1) :
    ∃ x : Fin m → Kˣ, g = torusGL K m x := by
  obtain ⟨x, h, hiso, rfl⟩ := centralizer_primeTorusGL (p := p) (m := m) hp2 hζ hg hc
  have hcomm : Commute (torusGL K m x) (blockInrGL h) := by
    rw [torusGL_apply]
    exact blockInl_commute_blockInr _ _
  have hhpow : h ^ (Nat.card K - 1) = 1 :=
    blockInr_pow_eq_one_of_mul_pow_eq_one hcomm hpow
  have hiso' : ∀ w : Fin 2 → K,
      minusTailForm K b c ((h : Matrix (Fin 2) (Fin 2) K) *ᵥ w) = minusTailForm K b c w := by
    intro w
    rw [← anisoN_eq_minusTailForm, ← anisoN_eq_minusTailForm]
    exact hiso w
  have hh : h = 1 := eq_one_of_isometry_pow_card_sub_one_eq_one hirr hiso' hhpow
  refine ⟨x, ?_⟩
  rw [hh, map_one, mul_one]

theorem commute_torusGL_of_mem_centralizer {b c : K} {ζ : Kˣ} (hp2 : p ≠ 2)
    (hζ : orderOf ζ = p) {g : GL (LargeEvenMinusIdx m) K}
    (hg : g ∈ LargeEvenOrthGroup (LargeEvenQMinus m b c))
    (hc : ∀ e ∈ primeTorusGL K m p, g * e = e * g) (x : Fin m → Kˣ) :
    g * torusGL K m x = torusGL K m x * g := by
  obtain ⟨u, h, -, rfl⟩ := centralizer_primeTorusGL (p := p) (m := m) hp2 hζ hg hc
  have htu : torusGL K m u * torusGL K m x = torusGL K m x * torusGL K m u := by
    rw [← map_mul, ← map_mul, mul_comm]
  have hbx : blockInrGL h * torusGL K m x = torusGL K m x * blockInrGL h := by
    rw [torusGL_apply]
    exact (blockInl_commute_blockInr _ _).symm
  calc (torusGL K m u * blockInrGL h) * torusGL K m x
      = torusGL K m u * (blockInrGL h * torusGL K m x) := by group
    _ = torusGL K m u * (torusGL K m x * blockInrGL h) := by rw [hbx]
    _ = (torusGL K m u * torusGL K m x) * blockInrGL h := by group
    _ = (torusGL K m x * torusGL K m u) * blockInrGL h := by rw [htu]
    _ = torusGL K m x * (torusGL K m u * blockInrGL h) := by group

theorem conj_inv_mem_of_normalizes {g : GL (LargeEvenMinusIdx m) K}
    (hn : ∀ e ∈ primeTorusGL K m p, g * e * g⁻¹ ∈ primeTorusGL K m p) :
    ∀ e ∈ primeTorusGL K m p, g⁻¹ * e * g ∈ primeTorusGL K m p := by
  classical
  let T := primeTorusGL K m p
  haveI : Finite T := Subtype.finite
  let φ : T → T := fun x => ⟨g * (x : GL (LargeEvenMinusIdx m) K) * g⁻¹, hn x x.2⟩
  have hφinj : Function.Injective φ := by
    intro x y hxy
    apply Subtype.ext
    have := congrArg (fun z : T => g⁻¹ * (z : GL (LargeEvenMinusIdx m) K) * g) hxy
    simpa [φ] using this
  have hφsurj : Function.Surjective φ := Finite.injective_iff_surjective.mp hφinj
  intro e he
  obtain ⟨x, hx⟩ := hφsurj ⟨e, he⟩
  have hx'' : g * (x : GL (LargeEvenMinusIdx m) K) * g⁻¹ = e := by
    simpa [φ] using congrArg (fun z : T => (z : GL (LargeEvenMinusIdx m) K)) hx
  have hx' : (x : GL (LargeEvenMinusIdx m) K) = g⁻¹ * e * g := by
    calc (x : GL (LargeEvenMinusIdx m) K)
        = g⁻¹ * (g * (x : GL (LargeEvenMinusIdx m) K) * g⁻¹) * g := by group
      _ = g⁻¹ * e * g := by rw [hx'']
  simpa [← hx'] using x.2

theorem column_ne_zero (g : GL (LargeEvenMinusIdx m) K) (c : LargeEvenMinusIdx m) :
    (g : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) *ᵥ basisVec c ≠ 0 := by
  intro h
  have h1 : ((g⁻¹ : GL (LargeEvenMinusIdx m) K) :
      Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) *ᵥ
      ((g : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) *ᵥ basisVec c) =
      basisVec c := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel g, Units.val_one,
      Matrix.one_mulVec]
  rw [h, Matrix.mulVec_zero] at h1
  have hsingle : basisVec (K := K) (m := m) c ≠ 0 := by
    intro hc
    have hcc : (1 : K) = 0 := by
      simpa [basisVec] using congrFun hc c
    exact one_ne_zero hcc
  exact hsingle h1.symm

theorem support_inl_of_normalizes {ζ : Kˣ} (hp2 : p ≠ 2) (hζ : orderOf ζ = p)
    {g : GL (LargeEvenMinusIdx m) K}
    (hn : ∀ e ∈ primeTorusGL K m p, g * e * g⁻¹ ∈ primeTorusGL K m p)
    (c : Fin m ⊕ Fin m) :
    ∃ d : Fin m ⊕ Fin m, ∀ r : LargeEvenMinusIdx m,
      (g : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) r (Sum.inl c) ≠ 0 →
        r = Sum.inl d := by
  classical
  have hinv := conj_inv_mem_of_normalizes hn
  let T := primeTorusGL K m p
  let ρ : GL (LargeEvenMinusIdx m) K →* Module.End K (LargeEvenMinusIdx m → K) :=
    ((Matrix.toLinAlgEquiv' :
        Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K ≃ₐ[K]
          (LargeEvenMinusIdx m → K) →ₗ[K] (LargeEvenMinusIdx m → K)).toAlgHom.toMonoidHom).comp
      (Units.coeHom (Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K))
  let χ : LargeEvenMinusIdx m → GL (LargeEvenMinusIdx m) K → K :=
    fun r x => (x : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) r r
  have hχ : ∀ x ∈ T, ∀ r, ρ x (Pi.basisFun K (LargeEvenMinusIdx m) r) =
      χ r x • Pi.basisFun K (LargeEvenMinusIdx m) r := by
    intro x hx r
    simpa [ρ, χ, Pi.basisFun_apply] using primeTorus_mulVec_single hx r
  let v : LargeEvenMinusIdx m → K :=
    ρ g (Pi.basisFun K (LargeEvenMinusIdx m) (Sum.inl c))
  have hv_coord : ∀ r, v r =
      (g : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) r (Sum.inl c) := by
    intro r
    simp [v, ρ, Pi.basisFun_apply, Matrix.mulVec_single]
  let ψ : GL (LargeEvenMinusIdx m) K → K := fun x => χ (Sum.inl c) (g⁻¹ * x * g)
  have hψ : ∀ x ∈ T, ρ x v = ψ x • v := by
    intro x hx
    have hmem : g⁻¹ * x * g ∈ T := hinv x hx
    calc ρ x v = ρ (x * g) (Pi.basisFun K (LargeEvenMinusIdx m) (Sum.inl c)) := by
          rw [map_mul, Module.End.mul_apply]
      _ = ρ (g * (g⁻¹ * x * g)) (Pi.basisFun K (LargeEvenMinusIdx m) (Sum.inl c)) := by
          rw [show x * g = g * (g⁻¹ * x * g) by group]
      _ = ρ g (ρ (g⁻¹ * x * g) (Pi.basisFun K (LargeEvenMinusIdx m) (Sum.inl c))) := by
          rw [map_mul, Module.End.mul_apply]
      _ = ρ g (χ (Sum.inl c) (g⁻¹ * x * g) •
            Pi.basisFun K (LargeEvenMinusIdx m) (Sum.inl c)) := by rw [hχ _ hmem]
      _ = ψ x • v := by rw [map_smul]
  have hψne : ∃ x ∈ T, ψ x ≠ 1 := by
    obtain ⟨y, hyT, hy1⟩ := exists_torus_char_ne_one (p := p) (m := m) hζ c
    refine ⟨g * y * g⁻¹, hn y hyT, ?_⟩
    have hy : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    simpa [ψ, hy] using hy1
  obtain ⟨r₀, hr₀⟩ : ∃ r, (g : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K)
      r (Sum.inl c) ≠ 0 := by
    by_contra h
    push Not at h
    apply column_ne_zero (K := K) (m := m) g (Sum.inl c)
    funext r
    rw [basisVec, Matrix.mulVec_single_one]
    exact h r
  have hchar₀ : ∀ x ∈ T, χ r₀ x = ψ x :=
    eigen_support hχ hψ (by rw [Pi.basisFun_repr, hv_coord r₀]; exact hr₀)
  have hchar : ∀ r, (g : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K)
      r (Sum.inl c) ≠ 0 → ∀ x ∈ T, χ r x = ψ x := by
    intro r hr x hx
    exact eigen_support hχ hψ (by rw [Pi.basisFun_repr, hv_coord r]; exact hr) x hx
  have hχinr : ∀ (j : Fin 2) (x : GL (LargeEvenMinusIdx m) K),
      x ∈ T → χ (Sum.inr j) x = 1 := by
    intro j x hx
    obtain ⟨u, -, rfl⟩ := (mem_primeTorusGL K m).mp hx
    change ((torusGL K m u : GL (LargeEvenMinusIdx m) K) :
      Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) (Sum.inr j) (Sum.inr j) = 1
    exact torusGL_apply_inr u j
  have hr₀inl : ∃ d, r₀ = Sum.inl d := by
    rcases r₀ with d | j
    · exact ⟨d, rfl⟩
    · obtain ⟨x, hxT, hx1⟩ := hψne
      have h1 := hchar₀ x hxT
      have h2 := hχinr j x hxT
      exact absurd (by rw [← h1, h2]) hx1
  obtain ⟨d₀, hd₀⟩ := hr₀inl
  refine ⟨d₀, fun r hr => ?_⟩
  have hchar_r := hchar r hr
  rcases r with d | j
  · by_contra hdd
    have hdd' : d ≠ d₀ := fun h => hdd (by rw [h])
    obtain ⟨x, hxT, hxne⟩ := exists_torus_char_ne (p := p) (m := m)
      (d₁ := d) (d₂ := d₀) hp2 hζ hdd'
    refine hxne ?_
    have h1 : χ (Sum.inl d) x = χ (Sum.inl d₀) x := by
      rw [hchar_r x hxT]
      rw [hd₀] at hchar₀
      exact (hchar₀ x hxT).symm
    simpa [χ] using h1
  · obtain ⟨x, hxT, hx1⟩ := hψne
    have h2 := hχinr j x hxT
    have h3 := hchar_r x hxT
    exact absurd (by rw [← h3, h2]) hx1

theorem column_inl_normalizer {ζ : Kˣ} (hp2 : p ≠ 2) (hζ : orderOf ζ = p)
    {g : GL (LargeEvenMinusIdx m) K}
    (hn : ∀ e ∈ primeTorusGL K m p, g * e * g⁻¹ ∈ primeTorusGL K m p)
    (c : Fin m ⊕ Fin m) :
    ∃ d : Fin m ⊕ Fin m, ∃ a : K, a ≠ 0 ∧
      (g : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) *ᵥ basisVec (Sum.inl c) =
        a • basisVec (Sum.inl d) := by
  classical
  obtain ⟨d, hsupp⟩ := support_inl_of_normalizes (p := p) (m := m) hp2 hζ hn c
  let a : K := (g : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) (Sum.inl d) (Sum.inl c)
  have ha : a ≠ 0 := by
    intro h0
    have hzero : (g : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) *ᵥ
        basisVec (Sum.inl c) = 0 := by
      funext r
      rw [basisVec, Matrix.mulVec_single_one]
      by_cases hr : r = Sum.inl d
      · subst hr
        simp [a, h0]
      · have hz : (g : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K)
            r (Sum.inl c) = 0 := by
          by_contra hne
          exact hr (hsupp r hne)
        simp [hz, hr]
    exact column_ne_zero (K := K) (m := m) g (Sum.inl c) hzero
  refine ⟨d, a, ha, ?_⟩
  funext r
  rw [basisVec, Matrix.mulVec_single_one]
  by_cases hr : r = Sum.inl d
  · subst hr
    simp [a, basisVec]
  · have hz : (g : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K)
        r (Sum.inl c) = 0 := by
      by_contra hne
      exact hr (hsupp r hne)
    simp [hz, hr, basisVec]

theorem pairOf_sigma_eq_of_isometry {b c : K} {g : GL (LargeEvenMinusIdx m) K}
    (hg : g ∈ LargeEvenOrthGroup (LargeEvenQMinus m b c))
    (hn : ∀ e ∈ primeTorusGL K m p, g * e * g⁻¹ ∈ primeTorusGL K m p)
    {σ : Fin m ⊕ Fin m → Fin m ⊕ Fin m}
    (hσ : ∀ c, ∃ a : K, a ≠ 0 ∧
      (g : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) *ᵥ basisVec (Sum.inl c) =
        a • basisVec (Sum.inl (σ c)))
    (hσinj : Function.Injective σ) (i : Fin m) :
    pairOf (σ (Sum.inl i)) = pairOf (σ (Sum.inr i)) := by
  obtain ⟨a, ha, hv_a⟩ := hσ (Sum.inl i)
  obtain ⟨d, hd, hv_d⟩ := hσ (Sum.inr i)
  have hv : (g : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) *ᵥ
      (basisVec (Sum.inl (Sum.inl i)) + basisVec (Sum.inl (Sum.inr i))) =
      a • basisVec (Sum.inl (σ (Sum.inl i))) +
        d • basisVec (Sum.inl (σ (Sum.inr i))) := by
    rw [Matrix.mulVec_add, hv_a, hv_d]
  have hiso := isometry_of_mem_largeEvenOrthGroup
    (Q := LargeEvenQMinus m b c) hg
    (basisVec (Sum.inl (Sum.inl i)) + basisVec (Sum.inl (Sum.inr i)))
  rw [hv] at hiso
  have hQv : LargeEvenQMinus m b c
      (basisVec (Sum.inl (Sum.inl i)) + basisVec (Sum.inl (Sum.inr i))) = 1 := by
    simpa [one_smul] using largeEvenQMinus_basisVec_pair b c i (1 : K) (1 : K)
  rw [hQv] at hiso
  have hne : LargeEvenQMinus m b c
      (a • basisVec (Sum.inl (σ (Sum.inl i))) +
        d • basisVec (Sum.inl (σ (Sum.inr i)))) ≠ 0 := by
    rw [hiso]
    exact one_ne_zero
  rcases largeEvenQMinus_basisVec_pair_ne_zero ha hd hne with ⟨j, hp, hq⟩ | ⟨j, hp, hq⟩
  · rw [hp, hq]
    rfl
  · rw [hp, hq]
    rfl

theorem sigma_injective_of_column {g : GL (LargeEvenMinusIdx m) K}
    {σ : Fin m ⊕ Fin m → Fin m ⊕ Fin m}
    (hσ : ∀ c, ∃ a : K, a ≠ 0 ∧
      (g : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) *ᵥ basisVec (K := K) (m := m) (Sum.inl c) =
        a • basisVec (Sum.inl (σ c))) :
    Function.Injective σ := by
  intro c₁ c₂ h
  obtain ⟨a₁, ha₁, hv₁⟩ := hσ c₁
  obtain ⟨a₂, ha₂, hv₂⟩ := hσ c₂
  rw [h] at hv₁
  by_contra hne
  have hlin : a₂ • basisVec (K := K) (m := m) (Sum.inl c₁) = a₁ • basisVec (K := K) (m := m) (Sum.inl c₂) := by
    have h2 : a₂ • ((g : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) *ᵥ
        basisVec (K := K) (m := m) (Sum.inl c₁)) =
        a₁ • ((g : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) *ᵥ
          basisVec (K := K) (m := m) (Sum.inl c₂)) := by
      rw [hv₁, hv₂]
      simp [smul_smul, mul_comm]
    have h3 := congrArg (fun v => ((g⁻¹ : GL (LargeEvenMinusIdx m) K) :
      Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) *ᵥ v) h2
    simpa [Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel g,
      Units.val_one, Matrix.one_mulVec] using h3
  have hentry := congrFun hlin (Sum.inl c₁)
  have hne' : (Sum.inl c₁ : LargeEvenMinusIdx m) ≠ Sum.inl c₂ :=
    fun hh => hne (Sum.inl_injective hh)
  simp [basisVec, hne'] at hentry
  exact ha₂ hentry

theorem pi_surjective_of_pair {σ : Fin m ⊕ Fin m → Fin m ⊕ Fin m}
    (hσsurj : Function.Surjective σ)
    (hpair : ∀ i : Fin m, pairOf (σ (Sum.inl i)) = pairOf (σ (Sum.inr i))) :
    Function.Surjective (fun i : Fin m => pairOf (σ (Sum.inl i))) := by
  intro j
  obtain ⟨c, hc⟩ := hσsurj (Sum.inl j)
  rcases c with k | k
  · refine ⟨k, ?_⟩
    change pairOf (σ (Sum.inl k)) = j
    rw [hc]
    rfl
  · refine ⟨k, ?_⟩
    change pairOf (σ (Sum.inl k)) = j
    calc pairOf (σ (Sum.inl k)) = pairOf (σ (Sum.inr k)) := hpair k
      _ = pairOf (Sum.inl j) := by rw [hc]
      _ = j := rfl

theorem conj_torusGL_of_mem_normalizer {b c : K} {ζ : Kˣ} (hp2 : p ≠ 2)
    (hζ : orderOf ζ = p) {g : GL (LargeEvenMinusIdx m) K}
    (hg : g ∈ LargeEvenOrthGroup (LargeEvenQMinus m b c))
    (hn : ∀ e ∈ primeTorusGL K m p, g * e * g⁻¹ ∈ primeTorusGL K m p) :
    ∃ (π : Equiv.Perm (Fin m)) (ε : Fin m → ℤ),
      (∀ i, ε i = 1 ∨ ε i = -1) ∧
      ∀ x : Fin m → Kˣ, x ^ p = 1 →
        g * torusGL K m x * g⁻¹ =
          torusGL K m (fun i => x (π.symm i) ^ ε (π.symm i)) := by
  classical
  let σ : Fin m ⊕ Fin m → Fin m ⊕ Fin m := fun c =>
    Classical.choose (column_inl_normalizer (p := p) (m := m) hp2 hζ hn c)
  have hσ : ∀ c, ∃ a : K, a ≠ 0 ∧
      (g : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) *ᵥ
        basisVec (Sum.inl c) = a • basisVec (Sum.inl (σ c)) := fun c =>
    Classical.choose_spec (column_inl_normalizer (p := p) (m := m) hp2 hζ hn c)
  have hσinj : Function.Injective σ := sigma_injective_of_column hσ
  have hσsurj : Function.Surjective σ := Finite.injective_iff_surjective.mp hσinj
  have hpair : ∀ i : Fin m, pairOf (σ (Sum.inl i)) = pairOf (σ (Sum.inr i)) :=
    fun i => pairOf_sigma_eq_of_isometry hg hn hσ hσinj i
  let πfun : Fin m → Fin m := fun i => pairOf (σ (Sum.inl i))
  have hπsurj : Function.Surjective πfun := pi_surjective_of_pair hσsurj hpair
  have hπinj : Function.Injective πfun := Finite.injective_iff_surjective.mpr hπsurj
  let π : Equiv.Perm (Fin m) := Equiv.ofBijective πfun (Finite.injective_iff_bijective.mp hπinj)
  have hπ_apply (i : Fin m) : π i = pairOf (σ (Sum.inl i)) := by
    change (Equiv.ofBijective πfun (Finite.injective_iff_bijective.mp hπinj)) i =
      pairOf (σ (Sum.inl i))
    rw [Equiv.ofBijective_apply]
  let ε : Fin m → ℤ := fun i => if σ (Sum.inl i) = Sum.inl (π i) then 1 else -1
  refine ⟨π, ε, ?_, ?_⟩
  · intro i
    by_cases h : σ (Sum.inl i) = Sum.inl (π i)
    · simp [ε, h]
    · simp [ε, h]
  · intro x hxpow
    let t : GL (LargeEvenMinusIdx m) K := torusGL K m x
    let d : GL (LargeEvenMinusIdx m) K := g * t * g⁻¹
    have htT : t ∈ primeTorusGL K m p := torusGL_mem_primeTorusGL hxpow
    have hdT : d ∈ primeTorusGL K m p := hn t htT
    obtain ⟨y, hy, hd_eq⟩ := (mem_primeTorusGL K m).mp hdT
    have hd_entry : ∀ c : Fin m ⊕ Fin m,
        ((d : GL (LargeEvenMinusIdx m) K) :
          Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K)
          (Sum.inl (σ c)) (Sum.inl (σ c)) =
        ((t : GL (LargeEvenMinusIdx m) K) :
          Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K)
          (Sum.inl c) (Sum.inl c) := by
      intro c
      obtain ⟨a, ha, hv⟩ := hσ c
      have hdt : ((d : GL (LargeEvenMinusIdx m) K) :
          Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) *ᵥ
          ((g : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) *ᵥ
            basisVec (Sum.inl c)) =
          (g : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) *ᵥ
            (((t : GL (LargeEvenMinusIdx m) K) :
              Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) *ᵥ
              basisVec (Sum.inl c)) := by
        have hdg : d * g = g * t := by
          dsimp [d]
          group
        rw [Matrix.mulVec_mulVec]
        rw [← Units.val_mul, hdg, Units.val_mul]
        rw [← Matrix.mulVec_mulVec]
      have ht_diag : ((t : GL (LargeEvenMinusIdx m) K) :
          Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) *ᵥ
          basisVec (Sum.inl c) =
          (((t : GL (LargeEvenMinusIdx m) K) :
            Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K)
            (Sum.inl c) (Sum.inl c)) • basisVec (Sum.inl c) := by
        simpa [basisVec] using primeTorus_mulVec_single htT (Sum.inl c)
      have h1 : ((d : GL (LargeEvenMinusIdx m) K) :
          Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) *ᵥ
          ((g : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) *ᵥ
            basisVec (Sum.inl c)) =
          (((t : GL (LargeEvenMinusIdx m) K) :
            Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K)
            (Sum.inl c) (Sum.inl c)) •
            ((g : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) *ᵥ
              basisVec (Sum.inl c)) := by
        rw [hdt]
        rw [ht_diag, Matrix.mulVec_smul]
      rw [hv, Matrix.mulVec_smul] at h1
      have hd_diag : ((d : GL (LargeEvenMinusIdx m) K) :
          Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) *ᵥ
          basisVec (Sum.inl (σ c)) =
          (((d : GL (LargeEvenMinusIdx m) K) :
            Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K)
            (Sum.inl (σ c)) (Sum.inl (σ c))) • basisVec (Sum.inl (σ c)) := by
        simpa [basisVec] using primeTorus_mulVec_single hdT (Sum.inl (σ c))
      rw [hd_diag] at h1
      simp only [smul_smul, mul_comm, mul_left_comm, mul_assoc] at h1
      have h2 := congrFun h1 (Sum.inl (σ c))
      simp [basisVec, Pi.smul_apply, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] at h2
      exact mul_left_cancel₀ ha (by simpa [mul_comm] using h2)
    have hy_eq : y = fun j => x (π.symm j) ^ ε (π.symm j) := by
      funext j
      let i : Fin m := π.symm j
      have hπi : π i = j := by
        simp [i]
      have hpair_i : pairOf (σ (Sum.inl i)) = j := by
        rw [← hπ_apply i, hπi]
      by_cases hσx : σ (Sum.inl i) = (Sum.inl j : Fin m ⊕ Fin m)
      · have hε : ε i = 1 := by simp [ε, hσx, hπi]
        have hdval : ((d : GL (LargeEvenMinusIdx m) K) :
            Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K)
            (Sum.inl (Sum.inl j)) (Sum.inl (Sum.inl j)) = x i := by
          rw [← hσx, hd_entry (Sum.inl i), torusGL_apply_inl_inl]
        have hyval : y j = x i := by
          apply Units.ext
          rw [show (y j : K) = ((torusGL K m y : GL (LargeEvenMinusIdx m) K) :
              Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K)
              (Sum.inl (Sum.inl j)) (Sum.inl (Sum.inl j)) from
            (torusGL_apply_inl_inl y j).symm]
          rw [hd_eq, hdval]
        simpa [i, hε] using hyval
      · have hσx' : σ (Sum.inl i) = Sum.inr j := by
          rcases h : σ (Sum.inl i) with p | p
          · have hpj : p = j := by simpa [h, pairOf] using hpair_i
            exact absurd (by rw [h, hpj]) hσx
          · have hpj : p = j := by simpa [h, pairOf] using hpair_i
            exact congrArg Sum.inr hpj
        have hε : ε i = -1 := by simp [ε, hσx', hπi]
        have hdval : ((d : GL (LargeEvenMinusIdx m) K) :
            Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K)
            (Sum.inl (Sum.inr j)) (Sum.inl (Sum.inr j)) = x i := by
          rw [← hσx', hd_entry (Sum.inl i), torusGL_apply_inl_inl]
        have hyval : (y j)⁻¹ = x i := by
          apply Units.ext
          rw [Units.val_inv_eq_inv_val]
          rw [show ((↑(y j))⁻¹ : K) = ((torusGL K m y : GL (LargeEvenMinusIdx m) K) :
              Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K)
              (Sum.inl (Sum.inr j)) (Sum.inl (Sum.inr j)) from
            (torusGL_apply_inl_inr y j).symm]
          rw [hd_eq, hdval]
        have hyval' : y j = (x i)⁻¹ := inv_eq_iff_eq_inv.mp hyval
        simpa [i, hε] using hyval'
    change d = torusGL K m (fun i => x (π.symm i) ^ ε (π.symm i))
    rw [← hd_eq, hy_eq]

end RelDMinus

end CFSG.StandardType
