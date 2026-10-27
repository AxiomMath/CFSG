module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.RankThree.GF2n.Smith81

open Matrix

section Alg

variable {F : Type} [Field F]

@[expose] def planeAdd (u : Fin 2 → F) : AddSubgroup (Matrix (Fin 2) (Fin 2) F) where
  carrier := {X | ∃ n : Fin 2 → F, X = Matrix.vecMulVec n u}
  add_mem' := by
    rintro _ _ ⟨n, rfl⟩ ⟨n', rfl⟩
    exact ⟨n + n', (Matrix.add_vecMulVec n n' u).symm⟩
  zero_mem' := ⟨0, (Matrix.zero_vecMulVec u).symm⟩
  neg_mem' := by
    rintro _ ⟨n, rfl⟩
    exact ⟨-n, (Matrix.neg_vecMulVec n u).symm⟩

theorem mem_planeAdd {u : Fin 2 → F} {X : Matrix (Fin 2) (Fin 2) F} :
    X ∈ planeAdd u ↔ ∃ n : Fin 2 → F, X = Matrix.vecMulVec n u := Iff.rfl

theorem vecMulVec_mem_planeAdd (n u : Fin 2 → F) : Matrix.vecMulVec n u ∈ planeAdd u :=
  ⟨n, rfl⟩

theorem vecMulVec_left_injective {u : Fin 2 → F} (hu : u ≠ 0) :
    Function.Injective fun n : Fin 2 → F => Matrix.vecMulVec n u := by
  intro n n' h
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hu
  funext i
  have h' : n i * u j = n' i * u j := congrFun (congrFun h i) j
  exact mul_right_cancel₀ hj h'

@[expose] noncomputable def planeEquiv {u : Fin 2 → F} (hu : u ≠ 0) :
    (Fin 2 → F) ≃+ planeAdd u :=
  AddEquiv.ofBijective
    (AddMonoidHom.mk' (fun n => ⟨Matrix.vecMulVec n u, n, rfl⟩)
      fun n n' => Subtype.ext (Matrix.add_vecMulVec n n' u))
    ⟨fun n n' h => vecMulVec_left_injective hu (congrArg Subtype.val h), fun X => by
      obtain ⟨n, hn⟩ := mem_planeAdd.mp X.2
      exact ⟨n, Subtype.ext hn.symm⟩⟩

theorem coe_planeEquiv {u : Fin 2 → F} (hu : u ≠ 0) (n : Fin 2 → F) :
    ((planeEquiv hu n : planeAdd u) : Matrix (Fin 2) (Fin 2) F) = Matrix.vecMulVec n u := rfl

theorem card_planeAdd [Finite F] {u : Fin 2 → F} (hu : u ≠ 0) :
    Nat.card (planeAdd u) = Nat.card F ^ 2 := by
  rw [← Nat.card_congr (planeEquiv hu).toEquiv, Nat.card_fun, Nat.card_fin]

theorem planeAdd_smul {u : Fin 2 → F} {c : F} (hc : c ≠ 0) : planeAdd (c • u) = planeAdd u := by
  ext X
  simp only [mem_planeAdd]
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨c • n, by rw [Matrix.vecMulVec_smul, Matrix.smul_vecMulVec]⟩
  · rintro ⟨n, rfl⟩
    refine ⟨c⁻¹ • n, ?_⟩
    rw [Matrix.vecMulVec_smul, Matrix.smul_vecMulVec, smul_smul, mul_inv_cancel₀ hc, one_smul]

theorem det_ne_zero_of_ne_smul {u u' : Fin 2 → F} (hu : u ≠ 0) (hne : ∀ c : F, u' ≠ c • u) :
    u 0 * u' 1 - u 1 * u' 0 ≠ 0 := by
  intro hd
  by_cases h0 : u 0 = 0
  · have h1 : u 1 ≠ 0 := fun h1 => hu (by ext k; fin_cases k <;> simp [h0, h1])
    have h0' : u' 0 = 0 := by
      have h2 : u 1 * u' 0 = 0 := by rw [h0] at hd; linear_combination -hd
      exact (mul_eq_zero.mp h2).resolve_left h1
    apply hne (u' 1 / u 1)
    ext k
    fin_cases k
    · simp [h0, h0']
    · simp [div_mul_cancel₀ _ h1]
  · apply hne (u' 0 / u 0)
    ext k
    fin_cases k
    · simp [div_mul_cancel₀ _ h0]
    · simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply, smul_eq_mul]
      rw [div_mul_eq_mul_div, eq_div_iff h0]
      linear_combination hd

theorem vecMulVec_eq_smul_iff {a b n u : Fin 2 → F} {c : F} (ha : a ≠ 0) (hb : b ≠ 0)
    (hn : n ≠ 0) (hu : u ≠ 0) (hc : c ≠ 0)
    (h : Matrix.vecMulVec a b = c • Matrix.vecMulVec n u) :
    ∃ α β : F, a = α • n ∧ b = β • u ∧ α * β = c := by
  have he : ∀ i k, a i * b k = c * (n i * u k) := fun i k => by
    simpa [Matrix.vecMulVec_apply] using congrFun (congrFun h i) k
  obtain ⟨k₀, hk₀⟩ := Function.ne_iff.mp hb
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hn
  have hk₀' : b k₀ ≠ 0 := hk₀
  have hi₀' : n i₀ ≠ 0 := hi₀
  obtain ⟨α, hα⟩ : ∃ α : F, a = α • n := by
    refine ⟨c * u k₀ / b k₀, funext fun i => ?_⟩
    rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hk₀']
    linear_combination he i k₀
  have hα0 : α ≠ 0 := by
    rintro rfl
    exact ha (by rw [hα, zero_smul])
  refine ⟨α, c / α, hα, funext fun k => ?_, mul_div_cancel₀ c hα0⟩
  have hk := he i₀ k
  rw [hα, Pi.smul_apply, smul_eq_mul] at hk
  rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hα0]
  apply mul_left_cancel₀ hi₀'
  linear_combination hk

theorem exists_smul_of_ne_zero_mem_planeAdd {u u' : Fin 2 → F} (hu : u ≠ 0) (hu' : u' ≠ 0)
    {X : Matrix (Fin 2) (Fin 2) F} (hX : X ≠ 0) (h1 : X ∈ planeAdd u) (h2 : X ∈ planeAdd u') :
    ∃ c : F, c ≠ 0 ∧ u' = c • u := by
  obtain ⟨n, rfl⟩ := h1
  obtain ⟨n', hn'⟩ := h2
  have hn : n ≠ 0 := by
    rintro rfl
    exact hX (Matrix.zero_vecMulVec u)
  have hn'0 : n' ≠ 0 := by
    rintro rfl
    exact hX (by rw [hn', Matrix.zero_vecMulVec])
  obtain ⟨α, β, -, hβ, hαβ⟩ := vecMulVec_eq_smul_iff hn'0 hu' hn hu one_ne_zero
    (by rw [one_smul, hn'])
  exact ⟨β, right_ne_zero_of_mul_eq_one hαβ, hβ⟩

theorem planeAdd_inf {u u' : Fin 2 → F} (hu : u ≠ 0) (hu' : u' ≠ 0) (hne : ∀ c : F, u' ≠ c • u) :
    planeAdd u ⊓ planeAdd u' = ⊥ := by
  rw [eq_bot_iff]
  intro X hX
  rw [AddSubgroup.mem_bot]
  by_contra hX0
  obtain ⟨c, -, hc⟩ := exists_smul_of_ne_zero_mem_planeAdd hu hu' hX0
    (AddSubgroup.mem_inf.mp hX).1 (AddSubgroup.mem_inf.mp hX).2
  exact hne c hc

theorem planeAdd_sup {u u' : Fin 2 → F} (hu : u ≠ 0) (hu' : u' ≠ 0) (hne : ∀ c : F, u' ≠ c • u) :
    planeAdd u ⊔ planeAdd u' = ⊤ := by
  have hd := det_ne_zero_of_ne_smul hu hne
  rw [eq_top_iff]
  intro X _
  have hX : X = Matrix.vecMulVec (fun i => (X i 0 * u' 1 - X i 1 * u' 0) /
      (u 0 * u' 1 - u 1 * u' 0)) u + Matrix.vecMulVec (fun i => (u 0 * X i 1 - u 1 * X i 0) /
      (u 0 * u' 1 - u 1 * u' 0)) u' := by
    ext i j
    simp only [Matrix.add_apply, Matrix.vecMulVec_apply]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hd]
    fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue]
      ring
    · simp only [Fin.mk_one, Fin.isValue]
      ring
  rw [hX]
  exact add_mem (AddSubgroup.mem_sup_left ⟨_, rfl⟩) (AddSubgroup.mem_sup_right ⟨_, rfl⟩)

theorem det_eq_zero_of_mem_planeAdd {u : Fin 2 → F} {X : Matrix (Fin 2) (Fin 2) F}
    (hX : X ∈ planeAdd u) : X.det = 0 := by
  obtain ⟨n, rfl⟩ := hX
  exact Matrix.det_vecMulVec n u

theorem det_add_of_mem_planeAdd {u : Fin 2 → F} {X Y : Matrix (Fin 2) (Fin 2) F}
    (hX : X ∈ planeAdd u) (hY : Y ∈ planeAdd u) : (X + Y).det = X.det + Y.det := by
  rw [det_eq_zero_of_mem_planeAdd (add_mem hX hY), det_eq_zero_of_mem_planeAdd hX,
    det_eq_zero_of_mem_planeAdd hY, add_zero]

theorem det_vecMulVec_add (n u n' u' : Fin 2 → F) :
    (Matrix.vecMulVec n u + Matrix.vecMulVec n' u').det =
      (n 0 * n' 1 - n 1 * n' 0) * (u 0 * u' 1 - u 1 * u' 0) := by
  rw [Matrix.det_fin_two]
  simp only [Matrix.add_apply, Matrix.vecMulVec_apply]
  ring

theorem mul_mem_planeAdd {u : Fin 2 → F} {X : Matrix (Fin 2) (Fin 2) F} (hX : X ∈ planeAdd u)
    (g : Matrix (Fin 2) (Fin 2) F) : g * X ∈ planeAdd u := by
  obtain ⟨n, rfl⟩ := hX
  exact ⟨g *ᵥ n, Matrix.mul_vecMulVec g n u⟩

theorem smul_mem_planeAdd {u : Fin 2 → F} {X : Matrix (Fin 2) (Fin 2) F} (hX : X ∈ planeAdd u)
    (c : F) : c • X ∈ planeAdd u := by
  obtain ⟨n, rfl⟩ := hX
  exact ⟨c • n, (Matrix.smul_vecMulVec c n u).symm⟩

theorem mul_mem_planeAdd_vecMul {u : Fin 2 → F} {X : Matrix (Fin 2) (Fin 2) F}
    (hX : X ∈ planeAdd u) (H : Matrix (Fin 2) (Fin 2) F) : X * H ∈ planeAdd (u ᵥ* H) := by
  obtain ⟨n, rfl⟩ := hX
  exact ⟨n, Matrix.vecMulVec_mul n u H⟩

theorem mul_mul_mem_planeAdd_iff {P H : Matrix (Fin 2) (Fin 2) F} (hP : IsUnit P.det)
    (hH : IsUnit H.det) {u : Fin 2 → F} {X : Matrix (Fin 2) (Fin 2) F} :
    P * X * H ∈ planeAdd (u ᵥ* H) ↔ X ∈ planeAdd u := by
  refine ⟨fun h => ?_, fun h => mul_mem_planeAdd_vecMul (mul_mem_planeAdd h P) H⟩
  have h' := mul_mem_planeAdd_vecMul (mul_mem_planeAdd h P⁻¹) H⁻¹
  have e1 : P⁻¹ * (P * X * H) * H⁻¹ = X := by
    rw [← mul_assoc, ← mul_assoc, Matrix.nonsing_inv_mul _ hP, one_mul, mul_assoc,
      Matrix.mul_nonsing_inv _ hH, mul_one]
  have e2 : u ᵥ* H ᵥ* H⁻¹ = u := by
    rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hH, Matrix.vecMul_one]
  rwa [e1, e2] at h'

theorem exists_vecMulVec_of_det_eq_zero {X : Matrix (Fin 2) (Fin 2) F} (hX : X ≠ 0)
    (hd : X.det = 0) : ∃ n u : Fin 2 → F, n ≠ 0 ∧ u ≠ 0 ∧ X = Matrix.vecMulVec n u := by
  by_cases h0 : X 0 = 0
  · have h1 : X 1 ≠ 0 := by
      intro h1
      apply hX
      ext i j
      fin_cases i
      · exact congrFun h0 j
      · exact congrFun h1 j
    refine ⟨![0, 1], X 1, fun h => by simpa using congrFun h 1, h1, ?_⟩
    ext i j
    fin_cases i
    · simpa [Matrix.vecMulVec_apply] using congrFun h0 j
    · simp [Matrix.vecMulVec_apply]
  · obtain ⟨c, hc⟩ : ∃ c : F, X 1 = c • X 0 := by
      by_contra hcon
      push Not at hcon
      exact det_ne_zero_of_ne_smul h0 hcon (by rw [Matrix.det_fin_two] at hd; exact hd)
    refine ⟨![1, c], X 0, fun h => by simpa using congrFun h 0, h0, ?_⟩
    ext i j
    fin_cases i
    · simp [Matrix.vecMulVec_apply]
    · simpa [Matrix.vecMulVec_apply] using congrFun hc j

theorem forall_of_forall_det_eq_one {p : Matrix (Fin 2) (Fin 2) F → Prop}
    (hSL : ∀ g : Matrix (Fin 2) (Fin 2) F, g.det = 1 → p g)
    (hsub : ∀ A B, p A → p B → p (A - B)) (hmul : ∀ A B, p A → p B → p (A * B))
    (A : Matrix (Fin 2) (Fin 2) F) : p A := by
  have h1 : p 1 := hSL 1 Matrix.det_one
  have h0 : p 0 := by simpa using hsub 1 1 h1 h1
  have hadd : ∀ A B, p A → p B → p (A + B) := fun A B hA hB => by
    simpa using hsub A (0 - B) hA (hsub 0 B h0 hB)
  have h01 : ∀ t : F, p !![0, t; 0, 0] := fun t => by
    have := hsub _ _ (hSL !![1, t; 0, 1] (by simp [Matrix.det_fin_two_of])) h1
    convert this using 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have h10 : ∀ t : F, p !![0, 0; t, 0] := fun t => by
    have := hsub _ _ (hSL !![1, 0; t, 1] (by simp [Matrix.det_fin_two_of])) h1
    convert this using 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have h00 : ∀ t : F, p !![t, 0; 0, 0] := fun t => by
    convert hmul _ _ (h01 t) (h10 1) using 1
    simp [Matrix.mul_fin_two]
  have h11 : ∀ t : F, p !![0, 0; 0, t] := fun t => by
    convert hmul _ _ (h10 t) (h01 1) using 1
    simp [Matrix.mul_fin_two]
  have hA : A = !![A 0 0, 0; 0, 0] + !![0, A 0 1; 0, 0] + !![0, 0; A 1 0, 0] +
      !![0, 0; 0, A 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [hA]
  exact hadd _ _ (hadd _ _ (hadd _ _ (h00 _) (h01 _)) (h10 _)) (h11 _)

theorem schur_right (T : Matrix (Fin 2) (Fin 2) F →+ Matrix (Fin 2) (Fin 2) F)
    (hT : ∀ g : Matrix (Fin 2) (Fin 2) F, g.det = 1 → ∀ X, T (g * X) = g * T X) :
    ∃ H : Matrix (Fin 2) (Fin 2) F, ∀ X, T X = X * H := by
  have hall : ∀ A X : Matrix (Fin 2) (Fin 2) F, T (A * X) = A * T X :=
    forall_of_forall_det_eq_one (p := fun A => ∀ X, T (A * X) = A * T X) hT
      (fun A B hA hB X => by rw [sub_mul, sub_mul, map_sub, hA, hB])
      (fun A B hA hB X => by simp only [mul_assoc]; rw [hA, hB])
  exact ⟨T 1, fun X => by rw [← hall X 1, mul_one]⟩

theorem exists_mul_mul_of_intertwine (T : Matrix (Fin 2) (Fin 2) F →+ Matrix (Fin 2) (Fin 2) F)
    (hbij : Function.Bijective T)
    (hlin : ∀ (c : F) (X : Matrix (Fin 2) (Fin 2) F), T (c • X) = c • T X)
    (hT : ∀ g : Matrix (Fin 2) (Fin 2) F, g.det = 1 →
      ∃ g' : Matrix (Fin 2) (Fin 2) F, ∀ X, T (g * X) = g' * T X) :
    ∃ P H : Matrix (Fin 2) (Fin 2) F, IsUnit P.det ∧ IsUnit H.det ∧ ∀ X, T X = P * X * H := by
  have hall : ∀ A : Matrix (Fin 2) (Fin 2) F, ∃ A' : Matrix (Fin 2) (Fin 2) F,
      ∀ X, T (A * X) = A' * T X :=
    forall_of_forall_det_eq_one (p := fun A => ∃ A', ∀ X, T (A * X) = A' * T X) hT
      (fun A B ⟨A', hA⟩ ⟨B', hB⟩ =>
        ⟨A' - B', fun X => by rw [sub_mul, sub_mul, map_sub, hA, hB]⟩)
      (fun A B ⟨A', hA⟩ ⟨B', hB⟩ =>
        ⟨A' * B', fun X => by simp only [mul_assoc]; rw [hA, hB]⟩)
  let L : Fin 2 → (Fin 2 → F) →ₗ[F] (Fin 2 → F) := fun j =>
    { toFun := fun x i => T (Matrix.vecMulVec x (Pi.single 0 1)) i j
      map_add' := fun x y => by
        funext i
        simp only [Matrix.add_vecMulVec, map_add, Matrix.add_apply, Pi.add_apply]
      map_smul' := fun c x => by
        funext i
        simp only [Matrix.smul_vecMulVec, hlin, Matrix.smul_apply, Pi.smul_apply,
          RingHom.id_apply] }
  let P : Fin 2 → Matrix (Fin 2) (Fin 2) F := fun j => LinearMap.toMatrix' (L j)
  have hP : ∀ j x, P j *ᵥ x = fun i => T (Matrix.vecMulVec x (Pi.single 0 1)) i j :=
    fun j x => LinearMap.toMatrix'_mulVec (L j) x
  have hPA : ∀ j (A A' : Matrix (Fin 2) (Fin 2) F), (∀ X, T (A * X) = A' * T X) →
      P j * A = A' * P j := by
    intro j A A' hA
    refine Matrix.ext_of_mulVec_single fun k => ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hP, hP, ← Matrix.mul_vecMulVec, hA]
    funext i
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have hker : ∀ j, (P j).det = 0 → P j = 0 := by
    intro j hj
    obtain ⟨v, hv, hPv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hj
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hv
    have hk' : v k ≠ 0 := hk
    refine Matrix.ext_of_mulVec_single fun l => ?_
    obtain ⟨A', hA'⟩ := hall (Matrix.vecMulVec (Pi.single l 1) (Pi.single k (v k)⁻¹))
    have hAv : Matrix.vecMulVec (Pi.single l 1) (Pi.single k (v k)⁻¹) *ᵥ v = Pi.single l 1 := by
      rw [Matrix.vecMulVec_mulVec, single_dotProduct, inv_mul_cancel₀ hk']
      simp
    rw [← hAv, Matrix.mulVec_mulVec, hPA j _ A' hA', ← Matrix.mulVec_mulVec, hPv,
      Matrix.mulVec_zero, Matrix.zero_mulVec]
  obtain ⟨j, hj⟩ : ∃ j, (P j).det ≠ 0 := by
    by_contra h
    push Not at h
    have h0 : T (Matrix.vecMulVec (Pi.single 0 1) (Pi.single 0 1)) = 0 := by
      ext a b
      have := congrFun (hP b (Pi.single 0 1)) a
      rw [hker b (h b), Matrix.zero_mulVec] at this
      simpa using this.symm
    have h1 : Matrix.vecMulVec (Pi.single 0 1 : Fin 2 → F) (Pi.single 0 1 : Fin 2 → F) = 0 :=
      hbij.1 (h0.trans (map_zero T).symm)
    have := congrFun (congrFun h1 0) 0
    simp [Matrix.vecMulVec_apply] at this
  have hPu : IsUnit (P j).det := isUnit_iff_ne_zero.mpr hj
  obtain ⟨H, hH⟩ := schur_right ((AddMonoidHom.mulLeft (P j)⁻¹).comp T) fun g hg X => by
    obtain ⟨g', hg'⟩ := hT g hg
    have hPg := hPA j g g' hg'
    have hconj : (P j)⁻¹ * g' = g * (P j)⁻¹ := by
      calc (P j)⁻¹ * g' = (P j)⁻¹ * (g' * P j) * (P j)⁻¹ := by
              rw [mul_assoc, mul_assoc, Matrix.mul_nonsing_inv _ hPu, mul_one]
        _ = g * (P j)⁻¹ := by
              rw [← hPg, ← mul_assoc, Matrix.nonsing_inv_mul _ hPu, one_mul]
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulLeft]
    rw [hg', ← mul_assoc (P j)⁻¹ g', hconj, mul_assoc]
  have hTX : ∀ X, T X = P j * X * H := fun X => by
    have := hH X
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulLeft] at this
    calc T X = P j * ((P j)⁻¹ * T X) := by
          rw [← mul_assoc, Matrix.mul_nonsing_inv _ hPu, one_mul]
      _ = P j * X * H := by rw [this, mul_assoc]
  refine ⟨P j, H, hPu, ?_, hTX⟩
  obtain ⟨X₀, hX₀⟩ := hbij.2 1
  have := congrArg Matrix.det ((hTX X₀).symm.trans hX₀)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_one] at this
  exact IsUnit.of_mul_eq_one_right _ this

theorem eq_planeAdd_of_card [Finite F] (Y : AddSubgroup (Matrix (Fin 2) (Fin 2) F))
    (hY : ∀ g : Matrix (Fin 2) (Fin 2) F, g.det = 1 → ∀ X ∈ Y, g * X ∈ Y)
    (hcard : Nat.card Y = Nat.card F ^ 2) : ∃ u : Fin 2 → F, u ≠ 0 ∧ Y = planeAdd u := by
  have hall : ∀ A : Matrix (Fin 2) (Fin 2) F, ∀ X ∈ Y, A * X ∈ Y :=
    forall_of_forall_det_eq_one (p := fun A => ∀ X ∈ Y, A * X ∈ Y) hY
      (fun A B hA hB X hX => by rw [sub_mul]; exact sub_mem (hA X hX) (hB X hX))
      (fun A B hA hB X hX => by rw [mul_assoc]; exact hA _ (hB X hX))
  obtain ⟨X, hXY, hX0⟩ : ∃ X ∈ Y, X ≠ 0 := by
    rcases Y.bot_or_exists_ne_zero with h | h
    · exfalso
      rw [h, AddSubgroup.card_bot] at hcard
      have h1 : 1 < Nat.card F := Finite.one_lt_card
      have h2 : 1 < Nat.card F ^ 2 := Nat.one_lt_pow two_ne_zero h1
      exact absurd hcard (ne_of_lt h2)
    · exact h
  obtain ⟨i, hi⟩ : ∃ i, X i ≠ 0 := by
    by_contra h
    push Not at h
    exact hX0 (Matrix.ext fun a b => congrFun (h a) b)
  refine ⟨X i, hi, (AddSubgroup.eq_of_le_of_card_ge ?_ ?_).symm⟩
  · rintro _ ⟨n, rfl⟩
    have : Matrix.vecMulVec n (X i) = Matrix.vecMulVec n (Pi.single i 1) * X := by
      rw [Matrix.vecMulVec_mul, Matrix.single_one_vecMul]
      rfl
    rw [this]
    exact hall _ X hXY
  · rw [hcard, card_planeAdd hi]

theorem ne_of_torus_relations [CharP F 2] {γ μ μ' δ : F} (hγ : γ ≠ 0) (hμ : μ ≠ 0)
    (hμ' : μ' ≠ 0) (hdet : δ = μ * μ') (hδ : δ ≠ 1) (hV : δ * (γ * μ) = 1)
    (hD : μ = γ ∨ γ * μ' = 1) : μ ≠ μ' := by
  intro hμμ
  rw [← hμμ] at hdet hD
  rcases hD with h | h
  ·
    rw [← h, hdet] at hV
    rw [hdet] at hδ
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    have h4 : (μ + 1) ^ 4 = 0 := by
      linear_combination (2 * μ ^ 3 + 3 * μ ^ 2 + 2 * μ + 1) * h2 + hV
    have h1 : μ + 1 = 0 := (pow_eq_zero_iff (by norm_num)).mp h4
    have hμ1 : μ = 1 := by linear_combination h1 - h2
    exact hδ (by rw [hμ1, one_mul])
  · rw [h, mul_one] at hV
    exact hδ hV

end Alg

end CFSG.RankThree.GF2n.Smith81
