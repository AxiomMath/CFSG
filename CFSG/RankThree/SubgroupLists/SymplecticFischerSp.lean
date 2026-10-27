module

public import CFSG.RankThree.SubgroupLists.SymplecticFischerOrth
public import CFSG.Fischer.Classification.Recognition.CaseSp
public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalSymplecticSix

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Open CFSG.Fischer.Classification CFSG.ComponentClassification.PresentationLocal

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace SpFischer

open CFSG.Fischer.Classification.Recognition.SpU.Sp (b_symm exists_b_eq_one eq_one_of_ne_zero_zmod2
  add_self_zmod2)

variable {n : ℕ} {b : LinearMap.BilinForm (ZMod 2) (Fin n → ZMod 2)}

theorem exists_ne_zero_forall_eq_zero {k : ℕ} (hk : k < n) (w : Fin k → Fin n → ZMod 2) :
    ∃ x : Fin n → ZMod 2, x ≠ 0 ∧ ∀ i, b x (w i) = 0 := by
  have hcard : Fintype.card (Fin k → ZMod 2) < Fintype.card (Fin n → ZMod 2) := by
    simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card]
    exact Nat.pow_lt_pow_right (by norm_num) hk
  obtain ⟨x, y, hxy, h⟩ := Fintype.exists_ne_map_eq_of_card_lt (fun x i => b x (w i)) hcard
  refine ⟨x - y, sub_ne_zero.2 hxy, fun i => ?_⟩
  rw [LinearMap.BilinForm.sub_left, sub_eq_zero]
  exact congrFun h i

variable (halt : ∀ x, b x x = 0) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)

include hnd in
theorem eq_of_sympTransvectionGL_eq {v w : Fin n → ZMod 2} (hv : v ≠ 0)
    (h : sympTransvectionGL b halt v = sympTransvectionGL b halt w) : v = w := by
  obtain ⟨y, hy⟩ := exists_b_eq_one halt hnd hv
  have e := congrArg (fun g : GL (Fin n) (ZMod 2) => (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ y) h
  simp only [sympTransvectionGL_mulVec, hy, one_smul] at e
  have e' : v = b y w • w := add_left_cancel e
  rcases eq_or_ne (b y w) 0 with h0 | h1
  · rw [h0, zero_smul] at e'
    exact absurd e' hv
  · rwa [eq_one_of_ne_zero_zmod2 h1, one_smul] at e'

theorem sympTransvectionGL_commute {v w : Fin n → ZMod 2} (hvw : b v w = 0) :
    sympTransvectionGL b halt v * sympTransvectionGL b halt w =
      sympTransvectionGL b halt w * sympTransvectionGL b halt v := by
  have hwv : b w v = 0 := by rw [b_symm halt]; exact hvw
  refine Units.ext (Matrix.ext_of_mulVec_single fun i => ?_)
  rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    sympTransvectionGL_mulVec, sympTransvectionGL_mulVec, sympTransvectionGL_mulVec,
    sympTransvectionGL_mulVec]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hvw, hwv,
    mul_zero, add_zero]
  abel

include halt hnd in
theorem exists_isotropic_triple (hn : 6 ≤ n) :
    ∃ u₁ u₂ u₃ : Fin n → ZMod 2, b u₁ u₂ = 0 ∧ b u₁ u₃ = 0 ∧ b u₂ u₃ = 0 ∧
      ∀ a c d : ZMod 2, a • u₁ + c • u₂ + d • u₃ = 0 → a = 0 ∧ c = 0 ∧ d = 0 := by
  have hs := b_symm halt
  set u₁ : Fin n → ZMod 2 := Pi.single ⟨0, by omega⟩ 1
  have hu₁ : u₁ ≠ 0 := fun h => by simpa [u₁] using congrFun h ⟨0, by omega⟩
  obtain ⟨w₁, hw₁⟩ := exists_b_eq_one halt hnd hu₁
  obtain ⟨u₂, hu₂, h₂⟩ := exists_ne_zero_forall_eq_zero (b := b) (k := 2) (by omega) ![u₁, w₁]
  obtain ⟨w₂, hw₂⟩ := exists_b_eq_one halt hnd hu₂
  obtain ⟨u₃, hu₃, h₃⟩ :=
    exists_ne_zero_forall_eq_zero (b := b) (k := 4) (by omega) ![u₁, w₁, u₂, w₂]
  have h21 : b u₂ u₁ = 0 := h₂ 0
  have h2w : b u₂ w₁ = 0 := h₂ 1
  have h31 : b u₃ u₁ = 0 := h₃ 0
  have h3w : b u₃ w₁ = 0 := h₃ 1
  have h32 : b u₃ u₂ = 0 := h₃ 2
  have h3w' : b u₃ w₂ = 0 := h₃ 3
  have h1w : b u₁ w₁ = 1 := by rw [hs]; exact hw₁
  have h2w' : b u₂ w₂ = 1 := by rw [hs]; exact hw₂
  refine ⟨u₁, u₂, u₃, by rw [hs]; exact h21, by rw [hs]; exact h31, by rw [hs]; exact h32,
    fun a c d h => ?_⟩
  have e₁ := congrArg (fun x => b x w₁) h
  have e₂ := congrArg (fun x => b x w₂) h
  simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, h1w, h2w, h3w,
    LinearMap.BilinForm.zero_left, mul_zero, mul_one, add_zero] at e₁
  subst e₁
  simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, h2w', h3w',
    LinearMap.BilinForm.zero_left, zero_mul, mul_zero, mul_one, zero_add, add_zero] at e₂
  subst e₂
  simp only [zero_smul, zero_add] at h
  exact ⟨rfl, rfl, (smul_eq_zero.1 h).resolve_right hu₃⟩

section Four

omit halt hnd

variable {b : LinearMap.BilinForm (ZMod 2) (Fin 4 → ZMod 2)}

theorem exists_antidiag_basis (halt : ∀ x, b x x = 0) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) :
    ∃ e : Fin 4 → Fin 4 → ZMod 2, ∀ i j, b (e i) (e j) = antidiagGram i j := by
  have hs := b_symm halt
  set u₁ : Fin 4 → ZMod 2 := Pi.single 0 1
  have hu₁ : u₁ ≠ 0 := fun h => by simpa [u₁] using congrFun h 0
  obtain ⟨w₁, hw₁⟩ := exists_b_eq_one halt hnd hu₁
  obtain ⟨u₂, hu₂, h₂⟩ := exists_ne_zero_forall_eq_zero (b := b) (k := 2) (by norm_num) ![u₁, w₁]
  have h21 : b u₂ u₁ = 0 := h₂ 0
  have h2w : b u₂ w₁ = 0 := h₂ 1
  obtain ⟨w₂, hw₂⟩ := exists_b_eq_one halt hnd hu₂
  set w₂' := w₂ + b w₂ w₁ • u₁ + b w₂ u₁ • w₁ with hw₂'
  have a11 : b u₁ u₁ = 0 := halt u₁
  have a12 : b u₁ u₂ = 0 := by rw [hs]; exact h21
  have a14 : b u₁ w₁ = 1 := by rw [hs]; exact hw₁
  have a22 : b u₂ u₂ = 0 := halt u₂
  have a44 : b w₁ w₁ = 0 := halt w₁
  have a42 : b w₁ u₂ = 0 := by rw [hs]; exact h2w
  have a31 : b w₂' u₁ = 0 := by
    simp only [hw₂', LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, a11, hw₁,
      mul_zero, add_zero, mul_one, add_self_zmod2]
  have a34 : b w₂' w₁ = 0 := by
    simp only [hw₂', LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, a14, a44,
      mul_zero, add_zero, mul_one, add_self_zmod2]
  have a32 : b w₂' u₂ = 1 := by
    simp only [hw₂', LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, a12, a42, hw₂,
      mul_zero, add_zero]
  have a33 : b w₂' w₂' = 0 := halt w₂'
  have a13 : b u₁ w₂' = 0 := by rw [hs]; exact a31
  have a43 : b w₁ w₂' = 0 := by rw [hs]; exact a34
  have a23 : b u₂ w₂' = 1 := by rw [hs]; exact a32
  refine ⟨![u₁, u₂, w₂', w₁], fun i j => ?_⟩
  fin_cases i <;> fin_cases j <;>
    simp [antidiagGram, a11, a12, a13, a14, h21, a22, a23, h2w, a31, a32, a33, a34, hw₁, a42, a43,
      a44]

@[expose] def basisMat (e : Fin 4 → Fin 4 → ZMod 2) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  Matrix.of fun k i => e i k

theorem basisMat_mulVec (e : Fin 4 → Fin 4 → ZMod 2) (x : Fin 4 → ZMod 2) :
    basisMat e *ᵥ x = ∑ i, x i • e i := by
  ext k
  simp [basisMat, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem b_basisMat {e : Fin 4 → Fin 4 → ZMod 2} (he : ∀ i j, b (e i) (e j) = antidiagGram i j)
    (x y : Fin 4 → ZMod 2) :
    b (basisMat e *ᵥ x) (basisMat e *ᵥ y) = x ⬝ᵥ (antidiagGram *ᵥ y) := by
  rw [basisMat_mulVec, basisMat_mulVec]
  simp only [Fin.sum_univ_four, LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
    LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, he, dotProduct, Matrix.mulVec]
  ring

theorem basisMat_mulVec_injective {e : Fin 4 → Fin 4 → ZMod 2}
    (he : ∀ i j, b (e i) (e j) = antidiagGram i j) : Function.Injective (basisMat e).mulVec := by
  intro x y hxy
  have key : ∀ z, x ⬝ᵥ (antidiagGram *ᵥ z) = y ⬝ᵥ (antidiagGram *ᵥ z) := fun z => by
    rw [← b_basisMat he, ← b_basisMat he, hxy]
  funext i
  have := key (Pi.single (Fin.rev i) 1)
  fin_cases i <;> simpa [Matrix.mulVec, dotProduct, antidiagGram, Fin.sum_univ_four] using this

theorem dotProduct_transpose_mul_mulVec (M J : Matrix (Fin 4) (Fin 4) (ZMod 2))
    (x y : Fin 4 → ZMod 2) : x ⬝ᵥ ((Mᵀ * J * M) *ᵥ y) = (M *ᵥ x) ⬝ᵥ (J *ᵥ (M *ᵥ y)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

theorem matrix_eq_of_dotProduct {A B : Matrix (Fin 4) (Fin 4) (ZMod 2)}
    (h : ∀ x y, x ⬝ᵥ (A *ᵥ y) = x ⬝ᵥ (B *ᵥ y)) : A = B := by
  ext i j
  simpa [Matrix.mulVec_single_one, single_one_dotProduct] using
    h (Pi.single i 1) (Pi.single j 1)

theorem conj_mem_sympFour_iff {e : Fin 4 → Fin 4 → ZMod 2}
    (he : ∀ i j, b (e i) (e j) = antidiagGram i j) {P : GL (Fin 4) (ZMod 2)}
    (hP : (P : Matrix (Fin 4) (Fin 4) (ZMod 2)) = basisMat e) (g : GL (Fin 4) (ZMod 2)) :
    P⁻¹ * g * P ∈ sympFour ↔
      ∀ x y, b ((g : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x)
        ((g : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ y) = b x y := by
  have hb : ∀ x y, b ((P : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x)
      ((P : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ y) = x ⬝ᵥ (antidiagGram *ᵥ y) := by
    rw [hP]
    exact b_basisMat he
  have hPM : ∀ x, (P : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
      (((P⁻¹ * g * P : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x) =
        (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ ((P : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x) := by
    intro x
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
    congr 2
    group
  have hPPi : ∀ x, (P : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
      (((P⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x) = x := by
    intro x
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  rw [mem_sympFour_iff]
  constructor
  · intro h u v
    obtain ⟨x, rfl⟩ : ∃ x, (P : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x = u := ⟨_, hPPi u⟩
    obtain ⟨y, rfl⟩ : ∃ y, (P : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ y = v := ⟨_, hPPi v⟩
    rw [← hPM, ← hPM, hb, hb, ← dotProduct_transpose_mul_mulVec, h]
  · intro h
    refine matrix_eq_of_dotProduct fun x y => ?_
    rw [dotProduct_transpose_mul_mulVec, ← hb, hPM, hPM, h, hb]

theorem not_isPerfect_sp4 (halt : ∀ x, b x x = 0) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) :
    ¬ Group.IsPerfect (fischerMatrixGroup fun A : Matrix (Fin 4) (Fin 4) (ZMod 2) =>
      ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y) := by
  intro hPf
  obtain ⟨e, he⟩ := exists_antidiag_basis halt hnd
  have hu : IsUnit (basisMat e) :=
    Matrix.mulVec_injective_iff_isUnit.1 (basisMat_mulVec_injective he)
  set H := fischerMatrixGroup fun A : Matrix (Fin 4) (Fin 4) (ZMod 2) =>
    ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y
  have hmem : ∀ g, g ∈ H ↔ hu.unit⁻¹ * g * hu.unit ∈ sympFour := fun g => by
    rw [conj_mem_sympFour_iff he hu.unit_spec g]
    exact mem_fischerMatrixGroup_bilin_iff b g
  let ψ : H →* sympFour :=
    ((MulAut.conj hu.unit⁻¹).toMonoidHom.comp H.subtype).codRestrict sympFour fun g => by
      simpa [MulAut.conj_apply] using (hmem g).1 g.2
  have hψ : Function.Surjective ψ := by
    intro h
    refine ⟨⟨hu.unit * h * hu.unit⁻¹, (hmem _).2 (by simp [mul_assoc])⟩,
      Subtype.ext ?_⟩
    simp [ψ, mul_assoc]
  have := hPf
  have h1 := eq_one_of_isPerfect (Group.IsPerfect.ofSurjective hψ)
    (Equiv.Perm.sign.comp omegaPerm) rootInvolutionA
  rw [MonoidHom.comp_apply, omegaPerm_rootInvolutionA, Equiv.Perm.sign_swap (by decide)] at h1
  exact absurd h1 (by decide)

end Four

theorem cliqueCoeff_spec :
    Function.Injective (![(1, 0, 0), (0, 1, 0), (0, 0, 1), (1, 1, 0), (1, 0, 1), (0, 1, 1)] :
      Fin 6 → ZMod 2 × ZMod 2 × ZMod 2) ∧
    ∀ i, (![(1, 0, 0), (0, 1, 0), (0, 0, 1), (1, 1, 0), (1, 0, 1), (0, 1, 1)] :
      Fin 6 → ZMod 2 × ZMod 2 × ZMod 2) i ≠ 0 := by
  decide

end SpFischer

open SpFischer

theorem fischerSpClique : FischerSpClique := by
  intro m hm b halt hnd hP
  rcases Nat.lt_or_ge m 3 with h3 | h3
  · obtain rfl : m = 2 := by omega
    exact (not_isPerfect_sp4 halt hnd hP).elim
  obtain ⟨u₁, u₂, u₃, h12, h13, h23, hind⟩ :=
    exists_isotropic_triple (n := 2 * m) halt hnd (by omega)
  have hs := CFSG.Fischer.Classification.Recognition.SpU.Sp.b_symm halt
  obtain ⟨hcinj, hc0⟩ := cliqueCoeff_spec
  set c : Fin 6 → ZMod 2 × ZMod 2 × ZMod 2 :=
    ![(1, 0, 0), (0, 1, 0), (0, 0, 1), (1, 1, 0), (1, 0, 1), (0, 1, 1)] with hcdef
  set x : Fin 6 → Fin (2 * m) → ZMod 2 :=
    fun i => (c i).1 • u₁ + (c i).2.1 • u₂ + (c i).2.2 • u₃ with hxdef
  have hx0 : ∀ i, x i ≠ 0 := fun i h => by
    obtain ⟨h1, h2, h3⟩ := hind _ _ _ h
    exact hc0 i (Prod.ext h1 (Prod.ext h2 h3))
  have hxinj : Function.Injective x := fun i j h => by
    have h' : ((c i).1 - (c j).1) • u₁ + ((c i).2.1 - (c j).2.1) • u₂ +
        ((c i).2.2 - (c j).2.2) • u₃ = 0 := by
      have := sub_eq_zero.2 h
      simp only [hxdef] at this
      rw [← this]
      module
    obtain ⟨h1, h2, h3⟩ := hind _ _ _ h'
    exact hcinj (Prod.ext (sub_eq_zero.1 h1) (Prod.ext (sub_eq_zero.1 h2) (sub_eq_zero.1 h3)))
  have h21 : b u₂ u₁ = 0 := by rw [hs]; exact h12
  have h31 : b u₃ u₁ = 0 := by rw [hs]; exact h13
  have h32 : b u₃ u₂ = 0 := by rw [hs]; exact h23
  have hxorth : ∀ i j, b (x i) (x j) = 0 := fun i j => by
    simp only [hxdef, LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, halt, h12, h13, h23, h21,
      h31, h32, mul_zero, add_zero]
  refine ⟨fun i => ⟨sympTransvectionGL b halt (x i), sympTransvectionGL_mem_fischerMatrixGroup _⟩,
    fun i j h => hxinj (eq_of_sympTransvectionGL_eq halt hnd (hx0 i) (congrArg Subtype.val h)),
    fun i => sympTransvectionGL_mem_fischerTransvections (hx0 i),
    fun i j => Subtype.ext (sympTransvectionGL_commute halt (hxorth i j))⟩

theorem fischerSpCard : FischerSpCard := by
  intro m hm b halt hnd hP
  rcases Nat.lt_or_ge m 3 with h3 | h3
  · obtain rfl : m = 2 := by omega
    exact (not_isPerfect_sp4 halt hnd hP).elim
  let F : {v : Fin (2 * m) → ZMod 2 // v ≠ 0} →
      {g : fischerMatrixGroup (fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y) //
        (g : GL (Fin (2 * m)) (ZMod 2)) ∈ fischerTransvections (fun x y => b x y) fun v => v ≠ 0} :=
    fun v => ⟨⟨sympTransvectionGL b halt v, sympTransvectionGL_mem_fischerMatrixGroup _⟩,
      sympTransvectionGL_mem_fischerTransvections v.2⟩
  have hF : Function.Injective F := fun v w h => Subtype.ext (eq_of_sympTransvectionGL_eq halt hnd
    v.2 (congrArg (fun g => (g.1 : GL (Fin (2 * m)) (ZMod 2))) h))
  have hle := Nat.card_le_card_of_injective F hF
  have hcard : Nat.card {v : Fin (2 * m) → ZMod 2 // v ≠ 0} = 2 ^ (2 * m) - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq]
    simp [ZMod.card]
  have h64 : 2 ^ 6 ≤ 2 ^ (2 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

end CFSG.RankThree.SubgroupLists
