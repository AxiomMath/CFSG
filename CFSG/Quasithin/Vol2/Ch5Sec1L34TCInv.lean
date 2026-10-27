module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34E9

public section

namespace CFSG.Quasithin.H13.TorusComm

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourOuter
open CFSG.Quasithin.H13.KGL34P
open scoped Pointwise

variable {k : Type} [Field k]

theorem coe_slConj_diagGL (x : kˣ) (g : SpecialLinearGroup (Fin 3) k) (i j : Fin 3) :
    ((CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 k (diagGL x) g :
      SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) i j =
      ![(x : k), 1, 1] i * (g : Matrix (Fin 3) (Fin 3) k) i j * ![((x⁻¹ : kˣ) : k), 1, 1] j := by
  rw [coe_slConjugation, coe_diagGL, coe_diagGL_inv, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem diagGL_slConj_mem_upper (x : kˣ) {g : SpecialLinearGroup (Fin 3) k}
    (hg : g ∈ upperTriangular 3 k) :
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 k (diagGL x) g ∈
      upperTriangular 3 k := fun i j hij => by
  rw [coe_slConj_diagGL, hg i j hij, mul_zero, zero_mul]

theorem conjAut_diagGL_mem_projUnitriangular (x : kˣ) {u : projectiveSL 3 k}
    (hu : u ∈ projUnitriangular 3 k) :
    LinearFlag.conjAut 3 k (diagGL x) u ∈ projUnitriangular 3 k := by
  obtain ⟨g, hg, rfl⟩ := hu
  rw [conjAut_proj]
  refine ⟨_, ⟨diagGL_slConj_mem_upper x hg.1, fun i => ?_⟩, rfl⟩
  rw [coe_slConj_diagGL, hg.2 i, mul_one]
  fin_cases i <;> simp

theorem conjAut_diagGL_mem_projUpper (x : kˣ) {u : projectiveSL 3 k}
    (hu : u ∈ projUpperTriangular 3 k) :
    LinearFlag.conjAut 3 k (diagGL x) u ∈ projUpperTriangular 3 k := by
  obtain ⟨g, hg, rfl⟩ := hu
  rw [conjAut_proj]
  exact ⟨_, diagGL_slConj_mem_upper x hg, rfl⟩

theorem unit_conj_div (x : kˣ) (a b : k) : (x : k) * a * ((x⁻¹ : kˣ) : k) * b⁻¹ = a * b⁻¹ := by
  rw [mul_comm (x : k) a, mul_assoc a, Units.mul_inv, mul_one]

theorem chiP_conjAut_diagGL (x : kˣ) (u : projUpperTriangular 3 k) :
    chiP (⟨LinearFlag.conjAut 3 k (diagGL x) u, conjAut_diagGL_mem_projUpper x u.2⟩ :
      projUpperTriangular 3 k) = chiP u := by
  obtain ⟨g, rfl⟩ := projB_surjective u
  have he : (⟨LinearFlag.conjAut 3 k (diagGL x) (projB g),
      conjAut_diagGL_mem_projUpper x (projB g).2⟩ :
      projUpperTriangular 3 k) = projB ⟨_, diagGL_slConj_mem_upper x g.2⟩ := by
    apply Subtype.ext
    show LinearFlag.conjAut 3 k (diagGL x) (proj 3 k (g : SpecialLinearGroup (Fin 3) k)) = _
    rw [conjAut_proj]
    rfl
  rw [he, chiP_projB, chiP_projB]
  apply Units.ext
  rw [val_chiB, val_chiB, coe_slConj_diagGL, coe_slConj_diagGL]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
    mul_one, one_mul]
  exact unit_conj_div x _ _

theorem fieldAut_map_mem_upper (σ : k ≃+* k) {g : SpecialLinearGroup (Fin 3) k}
    (hg : g ∈ upperTriangular 3 k) :
    SpecialLinearGroup.map σ.toRingHom g ∈ upperTriangular 3 k := fun i j hij => by
  rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    hg i j hij, map_zero]

theorem fieldAut_mem_projUnitriangular (σ : k ≃+* k) {u : projectiveSL 3 k}
    (hu : u ∈ projUnitriangular 3 k) : fieldAut 3 k σ u ∈ projUnitriangular 3 k := by
  obtain ⟨g, hg, rfl⟩ := hu
  rw [fieldAut_proj]
  refine ⟨_, ⟨fieldAut_map_mem_upper σ hg.1, fun i => ?_⟩, rfl⟩
  rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, hg.2 i,
    map_one]

theorem fieldAut_mem_projUpper (σ : k ≃+* k) {u : projectiveSL 3 k}
    (hu : u ∈ projUpperTriangular 3 k) : fieldAut 3 k σ u ∈ projUpperTriangular 3 k := by
  obtain ⟨g, hg, rfl⟩ := hu
  rw [fieldAut_proj]
  exact ⟨_, fieldAut_map_mem_upper σ hg, rfl⟩

theorem chiP_fieldAut {σ : k ≃+* k} (hσ : ∀ a, σ a = a ^ 2) (u : projUpperTriangular 3 k) :
    chiP (⟨fieldAut 3 k σ u, fieldAut_mem_projUpper σ u.2⟩ : projUpperTriangular 3 k) =
      chiP u ^ 2 := by
  obtain ⟨g, rfl⟩ := projB_surjective u
  have he : (⟨fieldAut 3 k σ (projB g), fieldAut_mem_projUpper σ (projB g).2⟩ :
      projUpperTriangular 3 k) = projB ⟨_, fieldAut_map_mem_upper σ g.2⟩ := by
    apply Subtype.ext
    show fieldAut 3 k σ (proj 3 k (g : SpecialLinearGroup (Fin 3) k)) = _
    rw [fieldAut_proj]
    rfl
  rw [he, chiP_projB, chiP_projB]
  apply Units.ext
  rw [val_chiB, Units.val_pow_eq_pow_val, val_chiB]
  simp only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hσ]
  ring

@[expose] noncomputable def gam : MulAut (projectiveSL 3 k) :=
  LinearFlag.conjAut 3 k w0GL * dualAut 3 k

theorem gam_proj (h : SpecialLinearGroup (Fin 3) k) :
    gam (proj 3 k h) = proj 3 k
      (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 k w0GL
        (h⁻¹).transpose) := by
  simp only [gam, MulAut.mul_apply, dualAut_proj, conjAut_proj]

theorem gam_matrix (h : SpecialLinearGroup (Fin 3) k) (i j : Fin 3) :
    ((CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 k w0GL
        (h⁻¹).transpose : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) i j =
      ((h⁻¹ : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) (Fin.rev j)
        (Fin.rev i) := by
  rw [coe_slConjugation]
  have hw : ((w0GL⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) = w0M := rfl
  rw [hw]
  show (((w0M : Matrix (Fin 3) (Fin 3) k) * _ * (w0M : Matrix (Fin 3) (Fin 3) k)) :
    Matrix (Fin 3) (Fin 3) k) i j = _
  rw [w0M_conj_apply, SpecialLinearGroup.coe_transpose, Matrix.transpose_apply]

theorem gam_upper {h : SpecialLinearGroup (Fin 3) k} (hh : h ∈ upperTriangular 3 k) :
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 k w0GL
      (h⁻¹).transpose ∈ upperTriangular 3 k := by
  intro i j hij
  have hU := coe_inv_isUpperTriangular (mem_upperTriangular_iff_isUpperTriangular.mp hh)
  rw [gam_matrix]
  exact hU (Fin.rev_lt_rev.mpr hij)

theorem gam_unitriangular {h : SpecialLinearGroup (Fin 3) k} (hh : h ∈ unitriangular 3 k) :
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 k w0GL
      (h⁻¹).transpose ∈ unitriangular 3 k := by
  refine ⟨gam_upper (unitriangular_le_upperTriangular 3 k hh), fun i => ?_⟩
  rw [gam_matrix]
  exact ((unitriangular 3 k).inv_mem hh).2 _

theorem gam_mem_projUnitriangular {x : projectiveSL 3 k} (hx : x ∈ projUnitriangular 3 k) :
    gam x ∈ projUnitriangular 3 k := by
  obtain ⟨h, hh, rfl⟩ := hx
  rw [gam_proj]
  exact ⟨_, gam_unitriangular hh, rfl⟩

theorem inverseTranspose_w0GL :
    GeneralLinearGroup.inverseTranspose (w0GL : GL (Fin 3) k) = w0GL := by
  refine Units.ext ?_
  rw [GeneralLinearGroup.coe_inverseTranspose]
  show (w0M : Matrix (Fin 3) (Fin 3) k)ᵀ = w0M
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem dualAut_mul_conjAut (B : GL (Fin 3) k) :
    dualAut 3 k * LinearFlag.conjAut 3 k B =
      LinearFlag.conjAut 3 k (GeneralLinearGroup.inverseTranspose B) * dualAut 3 k := by
  have h := dualAut_pow_mul_conjAut (1 : ZMod 2) B
  have ht : twistD (1 : ZMod 2) B = GeneralLinearGroup.inverseTranspose B := by simp [twistD]
  rwa [val_one_two, pow_one, ht] at h

theorem gam_mul_conjAut (B : GL (Fin 3) k) :
    gam * LinearFlag.conjAut 3 k B =
      LinearFlag.conjAut 3 k (w0GL * GeneralLinearGroup.inverseTranspose B * w0GL⁻¹) * gam := by
  calc gam * LinearFlag.conjAut 3 k B
      = LinearFlag.conjAut 3 k w0GL * (dualAut 3 k * LinearFlag.conjAut 3 k B) := by
        rw [gam, mul_assoc]
    _ = LinearFlag.conjAut 3 k w0GL *
        (LinearFlag.conjAut 3 k (GeneralLinearGroup.inverseTranspose B) * dualAut 3 k) := by
        rw [dualAut_mul_conjAut]
    _ = _ := by
        rw [gam, map_mul, map_mul, map_inv]
        group

theorem gam_mul_self : (gam : MulAut (projectiveSL 3 k)) * gam = 1 := by
  have hw : (w0GL : GL (Fin 3) k) * w0GL = 1 := Units.ext w0M_mul_self
  calc (gam : MulAut (projectiveSL 3 k)) * gam
      = LinearFlag.conjAut 3 k w0GL * (dualAut 3 k * LinearFlag.conjAut 3 k w0GL) *
        dualAut 3 k := by
        rw [gam]
        group
    _ = LinearFlag.conjAut 3 k w0GL * (LinearFlag.conjAut 3 k w0GL * dualAut 3 k) *
        dualAut 3 k := by
        rw [dualAut_mul_conjAut, inverseTranspose_w0GL]
    _ = LinearFlag.conjAut 3 k (w0GL * w0GL) * (dualAut 3 k * dualAut 3 k) := by
        rw [map_mul]
        group
    _ = 1 := by rw [hw, map_one, dualAut_mul_self, one_mul]

theorem cycSL_inv : (cycSL⁻¹ : SpecialLinearGroup (Fin 3) k) = cycSL.transpose := by
  refine (eq_inv_of_mul_eq_one_right ?_).symm
  apply Subtype.ext
  change !![0, 0, 1; 1, 0, 0; 0, 1, 0] * (!![0, 0, 1; 1, 0, 0; 0, 1, 0])ᵀ =
    (1 : Matrix (Fin 3) (Fin 3) k)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem gam_cycSL : gam (proj 3 k cycSL) = (proj 3 k cycSL)⁻¹ := by
  rw [gam_proj, ← map_inv]
  congr 1
  apply Subtype.ext
  ext i j
  rw [gam_matrix, cycSL_inv]
  fin_cases i <;> fin_cases j <;> rfl

theorem mem_normalizer_of_conj_mem {G : Type*} [Group G] {H : Subgroup G} [Finite H] {g : G}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  let f : H → H := fun y => ⟨g * y * g⁻¹, h y y.2⟩
  have hf : Function.Injective f := fun a b hab => Subtype.ext (by
    have h1 : g * (a : G) * g⁻¹ = g * b * g⁻¹ := congrArg Subtype.val hab
    simpa using h1)
  obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.mp hf) ⟨_, hx⟩
  have h1 : g * (y : G) * g⁻¹ = g * x * g⁻¹ := congrArg Subtype.val hy
  have h2 : (y : G) = x := by simpa using h1
  rw [← h2]
  exact y.2

theorem diagGL_inv (x : kˣ) : (diagGL x)⁻¹ = (diagGL x⁻¹ : GL (Fin 3) k) := by
  rw [inv_eq_iff_mul_eq_one, diagGL_mul, mul_inv_cancel, diagGL_one]

theorem decomp_mem_projUpper (x : kˣ) {g : SpecialLinearGroup (Fin 3) k}
    (hg : g ∈ upperTriangular 3 k) {u : projectiveSL 3 k} (hu : u ∈ projUpperTriangular 3 k) :
    (LinearFlag.conjAut 3 k (diagGL x) * MulAut.conj (proj 3 k g)) u ∈
      projUpperTriangular 3 k := by
  have hgB : proj 3 k g ∈ projUpperTriangular 3 k := ⟨g, hg, rfl⟩
  rw [MulAut.mul_apply, MulAut.conj_apply]
  exact conjAut_diagGL_mem_projUpper x ((projUpperTriangular 3 k).mul_mem
    ((projUpperTriangular 3 k).mul_mem hgB hu) ((projUpperTriangular 3 k).inv_mem hgB))

theorem chiP_decomp (x : kˣ) {g : SpecialLinearGroup (Fin 3) k} (hg : g ∈ upperTriangular 3 k)
    (u : projUpperTriangular 3 k) :
    chiP (⟨(LinearFlag.conjAut 3 k (diagGL x) * MulAut.conj (proj 3 k g)) u,
      decomp_mem_projUpper x hg u.2⟩ : projUpperTriangular 3 k) = chiP u := by
  have hgB : proj 3 k g ∈ projUpperTriangular 3 k := ⟨g, hg, rfl⟩
  let gB : projUpperTriangular 3 k := ⟨proj 3 k g, hgB⟩
  have he : (⟨(LinearFlag.conjAut 3 k (diagGL x) * MulAut.conj (proj 3 k g)) u,
      decomp_mem_projUpper x hg u.2⟩ : projUpperTriangular 3 k) =
      ⟨LinearFlag.conjAut 3 k (diagGL x) ((gB * u * gB⁻¹ : projUpperTriangular 3 k) :
        projectiveSL 3 k), conjAut_diagGL_mem_projUpper x (gB * u * gB⁻¹).2⟩ := rfl
  rw [he, chiP_conjAut_diagGL, map_mul, map_mul, map_inv, mul_comm (chiP gB),
    mul_inv_cancel_right]

variable [Finite k] [CharP k 2]

theorem exists_decomp {C : GL (Fin 3) k}
    (hC : ∀ u ∈ projUnitriangular 3 k, LinearFlag.conjAut 3 k C u ∈ projUnitriangular 3 k) :
    ∃ (x : kˣ) (g : SpecialLinearGroup (Fin 3) k), g ∈ upperTriangular 3 k ∧
      LinearFlag.conjAut 3 k C =
        LinearFlag.conjAut 3 k (diagGL x) * MulAut.conj (proj 3 k g) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set x := GeneralLinearGroup.det C with hx
  have hdet : GeneralLinearGroup.det ((diagGL x)⁻¹ * C) = 1 := by
    rw [map_mul, map_inv, det_diagGL, inv_mul_cancel]
  let g₀ : SpecialLinearGroup (Fin 3) k :=
    ⟨(((diagGL x)⁻¹ * C : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k), by
      rw [← GeneralLinearGroup.val_det_apply, hdet, Units.val_one]⟩
  have hg₀ : SpecialLinearGroup.toGL g₀ = (diagGL x)⁻¹ * C := Units.ext rfl
  have hCe : LinearFlag.conjAut 3 k C =
      LinearFlag.conjAut 3 k (diagGL x) * MulAut.conj (proj 3 k g₀) := by
    rw [← conjAut_toGL, hg₀, ← map_mul, mul_inv_cancel_left]
  have hN : proj 3 k g₀ ∈ Subgroup.normalizer (projUnitriangular 3 k : Set (projectiveSL 3 k)) := by
    refine mem_normalizer_of_conj_mem fun u hu => ?_
    have h1 : MulAut.conj (proj 3 k g₀) =
        LinearFlag.conjAut 3 k (diagGL x⁻¹) * LinearFlag.conjAut 3 k C := by
      rw [hCe, ← mul_assoc, ← map_mul, ← diagGL_inv, inv_mul_cancel, map_one, one_mul]
    have h2 : proj 3 k g₀ * u * (proj 3 k g₀)⁻¹ =
        LinearFlag.conjAut 3 k (diagGL x⁻¹) (LinearFlag.conjAut 3 k C u) := by
      rw [← MulAut.conj_apply, h1, MulAut.mul_apply]
    rw [h2]
    exact conjAut_diagGL_mem_projUnitriangular _ (hC u hu)
  rw [normalizer_projUnitriangular 2] at hN
  obtain ⟨g, hg, hgg⟩ := hN
  exact ⟨x, g, hg, by rw [hCe, ← hgg]⟩

omit [CharP k 2] in
theorem exists_inv_of_chiP (hk : Nat.card k = 4) {α : MulAut (projectiveSL 3 k)}
    (hα2 : α * α = 1) {b : projectiveSL 3 k} (hb : b ∈ projUpperTriangular 3 k)
    (hαb : α b ∈ projUpperTriangular 3 k)
    (hχ : chiP (⟨α b, hαb⟩ : projUpperTriangular 3 k) = chiP ⟨b, hb⟩ ^ 2)
    (hb1 : chiP (⟨b, hb⟩ : projUpperTriangular 3 k) ≠ 1) :
    ∃ y : projectiveSL 3 k, orderOf y = 3 ∧ α y = y⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set z := α b * b⁻¹ with hz
  have hzB : z ∈ projUpperTriangular 3 k :=
    (projUpperTriangular 3 k).mul_mem hαb ((projUpperTriangular 3 k).inv_mem hb)
  have hχz : chiP (⟨z, hzB⟩ : projUpperTriangular 3 k) = chiP ⟨b, hb⟩ := by
    have e : (⟨z, hzB⟩ : projUpperTriangular 3 k) =
        ⟨α b, hαb⟩ * (⟨b, hb⟩ : projUpperTriangular 3 k)⁻¹ := rfl
    rw [e, map_mul, map_inv, hχ, sq, mul_inv_cancel_right]
  have hαz : α z = z⁻¹ := by
    have h2 : α (α b) = b := by
      rw [← MulAut.mul_apply, hα2, MulAut.one_apply]
    rw [hz, map_mul, map_inv, h2, _root_.mul_inv_rev, inv_inv]
  have hm0 : orderOf z ≠ 0 := (orderOf_pos z).ne'
  have h3 : 3 ∣ orderOf z := by
    by_contra h3
    have hcop : Nat.Coprime 3 (orderOf z) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
    have hzpow : (⟨z, hzB⟩ : projUpperTriangular 3 k) ^ orderOf z = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact pow_orderOf_eq_one z)
    have h1 : chiP (⟨z, hzB⟩ : projUpperTriangular 3 k) ^ orderOf z = 1 := by
      rw [← map_pow, hzpow, map_one]
    have h2 : chiP (⟨z, hzB⟩ : projUpperTriangular 3 k) ^ 3 = 1 := unit_pow_three hk _
    have h4 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h1)
    rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff, hχz] at h4
    exact hb1 h4
  refine ⟨z ^ (orderOf z / 3), orderOf_pow_orderOf_div hm0 h3, ?_⟩
  rw [map_pow, hαz, inv_pow]

omit [Finite k] [CharP k 2] in
theorem torusDiag_mem_upper {ω : k} (hω3 : ω ^ 3 = 1) : torusDiag ω hω3 ∈ upperTriangular 3 k := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [coe_torusDiag]

omit [Finite k] in
theorem chiP_torusDiag_ne_one {ω : k} (hω3 : ω ^ 3 = 1) (hω2 : ω ^ 2 + ω + 1 = 0)
    (hb : proj 3 k (torusDiag ω hω3) ∈ projUpperTriangular 3 k) :
    chiP (⟨proj 3 k (torusDiag ω hω3), hb⟩ : projUpperTriangular 3 k) ≠ 1 := by
  have he : (⟨proj 3 k (torusDiag ω hω3), hb⟩ : projUpperTriangular 3 k) =
      projB ⟨torusDiag ω hω3, torusDiag_mem_upper hω3⟩ := rfl
  rw [he, chiP_projB]
  intro h
  have h1 := congrArg Units.val h
  rw [val_chiB, Units.val_one, coe_torusDiag] at h1
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.tail_cons, Matrix.head_cons, one_mul] at h1
  have hω0 : ω ≠ 0 := by
    rintro rfl
    simp at hω3
  have h2 : ω ^ 2 = 1 := by
    have := (inv_eq_one.mp h1)
    exact this
  have h3 : ω = 1 := by
    calc ω = ω ^ 3 * (ω ^ 2)⁻¹ := by field_simp
      _ = 1 := by rw [hω3, h2, inv_one, one_mul]
  rw [h3] at hω2
  have h4 : (1 : k) + 1 = 0 := CharTwo.add_self_eq_zero 1
  have : (1 : k) = 0 := by linear_combination hω2 - h4
  exact one_ne_zero this

omit [Finite k] [CharP k 2] in
theorem orderOf_proj_eq_three {h : SpecialLinearGroup (Fin 3) k} (h3 : h ^ 3 = 1) {i j : Fin 3}
    (hij : i ≠ j) (hne : (h : Matrix (Fin 3) (Fin 3) k) i j ≠ 0) : orderOf (proj 3 k h) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime (by rw [← map_pow, h3, map_one]) ?_
  rw [Ne, proj_eq_one_iff]
  rintro ⟨c, -, hc⟩
  apply hne
  rw [hc, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij]

omit [Finite k] [CharP k 2] in
theorem conj_inv_of_involutions {N N' : SpecialLinearGroup (Fin 3) k} (hN : N * N = 1)
    (hN' : N' * N' = 1) :
    MulAut.conj (proj 3 k N) (proj 3 k (N * N')) = (proj 3 k (N * N'))⁻¹ := by
  have hNi : N⁻¹ = N := (inv_eq_of_mul_eq_one_right hN)
  have hN'i : N'⁻¹ = N' := (inv_eq_of_mul_eq_one_right hN')
  rw [MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul, ← map_inv, _root_.mul_inv_rev, hNi,
    hN'i]
  congr 1
  calc N * (N * N') * N = (N * N) * N' * N := by group
    _ = N' * N := by rw [hN, one_mul]

omit [Finite k] in
theorem fam_one {x y : k} (hx : x ≠ 0) :
    !![1, 0, 0; x⁻¹, 1, 0; 0, 0, 1] * !![1, 0, 0; x⁻¹, 1, 0; 0, 0, 1] =
      (1 : Matrix (Fin 3) (Fin 3) k) ∧
    (!![1, x, y; 0, 1, 0; 0, 0, 1] * !![1, 0, 0; x⁻¹, 1, 0; 0, 0, 1]) *
      ((!![1, x, y; 0, 1, 0; 0, 0, 1] * !![1, 0, 0; x⁻¹, 1, 0; 0, 0, 1]) *
        (!![1, x, y; 0, 1, 0; 0, 0, 1] * !![1, 0, 0; x⁻¹, 1, 0; 0, 0, 1])) =
      (1 : Matrix (Fin 3) (Fin 3) k) := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  constructor
  · simp only [Matrix.mul_fin_three]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    linear_combination x⁻¹ * h2
  · simp only [Matrix.mul_fin_three]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> ring_nf
    · linear_combination 6 * h2
    · linear_combination 4 * x * h2
    · linear_combination 4 * y * h2
    · linear_combination 4 * h2
    · linear_combination 2 * h2
    · linear_combination 2 * y * h2

omit [Finite k] in
theorem fam_two {y z : k} (hz : z ≠ 0) :
    !![1, 0, 0; 0, 1, 0; 0, z⁻¹, 1] * !![1, 0, 0; 0, 1, 0; 0, z⁻¹, 1] =
      (1 : Matrix (Fin 3) (Fin 3) k) ∧
    (!![1, 0, y; 0, 1, z; 0, 0, 1] * !![1, 0, 0; 0, 1, 0; 0, z⁻¹, 1]) *
      ((!![1, 0, y; 0, 1, z; 0, 0, 1] * !![1, 0, 0; 0, 1, 0; 0, z⁻¹, 1]) *
        (!![1, 0, y; 0, 1, z; 0, 0, 1] * !![1, 0, 0; 0, 1, 0; 0, z⁻¹, 1])) =
      (1 : Matrix (Fin 3) (Fin 3) k) := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  constructor
  · simp only [Matrix.mul_fin_three]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    linear_combination z⁻¹ * h2
  · simp only [Matrix.mul_fin_three]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> ring_nf
    · linear_combination 6 * y * h2
    · linear_combination 4 * y * h2
    · linear_combination 6 * h2
    · linear_combination 4 * z * h2
    · linear_combination 4 * h2
    · linear_combination 2 * h2

omit [Finite k] in
theorem fam_three {y : k} (hy : y ≠ 0) :
    !![1, 0, 0; 0, 1, 0; y⁻¹, 0, 1] * !![1, 0, 0; 0, 1, 0; y⁻¹, 0, 1] =
      (1 : Matrix (Fin 3) (Fin 3) k) ∧
    (!![1, 0, y; 0, 1, 0; 0, 0, 1] * !![1, 0, 0; 0, 1, 0; y⁻¹, 0, 1]) *
      ((!![1, 0, y; 0, 1, 0; 0, 0, 1] * !![1, 0, 0; 0, 1, 0; y⁻¹, 0, 1]) *
        (!![1, 0, y; 0, 1, 0; 0, 0, 1] * !![1, 0, 0; 0, 1, 0; y⁻¹, 0, 1])) =
      (1 : Matrix (Fin 3) (Fin 3) k) := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  constructor
  · simp only [Matrix.mul_fin_three]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    linear_combination y⁻¹ * h2
  · simp only [Matrix.mul_fin_three]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> ring_nf
    · linear_combination 6 * h2
    · linear_combination 4 * y * h2
    · linear_combination 4 * h2
    · linear_combination 2 * h2

omit [Finite k] [CharP k 2] in
theorem exists_inv_of_partner {N : SpecialLinearGroup (Fin 3) k} (hNN : N * N = 1)
    {Nm N'm : Matrix (Fin 3) (Fin 3) k} (hNm : (N : Matrix (Fin 3) (Fin 3) k) = Nm)
    (hdet : N'm.det = 1) (h2 : N'm * N'm = 1) (h3 : (Nm * N'm) * ((Nm * N'm) * (Nm * N'm)) = 1)
    {i j : Fin 3} (hij : i ≠ j) (hne : (Nm * N'm) i j ≠ 0) :
    ∃ y : projectiveSL 3 k, orderOf y = 3 ∧ MulAut.conj (proj 3 k N) y = y⁻¹ := by
  obtain ⟨N', hN'⟩ : ∃ N' : SpecialLinearGroup (Fin 3) k,
      (N' : Matrix (Fin 3) (Fin 3) k) = N'm := ⟨⟨N'm, hdet⟩, rfl⟩
  have hN'2 : N' * N' = 1 := by
    apply Subtype.ext
    change (N' : Matrix (Fin 3) (Fin 3) k) * (N' : Matrix (Fin 3) (Fin 3) k) = 1
    rw [hN', h2]
  have hh3 : (N * N') ^ 3 = 1 := by
    rw [pow_three]
    apply Subtype.ext
    change ((N : Matrix (Fin 3) (Fin 3) k) * N') * (((N : Matrix (Fin 3) (Fin 3) k) * N') *
      ((N : Matrix (Fin 3) (Fin 3) k) * N')) = 1
    rw [hNm, hN', h3]
  refine ⟨proj 3 k (N * N'), orderOf_proj_eq_three hh3 hij ?_, conj_inv_of_involutions hNN hN'2⟩
  change ((N : Matrix (Fin 3) (Fin 3) k) * N') i j ≠ 0
  rw [hNm, hN']
  exact hne

omit [Finite k] in
theorem exists_inv_of_unitri {N : SpecialLinearGroup (Fin 3) k} (hN : N ∈ unitriangular 3 k)
    (hNN : N * N = 1) (hN1 : N ≠ 1) :
    ∃ y : projectiveSL 3 k, orderOf y = 3 ∧ MulAut.conj (proj 3 k N) y = y⁻¹ := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  set x := (N : Matrix (Fin 3) (Fin 3) k) 0 1 with hx
  set y := (N : Matrix (Fin 3) (Fin 3) k) 0 2 with hy
  set z := (N : Matrix (Fin 3) (Fin 3) k) 1 2 with hz
  have hNm : (N : Matrix (Fin 3) (Fin 3) k) = !![1, x, y; 0, 1, z; 0, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j
    all_goals first
      | exact hN.2 _
      | exact hN.1 _ _ (by decide)
      | rfl
  have hxz : x * z = 0 := by
    have h : ((N : Matrix (Fin 3) (Fin 3) k) * N) 0 2 = (1 : Matrix (Fin 3) (Fin 3) k) 0 2 :=
      congrArg (fun M : SpecialLinearGroup (Fin 3) k => (M : Matrix (Fin 3) (Fin 3) k) 0 2) hNN
    rw [hNm] at h
    simp [Matrix.mul_apply, Fin.sum_univ_three] at h
    linear_combination h - y * h2
  by_cases hx0 : x = 0
  · by_cases hz0 : z = 0
    · have hy0 : y ≠ 0 := by
        intro hy0
        apply hN1
        apply Subtype.ext
        change (N : Matrix (Fin 3) (Fin 3) k) = 1
        rw [hNm, hx0, hy0, hz0]
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      refine exists_inv_of_partner hNN (by rw [hNm, hx0, hz0])
        (by simp [Matrix.det_fin_three]) (fam_three hy0).1 (fam_three hy0).2
        (i := 2) (j := 0) (by decide) ?_
      simp [Matrix.mul_apply, Fin.sum_univ_three, hy0]
    · refine exists_inv_of_partner hNN (by rw [hNm, hx0])
        (by simp [Matrix.det_fin_three]) (fam_two (y := y) hz0).1 (fam_two (y := y) hz0).2
        (i := 2) (j := 1) (by decide) ?_
      simp [Matrix.mul_apply, Fin.sum_univ_three, hz0]
  · have hz0 : z = 0 := by
      rcases mul_eq_zero.mp hxz with h | h
      · exact absurd h hx0
      · exact h
    refine exists_inv_of_partner hNN (by rw [hNm, hz0])
      (by simp [Matrix.det_fin_three]) (fam_one (y := y) hx0).1 (fam_one (y := y) hx0).2
      (i := 1) (j := 0) (by decide) ?_
    simp [Matrix.mul_apply, Fin.sum_univ_three, hx0]

omit [Finite k] in
theorem exists_unitri_of_upper (hk : Nat.card k = 4) {g : SpecialLinearGroup (Fin 3) k}
    (hg : g ∈ upperTriangular 3 k) (hg2 : g * g ∈ scalars 3 k) :
    ∃ N : SpecialLinearGroup (Fin 3) k, N ∈ unitriangular 3 k ∧ N * N = 1 ∧
      proj 3 k N = proj 3 k g := by
  have hU := mem_upperTriangular_iff_isUpperTriangular.mp hg
  obtain ⟨c, -, hc⟩ := hg2
  have hc' : (g : Matrix (Fin 3) (Fin 3) k) * (g : Matrix (Fin 3) (Fin 3) k) =
      scalar (Fin 3) (c : k) := hc
  have hd : ∀ i, (g : Matrix (Fin 3) (Fin 3) k) i i ^ 2 = c := by
    intro i
    have h := congrFun (congrFun hc' i) i
    rw [mul_apply_self_of_isUpperTriangular hU hU, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq] at h
    rw [sq, h]
  set μ := (g : Matrix (Fin 3) (Fin 3) k) 0 0 with hμ
  have hdiag : ∀ i, (g : Matrix (Fin 3) (Fin 3) k) i i = μ := by
    intro i
    apply frobenius_inj k 2
    rw [frobenius_def, frobenius_def, hd, hμ, hd]
  have hμ0 : μ ≠ 0 := by
    intro h0
    have h := hd 0
    rw [← hμ, h0, zero_pow two_ne_zero] at h
    exact c.ne_zero h.symm
  set μu := Units.mk0 μ hμ0 with hμu
  have hdet : (scalar (Fin 3) ((μu⁻¹ : kˣ) : k)).det = 1 := by
    rw [Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, ← Units.val_pow_eq_pow_val, unit_pow_three hk, Units.val_one]
  obtain ⟨t, ht⟩ : ∃ t : SpecialLinearGroup (Fin 3) k,
      (t : Matrix (Fin 3) (Fin 3) k) = scalar (Fin 3) ((μu⁻¹ : kˣ) : k) := ⟨⟨_, hdet⟩, rfl⟩
  have htZ : t ∈ scalars 3 k := ⟨μu⁻¹, unit_pow_three hk _, ht⟩
  have hNm : ((t * g : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
      scalar (Fin 3) ((μu⁻¹ : kˣ) : k) * (g : Matrix (Fin 3) (Fin 3) k) := by
    change (t : Matrix (Fin 3) (Fin 3) k) * g = _
    rw [ht]
  have hentry : ∀ i j, ((t * g : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) i j =
      ((μu⁻¹ : kˣ) : k) * (g : Matrix (Fin 3) (Fin 3) k) i j := by
    intro i j
    rw [hNm, Matrix.scalar_apply, Matrix.diagonal_mul]
  refine ⟨t * g, ⟨fun i j hij => ?_, fun i => ?_⟩, ?_, ?_⟩
  · rw [hentry, hg i j hij, mul_zero]
  · rw [hentry, hdiag, hμu, Units.val_inv_eq_inv_val, Units.val_mk0, inv_mul_cancel₀ hμ0]
  · apply Subtype.ext
    change ((t * g : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *
      ((t * g : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) = 1
    rw [hNm, mul_assoc, ← mul_assoc (g : Matrix (Fin 3) (Fin 3) k),
      ← (Matrix.scalar_commute ((μu⁻¹ : kˣ) : k) (Commute.all _) (g : Matrix (Fin 3) (Fin 3) k)),
      mul_assoc, hc', ← mul_assoc, ← map_mul, ← map_mul]
    have hc2 : ((μu⁻¹ : kˣ) : k) * ((μu⁻¹ : kˣ) : k) * (c : k) = 1 := by
      have h0 := hd 0
      rw [← hμ] at h0
      rw [← h0, hμu, Units.val_inv_eq_inv_val, Units.val_mk0]
      field_simp
    rw [hc2, map_one]
  · rw [map_mul, proj_eq_one_iff.mpr htZ, one_mul]

omit [Finite k] in
theorem congr_w0 {a b c d d₂ x z : k} (hd2 : d₂ ^ 2 * d = a) (hx : x ^ 2 * a = c)
    (hz : z * a = b * d₂ + x * a) :
    !![1, x * d₂, x * z; 0, d₂, z; 0, 0, 1] * (!![a, b, c; 0, d, b; 0, 0, a] * w0M) *
      (!![1, x * d₂, x * z; 0, d₂, z; 0, 0, 1])ᵀ = a • (w0M : Matrix (Fin 3) (Fin 3) k) := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [w0M, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply]
  · linear_combination x ^ 2 * hd2 + hx + (c + x * d₂ * b + x * z * a) * h2
  · linear_combination x * hd2 + hz + (b * d₂ + x * a) * h2
  · linear_combination x * hd2 + hz + (b * d₂ + x * a) * h2
  · linear_combination hd2

omit [CharP k 2] in
theorem pow_four_eq_self (hk : Nat.card k = 4) (x : k) : x ^ 4 = x := by
  have := Fintype.ofFinite k
  have h := FiniteField.pow_card x
  rwa [Fintype.card_eq_nat_card, hk] at h

theorem exists_inv_of_graph (hk : Nat.card k = 4) {T : GL (Fin 3) k}
    (hT : ∀ i j : Fin 3, j < i → (T : Matrix (Fin 3) (Fin 3) k) i j = 0)
    (h2 : (LinearFlag.conjAut 3 k T * gam) * (LinearFlag.conjAut 3 k T * gam) = 1) :
    ∃ y : projectiveSL 3 k, orderOf y = 3 ∧
      (LinearFlag.conjAut 3 k T * gam : MulAut (projectiveSL 3 k)) y = y⁻¹ := by
  have hsq : (LinearFlag.conjAut 3 k T * gam) * (LinearFlag.conjAut 3 k T * gam) =
      LinearFlag.conjAut 3 k (T * (w0GL * GeneralLinearGroup.inverseTranspose T * w0GL⁻¹)) := by
    calc (LinearFlag.conjAut 3 k T * gam) * (LinearFlag.conjAut 3 k T * gam)
        = LinearFlag.conjAut 3 k T * (gam * LinearFlag.conjAut 3 k T) * gam := by group
      _ = LinearFlag.conjAut 3 k T * (LinearFlag.conjAut 3 k
          (w0GL * GeneralLinearGroup.inverseTranspose T * w0GL⁻¹) * gam) * gam := by
          rw [gam_mul_conjAut]
      _ = LinearFlag.conjAut 3 k T * LinearFlag.conjAut 3 k
          (w0GL * GeneralLinearGroup.inverseTranspose T * w0GL⁻¹) * (gam * gam) := by group
      _ = _ := by rw [gam_mul_self, mul_one, ← map_mul]
  obtain ⟨-, l, hl⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one le_rfl
    (T * (w0GL * GeneralLinearGroup.inverseTranspose T * w0GL⁻¹)) 1
    (by rw [map_one, mul_one, ← hsq, h2])
  set Tm := (T : Matrix (Fin 3) (Fin 3) k) with hTm
  have hTTi : Tm * ((T⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) = 1 := T.mul_inv
  have hlm : scalar (Fin 3) (l : k) =
      Tm * (w0M * (((T⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k))ᵀ * w0M) := by
    have h1 := congrArg (fun B : GL (Fin 3) k => (B : Matrix (Fin 3) (Fin 3) k)) hl
    simp only [GeneralLinearGroup.coe_scalar, Units.val_mul,
      GeneralLinearGroup.coe_inverseTranspose] at h1
    exact h1
  have hkey : Tm * w0M = (l : k) • (w0M * Tmᵀ) := by
    have h1 : Tm * w0M = scalar (Fin 3) (l : k) * (w0M * Tmᵀ) := by
      rw [hlm]
      calc Tm * w0M = Tm * w0M * (Tm * ((T⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k))ᵀ := by
            rw [hTTi, transpose_one, mul_one]
        _ = _ := by
            rw [transpose_mul]
            simp only [mul_assoc]
            rw [← mul_assoc w0M w0M, w0M_mul_self, one_mul]
    rw [h1, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
  have e02 := congrFun (congrFun hkey 0) 2
  have e20 := congrFun (congrFun hkey 2) 0
  have e01 := congrFun (congrFun hkey 0) 1
  simp [w0M, Matrix.mul_apply, Fin.sum_univ_three, hT, Matrix.vecMul, dotProduct,
    Matrix.transpose_apply] at e02 e20 e01
  have hUT : Tm.IsUpperTriangular := fun i j hij => hT i j hij
  have hdetT : Tm.det = Tm 0 0 * Tm 1 1 * Tm 2 2 := by
    rw [Matrix.det_of_isUpperTriangular hUT, Fin.prod_univ_three]
  have hdet0 : Tm.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det Tm).mp T.isUnit).ne_zero
  have ha0 : Tm 0 0 ≠ 0 := fun h => hdet0 (by rw [hdetT, h, zero_mul, zero_mul])
  have hd0 : Tm 1 1 ≠ 0 := fun h => hdet0 (by rw [hdetT, h, mul_zero, zero_mul])
  have hl2 : (l : k) ^ 2 = 1 := by
    have h1 : (l : k) ^ 2 * Tm 0 0 = 1 * Tm 0 0 := by
      rw [one_mul]
      calc (l : k) ^ 2 * Tm 0 0 = (l : k) * ((l : k) * Tm 0 0) := by ring
        _ = Tm 0 0 := by rw [← e20, ← e02]
    exact mul_right_cancel₀ ha0 h1
  have hl1 : (l : k) = 1 := by
    apply frobenius_inj k 2
    rw [frobenius_def, frobenius_def, hl2, one_pow]
  rw [hl1, one_mul] at e20 e01
  set a := Tm 0 0 with ha
  set b := Tm 0 1 with hb
  set c := Tm 0 2 with hc
  set d := Tm 1 1 with hd
  have hTmat : Tm = !![a, b, c; 0, d, b; 0, 0, a] := by
    ext i j
    fin_cases i <;> fin_cases j
    all_goals first
      | exact hT _ _ (by decide)
      | rfl
      | exact e20
      | exact e01.symm
  set d₂ := (a * d⁻¹) ^ 2 with hd₂
  set x := (c * a⁻¹) ^ 2 with hx
  set z := b * d₂ * a⁻¹ + x with hz
  have hd2 : d₂ ^ 2 * d = a := by
    rw [hd₂, ← pow_mul, show 2 * 2 = 4 from rfl, pow_four_eq_self hk]
    field_simp
  have hx2 : x ^ 2 * a = c := by
    rw [hx, ← pow_mul, show 2 * 2 = 4 from rfl, pow_four_eq_self hk]
    field_simp
  have hz2 : z * a = b * d₂ + x * a := by
    rw [hz]
    field_simp
  have hd20 : d₂ ≠ 0 := by
    rw [hd₂]
    exact pow_ne_zero _ (mul_ne_zero ha0 (inv_ne_zero hd0))
  have hMdet : (!![1, x * d₂, x * z; 0, d₂, z; 0, 0, 1] : Matrix (Fin 3) (Fin 3) k).det = d₂ := by
    rw [Matrix.det_fin_three]
    simp
  let Mg : GL (Fin 3) k := Matrix.nonsingInvUnit !![1, x * d₂, x * z; 0, d₂, z; 0, 0, 1]
    (isUnit_iff_ne_zero.mpr (by rw [hMdet]; exact hd20))
  have hMg : (Mg : Matrix (Fin 3) (Fin 3) k) = !![1, x * d₂, x * z; 0, d₂, z; 0, 0, 1] := rfl
  have hsc : Mg * T * (w0GL * GeneralLinearGroup.inverseTranspose Mg⁻¹ * w0GL⁻¹) =
      GeneralLinearGroup.scalar (Fin 3) (Units.mk0 a ha0) := by
    apply Units.ext
    simp only [Units.val_mul, GeneralLinearGroup.coe_inverseTranspose, inv_inv,
      GeneralLinearGroup.coe_scalar, Units.val_mk0]
    change (Mg : Matrix (Fin 3) (Fin 3) k) * Tm * (w0M * (Mg : Matrix (Fin 3) (Fin 3) k)ᵀ * w0M) =
      scalar (Fin 3) a
    rw [hMg, hTmat]
    calc !![1, x * d₂, x * z; 0, d₂, z; 0, 0, 1] * !![a, b, c; 0, d, b; 0, 0, a] *
          (w0M * (!![1, x * d₂, x * z; 0, d₂, z; 0, 0, 1])ᵀ * w0M)
        = (!![1, x * d₂, x * z; 0, d₂, z; 0, 0, 1] * (!![a, b, c; 0, d, b; 0, 0, a] * w0M) *
            (!![1, x * d₂, x * z; 0, d₂, z; 0, 0, 1])ᵀ) * w0M := by simp only [mul_assoc]
      _ = (a • (w0M : Matrix (Fin 3) (Fin 3) k)) * w0M := by rw [congr_w0 hd2 hx2 hz2]
      _ = scalar (Fin 3) a := by
        rw [Matrix.smul_mul, w0M_mul_self, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hconj : LinearFlag.conjAut 3 k Mg * (LinearFlag.conjAut 3 k T * gam) *
      LinearFlag.conjAut 3 k Mg⁻¹ = gam := by
    calc LinearFlag.conjAut 3 k Mg * (LinearFlag.conjAut 3 k T * gam) *
          LinearFlag.conjAut 3 k Mg⁻¹
        = LinearFlag.conjAut 3 k Mg * LinearFlag.conjAut 3 k T *
          (gam * LinearFlag.conjAut 3 k Mg⁻¹) := by group
      _ = LinearFlag.conjAut 3 k Mg * LinearFlag.conjAut 3 k T *
          (LinearFlag.conjAut 3 k (w0GL * GeneralLinearGroup.inverseTranspose Mg⁻¹ * w0GL⁻¹) *
            gam) := by rw [gam_mul_conjAut]
      _ = LinearFlag.conjAut 3 k Mg * LinearFlag.conjAut 3 k T *
          LinearFlag.conjAut 3 k (w0GL * GeneralLinearGroup.inverseTranspose Mg⁻¹ * w0GL⁻¹) *
            gam := by group
      _ = LinearFlag.conjAut 3 k
          (Mg * T * (w0GL * GeneralLinearGroup.inverseTranspose Mg⁻¹ * w0GL⁻¹)) * gam := by
          rw [← map_mul, ← map_mul]
      _ = gam := by rw [hsc, conjAut_scalar, one_mul]
  have hα : (LinearFlag.conjAut 3 k T * gam : MulAut (projectiveSL 3 k)) =
      (LinearFlag.conjAut 3 k Mg)⁻¹ * gam * LinearFlag.conjAut 3 k Mg := by
    have h1 : (LinearFlag.conjAut 3 k T * gam : MulAut (projectiveSL 3 k)) =
        (LinearFlag.conjAut 3 k Mg)⁻¹ * (LinearFlag.conjAut 3 k Mg *
          (LinearFlag.conjAut 3 k T * gam) * LinearFlag.conjAut 3 k Mg⁻¹) *
          (LinearFlag.conjAut 3 k Mg⁻¹)⁻¹ := by group
    rw [h1, hconj, map_inv, inv_inv]
  refine ⟨(LinearFlag.conjAut 3 k Mg)⁻¹ (proj 3 k cycSL), ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq]
    exact orderOf_proj_eq_three cycSL_pow_three (i := 1) (j := 0) (by decide)
      (by simp [coe_cycSL])
  · rw [hα, MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self, gam_cycSL, map_inv]

theorem exists_inv_three_proj (hk : Nat.card k = 4) {α : MulAut (projectiveSL 3 k)}
    (hα2 : α * α = 1) (hα1 : α ≠ 1)
    (hαU : ∀ u ∈ projUnitriangular 3 k, α u ∈ projUnitriangular 3 k) :
    ∃ y : projectiveSL 3 k, orderOf y = 3 ∧ α y = y⁻¹ := by
  have hσ : ∀ a, frobeniusEquiv k 2 a = a ^ 2 := fun a => frobeniusEquiv_apply k 2 a
  obtain ⟨ω, hω3, hω2⟩ := exists_primitive_cube_root hk
  obtain ⟨⟨A, a, b⟩, hnf⟩ := exists_nf hσ hk α
  have hb0 : proj 3 k (torusDiag ω hω3) ∈ projUpperTriangular 3 k :=
    ⟨_, torusDiag_mem_upper hω3, rfl⟩
  rcases zmod_two_cases a with rfl | rfl
  · rcases zmod_two_cases b with rfl | rfl
    ·
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hα : α = LinearFlag.conjAut 3 k A := by rw [hnf, nf_zero_zero]
      have hAA : LinearFlag.conjAut 3 k (A * A) * fieldAut 3 k 1 = 1 := by
        rw [map_one, mul_one, map_mul, ← hα, hα2]
      obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one le_rfl (A * A) 1 hAA
      have hdetA : GeneralLinearGroup.det A = 1 := by
        have h1 := congrArg GeneralLinearGroup.det hc
        have hsc : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3) c) = 1 := by
          refine Units.ext ?_
          rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.coe_scalar, scalar_apply,
            det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Units.val_one,
            ← Units.val_pow_eq_pow_val, unit_pow_three hk, Units.val_one]
        rw [hsc, map_mul] at h1
        have h3 := unit_pow_three hk (GeneralLinearGroup.det A)
        calc GeneralLinearGroup.det A = GeneralLinearGroup.det A ^ 3 *
            (GeneralLinearGroup.det A * GeneralLinearGroup.det A)⁻¹ := by group
          _ = 1 := by rw [h3, ← h1, inv_one, one_mul]
      obtain ⟨g₀, hg₀⟩ : ∃ g₀ : SpecialLinearGroup (Fin 3) k,
          SpecialLinearGroup.toGL g₀ = A := ⟨⟨(A : Matrix (Fin 3) (Fin 3) k), by
            rw [← GeneralLinearGroup.val_det_apply, hdetA, Units.val_one]⟩, Units.ext rfl⟩
      have hαg : α = MulAut.conj (proj 3 k g₀) := by rw [hα, ← hg₀, conjAut_toGL]
      have hN : proj 3 k g₀ ∈ Subgroup.normalizer
          (projUnitriangular 3 k : Set (projectiveSL 3 k)) :=
        mem_normalizer_of_conj_mem fun u hu => by
          rw [← MulAut.conj_apply, ← hαg]
          exact hαU u hu
      rw [normalizer_projUnitriangular 2] at hN
      obtain ⟨g, hg, hgg⟩ := hN
      rw [← hgg] at hαg
      have hg2 : g * g ∈ scalars 3 k := by
        rw [← proj_eq_one_iff]
        have h1 : MulAut.conj (proj 3 k (g * g)) = 1 := by rw [map_mul, map_mul, ← hαg, hα2]
        have h2 : proj 3 k (g * g) ∈ Subgroup.center (projectiveSL 3 k) := by
          rw [Subgroup.mem_center_iff]
          intro w
          have h3 := congrArg (fun φ : MulAut (projectiveSL 3 k) => φ w) h1
          simp only [MulAut.conj_apply, MulAut.one_apply] at h3
          calc w * proj 3 k (g * g) =
              (proj 3 k (g * g) * w * (proj 3 k (g * g))⁻¹) * proj 3 k (g * g) := by rw [h3]
            _ = proj 3 k (g * g) * w := by group
        rw [center_projectiveSL_three_eq_bot hk, Subgroup.mem_bot] at h2
        exact h2
      obtain ⟨N, hN, hNN, hNg⟩ := exists_unitri_of_upper hk hg hg2
      rw [← hNg] at hαg
      have hN1 : N ≠ 1 := by
        rintro rfl
        rw [map_one, map_one] at hαg
        exact hα1 hαg
      rw [hαg]
      exact exists_inv_of_unitri hN hNN hN1
    ·
      have hα : α = LinearFlag.conjAut 3 k (A * w0GL⁻¹) * gam := by
        rw [hnf, gam]
        simp only [nf, val_one_two, ZMod.val_zero, pow_zero, mul_one, pow_one, map_mul, map_inv]
        group
      have hAU : ∀ u ∈ projUnitriangular 3 k,
          LinearFlag.conjAut 3 k (A * w0GL⁻¹) u ∈ projUnitriangular 3 k := by
        intro u hu
        have hgg : ∀ v : projectiveSL 3 k, gam (gam v) = v := fun v => by
          rw [← MulAut.mul_apply, gam_mul_self, MulAut.one_apply]
        have h1 : LinearFlag.conjAut 3 k (A * w0GL⁻¹) u = α (gam u) := by
          rw [hα, MulAut.mul_apply, hgg]
        rw [h1]
        exact hαU _ (gam_mem_projUnitriangular hu)
      obtain ⟨x, g, hg, hdec⟩ := exists_decomp hAU
      have hT : ∀ i j : Fin 3, j < i →
          ((diagGL x * SpecialLinearGroup.toGL g : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) i j =
            0 := by
        intro i j hij
        rw [Units.val_mul, coe_diagGL, Matrix.diagonal_mul]
        rw [show ((SpecialLinearGroup.toGL g : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
          (g : Matrix (Fin 3) (Fin 3) k) from rfl, hg i j hij, mul_zero]
      have hαT : α = LinearFlag.conjAut 3 k (diagGL x * SpecialLinearGroup.toGL g) * gam := by
        rw [hα, hdec, map_mul, conjAut_toGL]
      rw [hαT] at hα2 ⊢
      exact exists_inv_of_graph hk hT hα2
  ·
    have hχ : ∀ u : projUpperTriangular 3 k, ∃ h : α u ∈ projUpperTriangular 3 k,
        chiP (⟨α u, h⟩ : projUpperTriangular 3 k) = chiP u ^ 2 := by
      rcases zmod_two_cases b with rfl | rfl
      · have hα : α = LinearFlag.conjAut 3 k A * fieldAut 3 k (frobeniusEquiv k 2) := by
          rw [hnf]
          simp [nf, val_one_two]
        have hAU : ∀ u ∈ projUnitriangular 3 k,
            LinearFlag.conjAut 3 k A u ∈ projUnitriangular 3 k := by
          intro u hu
          have hff : ∀ v, fieldAut 3 k (frobeniusEquiv k 2) (fieldAut 3 k (frobeniusEquiv k 2) v)
              = v := fun v => by
            rw [← MulAut.mul_apply, fieldAut_sigma_mul_self hσ hk, MulAut.one_apply]
          have h1 : LinearFlag.conjAut 3 k A u =
              α (fieldAut 3 k (frobeniusEquiv k 2) u) := by
            rw [hα, MulAut.mul_apply, hff]
          rw [h1]
          exact hαU _ (fieldAut_mem_projUnitriangular _ hu)
        obtain ⟨x, g, hg, hdec⟩ := exists_decomp hAU
        intro u
        have h1 : α u = (LinearFlag.conjAut 3 k (diagGL x) * MulAut.conj (proj 3 k g))
            (fieldAut 3 k (frobeniusEquiv k 2) u) := by
          rw [hα, MulAut.mul_apply, hdec]
        have hm := decomp_mem_projUpper x hg (fieldAut_mem_projUpper (frobeniusEquiv k 2) u.2)
        refine ⟨h1 ▸ hm, ?_⟩
        have e : (⟨α u, h1 ▸ hm⟩ : projUpperTriangular 3 k) = ⟨_, hm⟩ := Subtype.ext h1
        rw [e, chiP_decomp x hg ⟨_, fieldAut_mem_projUpper (frobeniusEquiv k 2) u.2⟩,
          chiP_fieldAut hσ]
      · have hα : α = LinearFlag.conjAut 3 k (A * w0GL⁻¹) * nf (frobeniusEquiv k 2) w0GL 1 1 := by
          rw [hnf]
          simp only [nf, val_one_two, pow_one, map_mul, map_inv]
          group
        have h0U : ∀ u ∈ projUnitriangular 3 k,
            (nf (frobeniusEquiv k 2) w0GL 1 1)⁻¹ u ∈ projUnitriangular 3 k := by
          intro u hu
          have hmap := map_projUnitriangular_eq (β := nf (frobeniusEquiv k 2) w0GL 1 1)
            (fun v hv => alpha0_mem_projUnitriangular hv)
          rw [← hmap] at hu
          obtain ⟨v, hv, rfl⟩ := hu
          simpa using hv
        have hAU : ∀ u ∈ projUnitriangular 3 k,
            LinearFlag.conjAut 3 k (A * w0GL⁻¹) u ∈ projUnitriangular 3 k := by
          intro u hu
          have h1 : LinearFlag.conjAut 3 k (A * w0GL⁻¹) u =
              α ((nf (frobeniusEquiv k 2) w0GL 1 1)⁻¹ u) := by
            rw [hα, MulAut.mul_apply, MulAut.apply_inv_self]
          rw [h1]
          exact hαU _ (h0U u hu)
        obtain ⟨x, g, hg, hdec⟩ := exists_decomp hAU
        intro u
        have h1 : α u = (LinearFlag.conjAut 3 k (diagGL x) * MulAut.conj (proj 3 k g))
            (nf (frobeniusEquiv k 2) w0GL 1 1 u) := by
          rw [hα, MulAut.mul_apply, hdec]
        have hm := decomp_mem_projUpper x hg (alpha0_mem_projUpperTriangular (σ :=
          frobeniusEquiv k 2) u.2)
        refine ⟨h1 ▸ hm, ?_⟩
        have e : (⟨α u, h1 ▸ hm⟩ : projUpperTriangular 3 k) = ⟨_, hm⟩ := Subtype.ext h1
        rw [e, chiP_decomp x hg ⟨_, alpha0_mem_projUpperTriangular u.2⟩, chiP_alpha0 hσ]
    obtain ⟨h, hχb⟩ := hχ ⟨_, hb0⟩
    exact exists_inv_of_chiP hk hα2 hb0 h hχb (chiP_torusDiag_ne_one hω3 hω2 hb0)

omit [Finite k] [CharP k 2] in
theorem exists_sylow_two_fixed {X : Type} [Group X] [Finite X] {τ : MulAut X}
    (hτ2 : τ * τ = 1) : ∃ S : Sylow 2 X, τ • S = S := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let H : Subgroup (MulAut X) := Subgroup.zpowers τ
  have hH : IsPGroup 2 H := by
    rintro ⟨h, hh⟩
    refine ⟨1, Subtype.ext ?_⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, ← zpow_natCast, ← _root_.zpow_mul, mul_comm,
      _root_.zpow_mul, zpow_natCast, sq, hτ2, _root_.one_zpow]
  have h1 := hH.card_modEq_card_fixedPoints (Sylow 2 X)
  have h2 := card_sylow_modEq_one 2 X
  have h3 : Nat.card (MulAction.fixedPoints H (Sylow 2 X)) ≠ 0 := by
    intro h0
    rw [h0] at h1
    have h4 := h2.symm.trans h1
    exact absurd h4 (by decide)
  have : Nonempty (MulAction.fixedPoints H (Sylow 2 X)) := (Nat.card_ne_zero.mp h3).1
  obtain ⟨⟨S, hS⟩⟩ := this
  exact ⟨S, hS ⟨τ, Subgroup.mem_zpowers τ⟩⟩

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin in
theorem exists_inv_three {X : Type} [Group X] [Finite X] (hX : LieModel X .PSL 3 2 2)
    {τ : MulAut X} (hτ2 : τ * τ = 1) (hτ1 : τ ≠ 1) : ∃ y : X, orderOf y = 3 ∧ τ y = y⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := exists_sylow_two_fixed hτ2
  have hS2 : IsSylowTwoOf (S : Subgroup X) ⊤ := by
    refine ⟨le_top, S.isPGroup', ?_⟩
    change ¬ 2 ∣ (S : Subgroup X).relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact S.not_dvd_index
  obtain ⟨k, _, hk, e, he⟩ := exists_mulEquiv_sylow_eq hX hS2
  have : Finite k := LinearFieldFour.finite_of_card_eq_four hk
  have : CharP k 2 := LinearFieldFour.charP_two_of_card_eq_four hk
  set α := MulAut.congr e τ with hα
  have hαapp : ∀ x, α x = e (τ (e.symm x)) := fun x => rfl
  have hα2 : α * α = 1 := by rw [hα, ← map_mul, hτ2, map_one]
  have hα1 : α ≠ 1 := by
    intro h
    apply hτ1
    rw [← map_one (MulAut.congr e)] at h
    exact (MulAut.congr e).injective h
  have hτS : ∀ s ∈ (S : Subgroup X), τ s ∈ (S : Subgroup X) := by
    intro s hs
    have h1 : τ s ∈ ((τ • S : Sylow 2 X) : Subgroup X) := by
      change τ s ∈ τ • (S : Subgroup X)
      rw [Subgroup.mem_smul_pointwise_iff_exists]
      exact ⟨s, hs, rfl⟩
    rwa [hS] at h1
  have hαU : ∀ u ∈ projUnitriangular 3 k, α u ∈ projUnitriangular 3 k := by
    intro u hu
    rw [← he] at hu ⊢
    obtain ⟨s, hs, rfl⟩ := hu
    refine ⟨τ s, hτS s hs, ?_⟩
    rw [hαapp]
    simp
  obtain ⟨y, hy3, hyα⟩ := exists_inv_three_proj hk hα2 hα1 hαU
  refine ⟨e.symm y, by rw [MulEquiv.orderOf_eq, hy3], ?_⟩
  have h1 : e (τ (e.symm y)) = y⁻¹ := by rw [← hαapp, hyα]
  rw [← map_inv, ← h1, MulEquiv.symm_apply_apply]

end CFSG.Quasithin.H13.TorusComm
