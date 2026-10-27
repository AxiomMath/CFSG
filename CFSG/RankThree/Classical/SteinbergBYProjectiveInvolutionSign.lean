module

public import CFSG.LinearAlgebra.LinearGroups.LinearTwoOddFourGroups
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

namespace CFSG.RankThree.Classical.SteinbergBY

open CFSG.LinearGroups CFSG.ComponentClassification.CatalogueSchreierLinearTwo Matrix

variable {F : Type*} [Field F]

local notation "M₂" => Matrix (Fin 2) (Fin 2) F

theorem exists_cyclic_vector {Z : Matrix (Fin 2) (Fin 2) F}
    (hZ : ∀ c : F, Z ≠ Matrix.scalar (Fin 2) c) :
    ∃ v : Fin 2 → F, LinearIndependent F ![v, Z *ᵥ v] := by
  by_contra h
  push Not at h
  obtain ⟨a, ha⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent
    (f := Matrix.toLin' Z) (fun v => by simpa [Matrix.toLin'_apply] using h v)
  apply hZ a
  apply Matrix.toLin'.injective
  rw [ha]
  ext v i
  simp [Matrix.toLin'_apply, Matrix.scalar_apply, Pi.single_apply]

theorem eq_zero_of_mulVec_cyclic {Z C : Matrix (Fin 2) (Fin 2) F} {v : Fin 2 → F}
    (hv : LinearIndependent F ![v, Z *ᵥ v]) (h1 : C *ᵥ v = 0) (h2 : C *ᵥ (Z *ᵥ v) = 0) :
    C = 0 := by
  have hspan : Submodule.span F (Set.range ![v, Z *ᵥ v]) = ⊤ :=
    hv.span_eq_top_of_card_eq_finrank (by simp)
  apply Matrix.toLin'.injective
  rw [map_zero]
  apply LinearMap.ext_on_range hspan
  intro i
  fin_cases i
  · simpa [Matrix.toLin'_apply] using h1
  · simpa [Matrix.toLin'_apply] using h2

theorem exists_eq_add_of_cyclic {Z : Matrix (Fin 2) (Fin 2) F} {v : Fin 2 → F}
    (hv : LinearIndependent F ![v, Z *ᵥ v]) (w : Fin 2 → F) :
    ∃ a b : F, w = a • v + b • (Z *ᵥ v) := by
  have hspan : Submodule.span F (Set.range ![v, Z *ᵥ v]) = ⊤ :=
    hv.span_eq_top_of_card_eq_finrank (by simp)
  have hw : w ∈ Submodule.span F {v, Z *ᵥ v} := by
    have : Set.range ![v, Z *ᵥ v] = {v, Z *ᵥ v} := by
      rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty]
      rfl
    rw [← this, hspan]
    exact Submodule.mem_top
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hw
  exact ⟨a, b, hab.symm⟩

theorem scalar_two_mulVec (c : F) (w : Fin 2 → F) : Matrix.scalar (Fin 2) c *ᵥ w = c • w := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Matrix.scalar_apply, Matrix.diagonal]

theorem exists_eq_scalar_add_smul_of_commute {Z B : Matrix (Fin 2) (Fin 2) F}
    (hZ : ∀ c : F, Z ≠ Matrix.scalar (Fin 2) c) (hBZ : B * Z = Z * B) :
    ∃ a b : F, B = Matrix.scalar (Fin 2) a + b • Z := by
  obtain ⟨v, hv⟩ := exists_cyclic_vector hZ
  obtain ⟨a, b, hab⟩ := exists_eq_add_of_cyclic hv (B *ᵥ v)
  refine ⟨a, b, ?_⟩
  have hC : B - (Matrix.scalar (Fin 2) a + b • Z) = 0 := by
    refine eq_zero_of_mulVec_cyclic hv ?_ ?_
    · rw [Matrix.sub_mulVec, Matrix.add_mulVec, hab, scalar_two_mulVec,
        Matrix.smul_mulVec]
      abel
    · have hBZv : B *ᵥ (Z *ᵥ v) = Z *ᵥ (B *ᵥ v) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hBZ]
      rw [Matrix.sub_mulVec, Matrix.add_mulVec, hBZv, hab, scalar_two_mulVec,
        Matrix.smul_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
      abel
  exact sub_eq_zero.mp hC

theorem exists_sq_eq_scalar_of_anticommute {Z A : Matrix (Fin 2) (Fin 2) F} {c : F}
    (hZ : ∀ c : F, Z ≠ Matrix.scalar (Fin 2) c) (hZ2 : Z * Z = Matrix.scalar (Fin 2) c)
    (hAZ : A * Z = -(Z * A)) : ∃ s : F, A * A = Matrix.scalar (Fin 2) s := by
  obtain ⟨v, hv⟩ := exists_cyclic_vector hZ
  obtain ⟨a, b, hab⟩ := exists_eq_add_of_cyclic hv (A *ᵥ v)
  have hZZv : Z *ᵥ (Z *ᵥ v) = c • v := by
    rw [Matrix.mulVec_mulVec, hZ2, scalar_two_mulVec]
  have hAZv : A *ᵥ (Z *ᵥ v) = -(a • (Z *ᵥ v) + (b * c) • v) := by
    rw [Matrix.mulVec_mulVec, hAZ, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, hab,
      Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hZZv, smul_smul]
  refine ⟨a ^ 2 - b ^ 2 * c, ?_⟩
  have hC : A * A - Matrix.scalar (Fin 2) (a ^ 2 - b ^ 2 * c) = 0 := by
    refine eq_zero_of_mulVec_cyclic hv ?_ ?_
    · rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hab, Matrix.mulVec_add, Matrix.mulVec_smul,
        Matrix.mulVec_smul, hab, hAZv, scalar_two_mulVec]
      module
    · rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hAZv, Matrix.mulVec_neg, Matrix.mulVec_add,
        Matrix.mulVec_smul, Matrix.mulVec_smul, hAZv, hab, scalar_two_mulVec]
      module
  exact sub_eq_zero.mp hC

theorem mul_scalar_two (M : Matrix (Fin 2) (Fin 2) F) (a : F) :
    M * Matrix.scalar (Fin 2) a = a • M := by
  rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]

theorem scalar_two_mul (M : Matrix (Fin 2) (Fin 2) F) (a : F) :
    Matrix.scalar (Fin 2) a * M = a • M := by
  rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul]

theorem gl_val_ne_zero (A : GL (Fin 2) F) : (A : M₂) ≠ 0 := fun h => by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp A.isUnit
  rw [h, Matrix.det_zero] at hdet
  exact not_isUnit_zero hdet

variable [Finite F]

theorem lift_of_projective_involution {Z : GL (Fin 2) F} (h1 : coordinateGLAction F Z ≠ 1)
    (h2 : coordinateGLAction F Z ^ 2 = 1) :
    (∃ c : Fˣ, (Z : M₂) * (Z : M₂) = Matrix.scalar (Fin 2) (c : F)) ∧
      Z ∉ Subgroup.center (GL (Fin 2) F) := by
  refine ⟨?_, fun hc => h1 ((coordinateGLAction_eq_one_iff Z).mpr hc)⟩
  have hc : Z ^ 2 ∈ Subgroup.center (GL (Fin 2) F) :=
    (coordinateGLAction_eq_one_iff _).mp (by rw [map_pow]; exact h2)
  rw [GeneralLinearGroup.center_eq_range_scalar] at hc
  obtain ⟨c, hc⟩ := hc
  refine ⟨c, ?_⟩
  have := congrArg Units.val hc
  rw [GeneralLinearGroup.coe_scalar, Units.val_pow_eq_pow_val, pow_two] at this
  exact this.symm

omit [Finite F] in
theorem ne_scalar_of_not_mem_center {Z : GL (Fin 2) F} (hZ : Z ∉ Subgroup.center (GL (Fin 2) F)) :
    ∀ c : F, (Z : M₂) ≠ Matrix.scalar (Fin 2) c := by
  intro c hc
  apply hZ
  have hc0 : c ≠ 0 := by
    rintro rfl
    have hdet := (Matrix.isUnit_iff_isUnit_det _).mp Z.isUnit
    rw [hc, map_zero, Matrix.det_zero] at hdet
    exact not_isUnit_zero hdet
  rw [GeneralLinearGroup.center_eq_range_scalar]
  exact ⟨Units.mk0 c hc0, Units.ext (by rw [GeneralLinearGroup.coe_scalar, hc]; rfl)⟩

theorem exists_sign_of_proj_commute {A Z : GL (Fin 2) F} (h1 : coordinateGLAction F Z ≠ 1)
    (h2 : coordinateGLAction F Z ^ 2 = 1)
    (hc : coordinateGLAction F A * coordinateGLAction F Z =
      coordinateGLAction F Z * coordinateGLAction F A) :
    ∃ ε : ℤˣ, (A : M₂) * (Z : M₂) = ((ε : ℤ) : F) • ((Z : M₂) * (A : M₂)) := by
  obtain ⟨⟨c, hc2⟩, -⟩ := lift_of_projective_involution h1 h2
  rw [← map_mul, ← map_mul, coordinateGLAction_eq_iff] at hc
  obtain ⟨u, hu⟩ := hc
  have hm : (Z : M₂) * (A : M₂) = (u : F) • ((A : M₂) * (Z : M₂)) := by
    have h := congrArg Units.val hu
    rw [Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar, mul_scalar_two] at h
    exact h.symm
  have e1 : (Z : M₂) * (Z : M₂) * (A : M₂) = (c : F) • (A : M₂) := by
    rw [hc2, scalar_two_mul]
  have e2 : (Z : M₂) * (Z : M₂) * (A : M₂) = ((u : F) ^ 2 * c) • (A : M₂) := by
    calc (Z : M₂) * (Z : M₂) * (A : M₂) = (Z : M₂) * ((Z : M₂) * (A : M₂)) := Matrix.mul_assoc _ _ _
      _ = (Z : M₂) * ((u : F) • ((A : M₂) * (Z : M₂))) := by rw [hm]
      _ = (u : F) • ((Z : M₂) * (A : M₂) * (Z : M₂)) := by rw [Matrix.mul_smul, Matrix.mul_assoc]
      _ = (u : F) • (((u : F) • ((A : M₂) * (Z : M₂))) * (Z : M₂)) := by rw [hm]
      _ = ((u : F) ^ 2) • ((A : M₂) * ((Z : M₂) * (Z : M₂))) := by
          rw [Matrix.smul_mul, smul_smul, Matrix.mul_assoc, sq]
      _ = ((u : F) ^ 2 * c) • (A : M₂) := by rw [hc2, mul_scalar_two, smul_smul]
  have key : ((c : F) - (u : F) ^ 2 * c) • (A : M₂) = 0 := by
    rw [sub_smul, ← e1, ← e2, sub_self]
  have hu2 : (u : F) ^ 2 = 1 := by
    rcases smul_eq_zero.mp key with h | h
    · have h' : (c : F) * (1 - (u : F) ^ 2) = 0 := by linear_combination h
      rcases mul_eq_zero.mp h' with h'' | h''
      · exact absurd h'' c.ne_zero
      · linear_combination -h''
    · exact absurd h (gl_val_ne_zero A)
  rcases sq_eq_one_iff.mp hu2 with hu1 | hu1
  · refine ⟨1, ?_⟩
    rw [hu1, one_smul] at hm
    rw [Units.val_one, Int.cast_one, one_smul, hm]
  · refine ⟨-1, ?_⟩
    rw [hu1, neg_one_smul] at hm
    rw [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_smul, hm, neg_neg]

omit [Finite F] in
theorem sign_unique (hF : ringChar F ≠ 2) {A Z : GL (Fin 2) F} {ε ε' : ℤˣ}
    (h : ((ε : ℤ) : F) • ((Z : M₂) * (A : M₂)) =
      ((ε' : ℤ) : F) • ((Z : M₂) * (A : M₂))) : ε = ε' := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hZA : (Z : M₂) * (A : M₂) ≠ 0 := gl_val_ne_zero (Z * A)
  have hεε : ((ε : ℤ) : F) = ((ε' : ℤ) : F) := by
    by_contra hne
    apply hZA
    have := sub_eq_zero.mpr h
    rw [← sub_smul] at this
    rcases smul_eq_zero.mp this with h' | h'
    · exact absurd (sub_eq_zero.mp h') hne
    · exact h'
  rcases Int.units_eq_one_or ε with rfl | rfl <;> rcases Int.units_eq_one_or ε' with rfl | rfl
  · rfl
  · exfalso
    apply h2
    simp at hεε
    linear_combination hεε
  · exfalso
    apply h2
    simp at hεε
    linear_combination -hεε
  · rfl

open _root_.Classical in
@[expose] noncomputable def projInvolutionSign (z d : Equiv.Perm (Omega F)) : ℤˣ :=
  if ∃ A Z : GL (Fin 2) F, coordinateGLAction F A = d ∧ coordinateGLAction F Z = z ∧
      A * Z = Z * A then 1 else -1

theorem projInvolutionSign_spec (hF : ringChar F ≠ 2) {A Z : GL (Fin 2) F}
    (h1 : coordinateGLAction F Z ≠ 1) (h2 : coordinateGLAction F Z ^ 2 = 1)
    (hc : coordinateGLAction F A * coordinateGLAction F Z =
      coordinateGLAction F Z * coordinateGLAction F A) :
    (A : M₂) * (Z : M₂) =
      ((projInvolutionSign (coordinateGLAction F Z) (coordinateGLAction F A) : ℤ) : F) •
        ((Z : M₂) * (A : M₂)) := by
  have h2F : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  obtain ⟨ε, hε⟩ := exists_sign_of_proj_commute h1 h2 hc
  rcases Int.units_eq_one_or ε with rfl | rfl
  · have hcomm : A * Z = Z * A := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hε]
      simp
    rw [projInvolutionSign, ite_eq_left ⟨A, Z, rfl, rfl, hcomm⟩, hε]
  · have hAZ : (A : M₂) * (Z : M₂) = -((Z : M₂) * (A : M₂)) := by
      simpa using hε
    have hneg : ¬ ∃ A' Z' : GL (Fin 2) F, coordinateGLAction F A' = coordinateGLAction F A ∧
        coordinateGLAction F Z' = coordinateGLAction F Z ∧ A' * Z' = Z' * A' := by
      rintro ⟨A', Z', hA', hZ', hcomm⟩
      obtain ⟨s, hs⟩ := coordinateGLAction_eq_iff.mp hA'.symm
      obtain ⟨t, ht⟩ := coordinateGLAction_eq_iff.mp hZ'.symm
      have hA'm : (A' : M₂) = (s : F) • (A : M₂) := by
        rw [← hs, Units.val_mul, GeneralLinearGroup.coe_scalar, mul_scalar_two]
      have hZ'm : (Z' : M₂) = (t : F) • (Z : M₂) := by
        rw [← ht, Units.val_mul, GeneralLinearGroup.coe_scalar, mul_scalar_two]
      have hm := congrArg Units.val hcomm
      rw [Units.val_mul, Units.val_mul, hA'm, hZ'm, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_smul, hAZ, mul_comm (t : F)] at hm
      have h0 : (2 * ((s : F) * t)) • ((Z : M₂) * (A : M₂)) = 0 := by
        rw [two_mul, add_smul]
        nth_rewrite 2 [← hm]
        rw [smul_neg, add_neg_cancel]
      rcases smul_eq_zero.mp h0 with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact h2F h
        · rcases mul_eq_zero.mp h with h | h
          · exact s.ne_zero h
          · exact t.ne_zero h
      · exact gl_val_ne_zero (Z * A) (by rw [Units.val_mul]; exact h)
    rw [projInvolutionSign, ite_eq_right hneg, hAZ]
    simp

omit [Finite F] in
theorem exists_lift_of_mem_coordinateD {d : Equiv.Perm (Omega F)} (hd : d ∈ coordinateD F) :
    ∃ A : GL (Fin 2) F, coordinateGLAction F A = d := by
  rw [← (linear_two_projective_identification F).2.2.2.2.1] at hd
  exact hd

omit [Finite F] in
theorem coordinateGLAction_mem_coordinateD (A : GL (Fin 2) F) :
    coordinateGLAction F A ∈ coordinateD F := by
  rw [← (linear_two_projective_identification F).2.2.2.2.1]
  exact ⟨A, rfl⟩

omit [Finite F] in
theorem lift_conditions_of_involution {z : coordinateD F} (hz : orderOf z = 2) {Z : GL (Fin 2) F}
    (hZ : coordinateGLAction F Z = z) :
    coordinateGLAction F Z ≠ 1 ∧ coordinateGLAction F Z ^ 2 = 1 := by
  refine ⟨fun h => ?_, ?_⟩
  · have hz1 : z = 1 := Subtype.ext (by rw [← hZ, h]; rfl)
    rw [hz1, orderOf_one] at hz
    exact absurd hz (by norm_num)
  · rw [hZ, ← Subgroup.coe_pow, pow_two, ← pow_two, ← hz, pow_orderOf_eq_one]
    rfl

@[expose] noncomputable def projInvolutionSignHom (hF : ringChar F ≠ 2) (z : coordinateD F)
    (hz : orderOf z = 2) : Subgroup.centralizer ({z} : Set (coordinateD F)) →* ℤˣ where
  toFun d := projInvolutionSign (z : Equiv.Perm (Omega F)) ((d : coordinateD F) :
    Equiv.Perm (Omega F))
  map_one' := by
    obtain ⟨Z, hZ⟩ := exists_lift_of_mem_coordinateD z.2
    obtain ⟨h1, h2⟩ := lift_conditions_of_involution hz hZ
    have hspec := projInvolutionSign_spec hF (A := 1) h1 h2 (by rw [map_one, one_mul, mul_one])
    rw [hZ, map_one] at hspec
    show projInvolutionSign (z : Equiv.Perm (Omega F)) 1 = 1
    apply sign_unique hF (A := 1) (Z := Z)
    rw [← hspec]
    simp
  map_mul' d₁ d₂ := by
    obtain ⟨Z, hZ⟩ := exists_lift_of_mem_coordinateD z.2
    obtain ⟨h1, h2⟩ := lift_conditions_of_involution hz hZ
    obtain ⟨A₁, hA₁⟩ := exists_lift_of_mem_coordinateD ((d₁ : coordinateD F)).2
    obtain ⟨A₂, hA₂⟩ := exists_lift_of_mem_coordinateD ((d₂ : coordinateD F)).2
    have hc : ∀ (d : Subgroup.centralizer ({z} : Set (coordinateD F))) (A : GL (Fin 2) F),
        coordinateGLAction F A = ((d : coordinateD F) : Equiv.Perm (Omega F)) →
        coordinateGLAction F A * coordinateGLAction F Z =
          coordinateGLAction F Z * coordinateGLAction F A := by
      intro d A hA
      rw [hA, hZ]
      have := Subgroup.mem_centralizer_singleton_iff.mp d.2
      exact congrArg Subtype.val this
    have s₁ := projInvolutionSign_spec hF h1 h2 (hc d₁ A₁ hA₁)
    have s₂ := projInvolutionSign_spec hF h1 h2 (hc d₂ A₂ hA₂)
    have hA₁₂ : coordinateGLAction F (A₁ * A₂) =
        ((d₁ * d₂ : Subgroup.centralizer ({z} : Set (coordinateD F))) : coordinateD F) := by
      rw [map_mul, hA₁, hA₂]
      rfl
    have s₁₂ := projInvolutionSign_spec hF h1 h2 (hc (d₁ * d₂) (A₁ * A₂) hA₁₂)
    rw [hZ, hA₁] at s₁
    rw [hZ, hA₂] at s₂
    rw [hZ, hA₁₂] at s₁₂
    set ε₁ := projInvolutionSign (z : Equiv.Perm (Omega F)) ((d₁ : coordinateD F) :
      Equiv.Perm (Omega F))
    set ε₂ := projInvolutionSign (z : Equiv.Perm (Omega F)) ((d₂ : coordinateD F) :
      Equiv.Perm (Omega F))
    change projInvolutionSign (z : Equiv.Perm (Omega F))
      (((d₁ * d₂ : Subgroup.centralizer ({z} : Set (coordinateD F))) : coordinateD F) :
        Equiv.Perm (Omega F)) = ε₁ * ε₂
    have hprod : ((A₁ * A₂ : GL (Fin 2) F) : M₂) * (Z : M₂) =
        (((ε₁ * ε₂ : ℤˣ) : ℤ) : F) • ((Z : M₂) * ((A₁ * A₂ : GL (Fin 2) F) : M₂)) := by
      rw [Units.val_mul, Matrix.mul_assoc, s₂, Matrix.mul_smul, ← Matrix.mul_assoc, s₁,
        Matrix.smul_mul, smul_smul, Units.val_mul, Int.cast_mul, mul_comm, Matrix.mul_assoc]
    exact sign_unique hF (A := A₁ * A₂) (Z := Z) (s₁₂.symm.trans hprod)

theorem projInvolutionSignHom_spec (hF : ringChar F ≠ 2) {z : coordinateD F} (hz : orderOf z = 2)
    (d : Subgroup.centralizer ({z} : Set (coordinateD F))) {A Z : GL (Fin 2) F}
    (hA : coordinateGLAction F A = ((d : coordinateD F) : Equiv.Perm (Omega F)))
    (hZ : coordinateGLAction F Z = z) :
    (A : M₂) * (Z : M₂) = ((projInvolutionSignHom hF z hz d : ℤ) : F) • ((Z : M₂) * (A : M₂)) := by
  obtain ⟨h1, h2⟩ := lift_conditions_of_involution hz hZ
  have hc : coordinateGLAction F A * coordinateGLAction F Z =
      coordinateGLAction F Z * coordinateGLAction F A := by
    rw [hA, hZ]
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp d.2)
  have h := projInvolutionSign_spec hF h1 h2 hc
  rw [hA, hZ] at h
  exact h

omit [Finite F] in
theorem conj_eq_smul_iff {A Z : GL (Fin 2) F} {e : F} :
    (A : M₂) * (Z : M₂) * ((A⁻¹ : GL (Fin 2) F) : M₂) = e • (Z : M₂) ↔
      (A : M₂) * (Z : M₂) = e • ((Z : M₂) * (A : M₂)) := by
  have hinv : ((A⁻¹ : GL (Fin 2) F) : M₂) * (A : M₂) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hinv' : (A : M₂) * ((A⁻¹ : GL (Fin 2) F) : M₂) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  constructor
  · intro h
    calc (A : M₂) * (Z : M₂)
        = (A : M₂) * (Z : M₂) * (((A⁻¹ : GL (Fin 2) F) : M₂) * (A : M₂)) := by
          rw [hinv, Matrix.mul_one]
      _ = (A : M₂) * (Z : M₂) * ((A⁻¹ : GL (Fin 2) F) : M₂) * (A : M₂) := by
          rw [Matrix.mul_assoc ((A : M₂) * (Z : M₂))]
      _ = e • ((Z : M₂) * (A : M₂)) := by rw [h, Matrix.smul_mul]
  · intro h
    rw [h, Matrix.smul_mul, Matrix.mul_assoc, hinv', Matrix.mul_one]

theorem mem_ker_projInvolutionSignHom_iff (hF : ringChar F ≠ 2) {z : coordinateD F}
    (hz : orderOf z = 2) {Z : GL (Fin 2) F} (hZ : coordinateGLAction F Z = z)
    (d : Subgroup.centralizer ({z} : Set (coordinateD F))) :
    d ∈ (projInvolutionSignHom hF z hz).ker ↔ ∃ A : GL (Fin 2) F,
      coordinateGLAction F A = ((d : coordinateD F) : Equiv.Perm (Omega F)) ∧ A * Z = Z * A := by
  obtain ⟨A, hA⟩ := exists_lift_of_mem_coordinateD (d : coordinateD F).2
  have hspec := projInvolutionSignHom_spec hF hz d hA hZ
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    refine ⟨A, hA, Units.ext ?_⟩
    rw [Units.val_mul, Units.val_mul, hspec, h]
    simp
  · rintro ⟨A', hA', hcomm⟩
    have hspec' := projInvolutionSignHom_spec hF hz d hA' hZ
    have hm : (A' : M₂) * (Z : M₂) = (Z : M₂) * (A' : M₂) := by
      rw [← Units.val_mul, ← Units.val_mul, hcomm]
    apply sign_unique hF (A := A') (Z := Z)
    rw [← hspec', hm]
    simp

omit [Finite F] in
theorem commute_scalar_add_smul (Z : M₂) (a b a' b' : F) :
    Commute (Matrix.scalar (Fin 2) a + b • Z) (Matrix.scalar (Fin 2) a' + b' • Z) :=
  Commute.add_left (Matrix.scalar_commute a (fun _ => Commute.all _ _) _)
    (Commute.add_right (Matrix.scalar_commute a' (fun _ => Commute.all _ _) _).symm
      (((Commute.refl Z).smul_left b).smul_right b'))

theorem ker_projInvolutionSignHom_commute (hF : ringChar F ≠ 2) {z : coordinateD F}
    (hz : orderOf z = 2) {d₁ d₂ : Subgroup.centralizer ({z} : Set (coordinateD F))}
    (h₁ : d₁ ∈ (projInvolutionSignHom hF z hz).ker)
    (h₂ : d₂ ∈ (projInvolutionSignHom hF z hz).ker) : d₁ * d₂ = d₂ * d₁ := by
  obtain ⟨Z, hZ⟩ := exists_lift_of_mem_coordinateD z.2
  obtain ⟨h1, h2⟩ := lift_conditions_of_involution hz hZ
  have hZs := ne_scalar_of_not_mem_center (lift_of_projective_involution h1 h2).2
  obtain ⟨A₁, hA₁, c₁⟩ := (mem_ker_projInvolutionSignHom_iff hF hz hZ d₁).mp h₁
  obtain ⟨A₂, hA₂, c₂⟩ := (mem_ker_projInvolutionSignHom_iff hF hz hZ d₂).mp h₂
  have m₁ : (A₁ : M₂) * (Z : M₂) = (Z : M₂) * (A₁ : M₂) := by
    rw [← Units.val_mul, ← Units.val_mul, c₁]
  have m₂ : (A₂ : M₂) * (Z : M₂) = (Z : M₂) * (A₂ : M₂) := by
    rw [← Units.val_mul, ← Units.val_mul, c₂]
  obtain ⟨a₁, b₁, e₁⟩ := exists_eq_scalar_add_smul_of_commute hZs m₁
  obtain ⟨a₂, b₂, e₂⟩ := exists_eq_scalar_add_smul_of_commute hZs m₂
  have hcomm : A₁ * A₂ = A₂ * A₁ := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, e₁, e₂]
    exact (commute_scalar_add_smul _ a₁ b₁ a₂ b₂).eq
  have h : ((d₁ : coordinateD F) : Equiv.Perm (Omega F)) * ((d₂ : coordinateD F) :
      Equiv.Perm (Omega F)) = ((d₂ : coordinateD F) : Equiv.Perm (Omega F)) *
        ((d₁ : coordinateD F) : Equiv.Perm (Omega F)) := by
    rw [← hA₁, ← hA₂, ← map_mul, ← map_mul, hcomm]
  exact Subtype.ext (Subtype.ext h)

theorem orderOf_eq_two_of_not_mem_ker (hF : ringChar F ≠ 2) {z : coordinateD F}
    (hz : orderOf z = 2) {d : Subgroup.centralizer ({z} : Set (coordinateD F))}
    (hd : d ∉ (projInvolutionSignHom hF z hz).ker) : orderOf d = 2 := by
  obtain ⟨Z, hZ⟩ := exists_lift_of_mem_coordinateD z.2
  obtain ⟨h1, h2⟩ := lift_conditions_of_involution hz hZ
  obtain ⟨⟨c, hc⟩, hZc⟩ := lift_of_projective_involution h1 h2
  have hZs := ne_scalar_of_not_mem_center hZc
  obtain ⟨A, hA⟩ := exists_lift_of_mem_coordinateD (d : coordinateD F).2
  have hspec := projInvolutionSignHom_spec hF hz d hA hZ
  have hneg : projInvolutionSignHom hF z hz d = -1 := by
    rcases Int.units_eq_one_or (projInvolutionSignHom hF z hz d) with h | h
    · exact absurd h hd
    · exact h
  rw [hneg] at hspec
  have hAZ : (A : M₂) * (Z : M₂) = -((Z : M₂) * (A : M₂)) := by simpa using hspec
  obtain ⟨s, hs⟩ := exists_sq_eq_scalar_of_anticommute hZs hc hAZ
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply gl_val_ne_zero (A * A)
    rw [Units.val_mul, hs, map_zero]
  have hcen : A ^ 2 ∈ Subgroup.center (GL (Fin 2) F) := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨Units.mk0 s hs0, Units.ext (by
      rw [GeneralLinearGroup.coe_scalar, pow_two, Units.val_mul, hs]
      rfl)⟩
  have hd2 : ((d : coordinateD F) : Equiv.Perm (Omega F)) ^ 2 = 1 := by
    rw [← hA, ← map_pow, (coordinateGLAction_eq_one_iff _).mpr hcen]
  have hd1 : d ≠ 1 := by
    rintro rfl
    exact hd (one_mem _)
  exact orderOf_eq_prime (Subtype.ext (Subtype.ext hd2)) hd1

theorem quaternion_a_n_commute (n : ℕ) (g : QuaternionGroup n) :
    g * QuaternionGroup.a n = QuaternionGroup.a n * g := by
  have h : ((n : ℕ) : ZMod (2 * n)) + n = 0 := by
    rw [← Nat.cast_add, ← two_mul, ZMod.natCast_self]
  rcases g with i | i
  · rw [QuaternionGroup.a_mul_a, QuaternionGroup.a_mul_a, add_comm]
  · rw [QuaternionGroup.xa_mul_a, QuaternionGroup.a_mul_xa]
    congr 1
    linear_combination h

theorem not_injective_quaternion_coordinateD (hF : ringChar F ≠ 2) {n : ℕ} (hn : 2 ≤ n)
    (f : QuaternionGroup n →* coordinateD F) : ¬ Function.Injective f := by
  intro hf
  have : NeZero n := ⟨by omega⟩
  have hz : orderOf (f (QuaternionGroup.a n)) = 2 := by
    rw [orderOf_injective f hf, ← QuaternionGroup.xa_sq 0,
      orderOf_pow_of_dvd (by norm_num) (by rw [QuaternionGroup.orderOf_xa]; norm_num),
      QuaternionGroup.orderOf_xa]
  have hcen : ∀ g : QuaternionGroup n,
      f g ∈ Subgroup.centralizer ({f (QuaternionGroup.a n)} : Set (coordinateD F)) := by
    intro g
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, quaternion_a_n_commute]
  have hker : ∀ g : QuaternionGroup n, 2 < orderOf g →
      (⟨f g, hcen g⟩ : Subgroup.centralizer ({f (QuaternionGroup.a n)} : Set (coordinateD F))) ∈
        (projInvolutionSignHom hF _ hz).ker := by
    intro g hg
    by_contra h
    have h2 := orderOf_eq_two_of_not_mem_ker hF hz h
    rw [Subgroup.orderOf_mk, orderOf_injective f hf] at h2
    omega
  have h₁ := hker (QuaternionGroup.a 1) (by rw [QuaternionGroup.orderOf_a_one]; omega)
  have h₂ := hker (QuaternionGroup.xa 0) (by rw [QuaternionGroup.orderOf_xa]; norm_num)
  have hc := ker_projInvolutionSignHom_commute hF hz h₁ h₂
  have hc' : QuaternionGroup.a 1 * QuaternionGroup.xa 0 =
      (QuaternionGroup.xa 0 * QuaternionGroup.a 1 : QuaternionGroup n) := by
    apply hf
    rw [map_mul, map_mul]
    exact congrArg Subtype.val hc
  rw [QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a, QuaternionGroup.xa.injEq, zero_sub,
    zero_add] at hc'
  have : Fact (2 < 2 * n) := ⟨by omega⟩
  exact ZMod.neg_one_ne_one hc'

theorem odd_linear_two_projective_involution_centralizers_exclude_quaternion
    (hF : ringChar F ≠ 2) :
    (∀ (z : coordinateD F) (hz : orderOf z = 2),
      (∀ Z : GL (Fin 2) F, coordinateGLAction F Z = z →
        (∃ c : Fˣ, (Z : M₂) * (Z : M₂) = Matrix.scalar (Fin 2) (c : F)) ∧
          ∀ c : F, (Z : M₂) ≠ Matrix.scalar (Fin 2) c) ∧
      (∀ (d : Subgroup.centralizer ({z} : Set (coordinateD F))) (A Z : GL (Fin 2) F),
        coordinateGLAction F A = ((d : coordinateD F) : Equiv.Perm (Omega F)) →
        coordinateGLAction F Z = z →
        (A : M₂) * (Z : M₂) * ((A⁻¹ : GL (Fin 2) F) : M₂) =
            ((projInvolutionSignHom hF z hz d : ℤ) : F) • (Z : M₂) ∧
          ∀ ε : ℤˣ, (A : M₂) * (Z : M₂) * ((A⁻¹ : GL (Fin 2) F) : M₂) =
            ((ε : ℤ) : F) • (Z : M₂) → ε = projInvolutionSignHom hF z hz d) ∧
      (∀ Z : GL (Fin 2) F, coordinateGLAction F Z = z →
        ∀ d : Subgroup.centralizer ({z} : Set (coordinateD F)),
          d ∈ (projInvolutionSignHom hF z hz).ker ↔ ∃ A : GL (Fin 2) F,
            coordinateGLAction F A = ((d : coordinateD F) : Equiv.Perm (Omega F)) ∧
              A * Z = Z * A) ∧
      (∀ d₁ ∈ (projInvolutionSignHom hF z hz).ker, ∀ d₂ ∈ (projInvolutionSignHom hF z hz).ker,
        d₁ * d₂ = d₂ * d₁) ∧
      ∀ d, d ∉ (projInvolutionSignHom hF z hz).ker → orderOf d = 2) ∧
    ∀ r : ℕ, 3 ≤ r → ∀ H : Subgroup (Equiv.Perm (Omega F)), H ≤ coordinateD F →
      IsEmpty (H ≃* QuaternionGroup (2 ^ (r - 2))) := by
  refine ⟨fun z hz => ⟨fun Z hZ => ?_, fun d A Z hA hZ => ?_, fun Z hZ d =>
    mem_ker_projInvolutionSignHom_iff hF hz hZ d, fun d₁ h₁ d₂ h₂ =>
    ker_projInvolutionSignHom_commute hF hz h₁ h₂, fun d hd =>
    orderOf_eq_two_of_not_mem_ker hF hz hd⟩, fun r hr H hH => ⟨fun e => ?_⟩⟩
  · obtain ⟨h1, h2⟩ := lift_conditions_of_involution hz hZ
    obtain ⟨hc, hZc⟩ := lift_of_projective_involution h1 h2
    exact ⟨hc, ne_scalar_of_not_mem_center hZc⟩
  · have hspec := projInvolutionSignHom_spec hF hz d hA hZ
    refine ⟨conj_eq_smul_iff.mpr hspec, fun ε hε => ?_⟩
    exact sign_unique hF ((conj_eq_smul_iff.mp hε).symm.trans hspec)
  · have hn : 2 ≤ 2 ^ (r - 2) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (r - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact not_injective_quaternion_coordinateD hF hn
      ((Subgroup.inclusion hH).comp e.symm.toMonoidHom)
      ((Subgroup.inclusion_injective hH).comp e.symm.injective)

end CFSG.RankThree.Classical.SteinbergBY
