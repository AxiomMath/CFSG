module

public import CFSG.Quasithin.Background.SmithB42LnL5Inv
public import CFSG.Quasithin.Background.F918T0

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.S153G93D.ExtSq5

open CFSG.Quasithin CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.B5.Ln (mat)
open scoped Matrix

@[expose] def Indep3 {G : Type*} [Group G] (x y z : G) : Prop :=
  x ≠ 1 ∧ y ≠ 1 ∧ z ≠ 1 ∧ x * y ≠ 1 ∧ x * z ≠ 1 ∧ y * z ≠ 1 ∧ x * y * z ≠ 1

theorem Indep3.map {G H : Type*} [Group G] [Group H] (f : G →* H) (hf : Function.Injective f)
    {x y z : G} (h : Indep3 x y z) : Indep3 (f x) (f y) (f z) := by
  obtain ⟨h1, h2, h3, h12, h13, h23, h123⟩ := h
  have key : ∀ w : G, w ≠ 1 → f w ≠ 1 := fun w hw h => hw (hf (h.trans (map_one f).symm))
  refine ⟨key _ h1, key _ h2, key _ h3, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul]
    exact key _ h12
  · rw [← map_mul]
    exact key _ h13
  · rw [← map_mul]
    exact key _ h23
  · rw [← map_mul, ← map_mul]
    exact key _ h123

theorem Indep3.of_map {G H : Type*} [Group G] [Group H] (f : G →* H) {x y z : G}
    (h : Indep3 (f x) (f y) (f z)) : Indep3 x y z := by
  obtain ⟨h1, h2, h3, h12, h13, h23, h123⟩ := h
  refine ⟨fun h => h1 (by rw [h, map_one]), fun h => h2 (by rw [h, map_one]),
    fun h => h3 (by rw [h, map_one]), fun h => h12 (by rw [← map_mul, h, map_one]),
    fun h => h13 (by rw [← map_mul, h, map_one]), fun h => h23 (by rw [← map_mul, h, map_one]),
    fun h => h123 (by rw [← map_mul, ← map_mul, h, map_one])⟩

theorem injective_five {X : Type*} {a b c d e : X} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hae : a ≠ e) (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e)
    (hde : d ≠ e) : Function.Injective ![a, b, c, d, e] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> first
    | exact hab hij | exact hab hij.symm | exact hac hij | exact hac hij.symm
    | exact had hij | exact had hij.symm | exact hae hij | exact hae hij.symm
    | exact hbc hij | exact hbc hij.symm | exact hbd hij | exact hbd hij.symm
    | exact hbe hij | exact hbe hij.symm | exact hcd hij | exact hcd hij.symm
    | exact hce hij | exact hce hij.symm | exact hde hij | exact hde hij.symm

theorem Indep3.false_of_card_eq_four {X : Type*} [CommGroup X] (hX : ∀ x : X, x * x = 1)
    {H : Subgroup X} [Finite H] (hH : Nat.card H = 4) {u₁ u₂ u₃ : X}
    (h₁ : u₁ ∈ H) (h₂ : u₂ ∈ H) (h₃ : u₃ ∈ H) (hi : Indep3 u₁ u₂ u₃) : False := by
  obtain ⟨c1, c2, c3, c12, c13, c23, c123⟩ := hi
  have d12 : u₁ ≠ u₂ := fun h => c12 (by rw [h]; exact hX u₂)
  have d13 : u₁ ≠ u₃ := fun h => c13 (by rw [h]; exact hX u₃)
  have d23 : u₂ ≠ u₃ := fun h => c23 (by rw [h]; exact hX u₃)
  have e1 : u₁ ≠ u₁ * u₂ := fun h => c2 (by simpa using h.symm)
  have e2 : u₂ ≠ u₁ * u₂ := fun h => c1 (by simpa using h.symm)
  have e3 : u₃ ≠ u₁ * u₂ := fun h => c123 (by rw [← h]; exact hX u₃)
  have hinj := injective_five (X := ↥H) (a := 1) (b := ⟨u₁, h₁⟩) (c := ⟨u₂, h₂⟩)
    (d := ⟨u₃, h₃⟩) (e := ⟨u₁ * u₂, H.mul_mem h₁ h₂⟩)
    (fun h => c1 (congrArg Subtype.val h).symm) (fun h => c2 (congrArg Subtype.val h).symm)
    (fun h => c3 (congrArg Subtype.val h).symm) (fun h => c12 (congrArg Subtype.val h).symm)
    (fun h => d12 (congrArg Subtype.val h)) (fun h => d13 (congrArg Subtype.val h))
    (fun h => e1 (congrArg Subtype.val h)) (fun h => d23 (congrArg Subtype.val h))
    (fun h => e2 (congrArg Subtype.val h)) (fun h => e3 (congrArg Subtype.val h))
  have := Nat.card_le_card_of_injective _ hinj
  rw [hH, Nat.card_eq_fintype_card, Fintype.card_fin] at this
  omega

theorem conj_comm {Γ M : Type*} [Group Γ] [CommGroup M] (ρ : Γ →* MulAut M) {γ c τ : Γ}
    (h : c * γ * c⁻¹ = τ) (B : M) :
    ρ γ (ρ c⁻¹ B) * (ρ c⁻¹ B)⁻¹ = ρ c⁻¹ (ρ τ B * B⁻¹) := by
  have e : γ * c⁻¹ = c⁻¹ * τ := by
    rw [← h]
    group
  have h1 : ρ γ (ρ c⁻¹ B) = ρ c⁻¹ (ρ τ B) := by
    rw [← MulAut.mul_apply, ← map_mul, e, map_mul, MulAut.mul_apply]
  rw [h1, map_mul (ρ c⁻¹), map_inv (ρ c⁻¹)]

theorem conj_indep {Γ M : Type*} [Group Γ] [CommGroup M] (ρ : Γ →* MulAut M) {γ c τ : Γ}
    (h : c * γ * c⁻¹ = τ) {B₁ B₂ B₃ : M}
    (hi : Indep3 (ρ τ B₁ * B₁⁻¹) (ρ τ B₂ * B₂⁻¹) (ρ τ B₃ * B₃⁻¹)) :
    Indep3 (ρ γ (ρ c⁻¹ B₁) * (ρ c⁻¹ B₁)⁻¹) (ρ γ (ρ c⁻¹ B₂) * (ρ c⁻¹ B₂)⁻¹)
      (ρ γ (ρ c⁻¹ B₃) * (ρ c⁻¹ B₃)⁻¹) := by
  rw [conj_comm ρ h, conj_comm ρ h, conj_comm ρ h]
  exact Indep3.map (ρ c⁻¹).toMonoidHom (ρ c⁻¹).injective hi

@[expose] noncomputable def altAct :
    ↥(StatedSL 5 (ZMod 2)) →* MulAut (Multiplicative ↥(altMat 5)) where
  toFun γ :=
    { toFun := altMulAct γ
      invFun := altMulAct γ⁻¹
      left_inv := fun B => by rw [← altMulAct_mul, inv_mul_cancel, altMulAct_one]
      right_inv := fun B => by rw [← altMulAct_mul, mul_inv_cancel, altMulAct_one]
      map_mul' := altMulAct_mul_distrib γ }
  map_one' := MulEquiv.ext fun B => altMulAct_one B
  map_mul' γ δ := MulEquiv.ext fun B => altMulAct_mul γ δ B

@[expose] def coeM (x : Multiplicative ↥(altMat 5)) : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  ((Multiplicative.toAdd x : ↥(altMat 5)) : Matrix (Fin 5) (Fin 5) (ZMod 2))

theorem coeM_mul (x y : Multiplicative ↥(altMat 5)) : coeM (x * y) = coeM x + coeM y := rfl

theorem coeM_eq_zero_iff (x : Multiplicative ↥(altMat 5)) : coeM x = 0 ↔ x = 1 := by
  constructor
  · intro h
    apply Multiplicative.toAdd.injective
    exact Subtype.ext h
  · rintro rfl
    rfl

@[expose] def IndepMat (x y z : Matrix (Fin 5) (Fin 5) (ZMod 2)) : Prop :=
  x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧ x + y ≠ 0 ∧ x + z ≠ 0 ∧ y + z ≠ 0 ∧ x + y + z ≠ 0

instance (x y z : Matrix (Fin 5) (Fin 5) (ZMod 2)) : Decidable (IndepMat x y z) := by
  unfold IndepMat
  infer_instance

theorem indep3_of_indepMat {x y z : Multiplicative ↥(altMat 5)}
    (h : IndepMat (coeM x) (coeM y) (coeM z)) : Indep3 x y z := by
  obtain ⟨h1, h2, h3, h12, h13, h23, h123⟩ := h
  simp only [← coeM_mul] at h12 h13 h23 h123
  simp only [Indep3, ne_eq, ← coeM_eq_zero_iff]
  exact ⟨h1, h2, h3, h12, h13, h23, h123⟩

def bT1 : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![0, 0, 0, 0, 0; 0, 0, 1, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, 0, 0]

def bT2 : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![0, 0, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 0, 0]

def bT3 : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![0, 0, 0, 0, 0; 0, 0, 0, 0, 1; 0, 0, 0, 0, 0; 0, 0, 0, 0, 0; 0, 1, 0, 0, 0]

def bS1 : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![0, 0, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, 0, 1; 0, 0, 0, 0, 0; 0, 0, 1, 0, 0]

def bS2 : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![0, 0, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, 0, 1; 0, 0, 0, 1, 0]

def bS3 : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![0, 0, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 0]

theorem bT1_mem : bT1 ∈ altMat 5 := mem_altMat.2 (by decide)

theorem bT2_mem : bT2 ∈ altMat 5 := mem_altMat.2 (by decide)

theorem bT3_mem : bT3 ∈ altMat 5 := mem_altMat.2 (by decide)

theorem bS1_mem : bS1 ∈ altMat 5 := mem_altMat.2 (by decide)

theorem bS2_mem : bS2 ∈ altMat 5 := mem_altMat.2 (by decide)

theorem bS3_mem : bS3 ∈ altMat 5 := mem_altMat.2 (by decide)

theorem t0_indepMat : IndepMat (B42Ln.t0M * bT1 * B42Ln.t0Mᵀ + -bT1)
    (B42Ln.t0M * bT2 * B42Ln.t0Mᵀ + -bT2) (B42Ln.t0M * bT3 * B42Ln.t0Mᵀ + -bT3) := by
  decide

theorem s0_indepMat : IndepMat (B42Ln.s0M * bS1 * B42Ln.s0Mᵀ + -bS1)
    (B42Ln.s0M * bS2 * B42Ln.s0Mᵀ + -bS2) (B42Ln.s0M * bS3 * B42Ln.s0Mᵀ + -bS3) := by
  decide

theorem t0_indep : ∃ B₁ B₂ B₃ : Multiplicative ↥(altMat 5),
    Indep3 (altAct (specialLinearGroupEquivStatedSL 5 (ZMod 2) B42Ln.t0) B₁ * B₁⁻¹)
      (altAct (specialLinearGroupEquivStatedSL 5 (ZMod 2) B42Ln.t0) B₂ * B₂⁻¹)
      (altAct (specialLinearGroupEquivStatedSL 5 (ZMod 2) B42Ln.t0) B₃ * B₃⁻¹) :=
  ⟨Multiplicative.ofAdd ⟨bT1, bT1_mem⟩, Multiplicative.ofAdd ⟨bT2, bT2_mem⟩,
    Multiplicative.ofAdd ⟨bT3, bT3_mem⟩, indep3_of_indepMat t0_indepMat⟩

theorem s0_indep : ∃ B₁ B₂ B₃ : Multiplicative ↥(altMat 5),
    Indep3 (altAct (specialLinearGroupEquivStatedSL 5 (ZMod 2) B42Ln.s0) B₁ * B₁⁻¹)
      (altAct (specialLinearGroupEquivStatedSL 5 (ZMod 2) B42Ln.s0) B₂ * B₂⁻¹)
      (altAct (specialLinearGroupEquivStatedSL 5 (ZMod 2) B42Ln.s0) B₃ * B₃⁻¹) :=
  ⟨Multiplicative.ofAdd ⟨bS1, bS1_mem⟩, Multiplicative.ofAdd ⟨bS2, bS2_mem⟩,
    Multiplicative.ofAdd ⟨bS3, bS3_mem⟩, indep3_of_indepMat s0_indepMat⟩

theorem exists_indep3 {γ : ↥(StatedSL 5 (ZMod 2))} (h1 : γ ≠ 1) (h2 : γ * γ = 1) :
    ∃ B₁ B₂ B₃ : Multiplicative ↥(altMat 5),
      Indep3 (altAct γ B₁ * B₁⁻¹) (altAct γ B₂ * B₂⁻¹) (altAct γ B₃ * B₃⁻¹) := by
  set e := specialLinearGroupEquivStatedSL 5 (ZMod 2) with he
  have hu2 : e.symm γ * e.symm γ = 1 := by rw [← map_mul, h2, map_one]
  have hu1 : e.symm γ ≠ 1 := by
    intro h
    apply h1
    rw [← e.apply_symm_apply γ, h, map_one]
  obtain ⟨g, hg | hg⟩ := B42Ln.exists_conj_t0_or_s0 hu2 hu1
  · have hc : e g * γ * (e g)⁻¹ = e B42Ln.t0 := by
      have := congrArg e hg
      simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply] using this
    obtain ⟨B₁, B₂, B₃, hB⟩ := t0_indep
    exact ⟨altAct (e g)⁻¹ B₁, altAct (e g)⁻¹ B₂, altAct (e g)⁻¹ B₃, conj_indep altAct hc hB⟩
  · have hc : e g * γ * (e g)⁻¹ = e B42Ln.s0 := by
      have := congrArg e hg
      simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply] using this
    obtain ⟨B₁, B₂, B₃, hB⟩ := s0_indep
    exact ⟨altAct (e g)⁻¹ B₁, altAct (e g)⁻¹ B₂, altAct (e g)⁻¹ B₃, conj_indep altAct hc hB⟩

end CFSG.Quasithin.S153G93D.ExtSq5
