module

public import CFSG.RankThree.Chevalley.SteinbergBIE6D4Layers
public import CFSG.RankThree.E6.NativeTwoA2

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Classical2
  Matrix
open scoped MatrixGroups Pointwise

variable (Ω : Type) [Field Ω]

@[expose] def a2Inv₁ : SL(3, Ω) →* ModGL Tag.E6 Ω :=
  (subsystemGroup Tag.E6 Ω support13).subtype.comp (a2Equiv₁ Ω).symm.toMonoidHom

@[expose] def a2Inv₂ : SL(3, Ω) →* ModGL Tag.E6 Ω :=
  (subsystemGroup Tag.E6 Ω support56).subtype.comp (a2Equiv₂ Ω).symm.toMonoidHom

variable {Ω}

theorem a2Inv₁_eq_iff {X : SL(3, Ω)} {g : ModGL Tag.E6 Ω}
    (hg : g ∈ subsystemGroup Tag.E6 Ω support13) :
    a2Inv₁ Ω X = g ↔ (X : Matrix (Fin 3) (Fin 3) Ω) = a2Mat₁ g := by
  constructor
  · rintro rfl
    change _ = a2Mat₁ (((a2Equiv₁ Ω).symm X : subsystemGroup Tag.E6 Ω support13) : ModGL Tag.E6 Ω)
    rw [← coe_a2Rep₁]
    exact congrArg Subtype.val ((a2Equiv₁ Ω).apply_symm_apply X).symm
  · intro h
    have e : (a2Equiv₁ Ω).symm X = ⟨g, hg⟩ := by
      rw [MulEquiv.symm_apply_eq]
      exact Subtype.ext h
    change (((a2Equiv₁ Ω).symm X : subsystemGroup Tag.E6 Ω support13) : ModGL Tag.E6 Ω) = g
    rw [e]

theorem a2Inv₂_eq_iff {X : SL(3, Ω)} {g : ModGL Tag.E6 Ω}
    (hg : g ∈ subsystemGroup Tag.E6 Ω support56) :
    a2Inv₂ Ω X = g ↔ (X : Matrix (Fin 3) (Fin 3) Ω) = a2Mat₂ g := by
  constructor
  · rintro rfl
    change _ = a2Mat₂ (((a2Equiv₂ Ω).symm X : subsystemGroup Tag.E6 Ω support56) : ModGL Tag.E6 Ω)
    rw [← coe_a2Rep₂]
    exact congrArg Subtype.val ((a2Equiv₂ Ω).apply_symm_apply X).symm
  · intro h
    have e : (a2Equiv₂ Ω).symm X = ⟨g, hg⟩ := by
      rw [MulEquiv.symm_apply_eq]
      exact Subtype.ext h
    change (((a2Equiv₂ Ω).symm X : subsystemGroup Tag.E6 Ω support56) : ModGL Tag.E6 Ω) = g
    rw [e]

theorem coe_transvection {a b : Fin 3} (hab : a ≠ b) (t : Ω) :
    ((SpecialLinearGroup.transvection hab t : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) =
      1 + single a b t :=
  rfl

theorem range_a2Inv₁ : (a2Inv₁ Ω).range = subsystemGroup Tag.E6 Ω support13 := by
  ext g
  constructor
  · rintro ⟨X, rfl⟩
    exact ((a2Equiv₁ Ω).symm X).2
  · intro hg
    exact ⟨a2Equiv₁ Ω ⟨g, hg⟩, by
      change (((a2Equiv₁ Ω).symm (a2Equiv₁ Ω ⟨g, hg⟩) : subsystemGroup Tag.E6 Ω support13) :
        ModGL Tag.E6 Ω) = g
      rw [MulEquiv.symm_apply_apply]⟩

theorem range_a2Inv₂ : (a2Inv₂ Ω).range = subsystemGroup Tag.E6 Ω support56 := by
  ext g
  constructor
  · rintro ⟨X, rfl⟩
    exact ((a2Equiv₂ Ω).symm X).2
  · intro hg
    exact ⟨a2Equiv₂ Ω ⟨g, hg⟩, by
      change (((a2Equiv₂ Ω).symm (a2Equiv₂ Ω ⟨g, hg⟩) : subsystemGroup Tag.E6 Ω support56) :
        ModGL Tag.E6 Ω) = g
      rw [MulEquiv.symm_apply_apply]⟩

theorem isA2Layer_a2Inv₁ : IsA2Layer (a2Inv₁ Ω) support13 (e6Index 0) (e6Index 2) where
  injective := Subtype.val_injective.comp (a2Equiv₁ Ω).symm.injective
  range_eq := range_a2Inv₁
  mem_iff := mem_support13
  x_i t := (a2Inv₁_eq_iff (xUnit_mem_subsystemGroup e6Index_0_mem_support13 t)).2
    (by rw [coe_transvection, a2Mat₁_x1])
  x_j t := (a2Inv₁_eq_iff (xUnit_mem_subsystemGroup e6Index_2_mem_support13 t)).2
    (by rw [coe_transvection, a2Mat₁_x3])
  y_i t := (a2Inv₁_eq_iff (yUnit_mem_subsystemGroup e6Index_0_mem_support13 t)).2
    (by rw [coe_transvection, a2Mat₁_y1])
  y_j t := (a2Inv₁_eq_iff (yUnit_mem_subsystemGroup e6Index_2_mem_support13 t)).2
    (by rw [coe_transvection, a2Mat₁_y3])

theorem isA2Layer_a2Inv₂ : IsA2Layer (a2Inv₂ Ω) support56 (e6Index 4) (e6Index 5) where
  injective := Subtype.val_injective.comp (a2Equiv₂ Ω).symm.injective
  range_eq := range_a2Inv₂
  mem_iff := mem_support56
  x_i t := (a2Inv₂_eq_iff (xUnit_mem_subsystemGroup e6Index_4_mem_support56 t)).2
    (by rw [coe_transvection, a2Mat₂_x5])
  x_j t := (a2Inv₂_eq_iff (xUnit_mem_subsystemGroup e6Index_5_mem_support56 t)).2
    (by rw [coe_transvection, a2Mat₂_x6])
  y_i t := (a2Inv₂_eq_iff (yUnit_mem_subsystemGroup e6Index_4_mem_support56 t)).2
    (by rw [coe_transvection, a2Mat₂_y5])
  y_j t := (a2Inv₂_eq_iff (yUnit_mem_subsystemGroup e6Index_5_mem_support56 t)).2
    (by rw [coe_transvection, a2Mat₂_y6])

theorem a2CertOK_13 : a2CertOK (e6Index 0 : Fin Tag.E6.rank) (e6Index 2 : Fin Tag.E6.rank) = true :=
  a2CertOK_02

theorem a2CertOK_56 : a2CertOK (e6Index 4 : Fin Tag.E6.rank) (e6Index 5 : Fin Tag.E6.rank) = true :=
  a2CertOK_45

@[expose] def twoA2SplitLayer {k : Type} [Field k] (ι : k →+* Ω) : Subgroup (ModGL Tag.E6 Ω) :=
  ((twoA2Mul Ω).comp ((SpecialLinearGroup.map ι).prodMap (SpecialLinearGroup.map ι))).range

@[expose] def twoA2UnitaryLayer (q : ℕ) (A₁ A₂ : GL (Fin 3) Ω) : Set (ModGL Tag.E6 Ω) :=
  twoA2Mul Ω '' {XY | SpecialLinearGroup.toGL XY.1 ∈ (fun Y => A₁ * Y * A₁⁻¹) '' unitarySet q 3 ∧
    SpecialLinearGroup.toGL XY.2 ∈ (fun Y => A₂ * Y * A₂⁻¹) '' unitarySet q 3}

theorem twoA2Mul_eq (X Y : SL(3, Ω)) : twoA2Mul Ω (X, Y) = a2Inv₁ Ω X * a2Inv₂ Ω Y :=
  twoA2Mul_apply X Y

theorem twoA2SplitLayer_eq {k : Type} [Field k] (ι : k →+* Ω) :
    (twoA2SplitLayer ι : Set (ModGL Tag.E6 Ω)) =
      (splitLayer (a2Inv₁ Ω) ι : Set (ModGL Tag.E6 Ω)) * splitLayer (a2Inv₂ Ω) ι := by
  ext g
  constructor
  · rintro ⟨⟨A, B⟩, rfl⟩
    exact ⟨_, ⟨A, rfl⟩, _, ⟨B, rfl⟩, (twoA2Mul_eq _ _).symm⟩
  · rintro ⟨_, ⟨A, rfl⟩, _, ⟨B, rfl⟩, rfl⟩
    exact ⟨(A, B), twoA2Mul_eq _ _⟩

theorem twoA2UnitaryLayer_eq (q : ℕ) (A₁ A₂ : GL (Fin 3) Ω) :
    twoA2UnitaryLayer q A₁ A₂ = unitaryLayer (a2Inv₁ Ω) q A₁ * unitaryLayer (a2Inv₂ Ω) q A₂ := by
  ext g
  constructor
  · rintro ⟨⟨X, Y⟩, ⟨hX, hY⟩, rfl⟩
    exact ⟨_, ⟨X, hX, rfl⟩, _, ⟨Y, hY, rfl⟩, (twoA2Mul_eq _ _).symm⟩
  · rintro ⟨_, ⟨X, hX, rfl⟩, _, ⟨Y, hY, rfl⟩, rfl⟩
    exact ⟨(X, Y), ⟨hX, hY⟩, twoA2Mul_eq _ _⟩

theorem range_twoA2Mul_eq :
    Set.range (twoA2Mul Ω) = (subsystemGroup Tag.E6 Ω support13 : Set (ModGL Tag.E6 Ω)) *
      (subsystemGroup Tag.E6 Ω support56 : Set (ModGL Tag.E6 Ω)) :=
  range_twoA2Mul

theorem one_mem_unitarySet {q : ℕ} (hq : 1 ≤ q) : (1 : GL (Fin 3) Ω) ∈ unitarySet q 3 := by
  have h0 : (0 : Ω) ^ q ^ 2 = 0 := zero_pow (by positivity)
  refine ⟨fun i j => ?_, by simp, ?_⟩
  · rw [Units.val_one, Matrix.one_apply]
    split_ifs
    · exact one_pow _
    · exact h0
  · have h0' : (0 : Ω) ^ q = 0 := zero_pow (by omega)
    rw [Units.val_one]
    have : (1 : Matrix (Fin 3) (Fin 3) Ω).map (· ^ q) = 1 := by
      ext i j
      rw [Matrix.map_apply, Matrix.one_apply]
      split_ifs
      · exact one_pow _
      · exact h0'
    rw [this, Matrix.transpose_one, Matrix.one_mul]

theorem one_mem_unitaryLayer (ψ : SL(3, Ω) →* ModGL Tag.E6 Ω) {q : ℕ} (hq : 1 ≤ q)
    (A : GL (Fin 3) Ω) : (1 : ModGL Tag.E6 Ω) ∈ unitaryLayer ψ q A :=
  ⟨1, ⟨1, one_mem_unitarySet hq, by
    change A * 1 * A⁻¹ = SpecialLinearGroup.toGL 1
    rw [mul_one, mul_inv_cancel, map_one]⟩, map_one ψ⟩

theorem mul_one_mem_mul {S T : Set (ModGL Tag.E6 Ω)} (hT : 1 ∈ T) {g : ModGL Tag.E6 Ω}
    (hg : g ∈ S) : g ∈ S * T :=
  ⟨g, hg, 1, hT, mul_one g⟩

theorem injective_simpleRootSL2_map {k : Type} [Field k] (ι : k →+* Ω) (i : Fin Tag.E6.rank) :
    Function.Injective fun B : SL(2, k) =>
      simpleRootSL2 Tag.E6 Ω i (SpecialLinearGroup.map ι B) := by
  have hmap : Function.Injective (SpecialLinearGroup.map (n := Fin 2) ι) :=
    fun X Y hXY => Subtype.ext (Matrix.ext fun a b => ι.injective (congrFun (congrFun
      (congrArg Subtype.val hXY) a) b))
  exact (simpleRootSL2_injective_of_field Tag.E6 i).comp hmap

theorem E6_finite_A2_D4_layers_detect_full_module_commutants (ℓ d : ℕ) (hℓ : ℓ.Prime)
    (hd : 1 ≤ d) (k : Type) [Field k] (hk : Nat.card k = ℓ ^ d) (Ω : Type) [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ (ℓ ^ d)) :
    IsA2Layer (a2Inv₁ Ω) support13 (e6Index 0) (e6Index 2) ∧
    IsA2Layer (a2Inv₂ Ω) support56 (e6Index 4) (e6Index 5) ∧
    e6Commutant (splitLayer (a2Inv₁ Ω) (algebraMap k Ω) : Set (ModGL Tag.E6 Ω)) =
      e6Commutant (subsystemGroup Tag.E6 Ω support13 : Set (ModGL Tag.E6 Ω)) ∧
    (3 ≤ ℓ ^ d → ∀ A : GL (Fin 3) Ω,
      e6Commutant (unitaryLayer (a2Inv₁ Ω) (ℓ ^ d) A) =
        e6Commutant (subsystemGroup Tag.E6 Ω support13 : Set (ModGL Tag.E6 Ω))) ∧
    (∀ e, e = 1 ∨ e = 2 →
      e6Commutant (d4Layer Fr e : Set (ModGL Tag.E6 Ω)) =
        e6Commutant (subsystemGroup Tag.E6 Ω d4Support : Set (ModGL Tag.E6 Ω))) ∧
    (∀ (P Q : Set (ModGL Tag.E6 Ω)) (m : ModGL Tag.E6 Ω), e6Commutant P = e6Commutant Q →
      e6Commutant ((fun g => m * g * m⁻¹) '' P) = e6Commutant ((fun g => m * g * m⁻¹) '' Q)) ∧
    (∀ m : ModGL Tag.E6 Ω,
      e6Commutant ((fun g => m * g * m⁻¹) '' (splitLayer (a2Inv₁ Ω) (algebraMap k Ω) :
          Set (ModGL Tag.E6 Ω))) =
        e6Commutant ((fun g => m * g * m⁻¹) ''
          (subsystemGroup Tag.E6 Ω support13 : Set (ModGL Tag.E6 Ω))) ∧
      (3 ≤ ℓ ^ d → ∀ A : GL (Fin 3) Ω,
        e6Commutant ((fun g => m * g * m⁻¹) '' unitaryLayer (a2Inv₁ Ω) (ℓ ^ d) A) =
          e6Commutant ((fun g => m * g * m⁻¹) ''
            (subsystemGroup Tag.E6 Ω support13 : Set (ModGL Tag.E6 Ω)))) ∧
      (∀ e, e = 1 ∨ e = 2 →
        e6Commutant ((fun g => m * g * m⁻¹) '' (d4Layer Fr e : Set (ModGL Tag.E6 Ω))) =
          e6Commutant ((fun g => m * g * m⁻¹) ''
            (subsystemGroup Tag.E6 Ω d4Support : Set (ModGL Tag.E6 Ω)))) ∧
      e6Commutant ((fun g => m * g * m⁻¹) '' (twoA2SplitLayer (algebraMap k Ω) :
          Set (ModGL Tag.E6 Ω))) =
        e6Commutant ((fun g => m * g * m⁻¹) '' Set.range (twoA2Mul Ω)) ∧
      (3 ≤ ℓ ^ d → ∀ A₁ A₂ : GL (Fin 3) Ω,
        e6Commutant ((fun g => m * g * m⁻¹) '' twoA2UnitaryLayer (ℓ ^ d) A₁ A₂) =
          e6Commutant ((fun g => m * g * m⁻¹) '' Set.range (twoA2Mul Ω)))) ∧
    e6Commutant (twoA2SplitLayer (algebraMap k Ω) : Set (ModGL Tag.E6 Ω)) =
      e6Commutant (Set.range (twoA2Mul Ω)) ∧
    (3 ≤ ℓ ^ d → ∀ A₁ A₂ : GL (Fin 3) Ω,
      e6Commutant (twoA2UnitaryLayer (ℓ ^ d) A₁ A₂) = e6Commutant (Set.range (twoA2Mul Ω))) ∧
    Function.Injective (fun B : SL(2, k) =>
      simpleRootSL2 Tag.E6 Ω (e6Index 0) (SpecialLinearGroup.map (algebraMap k Ω) B)) ∧
    Function.Injective (fun B : SL(2, k) =>
      simpleRootSL2 Tag.E6 Ω (d4Idx 2) (SpecialLinearGroup.map (algebraMap k Ω) B)) ∧
    (∀ B : SL(2, k), simpleRootSL2 Tag.E6 Ω (e6Index 0)
      (SpecialLinearGroup.map (algebraMap k Ω) B) ∈ splitLayer (a2Inv₁ Ω) (algebraMap k Ω)) ∧
    (3 ≤ ℓ ^ d → ∀ A : GL (Fin 3) Ω, ∃ g ∈ subsystemGroup Tag.E6 Ω support13, ∀ B : SL(2, k),
      g * simpleRootSL2 Tag.E6 Ω (e6Index 0) (SpecialLinearGroup.map (algebraMap k Ω) B) * g⁻¹ ∈
        unitaryLayer (a2Inv₁ Ω) (ℓ ^ d) A) ∧
    (∀ e, e = 1 ∨ e = 2 → ∀ B : SL(2, k), simpleRootSL2 Tag.E6 Ω (d4Idx 2)
      (SpecialLinearGroup.map (algebraMap k Ω) B) ∈ d4Layer Fr e) ∧
    (∀ B : SL(2, k), simpleRootSL2 Tag.E6 Ω (e6Index 0)
      (SpecialLinearGroup.map (algebraMap k Ω) B) ∈ twoA2SplitLayer (algebraMap k Ω)) ∧
    (3 ≤ ℓ ^ d → ∀ A₁ A₂ : GL (Fin 3) Ω, ∃ g ∈ Set.range (twoA2Mul Ω), ∀ B : SL(2, k),
      g * simpleRootSL2 Tag.E6 Ω (e6Index 0) (SpecialLinearGroup.map (algebraMap k Ω) B) * g⁻¹ ∈
        twoA2UnitaryLayer (ℓ ^ d) A₁ A₂) := by
  have : CharP k ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hℓ hd hk
  have : CharP Ω ℓ := charP_of_card hℓ hd hk (algebraMap k Ω)
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  obtain ⟨_, hcard⟩ := fintype_card_of_natCard hℓ hk
  have h1 := isA2Layer_a2Inv₁ (Ω := Ω)
  have h2 := isA2Layer_a2Inv₂ (Ω := Ω)
  have hq1 : 1 ≤ ℓ ^ d := Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ hℓ.ne_zero)
  have hsplit₁ := h1.e6Commutant_splitLayer a2CertOK_13 hℓ hd hk (algebraMap k Ω)
  have hsplit₂ := h2.e6Commutant_splitLayer a2CertOK_56 hℓ hd hk (algebraMap k Ω)
  have hunit₁ := fun hq A => h1.e6Commutant_unitaryLayer hℓ hd hk hq A
  have hunit₂ := fun hq A => h2.e6Commutant_unitaryLayer hℓ hd hk hq A
  have hD := fun e (he : e = 1 ∨ e = 2) => e6Commutant_d4Layer (Ω := Ω) hℓ hd hFr he
  have hι : ∀ b : k, algebraMap k Ω b ^ (ℓ ^ d) = algebraMap k Ω b := fun b => by
    rw [← map_pow, ← hcard, FiniteField.pow_card]
  have htwo : e6Commutant (twoA2SplitLayer (algebraMap k Ω) : Set (ModGL Tag.E6 Ω)) =
      e6Commutant (Set.range (twoA2Mul Ω)) := by
    rw [twoA2SplitLayer_eq, range_twoA2Mul_eq,
      e6Commutant_mul (one_mem (splitLayer (a2Inv₁ Ω) (algebraMap k Ω)))
        (one_mem (splitLayer (a2Inv₂ Ω) (algebraMap k Ω))),
      e6Commutant_mul (one_mem (subsystemGroup Tag.E6 Ω support13))
        (one_mem (subsystemGroup Tag.E6 Ω support56)), hsplit₁, hsplit₂]
  have htwoU : 3 ≤ ℓ ^ d → ∀ A₁ A₂ : GL (Fin 3) Ω,
      e6Commutant (twoA2UnitaryLayer (ℓ ^ d) A₁ A₂) = e6Commutant (Set.range (twoA2Mul Ω)) := by
    intro hq A₁ A₂
    rw [twoA2UnitaryLayer_eq, range_twoA2Mul_eq,
      e6Commutant_mul (one_mem_unitaryLayer _ hq1 A₁) (one_mem_unitaryLayer _ hq1 A₂),
      e6Commutant_mul (one_mem (subsystemGroup Tag.E6 Ω support13))
        (one_mem (subsystemGroup Tag.E6 Ω support56)), hunit₁ hq A₁, hunit₂ hq A₂]
  refine ⟨h1, h2, hsplit₁, hunit₁, hD, fun P Q m h => e6Commutant_conj_eq h m,
    fun m => ⟨e6Commutant_conj_eq hsplit₁ m, fun hq A => e6Commutant_conj_eq (hunit₁ hq A) m,
      fun e he => e6Commutant_conj_eq (hD e he) m, e6Commutant_conj_eq htwo m,
      fun hq A₁ A₂ => e6Commutant_conj_eq (htwoU hq A₁ A₂) m⟩, htwo, htwoU,
    injective_simpleRootSL2_map _ _, injective_simpleRootSL2_map _ _,
    h1.simpleRootSL2_mem_splitLayer _,
    fun _ A => h1.exists_conj_simpleRootSL2_mem_unitaryLayer hℓ hd hk A,
    fun e he B => simpleRootSL2_mem_d4Layer hFr he _ hι B, fun B => ?_, fun _ A₁ A₂ => ?_⟩
  · change _ ∈ (twoA2SplitLayer (algebraMap k Ω) : Set (ModGL Tag.E6 Ω))
    rw [twoA2SplitLayer_eq]
    exact mul_one_mem_mul (one_mem (splitLayer (a2Inv₂ Ω) (algebraMap k Ω)))
      (h1.simpleRootSL2_mem_splitLayer _ B)
  · obtain ⟨g, hg, hgB⟩ := h1.exists_conj_simpleRootSL2_mem_unitaryLayer hℓ hd hk A₁
    refine ⟨g, ?_, fun B => ?_⟩
    · rw [range_twoA2Mul_eq]
      exact mul_one_mem_mul (one_mem (subsystemGroup Tag.E6 Ω support56)) hg
    · rw [twoA2UnitaryLayer_eq]
      exact mul_one_mem_mul (one_mem_unitaryLayer _ hq1 A₂) (hgB B)

end CFSG.RankThree.Chevalley
