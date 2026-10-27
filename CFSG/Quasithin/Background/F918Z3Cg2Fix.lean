module

public import CFSG.Quasithin.Background.F918Z6Def
public import CFSG.Quasithin.Background.F918Z3D

public section

namespace CFSG.Quasithin

open scoped Matrix

namespace Z3Cg2

theorem card_fixV_zpowers_eq {V : Type} [CommGroup V] {G : Type} [AddCommGroup G]
    (β : V ≃* Multiplicative G) (g : MulAut V) (f : G → G)
    (hf : ∀ v : V, Multiplicative.toAdd (β (g v)) = f (Multiplicative.toAdd (β v))) :
    Nat.card ↥(fixV (Subgroup.zpowers g)) = Nat.card {M : G // f M = M} := by
  have key : ∀ v : V, v ∈ fixV (Subgroup.zpowers g) ↔
      f ((β.toEquiv.trans Multiplicative.toAdd) v) = (β.toEquiv.trans Multiplicative.toAdd) v := by
    intro v
    rw [Z3D.mem_fixV_zpowers_iff]
    change g v = v ↔ f (Multiplicative.toAdd (β v)) = Multiplicative.toAdd (β v)
    rw [← hf v]
    constructor
    · intro h
      rw [h]
    · intro h
      exact β.injective (Multiplicative.toAdd.injective h)
  exact Nat.card_congr (Equiv.subtypeEquiv (β.toEquiv.trans Multiplicative.toAdd) key)

theorem exists_mul_of_mem_sup {G : Type*} [Group G] {D X : Subgroup G}
    (hcomm : ∀ g ∈ D, ∀ x ∈ X, g * x = x * g) {j : G} (hj : j ∈ D ⊔ X) :
    ∃ y ∈ D, ∃ x ∈ X, j = y * x := by
  let S : Subgroup G :=
    { carrier := {j | ∃ y ∈ D, ∃ x ∈ X, j = y * x}
      one_mem' := ⟨1, D.one_mem, 1, X.one_mem, (mul_one 1).symm⟩
      mul_mem' := by
        rintro _ _ ⟨y, hy, x, hx, rfl⟩ ⟨y', hy', x', hx', rfl⟩
        refine ⟨y * y', D.mul_mem hy hy', x * x', X.mul_mem hx hx', ?_⟩
        calc y * x * (y' * x') = y * (x * y') * x' := by group
          _ = y * (y' * x) * x' := by rw [← hcomm y' hy' x hx]
          _ = y * y' * (x * x') := by group
      inv_mem' := by
        rintro _ ⟨y, hy, x, hx, rfl⟩
        refine ⟨y⁻¹, D.inv_mem hy, x⁻¹, X.inv_mem hx, ?_⟩
        rw [mul_inv_rev]
        have h := hcomm y hy x hx
        calc x⁻¹ * y⁻¹ = (y * x)⁻¹ := (mul_inv_rev y x).symm
          _ = (x * y)⁻¹ := by rw [h]
          _ = y⁻¹ * x⁻¹ := mul_inv_rev x y }
  have hle : D ⊔ X ≤ S := sup_le (fun y hy => ⟨y, hy, 1, X.one_mem, (mul_one y).symm⟩)
    (fun x hx => ⟨1, D.one_mem, x, hx, (one_mul x).symm⟩)
  exact hle hj

section ZSit

variable {V : Type} [CommGroup V] [Finite V] {D X G T' : Subgroup (MulAut V)} {s : MulAut V}

theorem center_eq_bot_of_simple {Q : Type*} [Group Q] [IsSimpleGroup Q] {a b : Q}
    (hab : a * b ≠ b * a) : Subgroup.center Q = ⊥ := by
  refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q)).resolve_right
    fun htop => hab ?_
  have ha : a ∈ Subgroup.center Q := by
    rw [htop]
    exact Subgroup.mem_top a
  exact (Subgroup.mem_center_iff.1 ha b).symm

theorem eq_one_of_mem_inf (hZ : Z37 D X G T' s) {z : MulAut V} (hzD : z ∈ D) (hzX : z ∈ X) :
    z = 1 := by
  have : IsSimpleGroup ↥D := hZ.simple
  obtain ⟨a, ha, b, hb, hab⟩ := hZ.nonab
  have hab' : (⟨a, ha⟩ : ↥D) * ⟨b, hb⟩ ≠ ⟨b, hb⟩ * ⟨a, ha⟩ := fun h =>
    hab (congrArg Subtype.val h)
  have hz : (⟨z, hzD⟩ : ↥D) ∈ Subgroup.center ↥D := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hZ.comm g g.2 z hzX)
  rw [center_eq_bot_of_simple hab', Subgroup.mem_bot] at hz
  exact congrArg Subtype.val hz

theorem sq_eq_one_of_mul_eq_one (hZ : Z37 D X G T' s) {y x : MulAut V} (hy : y ∈ D) (hx : x ∈ X)
    (h : (y * x) * (y * x) = 1) : y * y = 1 ∧ x * x = 1 := by
  have hyx : y * x = x * y := hZ.comm y hy x hx
  have h2 : (y * y) * (x * x) = 1 := by
    calc (y * y) * (x * x) = y * (y * x) * x := by group
      _ = y * (x * y) * x := by rw [hyx]
      _ = (y * x) * (y * x) := by group
      _ = 1 := h
  have h3 : y * y = (x * x)⁻¹ := eq_inv_of_mul_eq_one_left h2
  have hyyD : y * y ∈ D := D.mul_mem hy hy
  have hyyX : y * y ∈ X := by
    rw [h3]
    exact X.inv_mem (X.mul_mem hx hx)
  have h4 : y * y = 1 := eq_one_of_mem_inf hZ hyyD hyyX
  refine ⟨h4, ?_⟩
  rw [h4, one_mul] at h2
  exact h2

end ZSit

section Model

variable {V : Type} [CommGroup V] {D X : Subgroup (MulAut V)} {F : Type} [Field F] {d : ℕ}
  {β : V ≃* Multiplicative (Matrix (Fin d) (Fin d) F)}
  {ρ : ↥D →* Matrix.GeneralLinearGroup (Fin d) F}
  {σ : ↥X →* Matrix.GeneralLinearGroup (Fin d) F}

theorem toAdd_mul_apply (hM : IsMatModel D X β ρ σ) {y x : MulAut V} (hy : y ∈ D) (hx : x ∈ X)
    (v : V) :
    Multiplicative.toAdd (β ((y * x) v)) =
      (ρ ⟨y, hy⟩ : Matrix (Fin d) (Fin d) F) * Multiplicative.toAdd (β v) *
        ((σ ⟨x, hx⟩ : Matrix (Fin d) (Fin d) F))ᵀ := by
  have h1 : β (x v) = Multiplicative.ofAdd (Multiplicative.toAdd (β v) *
      ((σ ⟨x, hx⟩ : Matrix (Fin d) (Fin d) F))ᵀ) := hM.hσ ⟨x, hx⟩ v
  have h2 : β (y (x v)) = Multiplicative.ofAdd ((ρ ⟨y, hy⟩ : Matrix (Fin d) (Fin d) F) *
      Multiplicative.toAdd (β (x v))) := hM.hρ ⟨y, hy⟩ (x v)
  change Multiplicative.toAdd (β (y (x v))) = _
  rw [h2, toAdd_ofAdd, h1, toAdd_ofAdd, Matrix.mul_assoc]

theorem toAdd_left_apply (hM : IsMatModel D X β ρ σ) {y : MulAut V} (hy : y ∈ D) (v : V) :
    Multiplicative.toAdd (β (y v)) =
      (ρ ⟨y, hy⟩ : Matrix (Fin d) (Fin d) F) * Multiplicative.toAdd (β v) := by
  have h := hM.hρ ⟨y, hy⟩ v
  change Multiplicative.toAdd (β (y v)) = _
  rw [h, toAdd_ofAdd]

theorem toAdd_right_apply (hM : IsMatModel D X β ρ σ) {x : MulAut V} (hx : x ∈ X) (v : V) :
    Multiplicative.toAdd (β (x v)) =
      Multiplicative.toAdd (β v) * ((σ ⟨x, hx⟩ : Matrix (Fin d) (Fin d) F))ᵀ := by
  have h := hM.hσ ⟨x, hx⟩ v
  change Multiplicative.toAdd (β (x v)) = _
  rw [h, toAdd_ofAdd]

theorem rho_mul_self {y : MulAut V} (hy : y ∈ D) (h : y * y = 1) :
    (ρ ⟨y, hy⟩ : Matrix (Fin d) (Fin d) F) * (ρ ⟨y, hy⟩ : Matrix (Fin d) (Fin d) F) = 1 := by
  have h1 : (⟨y, hy⟩ : ↥D) * ⟨y, hy⟩ = 1 := Subtype.ext h
  have h2 : ρ ⟨y, hy⟩ * ρ ⟨y, hy⟩ = 1 := by rw [← map_mul, h1, map_one]
  have h3 := congrArg
    (fun u : Matrix.GeneralLinearGroup (Fin d) F => (u : Matrix (Fin d) (Fin d) F)) h2
  simpa using h3

theorem sigma_mul_self {x : MulAut V} (hx : x ∈ X) (h : x * x = 1) :
    (σ ⟨x, hx⟩ : Matrix (Fin d) (Fin d) F) * (σ ⟨x, hx⟩ : Matrix (Fin d) (Fin d) F) = 1 := by
  have h1 : (⟨x, hx⟩ : ↥X) * ⟨x, hx⟩ = 1 := Subtype.ext h
  have h2 : σ ⟨x, hx⟩ * σ ⟨x, hx⟩ = 1 := by rw [← map_mul, h1, map_one]
  have h3 := congrArg
    (fun u : Matrix.GeneralLinearGroup (Fin d) F => (u : Matrix (Fin d) (Fin d) F)) h2
  simpa using h3

theorem eq_one_of_rho_eq_one (hM : IsMatModel D X β ρ σ) {y : MulAut V} (hy : y ∈ D)
    (h : (ρ ⟨y, hy⟩ : Matrix (Fin d) (Fin d) F) = 1) : y = 1 := by
  ext v
  apply β.injective
  apply Multiplicative.toAdd.injective
  rw [toAdd_left_apply hM hy, h, Matrix.one_mul]
  rfl

theorem eq_one_of_sigma_eq_one (hM : IsMatModel D X β ρ σ) {x : MulAut V} (hx : x ∈ X)
    (h : (σ ⟨x, hx⟩ : Matrix (Fin d) (Fin d) F) = 1) : x = 1 := by
  ext v
  apply β.injective
  apply Multiplicative.toAdd.injective
  rw [toAdd_right_apply hM hx, h, Matrix.transpose_one, Matrix.mul_one]
  rfl

end Model

end Z3Cg2

end CFSG.Quasithin
