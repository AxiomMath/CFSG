module

public import CFSG.Quasithin.Vol2.Ch11SecANat
public import CFSG.GH74.Uniqueness.SU.SU2Sylow

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.GH74.Uniqueness.SU.SU2
open scoped Pointwise

variable {G : Type} [Group G]

@[expose] noncomputable def onanRho (Z Y : Subgroup G) (hYZ : Y ≤ Subgroup.normalizer (Z : Set G)) :
    ↥Y →* MulAut ↥Z :=
  (conjAct Z).comp (Subgroup.inclusion hYZ)

theorem onanRho_apply_coe {Z Y : Subgroup G} (hYZ : Y ≤ Subgroup.normalizer (Z : Set G))
    (y : ↥Y) (v : ↥Z) : ((onanRho Z Y hYZ y v : ↥Z) : G) = y * v * (y : G)⁻¹ :=
  conjV_apply_coe Z (hYZ y.2) v

noncomputable abbrev onanX (Z Y : Subgroup G) (hYZ : Y ≤ Subgroup.normalizer (Z : Set G)) :
    Subgroup (MulAut ↥Z) :=
  (onanRho Z Y hYZ).range

structure OnanData (Z Y T V₁ C : Subgroup G) (d : G) : Prop where
  exp2 : ∀ z ∈ Z, z * z = 1
  YZ : Y ≤ Subgroup.normalizer (Z : Set G)
  TY : T ≤ Y
  T2 : IsPGroup 2 T
  Todd : ¬ 2 ∣ T.relIndex Y
  VZ : V₁ ≤ Z
  CZ : C ≤ Z
  ZVC : Z ≤ V₁ ⊔ C
  Cne : C ≠ ⊥
  dY : d ∈ Y
  dV : d ∈ Subgroup.normalizer (V₁ : Set G)
  dC : ∀ c ∈ C, d * c = c * d
  odd : ∃ m : ℕ, Odd m ∧ ∀ z ∈ Z, d ^ m * z = z * d ^ m
  trans : ∀ v ∈ V₁, ∀ w ∈ V₁, v ∉ C → w ∉ C → ∃ k : ℕ, d ^ k * v * (d ^ k)⁻¹ * w⁻¹ ∈ C
  three : ∃ v ∈ V₁, ∃ w ∈ V₁, v ∉ C ∧ w ∉ C ∧ v * w⁻¹ ∉ C
  TI : ∀ y ∈ Y, C ⊓ C.map (MulAut.conj y).toMonoidHom ≠ ⊥ →
    C.map (MulAut.conj y).toMonoidHom = C
  norm : ∀ y ∈ Y, C.map (MulAut.conj y).toMonoidHom = C → ∃ k : ℕ, ∀ z ∈ Z,
    (y * d * y⁻¹) * z * (y * d * y⁻¹)⁻¹ = d ^ k * z * (d ^ k)⁻¹
  TC : T ≤ Subgroup.normalizer (C : Set G)

namespace OnanData

variable {Z Y T V₁ C : Subgroup G} {d : G}

theorem comm (D : OnanData Z Y T V₁ C d) : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := by
  intro a ha b hb
  have h1 := D.exp2 _ (Z.mul_mem ha hb)
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (D.exp2 a ha)
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (D.exp2 b hb)
  calc a * b = (b * a)⁻¹ := by rw [mul_inv_rev, ha', hb']
    _ = b * a := inv_eq_of_mul_eq_one_right (D.exp2 _ (Z.mul_mem hb ha))

theorem decomp (D : OnanData Z Y T V₁ C d) {z : G} (hz : z ∈ Z) :
    ∃ a ∈ V₁, ∃ c ∈ C, z = a * c := by
  have hCN : C ≤ Subgroup.normalizer (V₁ : Set G) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro v
    have hcv : ∀ v ∈ V₁, c * v * c⁻¹ = v := fun v hv => by
      rw [D.comm c (D.CZ hc) v (D.VZ hv), mul_inv_cancel_right]
    constructor
    · intro hv; rw [hcv v hv]; exact hv
    · intro hv
      have h1 := hcv _ hv
      have : v = c * v * c⁻¹ := by
        calc v = c⁻¹ * (c * v * c⁻¹) * c := by group
          _ = c⁻¹ * (c * (c * v * c⁻¹) * c⁻¹) * c := by rw [h1]
          _ = c * v * c⁻¹ := by group
      rw [this]; exact hv
  have hz' : z ∈ ((V₁ ⊔ C : Subgroup G) : Set G) := D.ZVC hz
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hCN] at hz'
  obtain ⟨a, ha, c, hc, rfl⟩ := hz'
  exact ⟨a, ha, c, hc, rfl⟩

@[expose] noncomputable def dstar (D : OnanData Z Y T V₁ C d) : ↥(onanX Z Y D.YZ) :=
  ⟨onanRho Z Y D.YZ ⟨d, D.dY⟩, ⟨_, rfl⟩⟩

theorem dstar_pow_apply_coe (D : OnanData Z Y T V₁ C d) (k : ℕ) (v : ↥Z) :
    (((D.dstar ^ k : ↥(onanX Z Y D.YZ)) : MulAut ↥Z) v : G) = d ^ k * v * (d ^ k)⁻¹ := by
  induction k generalizing v with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Subgroup.coe_mul, MulAut.mul_apply, ih]
    simp only [dstar, onanRho_apply_coe]
    group

omit [Group G] in
theorem exists_pow_of_mem_zpowers {H : Type*} [Group H] [Finite H] {x y : H}
    (h : y ∈ Subgroup.zpowers x) : ∃ n : ℕ, x ^ n = y :=
  (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr h)

theorem pow_conj_eq_of_conj_eq {a : G} (h : d * a * d⁻¹ = a) (k : ℕ) :
    d ^ k * a * (d ^ k)⁻¹ = a := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc d ^ (k + 1) * a * (d ^ (k + 1))⁻¹ = d ^ k * (d * a * d⁻¹) * (d ^ k)⁻¹ := by group
      _ = a := by rw [h, ih]

theorem conj_eq_iff (D : OnanData Z Y T V₁ C d) {z : G} (hz : z ∈ Z) :
    d * z * d⁻¹ = z ↔ z ∈ C := by
  constructor
  · intro hfix
    obtain ⟨a, ha, c, hc, rfl⟩ := D.decomp hz
    have hdc : d * c * d⁻¹ = c := by rw [D.dC c hc, mul_inv_cancel_right]
    have hda : d * a * d⁻¹ = a := by
      have : d * (a * c) * d⁻¹ = (d * a * d⁻¹) * (d * c * d⁻¹) := by group
      rw [this, hdc] at hfix
      exact mul_right_cancel hfix
    by_contra haC
    have haC' : a ∉ C := fun h => haC (C.mul_mem h hc)
    obtain ⟨v, hv, w, hw, hvC, hwC, hvw⟩ := D.three
    obtain ⟨k, hk⟩ := D.trans a ha v hv haC' hvC
    obtain ⟨k', hk'⟩ := D.trans a ha w hw haC' hwC
    rw [pow_conj_eq_of_conj_eq hda] at hk hk'
    apply hvw
    have : v * w⁻¹ = (a * v⁻¹)⁻¹ * (a * w⁻¹) := by group
    rw [this]
    exact C.mul_mem (C.inv_mem hk) hk'
  · intro hzC
    rw [D.dC z hzC, mul_inv_cancel_right]

end OnanData

end CFSG.Quasithin.Vol2.Ch11.SecA
