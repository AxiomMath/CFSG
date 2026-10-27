module

public import CFSG.Quasithin.Vol2.Ch11SecA15GO2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.GH74.Uniqueness.SU CFSG.GH74.Uniqueness.SU.SU2
open scoped Pointwise

variable {G : Type} [Group G]

namespace OnanData

variable {Z Y T V₁ C : Subgroup G} {d : G}

theorem ystar_smul_coe (D : OnanData Z Y T V₁ C d) (y : ↥Y) (v : ↥Z) :
    ((D.ystar y • v : ↥Z) : G) = y * v * (y : G)⁻¹ :=
  onanRho_apply_coe D.YZ y v

theorem dstar_pow_smul_coe (D : OnanData Z Y T V₁ C d) (k : ℕ) (v : ↥Z) :
    ((D.dstar ^ k • v : ↥Z) : G) = d ^ k * v * (d ^ k)⁻¹ :=
  D.dstar_pow_apply_coe k v

theorem mem_map_conj_iff {W : Subgroup G} {y x : G} :
    x ∈ W.map (MulAut.conj y).toMonoidHom ↔ y⁻¹ * x * y ∈ W := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa [mul_assoc] using hw
  · intro hx
    refine ⟨_, hx, ?_⟩
    simp [mul_assoc]

theorem commSub_le [Finite G] (D : OnanData Z Y T V₁ C d) :
    SU2.commSub ↥Z (Subgroup.zpowers D.dstar) ≤ V₁.subgroupOf Z := by
  rw [SU2.commSub, Subgroup.closure_le]
  rintro _ ⟨g, hg, v, rfl⟩
  obtain ⟨k, rfl⟩ := exists_pow_of_mem_zpowers hg
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv,
    dstar_pow_smul_coe]
  obtain ⟨a, ha, c, hc, hv⟩ := D.decomp v.2
  rw [hv]
  have hdc := pow_conj_eq_of_conj_eq ((D.conj_eq_iff (D.CZ hc)).mpr hc) k
  have e : d ^ k * (a * c) * (d ^ k)⁻¹ * (a * c)⁻¹ =
      (d ^ k * a * (d ^ k)⁻¹) * (d ^ k * c * (d ^ k)⁻¹) * c⁻¹ * a⁻¹ := by group
  rw [e, hdc, mul_inv_cancel_right]
  exact V₁.mul_mem ((Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ D.dV k) a).mp ha)
    (V₁.inv_mem ha)

theorem smul_mem_commSub [Finite G] (D : OnanData Z Y T V₁ C d) {g : ↥(onanX Z Y D.YZ)}
    (hg : g ∈ Subgroup.zpowers D.dstar) {u : ↥Z}
    (hu : u ∈ SU2.commSub ↥Z (Subgroup.zpowers D.dstar)) :
    g • u ∈ SU2.commSub ↥Z (Subgroup.zpowers D.dstar) := by
  obtain ⟨j, rfl⟩ := exists_pow_of_mem_zpowers hg
  induction hu using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨y, hy, v, rfl⟩ := hx
    obtain ⟨i, rfl⟩ := exists_pow_of_mem_zpowers hy
    rw [smul_mul', smul_inv', smul_smul, ← pow_add, add_comm, pow_add, ← smul_smul]
    exact smul_mul_inv_mem_commSub hy _
  | one => rw [smul_one]; exact Subgroup.one_mem _
  | mul a b _ _ ha hb => rw [smul_mul']; exact Subgroup.mul_mem _ ha hb
  | inv a _ ha => rw [smul_inv']; exact Subgroup.inv_mem _ ha

theorem dstar_pow_eq_one (D : OnanData Z Y T V₁ C d) {m : ℕ}
    (hm : ∀ z ∈ Z, d ^ m * z = z * d ^ m) : D.dstar ^ m = 1 := by
  apply Subtype.ext
  apply MulEquiv.ext
  intro v
  apply Subtype.ext
  change ((D.dstar ^ m • v : ↥Z) : G) = v
  rw [dstar_pow_smul_coe, hm v v.2, mul_inv_cancel_right]

end OnanData

end CFSG.Quasithin.Vol2.Ch11.SecA
