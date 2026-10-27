module

public import CFSG.Quasithin.H13.AS91Sec5Local
public import CFSG.Quasithin.H13.AS91Sec8AutElem
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisGL3

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

theorem Z_le_R : c.Z ≤ c.R := by
  intro x hx
  rw [← c.center_R] at hx
  obtain ⟨r, -, rfl⟩ := Subgroup.mem_map.mp hx
  exact r.2

theorem Z_comm_R {x : G} (hx : x ∈ c.Z) {y : G} (hy : y ∈ c.R) : x * y = y * x := by
  rw [← c.center_R] at hx
  obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hx
  have := Subgroup.mem_center_iff.mp hr ⟨y, hy⟩
  have h2 := congrArg Subtype.val this
  exact h2.symm

theorem Z_comm {x y : G} (hx : x ∈ c.Z) (hy : y ∈ c.Z) : x * y = y * x :=
  c.Z_comm_R hx (c.Z_le_R hy)

theorem R_le_CZ : c.R ≤ c.CZ := by
  rw [← c.K_inf]; exact inf_le_right

theorem mem_R_iff {r : G} : r ∈ c.R ↔ r ∈ c.K ∧ r ∈ c.CZ := by
  rw [← c.K_inf]; exact Subgroup.mem_inf

theorem K_conj_Z {k : G} (hk : k ∈ c.K) {x : G} (hx : x ∈ c.Z) : k * x * k⁻¹ ∈ c.Z :=
  (Subgroup.mem_normalizer_iff.mp (c.K_le_G2 hk) x).mp hx

theorem K_conj_Z' {k : G} (hk : k ∈ c.K) {x : G} (hx : x ∈ c.Z) : k⁻¹ * x * k ∈ c.Z := by
  simpa using c.K_conj_Z (inv_mem hk) hx

theorem R_conj {k : G} (hk : k ∈ c.K) {r : G} (hr : r ∈ c.R) : k * r * k⁻¹ ∈ c.R := by
  obtain ⟨hrK, hrC⟩ := c.mem_R_iff.mp hr
  rw [c.mem_R_iff]
  refine ⟨mul_mem (mul_mem hk hrK) (inv_mem hk), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hx' := c.K_conj_Z' hk hx
  have h1 : (k⁻¹ * x * k) * r = r * (k⁻¹ * x * k) :=
    Subgroup.mem_centralizer_iff.mp hrC _ hx'
  calc x * (k * r * k⁻¹) = k * ((k⁻¹ * x * k) * r) * k⁻¹ := by group
    _ = k * (r * (k⁻¹ * x * k)) * k⁻¹ := by rw [h1]
    _ = (k * r * k⁻¹) * x := by group

theorem R_conj_G2 {g : G} (hg : g ∈ c.G2) {r : G} (hr : r ∈ c.R) : g * r * g⁻¹ ∈ c.R := by
  obtain ⟨hrK, hrC⟩ := c.mem_R_iff.mp hr
  rw [c.mem_R_iff]
  refine ⟨c.K_normal g hg r hrK, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hx' : g⁻¹ * x * g ∈ c.Z := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) x).mp hx
    simpa using this
  have h1 : (g⁻¹ * x * g) * r = r * (g⁻¹ * x * g) :=
    Subgroup.mem_centralizer_iff.mp hrC _ hx'
  calc x * (g * r * g⁻¹) = g * ((g⁻¹ * x * g) * r) * g⁻¹ := by group
    _ = g * (r * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
    _ = (g * r * g⁻¹) * x := by group

theorem K_cent_R_le_Z {k : G} (hk : k ∈ c.K) (h : ∀ r ∈ c.R, r * k = k * r) : k ∈ c.Z := by
  have hkC : k ∈ c.CZ := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact h x (c.Z_le_R hx)
  have hkR : k ∈ c.R := c.mem_R_iff.mpr ⟨hk, hkC⟩
  rw [← c.center_R]
  refine Subgroup.mem_map.mpr ⟨⟨k, hkR⟩, ?_, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (h g g.2)

theorem R_le_G3 : c.R ≤ c.G3 := c.R_le_CZ.trans c.CZ_le_G3

theorem z_ne_one (hJ : HypJ4 G z) : z ≠ 1 := by
  intro h
  have := hJ.orderOf_z
  rw [h, orderOf_one] at this
  exact absurd this (by norm_num)

@[expose] noncomputable def actKZ : ↥c.K →* MulAut ↥c.Z :=
  (conjNormalizer c.Z).comp (Subgroup.inclusion c.K_le_G2)

theorem actKZ_apply (k : ↥c.K) (x : ↥c.Z) : ((c.actKZ k x : ↥c.Z) : G) = k * x * k⁻¹ := rfl

theorem mem_ker_actKZ {k : ↥c.K} : k ∈ c.actKZ.ker ↔ (k : G) ∈ c.R := by
  rw [MonoidHom.mem_ker, c.mem_R_iff]
  constructor
  · intro h
    refine ⟨k.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := congrArg (fun f : MulAut ↥c.Z => ((f ⟨x, hx⟩ : ↥c.Z) : G)) h
    simp only [c.actKZ_apply, MulAut.one_apply, Subgroup.coe_inv] at h1
    calc x * k = (k * x * (k : G)⁻¹) * k := by rw [h1]
      _ = k * x := by group
  · rintro ⟨-, hk⟩
    ext x
    rw [c.actKZ_apply, MulAut.one_apply, Subgroup.coe_inv, mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_centralizer_iff.mp hk x x.2).symm

theorem index_R_K : (c.R.subgroupOf c.K).index = 168 := by
  obtain ⟨φ, hφs, hφk⟩ := c.K_quot
  rw [← hφk, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hφs, Subgroup.card_top]
  exact CFSG.ComponentClassification.GHarris.card_GL32_gh

theorem ker_actKZ : c.actKZ.ker = c.R.subgroupOf c.K := by
  ext k
  rw [c.mem_ker_actKZ, Subgroup.mem_subgroupOf]

theorem Z_comm' : ∀ a b : ↥c.Z, a * b = b * a := fun a b => Subtype.ext (c.Z_comm a.2 b.2)

theorem Z_sq' : ∀ a : ↥c.Z, a * a = 1 := fun a => Subtype.ext (c.Z_sq a a.2)

theorem actKZ_range_eq_top : c.actKZ.range = ⊤ := by
  have h1 := elem8_card_mulAut_le c.Z_comm' c.Z_sq' c.card_Z
  have h2 : Nat.card c.actKZ.range = 168 := by
    have := Subgroup.index_ker c.actKZ
    rw [c.ker_actKZ, c.index_R_K] at this
    exact this.symm
  apply Subgroup.eq_top_of_card_eq
  have h3 := Subgroup.card_le_card_group c.actKZ.range
  omega

theorem actKZ_surjective : Function.Surjective c.actKZ :=
  MonoidHom.range_eq_top.mp c.actKZ_range_eq_top

theorem exists_mem_K_conj_eq (f : MulAut ↥c.Z) :
    ∃ k : ↥c.K, ∀ x : ↥c.Z, ((f x : ↥c.Z) : G) = k * x * (k : G)⁻¹ := by
  obtain ⟨k, rfl⟩ := c.actKZ_surjective f
  exact ⟨k, fun x => by rw [c.actKZ_apply, Subgroup.coe_inv]⟩

end Loc49

end CFSG.Quasithin.H13.AS91
