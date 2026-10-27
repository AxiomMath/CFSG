module

public import CFSG.Quasithin.H13.AS91Sec5Defs
public import CFSG.Quasithin.H13.AS91Sec5Ker
public import CFSG.Quasithin.Recognition.UniquenessSystemCoset

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction CFSG.Quasithin.Asc94
open scoped Pointwise

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

theorem z_mem_Z : z ∈ c.Z := by
  rw [c.Z_eq_closure]
  exact Subgroup.subset_closure (by simp)

theorem CZ_le_G2 : c.CZ ≤ c.G2 := Subgroup.centralizer_le_normalizer _

theorem CZ_le_G3 : c.CZ ≤ c.G3 := by
  intro g hg
  rw [Subgroup.mem_centralizer_iff] at hg
  rw [Loc49.G3, H, Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  rw [hh]
  exact hg _ c.z_mem_Z

theorem K_le_G2 : c.K ≤ c.G2 := fun k hk => by
  have := c.K_le hk
  rw [c.G12_eq] at this
  exact this.1

theorem K_le_G1 : c.K ≤ c.G1 := fun k hk => by
  have := c.K_le hk
  rw [c.G12_eq] at this
  exact this.2

theorem E_le_G1 : c.E ≤ c.G1 := Subgroup.le_normalizer

theorem E_le_T : c.E ≤ (c.T : Subgroup G) := by
  rw [c.E_eq]
  exact CFSG.ambientMaxCardThompson_le _

theorem E_le_G2 : c.E ≤ c.G2 := c.E_le_T.trans c.T_le_normalizer

theorem E_le_G3 : c.E ≤ c.G3 := c.E_le.trans c.G13_le

theorem mem_ptsL_iff (y : G ⧸ c.G1) : y ∈ c.ptsL ↔ ∃ g ∈ c.G2, (g : G ⧸ c.G1) = y := by
  rw [Loc49.ptsL, Loc49.l0, objOf_one]
  simp

theorem x0_mem_ptsL : c.x0 ∈ c.ptsL := basePt_mem_objOf_base c.G1 c.G2

theorem stab_x0 : stabilizer G c.x0 = c.G1 := stabilizer_mk_one c.G1

theorem card_ptsL : Nat.card c.ptsL = 5 := by
  have h1 : c.ptsL = MulAction.orbit ↥c.G2 c.x0 := by
    ext y
    rw [c.mem_ptsL_iff]
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine ⟨⟨g, hg⟩, ?_⟩
      show g • c.x0 = _
      rw [← mul_one g, mk_mul_eq_smul]
      simp
    · rintro ⟨g, rfl⟩
      refine ⟨g, g.2, ?_⟩
      show _ = (g : G) • c.x0
      rw [← mul_one (g : G), mk_mul_eq_smul]
      simp
  rw [h1, Nat.card_congr (MulAction.orbitEquivQuotientStabilizer ↥c.G2 c.x0)]
  have h2 : MulAction.stabilizer ↥c.G2 c.x0 = c.G12.subgroupOf c.G2 := by
    ext g
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, c.G12_eq, Subgroup.mem_inf]
    constructor
    · intro hg
      refine ⟨g.2, ?_⟩
      have : (g : G) ∈ stabilizer G c.x0 := mem_stabilizer_iff.mpr hg
      rwa [c.stab_x0] at this
    · rintro ⟨-, hg⟩
      have : (g : G) ∈ stabilizer G c.x0 := by rwa [c.stab_x0]
      exact mem_stabilizer_iff.mp this
  rw [h2]
  exact c.relIndex_G12

theorem G2_eq_mul {g : G} (hg : g ∈ c.G2) : ∃ k ∈ c.K, ∃ s ∈ c.CZ, k * s = g := by
  have hg' : g ∈ c.K ⊔ c.CZ := by rw [← c.normalizer_eq]; exact hg
  rw [Subgroup.sup_eq_closure_mul] at hg'
  have key : ∀ g ∈ Subgroup.closure ((c.K : Set G) * (c.CZ : Set G)), ∃ k ∈ c.K, ∃ s ∈ c.CZ,
      k * s = g := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg => obtain ⟨k, hk, s, hs, rfl⟩ := hg; exact ⟨k, hk, s, hs, rfl⟩
    | one => exact ⟨1, one_mem _, 1, one_mem _, one_mul 1⟩
    | mul a b _ _ ha hb =>
      obtain ⟨k₁, hk₁, s₁, hs₁, rfl⟩ := ha
      obtain ⟨k₂, hk₂, s₂, hs₂, rfl⟩ := hb
      have hs₁G2 : s₁ ∈ c.G2 := c.CZ_le_G2 hs₁
      refine ⟨k₁ * (s₁ * k₂ * s₁⁻¹), mul_mem hk₁ (c.K_normal s₁ hs₁G2 k₂ hk₂), s₁ * s₂,
        mul_mem hs₁ hs₂, ?_⟩
      group
    | inv a _ ha =>
      obtain ⟨k, hk, s, hs, rfl⟩ := ha
      have hsG2 : s ∈ c.G2 := c.CZ_le_G2 hs
      refine ⟨s⁻¹ * k⁻¹ * s, ?_, s⁻¹, inv_mem hs, ?_⟩
      · have := c.K_normal s⁻¹ (inv_mem hsG2) k⁻¹ (inv_mem hk)
        simpa using this
      · group
  exact key g hg'

theorem R_le_K : c.R ≤ c.K := by
  rw [← c.K_inf]; exact inf_le_left

theorem K_fix {k : G} (hk : k ∈ c.K) {p : G ⧸ c.G1} (hp : p ∈ c.ptsL) : k • p = p := by
  obtain ⟨h, hh, rfl⟩ := (c.mem_ptsL_iff p).mp hp
  have hk' : h⁻¹ * k * h ∈ c.K := by
    simpa using c.K_normal h⁻¹ (inv_mem hh) k hk
  have hx : (h⁻¹ * k * h) • c.x0 = c.x0 := by
    have := c.K_le_G1 hk'
    rw [← c.stab_x0] at this
    exact mem_stabilizer_iff.mp this
  have e : ((h : G) : G ⧸ c.G1) = h • c.x0 := by
    rw [← mul_one h, mk_mul_eq_smul]; simp
  rw [e, ← mul_smul]
  have : k * h = h * (h⁻¹ * k * h) := by group
  rw [this, mul_smul, hx]

theorem ker_CZ_le_R : ∀ g ∈ c.CZ, (∀ p ∈ c.ptsL, g • p = p) → g ∈ c.R := by
  refine ker_le_of_S5 c.G1 c.G2 c.CZ c.R c.CZ_le_G2 c.card_ptsL c.S_quot ?_ ?_
  · intro r hr p hp
    exact c.K_fix (c.R_le_K hr) hp
  · intro p hp q hq
    obtain ⟨g1, hg1, rfl⟩ := (c.mem_ptsL_iff p).mp hp
    obtain ⟨g2, hg2, rfl⟩ := (c.mem_ptsL_iff q).mp hq
    obtain ⟨k, hk, s, hs, hks⟩ := c.G2_eq_mul (mul_mem hg2 (inv_mem hg1))
    refine ⟨s, hs, ?_⟩
    have hsp : s • ((g1 : G) : G ⧸ c.G1) ∈ c.ptsL :=
      smul_mem_objOf_base (c.CZ_le_G2 hs) hp
    have h1 : (k * s) • ((g1 : G) : G ⧸ c.G1) = ((g2 : G) : G ⧸ c.G1) := by
      rw [hks, show ((g1 : G) : G ⧸ c.G1) = g1 • c.x0 by rw [← mul_one g1, mk_mul_eq_smul]; simp,
        ← mul_smul, mul_assoc, inv_mul_cancel, mul_one]
      rw [← mul_one g2, mk_mul_eq_smul]; simp
    rw [mul_smul, c.K_fix hk hsp] at h1
    exact h1

theorem kernel_ptsL : ∀ g ∈ c.G2, (∀ p ∈ c.ptsL, g • p = p) ↔ g ∈ c.K := by
  intro g hg
  constructor
  · intro hfix
    obtain ⟨k, hk, s, hs, rfl⟩ := c.G2_eq_mul hg
    have hsfix : ∀ p ∈ c.ptsL, s • p = p := by
      intro p hp
      have h1 := hfix p hp
      rw [mul_smul] at h1
      have hsp : s • p ∈ c.ptsL := smul_mem_objOf_base (c.CZ_le_G2 hs) hp
      rwa [c.K_fix hk hsp] at h1
    exact mul_mem hk (c.R_le_K (c.ker_CZ_le_R s hs hsfix))
  · intro hk p hp
    exact c.K_fix hk hp

theorem exists_pt (hcard : Nat.card c.ptsL = 5) : ∃ y ∈ c.ptsL, y ≠ c.x0 := by
  have hfin : c.ptsL.Finite := Set.toFinite _
  have h1 : 1 < c.ptsL.ncard := by
    rw [← Nat.card_coe_set_eq, hcard]; norm_num
  obtain ⟨a, b, ha, hb, hab⟩ := (Set.one_lt_ncard_iff hfin).mp h1
  by_cases ha0 : a = c.x0
  · exact ⟨b, hb, fun h => hab (ha0.trans h.symm)⟩
  · exact ⟨a, ha, ha0⟩

theorem index_R_CZ : (c.R.subgroupOf c.CZ).index = Nat.factorial 5 := by
  obtain ⟨φ, hφs, hφk⟩ := c.S_quot
  have h : φ.ker.index = Nat.factorial 5 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hφs, Subgroup.card_top, Nat.card_perm,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  rwa [hφk] at h

theorem K_le_stab {p : G ⧸ c.G1} (hp : p ∈ c.ptsL) : c.K ≤ stabilizer G p :=
  fun _ hk => mem_stabilizer_iff.mpr (c.K_fix hk hp)

theorem mem_normalizer_K {g : G} (hg : g ∈ c.G2) : g ∈ normalizer (c.K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · intro hk; exact c.K_normal g hg k hk
  · intro hk
    have := c.K_normal g⁻¹ (inv_mem hg) _ hk
    simpa [mul_assoc] using this

theorem exists_swap_fix {y : G ⧸ c.G1} (hy : y ∈ c.ptsL)
    (hyx : y ≠ c.x0) :
    ∃ t ∈ c.CZ, t • c.x0 = y ∧ t • y = c.x0 ∧
      ∃ u ∈ c.ptsL, u ≠ c.x0 ∧ u ≠ y ∧ t • u = u := by
  classical
  have hc5 := c.card_ptsL
  obtain ⟨s, hs, hsσ⟩ := exists_mem_smul_eq_perm c.G1 c.G2 c.CZ c.R c.CZ_le_G2 hc5
    c.ker_CZ_le_R c.index_R_CZ
    (Equiv.swap (⟨c.x0, c.x0_mem_ptsL⟩ : ↥c.ptsL) ⟨y, hy⟩)
  have hne : (⟨c.x0, c.x0_mem_ptsL⟩ : ↥c.ptsL) ≠ ⟨y, hy⟩ :=
    fun h => hyx (congrArg Subtype.val h).symm
  have h1 : s • c.x0 = y := by
    have := hsσ ⟨c.x0, c.x0_mem_ptsL⟩
    simpa using this
  have h2 : s • y = c.x0 := by
    have := hsσ ⟨y, hy⟩
    simpa using this
  have hfin : ({c.x0, y} : Set (G ⧸ c.G1)).Finite := Set.toFinite _
  have hlt : ({c.x0, y} : Set (G ⧸ c.G1)).ncard < c.ptsL.ncard := by
    rw [Set.ncard_pair hyx.symm, ← Nat.card_coe_set_eq, hc5]; norm_num
  obtain ⟨u, hu, hu'⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hlt hfin
  have hux : u ≠ c.x0 := fun h => hu' (Or.inl h)
  have huy : u ≠ y := fun h => hu' (Or.inr h)
  refine ⟨s, hs, h1, h2, u, hu, hux, huy, ?_⟩
  have := hsσ ⟨u, hu⟩
  have hu1 : (⟨u, hu⟩ : ↥c.ptsL) ≠ ⟨c.x0, c.x0_mem_ptsL⟩ := fun h => hux (congrArg Subtype.val h)
  have hu2 : (⟨u, hu⟩ : ↥c.ptsL) ≠ ⟨y, hy⟩ := fun h => huy (congrArg Subtype.val h)
  rw [Equiv.swap_apply_of_ne_of_ne hu1 hu2] at this
  exact this

end Loc49

end CFSG.Quasithin.H13.AS91
