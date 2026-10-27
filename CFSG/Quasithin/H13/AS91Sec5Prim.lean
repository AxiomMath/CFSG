module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisGL3
public import CFSG.Quasithin.H13.AS91Sec5Local

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction CFSG.Quasithin.Asc94
open scoped Pointwise

@[expose] def Stmt5_Max12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (_ : HypJ4 G z) (c : Loc49 G z),
    (∀ L : Subgroup G, c.G1 ⊓ c.G2 ≤ L → L ≤ c.G1 → L = c.G1 ⊓ c.G2 ∨ L = c.G1) ∧
    ∃ g ∈ c.G1, g ∉ normalizer ((c.G1 ⊓ c.G2 : Subgroup G) : Set G)

@[expose] def Stmt5_Max13 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (_ : HypJ4 G z) (c : Loc49 G z),
    ∀ L : Subgroup G, c.G3 ⊓ c.G1 ≤ L → L ≤ c.G3 → L = c.G3 ⊓ c.G1 ∨ L = c.G3

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

theorem G13_le_inf : c.G13 ≤ c.G1 ⊓ c.G3 := by
  intro g hg
  refine Subgroup.mem_inf.mpr ⟨?_, c.G13_le hg⟩
  rw [Subgroup.mem_normalizer_iff]
  intro e
  refine ⟨fun he => c.E_normal g hg e he, fun h => ?_⟩
  have := c.E_normal g⁻¹ (inv_mem hg) _ h
  simpa [mul_assoc] using this

theorem card_G1_inf_G2 : Nat.card ↥(c.G1 ⊓ c.G2) = 2 ^ 17 * 1008 := by
  obtain ⟨φ, hφs, hφk⟩ := c.G12_quot
  have hG12 : c.G12 = c.G1 ⊓ c.G2 := by rw [c.G12_eq, inf_comm]
  have hRE : c.R ⊔ c.E ≤ c.G12 := by
    refine sup_le ?_ ?_
    · intro x hx
      exact c.K_le (c.R_le_K hx)
    · intro x hx
      rw [c.G12_eq]
      exact Subgroup.mem_inf.mpr ⟨c.E_le_G2 hx, c.E_le_G1 hx⟩
  have h1 := Subgroup.relIndex_mul_card (H := c.R ⊔ c.E) (K := c.G12)
  have h2 : (c.R ⊔ c.E).relIndex c.G12 = 1008 := by
    show ((c.R ⊔ c.E).subgroupOf c.G12).index = 1008
    rw [← hφk, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hφs, Subgroup.card_top,
      Nat.card_prod, Nat.card_perm, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin,
      CFSG.ComponentClassification.GHarris.card_GL32_gh]
    norm_num [Nat.factorial]
  rw [inf_eq_left.mpr hRE, c.card_RE, h2] at h1
  rw [← hG12, ← h1]
  ring

theorem G13_not_le_G2 : ¬ (c.G1 ⊓ c.G3 ≤ c.G1 ⊓ c.G2) := by
  intro h
  have h1 := Subgroup.card_le_of_le h
  have h2 := Subgroup.card_le_of_le c.G13_le_inf
  rw [c.card_G1_inf_G2] at h1
  rw [c.card_G13] at h2
  norm_num at h1 h2
  omega

theorem gen1_of_max12
    (hmax : ∀ L : Subgroup G, c.G1 ⊓ c.G2 ≤ L → L ≤ c.G1 → L = c.G1 ⊓ c.G2 ∨ L = c.G1) :
    c.G1 ≤ (c.G1 ⊓ c.G2) ⊔ (c.G1 ⊓ c.G3) := by
  rcases hmax ((c.G1 ⊓ c.G2) ⊔ (c.G1 ⊓ c.G3)) le_sup_left
    (sup_le inf_le_left inf_le_left) with h | h
  · exfalso
    apply c.G13_not_le_G2
    rw [← h]
    exact le_sup_right
  · exact h.ge

theorem G3_inf_G2_not_le_G1 : ¬ (c.G3 ⊓ c.G2 ≤ c.G1) := by
  intro h
  obtain ⟨y, hy, hyx⟩ := c.exists_pt c.card_ptsL
  obtain ⟨t, ht, htx, -⟩ := c.exists_swap_fix hy hyx
  have htG1 : t ∈ c.G1 := h (Subgroup.mem_inf.mpr ⟨c.CZ_le_G3 ht, c.CZ_le_G2 ht⟩)
  have : t • c.x0 = c.x0 := by
    have : t ∈ stabilizer G c.x0 := by rw [c.stab_x0]; exact htG1
    exact mem_stabilizer_iff.mp this
  exact hyx (htx.symm.trans this)

theorem gen3_of_max13
    (hmax : ∀ L : Subgroup G, c.G3 ⊓ c.G1 ≤ L → L ≤ c.G3 → L = c.G3 ⊓ c.G1 ∨ L = c.G3) :
    c.G3 ≤ (c.G3 ⊓ c.G1) ⊔ (c.G3 ⊓ c.G2) := by
  rcases hmax ((c.G3 ⊓ c.G1) ⊔ (c.G3 ⊓ c.G2)) le_sup_left
    (sup_le inf_le_left inf_le_left) with h | h
  · exfalso
    apply c.G3_inf_G2_not_le_G1
    intro g hg
    have : g ∈ (c.G3 ⊓ c.G1) ⊔ (c.G3 ⊓ c.G2) := Subgroup.mem_sup_right hg
    rw [h] at this
    exact (Subgroup.mem_inf.mp this).2
  · exact h.ge

end Loc49

theorem stmt5_2u_of_max (h12 : Stmt5_Max12) (h13 : Stmt5_Max13) : Stmt5_2u := by
  intro G _ _ z hJ c
  exact ⟨c.gen1_of_max12 (h12 G z hJ c).1, c.gen3_of_max13 (h13 G z hJ c)⟩

end CFSG.Quasithin.H13.AS91
