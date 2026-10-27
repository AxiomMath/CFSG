module

public import CFSG.Quasithin.H13.AS91Sec7Chain
public import CFSG.Quasithin.H13.AS91Sec5TwoC

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction CFSG.Quasithin.Asc94
open scoped Pointwise
open CFSG.ASVolI.ChH (IsTrio IsSextet M24g S24)

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

include c in
theorem z_ne_one_loc : z ≠ 1 := fun h => c.S.z_ne_one (c.S_z.trans h)

private theorem E_comm {e e' : G} (he : e ∈ c.E) (he' : e' ∈ c.E) : e * e' = e' * e :=
  congrArg Subtype.val (c.E_elem.1.is_comm.comm (⟨e, he⟩ : ↥c.E) ⟨e', he'⟩)

private theorem smul_x0_eq (g : G) : g • c.x0 = (g : G ⧸ c.G1) := by
  simp [Loc49.x0, basePt, MulAction.Quotient.smul_mk]

theorem z_mul_of_mem_G3 {h : G} (hh : h ∈ c.G3) : z * h = h * z := by
  have h1 := c.G3_comm_z hh
  calc z * h = h * (h⁻¹ * z * h) := by group
    _ = h * z := by rw [h1]

theorem z_smul_x0 : z • c.x0 = c.x0 := c.smul_x0_of_mem (c.E_le_G1 c.z_mem_E)

theorem exists_G3_smul_x0 {a : G ⧸ c.G1} (ha : c.OnP a c.pi0) :
    ∃ h ∈ c.G3, h • c.x0 = a := by
  obtain ⟨h, hh, rfl⟩ := (c.mem_ptsP_iff a).mp ha
  exact ⟨h, hh, c.smul_x0_eq h⟩

theorem z_smul_of_onP {a : G ⧸ c.G1} (ha : c.OnP a c.pi0) : z • a = a := by
  obtain ⟨h, hh, rfl⟩ := c.exists_G3_smul_x0 ha
  rw [← mul_smul, c.z_mul_of_mem_G3 hh, mul_smul, c.z_smul_x0]

private theorem inv_smul_mem_ptsL {h : G} (hh : h ∈ c.G1) {m : G ⧸ c.G2} (hm : h • c.l0 = m)
    {a : G ⧸ c.G1} (ha : c.OnL a m) (hax : a ≠ c.x0) : h⁻¹ • a ∈ c.ptsL ∧ h⁻¹ • a ≠ c.x0 := by
  refine ⟨?_, fun e => hax ?_⟩
  · have h1 := (cInc_smul c.G1 c.G2 h⁻¹ a m).2 ha
    rwa [← hm, inv_smul_smul] at h1
  · rw [inv_smul_eq_iff] at e
    rw [e, c.smul_x0_of_mem hh]

theorem E_transitive_line {m : G ⧸ c.G2} (hm : c.OnL c.x0 m) {a b : G ⧸ c.G1}
    (ha : c.OnL a m) (hax : a ≠ c.x0) (hb : c.OnL b m) (hbx : b ≠ c.x0) :
    ∃ e ∈ c.E, e • a = b := by
  obtain ⟨h, hmh⟩ := c.exists_G1_smul_l0 hm
  obtain ⟨ha', ha'x⟩ := c.inv_smul_mem_ptsL h.2 hmh ha hax
  obtain ⟨hb', hb'x⟩ := c.inv_smul_mem_ptsL h.2 hmh hb hbx
  obtain ⟨e, he, hea⟩ := c.E_transitive ha' hb' ha'x hb'x
  refine ⟨(h : G) * e * (h : G)⁻¹, (Subgroup.mem_normalizer_iff.mp h.2 e).mp he, ?_⟩
  rw [mul_smul, mul_smul, hea, smul_inv_smul]

theorem E_fix_all_of_fix {m : G ⧸ c.G2} (hm : c.OnL c.x0 m) {e : G} (he : e ∈ c.E)
    {a b : G ⧸ c.G1} (ha : c.OnL a m) (hax : a ≠ c.x0) (hb : c.OnL b m) (hbx : b ≠ c.x0)
    (hea : e • a = a) : e • b = b := by
  obtain ⟨e', he', he'a⟩ := c.E_transitive_line hm ha hax hb hbx
  rw [← he'a, ← mul_smul, c.E_comm he he', mul_smul, hea]

end Loc49

namespace ResM24

variable {G : Type} [Group G] [Finite G] {z : G} {c : Loc49 G z} (ρ : ResM24 c)

include ρ in
theorem E_smul_line {e : G} (he : e ∈ c.E) {m : G ⧸ c.G2} (hm : c.OnL c.x0 m) : e • m = m := by
  have heG1 : e ∈ c.G1 := c.E_le_G1 he
  have hker : ρ.φ ⟨e, heG1⟩ = 1 := by
    have h1 : (⟨e, heG1⟩ : ↥c.G1) ∈ ρ.φ.ker := by
      rw [ρ.ker_eq, Subgroup.mem_subgroupOf]
      exact he
    exact h1
  refine ρ.trio_injOn ((c.cInc_x0_smul heG1).2 hm) hm ?_
  have h2 := ρ.trio_smul_line ⟨e, heG1⟩ hm
  rw [hker, one_smul] at h2
  exact h2

include ρ in
theorem z_smul_line_of_onP {a : G ⧸ c.G1} (ha : c.OnP a c.pi0) {m : G ⧸ c.G2}
    (hm : c.OnL a m) : z • m = m := by
  obtain ⟨h, hh, hha⟩ := c.exists_G3_smul_x0 ha
  have hz := ρ.E_smul_line c.z_mem_E (c.onL_x0_inv_smul hha hm)
  calc z • m = z • h • (h⁻¹ • m) := by rw [smul_inv_smul]
    _ = h • z • (h⁻¹ • m) := by rw [← mul_smul z h, ← mul_smul h z, c.z_mul_of_mem_G3 hh]
    _ = h • (h⁻¹ • m) := by rw [hz]
    _ = m := smul_inv_smul h m

include ρ in
theorem exists_adj_z_smul_ne :
    ∃ y, c.Delta.Adj c.x0 y ∧ z • y ≠ y := by
  by_contra hcon
  push Not at hcon
  obtain ⟨-, hirr, -⟩ := @CFSG.Quasithin.H.ModelIrr.cocode24_facts ↥c.E
    (commGroupOfElem c.E_elem) (conjNormalizer c.E).range c.todd
  let F : Subgroup G := c.E ⊓ fixingSubgroup G {y | c.Delta.Adj c.x0 y}
  have hzF : z ∈ F := ⟨c.z_mem_E, (mem_fixingSubgroup_iff G).2 fun y hy => hcon y hy⟩
  have hinv : ∀ g ∈ (conjNormalizer c.E).range, ∀ u ∈ F.subgroupOf c.E,
      g u ∈ F.subgroupOf c.E := by
    rintro _ ⟨n, rfl⟩ u hu
    rw [Subgroup.mem_subgroupOf] at hu ⊢
    refine ⟨(Subgroup.mem_normalizer_iff.mp n.2 u).mp u.2,
      (mem_fixingSubgroup_iff G).2 fun y hy => ?_⟩
    have hy' : c.Delta.Adj c.x0 ((n : G)⁻¹ • y) := by
      have h1 := (CFSG.Quasithin.GraphAction.adj_smul (H := G) (Γ := c.Delta) (n : G)⁻¹ c.x0 y).2 hy
      rwa [c.smul_x0_of_mem (inv_mem n.2)] at h1
    have hfix := (mem_fixingSubgroup_iff G).1 hu.2 _ hy'
    show ((n : G) * (u : G) * (n : G)⁻¹) • y = y
    rw [mul_smul, mul_smul, hfix, smul_inv_smul]
  rcases hirr (F.subgroupOf c.E) hinv with h0 | h0
  · have h1 : (⟨z, c.z_mem_E⟩ : ↥c.E) ∈ F.subgroupOf c.E := hzF
    rw [h0, Subgroup.mem_bot] at h1
    exact c.z_ne_one_loc (congrArg Subtype.val h1)
  · obtain ⟨a, haL, hax⟩ := c.exists_pt c.card_ptsL
    obtain ⟨-, -, -, -, b, hbL, hbx, hba, -⟩ := c.exists_swap_fix haL hax
    obtain ⟨e, he, hea⟩ := c.E_transitive haL hbL hax hbx
    have heF : e ∈ F := by
      have h1 : (⟨e, he⟩ : ↥c.E) ∈ F.subgroupOf c.E := by
        rw [h0]
        exact Subgroup.mem_top _
      exact h1
    have hadj : c.Delta.Adj c.x0 a := ⟨hax.symm, c.l0, c.x0_mem_ptsL, haL⟩
    exact hba (hea.symm.trans ((mem_fixingSubgroup_iff G).1 heF.2 a hadj))

end ResM24

end CFSG.Quasithin.H13.AS91
