module

public import CFSG.Quasithin.H13.AS91Sec7Geom
public import CFSG.Quasithin.H13.AS91Sec7Zfix

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction CFSG.Quasithin.Asc94
open scoped Pointwise

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

theorem z_smul_of_adj_far (hLU : Stmt5_LineU) (hJ : HypJ4 G z) {y u : G ⧸ c.G1}
    (hy : c.OnP y c.pi0) (hyx : y ≠ c.x0) (hxy : ¬ c.Delta.Adj c.x0 y)
    (hu : c.Delta.Adj c.x0 u) (huy : c.Delta.Adj y u) : z • u = u := by
  obtain ⟨-, m, hx0m, hum⟩ := colGraph_adj.mp hu
  obtain ⟨-, n, hyn, hun⟩ := colGraph_adj.mp huy
  have hzm : z • m = m := c.E_smul_line hx0m c.z_mem_E
  obtain ⟨h, hh, hhy⟩ := c.exists_G3_smul_x0 hy
  have hzn : z • n = n := by
    have h1 : z • h⁻¹ • n = h⁻¹ • n := c.E_smul_line (c.onL_x0_inv_smul hhy hyn) c.z_mem_E
    calc z • n = z • h • h⁻¹ • n := by rw [smul_inv_smul]
      _ = (z * h) • h⁻¹ • n := (mul_smul z h _).symm
      _ = (h * z) • h⁻¹ • n := by rw [c.z_mul_of_mem_G3 hh]
      _ = h • z • h⁻¹ • n := mul_smul h z _
      _ = h • h⁻¹ • n := by rw [h1]
      _ = n := smul_inv_smul h n
  have hzum : c.OnL (z • u) m := by
    have h1 := (cInc_smul c.G1 c.G2 z u m).2 hum
    rwa [hzm] at h1
  have hzun : c.OnL (z • u) n := by
    have h1 := (cInc_smul c.G1 c.G2 z u n).2 hun
    rwa [hzn] at h1
  by_contra hne
  have hne' : u ≠ z • u := fun h' => hne h'.symm
  have hmn : m = n := c.eq_of_onL hLU hJ hne' hum hzum hun hzun
  have hym : c.OnL y m := by
    rw [hmn]
    exact hyn
  exact hxy (c.adj_of_onL hyx.symm hx0m hym)

theorem onP_of_conj_mem_E (hJ : HypJ4 G z)
    (h2c : ∀ y ∈ c.ptsL, y ≠ c.x0 → ∀ g ∈ c.G2, g • c.x0 = y →
      (c.E.map (MulAut.conj g).toMonoidHom) ⊓ c.E = c.Z)
    {u : G ⧸ c.G1} (hu : c.Delta.Adj c.x0 u) {f : G} (hf : f • c.x0 = u)
    (hz : f⁻¹ * z * f ∈ c.E) : c.OnP u c.pi0 := by
  obtain ⟨hne, m, hx0m, hum⟩ := colGraph_adj.mp hu
  obtain ⟨w, hw1, hw2⟩ := hx0m
  obtain ⟨t, ht1, ht2⟩ := id hum
  have hwG1 : w ∈ c.G1 := (mk_eq_one_iff c.G1 w).mp hw1
  have htx : t • c.x0 = u := by
    rw [← ht1]
    simp [Loc49.x0, basePt, MulAction.Quotient.smul_mk]
  have hg₀ : w⁻¹ * t ∈ c.G2 := by
    have h1 : (w : G ⧸ c.G2) = (t : G ⧸ c.G2) := hw2.trans ht2.symm
    rwa [QuotientGroup.eq] at h1
  have hk : f⁻¹ * t ∈ c.G1 := by
    rw [← c.stab_x0]
    refine mem_stabilizer_iff.mpr ?_
    rw [mul_smul, htx, inv_smul_eq_iff, hf]
  have hzt : t⁻¹ * z * t ∈ c.E := by
    have h1 := (Subgroup.mem_normalizer_iff.mp (inv_mem hk) (f⁻¹ * z * f)).mp hz
    have e : t⁻¹ * z * t = (f⁻¹ * t)⁻¹ * (f⁻¹ * z * f) * (f⁻¹ * t)⁻¹⁻¹ := by group
    rw [e]
    exact h1
  have hgx : (w⁻¹ * t) • c.x0 ∈ c.ptsL := smul_mem_objOf_base hg₀ c.x0_mem_ptsL
  have hgxne : (w⁻¹ * t) • c.x0 ≠ c.x0 := by
    intro h'
    apply hne
    rw [mul_smul, htx] at h'
    have hw'x : w⁻¹ • c.x0 = c.x0 := c.smul_x0_of_mem (inv_mem hwG1)
    exact (smul_left_cancel w⁻¹ (h'.trans hw'x.symm)).symm
  have h2 := h2c _ hgx hgxne (w⁻¹ * t) hg₀ rfl
  have hzE : z ∈ c.E := c.z_mem_E
  have hwzE : w⁻¹ * z * w ∈ c.E := by
    have h1 := (Subgroup.mem_normalizer_iff.mp (inv_mem hwG1) z).mp hzE
    simpa using h1
  have hwzC : w⁻¹ * z * w ∈ c.E.map (MulAut.conj (w⁻¹ * t)).toMonoidHom := by
    rw [mem_conjSub_iff]
    have e : (w⁻¹ * t)⁻¹ * (w⁻¹ * z * w) * (w⁻¹ * t) = t⁻¹ * z * t := by group
    rw [e]
    exact hzt
  have hwZ : w⁻¹ * z * w ∈ c.Z := by
    rw [← h2]
    exact Subgroup.mem_inf.mpr ⟨hwzC, hwzE⟩
  have hz1 : z ≠ 1 := Loc49.z_ne_one hJ
  have hz'1 : w⁻¹ * z * w ≠ 1 := by
    intro h'
    apply hz1
    have e : z = w * (w⁻¹ * z * w) * w⁻¹ := by group
    rw [e, h']
    group
  obtain ⟨k₀, hk₀K, hk₀⟩ := c.exists_K_conj hwZ c.z_mem_Z hz'1 hz1
  have hvG3 : w * k₀⁻¹ ∈ c.G3 := by
    rw [Loc49.G3, H, Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    have e2 : (w * k₀⁻¹)⁻¹ * z * (w * k₀⁻¹) = z := by
      calc (w * k₀⁻¹)⁻¹ * z * (w * k₀⁻¹) = k₀ * (w⁻¹ * z * w) * k₀⁻¹ := by group
        _ = z := hk₀
    calc z * (w * k₀⁻¹) = (w * k₀⁻¹) * ((w * k₀⁻¹)⁻¹ * z * (w * k₀⁻¹)) := by group
      _ = (w * k₀⁻¹) * z := by rw [e2]
  have hvm : ((w * k₀⁻¹ : G) : G ⧸ c.G2) = m := by
    rw [← hw2, QuotientGroup.eq]
    have e3 : (w * k₀⁻¹)⁻¹ * w = k₀ := by group
    rw [e3]
    exact c.K_le_G2 hk₀K
  have hLnP : c.LnP m c.pi0 := ⟨w * k₀⁻¹, hvm, (mk_eq_one_iff c.G3 _).mpr hvG3⟩
  exact c.inc_pt_plane hum hLnP

end Loc49

end CFSG.Quasithin.H13.AS91
