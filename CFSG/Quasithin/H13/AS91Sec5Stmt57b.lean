module

public import CFSG.Quasithin.H13.AS91Sec3TwelveOneDefs
public import CFSG.Quasithin.H13.AS91Sec7Geom
public import CFSG.Quasithin.H13.AS91Sec7Zfix

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction CFSG.Quasithin.Asc94
open scoped Pointwise
open CFSG.ASVolI.ChH (IsTrio IsSextet M24g S24)

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

@[expose] def qMeet (k : G) : Subgroup G := c.E.map (MulAut.conj k).toMonoidHom ⊓ c.G1

theorem mem_qMeet_iff (k x : G) : x ∈ c.qMeet k ↔ k⁻¹ * x * k ∈ c.E ∧ x ∈ c.G1 := by
  rw [qMeet, Subgroup.mem_inf, Subgroup.mem_map]
  constructor
  · rintro ⟨⟨e, he, hex⟩, hx⟩
    have e1 : k⁻¹ * x * k = e := by
      rw [← hex]
      show k⁻¹ * (k * e * k⁻¹) * k = e
      group
    refine ⟨by rw [e1]; exact he, hx⟩
  · rintro ⟨h1, hx⟩
    refine ⟨⟨k⁻¹ * x * k, h1, ?_⟩, hx⟩
    show k * (k⁻¹ * x * k) * k⁻¹ = x
    group

theorem smul_point_of_mem_qMeet {k x : G} (hx : x ∈ c.qMeet k) :
    x • (k • c.x0) = k • c.x0 := by
  obtain ⟨he, -⟩ := (c.mem_qMeet_iff k x).1 hx
  have e : x * k = k * (k⁻¹ * x * k) := by group
  rw [← mul_smul, e, mul_smul, c.smul_x0_of_mem (c.E_le_G1 he)]

theorem conj_mem_G1_of_fix {k h : G} (hfix : h • (k • c.x0) = k • c.x0) :
    k⁻¹ * h * k ∈ c.G1 := by
  have h1 : (k⁻¹ * h * k) • c.x0 = c.x0 := by
    rw [mul_smul, mul_smul, hfix, inv_smul_smul]
  have h2 := MulAction.mem_stabilizer_iff.2 h1
  rwa [c.stab_x0] at h2

theorem conj_mem_qMeet {k h q : G} (hh : h ∈ c.G1) (hfix : h • (k • c.x0) = k • c.x0)
    (hq : q ∈ c.qMeet k) : h * q * h⁻¹ ∈ c.qMeet k := by
  obtain ⟨hqE, hqG1⟩ := (c.mem_qMeet_iff k q).1 hq
  have hg0 := c.conj_mem_G1_of_fix hfix
  have e2 : k⁻¹ * (h * q * h⁻¹) * k = (k⁻¹ * h * k) * (k⁻¹ * q * k) * (k⁻¹ * h * k)⁻¹ := by
    group
  refine (c.mem_qMeet_iff k _).2 ⟨?_, mul_mem (mul_mem hh hqG1) (inv_mem hh)⟩
  rw [e2]
  exact (Subgroup.mem_normalizer_iff.mp hg0 (k⁻¹ * q * k)).mp hqE

end Loc49

namespace ResM24

variable {G : Type} [Group G] [Finite G] {z : G} {c : Loc49 G z} (ρ : ResM24 c)

@[expose] noncomputable def nSub (k : G) : Subgroup S24 := ((c.qMeet k).subgroupOf c.G1).map ρ.φ

include ρ in
theorem nSub_le (k : G) : ρ.nSub k ≤ M24g := by
  intro σ hσ
  obtain ⟨h, -, rfl⟩ := Subgroup.mem_map.1 hσ
  exact ρ.φ_mem h

include ρ in
theorem phi_mem_nSub {k q : G} (hq : q ∈ c.qMeet k) (hq1 : q ∈ c.G1) :
    ρ.φ ⟨q, hq1⟩ ∈ ρ.nSub k :=
  Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hq)

include ρ in
theorem sq_eq_one_of_mem_nSub {k : G} {σ : S24} (hσ : σ ∈ ρ.nSub k) : σ ^ 2 = 1 := by
  obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 hσ
  rw [Subgroup.mem_subgroupOf] at hq
  obtain ⟨he, -⟩ := (c.mem_qMeet_iff k _).1 hq
  have h2 : (k⁻¹ * (q : G) * k) ^ 2 = 1 := c.E_elem.2 _ he
  have hq2 : (q : G) ^ 2 = 1 := by
    calc (q : G) ^ 2 = k * (k⁻¹ * (q : G) * k) ^ 2 * k⁻¹ := by
          simp only [pow_two]
          group
      _ = 1 := by
          rw [h2]
          group
  have hq2' : q ^ 2 = 1 := Subtype.ext hq2
  rw [← map_pow, hq2', map_one]

include ρ in
theorem isPGroup_nSub (k : G) : IsPGroup 2 (ρ.nSub k) := by
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  simpa using ρ.sq_eq_one_of_mem_nSub g.2

include ρ in
theorem nSub_fix (hLU : Stmt5_LineU) (hJ : HypJ4 G z) (k : G) {m' : G ⧸ c.G2}
    (hm0 : CInc c.G1 c.G2 c.x0 m') (hx1 : CInc c.G1 c.G2 (k • c.x0) m')
    (hx0 : k • c.x0 ≠ c.x0) : ∀ σ ∈ ρ.nSub k, σ • ρ.trio m' = ρ.trio m' := by
  intro σ hσ
  obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 hσ
  rw [Subgroup.mem_subgroupOf] at hq
  obtain ⟨-, hqG1⟩ := (c.mem_qMeet_iff k _).1 hq
  have hqx : (q : G) • (k • c.x0) = k • c.x0 := c.smul_point_of_mem_qMeet hq
  have hqm0 : CInc c.G1 c.G2 c.x0 ((q : G) • m') := by
    have h1 := (cInc_smul c.G1 c.G2 (q : G) c.x0 m').2 hm0
    rwa [c.smul_x0_of_mem hqG1] at h1
  have hqm1 : CInc c.G1 c.G2 (k • c.x0) ((q : G) • m') := by
    have h1 := (cInc_smul c.G1 c.G2 (q : G) (k • c.x0) m').2 hx1
    rwa [hqx] at h1
  have hqm : (q : G) • m' = m' :=
    (c.eq_of_onL hLU hJ hx0.symm hm0 hx1 hqm0 hqm1).symm
  rw [← ρ.trio_smul_line q hm0, hqm]

include ρ in
theorem exists_fix_point (k : G) {m' : G ⧸ c.G2} (hm0 : CInc c.G1 c.G2 c.x0 m')
    (hx1 : CInc c.G1 c.G2 (k • c.x0) m') (hx0 : k • c.x0 ≠ c.x0) (h : ↥c.G1)
    (hfix : ρ.φ h • ρ.trio m' = ρ.trio m') :
    ∃ h' : ↥c.G1, ρ.φ h' = ρ.φ h ∧ (h' : G) • (k • c.x0) = k • c.x0 := by
  have htr : ρ.trio ((h : G) • m') = ρ.trio m' := by
    rw [ρ.trio_smul_line h hm0]
    exact hfix
  have hhm0 : CInc c.G1 c.G2 c.x0 ((h : G) • m') := (c.cInc_x0_smul h.2).2 hm0
  have hhm : (h : G) • m' = m' := ρ.trio_injOn hhm0 hm0 htr
  have ha : c.OnL ((h : G) • (k • c.x0)) m' := by
    have h1 := (cInc_smul c.G1 c.G2 (h : G) (k • c.x0) m').2 hx1
    rwa [hhm] at h1
  have hax : (h : G) • (k • c.x0) ≠ c.x0 := by
    intro e
    apply hx0
    rw [← inv_smul_smul (h : G) (k • c.x0), e, c.smul_x0_of_mem (inv_mem h.2)]
  obtain ⟨e, he, hea⟩ := c.E_transitive_line hm0 ha hax hx1 hx0
  have heG1 : e ∈ c.G1 := c.E_le_G1 he
  refine ⟨⟨e * h, mul_mem heG1 h.2⟩, ?_, ?_⟩
  · have h1 : (⟨e, heG1⟩ : ↥c.G1) ∈ ρ.φ.ker := by
      rw [ρ.ker_eq, Subgroup.mem_subgroupOf]
      exact he
    have h2 : ρ.φ ⟨e, heG1⟩ = 1 := h1
    show ρ.φ (⟨e, heG1⟩ * h) = ρ.φ h
    rw [map_mul, h2, one_mul]
  · show (e * (h : G)) • (k • c.x0) = k • c.x0
    rw [mul_smul, hea]

include ρ in
theorem nSub_normal (k : G) {m' : G ⧸ c.G2} (hm0 : CInc c.G1 c.G2 c.x0 m')
    (hx1 : CInc c.G1 c.G2 (k • c.x0) m') (hx0 : k • c.x0 ≠ c.x0) :
    ∀ σ ∈ M24g, σ • ρ.trio m' = ρ.trio m' → ∀ n ∈ ρ.nSub k, σ * n * σ⁻¹ ∈ ρ.nSub k := by
  intro σ hσ hfix n hn
  obtain ⟨h, rfl⟩ := ρ.exists_φ_eq hσ
  obtain ⟨h', hh', hh'x⟩ := ρ.exists_fix_point k hm0 hx1 hx0 h hfix
  obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 hn
  rw [Subgroup.mem_subgroupOf] at hq
  have hmem : h' * q * h'⁻¹ ∈ (c.qMeet k).subgroupOf c.G1 := by
    rw [Subgroup.mem_subgroupOf]
    exact c.conj_mem_qMeet h'.2 hh'x hq
  have e : ρ.φ h * ρ.φ q * (ρ.φ h)⁻¹ = ρ.φ (h' * q * h'⁻¹) := by
    rw [← hh', map_mul, map_mul, map_inv]
  rw [e]
  exact Subgroup.mem_map_of_mem _ hmem

include ρ in
theorem coL_of_not_mem_Q
    (h121 : M24G.Stmt3_12_1M24) (hLU : Stmt5_LineU) (hJ : HypJ4 G z)
    {x y u : G ⧸ c.G1} (hxu : c.Delta.Adj x u) (hyu : c.Delta.Adj y u)
    {gx gy f : G} (hgx : gx • c.x0 = x) (hgy : gy • c.x0 = y) (hf : f • c.x0 = u)
    {w : G} (hwx : gx⁻¹ * w * gx ∈ c.E) (hwy : gy⁻¹ * w * gy ∈ c.E) (hwu : w • u = u)
    (hw : f⁻¹ * w * f ∉ c.E) {m n : G ⧸ c.G2} (hum : c.OnL u m) (hxm : c.OnL x m)
    (hun : c.OnL u n) (hyn : c.OnL y n) : c.CoL m n := by
  have hm0 : CInc c.G1 c.G2 c.x0 (f⁻¹ • m) := c.onL_x0_inv_smul hf hum
  have hn0 : CInc c.G1 c.G2 c.x0 (f⁻¹ • n) := c.onL_x0_inv_smul hf hun
  have hxm' : CInc c.G1 c.G2 (f⁻¹ • x) (f⁻¹ • m) := (cInc_smul c.G1 c.G2 f⁻¹ x m).2 hxm
  have hyn' : CInc c.G1 c.G2 (f⁻¹ • y) (f⁻¹ • n) := (cInc_smul c.G1 c.G2 f⁻¹ y n).2 hyn
  have hu0 : f⁻¹ • u = c.x0 := by rw [← hf, inv_smul_smul]
  have hx0 : f⁻¹ • x ≠ c.x0 := fun h => hxu.ne (MulAction.injective f⁻¹ (h.trans hu0.symm))
  have hy0 : f⁻¹ • y ≠ c.x0 := fun h => hyu.ne (MulAction.injective f⁻¹ (h.trans hu0.symm))
  have hkx : (f⁻¹ * gx) • c.x0 = f⁻¹ • x := by rw [mul_smul, hgx]
  have hky : (f⁻¹ * gy) • c.x0 = f⁻¹ • y := by rw [mul_smul, hgy]
  have hw1 : f⁻¹ * w * f ∈ c.G1 := by
    have h1 : (f⁻¹ * w * f) • c.x0 = c.x0 := by
      rw [mul_smul, mul_smul, hf, hwu, hu0]
    have h2 := MulAction.mem_stabilizer_iff.2 h1
    rwa [c.stab_x0] at h2
  have hwq1 : f⁻¹ * w * f ∈ c.qMeet (f⁻¹ * gx) := by
    refine (c.mem_qMeet_iff _ _).2 ⟨?_, hw1⟩
    have e1 : (f⁻¹ * gx)⁻¹ * (f⁻¹ * w * f) * (f⁻¹ * gx) = gx⁻¹ * w * gx := by group
    rw [e1]
    exact hwx
  have hwq2 : f⁻¹ * w * f ∈ c.qMeet (f⁻¹ * gy) := by
    refine (c.mem_qMeet_iff _ _).2 ⟨?_, hw1⟩
    have e1 : (f⁻¹ * gy)⁻¹ * (f⁻¹ * w * f) * (f⁻¹ * gy) = gy⁻¹ * w * gy := by group
    rw [e1]
    exact hwy
  have hne : ρ.φ ⟨f⁻¹ * w * f, hw1⟩ ≠ 1 := by
    intro h1
    apply hw
    have h2 : (⟨f⁻¹ * w * f, hw1⟩ : ↥c.G1) ∈ ρ.φ.ker := MonoidHom.mem_ker.2 h1
    rw [ρ.ker_eq, Subgroup.mem_subgroupOf] at h2
    exact h2
  have hcop : M24G.Coplanar (ρ.trio (f⁻¹ • m)) (ρ.trio (f⁻¹ • n)) := by
    refine h121 (ρ.trio (f⁻¹ • m)) (ρ.trio (f⁻¹ • n)) (ρ.nSub (f⁻¹ * gx)) (ρ.nSub (f⁻¹ * gy))
      (ρ.isTrio_trio hm0) (ρ.isTrio_trio hn0)
      (ρ.nSub_le (f⁻¹ * gx))
      (ρ.nSub_fix hLU hJ (f⁻¹ * gx) hm0 (by rw [hkx]; exact hxm') (by rw [hkx]; exact hx0))
      (ρ.nSub_normal (f⁻¹ * gx) hm0 (by rw [hkx]; exact hxm') (by rw [hkx]; exact hx0))
      (ρ.isPGroup_nSub (f⁻¹ * gx))
      (ρ.nSub_le (f⁻¹ * gy))
      (ρ.nSub_fix hLU hJ (f⁻¹ * gy) hn0 (by rw [hky]; exact hyn') (by rw [hky]; exact hy0))
      (ρ.nSub_normal (f⁻¹ * gy) hn0 (by rw [hky]; exact hyn') (by rw [hky]; exact hy0))
      (ρ.isPGroup_nSub (f⁻¹ * gy))
      ?_
    exact Subgroup.ne_bot_iff_exists_ne_one.2
      ⟨⟨ρ.φ ⟨f⁻¹ * w * f, hw1⟩, Subgroup.mem_inf.2
        ⟨ρ.phi_mem_nSub hwq1 hw1, ρ.phi_mem_nSub hwq2 hw1⟩⟩,
        fun h => hne (congrArg Subtype.val h)⟩
  exact (ρ.coplanar_iff_at hf hum hun).2 hcop

end ResM24

end CFSG.Quasithin.H13.AS91
