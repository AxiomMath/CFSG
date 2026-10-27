module

public import CFSG.RankThree.GF2n.Stroth80.Sec11Defs
public import CFSG.RankThree.GF2n.Stroth80.Sec5Vt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.conj_mem_H0 (hc : Ctx M Q Z B) {y h : G} (hy : y ∈ M) (hh : h ∈ H0 M Z) :
    y * h * y⁻¹ ∈ H0 M Z := by
  refine ⟨M.mul_mem (M.mul_mem hy hh.1) (M.inv_mem hy), Subgroup.mem_centralizer_iff.mpr ?_⟩
  intro z hz
  have hz' : y⁻¹ * z * y ∈ Z := by
    have := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 (M.inv_mem hy)) z).mp hz
    simpa using this
  have h1 := Subgroup.mem_centralizer_iff.mp hh.2 (y⁻¹ * z * y) hz'
  calc z * (y * h * y⁻¹) = y * ((y⁻¹ * z * y) * h) * y⁻¹ := by group
    _ = y * (h * (y⁻¹ * z * y)) * y⁻¹ := by rw [h1]
    _ = y * h * y⁻¹ * z := by group

theorem Ctx.mk_mem_Ebar [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {a : G}
    (ha : a ∈ LB M Q B) (hA : IsA2 Q Z a) :
    (QuotientGroup.mk (⟨a, hc.LB_le_M ha⟩ : ↥M) : Mbar M Q) ∈ Ebar M Q Z B := by
  refine ⟨⟨⟨a, hc.LB_le_M ha⟩, rfl, hA⟩, 1, ?_⟩
  rw [one_mul, inv_one, mul_one]
  exact Subgroup.mem_map.mpr ⟨⟨a, hc.LB_le_M ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩

theorem Ctx.Ebar_conj [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {d : Mbar M Q}
    (hd : d ∈ Ebar M Q Z B) (x : Mbar M Q) : x * d * x⁻¹ ∈ Ebar M Q Z B := by
  obtain ⟨⟨e, rfl, hA⟩, x', hx'⟩ := hd
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  refine ⟨⟨y * e * y⁻¹, ?_, ?_⟩, x' * (QuotientGroup.mk y)⁻¹, ?_⟩
  · simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  · have h := hA.conj (y : G)
    rw [hc.conj_Q_eq y.2, hc.conj_Z_eq y.2] at h
    exact h
  · have e1 : (x' * (QuotientGroup.mk y)⁻¹) * (QuotientGroup.mk y * QuotientGroup.mk e *
        (QuotientGroup.mk y)⁻¹ : Mbar M Q) * (x' * (QuotientGroup.mk y)⁻¹)⁻¹ =
        x' * QuotientGroup.mk e * x'⁻¹ := by group
    rw [e1]
    exact hx'

theorem Ctx.Ebar_subset_H [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {d : Mbar M Q}
    (hd : d ∈ Ebar M Q Z B) : d ∈ bar M Q (H0 M Z) := by
  obtain ⟨⟨e, rfl, -⟩, x, hx⟩ := hd
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨l, hl, hle⟩ := Subgroup.mem_map.mp hx
  have h1 : (QuotientGroup.mk (y * e * y⁻¹) : Mbar M Q) = QuotientGroup.mk l := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact hle.symm
  have h2 := QuotientGroup.eq.mp h1
  rw [Subgroup.mem_subgroupOf] at h2 hl
  have h3 : ((y * e * y⁻¹ : ↥M) : G) ∈ LB M Q B := by
    have e1 : ((y * e * y⁻¹ : ↥M) : G) =
        (l : G) * (((y * e * y⁻¹ : ↥M) : G)⁻¹ * (l : G))⁻¹ := by group
    rw [e1]
    exact (LB M Q B).mul_mem hl ((LB M Q B).inv_mem (Subgroup.mem_sup_left h2))
  have h4 : (e : G) ∈ H0 M Z := by
    have h5 := hc.conj_mem_H0 (M.inv_mem y.2) (hc.LB_le_H0 h3)
    have e2 : (y : G)⁻¹ * ((y * e * y⁻¹ : ↥M) : G) * ((y : G)⁻¹)⁻¹ = (e : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rwa [e2] at h5
  exact Subgroup.mem_map.mpr ⟨e, Subgroup.mem_subgroupOf.mpr h4, rfl⟩

theorem Ctx.Xbar_normal [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) :
    (Xbar M Q Z B).Normal := by
  refine ⟨fun n hn g => ?_⟩
  unfold Xbar at hn ⊢
  induction hn using Subgroup.closure_induction with
  | mem x hx => exact Subgroup.subset_closure (hc.Ebar_conj hx g)
  | one => simpa using Subgroup.one_mem _
  | mul x y _ _ hx hy =>
    have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ hx

end CFSG.RankThree.GF2n.Stroth80
