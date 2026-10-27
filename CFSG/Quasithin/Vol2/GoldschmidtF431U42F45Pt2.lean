module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42F45Pt
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42F45Lay
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42F45Poly

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin U42F431 CFSG.Quasithin.H13.F431.F45 CFSG.Quasithin.H13.F45Ru
open scoped Pointwise

theorem core_repsP1_iff {i : ℕ}
    {q : Y} (hi : i < 64) (hq : RepL (Tl.getD i []) (q : P45)) :
    (∀ r ∈ repsP1, r⁻¹ * q * r ∈ T) ↔ i ∈ core1 := by
  rw [(chkF45Pt_unpack).2.1, ← core_iff hi hq]
  constructor
  · intro h w hw
    obtain ⟨kw, hkw, rfl⟩ := List.mem_map.1 hw
    exact h _ ⟨kw, hkw, rfl⟩
  · rintro h r ⟨kw, hkw, rfl⟩
    exact h _ (List.mem_map.2 ⟨kw, hkw, rfl⟩)

theorem lt_64_of_mem_core1 {i : ℕ} (hi : i ∈ core1) : i < 64 := by
  rw [(chkF45Pt_unpack).2.1, coreIdx, List.mem_filter, List.mem_range] at hi
  exact hi.1

theorem b01_lt : b01 < 45 := by decide

theorem hfar_pt :
    ∀ b : Vtx, incGraph.dist (Sum.inl 0) b = 4 →
      ∃ q ∈ T, (∀ r ∈ repsP1, r⁻¹ * q * r ∈ T) ∧ q • (Sum.inl (ptOf b01) : Vtx) = b := by
  intro b hb
  rw [layers_pt.dist_eq b] at hb
  rcases b with p | k
  · have hlay : layPt0.getD p 0 = 4 := hb
    rcases (chkF45Pt_unpack).2.2.2.1 p p.2 with h | ⟨hc, hq⟩
    · exact absurd hlay h
    · have hmem : farW1.getD p 0 ∈ core1 := List.contains_iff_mem.1 hc
      obtain ⟨q, hqT, hqrep⟩ := exists_Tel (lt_64_of_mem_core1 hmem)
      refine ⟨q, hqT, (core_repsP1_iff (lt_64_of_mem_core1 hmem) hqrep).2 hmem, ?_⟩
      rw [Sum.smul_inl]
      refine congrArg Sum.inl (Fin.ext ?_)
      rw [smul_point, ← hq, ← (hqrep.2 (ptOf b01)), ptOf_val b01_lt]
  · exfalso
    exact (chkF45Pt_unpack).2.2.1 k k.2 hb

theorem hfree_pt :
    ∀ q ∈ T, (∀ r ∈ repsP1, r⁻¹ * q * r ∈ T) →
      q • (Sum.inl (ptOf b01) : Vtx) = Sum.inl (ptOf b01) → q = 1 := by
  intro q hqT hcore hfix
  obtain ⟨i, hi, hrep⟩ := (mem_T_iff q).1 hqT
  have hmem : i ∈ core1 := (core_repsP1_iff hi hrep).1 hcore
  have hfix' : (Tl.getD i []).getD b01 0 = b01 := by
    rw [Sum.smul_inl, Sum.inl.injEq, smul_point] at hfix
    have := congrArg Fin.val hfix
    rw [← hrep.2 (ptOf b01), ptOf_val b01_lt] at this
    exact this
  rcases (chkF45Pt_unpack).2.2.2.2.1 i hmem with h0 | hne
  · subst h0
    exact eq_one_of_repL_zero hrep
  · exact absurd hfix' hne

end CFSG.Quasithin.H13.F431.U42
