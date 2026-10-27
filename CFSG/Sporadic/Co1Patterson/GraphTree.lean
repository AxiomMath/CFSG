module

public import CFSG.Sporadic.Co1Patterson.GraphInputs
public import CFSG.Sporadic.Co1Block.Tools

public section

namespace CFSG.Sporadic.Co1Patterson

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1.InvNative CFSG.Sporadic.Co1.Module CFSG.Sporadic.Co1Patterson.Native

variable {G₀ : Type*} [Group G₀] (μ : G₀ →* Matrix (Fin 24) (Fin 24) (ZMod 2))

theorem orbOK_parts {G Gi : Array Native.Rows} {root : Native.Rows} {o : Orb}
    (h : orbOK G Gi root o = true) :
    0 < o.c.pts.size ∧ o.hs.size = o.c.pts.size ∧ o.his.size = o.c.pts.size ∧
    (∀ l < G.size, Native.mul G[l]! Gi[l]! = Native.one) ∧ o.hs[0]! = Native.one ∧
    o.his[0]! = Native.one ∧
    (∀ i < o.c.pts.size, i ≠ 0 → o.c.par[i]! < i ∧ o.c.lab[i]! < G.size ∧
      o.hs[i]! = Native.mul G[o.c.lab[i]!]! o.hs[o.c.par[i]!]! ∧
      o.his[i]! = Native.mul o.his[o.c.par[i]!]! Gi[o.c.lab[i]!]!) ∧
    (∀ i < o.c.pts.size, validRows o.c.pts[i]! = true ∧ validRows o.hs[i]! = true ∧
      validRows o.his[i]! = true ∧
      o.c.pts[i]! = Native.mul (Native.mul o.hs[i]! root) o.his[i]!) ∧
    distinctKeys (o.c.pts.toList.map rowsKey) = true := by
  unfold orbOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hpos, hhs⟩, hhis⟩, -⟩, -⟩, hinv⟩, h0⟩, h0'⟩, hstep⟩, hpts⟩, hd⟩ := h
  refine ⟨hpos, hhs, hhis, hinv, h0, h0', fun i hi hi0 => ?_, fun i hi => ?_, hd⟩
  · rcases hstep i hi with h | h
    · exact absurd h hi0
    · exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩
  · obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hpts i hi
    exact ⟨h1, h2, h3, h4⟩

theorem orbOK_sound {G Gi : Array Native.Rows} {root : Native.Rows} {o : Orb}
    (h : orbOK G Gi root o = true) (k : ℕ → G₀) (hk : ∀ l < G.size, μ (k l) = rowsMatrix 24 G[l]!)
    (r : G₀) (hr : μ r = rowsMatrix 24 root) :
    ∀ i < o.c.pts.size, ∃ g ∈ Subgroup.closure (k '' {l | l < G.size}),
      μ g = rowsMatrix 24 o.hs[i]! ∧ μ g⁻¹ = rowsMatrix 24 o.his[i]! ∧
      μ (g * r * g⁻¹) = rowsMatrix 24 o.c.pts[i]! := by
  obtain ⟨-, -, -, hinv, h0, h0', hstep, hpts, -⟩ := orbOK_parts h
  have hki : ∀ l < G.size, μ (k l)⁻¹ = rowsMatrix 24 Gi[l]! := by
    intro l hl
    refine CFSG.Sporadic.Co1Block.map_inv_eq_of_mul μ ?_
    rw [hk l hl, ← rowsMatrix_mulRows]
    exact (congrArg (rowsMatrix 24) (hinv l hl)).trans (rowsMatrix_idRows 24)
  have key : ∀ i < o.c.pts.size, ∃ g ∈ Subgroup.closure (k '' {l | l < G.size}),
      μ g = rowsMatrix 24 o.hs[i]! ∧ μ g⁻¹ = rowsMatrix 24 o.his[i]! := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      by_cases hi0 : i = 0
      · subst hi0
        refine ⟨1, Subgroup.one_mem _, ?_, ?_⟩
        · rw [map_one, h0]; exact (rowsMatrix_idRows 24).symm
        · rw [inv_one, map_one, h0']; exact (rowsMatrix_idRows 24).symm
      · obtain ⟨hp, hl, hhs, hhis⟩ := hstep i hi hi0
        obtain ⟨g, hg, hgμ, hgμ'⟩ := ih _ hp (by omega)
        refine ⟨k (o.c.lab[i]!) * g, Subgroup.mul_mem _ (Subgroup.subset_closure ⟨_, hl, rfl⟩)
          hg, ?_, ?_⟩
        · rw [map_mul, hk _ hl, hgμ, hhs, Native.mul, rowsMatrix_mulRows]
        · rw [mul_inv_rev, map_mul, hki _ hl, hgμ', hhis, Native.mul, rowsMatrix_mulRows]
  intro i hi
  obtain ⟨g, hg, hgμ, hgμ'⟩ := key i hi
  refine ⟨g, hg, hgμ, hgμ', ?_⟩
  rw [(hpts i hi).2.2.2, map_mul, map_mul, hgμ, hr, hgμ', Native.mul, Native.mul,
    rowsMatrix_mulRows, rowsMatrix_mulRows]

theorem orbOK_injective {G Gi : Array Native.Rows} {root : Native.Rows} {o : Orb}
    (h : orbOK G Gi root o = true) {i j : ℕ} (hi : i < o.c.pts.size) (hj : j < o.c.pts.size)
    (hm : rowsMatrix 24 o.c.pts[i]! = rowsMatrix 24 o.c.pts[j]!) : i = j := by
  obtain ⟨-, -, -, -, -, -, -, hpts, hd⟩ := orbOK_parts h
  exact CFSG.Sporadic.Co1Block.eq_of_rowsMatrix_eq (fun i hi => (hpts i hi).1) hd hi hj hm

theorem ptSet_contains_iff {o : Orb} {X : Native.Rows} :
    (CFSG.Sporadic.Co1Patterson.Native.ptSet o).contains X = true ↔
      ∃ i < o.c.pts.size, o.c.pts[i]! = X := by
  rw [CFSG.Sporadic.Co1Patterson.Native.ptSet, Std.HashSet.contains_ofList, List.contains_iff_mem,
    Array.mem_toList_iff, Array.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, getElem!_pos _ i hi⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, (getElem!_pos _ i hi).symm⟩

theorem orbClosed_sound [Finite G₀] {G Gi : Array Native.Rows} {root : Native.Rows} {o : Orb}
    (h : orbOK G Gi root o = true) (hc : orbClosed G Gi o = true) (k : ℕ → G₀)
    (hk : ∀ l < G.size, μ (k l) = rowsMatrix 24 G[l]!) (r : G₀) (hr : μ r = rowsMatrix 24 root) :
    ∀ g ∈ Subgroup.closure (k '' {l | l < G.size}),
      ∃ i < o.c.pts.size, μ (g * r * g⁻¹) = rowsMatrix 24 o.c.pts[i]! := by
  obtain ⟨hpos, -, -, hinv, -, -, -, hpts, -⟩ := orbOK_parts h
  have hki : ∀ l < G.size, μ (k l)⁻¹ = rowsMatrix 24 Gi[l]! := by
    intro l hl
    refine CFSG.Sporadic.Co1Block.map_inv_eq_of_mul μ ?_
    rw [hk l hl, ← rowsMatrix_mulRows]
    exact (congrArg (rowsMatrix 24) (hinv l hl)).trans (rowsMatrix_idRows 24)
  unfold orbClosed at hc
  simp only [List.all_eq_true, List.mem_range] at hc
  have hstep : ∀ x : G₀, (∃ i < o.c.pts.size, μ x = rowsMatrix 24 o.c.pts[i]!) →
      ∀ l < G.size, ∃ j < o.c.pts.size, μ (k l * x * (k l)⁻¹) = rowsMatrix 24 o.c.pts[j]! := by
    rintro x ⟨i, hi, hx⟩ l hl
    obtain ⟨j, hj, hje⟩ := ptSet_contains_iff.1 (hc i hi l hl)
    refine ⟨j, hj, ?_⟩
    rw [hje, map_mul, map_mul, hk l hl, hx, hki l hl, Native.mul, Native.mul, rowsMatrix_mulRows,
      rowsMatrix_mulRows]
  have h0 : μ r = rowsMatrix 24 o.c.pts[0]! := by
    rw [(hpts 0 hpos).2.2.2]
    obtain ⟨-, -, -, -, h0, h0', -⟩ := orbOK_parts h
    rw [h0, h0', Native.mul, Native.mul, rowsMatrix_mulRows, rowsMatrix_mulRows,
      show rowsMatrix 24 Native.one = 1 from rowsMatrix_idRows 24, ← hr, one_mul, mul_one]
  have hsub : ((Subgroup.closure (k '' {l | l < G.size}) : Subgroup G₀) : Set G₀) =
      Submonoid.closure (k '' {l | l < G.size}) := by
    have := congrArg (fun K : Submonoid G₀ => (K : Set G₀))
      (Subgroup.closure_toSubmonoid_of_finite (s := k '' {l | l < G.size}))
    simpa using this
  intro g hg
  have hg' : g ∈ Submonoid.closure (k '' {l | l < G.size}) := by
    rw [← SetLike.mem_coe, ← hsub]
    exact hg
  clear hg
  induction hg' using Submonoid.closure_induction_left with
  | one => exact ⟨0, hpos, by simpa using h0⟩
  | mul_left x hx y _ ih =>
    obtain ⟨l, hl, rfl⟩ := hx
    obtain ⟨j, hj, hje⟩ := hstep _ ih l hl
    exact ⟨j, hj, by rw [← hje]; congr 1; group⟩

end CFSG.Sporadic.Co1Patterson
