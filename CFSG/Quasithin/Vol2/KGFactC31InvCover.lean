module

public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses

public section

namespace CFSG.Quasithin.KGC31

open CFSG.Certificates CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native

variable {n : ℕ}

@[expose] def closureTabs (n : ℕ) (gens gensInv : Array Table) (reps : List Table) (cap : ℕ) :
    List Table :=
  reps.flatMap fun r => (conjClosure n gens gensInv r cap).1.toList

theorem exists_tab_of_repsOK (hn : n < 2 ^ 32) (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)
    {gens gensInv : Array Table} {gg : ℕ → Equiv.Perm (Fin n)}
    (hg : ∀ l < gens.size,
      Rep n gens[l]! (gg l) ∧ Rep n gensInv[l]! (gg l)⁻¹ ∧ gg l ∈ Q.originalSubgroup)
    (g₀ : Equiv.Perm (Fin n))
    (hg₀ : ∀ h ∈ Q.originalSubgroup, g₀⁻¹ * h * g₀ ∈ Q.originalSubgroup) {m : ℕ} (hm : 0 < m)
    (reps : List (Equiv.Perm (Fin n)))
    (hreps : ∀ r ∈ reps, g₀⁻¹ * r ∈ Q.originalSubgroup ∧ orderOf r = m) (cap : ℕ)
    (hok : repsOK n gens gensInv (cosetOrderTables Q g₀ m) (reps.map toTable) cap = true) :
    ∀ u, g₀⁻¹ * u ∈ Q.originalSubgroup → orderOf u = m →
      ∃ T ∈ closureTabs n gens gensInv (reps.map toTable) cap, Rep n T u := by
  set H := Q.originalSubgroup
  set L := enumeration Q
  have hmem : ∀ g, g ∈ L ↔ g ∈ H := mem_enumeration_iff Q hQ
  set XG := (L.map (g₀ * ·)).filter fun h => decide (orderOf h = m)
  have hX := forall₂_cosetOrderTables hn Q g₀ hm
  have hXG : ∀ u, u ∈ XG ↔ g₀⁻¹ * u ∈ H ∧ orderOf u = m := by
    intro u
    simp only [XG, List.mem_filter, List.mem_map, hmem, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨h, hh, rfl⟩, ho⟩
      exact ⟨by simpa using hh, ho⟩
    · rintro ⟨hu, ho⟩
      exact ⟨⟨g₀⁻¹ * u, hu, by group⟩, ho⟩
  have hclosed : ∀ c ∈ H, ∀ u, g₀⁻¹ * u ∈ H → orderOf u = m →
      g₀⁻¹ * (c * u * c⁻¹) ∈ H ∧ orderOf (c * u * c⁻¹) = m := by
    intro c hc u hu ho
    refine ⟨?_, (MulEquiv.orderOf_eq (MulAut.conj c) u).trans ho⟩
    have : g₀⁻¹ * (c * u * c⁻¹) = (g₀⁻¹ * c * g₀) * (g₀⁻¹ * u) * c⁻¹ := by group
    rw [this]
    exact H.mul_mem (H.mul_mem (hg₀ c hc) hu) (H.inv_mem hc)
  simp only [repsOK, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨htree, hdist⟩, hsum⟩ := hok
  set cl := (reps.map toTable).map fun r => (r, conjClosure n gens gensInv r cap)
  have hcl : ∀ c ∈ cl, ∃ r ∈ reps, c.1 = toTable r ∧
      c.2 = conjClosure n gens gensInv (toTable r) cap := by
    intro c hc
    simp only [cl, List.map_map, List.mem_map, Function.comp] at hc
    obtain ⟨r, hr, rfl⟩ := hc
    exact ⟨r, hr, rfl, rfl⟩
  have hentries : ∀ c ∈ cl, ∀ T ∈ c.2.1.toList, ∃ r ∈ reps, Rep n c.1 r ∧
      ∃ d ∈ H, Rep n T (d * r * d⁻¹) := by
    intro c hc T hT
    obtain ⟨r, hr, h1, -⟩ := hcl c hc
    have hrep : Rep n c.1 r := h1 ▸ rep_toTable hn r
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hT
    rw [Array.length_toList] at hk
    obtain ⟨d, hd, hrepd⟩ := conjTreeOK_spec H hg hrep (htree c hc) k hk
    refine ⟨r, hr, hrep, d, hd, ?_⟩
    rw [Array.getElem_toList]
    rwa [getElem!_pos c.2.1 k hk] at hrepd
  set U := cl.flatMap fun c => c.2.1.toList
  have hU : List.Forall₂ (Rep n) U (U.map (tablePerm n)) := by
    rw [List.forall₂_map_right_iff]
    refine List.forall₂_same.2 fun T hT => ?_
    obtain ⟨c, hc, hT⟩ := List.mem_flatMap.1 hT
    obtain ⟨r, -, -, d, -, hrep⟩ := hentries c hc T hT
    rw [tablePerm_eq hrep]
    exact hrep
  have hnodup : (U.map (tablePerm n)).Nodup := nodup_of_keysDistinct hU hdist
  have hUmem : ∀ T ∈ U, ∃ r ∈ reps, ∃ d ∈ H, tablePerm n T = d * r * d⁻¹ := by
    intro T hT
    obtain ⟨c, hc, hT⟩ := List.mem_flatMap.1 hT
    obtain ⟨r, hr, -, d, hd, hrep⟩ := hentries c hc T hT
    exact ⟨r, hr, d, hd, tablePerm_eq hrep⟩
  have hsub : U.map (tablePerm n) ⊆ XG := by
    intro y hy
    obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hy
    obtain ⟨r, hr, d, hd, heq⟩ := hUmem T hT
    rw [heq, hXG]
    exact hclosed d hd r (hreps r hr).1 (hreps r hr).2
  have hlen : XG.length ≤ (U.map (tablePerm n)).length := by
    rw [List.length_map, List.length_flatMap, ← List.length_reverse, ← hX.length_eq, ← hsum]
    simp
  have hperm := (hnodup.subperm hsub).perm_of_length_le hlen
  intro u hu ho
  have huU : u ∈ U.map (tablePerm n) := hperm.symm.subset ((hXG u).2 ⟨hu, ho⟩)
  obtain ⟨T, hT, rfl⟩ := List.mem_map.1 huU
  have hTU : T ∈ closureTabs n gens gensInv (reps.map toTable) cap := by
    obtain ⟨c, hc, hT⟩ := List.mem_flatMap.1 hT
    obtain ⟨r, hr, h1, h2⟩ := hcl c hc
    rw [closureTabs, List.mem_flatMap]
    refine ⟨toTable r, List.mem_map.2 ⟨r, hr, rfl⟩, ?_⟩
    rw [← h2]
    exact hT
  refine ⟨T, hTU, ?_⟩
  obtain ⟨c, hc, hT'⟩ := List.mem_flatMap.1 hT
  obtain ⟨r, -, -, d, -, hrep⟩ := hentries c hc T hT'
  rw [tablePerm_eq hrep]
  exact hrep

end CFSG.Quasithin.KGC31

end
