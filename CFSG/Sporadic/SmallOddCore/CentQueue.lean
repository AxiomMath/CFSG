module

public import CFSG.Sporadic.SmallOddCore.CentSpec

public section

namespace CFSG.Sporadic.SmallOddCore

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

variable {n : ℕ} {P : Subgroup (Equiv.Perm (Fin n))} {pg pgInv : Array Table}
  {gg : ℕ → Equiv.Perm (Fin n)} {sift : Table → Bool}

theorem classOK_queue_cover (hD : GroupData n P pg gg sift) {NP cap : ℕ} {u : Table}
    {r : ClassRow} {o : Closure} (h : classOK n NP cap pg pgInv sift u r o = true)
    (hcent : Nat.card ↥(P ⊓ centralizer ({tp n r.rep} : Set (Equiv.Perm (Fin n)))) =
      r.centOrder)
    {y : Equiv.Perm (Fin n)} (hy : y ∈ P ⊓ centralizer ({tp n r.rep} : Set _)) (hy1 : y ≠ 1)
    (hyp : ∃ p ∈ r.oddPrimes, y ^ p = 1) :
    ∃ s ∈ r.odd, ordTest n s.prime s.rep = true ∧
      (∃ c ∈ P ⊓ centralizer ({tp n r.rep} : Set _), y = c * tp n s.rep * c⁻¹) ∧
      ∃ k < (conjClosureH n r.centGens.toArray (r.centGens.toArray.map (invT n))
        s.rep cap).1.size,
      Rep n (conjClosureH n r.centGens.toArray (r.centGens.toArray.map (invT n)) s.rep cap).1[k]!
        y := by
  have hn := hD.lt
  set t := tp n r.rep
  set cg := r.centGens.toArray
  set cgInv := cg.map (invT n)
  set C := mulClosureH n cg cap
  simp only [classOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ht1, -⟩, -⟩, -⟩, -⟩, -⟩, hcg⟩, hCtree⟩, hCdist⟩,
    hCsize⟩, -⟩, hodd⟩, hqtree⟩, hcov⟩ := h
  have hT := rep_tp ht1
  rw [Array.all_eq_true'] at hcg
  simp only [Bool.and_eq_true] at hcg
  have hcgP : ∀ c ∈ cg, Rep n c (tp n c) ∧ tp n c ∈ P ⊓ centralizer ({t} : Set _) := by
    intro c hc
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, -⟩ := hcg c hc
    have hc' := rep_tp h1
    refine ⟨hc', mem_inf.mpr ⟨(hD.sift _ _ hc').1 h2, ?_⟩⟩
    rw [mem_centralizer_singleton_iff]
    exact (commTT_iff hc' hT).1 h3
  set K := closure (tp n '' {x | x ∈ cg})
  have hKle : K ≤ P ⊓ centralizer ({t} : Set _) := by
    rw [closure_le]
    rintro _ ⟨c, hc, rfl⟩
    exact (hcgP c hc).2
  have hga : ∀ l < cg.size, Rep n cg[l]! (tp n cg[l]!) ∧ tp n cg[l]! ∈ K := fun l hl =>
    ⟨(hcgP _ (getElem!_mem_array hl)).1, subset_closure ⟨_, getElem!_mem_array hl, rfl⟩⟩
  have hCK := mulTreeOK_spec hn K (gg := fun l => tp n cg[l]!) hga hCtree
  have hCrep : ∀ k < C.1.size, Rep n C.1[k]! (tablePerm n C.1[k]!) := by
    intro k hk
    obtain ⟨c, -, hrep⟩ := hCK k hk
    rw [tablePerm_eq hrep]
    exact hrep
  have hCmem : ∀ k < C.1.size, tablePerm n C.1[k]! ∈ K := by
    intro k hk
    obtain ⟨c, hc, hrep⟩ := hCK k hk
    rw [tablePerm_eq hrep]
    exact hc
  have hCnodup := nodup_of_hkeysDistinct (forall₂_tablePerm hCrep) hCdist
  obtain ⟨k, hk, hrep⟩ : ∃ k < C.1.size, Rep n C.1[k]! y := by
    have hmem := mem_of_nodup_of_card_le hCnodup (K := P ⊓ centralizer ({t} : Set _))
      (fun x hx => by
        obtain ⟨k, hk, rfl⟩ := mem_map_tablePerm hCrep hx
        exact hKle (hCmem k hk))
      (by rw [List.length_map, Array.length_toList, hCsize, hcent]) y hy
    obtain ⟨k, hk, rfl⟩ := mem_map_tablePerm hCrep hmem
    exact ⟨k, hk, hCrep k hk⟩
  have hcgK : ∀ l < cg.size, Rep n cg[l]! (tp n cg[l]!) ∧ Rep n cgInv[l]! (tp n cg[l]!)⁻¹ ∧
      tp n cg[l]! ∈ P ⊓ centralizer ({t} : Set _) := by
    intro l hl
    have hc := hcgP _ (getElem!_mem_array hl)
    refine ⟨hc.1, ?_, hc.2⟩
    have hinv := (hcg _ (getElem!_mem_array hl)).2
    rw [getElem!_pos cgInv l (by simpa [cgInv] using hl), Array.getElem_map,
      ← getElem!_pos cg l hl]
    exact rep_invT hc.1 hinv
  rw [List.all_eq_true] at hodd hqtree
  have hsel : selOK n r.oddPrimes C.1[k]! = true := by
    rw [selOK_iff hn hrep]
    exact ⟨hy1, hyp⟩
  rw [Array.all_eq_true] at hcov
  have h2 := hcov k hk
  rw [← getElem!_pos C.1 k hk, hsel, Bool.not_true, Bool.false_or, List.any_eq_true] at h2
  obtain ⟨q, hq, hmemq⟩ := h2
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hq
  have hrow := hodd s hs
  simp only [oddRowOK, Bool.and_eq_true] at hrow
  have hsrep := rep_tp hrow.1.1.1.1
  have hqspec := conjTreeOK_spec (P ⊓ centralizer ({t} : Set _)) hcgK hsrep
    (hqtree _ (List.mem_map.mpr ⟨s, hs, rfl⟩))
  have hqrep : ∀ j < (conjClosureH n cg cgInv s.rep cap).1.size,
      Rep n (conjClosureH n cg cgInv s.rep cap).1[j]!
        (tablePerm n (conjClosureH n cg cgInv s.rep cap).1[j]!) := by
    intro j hj
    obtain ⟨c, -, hc⟩ := hqspec j hj
    rw [tablePerm_eq hc]
    exact hc
  obtain ⟨j, hj, hyj⟩ := memT_spec hqrep hrep hmemq
  obtain ⟨c, hcK, hc⟩ := hqspec j hj
  refine ⟨s, hs, hrow.1.2, ⟨c, hcK, by rw [hyj, tablePerm_eq hc]⟩, j, hj, ?_⟩
  rw [hyj]
  exact hqrep j hj

end CFSG.Sporadic.SmallOddCore

end
