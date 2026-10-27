module

public import CFSG.Sporadic.Recognition.McLASInputs

public section

namespace CFSG.Sporadic.Recognition.McLAS

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

variable {n : ℕ}

structure ElemFacts (n : ℕ) (P : Subgroup (Equiv.Perm (Fin n))) (p : ℕ) (r : ElemRow) : Prop where
  rep : Rep n r.rep (tp n r.rep)
  order : orderOf (tp n r.rep) = p
  mem : tp n r.rep ∈ P
  gens : closure (tp n '' {x | x ∈ r.centGens.toArray}) =
    P ⊓ centralizer ({tp n r.rep} : Set (Equiv.Perm (Fin n)))
  cent : Nat.card ↥(P ⊓ centralizer ({tp n r.rep} : Set (Equiv.Perm (Fin n)))) = r.centOrder
  cls : (conjClass P (tp n r.rep)).ncard = r.classSize

theorem elemOK_spec {P : Subgroup (Equiv.Perm (Fin n))} {pg pgInv : Array Table}
    {gg : ℕ → Equiv.Perm (Fin n)} {sift : Table → Bool} (hD : GroupData n P pg gg sift)
    {NP cap p : ℕ} (hP : Nat.card P = NP) (hpgi : ∀ l < pg.size, Rep n pgInv[l]! (gg l)⁻¹)
    {r : ElemRow} (hp : 0 < p)
    (h : elemOK n NP cap p pg pgInv sift r (conjClosureH n pg pgInv r.rep cap) = true) :
    ElemFacts n P p r := by
  have hn := hD.lt
  set t := tp n r.rep
  set o := conjClosureH n pg pgInv r.rep cap
  set cg := r.centGens.toArray
  set C := mulClosureH n cg cap
  simp only [elemOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ht1, hsift⟩, hord⟩, horb⟩, hodist⟩, hosize⟩, hcg⟩, hCtree⟩, hCdist⟩, hCsize⟩,
    hprod⟩ := h
  have hT := rep_tp ht1
  have hordt : orderOf t = p := (ordTest_iff_perm hT hp).1 hord
  have htP : t ∈ P := (hD.sift _ _ hT).1 hsift
  have hgP : ∀ l < pg.size, Rep n pg[l]! (gg l) ∧ Rep n pgInv[l]! (gg l)⁻¹ ∧ gg l ∈ P :=
    fun l hl => ⟨hD.rep l hl, hpgi l hl, hD.mem hl⟩
  have horb' := conjTreeOK_spec P hgP hT horb
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
  have hKcard : r.centOrder ≤ Nat.card K := by
    have := length_le_card_of_nodup hCnodup fun x hx => by
      obtain ⟨k, hk, rfl⟩ := mem_map_tablePerm hCrep hx
      exact hCmem k hk
    rwa [List.length_map, Array.length_toList, hCsize] at this
  have horep : ∀ k < o.1.size, Rep n o.1[k]! (tablePerm n o.1[k]!) := by
    intro k hk
    obtain ⟨c, -, hrep⟩ := horb' k hk
    rw [tablePerm_eq hrep]
    exact hrep
  have honodup := nodup_of_hkeysDistinct (forall₂_tablePerm horep) hodist
  have hclass : r.classSize ≤ (conjClass P t).ncard := by
    have := length_le_ncard_of_nodup honodup (S := conjClass P t) fun x hx => by
      obtain ⟨k, hk, rfl⟩ := mem_map_tablePerm horep hx
      obtain ⟨c, hc, hrep⟩ := horb' k hk
      rw [tablePerm_eq hrep]
      exact ⟨c, hc, rfl⟩
    rwa [List.length_map, Array.length_toList, hosize] at this
  have hos := ncard_conjClass_mul_card P t
  rw [hP, ← hprod] at hos
  have hCle : Nat.card K ≤ Nat.card ↥(P ⊓ centralizer ({t} : Set _)) := card_le_of_le hKle
  have hpos1 : 0 < r.classSize := by
    rcases Nat.eq_zero_or_pos r.classSize with h0 | h0
    · rw [h0, zero_mul] at hprod
      rw [← hprod] at hP
      exact absurd hP (Nat.card_pos (α := P)).ne'
    · exact h0
  have hpos2 : 0 < r.centOrder := by
    rcases Nat.eq_zero_or_pos r.centOrder with h0 | h0
    · rw [h0, mul_zero] at hprod
      rw [← hprod] at hP
      exact absurd hP (Nat.card_pos (α := P)).ne'
    · exact h0
  have hcent : Nat.card ↥(P ⊓ centralizer ({t} : Set _)) = r.centOrder := by
    by_contra hne
    have hlt : r.centOrder < Nat.card ↥(P ⊓ centralizer ({t} : Set _)) := by omega
    have : r.classSize * r.centOrder < (conjClass P t).ncard *
        Nat.card ↥(P ⊓ centralizer ({t} : Set _)) :=
      Nat.mul_lt_mul_of_le_of_lt hclass hlt (hpos1.trans_le hclass)
    omega
  have hcls : (conjClass P t).ncard = r.classSize := by
    rw [hcent] at hos
    exact Nat.eq_of_mul_eq_mul_right hpos2 hos
  have hKeq : K = P ⊓ centralizer ({t} : Set _) :=
    Subgroup.eq_of_le_of_card_ge hKle (by rw [hcent]; exact hKcard)
  exact ⟨hT, hordt, htP, hKeq, hcent, hcls⟩


theorem elemRowsOK_spec {P : Subgroup (Equiv.Perm (Fin n))} {pg pgInv : Array Table}
    {gg : ℕ → Equiv.Perm (Fin n)} {sift : Table → Bool} (hD : GroupData n P pg gg sift)
    {NP cap p : ℕ} (hP : Nat.card P = NP) (hp : 0 < p) {rows : List ElemRow}
    (h : elemRowsOK n NP cap p pg pgInv sift rows = true) : ∀ r ∈ rows, ElemFacts n P p r := by
  simp only [elemRowsOK, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hinv, hrows⟩ := h
  have hpgi : ∀ l < pg.size, Rep n pgInv[l]! (gg l)⁻¹ := by
    intro l hl
    exact Rep.inv_of_invOK (hD.rep l hl) (allIn_eq_true.1 hinv l (Nat.zero_le _) hl)
  exact fun r hr => elemOK_spec hD hP hpgi hp (hrows r hr)

theorem mem_of_nodup_of_ncard_le {S : Set (Equiv.Perm (Fin n))} {L : List (Equiv.Perm (Fin n))}
    (hL : L.Nodup) (hS : ∀ x ∈ L, x ∈ S) (hlen : S.ncard ≤ L.length) : ∀ y ∈ S, y ∈ L := by
  classical
  have hsub : (L.toFinset : Set (Equiv.Perm (Fin n))) ⊆ S := fun x hx =>
    hS x (List.mem_toFinset.mp hx)
  have hcard : S.ncard ≤ (L.toFinset : Set (Equiv.Perm (Fin n))).ncard := by
    rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hL]
    exact hlen
  have heq := Set.eq_of_subset_of_ncard_le hsub hcard (Set.toFinite _)
  intro y hy
  have : y ∈ (L.toFinset : Set (Equiv.Perm (Fin n))) := by rw [heq]; exact hy
  exact List.mem_toFinset.mp this

theorem conjClosure_cover {P : Subgroup (Equiv.Perm (Fin n))} {pg pgInv : Array Table}
    {gg : ℕ → Equiv.Perm (Fin n)} {sift : Table → Bool} (hD : GroupData n P pg gg sift)
    (hpgi : ∀ l < pg.size, Rep n pgInv[l]! (gg l)⁻¹) {t : Table} {tg : Equiv.Perm (Fin n)}
    (hT : Rep n t tg) {o : Closure} (horb : conjTreeOK n pg pgInv t o.1 o.2.1 o.2.2 = true)
    (hdist : hkeysDistinct n o.1.toList = true) (hsize : (conjClass P tg).ncard ≤ o.1.size) :
    (∀ k < o.1.size, ∃ c ∈ P, Rep n o.1[k]! (c * tg * c⁻¹)) ∧
      ∀ y ∈ conjClass P tg, ∃ k < o.1.size, Rep n o.1[k]! y := by
  have hgP : ∀ l < pg.size, Rep n pg[l]! (gg l) ∧ Rep n pgInv[l]! (gg l)⁻¹ ∧ gg l ∈ P :=
    fun l hl => ⟨hD.rep l hl, hpgi l hl, hD.mem hl⟩
  have horb' := conjTreeOK_spec P hgP hT horb
  refine ⟨horb', fun y hy => ?_⟩
  have horep : ∀ k < o.1.size, Rep n o.1[k]! (tablePerm n o.1[k]!) := by
    intro k hk
    obtain ⟨c, -, hrep⟩ := horb' k hk
    rw [tablePerm_eq hrep]
    exact hrep
  have honodup := nodup_of_hkeysDistinct (forall₂_tablePerm horep) hdist
  have hmem := mem_of_nodup_of_ncard_le honodup (S := conjClass P tg)
    (fun x hx => by
      obtain ⟨k, hk, rfl⟩ := mem_map_tablePerm horep hx
      obtain ⟨c, hc, hrep⟩ := horb' k hk
      rw [tablePerm_eq hrep]
      exact ⟨c, hc, rfl⟩)
    (by rw [List.length_map, Array.length_toList]; exact hsize) y hy
  obtain ⟨k, hk, rfl⟩ := mem_map_tablePerm horep hmem
  exact ⟨k, hk, horep k hk⟩

end CFSG.Sporadic.Recognition.McLAS
