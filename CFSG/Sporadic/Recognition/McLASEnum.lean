module

public import CFSG.Sporadic.Recognition.McLASThreeLocalInputs

public section

namespace CFSG.Sporadic.Recognition.McLAS

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

variable {n : ℕ}

structure EnumFacts (n : ℕ) (E : Array Table) (K : Subgroup (Equiv.Perm (Fin n))) : Prop where
  rep : ∀ k < E.size, Rep n E[k]! (tablePerm n E[k]!)
  mem : ∀ k < E.size, tablePerm n E[k]! ∈ K
  cover : ∀ x ∈ K, ∃ k < E.size, Rep n E[k]! x
  nodup : (E.toList.map (tablePerm n)).Nodup

structure SubEnumFacts (n : ℕ) (P : Subgroup (Equiv.Perm (Fin n))) (sg E : Array Table) (order : ℕ)
    (K : Subgroup (Equiv.Perm (Fin n))) : Prop where
  le : K ≤ P
  card : Nat.card K = order
  enum : EnumFacts n E K
  rep : ∀ g ∈ sg, Rep n g (tp n g)
  repInv : ∀ g ∈ sg, Rep n (invT n g) (tp n g)⁻¹

theorem subEnumOK_spec {P : Subgroup (Equiv.Perm (Fin n))} {pg : Array Table}
    {gg : ℕ → Equiv.Perm (Fin n)} {sift : Table → Bool} (hD : GroupData n P pg gg sift)
    {cap order : ℕ} {sg : Array Table} (h : subEnumOK n cap order sift sg = true) :
    SubEnumFacts n P sg (mulClosureH n sg cap).1 order (closure (tp n '' {x | x ∈ sg})) := by
  have hn := hD.lt
  simp only [subEnumOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  rw [Array.all_eq_true'] at h1
  simp only [Bool.and_eq_true] at h1
  have hg : ∀ x ∈ sg, permOK n x = true := fun x hx => (h1 x hx).1.1
  have hginv : ∀ x ∈ sg, invOK n x (invT n x) = true := fun x hx => (h1 x hx).2
  obtain ⟨hE1, hE2, hE3⟩ := enum_spec hn hg hginv h2 h3 h4
  refine ⟨?_, by rw [hE3]; exact h5, ?_, fun x hx => rep_tp (hg x hx), fun x hx =>
    Rep.inv_of_invOK (rep_tp (hg x hx)) (hginv x hx)⟩
  · rw [closure_le]
    rintro _ ⟨x, hx, rfl⟩
    exact (hD.sift _ _ (rep_tp (hg x hx))).1 (h1 x hx).1.2
  · refine ⟨fun k hk => (hE1 k hk).1, fun k hk => (hE1 k hk).2, hE2, ?_⟩
    exact nodup_of_hkeysDistinct (forall₂_tablePerm fun k hk => (hE1 k hk).1) h4

namespace EnumFacts

variable {E : Array Table} {K : Subgroup (Equiv.Perm (Fin n))} (hE : EnumFacts n E K)
include hE

theorem mem_of_memT {t : Table} {g : Equiv.Perm (Fin n)} (ht : Rep n t g)
    (h : memT n E t = true) : g ∈ K := by
  obtain ⟨j, hj, hjg⟩ := memT_spec hE.rep ht h
  rw [hjg]
  exact hE.mem j hj

theorem memT_of_mem {t : Table} {g : Equiv.Perm (Fin n)} (ht : Rep n t g) (hg : g ∈ K) :
    memT n E t = true := by
  obtain ⟨k, hk, hkrep⟩ := hE.cover g hg
  rw [memT, Array.any_eq_true]
  refine ⟨k, hk, ?_⟩
  rw [getElem!_pos E k hk] at hkrep
  exact (tblEq_iff_eq ht hkrep).2 rfl

theorem mem_iff_memT {t : Table} {g : Equiv.Perm (Fin n)} (ht : Rep n t g) :
    g ∈ K ↔ memT n E t = true :=
  ⟨hE.memT_of_mem ht, hE.mem_of_memT ht⟩

theorem ncard_filter (p : Table → Bool) (q : Equiv.Perm (Fin n) → Prop)
    (hpq : ∀ (t : Table) (g : Equiv.Perm (Fin n)), Rep n t g → (p t = true ↔ q g)) :
    ({x : Equiv.Perm (Fin n) | x ∈ K ∧ q x}).ncard = (E.toList.filter p).length := by
  classical
  have hset : {x : Equiv.Perm (Fin n) | x ∈ K ∧ q x} =
      (((E.toList.filter p).map (tablePerm n)).toFinset : Set (Equiv.Perm (Fin n))) := by
    ext x
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, List.mem_toFinset, List.mem_map, List.mem_filter]
    constructor
    · rintro ⟨hxK, hxq⟩
      obtain ⟨k, hk, hkrep⟩ := hE.cover x hxK
      refine ⟨E[k]!, ⟨Array.mem_toList_iff.mpr (getElem!_mem_array hk), ?_⟩, tablePerm_eq hkrep⟩
      exact (hpq _ _ hkrep).2 hxq
    · rintro ⟨e, ⟨hemem, hpe⟩, rfl⟩
      obtain ⟨k, hk, rfl⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp hemem)
      have hrk := hE.rep k hk
      rw [getElem!_pos E k hk] at hrk
      refine ⟨?_, (hpq _ _ hrk).1 hpe⟩
      have := hE.mem k hk
      rwa [getElem!_pos E k hk] at this
  have hlist : ((E.toList.filter p).map (tablePerm n)).Nodup :=
    hE.nodup.sublist ((List.filter_sublist).map _)
  rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup hlist, List.length_map]

end EnumFacts

end CFSG.Sporadic.Recognition.McLAS
