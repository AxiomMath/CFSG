module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Z2Loc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PConj
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P62DCin
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5Stmt
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6LemD

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P62

@[expose] def Br (Γ : SimpleGraph V) (d ν l : V) : Prop := Γ.Adj d ν ∧ Γ.Adj ν l ∧ l ≠ d

theorem Br.symm {d ν l : V} (h : Br Γ d ν l) : Br Γ l ν d :=
  ⟨h.2.1.symm, h.1.symm, h.2.2.symm⟩

theorem Br.dist_two (F : FanTree Γ G) {d ν l : V} (h : Br Γ d ν l) : Γ.dist d l = 2 := by
  have := Arc.dist_eq F.isTree (Arc.two h.1 h.2.1 h.2.2.symm) 2 le_rfl
  rwa [Arc.two_vert_zero, Arc.two_vert_two] at this

theorem exists_br (F : FanTree Γ G) {d l : V} (h : Γ.dist d l = 2) : ∃ ν, Br Γ d ν l := by
  obtain ⟨ν, h1, h2⟩ := exists_mid F h
  refine ⟨ν, h1, h2, fun hl => ?_⟩
  rw [hl, dist_self] at h
  omega

theorem Br.unique (F : FanTree Γ G) {d ν ν' l : V} (h : Br Γ d ν l) (h' : Br Γ d ν' l) :
    ν = ν' :=
  F.eq_of_adj_adj h.1 h.2.1 h'.1 h'.2.1 h.2.2.symm

theorem Br.smul (F : FanTree Γ G) (g : G) {d ν l : V} (h : Br Γ d ν l) :
    Br Γ (g • d) (g • ν) (g • l) :=
  ⟨(F.adj_smul g _ _).2 h.1, (F.adj_smul g _ _).2 h.2.1, fun e => h.2.2 (MulAction.injective g e)⟩

theorem Br.valence (F : FanTree Γ G) {d ν l : V} (hd : valence Γ d = 5) (h : Br Γ d ν l) :
    valence Γ ν = 3 ∧ valence Γ l = 5 :=
  ⟨F.val3_of_adj_val5 h.1 hd, F.val5_of_adj_val3 h.2.1 (F.val3_of_adj_val5 h.1 hd)⟩

theorem exists_sibling (F : FanTree Γ G) {d ν l : V} (hd : valence Γ d = 5) (h : Br Γ d ν l) :
    ∃ l', Br Γ d ν l' ∧ l' ≠ l ∧ Γ.neighborSet ν = {d, l, l'} := by
  have hν : (Γ.neighborSet ν).ncard = 3 := by
    rw [← Nat.card_coe_set_eq]
    exact (Br.valence F hd h).1
  have hfin : (Γ.neighborSet ν).Finite := (F.ncard_neighborSet_le ν).2
  have hdl : d ≠ l := h.2.2.symm
  have hsub : ({d, l} : Set V) ⊆ Γ.neighborSet ν := by
    rintro x (rfl | rfl)
    · exact h.1.symm
    · exact h.2.1
  obtain ⟨l', hl', hn⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard
    (s := ({d, l} : Set V)) (t := Γ.neighborSet ν) (by rw [Set.ncard_pair hdl, hν]; omega)
  have hl'd : l' ≠ d := fun e => hn (Or.inl e)
  have hl'l : l' ≠ l := fun e => hn (Or.inr e)
  refine ⟨l', ⟨h.1, hl', hl'd⟩, hl'l, ?_⟩
  symm
  refine Set.eq_of_subset_of_ncard_le ?_ ?_ hfin
  · rintro x (rfl | rfl | rfl)
    · exact h.1.symm
    · exact h.2.1
    · exact hl'
  · rw [hν, Set.ncard_insert_of_notMem (by simp [hdl, hl'd.symm]), Set.ncard_pair hl'l.symm]

theorem br_cases (F : FanTree Γ G) {d ν l l' m : V} (hd : valence Γ d = 5) (h : Br Γ d ν l)
    (h' : Br Γ d ν l') (hne : l ≠ l') (hm : Br Γ d ν m) : m = l ∨ m = l' := by
  obtain ⟨l'', hl'', hne'', hset⟩ := exists_sibling F hd h
  have h1 : l'' = l' := by
    have hmem : l' ∈ Γ.neighborSet ν := h'.2.1
    rw [hset] at hmem
    rcases hmem with e | e | e
    · exact absurd e h'.2.2
    · exact absurd e.symm hne
    · exact e.symm
  have hmem : m ∈ Γ.neighborSet ν := hm.2.1
  rw [hset] at hmem
  rcases hmem with e | e | e
  · exact absurd e hm.2.2
  · exact Or.inl e
  · exact Or.inr (e.trans h1)

theorem dist_four (F : FanTree Γ G) {d ν ν' l l' : V} (h : Br Γ d ν l) (h' : Br Γ d ν' l')
    (hνν : ν ≠ ν') : Γ.dist l l' = 4 := by
  let P : Arc Γ 4 :=
    { vert := fun i => if i = 0 then l else if i = 1 then ν else if i = 2 then d else
        if i = 3 then ν' else l'
      adj := fun i hi => by
        interval_cases i
        · simpa using h.2.1.symm
        · simpa using h.1.symm
        · simpa using h'.1
        · simpa using h'.2.1
      nb := fun i hi => by
        have hi2 : i ≤ 2 := by omega
        interval_cases i
        · simpa using h.2.2
        · simpa using hνν
        · simpa using h'.2.2.symm }
  have := Arc.dist_eq F.isTree P 4 le_rfl
  simpa [P] using this

theorem Br.of_mem_nbrStab (F : FanTree Γ G) {d ν l : V} {k : G} (hk : k ∈ nbrStab Γ G d)
    (h : Br Γ d ν l) : Br Γ d ν (k • l) := by
  have hkd : k • d = d := MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer d hk)
  have hkν : k • ν = ν := mem_nbrStab.1 hk ν h.1
  refine ⟨h.1, ?_, fun e => h.2.2 ?_⟩
  · have := (F.adj_smul k ν l).2 h.2.1
    rwa [hkν] at this
  · apply MulAction.injective k
    show k • l = k • d
    rw [hkd]
    exact e

theorem nbrStab_swap (F : FanTree Γ G) {d ν l l' : V} {k : G} (hd : valence Γ d = 5)
    (hk : k ∈ nbrStab Γ G d) (h : Br Γ d ν l) (h' : Br Γ d ν l') (hne : l ≠ l') :
    k • l = l ∨ k • l = l' :=
  br_cases F hd h h' hne (Br.of_mem_nbrStab F hk h)

end P62

end CFSG.Quasithin.Fan86
