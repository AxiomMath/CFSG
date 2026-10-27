module

public import CFSG.Quasithin.Background.F3Paths
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Idx

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin U42F431

abbrev Vtx : Type := Fin 45 ⊕ Fin 27

abbrev lnF (k : Fin 27) : Set (Fin 45) := lnS k.val

theorem lnS_injective {i j : Fin 27} (h : lnF i = lnF j) :
    i = j := by
  rcases lines_spec.2.2.2.2.2 i i.2 j j.2 with h1 | h2
  · exact Fin.ext h1
  · exact absurd h (lineSet_ne_of_sameSet_false h2)

theorem exists_lnImg (g : Y) (k : Fin 27) :
    ∃ k' : Fin 27, (g : P45) '' lnF k = lnF k' := by
  obtain ⟨k', hk', h⟩ := line_stable g.2 k.2
  exact ⟨⟨k', hk'⟩, h⟩

@[expose] noncomputable def lnImg (g : Y) (k : Fin 27) : Fin 27 :=
  (exists_lnImg g k).choose

theorem lnImg_spec (g : Y) (k : Fin 27) :
    (g : P45) '' lnF k = lnF (lnImg g k) := (exists_lnImg g k).choose_spec

theorem lnImg_eq_iff {g : Y} {k k' : Fin 27} :
    lnImg g k = k' ↔ (g : P45) '' lnF k = lnF k' := by
  constructor
  · rintro rfl
    exact lnImg_spec g k
  · intro h
    exact lnS_injective ((lnImg_spec g k).symm.trans h)

theorem lnImg_one (k : Fin 27) : lnImg 1 k = k := by
  rw [lnImg_eq_iff]
  simp

theorem lnImg_mul (g h : Y) (k : Fin 27) :
    lnImg (g * h) k = lnImg g (lnImg h k) := by
  rw [lnImg_eq_iff, ← lnImg_spec g, ← lnImg_spec h]
  simp [Set.image_image]

noncomputable instance : MulAction Y (Fin 27) where
  smul := lnImg
  one_smul := lnImg_one
  mul_smul := lnImg_mul

theorem lnImg_def (g : Y) (k : Fin 27) : g • k = lnImg g k := rfl

theorem smul_lnS (g : Y) (k : Fin 27) :
    (g : P45) '' lnF k = lnF (g • k) := lnImg_spec g k

theorem smul_point (g : Y) (p : Fin 45) : g • p = (g : P45) p := rfl

@[expose] def incAdj : Vtx → Vtx → Prop
  | Sum.inl p, Sum.inr k => p ∈ lnF k
  | Sum.inr k, Sum.inl p => p ∈ lnF k
  | _, _ => False

@[expose] def incGraph : SimpleGraph Vtx where
  Adj := incAdj
  symm := ⟨fun a b h => by
    rcases a with p | k <;> rcases b with q | l
    · exact False.elim h
    · exact h
    · exact h
    · exact False.elim h⟩
  loopless := ⟨fun a h => by rcases a with p | k <;> exact False.elim h⟩

theorem adj_inl_inr {p : Fin 45} {k : Fin 27} : incGraph.Adj (Sum.inl p) (Sum.inr k) ↔ p ∈ lnF k :=
  Iff.rfl

theorem adj_inr_inl {p : Fin 45} {k : Fin 27} : incGraph.Adj (Sum.inr k) (Sum.inl p) ↔ p ∈ lnF k :=
  Iff.rfl

theorem not_adj_inl_inl (p q : Fin 45) : ¬ incGraph.Adj (Sum.inl p) (Sum.inl q) := fun h => h

theorem not_adj_inr_inr (k l : Fin 27) : ¬ incGraph.Adj (Sum.inr k) (Sum.inr l) := fun h => h

theorem mem_lnS_smul (g : Y) (p : Fin 45) (k : Fin 27) :
    g • p ∈ lnF (g • k) ↔ p ∈ lnF k := by
  rw [← smul_lnS, smul_point]
  exact (g : P45).injective.mem_set_image

instance : GraphAction Y incGraph where
  adj_smul g a b := by
    rcases a with p | k <;> rcases b with q | l
    · exact Iff.rfl
    · exact mem_lnS_smul g p l
    · exact mem_lnS_smul g q k
    · exact Iff.rfl

end CFSG.Quasithin.H13.F431.U42
