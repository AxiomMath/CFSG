module

public import CFSG.Quasithin.Background.B3Basic
public import CFSG.Quasithin.Background.B3Comp

public section

namespace CFSG.Quasithin.B3

variable {n : ℕ}

@[expose] def swapN (n a b : ℕ) : Gp n :=
  if h : a < n ∧ b < n then Equiv.swap ⟨a, h.1⟩ ⟨b, h.2⟩ else 1

@[expose] def ti (n i : ℕ) : Gp n := swapN n (2 * i) (2 * i + 1)

@[expose] def gensAm (n m : ℕ) : List (Gp n) := (List.range m).map (ti n)

@[expose] def Am (n m : ℕ) : Subgroup (Gp n) := Subgroup.closure {g | g ∈ gensAm n m}

@[expose] def Dsub (n : ℕ) : Subgroup (Gp n) := Am n (n / 2)

@[expose] def gensA0 (n : ℕ) : List (Gp n) :=
  [swapN n 0 1 * swapN n 2 3, swapN n 0 2 * swapN n 1 3] ++
    ((List.range (n / 2)).filter (fun i => 2 ≤ i)).map (ti n)

@[expose] def A0 (n : ℕ) : Subgroup (Gp n) := Subgroup.closure {g | g ∈ gensA0 n}

@[expose] def AmL (n m : ℕ) : List Tab := closeT n ((gensAm n m).map tab)

@[expose] def A0L (n : ℕ) : List Tab := closeT n ((gensA0 n).map tab)

@[expose] def chkGen (n : ℕ) (gensP : List (Gp n)) : Bool :=
  let S := closeT n (gensP.map tab)
  subOK n S && gensP.all (fun g => S.contains (tab g)) && chainOK (gensP.map tab) (idT n) [] S

theorem closure_eq_of_chkGen {gensP : List (Gp n)} (h : chkGen n gensP = true) :
    Subgroup.closure {g | g ∈ gensP} = subOf n (closeT n (gensP.map tab)) := by
  simp only [chkGen, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact closure_eq_subOf gensP _ h1 h2 h3

theorem subOf_congr {L L' : List Tab} (hL : subOK n L = true) (hL' : subOK n L' = true)
    (h : seteqT L L' = true) : subOf n L = subOf n L' := by
  simp only [seteqT, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
  ext x
  rw [mem_subOf hL, mem_subOf hL']
  exact ⟨fun hx => h.1 _ hx, fun hx => h.2 _ hx⟩

@[expose] def conjClass (S : Subgroup (Gp n)) : Set (Subgroup (Gp n)) := {A | ∃ γ : Gp n, A = cj γ S}

theorem mem_conjClass {S A : Subgroup (Gp n)} : A ∈ conjClass S ↔ ∃ γ : Gp n, A = cj γ S := Iff.rfl

end CFSG.Quasithin.B3
