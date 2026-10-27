module

public import Certificates.Data.D4HexF48Check
public import CFSG.Monster.B.Co2.PermArr

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.D4Hex CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

@[expose] def f48L0 : Finset (Fin 819) := {⟨0, by decide⟩, ⟨1, by decide⟩, ⟨5, by decide⟩}

@[expose] def f48WordVal {α : Type*} [Monoid α] (g : ℕ → α) : List ℕ → α
  | [] => 1
  | l :: w => g l * f48WordVal g w

theorem mem_f48L0_iff (p : Fin 819) : p ∈ f48L0 ↔ (p : ℕ) = 0 ∨ (p : ℕ) = 1 ∨ (p : ℕ) = 5 := by
  simp only [f48L0, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]

theorem image_f48L0_eq {ν : Equiv.Perm (Fin 819)} (h : ∀ p ∈ f48L0, ν p ∈ f48L0) :
    f48L0.image ν = f48L0 := by
  refine Finset.eq_of_subset_of_card_le (fun p hp => ?_)
    (le_of_eq (Finset.card_image_of_injective _ ν.injective).symm)
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hp
  exact h x hx

theorem rep_f48EvalW {G : Array (Array ℕ)} {g : ℕ → Equiv.Perm (Fin 819)}
    (hG : ∀ j < G.size, Rep 819 G[j]! (g j)) :
    ∀ w : List ℕ, (∀ l ∈ w, l < G.size) → Rep 819 (f48EvalW G w) (f48WordVal g w)
  | [], _ => by simpa [f48EvalW, f48WordVal] using (rep_idA (n := 819))
  | l :: w, hw => by
    rw [f48EvalW, f48WordVal]
    exact rep_compA (hG l (hw l List.mem_cons_self))
      (rep_f48EvalW hG w fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))

theorem f48LettersOK_spec {k : ℕ} {ws : List (List ℕ)} (h : f48LettersOK k ws = true) :
    ∀ w ∈ ws, ∀ l ∈ w, l < k := by
  intro w hw l hl
  simp only [f48LettersOK, List.all_eq_true, decide_eq_true_eq] at h
  exact h w hw l hl

theorem f48MapsL0_spec {a : Array ℕ} {ν : Equiv.Perm (Fin 819)} (ha : Rep 819 a ν)
    (h : f48MapsL0 a = true) : f48L0.image ν = f48L0 := by
  simp only [f48MapsL0, f48OnL0, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, or_assoc] at h
  obtain ⟨⟨h0, h1⟩, h5⟩ := h
  refine image_f48L0_eq fun p hp => ?_
  rw [mem_f48L0_iff] at hp ⊢
  rcases hp with hp | hp | hp
  · rw [← ha p, hp]
    exact h0
  · rw [← ha p, hp]
    exact h1
  · rw [← ha p, hp]
    exact h5

theorem f48InB_spec {a : Array ℕ} {ν : Equiv.Perm (Fin 819)} (ha : Rep 819 a ν)
    (h : f48InB a = true) : ν 0 = 0 ∧ f48L0.image ν = f48L0 := by
  simp only [f48InB, Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨Fin.ext ?_, f48MapsL0_spec ha h.2⟩
  rw [← ha 0]
  exact h.1

theorem f48NOK_spec {n : Array ℕ} {ν : Equiv.Perm (Fin 819)} (hn : Rep 819 n ν)
    (h : f48NOK n = true) : ν * ν = 1 ∧ ν 0 = 0 := by
  simp only [f48NOK, Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨(eqA_iff (rep_compA hn hn) rep_idA).1 h.1.1, Fin.ext ?_⟩
  rw [← hn 0]
  exact h.1.2

theorem f48LayOK_spec {lay : Array ℕ} {p0 : ℕ} (h : f48LayOK lay p0 = true) :
    lay[p0]! = 6 ∧ ∀ x < 819, lay[x]! ≤ 4 ∨ lay[x]! = 6 := by
  simp only [f48LayOK, Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨h.1, fun x hx => ?_⟩
  have := allLt_spec h.2 hx
  simpa only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] using this

theorem f48FOK_spec {n : Array ℕ} {F : Array (Array ℕ)} (h : f48FOK n F = true) {j : ℕ}
    (hj : j < F.size) : f48InB F[j]! = true ∧ f48InB (f48Conj n F[j]!) = true := by
  have := allLt_spec h hj
  simpa only [Bool.and_eq_true] using this

theorem f48BsOK_spec {bs : Array (Array ℕ)} (h : f48BsOK bs = true) :
    bs.size = 8 ∧ ∀ j < bs.size, f48InB bs[j]! = true := by
  simp only [f48BsOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, fun j hj => allLt_spec h.2 hj⟩

theorem f48OrbOK_facts {lay : Array ℕ} {F : Array (Array ℕ)} {r : OrbRec} {p0 : ℕ}
    (h : f48OrbOK lay F r p0 = true) :
    r.ord[0]! = p0 ∧ (∀ i < 512, r.ord[i]! < 819) ∧
      (∀ i, 0 < i → i < 512 → r.par[i]! < i ∧ r.lab[i]! < F.size ∧
        (F[r.lab[i]!]!)[r.ord[r.par[i]!]!]! = r.ord[i]!) ∧
      ∀ x < 819, lay[x]! = 6 → r.pos[x]! < 512 ∧ r.ord[r.pos[x]!]! = x := by
  simp only [f48OrbOK, orbOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, h0⟩, hlt⟩, hstep⟩, hcov⟩ := h
  refine ⟨h0, fun i hi => ?_, fun i hi0 hi => ?_, fun x hx hl => ?_⟩
  · simpa only [decide_eq_true_eq] using allLt_spec hlt hi
  · have := allLt_spec hstep hi
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at this
    rcases this with h1 | ⟨⟨h1, h2⟩, h3⟩
    · omega
    · exact ⟨h1, h2, h3⟩
  · have := allLt_spec hcov hx
    simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true, decide_eq_true_eq,
      beq_iff_eq, hl, beq_self_eq_true] at this
    simpa using this

theorem f48KeyAll_spec {lay : Array ℕ} {F : Array (Array ℕ)} {r : OrbRec} {M p0 : ℕ}
    {n q : Array ℕ} (h : f48KeyAll lay F r M p0 n q = true) {k : ℕ} (hk : k < 819)
    (hl : lay[k]! = 6) :
    f48CandOK lay F r p0 (f48TArr F r p0 k) k = true ∧
      (k = p0 → eqA 819 (f48TArr F r p0 k) (idA 819) = true) ∧
      (k ≠ p0 → f48FullFail M n q (f48TArr F r p0 k) = true) := by
  have := allLt_spec h hk
  simp only [f48KeyOK, hl, beq_self_eq_true, Bool.not_true, Bool.false_or,
    Bool.and_eq_true] at this
  refine ⟨this.1, fun hkp => ?_, fun hkp => ?_⟩
  · simpa [hkp] using this.2
  · simpa [hkp] using this.2

theorem f48In3_iff {x a b c : ℕ} : f48In3 x a b c = true ↔ x = a ∨ x = b ∨ x = c := by
  simp [f48In3, or_assoc]

theorem f48LinesOK_spec {lineTab n : Array ℕ} {bs : Array (Array ℕ)}
    (h : f48LinesOK lineTab n bs = true) {l : ℕ} (hl : l < 2457)
    (h0 : f48LineHas0 lineTab l = true) :
    f48LineIn lineTab l 0 1 5 = true ∨
      ∃ j < 8, f48LineInImg lineTab l (compA 819 bs[j]! n) = true := by
  have := allLt_spec h hl
  simp only [h0, Bool.not_true, Bool.false_or, Bool.or_eq_true, List.any_eq_true,
    List.mem_range] at this
  rcases this with h1 | ⟨j, hj, h2⟩
  · exact Or.inl h1
  · exact Or.inr ⟨j, hj, h2⟩

theorem f48FixOK_spec {F : Array (Array ℕ)} (h : f48FixOK F = true) {x : ℕ} (hx : x < 819)
    (hfix : ∀ j < F.size, F[j]![x]! = x) : x = 0 := by
  have h1 := allLt_spec h hx
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at h1
  rcases h1 with h0 | h1
  · exact h0
  · have h2 : allLt F.size (fun j => F[j]![x]! == x) = true :=
      allLt_iff.2 fun j hj => beq_iff_eq.2 (hfix j hj)
    rw [h2] at h1
    exact absurd h1 (by decide)

theorem hexF48Check_spec {M p0 : ℕ} {nW qW : List ℕ} {fW bW : List (List ℕ)}
    {lineTab lay : Array ℕ} {G : Array (Array ℕ)}
    (h : hexF48Check M p0 nW qW fW bW lineTab lay G = true) :
    M < 2 ^ 40 ∧ f48LettersOK G.size ([nW, qW] ++ fW ++ bW) = true ∧
      f48NOK (f48EvalW G nW) = true ∧ f48MapsL0 (f48EvalW G qW) = true ∧
      f48FOK (f48EvalW G nW) (f48WordArrs G fW) = true ∧ f48BsOK (f48WordArrs G bW) = true ∧
      f48LayOK lay p0 = true ∧
      f48OrbOK lay (f48WordArrs G fW) (f48Rec (f48WordArrs G fW) p0) p0 = true ∧
      f48KeyAll lay (f48WordArrs G fW) (f48Rec (f48WordArrs G fW) p0) M p0 (f48EvalW G nW)
        (f48EvalW G qW) = true ∧
      f48LinesOK lineTab (f48EvalW G nW) (f48WordArrs G bW) = true ∧
      f48FixOK (f48WordArrs G fW) = true := by
  simpa only [hexF48Check, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using h

end CFSG.Quasithin.D4Hex
