module

public import CFSG.Quasithin.Background.F918U4

public section

set_option exponentiation.threshold 2048

namespace CFSG.Quasithin.D35Chk

attribute [local irreducible] invMask

@[expose] def Step (nd nd' : Node) : Prop := ∃ g, nd.M.testBit g = true ∧ nd' = childOf nd g

@[expose] def Reach (nd : Node) : Prop := Relation.ReflTransGen Step root nd

@[expose] def Cov (nd : Node) (rem : ℕ) : Prop :=
  ∀ g, rem.testBit g = true → ∀ nd', Relation.ReflTransGen Step (childOf nd g) nd' → nodeOK nd' = true

theorem childOf_M_lt (nd : Node) (g : ℕ) : (childOf nd g).M < 2 ^ 1024 :=
  Nat.and_lt_two_pow _ (look_lt _ _ _)

private theorem topBit_spec {r : ℕ} (h0 : r ≠ 0) (h1 : r < 2 ^ 1024) :
    r.testBit (topBit r) = true ∧ topBit r < 1024 := by
  rw [topBit_eq_log2 (Nat.pos_of_ne_zero h0) h1]
  exact ⟨Nat.testBit_log2 h0, (Nat.log2_lt h0).2 h1⟩

private theorem xor_pow_lt {r g : ℕ} (h1 : r < 2 ^ 1024) (hg : g < 1024) : r ^^^ 2 ^ g < 2 ^ 1024 :=
  Nat.xor_lt_two_pow h1 (Nat.pow_lt_pow_right Nat.one_lt_two hg)

private theorem testBit_xor_pow (r g g' : ℕ) :
    (r ^^^ 2 ^ g).testBit g' = (r.testBit g' ^^ decide (g = g')) := by
  rw [Nat.testBit_xor, Nat.testBit_two_pow]

theorem runAux_sound : ∀ (f : ℕ) (st : List (Node × ℕ)), (∀ fr ∈ st, fr.2 < 2 ^ 1024) →
    runAux f st = true → ∀ fr ∈ st, Cov fr.1 fr.2 := by
  intro f
  induction f with
  | zero =>
    intro st _ h fr hfr
    have : st = [] := by simpa [runAux] using h
    subst this
    simp at hfr
  | succ f ih =>
    intro st hlt h
    rcases st with _ | ⟨⟨nd, rem⟩, rest⟩
    · intro fr hfr
      simp at hfr
    · have hrest : ∀ fr ∈ rest, fr.2 < 2 ^ 1024 := fun fr hfr => hlt fr (List.mem_cons_of_mem _ hfr)
      have hrem : rem < 2 ^ 1024 := hlt (nd, rem) List.mem_cons_self
      by_cases h0 : rem = 0
      · subst h0
        have h' : runAux f rest = true := by simpa [runAux] using h
        intro fr hfr
        rcases List.mem_cons.1 hfr with rfl | hfr
        · intro g hg
          simp at hg
        · exact ih rest hrest h' fr hfr
      · obtain ⟨hbit, hg1024⟩ := topBit_spec h0 hrem
        have hb : Nat.beq rem 0 = false := by
          rw [Bool.eq_false_iff]
          intro hb
          exact h0 (Nat.eq_of_beq_eq_true hb)
        have h' : nodeOK (childOf nd (topBit rem)) = true ∧
            runAux f ((childOf nd (topBit rem), (childOf nd (topBit rem)).M) ::
              (nd, Nat.xor rem (Nat.pow 2 (topBit rem))) :: rest) = true := by
          simpa [runAux, hb] using h
        obtain ⟨hok, hrec⟩ := h'
        have hlt' : ∀ fr ∈ ((childOf nd (topBit rem), (childOf nd (topBit rem)).M) ::
              (nd, Nat.xor rem (Nat.pow 2 (topBit rem))) :: rest), fr.2 < 2 ^ 1024 := by
          intro fr hfr
          rcases List.mem_cons.1 hfr with rfl | hfr
          · exact childOf_M_lt _ _
          · rcases List.mem_cons.1 hfr with rfl | hfr
            · exact xor_pow_lt hrem hg1024
            · exact hrest fr hfr
        have key := ih _ hlt' hrec
        have hCh := key (childOf nd (topBit rem), (childOf nd (topBit rem)).M) List.mem_cons_self
        have hNd := key (nd, Nat.xor rem (Nat.pow 2 (topBit rem))) (by simp)
        intro fr hfr
        rcases List.mem_cons.1 hfr with rfl | hfr
        · intro g' hg' nd' hpath
          by_cases hgg : g' = topBit rem
          · subst hgg
            rcases Relation.ReflTransGen.cases_head hpath with rfl | ⟨c, ⟨g'', hg'', rfl⟩, hrest'⟩
            · exact hok
            · exact hCh g'' hg'' nd' hrest'
          · refine hNd g' ?_ nd' hpath
            simp only [Nat.pow_eq, Nat.xor_eq]
            rw [testBit_xor_pow, hg']
            simp [Ne.symm hgg]
        · exact ih _ hlt' hrec _ (by simp [hfr])

private theorem root_M_lt : root.M < 2 ^ 1024 := by
  simp only [root]
  exact invMask_lt

private theorem run_eq : run = runAux 20000 [(root, root.M)] := rfl

theorem run_sound (h : run = true) : ∀ nd, Reach nd → nodeOK nd = true := by
  rw [run_eq] at h
  have hlt : ∀ fr ∈ [(root, root.M)], fr.2 < 2 ^ 1024 := by
    intro fr hfr
    rw [List.mem_singleton] at hfr
    subst hfr
    exact root_M_lt
  have hcov : Cov root root.M :=
    runAux_sound 20000 [(root, root.M)] hlt h (root, root.M) List.mem_cons_self
  intro nd hnd
  rcases Relation.ReflTransGen.cases_head hnd with rfl | ⟨c, ⟨g, hg, rfl⟩, hrest⟩
  · simp [nodeOK, root]
  · exact hcov g hg nd hrest

end CFSG.Quasithin.D35Chk
