module

public import CFSG.Monster.GMS.Griess13.Data
public import CFSG.Monster.GMS.Griess13.ChecksOrbitTab
public import Certificates.Certificate10034
public meta import CFSG.Monster.GMS.Griess13.Data
public meta import Mathlib
public meta import CFSG.Sporadic.Co1Base
public import CFSG.Sporadic.Co1Base
public meta import CFSG.Sporadic.Th.F2Spec
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.Monster.GMS.Griess13.Co1Data

open scoped Matrix

private theorem codeOf_lt : ∀ v : Fin 6 → ZMod 3, codeOf v < 729 :=
  Certificates.certificate10034.1

private theorem vecOfCode_codeOf :
    ∀ v : Fin 6 → ZMod 3, vecOfCode (codeOf v) = v :=
  Certificates.certificate10034.2.1

private theorem codeOf_pos :
    ∀ v : Fin 6 → ZMod 3, v ≠ 0 → 0 < codeOf v :=
  Certificates.certificate10034.2.2.1

private theorem vecOfCode_ne_zero :
    ∀ c < 729, 0 < c → vecOfCode c ≠ 0 :=
  Certificates.certificate10034.2.2.2.1

private theorem vecOfCode_stepS :
    ∀ s : Fin 2, ∀ c < 729, vecOfCode (stepS s.val c) = actN s *ᵥ vecOfCode c :=
  Certificates.certificate10034.2.2.2.2.1

private theorem orbCheckR_true :
    orbCheckR = true :=
  Certificates.certificate10034.2.2.2.2.2.1

private theorem orbCheckR_spec
    {c : ℕ} (hc : c < 729) (h0 : c ≠ 0) :
    (orbTabR.1[c]! = 1 ∨ orbTabR.1[c]! = 2 ∨ orbTabR.1[c]! = 3) ∧
    ((c = repCode orbTabR.1[c]! ∧ orbTabR.2.1[c]! = 0) ∨
      (c ≠ repCode orbTabR.1[c]! ∧ 0 < orbTabR.2.2.1[c]! ∧ orbTabR.2.2.1[c]! < 729 ∧
        orbTabR.2.2.2[c]! < 2 ∧ stepS orbTabR.2.2.2[c]! orbTabR.2.2.1[c]! = c ∧
        orbTabR.1[orbTabR.2.2.1[c]!]! = orbTabR.1[c]! ∧
        orbTabR.2.1[orbTabR.2.2.1[c]!]! < orbTabR.2.1[c]!)) := by
  have h := List.all_eq_true.1 orbCheckR_true c (List.mem_range.2 hc)
  have h0' : (c == 0) = false := by simpa using h0
  rw [h0', Bool.false_or, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  simp only [Bool.or_eq_true, beq_iff_eq] at h1
  refine ⟨or_assoc.1 h1, ?_⟩
  by_cases hr : c = repCode orbTabR.1[c]!
  · left
    refine ⟨hr, ?_⟩
    have hr' : (c == repCode orbTabR.1[c]!) = true := by simpa using hr
    rw [hr'] at h2
    simpa using h2
  · right
    refine ⟨hr, ?_⟩
    have hr' : (c == repCode orbTabR.1[c]!) = false := by simpa using hr
    rw [hr'] at h2
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq,
      beq_iff_eq] at h2
    obtain ⟨⟨⟨⟨⟨h3, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h2
    exact ⟨h3, h4, h5, h6, h7, h8⟩

private theorem f_orbit
    (f : (Fin 6 → ZMod 3) → ℕ)
    (hf : ∀ s : Fin 2, ∀ w, w ≠ 0 → f (actN s *ᵥ w) = f w) :
    ∀ n c, c < 729 → c ≠ 0 → orbTabR.2.1[c]! = n →
      f (vecOfCode c) = f (vecOfCode (repCode orbTabR.1[c]!)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c hc h0 hd
    rcases (orbCheckR_spec hc h0).2 with ⟨hr, _⟩ | ⟨_, hp0, hp729, hs, hstep, hcls, hdist⟩
    · rw [← hr]
    · set p := orbTabR.2.2.1[c]! with hp
      have hpne : p ≠ 0 := Nat.pos_iff_ne_zero.1 hp0
      have hvec : vecOfCode c = actN ⟨orbTabR.2.2.2[c]!, hs⟩ *ᵥ vecOfCode p := by
        have := vecOfCode_stepS ⟨orbTabR.2.2.2[c]!, hs⟩ p hp729
        rw [show (⟨orbTabR.2.2.2[c]!, hs⟩ : Fin 2).val = orbTabR.2.2.2[c]! from rfl, hstep] at this
        exact this
      rw [hvec, hf _ _ (vecOfCode_ne_zero p hp729 hp0)]
      have := ih (orbTabR.2.1[p]!) (hd ▸ hdist) p hp729 hpne rfl
      rw [this, hcls]

private theorem vecOfCode_repCode
    (k : ℕ) : vecOfCode (repCode k) = repVec k :=
  vecOfCode_codeOf (repVec k)

theorem repVec_one : repVec 1 = w1 := by simp [repVec]

theorem repVec_two : repVec 2 = wB := by simp [repVec]

theorem repVec_three : repVec 3 = wC := by simp [repVec]

theorem orbitClassR_repw :
    ∀ k : Fin 12, orbitClassR (repw k) = 1 :=
  Certificates.certificate10034.2.2.2.2.2.2.1

theorem orbitClassR_w1 :
    orbitClassR w1 = 1 :=
  Certificates.certificate10034.2.2.2.2.2.2.2.1

theorem orbitClassR_wB :
    orbitClassR wB = 2 :=
  Certificates.certificate10034.2.2.2.2.2.2.2.2.1

theorem orbitClassR_wC :
    orbitClassR wC = 3 :=
  Certificates.certificate10034.2.2.2.2.2.2.2.2.2.1

theorem orbitClassR_neg :
    ∀ w : Fin 6 → ZMod 3, orbitClassR (-w) = orbitClassR w :=
  Certificates.certificate10034.2.2.2.2.2.2.2.2.2.2.1

theorem orbitClassR_one_spec :
    ∀ w : Fin 6 → ZMod 3, w ≠ 0 → orbitClassR w = 1 →
    ∃ k : Fin 12, ∃ c : ZMod 3, c ≠ 0 ∧ w = c • repw k :=
  Certificates.certificate10034.2.2.2.2.2.2.2.2.2.2.2.1

theorem card_orbitClassR_one :
    ((Finset.univ.erase (0 : Fin 6 → ZMod 3)).filter fun w => orbitClassR w = 1).card = 24 :=
  Certificates.certificate10034.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem card_orbitClassR_two :
    ((Finset.univ.erase (0 : Fin 6 → ZMod 3)).filter fun w => orbitClassR w = 2).card = 264 :=
  Certificates.certificate10034.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem card_orbitClassR_three :
    ((Finset.univ.erase (0 : Fin 6 → ZMod 3)).filter fun w => orbitClassR w = 3).card = 440 :=
  Certificates.certificate10034.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem orbitClassR_mem
    {w : Fin 6 → ZMod 3} (hw : w ≠ 0) :
    orbitClassR w = 1 ∨ orbitClassR w = 2 ∨ orbitClassR w = 3 :=
  (orbCheckR_spec (codeOf_lt w) (codeOf_pos w hw).ne').1

theorem orbitIndexR_neg
    (w : Fin 6 → ZMod 3) : orbitIndexR (-w) = orbitIndexR w := by
  unfold orbitIndexR
  rw [orbitClassR_neg]

theorem orbitIndexR_repw
    (k : Fin 12) : orbitIndexR (repw k) = 0 := by
  simp [orbitIndexR, orbitClassR_repw]

theorem orbitIndexR_w1 :
    orbitIndexR w1 = 0 := by
  simp [orbitIndexR, orbitClassR_w1]

theorem orbitClassR_eq_of_orbitIndexR_eq
    {w w' : Fin 6 → ZMod 3} (hw : w ≠ 0) (hw' : w' ≠ 0)
    (h : orbitIndexR w = orbitIndexR w') : orbitClassR w = orbitClassR w' := by
  unfold orbitIndexR at h
  rcases orbitClassR_mem hw with h1 | h1 | h1 <;> rcases orbitClassR_mem hw' with h2 | h2 | h2 <;>
    simp [h1, h2] at h ⊢

theorem card_orbitIndexR_zero :
    (Finset.univ.filter fun w : Fin 6 → ZMod 3 => w ≠ 0 ∧ orbitIndexR w = 0).card = 24 :=
  Certificates.certificate10034.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem card_orbitIndexR_one :
    (Finset.univ.filter fun w : Fin 6 → ZMod 3 => w ≠ 0 ∧ orbitIndexR w = 1).card = 264 :=
  Certificates.certificate10034.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem card_orbitIndexR_two :
    (Finset.univ.filter fun w : Fin 6 → ZMod 3 => w ≠ 0 ∧ orbitIndexR w = 2).card = 440 :=
  Certificates.certificate10034.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem invariant_eq_rep
    (f : (Fin 6 → ZMod 3) → ℕ)
    (hf : ∀ s : Fin 2, ∀ w, w ≠ 0 → f (actN s *ᵥ w) = f w) {w : Fin 6 → ZMod 3} (hw : w ≠ 0) :
    f w = f (repVec (orbitClassR w)) := by
  have := f_orbit f hf _ (codeOf w) (codeOf_lt w) (codeOf_pos w hw).ne' rfl
  rwa [vecOfCode_codeOf, vecOfCode_repCode] at this

theorem eqvGen_to_rep
    (Rel : (Fin 6 → ZMod 3) → (Fin 6 → ZMod 3) → Prop)
    (hRel : ∀ s : Fin 2, ∀ w, w ≠ 0 → Rel (actN s *ᵥ w) w) {w : Fin 6 → ZMod 3} (hw : w ≠ 0) :
    Relation.EqvGen Rel w (repVec (orbitClassR w)) := by
  classical
  set f : (Fin 6 → ZMod 3) → ℕ :=
    fun v => if Relation.EqvGen Rel (repVec (orbitClassR w)) v then 1 else 0 with hfdef
  have hf : ∀ s : Fin 2, ∀ v, v ≠ 0 → f (actN s *ᵥ v) = f v := by
    intro s v hv
    have h1 : Relation.EqvGen Rel (actN s *ᵥ v) v := Relation.EqvGen.rel _ _ (hRel s v hv)
    simp only [hfdef]
    by_cases h : Relation.EqvGen Rel (repVec (orbitClassR w)) v
    · have : Relation.EqvGen Rel (repVec (orbitClassR w)) (actN s *ᵥ v) :=
        h.trans _ _ _ h1.symm
      simp [h, this]
    · have : ¬ Relation.EqvGen Rel (repVec (orbitClassR w)) (actN s *ᵥ v) := fun h2 =>
        h (h2.trans _ _ _ h1)
      simp [h, this]
  have hw' := invariant_eq_rep f hf hw
  have hrep : f (repVec (orbitClassR w)) = 1 := by
    simp [hfdef, Relation.EqvGen.refl]
  rw [hrep] at hw'
  by_contra hcon
  have hn : ¬ Relation.EqvGen Rel (repVec (orbitClassR w)) w := fun h => hcon h.symm
  have : f w = 0 := by simp [hfdef, hn]
  omega

theorem orbits_of_invariant
    (f : (Fin 6 → ZMod 3) → ℕ)
    (hf : ∀ s : Fin 2, ∀ w, w ≠ 0 → f (actN s *ᵥ w) = f w) :
    (∀ k : Fin 12, f (repw k) = f w1) ∧
    (∀ w : Fin 6 → ZMod 3, w ≠ 0 →
      ((∃ k : Fin 12, ∃ c : ZMod 3, c ≠ 0 ∧ w = c • repw k) ∧ f w = f w1) ∨
        f w = f wB ∨ f w = f wC) ∧
    ∑ w ∈ Finset.univ.erase (0 : Fin 6 → ZMod 3), f w =
      24 * f w1 + 264 * f wB + 440 * f wC := by
  have e1 : f (repVec 1) = f w1 := by rw [repVec_one]
  have e2 : f (repVec 2) = f wB := by rw [repVec_two]
  have e3 : f (repVec 3) = f wC := by rw [repVec_three]
  have hne : ∀ k : Fin 12, repw k ≠ 0 :=
    Certificates.certificate10034.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  refine ⟨fun k => ?_, fun w hw => ?_, ?_⟩
  · rw [invariant_eq_rep f hf (hne k), orbitClassR_repw, e1]
  · rcases orbitClassR_mem hw with h | h | h
    · left
      exact ⟨orbitClassR_one_spec w hw h, by rw [invariant_eq_rep f hf hw, h, e1]⟩
    · right; left
      rw [invariant_eq_rep f hf hw, h, e2]
    · right; right
      rw [invariant_eq_rep f hf hw, h, e3]
  · classical
    set F : ℕ → ℕ := fun k => f (repVec k) with hF
    have h1 : ∀ w ∈ Finset.univ.erase (0 : Fin 6 → ZMod 3), f w = F (orbitClassR w) := by
      intro w hw
      exact invariant_eq_rep f hf (Finset.ne_of_mem_erase hw)
    rw [Finset.sum_congr rfl h1,
      ← Finset.sum_fiberwise_of_maps_to (g := orbitClassR) (t := ({1, 2, 3} : Finset ℕ))
        (fun w hw => by
          have := orbitClassR_mem (Finset.ne_of_mem_erase hw)
          simp only [Finset.mem_insert, Finset.mem_singleton]
          exact this)]
    have key : ∀ k ∈ ({1, 2, 3} : Finset ℕ),
        ∑ w ∈ (Finset.univ.erase (0 : Fin 6 → ZMod 3)).filter (fun w => orbitClassR w = k),
          F (orbitClassR w) =
        ((Finset.univ.erase (0 : Fin 6 → ZMod 3)).filter
          (fun w => orbitClassR w = k)).card * F k := by
      intro k _
      rw [Finset.sum_congr rfl (fun w hw => by rw [(Finset.mem_filter.1 hw).2])]
      simp
    rw [Finset.sum_congr rfl key]
    simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton,
      show (1 : ℕ) ≠ 2 from by decide, show (1 : ℕ) ≠ 3 from by decide,
      show (2 : ℕ) ≠ 3 from by decide, or_self, not_false_eq_true]
    rw [card_orbitClassR_one, card_orbitClassR_two, card_orbitClassR_three]
    simp only [hF, e1, e2, e3]
    ring

end CFSG.Monster.GMS.Griess13.Co1Data
