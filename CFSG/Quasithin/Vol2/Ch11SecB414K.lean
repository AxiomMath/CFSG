module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.SetLike.Fintype
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.Quasithin.H13.Ch4.B414

variable {U : Type} [AddCommGroup U] [Module (ZMod 2) U] (t : U →+ U)

@[expose] def fixRel (B A : AddSubgroup U) : AddSubgroup U where
  carrier := {a | a ∈ A ∧ t a - a ∈ B}
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨A.add_mem ha hb, ?_⟩
    rw [map_add, add_sub_add_comm]
    exact B.add_mem ha' hb'
  zero_mem' := ⟨A.zero_mem, by rw [map_zero, sub_zero]; exact B.zero_mem⟩
  neg_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨A.neg_mem ha, ?_⟩
    rw [map_neg, neg_sub_neg, ← neg_sub]
    exact B.neg_mem ha'

theorem two_smul_eq (u : U) : u + u = 0 := by
  rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem exists_fix_of_mem (ht : ∀ u, t (t (t u)) = u) {B A : AddSubgroup U}
    (hA : ∀ a ∈ A, t a ∈ A) (hB : ∀ b ∈ B, t b ∈ B) {a : U} (ha : a ∈ fixRel t B A) :
    ∃ c ∈ A, t c = c ∧ a - c ∈ B := by
  obtain ⟨haA, hab⟩ := ha
  refine ⟨a + t a + t (t a), A.add_mem (A.add_mem haA (hA a haA)) (hA _ (hA a haA)), ?_, ?_⟩
  · rw [map_add, map_add, ht]
    abel
  · have h1 : a - (a + t a + t (t a)) = -t (t a - a) - (a + a) - ((t a - a) + (t a - a)) := by
      rw [map_sub]
      abel
    rw [h1, two_smul_eq, two_smul_eq, sub_zero, sub_zero]
    exact B.neg_mem (hB _ hab)

theorem card_fix_mul_card [Finite U] (ht : ∀ u, t (t (t u)) = u) {B A : AddSubgroup U}
    (hBA : B ≤ A) (hA : ∀ a ∈ A, t a ∈ A) (hB : ∀ b ∈ B, t b ∈ B) :
    Nat.card (fixRel t ⊥ A) * Nat.card B = Nat.card (fixRel t B A) * Nat.card (fixRel t ⊥ B) := by
  classical
  let φ : (fixRel t ⊥ A × B) →+ U :=
    { toFun := fun p => (p.1 : U) + (p.2 : U)
      map_zero' := by simp
      map_add' := fun p q => by
        simp only [Prod.fst_add, Prod.snd_add, AddSubgroup.coe_add]
        abel }
  have hrange : φ.range = fixRel t B A := by
    ext u
    constructor
    · rintro ⟨⟨⟨c, hcA, hc⟩, ⟨b, hb⟩⟩, rfl⟩
      refine ⟨A.add_mem hcA (hBA hb), ?_⟩
      have hc' : t c = c := sub_eq_zero.mp ((AddSubgroup.mem_bot).mp hc)
      show t (c + b) - (c + b) ∈ B
      rw [map_add, hc', add_sub_add_left_eq_sub]
      exact B.sub_mem (hB b hb) hb
    · intro hu
      obtain ⟨c, hcA, hc, hb⟩ := exists_fix_of_mem t ht hA hB hu
      refine ⟨(⟨c, hcA, by rw [hc, sub_self]; exact (AddSubgroup.mem_bot).mpr rfl⟩,
        ⟨u - c, hb⟩), ?_⟩
      show c + (u - c) = u
      abel
  have hker : Nat.card φ.ker = Nat.card (fixRel t ⊥ B) := by
    refine Nat.card_congr
      { toFun := fun p => ⟨(p.1.2 : U), (p.1.2).2, ?_⟩
        invFun := fun c => ⟨(⟨-(c : U), A.neg_mem (hBA c.2.1), ?_⟩, ⟨c, c.2.1⟩), ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · have h0 : (p.1.1 : U) + (p.1.2 : U) = 0 := p.2
      have h1 : (p.1.1 : U) = -(p.1.2 : U) := eq_neg_of_add_eq_zero_left h0
      have h2 := p.1.1.2.2
      rw [AddSubgroup.mem_bot] at h2 ⊢
      rw [h1, map_neg, neg_sub_neg, sub_eq_zero] at h2
      rw [← h2, sub_self]
    · have h2 := c.2.2
      rw [AddSubgroup.mem_bot] at h2 ⊢
      rw [sub_eq_zero] at h2
      rw [map_neg, h2, sub_self]
    · show -(c : U) + (c : U) = 0
      exact neg_add_cancel _
    · rintro ⟨⟨⟨c, hc⟩, ⟨b, hb⟩⟩, h⟩
      have h1 : c + b = 0 := h
      apply Subtype.ext
      apply Prod.ext
      · exact Subtype.ext (show -b = c from (eq_neg_of_add_eq_zero_left h1).symm)
      · rfl
    · intro c
      rfl
  have h := AddSubgroup.card_ker_mul_card_range φ
  rw [hrange, hker, Nat.card_prod] at h
  rw [mul_comm (Nat.card (fixRel t B A)), h]

theorem exists_card_eq_mul_pow [Finite U] (ht : ∀ u, t (t (t u)) = u)
    (Pf : AddSubgroup U → Prop) (hP : ∀ A, Pf A → ∀ a ∈ A, t a ∈ A) (hbot : Pf ⊥)
    (hchief : ∀ A B, Pf A → Pf B → B < A → (∀ C, Pf C → B ≤ C → C ≤ A → C = B ∨ C = A) →
      Nat.card A = Nat.card (fixRel t B A) ∨ Nat.card A = 16 * Nat.card (fixRel t B A))
    (A : AddSubgroup U) (hA : Pf A) : ∃ m, Nat.card A = Nat.card (fixRel t ⊥ A) * 16 ^ m := by
  induction h : Nat.card A using Nat.strong_induction_on generalizing A with
  | _ n ih =>
  subst h
  by_cases hA0 : A = ⊥
  · subst hA0
    refine ⟨0, ?_⟩
    have : fixRel t ⊥ (⊥ : AddSubgroup U) = ⊥ := le_antisymm (fun _ h => h.1) bot_le
    rw [this, pow_zero, mul_one]
  obtain ⟨B, -, hBmax⟩ := exists_maximal_ge_of_wellFoundedGT
    (fun B : AddSubgroup U => Pf B ∧ B < A) ⊥ ⟨hbot, bot_lt_iff_ne_bot.mpr hA0⟩
  obtain ⟨hPB, hBA⟩ := hBmax.prop
  have hchiefBA : ∀ C, Pf C → B ≤ C → C ≤ A → C = B ∨ C = A := by
    intro C hC hBC hCA
    by_cases hCA' : C = A
    · exact Or.inr hCA'
    · exact Or.inl (hBmax.eq_of_ge ⟨hC, lt_of_le_of_ne hCA hCA'⟩ hBC)
  obtain ⟨m, hm⟩ := ih _ (AddSubgroup.card_lt_of_lt hBA) B hPB rfl
  have hcount := card_fix_mul_card t ht hBA.le (hP A hA) (hP B hPB)
  have hpos : 0 < Nat.card (fixRel t ⊥ B) := Nat.card_pos
  rcases hchief A B hA hPB hBA hchiefBA with h1 | h1
  · refine ⟨m, Nat.eq_of_mul_eq_mul_right hpos ?_⟩
    rw [h1, ← hcount, hm]
    ring
  · refine ⟨m + 1, Nat.eq_of_mul_eq_mul_right hpos ?_⟩
    rw [h1, mul_assoc, ← hcount, hm]
    ring

end CFSG.Quasithin.H13.Ch4.B414
