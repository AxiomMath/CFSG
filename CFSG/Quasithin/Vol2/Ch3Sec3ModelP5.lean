module

public import CFSG.Quasithin.Vol2.Ch3Sec3CloseModelG
public import CFSG.Quasithin.Vol2.Ch3Sec3P5Act

public section

namespace CFSG.Quasithin.H13.ModelP5

open P5 CloseModelG ModelA2 S6Syl

theorem fix_check : (Finset.univ.filter fun v : Vec5 => act x₁ v = v).card = 8 ∧
    (Finset.univ.filter fun v : Vec5 => act x₂ v = v).card = 16 ∧
    (Finset.univ.filter fun v : Vec5 => act x₃ v = v).card = 8 ∧
    (Finset.univ.filter fun v : Vec5 => act x₁ v = v ∧ act x₂ v = v).card = 4 := by
  decide +kernel

theorem card_vec5 : Nat.card Vec5 = 32 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem fixS_bot : fixS actHom ⊥ = Set.univ := by
  ext v
  simp only [fixS, Subgroup.mem_bot, forall_eq, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact act_one v

theorem fixS_zpowers (x : Equiv.Perm (Fin 6)) :
    fixS actHom (Subgroup.zpowers x) = {v | act x v = v} := by
  ext v
  simp only [fixS, Set.mem_ofPred_eq]
  constructor
  · intro h
    exact h x (Subgroup.mem_zpowers x)
  · intro h y hy
    let H : Subgroup (Equiv.Perm (Fin 6)) :=
      { carrier := {y | act y v = v}
        one_mem' := act_one v
        mul_mem' := fun {a b} ha hb => by
          show act (a * b) v = v
          rw [act_mul, hb, ha]
        inv_mem' := fun {a} ha => by
          show act a⁻¹ v = v
          have := congrArg (act a⁻¹) ha
          rw [← act_mul, inv_mul_cancel, act_one] at this
          exact this.symm }
    exact (Subgroup.zpowers_le.mpr h : Subgroup.zpowers x ≤ H) hy

theorem fixS_aBar2 : fixS actHom aBar2 = {v | act x₁ v = v ∧ act x₂ v = v} := by
  ext v
  simp only [fixS, Set.mem_ofPred_eq]
  have hx₁ : x₁ ∈ aBar2 := (aBar2_eq x₁).mpr ((mem_elemsA x₁).mpr (Or.inr (Or.inl rfl)))
  have hx₂ : x₂ ∈ aBar2 := (aBar2_eq x₂).mpr ((mem_elemsA x₂).mpr (Or.inr (Or.inr (Or.inl rfl))))
  constructor
  · intro hv
    exact ⟨hv x₁ hx₁, hv x₂ hx₂⟩
  · rintro ⟨h1, h2⟩ y hy
    have h3 : act x₃ v = v := by rw [x₃, act_mul, h2, h1]
    rcases (mem_elemsA y).mp ((aBar2_eq y).mp hy) with rfl | rfl | rfl | rfl
    · exact act_one v
    · exact h1
    · exact h2
    · exact h3

theorem card_set_eq (p : Vec5 → Prop) [DecidablePred p] :
    Nat.card {v : Vec5 | p v} = (Finset.univ.filter p).card := by
  rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
  rfl

theorem wt_values : wt actHom ⊥ = 32 ∧ wt actHom (Subgroup.zpowers x₁) = 16 ∧
    wt actHom (Subgroup.zpowers x₂) = 32 ∧ wt actHom (Subgroup.zpowers x₃) = 16 ∧
    wt actHom aBar2 = 16 := by
  obtain ⟨h1₂, h2₂, h3₂, n1, n2, n3, -⟩ := x_facts
  obtain ⟨c1, c2, c3, c12⟩ := fix_check
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [wt, fixS_bot, Subgroup.card_bot, Nat.card_univ, one_mul, card_vec5]
  · rw [wt, card_zpowers_of h1₂ n1, fixS_zpowers, card_set_eq, c1]
  · rw [wt, card_zpowers_of h2₂ n2, fixS_zpowers, card_set_eq, c2]
  · rw [wt, card_zpowers_of h3₂ n3, fixS_zpowers, card_set_eq, c3]
  · rw [wt, card_aBar2, fixS_aBar2, card_set_eq, c12]

theorem wt_le (X : Subgroup (Equiv.Perm (Fin 6))) (hX : X ≤ aBar2) :
    wt actHom X ≤ Nat.card Vec5 := by
  obtain ⟨w0, w1, w2, w3, wA⟩ := wt_values
  rw [card_vec5]
  rcases subgroup_cases hX with rfl | rfl | rfl | rfl | rfl <;> omega

theorem wt_eq (X : Subgroup (Equiv.Perm (Fin 6))) (hX : X ≤ aBar2) (hne : X ≠ ⊥)
    (heq : wt actHom X = Nat.card Vec5) : X = Subgroup.zpowers x₂ := by
  obtain ⟨w0, w1, w2, w3, wA⟩ := wt_values
  rw [card_vec5] at heq
  rcases subgroup_cases hX with h | h | h | h | h
  · exact absurd h hne
  · rw [h] at heq; omega
  · exact h
  · rw [h] at heq; omega
  · rw [h] at heq; omega

theorem wt_W2 (X : Subgroup (Equiv.Perm (Fin 6))) (hX : X ≤ aBar2) (hne : X ≠ ⊥)
    (heq : wt actHom X = Nat.card Vec5) : ∃ x ∈ X, fixS actHom X = {m | actHom x m = m} := by
  rw [wt_eq X hX hne heq]
  exact ⟨x₂, Subgroup.mem_zpowers x₂, by rw [fixS_zpowers]; rfl⟩

theorem wt_W3 (X X' : Subgroup (Equiv.Perm (Fin 6))) (hX : X ≤ aBar2) (hX' : X' ≤ aBar2)
    (hne : X ≠ ⊥) (hne' : X' ≠ ⊥) (heq : wt actHom X = Nat.card Vec5)
    (heq' : wt actHom X' = Nat.card Vec5) : X = X' := by
  rw [wt_eq X hX hne heq, wt_eq X' hX' hne' heq']

end CFSG.Quasithin.H13.ModelP5
