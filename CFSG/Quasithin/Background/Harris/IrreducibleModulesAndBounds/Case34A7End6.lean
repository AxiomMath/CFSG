module

public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Case34A7End
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Case34A7Data

public section

namespace CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

open CFSG.Quasithin CFSG.Quasithin.G11 Equiv

namespace Case34A7

@[expose] def gen1 : Perm (Fin 7) := swap 2 3 * swap 3 4
@[expose] def gen2 : Perm (Fin 7) := swap 3 4 * swap 4 5
@[expose] def gen3 : Perm (Fin 7) := swap 4 5 * swap 5 6
@[expose] def gen4 : Perm (Fin 7) := swap 0 1 * swap 2 3
@[expose] def pair01 : Fin 7 → ZMod 2 := fun i => if i.val < 2 then 1 else 0

theorem sign_gens : Perm.sign gen1 = 1 ∧ Perm.sign gen2 = 1 ∧ Perm.sign gen3 = 1 ∧
    Perm.sign gen4 = 1 := by
  decide +kernel

theorem pair01_mem : pair01 ∈ permCore 7 := by
  show ∑ i, pair01 i = 0
  decide

theorem permAct_pair01 : permAct gen1 pair01 = pair01 ∧ permAct gen2 pair01 = pair01 ∧
    permAct gen3 pair01 = pair01 ∧ permAct gen4 pair01 = pair01 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> funext i <;> revert i <;> decide

theorem permAct_mem_permCore {n : ℕ} (σ : Perm (Fin n)) {x : Fin n → ZMod 2}
    (hx : x ∈ permCore n) : permAct σ x ∈ permCore n := by
  show ∑ i, permAct σ x i = 0
  have h : ∑ i, x i = 0 := hx
  simp only [permAct]
  rw [← h]
  exact Equiv.sum_comp σ⁻¹ x

theorem fixed_pair (x : Fin 7 → ZMod 2) (hx : ∑ i, x i = 0)
    (h1 : permAct gen1 x = x) (h2 : permAct gen2 x = x) (h3 : permAct gen3 x = x)
    (h4 : permAct gen4 x = x) : x = 0 ∨ x = pair01 := by
  have e1 := congrFun h1 3
  have e2 := congrFun h1 4
  have e4 := congrFun h2 5
  have e6 := congrFun h3 6
  have e7 := congrFun h4 1
  simp only [permAct] at e1 e2 e4 e6 e7
  rw [show (gen1⁻¹) 3 = 2 by decide] at e1
  rw [show (gen1⁻¹) 4 = 3 by decide] at e2
  rw [show (gen2⁻¹) 5 = 4 by decide] at e4
  rw [show (gen3⁻¹) 6 = 5 by decide] at e6
  rw [show (gen4⁻¹) 1 = 0 by decide] at e7
  rw [Fin.sum_univ_seven] at hx
  have c2 : x 2 = x 6 := by rw [e1, e2, e4, e6]
  have c3 : x 3 = x 6 := by rw [e2, e4, e6]
  have c4 : x 4 = x 6 := by rw [e4, e6]
  have c5 : x 5 = x 6 := e6
  rw [← e7, c2, c3, c4, c5] at hx
  have key : ∀ a c : ZMod 2, a + a + c + c + c + c + c = 0 → c = 0 := by decide
  have h6 : x 6 = 0 := key _ _ hx
  have hall : ∀ i : Fin 7, x i = if i.val < 2 then x 0 else 0 := by
    intro i
    fin_cases i
    · simp
    · simp [← e7]
    · simp [c2, h6]
    · simp [c3, h6]
    · simp [c4, h6]
    · simp [c5, h6]
    · simp [h6]
  have z01 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases z01 (x 0) with h | h
  · left
    funext i
    rw [hall i, h]
    simp
  · right
    funext i
    rw [hall i, h]
    simp [pair01]

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem endIsField_one_of_permCore [Finite V] {L : Subgroup (GLV V)} (hL : IsIrr L ⊤)
    {f : ↥L ≃* ↥(alternatingGroup (Fin 7))} {β : ↥(permCore 7) →ₗ[ZMod 2] V}
    (hβ : PermCoreData f β) : EndIsField L 1 := by
  obtain ⟨hbij, hequi⟩ := hβ
  obtain ⟨s1, s2, s3, s4⟩ := sign_gens
  let lift : (σ : Perm (Fin 7)) → Perm.sign σ = 1 → ↥L := fun σ hσ =>
    f.symm ⟨σ, Perm.mem_alternatingGroup.2 hσ⟩
  have hlift : ∀ (σ : Perm (Fin 7)) (hσ : Perm.sign σ = 1) (x : ↥(permCore 7)),
      β ⟨permAct σ (x : Fin 7 → ZMod 2), permAct_mem_permCore σ x.2⟩ =
        ((lift σ hσ : ↥L) : GLV V) (β x) := by
    intro σ hσ x
    refine hequi (lift σ hσ) x _ ?_
    simp [lift]
  let H₀ : Set (GLV V) := {g | g = ((lift gen1 s1 : ↥L) : GLV V) ∨
    g = ((lift gen2 s2 : ↥L) : GLV V) ∨ g = ((lift gen3 s3 : ↥L) : GLV V) ∨
    g = ((lift gen4 s4 : ↥L) : GLV V)}
  let p : ↥(permCore 7) := ⟨pair01, pair01_mem⟩
  have hp0 : p ≠ 0 := by
    intro h
    have := congrFun (congrArg Subtype.val h) 0
    revert this
    decide
  have hβ0 : β 0 = 0 := map_zero β
  have hu : β p ≠ 0 := fun h => hp0 (hbij.1 (h.trans hβ0.symm))
  have hfix : ∀ σ (hσ : Perm.sign σ = 1), permAct σ pair01 = pair01 →
      ((lift σ hσ : ↥L) : GLV V) (β p) = β p := by
    intro σ hσ h
    rw [← hlift σ hσ p]
    congr 1
    exact Subtype.ext h
  obtain ⟨pa1, pa2, pa3, pa4⟩ := permAct_pair01
  refine endIsField_one_of_fixed hL (H₀ := H₀) ?_ hu ?_ ?_
  · intro g hg
    rcases hg with rfl | rfl | rfl | rfl <;> exact Subtype.coe_prop _
  · intro g hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact hfix gen1 s1 pa1
    · exact hfix gen2 s2 pa2
    · exact hfix gen3 s3 pa3
    · exact hfix gen4 s4 pa4
  · intro w hw
    obtain ⟨x, rfl⟩ := hbij.2 w
    have hf : ∀ σ (hσ : Perm.sign σ = 1),
        ((lift σ hσ : ↥L) : GLV V) (β x) = β x → permAct σ (x : Fin 7 → ZMod 2) = x := by
      intro σ hσ h
      have := hlift σ hσ x
      rw [h] at this
      exact congrArg Subtype.val (hbij.1 this)
    have hx := fixed_pair x x.2 (hf gen1 s1 (hw _ (Or.inl rfl)))
      (hf gen2 s2 (hw _ (Or.inr (Or.inl rfl)))) (hf gen3 s3 (hw _ (Or.inr (Or.inr (Or.inl rfl)))))
      (hf gen4 s4 (hw _ (Or.inr (Or.inr (Or.inr rfl)))))
    rcases hx with h | h
    · left
      have : x = 0 := Subtype.ext h
      rw [this, hβ0]
    · right
      have : x = p := Subtype.ext h
      rw [this]

end Case34A7

end CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
