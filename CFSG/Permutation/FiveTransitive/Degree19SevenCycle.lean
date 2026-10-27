module

public import CFSG.Permutation.FiveTransitive.Helpers
public import CFSG.Permutation.FiveTransitive.Degree19SevenFiniteChecks
import CFSG.Permutation.FiveTransitive.Degree24SevenCycle

public section

namespace CFSG

namespace FiveTransitive.Degree19Seven

open MulAction SubMulAction Subgroup

theorem exists_controlled_conjugator
    (P : Subgroup (Equiv.Perm (Fin 19)))
    (h5 : ∀ a b : Fin 5 → Fin 19,
      Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i) :
    ∃ p : P,
      (p : Equiv.Perm (Fin 19)) 0 = 0 ∧
      (p : Equiv.Perm (Fin 19)) 1 = 1 ∧
      (p : Equiv.Perm (Fin 19)) 2 = 2 ∧
      (p : Equiv.Perm (Fin 19)) 3 = 3 ∧
      (p : Equiv.Perm (Fin 19)) 7 = 4 := by
  obtain ⟨p, hp⟩ := h5
    Degree19SevenFiniteChecks.sourceTuple
    Degree19SevenFiniteChecks.targetTuple
    Degree19SevenFiniteChecks.sourceTuple_injective
    Degree19SevenFiniteChecks.targetTuple_injective
  refine ⟨p, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Degree19SevenFiniteChecks.sourceTuple,
      Degree19SevenFiniteChecks.targetTuple, Subgroup.smul_def,
      Equiv.Perm.smul_def] using hp (0 : Fin 5)
  · simpa [Degree19SevenFiniteChecks.sourceTuple,
      Degree19SevenFiniteChecks.targetTuple, Subgroup.smul_def,
      Equiv.Perm.smul_def] using hp (1 : Fin 5)
  · simpa [Degree19SevenFiniteChecks.sourceTuple,
      Degree19SevenFiniteChecks.targetTuple, Subgroup.smul_def,
      Equiv.Perm.smul_def] using hp (2 : Fin 5)
  · simpa [Degree19SevenFiniteChecks.sourceTuple,
      Degree19SevenFiniteChecks.targetTuple, Subgroup.smul_def,
      Equiv.Perm.smul_def] using hp (3 : Fin 5)
  · simpa [Degree19SevenFiniteChecks.sourceTuple,
      Degree19SevenFiniteChecks.targetTuple, Subgroup.smul_def,
      Equiv.Perm.smul_def] using hp (4 : Fin 5)

theorem five_le_image_of_controlled_conjugator
    (p : Equiv.Perm (Fin 19))
    (hp0 : p 0 = 0) (hp1 : p 1 = 1) (hp2 : p 2 = 2)
    (hp3 : p 3 = 3) (hp7 : p 7 = 4)
    (i : Fin 19)
    (hi0 : i ≠ 0) (hi1 : i ≠ 1) (hi2 : i ≠ 2)
    (hi3 : i ≠ 3) (hi7 : i ≠ 7) :
    5 ≤ (p i).val := by
  apply Degree19SevenFiniteChecks.five_le_of_ne_zero_one_two_three_four
  · simpa [hp0] using p.injective.ne hi0
  · simpa [hp1] using p.injective.ne hi1
  · simpa [hp2] using p.injective.ne hi2
  · simpa [hp3] using p.injective.ne hi3
  · simpa [hp7] using p.injective.ne hi7

private theorem alternatingGroup_le_of_sevenCycle_mem
    (P : Subgroup (Equiv.Perm (Fin 19)))
    (h5 : ∀ a b : Fin 5 → Fin 19,
      Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hg : Degree19SevenFiniteChecks.sevenCycle ∈ P) :
    alternatingGroup (Fin 19) ≤ P := by
  classical
  obtain ⟨p, hp0, hp1, hp2, hp3, hp7⟩ :=
    exists_controlled_conjugator P h5
  let x : Fin 19 := (p : Equiv.Perm (Fin 19)) 4
  let y : Fin 19 := (p : Equiv.Perm (Fin 19)) 5
  let z : Fin 19 := (p : Equiv.Perm (Fin 19)) 6
  have hx : 5 ≤ x.val := by
    apply five_le_image_of_controlled_conjugator
      (p : Equiv.Perm (Fin 19)) hp0 hp1 hp2 hp3 hp7 <;> decide
  have hy : 5 ≤ y.val := by
    apply five_le_image_of_controlled_conjugator
      (p : Equiv.Perm (Fin 19)) hp0 hp1 hp2 hp3 hp7 <;> decide
  have hz : 5 ≤ z.val := by
    apply five_le_image_of_controlled_conjugator
      (p : Equiv.Perm (Fin 19)) hp0 hp1 hp2 hp3 hp7 <;> decide
  have hxy : x ≠ y :=
    (p : Equiv.Perm (Fin 19)).injective.ne (by decide)
  have hxz : x ≠ z :=
    (p : Equiv.Perm (Fin 19)).injective.ne (by decide)
  have hyz : y ≠ z :=
    (p : Equiv.Perm (Fin 19)).injective.ne (by decide)
  let h : Equiv.Perm (Fin 19) :=
    (p : Equiv.Perm (Fin 19)) * Degree19SevenFiniteChecks.sevenCycle *
      (p : Equiv.Perm (Fin 19))⁻¹
  have hh : h = Degree19SevenFiniteChecks.comparisonCycle x y z := by
    change
      (p : Equiv.Perm (Fin 19)) * Degree19SevenFiniteChecks.sevenCycle *
          (p : Equiv.Perm (Fin 19))⁻¹ =
        Degree19SevenFiniteChecks.comparisonCycle x y z
    rw [← Equiv.permCongr_eq_mul, Degree19SevenFiniteChecks.sevenCycle,
      Helpers.permCongr_formPerm]
    simp [Degree19SevenFiniteChecks.comparisonCycle, x, y, z,
      hp0, hp1, hp2, hp3]
  obtain ⟨w, hw, hwNe, hwsupport⟩ :=
    Degree19SevenFiniteChecks.exists_small_mem_closure
      x y z hx hy hz hxy hxz hyz
  have hclosure :
      Subgroup.closure
          ({Degree19SevenFiniteChecks.sevenCycle,
            Degree19SevenFiniteChecks.comparisonCycle x y z} :
            Set (Equiv.Perm (Fin 19))) ≤ P := by
    rw [Subgroup.closure_le]
    intro u hu
    rcases hu with (rfl | rfl)
    · exact hg
    · rw [← hh]
      exact P.mul_mem (P.mul_mem p.prop hg) (P.inv_mem p.prop)
  exact Helpers.alternatingGroup_le_of_nontrivial_card_support_le_five
    (Fin 19) P h5 (by norm_num) (hclosure hw) hwNe hwsupport

theorem alternatingGroup_le_of_cycleType_eq
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 19)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    {g : Equiv.Perm X} (hg : g ∈ P)
    (c : Equiv.Perm (Fin 19))
    (hcycleType :
      ((Fintype.equivFinOfCardEq hcard).permCongr g).cycleType =
        c.cycleType)
    (hforce :
      ∀ Q : Subgroup (Equiv.Perm (Fin 19)),
        (∀ a b : Fin 5 → Fin 19,
          Function.Injective a → Function.Injective b →
          ∃ q : Q, ∀ i, q • a i = b i) →
        c ∈ Q → alternatingGroup (Fin 19) ≤ Q) :
    alternatingGroup X ≤ P := by
  classical
  let e₀ : X ≃ Fin 19 := Fintype.equivFinOfCardEq hcard
  let g₁ : Equiv.Perm (Fin 19) := e₀.permCongr g
  obtain ⟨k, hk⟩ :=
    isConj_iff.mp (Equiv.Perm.isConj_of_cycleType_eq hcycleType)
  let e : X ≃ Fin 19 := e₀.trans k
  let P' : Subgroup (Equiv.Perm (Fin 19)) :=
    P.map e.permCongrHom
  have hemapg : e.permCongr g = c := by
    change k * g₁ * k⁻¹ = c
    exact hk
  have hc : c ∈ P' := by
    rw [Subgroup.mem_map]
    exact ⟨g, hg, hemapg⟩
  have h5P' :
      ∀ a b : Fin 5 → Fin 19,
        Function.Injective a → Function.Injective b →
        ∃ q : P', ∀ i, q • a i = b i := by
    intro a b ha hb
    have ha' : Function.Injective (fun i => e.symm (a i)) :=
      e.symm.injective.comp ha
    have hb' : Function.Injective (fun i => e.symm (b i)) :=
      e.symm.injective.comp hb
    obtain ⟨q, hq⟩ := h5
      (fun i => e.symm (a i)) (fun i => e.symm (b i)) ha' hb'
    let q' : Equiv.Perm (Fin 19) :=
      e.permCongr (q : Equiv.Perm X)
    have hq'P : q' ∈ P' :=
      Subgroup.mem_map_of_mem e.permCongrHom.toMonoidHom q.prop
    refine ⟨⟨q', hq'P⟩, ?_⟩
    intro i
    have hqi :
        (q : Equiv.Perm X) (e.symm (a i)) =
          e.symm (b i) := by
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hq i
    simpa [Subgroup.smul_def, Equiv.Perm.smul_def, q',
      Equiv.permCongr_apply] using congrArg e hqi
  have hAlt' : alternatingGroup (Fin 19) ≤ P' :=
    hforce P' h5P' hc
  intro σ hσ
  let σ' : Equiv.Perm (Fin 19) := e.permCongr σ
  have hσ' : σ' ∈ alternatingGroup (Fin 19) := by
    rw [Equiv.Perm.mem_alternatingGroup] at hσ ⊢
    simpa [σ', Equiv.Perm.sign_permCongr] using hσ
  have hmapped : σ' ∈ P' := hAlt' hσ'
  rw [Subgroup.mem_map] at hmapped
  obtain ⟨τ, hτ, hτσ⟩ := hmapped
  have hτeq : τ = σ := e.permCongrHom.injective (by
    simpa [σ'] using hτσ)
  rwa [← hτeq]

theorem alternatingGroup_le_of_sevenCycle
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 19)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    {g : Equiv.Perm X} (hg : g ∈ P)
    (hcycle : g.IsCycle) (hsupport : g.support.card = 7) :
    alternatingGroup X ≤ P := by
  classical
  let e₀ : X ≃ Fin 19 := Fintype.equivFinOfCardEq hcard
  let g₁ : Equiv.Perm (Fin 19) := e₀.permCongr g
  have hg₁cycle : g₁.IsCycle :=
    FiveTransitive.Degree24Seven.isCycle_permCongr e₀ hcycle
  have hsupportMap :
      g₁.support = g.support.map e₀.toEmbedding := by
    ext y
    simp [g₁, Equiv.Perm.mem_support, Equiv.permCongr_apply]
    constructor
    · intro h h'
      apply h
      rw [h', e₀.apply_symm_apply]
    · intro h h'
      apply h
      apply e₀.injective
      simpa using h'
  have hg₁support : g₁.support.card = 7 := by
    rw [hsupportMap, Finset.card_map, hsupport]
  apply alternatingGroup_le_of_cycleType_eq X P hcard h5 hg
    Degree19SevenFiniteChecks.sevenCycle
  · calc
      g₁.cycleType = {g₁.support.card} := hg₁cycle.cycleType
      _ = {7} := by rw [hg₁support]
      _ = Degree19SevenFiniteChecks.sevenCycle.cycleType := by
        rw [Degree19SevenFiniteChecks.sevenCycle_isCycle.cycleType,
          Degree19SevenFiniteChecks.sevenCycle_card_support]
  · intro Q h5Q hcanonical
    exact alternatingGroup_le_of_sevenCycle_mem Q h5Q hcanonical

end FiveTransitive.Degree19Seven

end CFSG
