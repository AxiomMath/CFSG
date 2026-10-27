module

public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityNFDefs
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofEvenDesc
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityPairUnitary

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
open CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec11
open CFSG.RankThree.PartTwo.Sec8 CFSG.RankThree.PartTwo.Sec8.LangTwistedProof
open CFSG.RankThree.PartTwo.Sec19.NF5Pair

namespace CFSG.RankThree.PartTwo.Sec19

section Model


variable {X : Type} [Field X] [Finite X] (σ : X ≃+* X)

theorem pairProp_autFix_y0 (n : ℕ) (hn : 1 ≤ n) (hX : Nat.card X = (2 ^ n) ^ 3)
    (hσ : ∀ c : X, σ c = c ^ (2 ^ n)) :
    PairProp (Sec4.autFix (MulAut.conj (d4TrialityY0Elt X σ) * tauAut σ)) := by
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := kF82D4SecondCentY0Even_holds n he hn X σ hX hσ
    exact PairProp.of_mulEquiv e (pair_projImage_glPi_true n he hn hF)
  · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := kF82D4SecondCentY0_holds n ho X σ hX hσ
    exact PairProp.of_mulEquiv e (pair_projImage_glPi_false n ho hF)

theorem nf5_classes (n : ℕ) (hX : Nat.card X = (2 ^ n) ^ 3) (hσ : ∀ c : X, σ c = c ^ (2 ^ n))
    {g : C0 σ} (hg3 : (MulAut.conj g * tauAut σ) ^ 3 = 1) :
    ∃ h : C0 σ,
      (MulAut.conj g * tauAut σ = MulAut.conj h⁻¹ * tauAut σ * (MulAut.conj h⁻¹)⁻¹) ∨
      (MulAut.conj g * tauAut σ = MulAut.conj h⁻¹ *
        (MulAut.conj (d4TrialityY0Elt X σ) * tauAut σ) * (MulAut.conj h⁻¹)⁻¹) := by
  obtain ⟨h, y, hy, heq⟩ := exists_conj_eq_of_geom d4TrialityGeomClasses_holds
    d4DiagramCentIrred_holds d4SecondCentIrred_holds hX hσ g hg3
  refine ⟨h, ?_⟩
  rcases hy with hy | hy
  · left
    have : y = 1 := Subtype.ext hy
    subst this
    have h1 : (MulAut.conj (1 : C0 σ) : MulAut (C0 σ)) = 1 := map_one _
    rw [h1, one_mul] at heq
    exact heq
  · right
    have : y = d4TrialityY0Elt X σ := Subtype.ext hy
    subst this
    exact heq


theorem outer_X_case_of_pair (hτ3 : tauAut σ ^ 3 = 1) (n : ℕ) (hn : 1 ≤ n)
    (hX : Nat.card X = (2 ^ n) ^ 3) (hσ : ∀ c : X, σ c = c ^ (2 ^ n)) {x g : C0 σ} {e : ℕ}
    (he : e = 1 ∨ e = 2) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hβ3 : (MulAut.conj g * tauAut σ ^ e) ^ 3 = 1)
    (hcomm : Commute (MulAut.conj x) (MulAut.conj g * tauAut σ ^ e))
    (hG : ¬ HasGLine σ x g e) :
    ∃ h : C0 σ, (MulAut.conj g * tauAut σ ^ e) h = h ∧
      (h * x * h⁻¹) * x = x * (h * x * h⁻¹) ∧ h * x * h⁻¹ ∉ Subgroup.zpowers x := by
  classical
  set β : MulAut (C0 σ) := MulAut.conj g * tauAut σ ^ e with hβ
  have hβx : β x = x := by
    have h1 : β * MulAut.conj x * β⁻¹ = MulAut.conj x := by
      rw [← hcomm.eq]; group
    rw [aut_conj_conj] at h1
    exact conj_injective_C0 σ n hn hX hσ h1
  obtain ⟨g', hγ⟩ : ∃ g' : C0 σ,
      MulAut.conj g' * tauAut σ = β ∨ MulAut.conj g' * tauAut σ = β⁻¹ := by
    rcases he with rfl | rfl
    · exact ⟨g, Or.inl (by simp [hβ])⟩
    · refine ⟨tauAut σ g⁻¹, Or.inr ?_⟩
      have h2 : (tauAut σ ^ 2)⁻¹ = tauAut σ :=
        inv_eq_of_mul_eq_one_right (by rw [← pow_succ]; exact hτ3)
      rw [hβ, mul_inv_rev, h2, ← aut_conj_conj (tauAut σ) g⁻¹, map_inv]
      group
  have hγ3 : (MulAut.conj g' * tauAut σ) ^ 3 = 1 := by
    rcases hγ with h | h <;> rw [h]
    · exact hβ3
    · rw [inv_pow, hβ3, inv_one]
  have hγx : (MulAut.conj g' * tauAut σ) x = x := by
    rcases hγ with h | h <;> rw [h]
    · exact hβx
    · rw [MulAut.inv_apply]
      exact (MulEquiv.symm_apply_eq β).2 hβx.symm
  obtain ⟨h, hh | hh⟩ := nf5_classes σ n hX hσ hγ3
  ·
    exfalso
    apply hG
    refine ⟨MulAut.conj h, 0, ?_⟩
    have key : MulAut.conj h * (MulAut.conj g' * tauAut σ) * (MulAut.conj h)⁻¹ = tauAut σ := by
      rw [hh]; simp only [map_inv, inv_inv]; group
    rcases hγ with h' | h'
    · left
      rw [h'] at key
      rw [pow_zero, mul_one]
      exact key
    · right
      have key' : MulAut.conj h * β * (MulAut.conj h)⁻¹ = (tauAut σ)⁻¹ := by
        rw [← key, h']; group
      rw [pow_zero, mul_one]
      exact key'
  ·
    set α : MulAut (C0 σ) := MulAut.conj (d4TrialityY0Elt X σ) * tauAut σ with hα
    have hγeq : ∀ k : C0 σ, (MulAut.conj g' * tauAut σ) k = k ↔
        α (h * k * h⁻¹) = h * k * h⁻¹ := by
      intro k
      rw [hh]
      have e1 : (MulAut.conj h⁻¹ * α * (MulAut.conj h⁻¹)⁻¹) k = h⁻¹ * α (h * k * h⁻¹) * h := by
        simp [MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply]
      rw [e1]
      constructor
      · intro h1
        have h2 : α (h * k * h⁻¹) = h * (h⁻¹ * α (h * k * h⁻¹) * h) * h⁻¹ := by group
        rw [h2, h1]
      · intro h1
        rw [h1]; group
    have hx'M : h * x * h⁻¹ ∈ Sec4.autFix α := (hγeq x).1 hγx
    have hx'3 : (h * x * h⁻¹) ^ 3 = 1 := by rw [conj_pow, hx3]; group
    have hx'1 : h * x * h⁻¹ ≠ 1 := fun h1 => hx1 (by
      have : x = h⁻¹ * (h * x * h⁻¹) * h := by group
      rw [this, h1]; group)
    obtain ⟨m, hmM, hcm, hnm⟩ :=
      (pairProp_autFix_y0 σ n hn hX hσ).subgroup hx'M hx'3 hx'1
    have hmα : α m = m := hmM
    have hfix : (MulAut.conj g' * tauAut σ) (h⁻¹ * m * h) = h⁻¹ * m * h := by
      rw [hγeq]
      have e2 : h * (h⁻¹ * m * h) * h⁻¹ = m := by group
      rw [e2]; exact hmα
    refine ⟨h⁻¹ * m * h, ?_, ?_, ?_⟩
    · rcases hγ with h' | h'
      · rw [h'] at hfix; exact hfix
      · rw [h'] at hfix
        rw [MulAut.inv_apply] at hfix
        have := congrArg β hfix
        rw [MulEquiv.apply_symm_apply] at this
        exact this.symm
    · have := congrArg (fun t => h⁻¹ * t * h) hcm
      group at this ⊢
      exact this
    · intro hmem
      apply hnm
      have := (mem_zpowers_conj_iff h (h⁻¹ * m * h * x * (h⁻¹ * m * h)⁻¹) x).2 hmem
      have e3 : h * (h⁻¹ * m * h * x * (h⁻¹ * m * h)⁻¹) * h⁻¹ = m * (h * x * h⁻¹) * m⁻¹ := by
        group
      rwa [e3] at this


theorem outer_X_case (hAB : TrialityABFacts σ) (n : ℕ) (hn : 2 ≤ n)
    (hX : Nat.card X = (2 ^ n) ^ 3) (hσ : ∀ c : X, σ c = c ^ (2 ^ n)) {x g : C0 σ} {e : ℕ}
    (he : e = 1 ∨ e = 2) (hx : IsClassX σ x)
    (hβ3 : (MulAut.conj g * tauAut σ ^ e) ^ 3 = 1) (hβ1 : MulAut.conj g * tauAut σ ^ e ≠ 1)
    (hcomm : Commute (MulAut.conj x) (MulAut.conj g * tauAut σ ^ e))
    (hG : ¬ HasGLine σ x g e) :
    ∃ h : C0 σ, (MulAut.conj g * tauAut σ ^ e) h = h ∧
      (h * x * h⁻¹) * x = x * (h * x * h⁻¹) ∧ h * x * h⁻¹ ∉ Subgroup.zpowers x :=
  outer_X_case_of_pair σ hAB.tau3 n (by omega) hX hσ he hx.1 hx.2.1 hβ3 hcomm hG

end Model

end CFSG.RankThree.PartTwo.Sec19
