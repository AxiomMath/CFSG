module

public import CFSG.Timmesfeld.RankTwo.LevisExtras
public import CFSG.LieType.Steinberg.Minuscule.ChevExtras

public section

namespace CFSG.Timmesfeld

open CFSG.LieType CFSG.LieType.Universal CFSG.Blueprint.Chevalley

@[expose] def edgeE (r : ℕ) (i j : Fin r) : Prop :=
  (i.val = 0 ∧ j.val = 2) ∨ (i.val = 1 ∧ j.val = 3) ∨ (2 ≤ i.val ∧ j.val = i.val + 1)

instance (r : ℕ) : DecidableRel (edgeE r) := fun i j =>
  inferInstanceAs (Decidable ((i.val = 0 ∧ j.val = 2) ∨ (i.val = 1 ∧ j.val = 3) ∨
    (2 ≤ i.val ∧ j.val = i.val + 1)))

namespace LevisExceptional

def cartanAt (τ : Tag) (i j : Fin τ.rank) : ℤ := τ.cartan i j

def IsOrientation (τ : Tag) : Prop :=
  (∀ i j : Fin τ.rank, edgeE τ.rank i j → ¬ edgeE τ.rank j i) ∧
  (∀ i j : Fin τ.rank, edgeE τ.rank i j → cartanAt τ i j = -1 ∧ cartanAt τ j i = -1) ∧
  (∀ i j : Fin τ.rank, i ≠ j → ¬ edgeE τ.rank i j → ¬ edgeE τ.rank j i →
    cartanAt τ i j = 0 ∧ cartanAt τ j i = 0) ∧
  (∀ i j : Fin τ.rank, edgeE τ.rank i j → ∃ k, k ≠ i ∧ k ≠ j ∧
    ((edgeE τ.rank j k ∨ edgeE τ.rank k j) ∧ ¬ edgeE τ.rank i k ∧ ¬ edgeE τ.rank k i ∨
      (edgeE τ.rank i k ∨ edgeE τ.rank k i) ∧ ¬ edgeE τ.rank j k ∧ ¬ edgeE τ.rank k j))

theorem isOrientation_E6 : IsOrientation .E6 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem isOrientation_E7 : IsOrientation .E7 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem isOrientation_E8 : IsOrientation .E8 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

end LevisExceptional

open LevisExceptional Steinberg

theorem simplyLacedLevis_e6 (F : Type) [Field F] [Finite F] [CharP F 2] :
    SimplyLacedLevis (Minuscule.e6Datum F) F (edgeE (Tag.rank .E6))
      (Minuscule.e6Data_valid.xm F) := by
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (Minuscule.e6Datum F).isFiniteType
    (Dv := (Minuscule.e6Datum F).divisible) rfl
  obtain ⟨h1, h2, h3, h4⟩ := isOrientation_E6
  exact simplyLacedLevis_of_chevalleyExtras (Minuscule.e6_chevalleyExtras F O _
      (Minuscule.e6Data_valid.commutatorFormula_commC F Minuscule.posDef_cartan_E6 _
        (Minuscule.roots_eq Minuscule.isFiniteType_cartan_E6) O)) rfl
    (fun α _ β _ _ _ => Minuscule.e6Data_valid.commC_natAbs F α β (1, 1)) h1 h2 h3 h4

theorem simplyLacedLevis_e7 (F : Type) [Field F] [Finite F] [CharP F 2] :
    SimplyLacedLevis (Minuscule.e7Datum F) F (edgeE (Tag.rank .E7))
      (Minuscule.e7Data_valid.xm F) := by
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (Minuscule.e7Datum F).isFiniteType
    (Dv := (Minuscule.e7Datum F).divisible) rfl
  obtain ⟨h1, h2, h3, h4⟩ := isOrientation_E7
  exact simplyLacedLevis_of_chevalleyExtras (Minuscule.e7_chevalleyExtras F O _
      (Minuscule.e7Data_valid.commutatorFormula_commC F Minuscule.posDef_cartan_E7 _
        (Minuscule.roots_eq Minuscule.isFiniteType_cartan_E7) O)) rfl
    (fun α _ β _ _ _ => Minuscule.e7Data_valid.commC_natAbs F α β (1, 1)) h1 h2 h3 h4

theorem simplyLacedLevis_e8 (F : Type) [Field F] [Finite F] [CharP F 2] :
    SimplyLacedLevis (Adjoint.e8Datum F) F (edgeE (Tag.rank .E8)) (Adjoint.e8Par F) := by
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (Adjoint.e8Datum F).isFiniteType
    (Dv := (Adjoint.e8Datum F).divisible) rfl
  obtain ⟨h1, h2, h3, h4⟩ := isOrientation_E8
  refine simplyLacedLevis_of_chevalleyExtras (Adjoint.e8_chevalleyExtras F O _
      (Adjoint.commutatorFormula_commC Adjoint.e8Data_valid Adjoint.noG2_E8 _
        (Adjoint.adjDatum_roots _ F) O)) rfl ?_ h1 h2 h3 h4
  intro α hα β hβ hr hd
  rw [Adjoint.mem_adjDatum_roots] at hα hβ hr hd
  have hne : α + β ≠ 0 := hr.ne_zero
  rw [Adjoint.commC_11 hα hβ hne, Adjoint.RootOperatorFamily'.coeff11,
    Adjoint.RootOperatorFamily'.bracketCoeff_natAbs _ _ (fun h => hne (by
      change β = -α at h
      rw [h, add_neg_cancel])) hr]
  exact Adjoint.stringNorm_of_not_isRoot hd

end CFSG.Timmesfeld
