module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18ModU4Outer
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open CFSG.HardMathSupport.U4FF (NaturalSU4 NaturalOmega6 disp)
open scoped commutatorElement Pointwise Matrix

abbrev Om6Idx : Type := Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2

@[expose] def adjOmega6 (F : Type) [Field F] (b : F) : AddSubgroup (Matrix Om6Idx Om6Idx F) where
  carrier := {X | Xᵀ = X ∧ (∀ i, X i i = 0) ∧
    ∑ i : Fin (3 - 1), X (.inl i) (.inr (.inl i)) + b * X (.inr (.inr 0)) (.inr (.inr 1)) = 0}
  add_mem' := by
    rintro X Y ⟨hX1, hX2, hX3⟩ ⟨hY1, hY2, hY3⟩
    refine ⟨by rw [Matrix.transpose_add, hX1, hY1], fun i => by simp [hX2 i, hY2 i], ?_⟩
    simp only [Matrix.add_apply, Finset.sum_add_distrib]
    linear_combination hX3 + hY3
  zero_mem' := ⟨Matrix.transpose_zero, fun _ => rfl, by simp⟩
  neg_mem' := by
    rintro X ⟨hX1, hX2, hX3⟩
    refine ⟨by rw [Matrix.transpose_neg, hX1], fun i => by simp [hX2 i], ?_⟩
    simp only [Matrix.neg_apply, Finset.sum_neg_distrib]
    linear_combination -hX3

@[expose] def wedgeM {ι F : Type} [Field F] (v w : ι → F) : Matrix ι ι F :=
  Matrix.vecMulVec v w + Matrix.vecMulVec w v

@[expose] def adjPolar {F : Type} [Field F] (b : F) (v w : Om6Idx → F) : F :=
  ∑ i : Fin (3 - 1), (v (.inl i) * w (.inr (.inl i)) + w (.inl i) * v (.inr (.inl i))) +
    b * (v (.inr (.inr 0)) * w (.inr (.inr 1)) + w (.inr (.inr 0)) * v (.inr (.inr 1)))

@[expose] noncomputable def adjBinv {F : Type} [Field F] (b : F) : Matrix Om6Idx Om6Idx F :=
  ∑ i : Fin (3 - 1),
      wedgeM (Pi.single (Sum.inl i : Om6Idx) (1 : F)) (Pi.single (Sum.inr (Sum.inl i)) 1) +
    b⁻¹ • wedgeM (Pi.single (Sum.inr (Sum.inr 0) : Om6Idx) (1 : F))
      (Pi.single (Sum.inr (Sum.inr 1)) 1)

@[expose] def AdjointOmega6 (n : ℕ) {U : Type} [CommGroup U] (S : Subgroup (MulAut U)) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F) (b c : F), Nat.card F = 2 ^ n ∧
    (∀ s : F, s ^ 2 + b * s + c ≠ 0) ∧
    ∃ (ε : ↥S ≃* ↥(StatedOmega (StatedQuadMinus 3 F b c)))
      (ψ : U ≃* Multiplicative ↥(adjOmega6 F b)),
      ∀ (l : ↥S) (u : U),
        ((Multiplicative.toAdd (ψ ((l : MulAut U) u)) : ↥(adjOmega6 F b)) :
            Matrix Om6Idx Om6Idx F) =
          ((ε l : GL Om6Idx F) : Matrix Om6Idx Om6Idx F) *
            ((Multiplicative.toAdd (ψ u) : ↥(adjOmega6 F b)) : Matrix Om6Idx Om6Idx F) *
            ((ε l : GL Om6Idx F) : Matrix Om6Idx Om6Idx F)ᵀ

@[expose] def K146U4OuterMcClurg : Prop :=
  ∀ (U : Type) [CommGroup U] [Finite U], (∀ u : U, u ^ 2 = 1) →
    ∀ (S : Subgroup (MulAut U)) (n : ℕ) (σ : MulAut U), IsU4 ↥S n → 1 < n → IsIrrOn S ⊤ ⊥ →
      (∀ t ∈ S, t ≠ 1 → t * t = 1 → 4 * n + 2 ≤ rkIdx (fixV (Subgroup.zpowers t))) →
      σ ∈ Subgroup.normalizer (S : Set (MulAut U)) → σ ∉ S → σ * σ = 1 →
      rkIdx (fixV (Subgroup.zpowers σ)) ≤ 3 * n + 2 →
      n = 2 ∧ AdjointOmega6 n S

@[expose] def K146U4AdjointAM : Prop :=
  ∀ (U : Type) [CommGroup U] [Finite U], (∀ u : U, u ^ 2 = 1) →
    ∀ (N S : Subgroup (MulAut U)), S ≤ N → (S.subgroupOf N).Normal →
      IsU4 ↥S 2 → IsIrrOn S ⊤ ⊥ → AdjointOmega6 2 S →
      8 ≤ E3.mParam N ∧ E3.aParam N ≤ 4

theorem k146ModU4Outer_of_mcClurg (hM : K146U4OuterMcClurg) (hAM : K146U4AdjointAM) :
    K146ModU4Outer := by
  intro U _ _ hU2 N S n hSN hSnormal hU4 hn hirr hbig hm
  classical
  have hevS : Even (Nat.card ↥S) := Thm14_5.even_card_of_isU4 hU4
  have hevN : Even (Nat.card N) := by
    rw [even_iff_two_dvd] at hevS ⊢
    exact hevS.trans (Subgroup.card_dvd_of_le hSN)
  obtain ⟨t₀, ht₀N, ht₀o, ht₀val⟩ :=
    CFSG.Quasithin.E3.exists_involution_rkIdx_fixV_eq_mParam N hevN
  have ht₀sq : t₀ * t₀ = 1 := by rw [← pow_two, ← ht₀o, pow_orderOf_eq_one]
  have ht₀ne : t₀ ≠ 1 := by rintro rfl; rw [orderOf_one] at ht₀o; omega
  have ht₀norm : t₀ ∈ Subgroup.normalizer (S : Set (MulAut U)) :=
    (CFSG.Quasithin.BlueprintB2.normal_subgroupOf_iff_le_normalizer hSN).mp hSnormal ht₀N
  have ht₀notS : t₀ ∉ S := by
    intro htS
    have hbig' := hbig t₀ htS ht₀ne ht₀sq
    rw [ht₀val] at hbig'
    omega
  obtain ⟨hn2, hAdj⟩ :=
    hM U hU2 S n t₀ hU4 hn hirr hbig ht₀norm ht₀notS ht₀sq
      (by rw [ht₀val]; exact hm)
  subst hn2
  obtain ⟨hm8, ha4⟩ := hAM U hU2 N S hSN hSnormal hU4 hirr hAdj
  exact ⟨rfl, by omega, by omega⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6
