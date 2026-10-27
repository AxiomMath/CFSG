module

public import CFSG.Quasithin.EmptyFaithful.S151XA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def SumNatDual15127 (Z₂ L : Subgroup G) : Prop :=
  ∃ (hU : IsElemAbelian 2 (uOf1527 Z₂ L)) (n : ℕ),
    @SumNatDual ↥(uOf1527 Z₂ L) (commGroupOfElemAbelian hU) (autOn L (uOf1527 Z₂ L))
      ((uLOf1527 Z₂ L).subgroupOf (uOf1527 Z₂ L)) n

@[expose] def Q1Offender15128 (T Mc Z₁ Z₂ L : Subgroup G) : Prop :=
  ∃ hU : IsElemAbelian 2 (uOf1527 Z₂ L), ∃ A : Subgroup (MulAut ↥(uOf1527 Z₂ L)),
    A ≤ autOn (q1_1516 Mc Z₁) (uOf1527 Z₂ L) ∧
      @IsFFStarOffender ↥(uOf1527 Z₂ L) (commGroupOfElemAbelian hU)
        (autOn (L ⊔ s1516 T Z₁) (uOf1527 Z₂ L)) A

@[expose] def vC27Of15128 (Mc Z₁ L : Subgroup G) : Subgroup G :=
  omegaOneCenterOf (pCoreOf 2 (L ⊔ q1_1516 Mc Z₁))

@[expose] def Q1OffenderV15128 (Mc Z₁ L : Subgroup G) : Prop :=
  ∃ hV : IsElemAbelian 2 (vC27Of15128 Mc Z₁ L),
    ∃ A : Subgroup (MulAut ↥(vC27Of15128 Mc Z₁ L)),
      A ≤ autOn (q1_1516 Mc Z₁) (vC27Of15128 Mc Z₁ L) ∧
        @IsFFStarOffender ↥(vC27Of15128 Mc Z₁ L) (commGroupOfElemAbelian hV)
          (autOn (L ⊔ q1_1516 Mc Z₁) (vC27Of15128 Mc Z₁ L)) A

theorem q1OffenderV15128_of (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G} (hc : Ctx15128 T Mc M Z₁ Z₂ V₁ V₂ L) :
    Q1OffenderV15128 Mc Z₁ L := by
  have hLN : g1_1516 Z₁ ≤ Subgroup.normalizer (L : Set G) := by
    have h := normalizer_le_normalizer_oPrimeResidualOf1516 3 (g1_1516 Z₁)
    rw [← hc.h25.one] at h
    exact Subgroup.le_normalizer.trans h
  have hRN : q1_1516 Mc Z₁ ≤ Subgroup.normalizer (L : Set G) :=
    ((q1_1516_le Mc Z₁).trans (mZ1516_le_g1 Mc Z₁)).trans hLN
  have h := hC27 G (g1_1516 Z₁) (q1_1516 Mc Z₁) (mZ1516 Mc Z₁) L (vC27Of15128 Mc Z₁ L)
    hc.h18.five.2.2 hc.hL.comp hc.hL.quasi hc.h26.1 hc.hL.not_le hRN rfl
  obtain ⟨-, ⟨-, hV, -, A, hA, hAoff⟩, -⟩ := h
  exact ⟨hV, A, hA, hAoff⟩

@[expose] def Input15128OffenderTransfer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15128 T Mc M Z₁ Z₂ V₁ V₂ L → Q1OffenderV15128 Mc Z₁ L → Q1Offender15128 T Mc Z₁ Z₂ L

@[expose] def Input15128Offender : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15128 T Mc M Z₁ Z₂ V₁ V₂ L → Q1Offender15128 T Mc Z₁ Z₂ L

theorem offender15128_of (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    (nTr : Input15128OffenderTransfer) : Input15128Offender :=
  fun G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc =>
    nTr G T Mc M Z₁ Z₂ V₁ V₂ L hc (q1OffenderV15128_of hC27 hc)

@[expose] def Input15128ML : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15128 T Mc M Z₁ Z₂ V₁ V₂ L → ¬ SumNatDual15127 Z₂ L →
    mZ1516 Mc Z₁ ⊓ L = L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ∧
      mZ1516 Mc Z₁ ⊓ L = L ⊓ Subgroup.normalizer (zUOf1528 Z₂ L : Set G)

@[expose] def Input15128Natural : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15128 T Mc M Z₁ Z₂ V₁ V₂ L → ¬ SumNatDual15127 Z₂ L →
    mZ1516 Mc Z₁ ⊓ L = L ⊓ Subgroup.normalizer (zUOf1528 Z₂ L : Set G) →
    Q1Offender15128 T Mc Z₁ Z₂ L →
    IsNaturalUL L (uLOf1527 Z₂ L) ∧ Nat.card (zUOf1528 Z₂ L) = 2

@[expose] def Input15128SumNatDual : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15128 T Mc M Z₁ Z₂ V₁ V₂ L → SumNatDual15127 Z₂ L → Q1Offender15128 T Mc Z₁ Z₂ L → False

theorem lemma15128InputU_of_named_inputs (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    (nTr : Input15128OffenderTransfer) (nML : Input15128ML)
    (nN : Input15128Natural) (nS : Input15128SumNatDual) : Lemma15128InputU := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 h19 hL h22 h24 h25 h26 h27
  have hc : Ctx15128 T Mc M Z₁ Z₂ V₁ V₂ L := ⟨hC, h17, h18, h19, hL, h22, h24, h25, h26, h27⟩
  have hoff := offender15128_of hC27 nTr G T Mc M Z₁ Z₂ V₁ V₂ L hc
  by_cases hsum : SumNatDual15127 Z₂ L
  · exact (nS G T Mc M Z₁ Z₂ V₁ V₂ L hc hsum hoff).elim
  · obtain ⟨hML1, hML2⟩ := nML G T Mc M Z₁ Z₂ V₁ V₂ L hc hsum
    obtain ⟨hnat, hcard⟩ := nN G T Mc M Z₁ Z₂ V₁ V₂ L hc hsum hML2 hoff
    exact ⟨hnat, hcard, hML1, hML2⟩

end CFSG.Quasithin
