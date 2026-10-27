module

public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperRestOrth
public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperRestUnitary
public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperRestExc
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRanks
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeThree

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggStdSubIOneProperInputOn_of_lift_card_lt {S : ℕ → LargeEvenLabel → Prop}
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenSplit p lab → LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧
        ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
          ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ → ∀ A : Subgroup (MulAut L'),
            IsElemAbelian p A → (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
              Nat.card A < p ^ 3) :
    GGStdSubIOneProperInputOn S := by
  intro G _ _ p B Bs x L hT _ _ hM
  have hp : p.Prime := hT.2.2.2.2.2.1.1
  have hM' := largeEvenMarking_and_labelAll (S := fun lab => S p lab ∧ LargeEvenSplit p lab)
    (fun lab hlab hs => h p lab hp hlab hs.1 hs.2) (fun _ _ _ _ _ _ hP => ⟨hP.1, hP.2.1⟩) hM
  obtain ⟨hL, lab, -, hraw⟩ := hM'
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, -, hBN, h3⟩, r, hlift, hsmall⟩ :=
    largeEvenRawDatum_exists hraw
  obtain ⟨-, -, -, -, -, hβ, hS, -⟩ := hT
  obtain ⟨hA, hAI, -, h3'⟩ := ggGamma_range_props hp hS hβ.2.2.2 hL θ hBN h3 hlift
  exact absurd h3' (not_le.mpr (hsmall L (ggQuotHom θ) (ggQuotHom_surjective θ)
    (by rw [ker_ggQuotHom]) hL _ hA hAI))

@[expose] def GGIOneUnitaryTwoLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twA ∧ lab.rank = 2 ∧ p ∣ 2 ^ lab.n + 1

section CertsU


theorem ggStdSubIOneProperInputOn_unitaryTwo :
    GGStdSubIOneProperInputOn GGIOneUnitaryTwoLabel := by
  refine ggStdSubIOneProperInputOn_of_lift_card_lt fun p lab hp hlab h _ => ?_
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hl, hpq⟩ := h
  dsimp only at ht hl hpq
  subst ht hl
  have hn2 : 2 ≤ n := hlab.2.2 rfl
  have h2 : 2 < 2 ^ n := by
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    omega
  have h1 := largeEvenLabelAll_torusLift_twA hlab rfl hp hpq
  refine (h1.and fun Q hQ => ?_).mono fun _ _ _ _ ⟨hlift, hsm⟩ => ⟨_, hlift, hsm⟩
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  exact ⟨K, i1, i2, hK, hq, fun L' _ _ ψ hψ hker hperf A hA hAI =>
    TableBUE.card_lt_unitary_three (TableBU.unitaryFieldData_of_card hK (by omega)) hK h2 hp hpq
      hψ hker hperf hA hAI⟩

end CertsU

section Certs


theorem ggStdSubIOneProperInputOn_small : GGStdSubIOneProperInputOn GGCorFourTwoSmallLabel :=
  ggStdSubIOneProperInputOn_of_card_lt fun _ _ hp hlab h hs =>
    largeEvenLabelAll_card_lt_corFourTwoSmall hp hlab h hs

theorem ggStdSubIOneProperInputOn_twF4Three (hSR : TableBExcSmallRanks.GGTwF4ThreeRankInput) :
    GGStdSubIOneProperInputOn fun p lab => lab.tag = .twF4 ∧ p = 3 :=
  ggStdSubIOneProperInputOn_of_card_lt fun p _ hp hlab ⟨ht, hp3⟩ hs => by
    subst hp3
    exact TableBExcSmallRanks.largeEvenLabelAll_card_lt_twF4_of
      (fun a ha K _ _ _ hK _ E hE => hSR a ha K hK E hE) hp hlab ht hs

@[expose] def GGIOneProperDoneLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGTypeALabel p lab ∨ GGReflSpLabel p lab ∨ GGTwoThreeLabel p lab ∨
    GGCorFourTwoOrthSplitLabel p lab ∨ GGIOneTwDThreeLabel p lab ∨ GGCorFourTwoSmallLabel p lab ∨
    (lab.tag = .twF4 ∧ p = 3) ∨ GGIOneUnitaryTwoLabel p lab ∨ GGIOneExcSplitLabel p lab

@[expose] def GGIOneProperRestLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  ¬ GGIOneUnitaryLabel p lab ∧ ¬ GGIOneProperDoneLabel p lab

theorem ggStdSubIOneProperInputOn_done (ha₀ : GGLNoncyclicInput)
    (hSR : TableBExcSmallRanks.GGTwF4ThreeRankInput) :
    GGStdSubIOneProperInputOn GGIOneProperDoneLabel :=
  (((((((((ggStdSubIOneProperInputOn_typeA ha₀).or (ggStdSubIOneProperInputOn_reflSp ha₀)).or
    (ggStdSubIOneProperInputOn_twoThree ha₀)).or (ggStdSubIOneProperInputOn_orthSplit ha₀)).or
      (ggStdSubIOneProperInputOn_twDThree ha₀)).or ggStdSubIOneProperInputOn_small).or
        (ggStdSubIOneProperInputOn_twF4Three hSR)).or ggStdSubIOneProperInputOn_unitaryTwo).or
          (ggStdSubIOneProperInputOn_excSplit ha₀)).mono
    fun _ _ h => by
      rcases h with h | h | h | h | h | h | h | h | h
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h)))))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))
      · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inl (Or.inr h)
      · exact Or.inr h

theorem ggStdSubIOneProperInputOn_notUnitary_of_rest (ha₀ : GGLNoncyclicInput)
    (hSR : TableBExcSmallRanks.GGTwF4ThreeRankInput)
    (hR : GGStdSubIOneProperInputOn GGIOneProperRestLabel) :
    GGStdSubIOneProperInputOn fun p lab => ¬ GGIOneUnitaryLabel p lab :=
  ((ggStdSubIOneProperInputOn_done ha₀ hSR).or hR).mono fun p lab h => by
    by_cases hd : GGIOneProperDoneLabel p lab
    · exact Or.inl hd
    · exact Or.inr ⟨h, hd⟩

theorem ggStdSubIOneProperInput_of_rest (ha₀ : GGLNoncyclicInput)
    (hSR : TableBExcSmallRanks.GGTwF4ThreeRankInput)
    (hR : GGStdSubIOneProperInputOn GGIOneProperRestLabel) : GGStdSubIOneProperInput :=
  ggStdSubIOneProperInput_of_cover ((ggStdSubIOneProperInputOn_unitary_holds ha₀).or
    (ggStdSubIOneProperInputOn_notUnitary_of_rest ha₀ hSR hR))
    fun p lab _ _ => em (GGIOneUnitaryLabel p lab)

end Certs

end CFSG.StandardType
