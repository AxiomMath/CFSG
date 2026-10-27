module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRest
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRanks
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallTits
public import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeAut
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeThree

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace StdSubRestThree

theorem card_lt_of_congr {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    {I : Set (MulAut R)} {I' : Set (MulAut R')} (hI : ∀ φ ∈ I, MulAut.congr e φ ∈ I') {p k : ℕ}
    (h : ∀ X' : Subgroup (MulAut R'), (X' : Set (MulAut R')) ⊆ I' → IsElemAbelian p X' →
      Nat.card X' < p ^ k)
    {X : Subgroup (MulAut R)} (hXI : (X : Set (MulAut R)) ⊆ I) (hX : IsElemAbelian p X) :
    Nat.card X < p ^ k := by
  have h1 := h (X.map (MulAut.congr e).toMonoidHom)
    (by
      rintro _ ⟨φ, hφ, rfl⟩
      exact hI φ (hXI hφ))
    (TableB.isElemAbelian_map hX _)
  rwa [Subgroup.card_map_of_injective (MulAut.congr e).injective] at h1

theorem recipeLinear_card_lt_two {d N : ℕ} (hd : 0 < d) (hd5 : d ≤ 5) (hN : N = 2)
    {Q : LargeEvenRawCont} (h : LargeEvenRecipeLinear d N Q) :
    LargeEvenRecipeLinear d N fun R _ I F => Q R I F ∧ ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian 3 X → Nat.card X < 3 ^ 3 := by
  subst hN
  obtain ⟨K, _, _, hK, hQ⟩ := h
  refine ⟨K, inferInstance, inferInstance, hK, hQ, fun X hXI hX => ?_⟩
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (le_refl 1) (by rw [hK, pow_one])
  exact card_lt_of_congr (TypeA.recipeEquiv d K) (fun _ hφ => TypeA.congr_recipeEquiv_mem hφ)
    (fun _ hX'I hX' => TwoThree.card_lt_of_subset_conjAut hK hd hd5 hX' hX'I) hXI hX

@[expose] def GGTwoThreeSmallLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p = 3 ∧ lab.n = 1 ∧ ((lab.tag = .A ∧ lab.rank ≤ 4) ∨ (lab.tag = .D ∧ lab.rank = 3))

theorem largeEvenLabelAll_card_lt_twoThreeSmall {p : ℕ} {lab : LargeEvenLabel}
    (h : GGTwoThreeSmallLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3 := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨rfl, hn, ht⟩ := h
  dsimp only at hn ht
  subst hn
  intro Q hQ
  rcases ht with ⟨rfl, hl⟩ | ⟨rfl, rfl⟩
  · exact recipeLinear_card_lt_two (d := l + 1) (by omega) (by omega) (by norm_num) hQ
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    simp only [↓reduceIte] at hQ ⊢
    exact recipeLinear_card_lt_two (d := 4) (by norm_num) (by norm_num) (by norm_num) hQ

theorem largeEvenLabelAll_lift_card_lt_unitaryThree {p : ℕ} {lab : LargeEvenLabel}
    (hp : p.Prime) (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .twA) (hl : lab.rank = 2)
    (hs : LargeEvenSplit p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R),
      Function.Surjective ψ → ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
      ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
        (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) → Nat.card A < p ^ 3 := by
  have hpq : p ∣ 2 ^ lab.n + 1 := dvd_of_largeEvenSplit_twA hs ht
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hl hpq
  subst ht hl
  obtain ⟨hn, -, hl22⟩ := hlab
  dsimp only at hn hl22
  have h2 : 2 < 2 ^ n := by
    have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (hl22 rfl)
    omega
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq'⟩ := hQ
  exact ⟨K, i1, i2, hK, hq', fun L' _ _ ψ hψ hker hperf A hA hAI =>
    TableBUE.card_lt_unitary_three (TableBU.unitaryFieldData_of_card hK hn) hK h2 hp hpq hψ hker
      hperf hA hAI⟩

end StdSubRestThree

open StdSubRestThree

open TableB in
theorem ggStdSubSmallInputOn_of_labelAll_lift_card_lt {S : ℕ → LargeEvenLabel → Prop}
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenSplit p lab → LargeEvenLabelAll lab fun R _ I _ => ∀ (L' : Type) [Group L']
        [Finite L'] (ψ : L' →* R), Function.Surjective ψ → ψ.ker ≤ Subgroup.center L' →
        commutator L' = ⊤ → ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
          (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) → Nat.card A < p ^ 3) :
    GGStdSubSmallInputOn S := by
  intro G _ _ p B Bs x L D J hcfg hM _
  obtain ⟨-, -, -, -, -, hβ, hS, -⟩ := hcfg.1
  have hp : p.Prime := hβ.1
  have := Fact.mk hp
  have hM' := largeEvenMarking_and_labelAll (S := fun lab => S p lab ∧ LargeEvenSplit p lab)
    (fun lab hlab hs => h p lab hp hlab hs.1 hs.2) (fun _ _ _ _ _ _ hP => ⟨hP.1, hP.2.1⟩) hM
  obtain ⟨hL, lab, -, hraw⟩ := hM'
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, -, hBN, h3⟩, hlt⟩ := largeEvenRawDatum_exists hraw
  set γ := ggGamma L hBN with hγ
  have hBp : ∀ b : B, b ^ p = 1 := fun b => Subtype.ext (by simpa using hS.1.1.2 b b.2)
  have hBc : ∀ a b : B, a * b = b * a := fun a b =>
    Subtype.ext (IsElemAbelian.comm hS.1.1 a.2 b.2)
  have hA : IsElemAbelian p γ.range := isElemAbelian_range hBc hBp γ
  have hAI : ∀ a ∈ γ.range, ∃ φ ∈ I, ∀ l : L, φ (ggQuotHom θ l) =
      ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta L θ hBN b, ggBeta_mem L θ hBN h3 b,
      fun l => ggBeta_ggQuotHom L hBN θ b l⟩
  have hcA := card_range_ggGamma_mul L hBN hp hS
  have h3' : p ^ 3 ≤ Nat.card γ.range := by
    have h4 := pow_four_le_card_of_bmax hp hS.1 hβ.2.2.2
    rw [← hcA, pow_succ] at h4
    exact Nat.le_of_mul_le_mul_right h4 hp.pos
  exact absurd (hlt L (ggQuotHom θ) (ggQuotHom_surjective θ)
    (by rw [ker_ggQuotHom]) hL γ.range hA hAI) (not_lt.mpr h3')

@[expose] def GGStdSubSmallVac3Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  TableBExcSmallRanks.GGTableBExcSmallRanksDoneLabel p lab ∨ lab.tag = .twF4der ∨
    GGTwoThreeSmallLabel p lab ∨ (lab.tag = .twA ∧ lab.rank = 2)

theorem ggStdSubSmallInputOn_vac3 :
    GGStdSubSmallInputOn GGStdSubSmallVac3Label :=
  ((ggStdSubSmallInputOn_of_labelAll_card_lt (S := fun p lab =>
      TableBExcSmallRanks.GGTableBExcSmallRanksDoneLabel p lab ∨ lab.tag = .twF4der ∨
        GGTwoThreeSmallLabel p lab) fun _ _ hp hlab h hs => by
      rcases h with h | h | h
      · exact TableBExcSmallRanks.largeEvenLabelAll_card_lt_smallRanksDone hp hlab h hs
      · exact TableBExcSmallRest.largeEvenLabelAll_card_lt_twF4der_holds hp hlab h hs
      · exact largeEvenLabelAll_card_lt_twoThreeSmall h).or
    (ggStdSubSmallInputOn_of_labelAll_lift_card_lt (S := fun _ lab =>
      lab.tag = .twA ∧ lab.rank = 2) fun _ _ hp hlab h hs =>
        largeEvenLabelAll_lift_card_lt_unitaryThree hp hlab h.1 h.2 hs)).mono fun _ _ h => by
    rcases h with h | h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inl (Or.inr (Or.inr h))
    · exact Or.inr h

theorem ggStdSubSmallInputOn_twF4
    (hF3 : TableBExcSmallRanks.GGTwF4ThreeRankInput) :
    GGStdSubSmallInputOn fun _ lab => lab.tag = .twF4 :=
  ggStdSubSmallInputOn_of_labelAll_card_lt fun p _ hp hlab ht hs => by
    by_cases hp3 : p = 3
    · subst hp3
      refine TableBExcSmallRanks.largeEvenLabelAll_card_lt_twF4_of ?_ hp hlab ht hs
      intro a ha K _ _ _ hK _ E hE
      exact hF3 a ha K hK E hE
    · exact TableBExcSmallRanks.largeEvenLabelAll_card_lt_twF4_of_ne_three hp3 hp hlab ht hs

end CFSG.StandardType
