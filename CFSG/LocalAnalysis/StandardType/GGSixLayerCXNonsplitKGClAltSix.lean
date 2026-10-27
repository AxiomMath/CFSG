module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGClSpOne
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpRestTypeDet

public section

namespace CFSG.StandardType

namespace ClNonsplit

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

section Orders

open CFSG.Timmesfeld.Orders CFSG.SeitzReduction.F4Pilot.EvenExc

theorem evenLieOrder_ne_three_sixty_of_admissible {t : StatedLieTag} {n f : ℕ}
    (hadm : StatedLieAdmissible t n 2 f) :
    CFSG.SeitzReduction.F4Pilot.evenLieOrder t n f ≠ 360 := by
  have hf : 1 ≤ f := hadm.2.1
  have h45 : Odd 45 := by decide
  rw [show (360 : ℕ) = 2 ^ 3 * 45 by norm_num]
  cases t with
  | PSL =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hadm.2.2.1; omega⟩
    have hm : 1 ≤ m := by have := hadm.2.2.1; omega
    show CFSG.Open.ordA (m + 1 - 1) (2 ^ f) ≠ _
    rw [Nat.add_sub_cancel]
    by_cases h31 : (m = 1 ∧ f = 3) ∨ (m = 2 ∧ f = 1)
    · rcases h31 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    · refine (profile_ordA hm hf).ne_of_ne h45 fun hN => h31 ?_
      rcases (show m = 1 ∨ 2 ≤ m by omega) with rfl | hm2
      · left
        simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_one] at hN
        exact ⟨rfl, hN⟩
      · right
        obtain ⟨hT3, hT6⟩ := MpTypeDet.three_le_tri hm2
        have hle := Nat.le_mul_of_pos_left (m * (m + 1) / 2) (show 0 < f by omega)
        have hT : m * (m + 1) / 2 = 3 := by omega
        have hm2' : m = 2 := by
          by_contra hne
          have := hT6 (by omega)
          omega
        refine ⟨hm2', ?_⟩
        rw [hT] at hN
        omega
  | PSU =>
    obtain ⟨-, -, hn, hn32⟩ := hadm
    show CFSG.Open.ordTwistedA (n - 1) (2 ^ f) ≠ _
    refine (profile_ordTwistedA (by omega) hf).ne_of_ne h45 fun hN => ?_
    obtain ⟨hT3, hT6⟩ := MpTypeDet.three_le_tri (m := n - 1) (by omega)
    have hle := Nat.le_mul_of_pos_left ((n - 1) * (n - 1 + 1) / 2) (show 0 < f by omega)
    have hT : (n - 1) * (n - 1 + 1) / 2 = 3 := by omega
    have hn3 : n = 3 := by
      by_contra hne
      have := hT6 (by omega)
      omega
    subst hn3
    rw [hT] at hN
    obtain rfl : f = 1 := by omega
    exact hn32 rfl
  | PSp =>
    obtain ⟨-, -, hn, -⟩ := hadm
    show CFSG.Open.ordBC n (2 ^ f) ≠ _
    refine (profile_ordBC hf).ne_of_ne h45 fun hN => ?_
    have h4 : 4 ≤ n * n := by nlinarith
    have hle := Nat.le_mul_of_pos_left (n * n) (show 0 < f by omega)
    omega
  | POmegaOdd => exact absurd rfl hadm.2.2.2
  | POmegaPlus =>
    have hn : 4 ≤ n := hadm.2.2
    show CFSG.Open.ordD n (2 ^ f) ≠ _
    refine (profile_ordD (by omega) hf).ne_of_ne h45 fun hN => ?_
    have h4 : 12 ≤ n * (n - 1) := by
      have : 3 ≤ n - 1 := by omega
      nlinarith
    have hle := Nat.le_mul_of_pos_left (n * (n - 1)) (show 0 < f by omega)
    omega
  | POmegaMinus =>
    have hn : 4 ≤ n := hadm.2.2
    show CFSG.Open.ordTwistedD n (2 ^ f) ≠ _
    refine (profile_ordTwistedD (by omega) hf).ne_of_ne h45 fun hN => ?_
    have h4 : 12 ≤ n * (n - 1) := by
      have : 3 ≤ n - 1 := by omega
      nlinarith
    have hle := Nat.le_mul_of_pos_left (n * (n - 1)) (show 0 < f by omega)
    omega
  | F4 => exact (profile_ordF4' hf).ne_of_ne h45 (by omega)
  | E6 => exact (profile_ordE6' hf).ne_of_ne h45 (by omega)
  | E7 => exact (profile_ordE7' hf).ne_of_ne h45 (by omega)
  | E8 => exact (profile_ordE8' hf).ne_of_ne h45 (by omega)
  | twistedE6 => exact (profile_ordTwistedE6' hf).ne_of_ne h45 (by omega)
  | G2 => exact (profile_ordG2' hf).ne_of_ne h45 (by omega)
  | trialityD4 => exact (profile_ordTrialityD4' hf).ne_of_ne h45 (by omega)
  | twistedB2 => exact (profile_ordSuzuki' hf).ne_of_ne h45 (by omega)
  | twistedG2 => exact absurd hadm.2.2.2.1 (by norm_num)
  | twistedF4 => exact (profile_ordTwistedF4' hf).ne_of_ne h45 (by omega)
  | Tits =>
    show CFSG.Open.ordTits ≠ _
    simp [CFSG.Open.ordTits]

end Orders

section Main

theorem not_ggNbrClauseFiveMarking_of_no_char_two {G : Type} [Group G] {K' : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hp3 : p ≠ 3) (x : G)
    (hno : ∀ lab : LargeEvenLabel, markChar lab = 2 →
      ¬ MarkedModel lab (↥K' ⧸ Subgroup.center ↥K')) :
    ¬ GGNbrClauseFiveMarking p x K' := by
  intro hmark
  rcases largeEvenMarking_or hmark with hHS' | hPF
  · obtain ⟨lab, hlab, R, _, I, F, θ, -, -, hHS'', hMM⟩ := largeEvenMarking_exists_markedModel hHS'
    have hX : MarkedModel lab (↥K' ⧸ Subgroup.center ↥K') := MarkedModel.of_mulEquiv θ.symm hMM
    by_cases hc : markChar lab = 2
    · exact hno lab hc hX
    · obtain ⟨t, l, n⟩ := lab
      cases t
      all_goals first
        | exact absurd rfl hc
        | (obtain ⟨-, hl⟩ := hlab
           obtain ⟨-, hn⟩ := hl
           simp only at hn
           subst hn
           rcases LinNonsplit.halfSplit_cases hHS'' with h1 | h1 | h1 | ⟨h0, -, -⟩ | ⟨h0 | h0, -, -⟩
           · exact hp.one_lt.ne' (Nat.dvd_one.mp (by simpa using h1))
           · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (by simpa using h1))
           · exact hp3 h1
           all_goals simp at h0)
  · have hS : ∀ (lab : LargeEvenLabel) (R : Type) [Group R] (I F : Set (MulAut R))
        (θ : ↥K' ⧸ Subgroup.center ↥K' ≃* R),
        (LargeEvenPrimeField p lab I F (LargeEvenInduces θ fun j j' => (j' : G) = x⁻¹ * j * x) ∧
          MarkedModel lab R) → lab.tag = .B2der ∨ lab.tag = .G2der := by
      intro lab R _ I F θ hP
      have hX : MarkedModel lab (↥K' ⧸ Subgroup.center ↥K') := MarkedModel.of_mulEquiv θ.symm hP.2
      by_cases hc : markChar lab = 2
      · exact absurd hX (hno lab hc)
      · obtain ⟨t, l, n⟩ := lab
        cases t <;> first | exact absurd rfl hc | simp
    have hall : ∀ lab, LargeEvenInLambda2 lab → (lab.tag = .B2der ∨ lab.tag = .G2der) →
        LargeEvenLabelAll lab fun R _ I F => ∀ φ ∈ F, φ = 1 := by
      intro lab hlab hS'
      rcases hS' with hB | hG2
      · exact largeEvenLabelAll_b2der hB fun K _ _ hK φ hφ =>
          matFieldImage_eq_one_of_card_two hK _ hφ
      · exact largeEvenLabelAll_smallExc hlab (Or.inl hG2) fun A K _ _ hK H φ hφ =>
          chevFieldImage_eq_one_of_card_two hK H hφ
    have hPF' := largeEvenMarking_and_labelAll hall hS (largeEvenMarking_markedModel hPF)
    obtain ⟨-, lab, hlab, hraw'⟩ := hPF'
    obtain ⟨R, _, I, F, -, -, θ, ⟨⟨-, f', hf', u', -, hord, -⟩, -⟩, htriv⟩ :=
      largeEvenRawDatum_exists hraw'
    rw [htriv f' hf', orderOf_one] at hord
    exact hp.one_lt.ne hord

end Main

section Input

theorem ggNonsplitNbrAltSixInput_holds : GGNonsplitNbrAltSixInput := by
  intro G _ _ K' ⟨e⟩ p hp _ hp3 x
  have h6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    have h := two_mul_nat_card_alternatingGroup (α := Fin 6)
    have hF6 : Nat.card (Fin 6) = 6 := by simp
    rw [Nat.card_perm, hF6, show Nat.factorial 6 = 720 by decide] at h
    omega
  have hZA : Subgroup.center (alternatingGroup (Fin 6)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simp)
  have hZ : Subgroup.center ↥K' = ⊥ := by
    have h1 := Subgroup.map_center_eq e
    rw [hZA] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1
  have hcard : Nat.card (↥K' ⧸ Subgroup.center ↥K') = 360 := by
    rw [hZ, Nat.card_congr (QuotientGroup.quotientBot (G := ↥K')).toEquiv,
      Nat.card_congr e.toEquiv, h6]
  refine not_ggNbrClauseFiveMarking_of_no_char_two hp hp3 x fun lab hc hX => ?_
  have hX' := lieModel_of_markedModel hc hX
  have h1 := CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hX'
  rw [hcard] at h1
  exact evenLieOrder_ne_three_sixty_of_admissible
    (CFSG.SeitzReduction.F4Pilot.statedLieAdmissible_of_lieModel hX') h1.symm

end Input

end ClNonsplit

section Tag

theorem ggNonsplitTag_PSp_holds : GGNonsplitTag .PSp :=
  ggNonsplitTag_PSp_of_altSix ClNonsplit.ggNonsplitNbrAltSixInput_holds

end Tag

end CFSG.StandardType
