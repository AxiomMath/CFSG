module

public import CFSG.RankThree.GF2n.Smith81.TiOuter
public import CFSG.RankThree.GF2n.Smith81.TiSylow
public import CFSG.RankThree.GF2n.Smith81.Sec1Main

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def TiFusionD2Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), StrothHyp M Q Z →
    (∃ g : G, B = conjSubgroup g Z) → B ≤ Q → B ≠ Z → CaseD2 M Q Z B →
      NoA2 Q Z (LB M Q B) → TIFusion M Q Z

@[expose] def TiFusionD3Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), StrothHyp M Q Z →
    (∃ g : G, B = conjSubgroup g Z) → B ≤ Q → B ≠ Z → CaseD3 M Q Z B → TIFusion M Q Z

section Lane

variable [Finite G] {M Q Z B : Subgroup G}

theorem not_pow_dvd_card (H : StrothHyp M Q Z) {n : ℕ} (hn : 1 ≤ n) (hw : Width Q Z n) (k : ℕ)
    (hk : (2 * n + 1) + n * (2 * n - 1) + 1 ≤ k) : ¬ Nat.card Z ^ k ∣ Nat.card G := by
  obtain ⟨f, k₀, hf, -⟩ := H.cp
  have hbound := factorization_card_le H hn hw
  have hfac : (Nat.card Z).factorization 2 = f := by
    rw [hf, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]
  rw [hfac] at hbound
  have hf0 : f ≠ 0 := by
    rintro rfl
    have := H.q4
    rw [hf] at this
    simp at this
  have hlt : f.factorization 2 < f := Nat.factorization_lt 2 hf0
  intro hdvd
  have hGne : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have h2 : 2 ^ (f * k) ∣ Nat.card G := by
    rw [hf, ← pow_mul] at hdvd
    exact hdvd
  have hle := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hGne).mp h2
  nlinarith

theorem smithLaneTI_D1 (hCorB : CorBRankTwo) (hOrd : TiLieOrders) (H : StrothHyp M Q Z)
    {n : ℕ} (hn : CaseD1 Q Z n) :
    CFSG.Blueprint.LieModel (FStar G) .PSL 3 2 n ∧ OuterOnFStar G := by
  obtain ⟨hZ, hw⟩ := width_of_caseD1 H hn
  have hT : TIFusion M Q Z := smith_1_12_of_width_one H hw
  obtain ⟨f, hf, hfam⟩ := tiFamily hCorB hOrd H hT (Or.inl rfl) hw
    (fun _ => not_pow_dvd_card H le_rfl hw 6 (by norm_num))
    (fun h => absurd h (by norm_num))
  have hfn : f = n := Nat.pow_right_injective (le_refl 2) (hf.symm.trans hZ)
  rcases hfam with ⟨-, hL⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact ⟨hfn ▸ hL, outerOnFStar_of_psl3 hOrd H hn hf hL⟩
  · omega
  · omega

theorem smithLaneTI_D2 (hCorB : CorBRankTwo) (hOrd : TiLieOrders)
    (hD2 : TiFusionD2Statement) (H : StrothHyp M Q Z) (hB : ∃ g : G, B = conjSubgroup g Z)
    (hBQ : B ≤ Q) (hBZ : B ≠ Z) (hc : CaseD2 M Q Z B) (hno : NoA2 Q Z (LB M Q B)) :
    ∃ f : ℕ, Nat.card Z = 2 ^ f ∧ CFSG.Blueprint.LieModel (FStar G) .G2 0 2 f := by
  have hT : TIFusion M Q Z := hD2 G M Q Z B H hB hBQ hBZ hc hno
  have hw : Width Q Z 2 := by
    have := hc.1
    unfold Width
    simpa using this
  obtain ⟨f, hf, hfam⟩ := tiFamily hCorB hOrd H hT (Or.inr (Or.inl rfl)) hw
    (fun h => absurd h (by norm_num))
    (fun _ => not_pow_dvd_card H (by norm_num) hw 12 (by norm_num))
  refine ⟨f, hf, ?_⟩
  rcases hfam with ⟨h, -⟩ | ⟨-, hL⟩ | ⟨h, -⟩
  · omega
  · exact hL
  · omega

theorem smithLaneTI_D3 (hCorB : CorBRankTwo) (hOrd : TiLieOrders)
    (hD3 : TiFusionD3Statement) (H : StrothHyp M Q Z) (hB : ∃ g : G, B = conjSubgroup g Z)
    (hBQ : B ≤ Q) (hBZ : B ≠ Z) (hc : CaseD3 M Q Z B) :
    ∃ f : ℕ, Nat.card Z = 2 ^ f ∧ CFSG.Blueprint.LieModel (FStar G) .trialityD4 0 2 f := by
  have hT : TIFusion M Q Z := hD3 G M Q Z B H hB hBQ hBZ hc
  have hw : Width Q Z 4 := by
    have := hc.1
    unfold Width
    simpa using this
  obtain ⟨f, hf, hfam⟩ := tiFamily hCorB hOrd H hT (Or.inr (Or.inr rfl)) hw
    (fun h => absurd h (by norm_num)) (fun h => absurd h (by norm_num))
  refine ⟨f, hf, ?_⟩
  rcases hfam with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, hL⟩
  · omega
  · omega
  · exact hL

end Lane

end CFSG.RankThree.GF2n.Smith81
