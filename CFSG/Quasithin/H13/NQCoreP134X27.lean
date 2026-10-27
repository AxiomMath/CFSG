module

public import CFSG.Quasithin.H13.NQCoreP134X27Pair
public import CFSG.Quasithin.H13.NQCoreP134Dich3

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.QuasithinUnique.Vol2Native CFSG.Quasithin.Ch1Sec3

@[expose] def NoThreeExtraspecialConfig : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (L P T : Subgroup A), OddConfig 3 L P T →
    Nat.card P = 27 → False

section Quotient

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem normal_of_threeExtraspecial (hyp : SQTKHypCat Γ) (h36 : A36CoreStatementCat Γ)
    (h37 : A37Statement Γ) (h38 : A38Part3 Γ) (hO3 : OutThreeFact) (hOA : OutAbelianFact)
    (hX27 : NoThreeExtraspecialConfig) {P T N O : Subgroup Γ} (hexp : ∀ x ∈ P, x ^ 3 = 1)
    (hcard : Nat.card P = 3 ^ 3) (hT : IsSylowTwoOf T ⊤) (hNT : N ≤ T)
    (hNP : N ≤ Subgroup.normalizer (P : Set Γ))
    (hirr : ∀ U : Subgroup Γ, ⁅P, P⁆ ≤ U → U ≤ P → N ≤ Subgroup.normalizer (U : Set Γ) →
      U = ⁅P, P⁆ ∨ U = P)
    (hmul : ∀ t ∈ T, ∀ x ∈ P, ∃ y ∈ P, ∃ s ∈ T, t * x = y * s)
    (hTON : T ≤ O ⊔ N) (hOX : ∀ K : Subgroup Γ, K.Normal → P ≤ K → O ≤ K)
    (hPc : P ≤ commutator Γ) : P.Normal := by
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hrank : ∀ r : ℕ, r.Prime → r ≠ 2 → Open.pRank r (⊤ : Subgroup Γ) ≤ 2 :=
    CFSG.SectionRank.isStronglyQuasithin_iff.1 hyp.sqt
  have hPp : IsPGroup 3 P := fun x => ⟨1, Subtype.ext (by simpa using hexp x x.2)⟩
  have hc2 : 3 ^ 2 ≤ Nat.card P := by
    rw [hcard]
    norm_num
  rcases P134.normal_or_centralizes_fitting hyp.o2 hrank (by norm_num) hPp hexp hc2 hcard.le hNP
      hirr hPc with hn | ⟨hFit, hrk⟩
  · exact hn
  exfalso
  have hrkP : 2 ≤ Open.pRank 3 P := two_le_pRank_of_pow_eq_one hexp hc2
  obtain ⟨L, hL, hLP⟩ := P134.exists_component_not_le_centralizer hPp hrkP hFit hrk
  have hLc : L ∈ cComp (⊤ : Subgroup Γ) := mem_cComp_top_of_isComponent hL
  by_cases hLn : L.Normal
  ·
    have hPL : P ≤ L :=
      le_of_normal_case_three hyp h36 hO3 hexp (Or.inr hcard) hNP hirr hLc hL hLn hLP
    refine hX27 Γ L P T
      { hyp := hyp
        normal := hLn
        component := hL
        le := hPL
        exp := hexp
        card := Or.inr hcard
        sylow := hT
        mul := hmul
        irred := fun U hcU hUP hTU => hirr U hcU hUP ((le_inf hNT hNP).trans hTU) } ?_
    rw [hcard]
    norm_num
  ·
    have h9 := card_sq_of_pair_case_odd hyp h37 h38 hOA (p := 3) (by norm_num) hexp
      (Or.inr hcard) hT hNT hNP hirr hTON hOX hLc hL hLn hLP
    rw [hcard] at h9
    norm_num at h9

end Quotient

theorem prop134ThreeExtraspecial_of_noConfig (h36 : A36CoreForSQTKCat) (h37 : A37ForSQTKCat)
    (h38 : A38ForSQTKCat) (hO3 : OutThreeFact) (hOA : OutAbelianFact)
    (hX27 : NoThreeExtraspecialConfig) : Prop134ThreeExtraspecial := by
  intro G _ _ H S X P hsqtk _ hS hXH hX h27 hPX hPp hP27
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hyp : SQTKHypCat (↥H ⧸ CFSG.pCore 2 ↥H) := SQTKHypCat.quotient_pCore ↥H hsqtk
  obtain ⟨hpX, hSyl⟩ := sylow_of_card_eq_relIndex hX hp2 hPX hPp (hP27.trans h27.symm)
  have hPH : P ≤ H := hPX.trans hXH
  have hcardb : Nat.card (modO2Image H P) = 3 ^ 3 := by
    rw [card_bar_of_sylow hXH hp2 hSyl, hP27]
    norm_num
  have hirr := irr_modO2Image' hPH (inf_le_left.trans hS.1) inf_le_right
    (irr_of_sylow hS hXH hX hp2 hpX hSyl)
  have hNT : modO2Image H (S ⊓ Subgroup.normalizer (P : Set G)) ≤ modO2Image H S :=
    P134.modO2Image_mono inf_le_left
  have hNP : modO2Image H (S ⊓ Subgroup.normalizer (P : Set G)) ≤
      Subgroup.normalizer (modO2Image H P : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    P134.modO2Image_le_normalizer inf_le_right
  exact le_normalizer_of_normal_of_sylow hS hXH hX hp2 hpX hSyl
    (normal_of_threeExtraspecial hyp (h36 _ hyp) (h37 _ hyp) (h38 _ hyp) hO3 hOA hX27
      (exp_bar_of_sylow hX hp2 hpX hSyl) hcardb (P134.sylow_bar hS) hNT hNP hirr
      (mul_bar_of_sylow hS hXH hX hp2 hpX hSyl) (sup_bar_of_sylow hS hXH hX hp2 hpX hSyl)
      (oX_bar_of_sylow hXH hX hp2 hpX hSyl) (comm_bar_of_sylow hS hXH hX hp2 hpX hSyl))

end CFSG.Quasithin.H13.NQCore
