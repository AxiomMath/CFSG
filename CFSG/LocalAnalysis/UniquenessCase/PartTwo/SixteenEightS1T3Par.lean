module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3ParA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3ParB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3ParC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3ParD
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3ParE

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W] {A L T : Subgroup (MulAut W)}

@[expose] def T3Parab (L T : Subgroup (MulAut W)) (a : ℕ) : Prop :=
  ∃ J : Subgroup (MulAut W), T ≤ J ∧ J ≤ L ⊔ T ∧ Nat.card ↥J = 3 ^ a * Nat.card ↥T ∧
    ∀ x ∈ J, ∀ n : ℕ, x ^ 3 ^ n = 1 → x ^ 3 = 1

theorem T3Parab.of_normalized (h : ThreeNat A L T) {P : Subgroup (MulAut W)} {a : ℕ}
    (hPL : P ≤ L) (hTP : ∀ t ∈ T, ∀ x ∈ P, t * x * t⁻¹ ∈ P) (hTL : T ⊓ L ≤ P)
    (hcard : Nat.card ↥P = 3 ^ a * Nat.card ↥(T ⊓ L))
    (hexp : ∀ x ∈ P, ∀ n : ℕ, x ^ 3 ^ n = 1 → x ^ 3 = 1) : T3Parab L T a := by
  have hTnorm : T ≤ Subgroup.normalizer (P : Set (MulAut W)) := by
    intro t ht
    rw [Subgroup.mem_set_normalizer_iff]
    intro n
    constructor
    · intro hn
      exact hTP t ht n hn
    · intro hn
      have h1 := hTP t⁻¹ (T.inv_mem ht) (t * n * t⁻¹) hn
      have h2 : t⁻¹ * (t * n * t⁻¹) * t = n := by group
      simpa [h2] using h1
  have hInf : T ⊓ P = T ⊓ L :=
    le_antisymm (inf_le_inf_left T hPL) (le_inf inf_le_left hTL)
  have hcardJ : Nat.card (T ⊔ P : Subgroup (MulAut W)) = 3 ^ a * Nat.card ↥T := by
    haveI : (P.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hTnorm
    haveI : (P.subgroupOf (T ⊔ P)).Normal :=
      Subgroup.normal_subgroupOf_sup_of_le_normalizer hTnorm
    have hformula : Nat.card (T ⊔ P : Subgroup (MulAut W)) *
        Nat.card (T ⊓ P : Subgroup (MulAut W)) = Nat.card ↥T * Nat.card ↥P := by
      have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient T P hTnorm
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (P.subgroupOf T)
      have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (P.subgroupOf (T ⊔ P))
      have h3 : Nat.card (P.subgroupOf T) = Nat.card (T ⊓ P : Subgroup (MulAut W)) := by
        rw [← Subgroup.card_map_of_injective T.subtype_injective,
          Subgroup.subgroupOf_map_subtype, inf_comm]
      have h4 : Nat.card (P.subgroupOf (T ⊔ P)) = Nat.card ↥P :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
      rw [h2, h4, h1, h3, Nat.card_congr e.toEquiv]
      ring
    have h' : Nat.card (T ⊔ P : Subgroup (MulAut W)) *
        Nat.card (T ⊓ L : Subgroup (MulAut W)) =
        (3 ^ a * Nat.card ↥T) * Nat.card (T ⊓ L : Subgroup (MulAut W)) := by
      rw [← hInf, hformula, hcard, hInf]
      ring
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h'
  refine ⟨T ⊔ P, le_sup_left, sup_le le_sup_right (hPL.trans le_sup_left), hcardJ, ?_⟩
  intro x hxJ n hxn
  have hxP : x ∈ P := by
    let J : Subgroup (MulAut W) := T ⊔ P
    haveI : (P.subgroupOf J).Normal :=
      Subgroup.normal_subgroupOf_sup_of_le_normalizer hTnorm
    let q : ↥J →* J ⧸ P.subgroupOf J := QuotientGroup.mk' (P.subgroupOf J)
    let xJ : ↥J := ⟨x, hxJ⟩
    have hq3 : q xJ ^ 3 ^ n = 1 := by
      rw [← map_pow]
      rw [show xJ ^ 3 ^ n = 1 from Subtype.ext (by simpa using hxn), map_one]
    have hqJ : IsPGroup 2 (J ⧸ P.subgroupOf J) := by
      haveI : (P.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hTnorm
      exact (h.sylow.isPGroup.to_quotient (P.subgroupOf T)).of_equiv
        (QuotientGroup.quotientInfEquivProdNormalizerQuotient T P hTnorm)
    obtain ⟨k, hk⟩ := hqJ (q xJ)
    have hcop : Nat.gcd (2 ^ k) (3 ^ n) = 1 := (by decide : Nat.Coprime 2 3).pow k n
    have hd : orderOf (q xJ) ∣ Nat.gcd (2 ^ k) (3 ^ n) :=
      Nat.dvd_gcd (orderOf_dvd_iff_pow_eq_one.mpr hk)
        (orderOf_dvd_iff_pow_eq_one.mpr hq3)
    rw [hcop] at hd
    have hq1 : q xJ = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)
    have hmem : xJ ∈ P.subgroupOf J := (QuotientGroup.eq_one_iff xJ).mp hq1
    simpa [Subgroup.mem_subgroupOf] using hmem
  exact hexp x hxP n hxn

theorem ThreeNat.parab_sl (h : ThreeNat A L T) {n : ℕ} (hn : 4 ≤ n) (hsl : IsSLn ↥L n 1)
    {I : Subgroup W} (hTI : StableUnder T I)
    (hnat : SumOfNat (fun H U Z => BinaryNaturalSL H U Z n 1) L I (I ⊓ fixV L) 1) :
    T3Parab L T (n / 2) := by
  obtain ⟨P, hPL, hTP, hTL, hcard, hexp⟩ := s16t3_exists_parab_sl h hn hsl hTI hnat
  exact T3Parab.of_normalized h hPL hTP hTL hcard hexp

theorem ThreeNat.parab_sp (h : ThreeNat A L T) {n : ℕ} (hn : 6 ≤ n) (hsp : IsSpn ↥L n 1)
    {I : Subgroup W} (hTI : StableUnder T I)
    (hnat : SumOfNat (fun H U Z => NatSpn H U Z n 1) L I (I ⊓ fixV L) 1) :
    T3Parab L T ((n + 2) / 4) := by
  obtain ⟨P, hPL, hTP, hTL, hcard, hexp⟩ := s16t3_exists_parab_sp h hn hsp hTI hnat
  exact T3Parab.of_normalized h hPL hTP hTL hcard hexp

theorem ThreeNat.parab_omegaPlus (h : ThreeNat A L T) {n : ℕ} (hn : 6 ≤ n)
    (hom : IsOmegaPlus ↥L n 1) {I : Subgroup W} (hTI : StableUnder T I)
    (hnat : SumOfNat (fun H U Z => NatOmegaPlus H U Z n 1) L I (I ⊓ fixV L) 1) :
    T3Parab L T ((n + 4) / 4) := by
  obtain ⟨P, hPL, hTP, hTL, hcard, hexp⟩ := s16t3_exists_parab_omegaPlus h hn hom hTI hnat
  exact T3Parab.of_normalized h hPL hTP hTL hcard hexp

theorem ThreeNat.parab_omegaMinus (h : ThreeNat A L T) {n : ℕ} (hn : 6 ≤ n)
    (hom : IsOmegaMinus ↥L n 1) {I : Subgroup W} (hTI : StableUnder T I)
    (hnat : SumOfNat (fun H U Z => NatOmegaMinus H U Z n 1) L I (I ⊓ fixV L) 1) :
    T3Parab L T ((n + 2) / 4) := by
  obtain ⟨P, hPL, hTP, hTL, hcard, hexp⟩ := s16t3_exists_parab_omegaMinus h hn hom hTI hnat
  exact T3Parab.of_normalized h hPL hTP hTL hcard hexp

theorem ThreeNat.parab_alt (h : ThreeNat A L T) {n : ℕ} (hn : 8 ≤ n) (halt : UC22.IsAlt ↥L n)
    {I : Subgroup W} (hTI : StableUnder T I)
    (hnat : SumOfNat (fun H U Z => AlternatingNatural H U Z n) L I (I ⊓ fixV L) 1) :
    T3Parab L T ((n + 1) / 4) := by
  obtain ⟨P, hPL, hTP, hTL, hcard, hexp⟩ := s16t3_exists_parab_alt h hn halt hTI hnat
  exact T3Parab.of_normalized h hPL hTP hTL hcard hexp

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
