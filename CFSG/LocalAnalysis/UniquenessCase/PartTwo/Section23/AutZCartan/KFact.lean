module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsRootModule
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Defs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23a.Holds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.AutZCartan.TorusSL
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.AutZCartan.TorusSp
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.AutZCartan.TorusOmega
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.AutZCartan.TorusSU
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.SylowLine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.FixedLineSL
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.FixedLineOmega
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.FixedLineSp
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KGen.SUFixedLine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KGenO6p.FixedLine

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.AutZC

open CFSG.Open CFSG.Quasithin
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

private lemma eq_of_mem_of_card_eq_two_pow {G : Type} [Group G] [Finite G] {ℓ : Subgroup G}
    {n : ℕ} (hcard : Nat.card ℓ = 2 ^ n) (hn : n ≤ 1) {v w : G} (hv : v ∈ ℓ) (hw : w ∈ ℓ)
    (hv1 : v ≠ 1) (hw1 : w ≠ 1) : v = w := by
  have hne : Nat.card ℓ ≠ 1 := by
    intro h1
    have hbot : ℓ = ⊥ := Subgroup.card_eq_one.mp h1
    rw [hbot] at hv
    exact hv1 (Subgroup.mem_bot.mp hv)
  have hn1 : n = 1 := by
    rcases n with _ | m
    · simp only [pow_zero] at hcard
      exact absurd hcard hne
    · omega
  have h2 : Nat.card ℓ = 2 := by
    rw [hn1] at hcard
    simpa using hcard
  obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : ℓ)).mp h2
  have hv' : (⟨v, hv⟩ : ℓ) ≠ 1 := fun hc => hv1 (congrArg Subtype.val hc)
  have hw' : (⟨w, hw⟩ : ℓ) ≠ 1 := fun hc => hw1 (congrArg Subtype.val hc)
  exact congrArg Subtype.val ((huniq ⟨v, hv⟩ hv').trans (huniq ⟨w, hw⟩ hw').symm)

private lemma lineTransitive_of_card_le_two {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {n : ℕ} (S : Sylow 2 ↥H)
    (hcard : letI : MulDistribMulAction ↥S W :=
      MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
      Nat.card (CFSG.fixedPointSubgroup ↥S W) = 2 ^ n) (hn : n ≤ 1) :
    letI : MulDistribMulAction ↥S W :=
      MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
    ∃ h ∈ KTabD.pointStab H S, ∀ v ∈ CFSG.fixedPointSubgroup ↥S W,
      ∀ w ∈ CFSG.fixedPointSubgroup ↥S W, v ≠ 1 → w ≠ 1 →
        ∃ k : ℤ, ((h ^ k : ↥H) : MulAut W) v = w := by
  refine ⟨1, Subgroup.one_mem _, ?_⟩
  intro v hv w hw hv1 hw1
  refine ⟨0, ?_⟩
  have hvw : v = w := eq_of_mem_of_card_eq_two_pow hcard hn hv hw hv1 hw1
  rw [hvw]
  simp

private lemma lineTransitive_of_binaryNaturalSL {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {n d : ℕ} (hd : 2 ≤ d)
    (h : BinaryNaturalSL H ⊤ ⊥ d n) (S : Sylow 2 ↥H) :
    letI : MulDistribMulAction ↥S W :=
      MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
    ∃ h ∈ KTabD.pointStab H S, ∀ v ∈ CFSG.fixedPointSubgroup ↥S W,
      ∀ w ∈ CFSG.fixedPointSubgroup ↥S W, v ≠ 1 → w ≠ 1 →
        ∃ k : ℤ, ((h ^ k : ↥H) : MulAut W) v = w := by
  obtain ⟨K, hField, hFinite, hK, hR⟩ := h
  letI : Field K := hField
  letI : Finite K := hFinite
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  haveI : NeZero d := ⟨by omega⟩
  exact exists_zpowers_transitive_of_lineTorus (K := K) hR
    (KTabD.sylowFixedLine_statedSL (K := K) hd) (lineTorus_statedSL (K := K) hd) S

private lemma lineTransitive_of_natSpn {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {n N : ℕ} (hN : 0 < N / 2)
    (h : NatSpn H ⊤ ⊥ N n) (S : Sylow 2 ↥H) :
    letI : MulDistribMulAction ↥S W :=
      MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
    ∃ h ∈ KTabD.pointStab H S, ∀ v ∈ CFSG.fixedPointSubgroup ↥S W,
      ∀ w ∈ CFSG.fixedPointSubgroup ↥S W, v ≠ 1 → w ≠ 1 →
        ∃ k : ℤ, ((h ^ k : ↥H) : MulAut W) v = w := by
  obtain ⟨-, K, hField, hFinite, hK, hR⟩ := h
  letI : Field K := hField
  letI : Finite K := hFinite
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  haveI : NeZero (N / 2) := ⟨by omega⟩
  exact exists_zpowers_transitive_of_lineTorus (K := K) hR
    (KTabD.sylowFixedLine_statedSp (K := K) (N / 2))
    (lineTorus_statedSp (K := K) (N / 2)) S

private lemma lineTransitive_of_natOmegaMinus {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {n N : ℕ} (hm : 2 ≤ N / 2)
    (h : NatOmegaMinus H ⊤ ⊥ N n) (S : Sylow 2 ↥H) :
    letI : MulDistribMulAction ↥S W :=
      MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
    ∃ h ∈ KTabD.pointStab H S, ∀ v ∈ CFSG.fixedPointSubgroup ↥S W,
      ∀ w ∈ CFSG.fixedPointSubgroup ↥S W, v ≠ 1 → w ≠ 1 →
        ∃ k : ℤ, ((h ^ k : ↥H) : MulAut W) v = w := by
  obtain ⟨-, K, hField, hFinite, b, c, hK, hirr, hR⟩ := h
  letI : Field K := hField
  letI : Finite K := hFinite
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  exact exists_zpowers_transitive_of_lineTorus (K := K) hR
    (KTabD.sylowFixedLine_omegaMinus (K := K) (m := N / 2) hm hirr)
    (lineTorus_omegaMinus (K := K) (m := N / 2) hm b c) S

private lemma lineTransitive_of_natOmegaPlusFour {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {n : ℕ} (hn : 2 ≤ n)
    (h : NatOmegaPlus H ⊤ ⊥ 4 n) (S : Sylow 2 ↥H) :
    letI : MulDistribMulAction ↥S W :=
      MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
    ∃ h ∈ KTabD.pointStab H S, ∀ v ∈ CFSG.fixedPointSubgroup ↥S W,
      ∀ w ∈ CFSG.fixedPointSubgroup ↥S W, v ≠ 1 → w ≠ 1 →
        ∃ k : ℤ, ((h ^ k : ↥H) : MulAut W) v = w := by
  obtain ⟨-, K, hField, hFinite, hK, hR⟩ := h
  letI : Field K := hField
  letI : Finite K := hFinite
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  rw [show 4 / 2 = 2 by norm_num] at hR
  exact exists_zpowers_transitive_of_lineTorus (K := K) hR
    (KTabC.sylowFixedLine_plus (K := K) hK4) (lineTorus_omegaPlus (K := K) 2) S

private lemma lineTransitive_of_natOmegaPlusSix {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {n : ℕ}
    (h : NatOmegaPlus H ⊤ ⊥ 6 n) (S : Sylow 2 ↥H) :
    letI : MulDistribMulAction ↥S W :=
      MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
    ∃ h ∈ KTabD.pointStab H S, ∀ v ∈ CFSG.fixedPointSubgroup ↥S W,
      ∀ w ∈ CFSG.fixedPointSubgroup ↥S W, v ≠ 1 → w ≠ 1 →
        ∃ k : ℤ, ((h ^ k : ↥H) : MulAut W) v = w := by
  obtain ⟨-, K, hField, hFinite, hK, hR⟩ := h
  letI : Field K := hField
  letI : Finite K := hFinite
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  rw [show 6 / 2 = 3 by norm_num] at hR
  exact exists_zpowers_transitive_of_lineTorus (K := K) hR
    (KGenO6pProof.sylowFixedLine_omegaPlusSix K) (lineTorus_omegaPlus (K := K) 3) S

private lemma lineTransitive_of_natSUn {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {a : ℕ} (h : NatSUn H ⊤ ⊥ 4 a) (S : Sylow 2 ↥H) :
    letI : MulDistribMulAction ↥S W :=
      MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
    ∃ h ∈ KTabD.pointStab H S, ∀ v ∈ CFSG.fixedPointSubgroup ↥S W,
      ∀ w ∈ CFSG.fixedPointSubgroup ↥S W, v ≠ 1 → w ≠ 1 →
        ∃ k : ℤ, ((h ^ k : ↥H) : MulAut W) v = w := by
  obtain ⟨K, hField, hFinite, hK, hR⟩ := h
  letI : Field K := hField
  letI : Finite K := hFinite
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq
    (hK.trans (pow_mul 2 a 2).symm)
  exact exists_zpowers_transitive_of_lineTorus (K := K) hR
    (KGenProof.sylowFixedLine_statedSU_four (K := K) hK)
    (lineTorus_statedSU_four (K := K) hK) S

theorem kLineTransitive_holds :
    ∀ (W : Type) [CommGroup W] [Finite W] (H : Subgroup (MulAut W)) (n : ℕ),
      IsNaturalClassicalModule H n → ⁅H, H⁆ = H → ∀ S : Sylow 2 ↥H,
        letI : MulDistribMulAction ↥S W :=
          MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
        ∃ h ∈ KTabD.pointStab H S, ∀ v ∈ CFSG.fixedPointSubgroup ↥S W,
          ∀ w ∈ CFSG.fixedPointSubgroup ↥S W, v ≠ 1 → w ≠ 1 →
            ∃ k : ℤ, ((h ^ k : ↥H) : MulAut W) v = w := by
  intro W _ _ H n hN hperf S
  obtain ⟨hcard, -, -⟩ := kTab23a_holds W H n hN hperf S
  by_cases hn : n ≤ 1
  · exact lineTransitive_of_card_le_two S hcard hn
  · have hn2 : 2 ≤ n := by omega
    rcases hN with h | h | h | h | h | h | h | h | h | h | h
    · exact lineTransitive_of_binaryNaturalSL (d := 2) (by norm_num) h.2 S
    · exact lineTransitive_of_natOmegaMinus (N := 4) (by norm_num) h.2 S
    · exact lineTransitive_of_natOmegaPlusFour hn2 h.2 S
    · exact lineTransitive_of_natSpn (N := 4) (by norm_num) h.2 S
    · exact lineTransitive_of_binaryNaturalSL (d := 3) (by norm_num) h.2 S
    · obtain ⟨a, -, -, hNat⟩ := h
      exact lineTransitive_of_natSUn hNat S
    · exact lineTransitive_of_natOmegaMinus (N := 6) (by norm_num) h.2 S
    · exact lineTransitive_of_binaryNaturalSL (d := 4) (by norm_num) h.2 S
    · exact lineTransitive_of_natOmegaPlusSix h.2 S
    · exact lineTransitive_of_natSpn (N := 6) (by norm_num) h.2 S
    · exact lineTransitive_of_natOmegaMinus (N := 8) (by norm_num) h.2 S

end CFSG.LocalAnalysis.UniquenessCase.UC22.AutZC
