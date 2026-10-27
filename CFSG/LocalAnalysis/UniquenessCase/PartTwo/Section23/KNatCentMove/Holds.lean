module

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatCentMove.Linear
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatCentMove.Omega
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatCentMove.Unitary
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23a.Perfect
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23a.PlusTwoNotPerfect
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.SylowLine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.FixedLineSL
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.FixedLineOmega
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.FixedLineSp
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KGen.SUFixedLine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KGenO6p.FixedLine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsRootModule

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Quasithin
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

private theorem holds_of_binaryNaturalSL {W : Type} [CommGroup W] [Finite W]
    {H S : Subgroup (MulAut W)} {n d : ℕ} (hd : 2 ≤ d)
    (h : BinaryNaturalSL H ⊤ ⊥ d n) (hS : IsSylowIn 2 S H) {v : W} (hv1 : v ≠ 1)
    (hvS : v ∉ fixV S) : ∃ h ∈ H, h v = v ∧ h ∉ stabSub (fixV S) := by
  obtain ⟨K, hField, hFinite, hK, hR⟩ := h
  letI : Field K := hField
  letI : Finite K := hFinite
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  haveI : NeZero d := ⟨by omega⟩
  have he0 : (Pi.single 0 1 : Fin d → K) ≠ 0 := by
    intro h0
    have h1 : (1 : K) = 0 := by simpa using congr_fun h0 0
    exact one_ne_zero h1
  exact NatCentMove.exists_fix_notMem_stabSub (K := K) (ι := Fin d) hR
    (KTabD.sylowFixedLine_statedSL (K := K) hd)
    (NatCentMove.centMove_statedSL (K := K) he0) hS hv1 hvS

private theorem holds_of_natSpn {W : Type} [CommGroup W] [Finite W]
    {H S : Subgroup (MulAut W)} {n N : ℕ} (hN : 0 < N / 2)
    (h : NatSpn H ⊤ ⊥ N n) (hS : IsSylowIn 2 S H) {v : W} (hv1 : v ≠ 1)
    (hvS : v ∉ fixV S) : ∃ h ∈ H, h v = v ∧ h ∉ stabSub (fixV S) := by
  obtain ⟨-, K, hField, hFinite, hK, hR⟩ := h
  letI : Field K := hField
  letI : Finite K := hFinite
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  haveI : NeZero (N / 2) := ⟨by omega⟩
  have he0 : (Pi.single (Sum.inl 0) 1 : Fin (N / 2) ⊕ Fin (N / 2) → K) ≠ 0 := by
    intro h0
    have h1 : (1 : K) = 0 := by simpa using congr_fun h0 (Sum.inl 0)
    exact one_ne_zero h1
  exact NatCentMove.exists_fix_notMem_stabSub (K := K) hR
    (KTabD.sylowFixedLine_statedSp (K := K) (N / 2))
    (NatCentMove.centMove_statedSp (K := K) (N / 2) he0) hS hv1 hvS

private theorem holds_of_natOmegaMinus {W : Type} [CommGroup W] [Finite W]
    {H S : Subgroup (MulAut W)} {n N : ℕ} (hm : 2 ≤ N / 2)
    (h : NatOmegaMinus H ⊤ ⊥ N n) (hS : IsSylowIn 2 S H) {v : W} (hv1 : v ≠ 1)
    (hvS : v ∉ fixV S) : ∃ h ∈ H, h v = v ∧ h ∉ stabSub (fixV S) := by
  obtain ⟨-, K, hField, hFinite, b, c, hK, hirr, hR⟩ := h
  letI : Field K := hField
  letI : Finite K := hFinite
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  obtain ⟨e, hline, he0, he⟩ :
      ∃ e : Fin (N / 2 - 1) ⊕ Fin (N / 2 - 1) ⊕ Fin 2 → K,
        KTabC.SylowFixedLine (StatedOmega (StatedQuadMinus (N / 2) K b c)) e ∧
          e ≠ 0 ∧ StatedQuadMinus (N / 2) K b c e = 0 := by
    refine ⟨Pi.single (Sum.inl (⟨0, by omega⟩ : Fin (N / 2 - 1))) 1,
      KTabD.sylowFixedLine_omegaMinus (K := K) (m := N / 2) hm hirr, ?_, ?_⟩
    · intro h0
      have h1 : (1 : K) = 0 := by
        simpa using congr_fun h0 (Sum.inl (⟨0, by omega⟩ : Fin (N / 2 - 1)))
      exact one_ne_zero h1
    · simp [StatedQuadMinus, CFSG.MatrixModel.minusQuadCore]
  exact NatCentMove.exists_fix_notMem_stabSub (K := K) hR hline
    (NatCentMove.centMove_statedOmega_minus (K := K) hm hirr he he0) hS hv1 hvS

private theorem holds_of_natOmegaPlusFour {W : Type} [CommGroup W] [Finite W]
    {H S : Subgroup (MulAut W)} {n : ℕ} (h : NatOmegaPlus H ⊤ ⊥ 4 n)
    (hperf : ⁅H, H⁆ = H) (hS : IsSylowIn 2 S H) {v : W} (hv1 : v ≠ 1)
    (hvS : v ∉ fixV S) : ∃ h ∈ H, h v = v ∧ h ∉ stabSub (fixV S) := by
  obtain ⟨-, K, hField, hFinite, hK, hR⟩ := h
  letI : Field K := hField
  letI : Finite K := hFinite
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  by_cases hK2 : 2 < Nat.card K
  · have hn2 : 2 ≤ n := by
      rcases n with _ | _ | k
      · rw [pow_zero] at hK
        omega
      · rw [pow_one] at hK
        omega
      · omega
    have hK4 : 4 ≤ Nat.card K := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
        _ = Nat.card K := hK.symm
    rw [show 4 / 2 = 2 by norm_num] at hR
    obtain ⟨e, hline, he0, he⟩ :
        ∃ e : Fin 2 ⊕ Fin 2 → K,
          KTabC.SylowFixedLine (StatedOmega (StatedQuadPlus 2 K)) e ∧ e ≠ 0 ∧
            StatedQuadPlus 2 K e = 0 := by
      refine ⟨KTabC.e1P K, KTabC.sylowFixedLine_plus (K := K) hK4, ?_, ?_⟩
      · simp [KTabC.e1P]
      · simp [KTabC.e1P, StatedQuadPlus, CFSG.MatrixModel.plusQuadCore, Fin.sum_univ_two]
    exact NatCentMove.exists_fix_notMem_stabSub (K := K) hR hline
      (NatCentMove.centMove_statedOmega_plus (K := K) (m := 2) (by norm_num) he he0)
      hS hv1 hvS
  · have hKge : 2 ≤ Nat.card K := by
      have := Finite.one_lt_card (α := K)
      omega
    have hKeq : Nat.card K = 2 := le_antisymm (not_lt.mp hK2) hKge
    rw [show 4 / 2 = 2 by norm_num] at hR
    have htop : commutator ↥(StatedOmega (StatedQuadPlus 2 K)) = ⊤ :=
      KTabA.commutator_eq_top_of_realizes hR hperf
    exact absurd htop (KTabA.commutator_statedOmega_plus_two_ne_top hKeq)

private theorem holds_of_natOmegaPlusSix {W : Type} [CommGroup W] [Finite W]
    {H S : Subgroup (MulAut W)} {n : ℕ} (h : NatOmegaPlus H ⊤ ⊥ 6 n)
    (hS : IsSylowIn 2 S H) {v : W} (hv1 : v ≠ 1) (hvS : v ∉ fixV S) :
    ∃ h ∈ H, h v = v ∧ h ∉ stabSub (fixV S) := by
  obtain ⟨-, K, hField, hFinite, hK, hR⟩ := h
  letI : Field K := hField
  letI : Finite K := hFinite
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  rw [show 6 / 2 = 3 by norm_num] at hR
  obtain ⟨e, hline, he0, he⟩ :
      ∃ e : Fin 3 ⊕ Fin 3 → K,
        KTabC.SylowFixedLine (StatedOmega (StatedQuadPlus 3 K)) e ∧ e ≠ 0 ∧
          StatedQuadPlus 3 K e = 0 := by
    refine ⟨Pi.single (Sum.inl 0) 1, KGenO6pProof.sylowFixedLine_omegaPlusSix K, ?_, ?_⟩
    · intro h0
      have h1 : (1 : K) = 0 := by simpa using congr_fun h0 (Sum.inl 0)
      exact one_ne_zero h1
    · simp [StatedQuadPlus, CFSG.MatrixModel.plusQuadCore]
  exact NatCentMove.exists_fix_notMem_stabSub (K := K) hR hline
    (NatCentMove.centMove_statedOmega_plus (K := K) (m := 3) (by norm_num) he he0)
    hS hv1 hvS

private theorem holds_of_natSUn {W : Type} [CommGroup W] [Finite W]
    {H S : Subgroup (MulAut W)} {a : ℕ} (h : NatSUn H ⊤ ⊥ 4 a)
    (hS : IsSylowIn 2 S H) {v : W} (hv1 : v ≠ 1) (hvS : v ∉ fixV S) :
    ∃ h ∈ H, h v = v ∧ h ∉ stabSub (fixV S) := by
  obtain ⟨K, hField, hFinite, hK, hR⟩ := h
  letI : Field K := hField
  letI : Finite K := hFinite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 :=
    CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq (hK.trans (pow_mul 2 a 2).symm)
  obtain ⟨e, hline, he0, he⟩ :
      ∃ e : Fin 4 → K,
        KTabC.SylowFixedLine (StatedSU 4 (2 ^ a) K) e ∧ e ≠ 0 ∧
          CFSG.ClassicalGroups.Unitary.herm (CFSG.LieType.BorelTits.unitaryInvolution K 2 a)
            e e = 0 := by
    refine ⟨(Pi.single 0 1 + Pi.single 1 1 : Fin 4 → K),
      KGenProof.sylowFixedLine_statedSU_four (K := K) hK, ?_, ?_⟩
    · intro h0
      have h1 : (1 : K) = 0 := by
        have := congr_fun h0 0
        simpa using this
      exact one_ne_zero h1
    · rw [CFSG.ClassicalGroups.Unitary.herm_def, Fin.sum_univ_four]
      simp [Pi.single_apply, map_one, CharTwo.add_self_eq_zero]
  exact NatCentMove.exists_fix_notMem_stabSub (K := K) hR hline
    (NatCentMove.centMove_statedSU (K := K) (p := 2) (f := a) hK (by norm_num) he he0)
    hS hv1 hvS

theorem kNatCentMove_holds :
    ∀ (W : Type) [CommGroup W] [Finite W] (H S : Subgroup (MulAut W)) (k : ℕ),
      IsNaturalClassicalModule H k → ⁅H, H⁆ = H → IsSylowIn 2 S H →
      ∀ v : W, v ≠ 1 → v ∉ fixV S → ∃ h ∈ H, h v = v ∧ h ∉ stabSub (fixV S) := by
  intro W _ _ H S k hN hperf hS v hv1 hvS
  rcases hN with h | h | h | h | h | h | h | h | h | h | h
  · exact holds_of_binaryNaturalSL (d := 2) (by norm_num) h.2 hS hv1 hvS
  · exact holds_of_natOmegaMinus (N := 4) (by norm_num) h.2 hS hv1 hvS
  · exact holds_of_natOmegaPlusFour h.2 hperf hS hv1 hvS
  · exact holds_of_natSpn (N := 4) (by norm_num) h.2 hS hv1 hvS
  · exact holds_of_binaryNaturalSL (d := 3) (by norm_num) h.2 hS hv1 hvS
  · obtain ⟨a, -, -, hNat⟩ := h
    exact holds_of_natSUn hNat hS hv1 hvS
  · exact holds_of_natOmegaMinus (N := 6) (by norm_num) h.2 hS hv1 hvS
  · exact holds_of_binaryNaturalSL (d := 4) (by norm_num) h.2 hS hv1 hvS
  · exact holds_of_natOmegaPlusSix h.2 hS hv1 hvS
  · exact holds_of_natSpn (N := 6) (by norm_num) h.2 hS hv1 hvS
  · exact holds_of_natOmegaMinus (N := 8) (by norm_num) h.2 hS hv1 hvS

end CFSG.LocalAnalysis.UniquenessCase.UC22
