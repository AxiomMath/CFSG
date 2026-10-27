module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsFiveK
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23a.Glue
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23a.Stab
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23a.Perfect
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23a.PlusTwoNotPerfect
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23a.LineSL
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23a.LineSp
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23a.LineSU
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23a.LinePlus
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23a.LinePlusTwo
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23a.LineMinus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Quasithin
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Matrix Pointwise commutatorElement

private theorem charP_two_of_card_eq_two_pow {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) : CharP K 2 := by
  letI := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card] at hK
  exact charP_of_card_eq_prime_pow hK

private theorem card_fixedPointSubgroup_eq_two_pow_of_realizes {W : Type} [CommGroup W]
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] {K : Type} [Field K] [Finite K]
    {n : ℕ} (hK : Nat.card K = 2 ^ n) {Γ : Subgroup (GL ι K)}
    {H : Subgroup (MulAut W)} (hR : (FFModel.nat Γ).Realizes H ⊤ ⊥)
    (hline : ∃ (U : Subgroup ↥Γ) (e : ι → K), IsPGroup 2 ↥U ∧
      ∀ v : ι → K, (∀ u ∈ U, ((u : GL ι K) : Matrix ι ι K) *ᵥ v = v) →
        v ∈ Submodule.span K {e})
    (S : Sylow 2 ↥H) :
    letI : MulDistribMulAction ↥S W :=
      MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
    Nat.card (CFSG.fixedPointSubgroup ↥S W) = 2 ^ n := by
  haveI : CharP K 2 := charP_two_of_card_eq_two_pow hK
  have h := KTabA.card_fixedPointSubgroup_sylow_of_realizes (W := W) (p := 2) (K := K)
    hR hline S
  rw [h, hK]

private theorem card_fixedPoint_of_binaryNaturalSL {W : Type} [CommGroup W]
    {H : Subgroup (MulAut W)} {n d : ℕ} (hd : 0 < d)
    (h : BinaryNaturalSL H ⊤ ⊥ d n) (S : Sylow 2 ↥H) :
    letI : MulDistribMulAction ↥S W :=
      MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
    Nat.card (CFSG.fixedPointSubgroup ↥S W) = 2 ^ n := by
  obtain ⟨K, hField, hFinite, hK, hR⟩ := h
  letI : Field K := hField
  letI : Finite K := hFinite
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  haveI : CharP K 2 := charP_two_of_card_eq_two_pow hK
  obtain ⟨U, e, hU, hfix⟩ := KTabA.exists_fixedLine_statedSL (K := K) 2 d
  exact card_fixedPointSubgroup_eq_two_pow_of_realizes hK hR ⟨U, e, hU, hfix⟩ S

private theorem card_fixedPoint_of_natSpn {W : Type} [CommGroup W]
    {H : Subgroup (MulAut W)} {n N : ℕ} (hN : 0 < N / 2)
    (h : NatSpn H ⊤ ⊥ N n) (S : Sylow 2 ↥H) :
    letI : MulDistribMulAction ↥S W :=
      MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
    Nat.card (CFSG.fixedPointSubgroup ↥S W) = 2 ^ n := by
  obtain ⟨-, K, hField, hFinite, hK, hR⟩ := h
  letI : Field K := hField
  letI : Finite K := hFinite
  haveI : Nonempty (Fin (N / 2)) := Fin.pos_iff_nonempty.mp hN
  haveI : CharP K 2 := charP_two_of_card_eq_two_pow hK
  obtain ⟨U, e, hU, hfix⟩ := KTabA.exists_fixedLine_statedSp (K := K) 2 (N / 2)
  exact card_fixedPointSubgroup_eq_two_pow_of_realizes hK hR ⟨U, e, hU, hfix⟩ S

private theorem card_fixedPoint_of_natOmegaMinus {W : Type} [CommGroup W]
    {H : Subgroup (MulAut W)} {n N : ℕ} (hN : 2 ≤ N / 2)
    (h : NatOmegaMinus H ⊤ ⊥ N n) (S : Sylow 2 ↥H) :
    letI : MulDistribMulAction ↥S W :=
      MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
    Nat.card (CFSG.fixedPointSubgroup ↥S W) = 2 ^ n := by
  obtain ⟨-, K, hField, hFinite, b, c, hK, hbc, hR⟩ := h
  letI : Field K := hField
  letI : Finite K := hFinite
  haveI : Nonempty (Fin 2) := Fin.pos_iff_nonempty.mp (by norm_num)
  haveI : CharP K 2 := charP_two_of_card_eq_two_pow hK
  obtain ⟨U, e, hU, hfix⟩ :=
    KTabA.exists_fixedLine_statedOmega_minus (K := K) (m := N / 2) hN hbc
  exact card_fixedPointSubgroup_eq_two_pow_of_realizes hK hR ⟨U, e, hU, hfix⟩ S

private theorem card_fixedPoint_of_natOmegaPlus {W : Type} [CommGroup W]
    {H : Subgroup (MulAut W)} {n N : ℕ} (hN : 3 ≤ N / 2)
    (h : NatOmegaPlus H ⊤ ⊥ N n) (S : Sylow 2 ↥H) :
    letI : MulDistribMulAction ↥S W :=
      MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
    Nat.card (CFSG.fixedPointSubgroup ↥S W) = 2 ^ n := by
  obtain ⟨-, K, hField, hFinite, hK, hR⟩ := h
  letI : Field K := hField
  letI : Finite K := hFinite
  haveI : Nonempty (Fin (N / 2)) := Fin.pos_iff_nonempty.mp (lt_of_lt_of_le (by norm_num) hN)
  haveI : CharP K 2 := charP_two_of_card_eq_two_pow hK
  obtain ⟨U, e, hU, hfix⟩ := KTabA.exists_fixedLine_statedOmega_plus (K := K) 2 hN
  exact card_fixedPointSubgroup_eq_two_pow_of_realizes hK hR ⟨U, e, hU, hfix⟩ S

private theorem card_fixedPoint_of_natOmegaPlusFour {W : Type} [CommGroup W]
    {H : Subgroup (MulAut W)} {n : ℕ} (h : NatOmegaPlus H ⊤ ⊥ 4 n)
    (hperf : ⁅H, H⁆ = H) (S : Sylow 2 ↥H) :
    letI : MulDistribMulAction ↥S W :=
      MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
    Nat.card (CFSG.fixedPointSubgroup ↥S W) = 2 ^ n := by
  obtain ⟨-, K, hField, hFinite, hK, hR⟩ := h
  letI : Field K := hField
  letI : Finite K := hFinite
  haveI : Nonempty (Fin 2) := Fin.pos_iff_nonempty.mp (by norm_num)
  haveI : CharP K 2 := charP_two_of_card_eq_two_pow hK
  by_cases hK2 : 2 < Nat.card K
  · obtain ⟨U, e, hU, hfix⟩ := KTabA.exists_fixedLine_statedOmega_plus_two (K := K) 2 hK2
    exact card_fixedPointSubgroup_eq_two_pow_of_realizes hK hR ⟨U, e, hU, hfix⟩ S
  · have hKge : 2 ≤ Nat.card K := by
      have := Finite.one_lt_card (α := K)
      omega
    have hKeq : Nat.card K = 2 := le_antisymm (not_lt.mp hK2) hKge
    have htop : commutator ↥(StatedOmega (StatedQuadPlus 2 K)) = ⊤ :=
      KTabA.commutator_eq_top_of_realizes hR hperf
    exact absurd htop (KTabA.commutator_statedOmega_plus_two_ne_top hKeq)

private theorem card_fixedPoint_of_natSUn {W : Type} [CommGroup W]
    {H : Subgroup (MulAut W)} {n a : ℕ} (hn : n = 2 * a)
    (h : NatSUn H ⊤ ⊥ 4 a) (S : Sylow 2 ↥H) :
    letI : MulDistribMulAction ↥S W :=
      MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
    Nat.card (CFSG.fixedPointSubgroup ↥S W) = 2 ^ n := by
  obtain ⟨K, hField, hFinite, hK, hR⟩ := h
  letI : Field K := hField
  letI : Finite K := hFinite
  haveI : Nonempty (Fin 4) := Fin.pos_iff_nonempty.mp (by norm_num)
  have hK' : Nat.card K = 2 ^ n := by rw [hn, hK, ← pow_mul, Nat.mul_comm a 2]
  haveI : CharP K 2 := charP_two_of_card_eq_two_pow hK'
  obtain ⟨U, e, hU, hfix⟩ := KTabA.exists_fixedLine_statedSU (K := K) (r := 2 ^ a) (d := 4) hK
  exact card_fixedPointSubgroup_eq_two_pow_of_realizes hK' hR ⟨U, e, hU, hfix⟩ S

private theorem card_fixedPoint_eq_two_pow {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {n : ℕ} (hN : IsNaturalClassicalModule H n) (hperf : ⁅H, H⁆ = H) (S : Sylow 2 ↥H) :
    letI : MulDistribMulAction ↥S W :=
      MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
    Nat.card (CFSG.fixedPointSubgroup ↥S W) = 2 ^ n := by
  rcases hN with h | h | h | h | h | h | h | h | h | h | h
  · exact card_fixedPoint_of_binaryNaturalSL (d := 2) (by norm_num) h.2 S
  · exact card_fixedPoint_of_natOmegaMinus (N := 4) (by norm_num) h.2 S
  · exact card_fixedPoint_of_natOmegaPlusFour h.2 hperf S
  · exact card_fixedPoint_of_natSpn (N := 4) (by norm_num) h.2 S
  · exact card_fixedPoint_of_binaryNaturalSL (d := 3) (by norm_num) h.2 S
  · obtain ⟨a, hn, -, hNat⟩ := h
    exact card_fixedPoint_of_natSUn hn hNat S
  · exact card_fixedPoint_of_natOmegaMinus (N := 6) (by norm_num) h.2 S
  · exact card_fixedPoint_of_binaryNaturalSL (d := 4) (by norm_num) h.2 S
  · exact card_fixedPoint_of_natOmegaPlus (N := 6) (by norm_num) h.2 S
  · exact card_fixedPoint_of_natSpn (N := 6) (by norm_num) h.2 S
  · exact card_fixedPoint_of_natOmegaMinus (N := 8) (by norm_num) h.2 S

theorem kTab23a_holds : KTab23a := by
  intro W hWc hWf H n hN hperf S
  have hStab := KTabA.normalizer_le_stabilizer_fixedPointSubgroup H (S : Subgroup ↥H)
  exact ⟨card_fixedPoint_eq_two_pow hN hperf S, ⟨S, hStab⟩,
    (S : Subgroup ↥H).le_normalizer.trans hStab⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
