module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsTwoThree
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatParMax.Transport
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatParMax.MaxSLSpSU
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatParMax.MaxOmegaMinus
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatParMax.MaxOmegaPlusSix
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatParMax.OmegaPlusFour
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.FixedLineSL
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.FixedLineOmega
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.FixedLineSp
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KGen.SUFixedLine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KGenO6p.FixedLine

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Quasithin
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

private theorem natParMax_of_natSpn_M10 {W : Type} [CommGroup W] [Finite W]
    {H S X : Subgroup (MulAut W)} {n N : ℕ} (hm : 2 ≤ N / 2)
    (h : NatSpn H ⊤ ⊥ N n) (hS : IsSylowIn 2 S H)
    (hXge : H ⊓ stabSub (fixV S) ≤ X) (hXlt : X < H) : X = H ⊓ stabSub (fixV S) := by
  obtain ⟨-, K, hField, hFinite, hK, hR⟩ := h
  letI : Field K := hField
  letI : Finite K := hFinite
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  haveI : NeZero (N / 2) := ⟨by omega⟩
  exact NatParMax.natParMax_of_realizes hR
    (KTabD.sylowFixedLine_statedSp (K := K) (N / 2))
    (NatParMax.lineStab_maximal_statedSp (m := N / 2) hm) hS hXge hXlt

private theorem natParMax_of_binaryNaturalSL_M10 {W : Type} [CommGroup W] [Finite W]
    {H S X : Subgroup (MulAut W)} {n d : ℕ} (hd : 2 ≤ d)
    (h : BinaryNaturalSL H ⊤ ⊥ d n) (hS : IsSylowIn 2 S H)
    (hXge : H ⊓ stabSub (fixV S) ≤ X) (hXlt : X < H) : X = H ⊓ stabSub (fixV S) := by
  obtain ⟨K, hField, hFinite, hK, hR⟩ := h
  letI : Field K := hField
  letI : Finite K := hFinite
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  haveI : NeZero d := ⟨by omega⟩
  exact NatParMax.natParMax_of_realizes hR
    (KTabD.sylowFixedLine_statedSL (K := K) hd)
    (NatParMax.lineStab_maximal_statedSL (k := d)) hS hXge hXlt

private theorem natParMax_of_natOmegaMinus_M10 {W : Type} [CommGroup W] [Finite W]
    {H S X : Subgroup (MulAut W)} {n N : ℕ} (hm : 3 ≤ N / 2)
    (h : NatOmegaMinus H ⊤ ⊥ N n) (hS : IsSylowIn 2 S H)
    (hXge : H ⊓ stabSub (fixV S) ≤ X) (hXlt : X < H) : X = H ⊓ stabSub (fixV S) := by
  obtain ⟨-, K, hField, hFinite, b, c, hK, hirr, hR⟩ := h
  letI : Field K := hField
  letI : Finite K := hFinite
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  exact NatParMax.natParMax_of_realizes hR
    (KTabD.sylowFixedLine_omegaMinus (K := K) (m := N / 2) (by omega) hirr)
    (NatParMax.lineStab_maximal_statedOmegaMinus (m := N / 2) hm hirr) hS hXge hXlt

private theorem natParMax_of_natOmegaPlusSix_M10 {W : Type} [CommGroup W] [Finite W]
    {H S X : Subgroup (MulAut W)} {n : ℕ}
    (h : NatOmegaPlus H ⊤ ⊥ 6 n) (hS : IsSylowIn 2 S H)
    (hXge : H ⊓ stabSub (fixV S) ≤ X) (hXlt : X < H) : X = H ⊓ stabSub (fixV S) := by
  obtain ⟨-, K, hField, hFinite, hK, hR⟩ := h
  letI : Field K := hField
  letI : Finite K := hFinite
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  rw [show 6 / 2 = 3 by norm_num] at hR
  exact NatParMax.natParMax_of_realizes hR
    (KGenO6pProof.sylowFixedLine_omegaPlusSix K)
    (NatParMax.lineStab_maximal_statedOmegaPlusSix (K := K)) hS hXge hXlt

private theorem natParMax_of_natSUn_M10 {W : Type} [CommGroup W] [Finite W]
    {H S X : Subgroup (MulAut W)} {a : ℕ} (h : NatSUn H ⊤ ⊥ 4 a) (hS : IsSylowIn 2 S H)
    (hXge : H ⊓ stabSub (fixV S) ≤ X) (hXlt : X < H) : X = H ⊓ stabSub (fixV S) := by
  obtain ⟨K, hField, hFinite, hK, hR⟩ := h
  letI : Field K := hField
  letI : Finite K := hFinite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 :=
    CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq (hK.trans (pow_mul 2 a 2).symm)
  exact NatParMax.natParMax_of_realizes hR
    (KGenProof.sylowFixedLine_statedSU_four (K := K) hK)
    (NatParMax.lineStab_maximal_statedSU_four (a := a) (K := K) hK) hS hXge hXlt

theorem kNatParMax_holds : KNatParMax := by
  intro W _ _ H R K S X k hN hperf hR hK hgen hS hRS hRX hXge hXlt
  rcases hN with h | h | h | h | h | h | h | h | h | h | h
  · exact NatParMax.natParMax_of_isL2 h.1 hS hXge hXlt
  · exact NatParMax.natParMax_of_isOmegaMinus_four h.1 hS hXge hXlt
  · exact NatParMax.natParMax_omegaPlusFour h.1 h.2 hperf hR hK hgen hS hRX hXge hXlt
  · exact natParMax_of_natSpn_M10 (N := 4) (by norm_num) h.2 hS hXge hXlt
  · exact natParMax_of_binaryNaturalSL_M10 (d := 3) (by norm_num) h.2 hS hXge hXlt
  · obtain ⟨a, -, -, hNat⟩ := h
    exact natParMax_of_natSUn_M10 hNat hS hXge hXlt
  · exact natParMax_of_natOmegaMinus_M10 (N := 6) (by norm_num) h.2 hS hXge hXlt
  · exact natParMax_of_binaryNaturalSL_M10 (d := 4) (by norm_num) h.2 hS hXge hXlt
  · exact natParMax_of_natOmegaPlusSix_M10 h.2 hS hXge hXlt
  · exact natParMax_of_natSpn_M10 (N := 6) (by norm_num) h.2 hS hXge hXlt
  · exact natParMax_of_natOmegaMinus_M10 (N := 8) (by norm_num) h.2 hS hXge hXlt

end CFSG.LocalAnalysis.UniquenessCase.UC22
