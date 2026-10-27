module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsTwoThree
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatInvol.Transport
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatInvol.CommutantSU
import CFSG.RankThree.GF2n.Stroth80.Sec5NatScalarsPlusTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Quasithin
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

private theorem holds_of_binaryNaturalSL {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {n d : ℕ} (hd : 2 ≤ d) (h : BinaryNaturalSL H ⊤ ⊥ d n)
    {s : MulAut W} (hs : s ∈ Subgroup.normalizer (H : Set (MulAut W))) (hs1 : s ≠ 1) :
    n ≤ rkIdx (fixV (Subgroup.zpowers s)) := by
  obtain ⟨K, hField, hFinite, hK, hR⟩ := h
  letI : Field K := hField
  letI : Finite K := hFinite
  exact NatInvol.le_rkIdx_of_realizes hR
    (NatInvol.semilinearNormalizer_of_addCommutantScalar
      (CFSG.RankThree.GF2n.Stroth80.addCommutantScalar_statedSL hd))
    (by simpa using hd) hK hs hs1

private theorem holds_of_natSpn {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {n N : ℕ} (hN : 0 < N / 2) (h : NatSpn H ⊤ ⊥ N n)
    {s : MulAut W} (hs : s ∈ Subgroup.normalizer (H : Set (MulAut W))) (hs1 : s ≠ 1) :
    n ≤ rkIdx (fixV (Subgroup.zpowers s)) := by
  obtain ⟨-, K, hField, hFinite, hK, hR⟩ := h
  letI : Field K := hField
  letI : Finite K := hFinite
  exact NatInvol.le_rkIdx_of_realizes hR
    (NatInvol.semilinearNormalizer_of_addCommutantScalar
      CFSG.RankThree.GF2n.Stroth80.addCommutantScalar_statedSp)
    (by simp; omega) hK hs hs1

private theorem holds_of_natOmegaMinus {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {n N : ℕ} (hm : 2 ≤ N / 2) (h : NatOmegaMinus H ⊤ ⊥ N n)
    {s : MulAut W} (hs : s ∈ Subgroup.normalizer (H : Set (MulAut W))) (hs1 : s ≠ 1) :
    n ≤ rkIdx (fixV (Subgroup.zpowers s)) := by
  obtain ⟨-, K, hField, hFinite, b, c, hK, hirr, hR⟩ := h
  letI : Field K := hField
  letI : Finite K := hFinite
  exact NatInvol.le_rkIdx_of_realizes hR
    (NatInvol.semilinearNormalizer_of_addCommutantScalar
      (CFSG.RankThree.GF2n.Stroth80.addCommutantScalar_statedOmegaMinus hm hirr))
    (by simp; omega) hK hs hs1

private theorem holds_of_natOmegaPlusFour {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {n : ℕ} (h : NatOmegaPlus H ⊤ ⊥ 4 n)
    {s : MulAut W} (hs : s ∈ Subgroup.normalizer (H : Set (MulAut W))) (hs1 : s ≠ 1) :
    n ≤ rkIdx (fixV (Subgroup.zpowers s)) := by
  obtain ⟨-, K, hField, hFinite, hK, hR⟩ := h
  letI : Field K := hField
  letI : Finite K := hFinite
  rw [show 4 / 2 = 2 by norm_num] at hR
  have hsemi : NatInvol.SemilinearNormalizer (StatedOmega (StatedQuadPlus 2 K)) := by
    by_cases hK2 : Nat.card K = 2
    · exact NatInvol.semilinearNormalizer_of_card_eq_two hK2 _
    · refine NatInvol.semilinearNormalizer_of_addCommutantScalar
        (CFSG.RankThree.GF2n.Stroth80.addCommutantScalar_statedOmegaPlus_two ?_)
      classical
      by_contra hno
      push Not at hno
      haveI : Fintype K := Fintype.ofFinite K
      have hsub : (Finset.univ : Finset K) ⊆ {0, 1} := by
        intro c _
        by_cases hc : c = 0
        · simp [hc]
        · simp [hno c hc]
      have hle := Finset.card_le_card hsub
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at hle
      have h01 : ({0, 1} : Finset K).card ≤ 2 := Finset.card_le_two
      have h1 := Finite.one_lt_card (α := K)
      omega
  exact NatInvol.le_rkIdx_of_realizes hR hsemi (by simp) hK hs hs1

private theorem holds_of_natOmegaPlusSix {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {n : ℕ} (h : NatOmegaPlus H ⊤ ⊥ 6 n)
    {s : MulAut W} (hs : s ∈ Subgroup.normalizer (H : Set (MulAut W))) (hs1 : s ≠ 1) :
    n ≤ rkIdx (fixV (Subgroup.zpowers s)) := by
  obtain ⟨-, K, hField, hFinite, hK, hR⟩ := h
  letI : Field K := hField
  letI : Finite K := hFinite
  rw [show 6 / 2 = 3 by norm_num] at hR
  exact NatInvol.le_rkIdx_of_realizes hR
    (NatInvol.semilinearNormalizer_of_addCommutantScalar
      (CFSG.RankThree.GF2n.Stroth80.addCommutantScalar_statedOmegaPlus (m := 3) le_rfl))
    (by simp) hK hs hs1

private theorem holds_of_natSUn {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {a : ℕ} (h : NatSUn H ⊤ ⊥ 4 a)
    {s : MulAut W} (hs : s ∈ Subgroup.normalizer (H : Set (MulAut W))) (hs1 : s ≠ 1) :
    2 * a ≤ rkIdx (fixV (Subgroup.zpowers s)) := by
  obtain ⟨K, hField, hFinite, hK, hR⟩ := h
  letI : Field K := hField
  letI : Finite K := hFinite
  haveI : CharP K 2 :=
    CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq (hK.trans (pow_mul 2 a 2).symm)
  have hK' : Nat.card K = 2 ^ (2 * a) := by rw [hK, ← pow_mul, mul_comm]
  exact NatInvol.le_rkIdx_of_realizes hR
    (NatInvol.semilinearNormalizer_of_addCommutantScalar
      (NatInvol.addCommutantScalar_statedSU_four hK))
    (by simp) hK' hs hs1

theorem kNatInvol_holds : KNatInvol := by
  intro W _ _ H k s hN hs hord _
  have hs1 : s ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hord
    exact absurd hord (by norm_num)
  rcases hN with h | h | h | h | h | h | h | h | h | h | h
  · exact holds_of_binaryNaturalSL (d := 2) (by norm_num) h.2 hs hs1
  · exact holds_of_natOmegaMinus (N := 4) (by norm_num) h.2 hs hs1
  · exact holds_of_natOmegaPlusFour h.2 hs hs1
  · exact holds_of_natSpn (N := 4) (by norm_num) h.2 hs hs1
  · exact holds_of_binaryNaturalSL (d := 3) (by norm_num) h.2 hs hs1
  · obtain ⟨a, rfl, -, hNat⟩ := h
    exact holds_of_natSUn hNat hs hs1
  · exact holds_of_natOmegaMinus (N := 6) (by norm_num) h.2 hs hs1
  · exact holds_of_binaryNaturalSL (d := 4) (by norm_num) h.2 hs hs1
  · exact holds_of_natOmegaPlusSix h.2 hs hs1
  · exact holds_of_natSpn (N := 6) (by norm_num) h.2 hs hs1
  · exact holds_of_natOmegaMinus (N := 8) (by norm_num) h.2 hs hs1

end CFSG.LocalAnalysis.UniquenessCase.UC22
