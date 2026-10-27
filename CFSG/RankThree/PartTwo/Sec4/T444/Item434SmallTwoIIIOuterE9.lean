module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434Kit
import CFSG.RankThree.PartTwo.Source.GammaTwoSubgroups

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII

open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

theorem exists_map_conj_le_of_card_27 {X : Type*} [Group X] [Finite X]
    (hZ : Subgroup.center X = ⊥) (hO : Nat.card (Outer X) < 9)
    {N : Subgroup (MulAut X)} (hN : CFSG.Assembly.IsElemAbelian 3 N) (hN27 : Nat.card N = 27) :
    ∃ E : Subgroup X, CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
      E.map (MulAut.conj : X →* MulAut X) ≤ N := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (MulAut X) := MulEquiv.finite_left
  have hinj := Item434Kit.conj_injective_of_center_eq_bot hZ
  set q : MulAut X →* Outer X := QuotientGroup.mk' (inner X) with hq
  have h1 := Item434Alt.card_eq_card_inf_ker_mul_card_map q N
  have hker : q.ker = (MulAut.conj : X →* MulAut X).range := QuotientGroup.ker_mk' _
  have hle : Nat.card (N.map q) < 9 := (Subgroup.card_le_card_group _).trans_lt hO
  have hpos : 0 < Nat.card (N.map q) := Nat.card_pos
  have h9 : 9 ∣ Nat.card (N ⊓ q.ker : Subgroup _) := by
    rw [hN27] at h1
    generalize Nat.card (N.map q) = a at h1 hle hpos
    generalize Nat.card (N ⊓ q.ker : Subgroup _) = b at h1 ⊢
    interval_cases a <;> omega
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 3 (G := ↥(N ⊓ q.ker)) (n := 2)
    (by simpa using h9)
  set B : Subgroup (MulAut X) := K.map (N ⊓ q.ker).subtype with hB
  have hBle : B ≤ N ⊓ q.ker := Subgroup.map_subtype_le K
  have hBN : B ≤ N := hBle.trans inf_le_left
  have hBcard : Nat.card B = 9 := by
    rw [hB, Subgroup.card_map_of_injective (N ⊓ q.ker).subtype_injective, hK]
    norm_num
  have hBinn : B ≤ (MulAut.conj : X →* MulAut X).range := by
    rw [← hker]
    exact hBle.trans inf_le_right
  have hBmap : (B.comap (MulAut.conj : X →* MulAut X)).map MulAut.conj = B :=
    Subgroup.map_comap_eq_self hBinn
  refine ⟨B.comap MulAut.conj, ?_, ?_, by rw [hBmap]; exact hBN⟩
  · refine Item434Kit.isElemAbelian_of_map_injective hinj ?_
    rw [hBmap]
    exact CFSG.RankThree.PartTwo.Source.isElemAbelian_of_le hN hBN
  · rw [← Subgroup.card_map_of_injective hinj, hBmap, hBcard]

end CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII
