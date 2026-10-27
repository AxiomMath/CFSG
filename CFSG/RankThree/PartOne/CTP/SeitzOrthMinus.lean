module

public import CFSG.RankThree.PartOne.CTP.SeitzOrthKernel
public import CFSG.RankThree.PartOne.CTP.SeitzOrthCount
public import CFSG.RankThree.PartOne.KC.OrthogonalSplitPrimeGeneration
public import CFSG.ClassicalGroups.Orthogonal.Simple

public section

namespace CFSG.RankThree.PartOne.CTP

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical
open CFSG.RankThree.Classical2 (orthDerived)

theorem closure_centralizers_orthDerived_quadMinus_four {K : Type} [Field K] [Finite K]
    [CharP K 2] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (E : Subgroup (orthDerived (quadMinus 4 K b c)))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ p = 1)
    (hcard : Nat.card E = p ^ 2) :
    Subgroup.closure {h : orthDerived (quadMinus 4 K b c) |
      ∃ x ∈ E, x ≠ 1 ∧ h * x = x * h} = ⊤ := by
  classical
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hQ, hT⟩ := regular_quadMinus (n := 4) (K := K) (by norm_num) hirr
  have hchar : ringChar K = 2 := ringChar.eq K 2
  have hpl : p ≠ ringChar K := by rw [hchar]; exact hp2
  have : Nontrivial (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K) := inferInstance
  obtain ⟨hK, hlcm⟩ := exists_kernelLineData_of_le hQ hp hp2 hpl E hcomm hexp hcard
  have hq1 : 1 ≤ Nat.card K := Nat.one_le_iff_ne_zero.mpr Finite.card_pos.ne'
  have hΩ : orthDerived (quadMinus 4 K b c) = elementaryGroup (quadMinus 4 K b c) :=
    (orthDerived_eq_and_le_closure hQ hT).1
  have hΩO : orthDerived (quadMinus 4 K b c) ≤
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b c) :=
    orthDerived_le_orthogonalGroup _
  set G := E.map (orthDerived (quadMinus 4 K b c)).subtype with hG
  have hGΩ : G ≤ orthDerived (quadMinus 4 K b c) := Subgroup.map_subtype_le E
  by_cases hq : ((Nat.card K : ℕ) : ZMod p) = 1
  ·
    have hpq : p ∣ Nat.card K - 1 := by
      refine (ZMod.natCast_eq_zero_iff _ _).1 ?_
      rw [Nat.cast_sub hq1, hq]
      simp
    have hGel : Assembly.IsElemAbelian p G := isElemAbelian_map_subtype E hcomm hexp
    have hGcard : Nat.card G = p ^ 2 := by
      rw [hG, Subgroup.card_map_of_injective (orthDerived _).subtype_injective, hcard]
    have hgen := orthogonal_plane_derived_centralizers_generate hQ hT hp (by omega) hpq G hGΩ hGel
      hGcard
    exact closure_centralizers_eq_top_of_le E (orthDerived_le_orthCentralizerSpan_of_iSup E hgen)
  ·
    have hpq0 : ((Nat.card K : ℕ) : ZMod p) ≠ 0 := by
      intro h0
      have hd := (ZMod.natCast_eq_zero_iff _ _).1 h0
      have := Fintype.ofFinite K
      obtain ⟨n, -, hn⟩ := FiniteField.card K 2
      have hd2 : p ∣ 2 ^ (n : ℕ) := by
        have := Nat.card_eq_fintype_card (α := K)
        rw [this, hn] at hd
        exact hd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd2))
    have hdim : finrank K (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K) = 8 := by simp
    rw [hdim] at hlcm
    have hordpos : 0 < orderOf ((Nat.card K : ℕ) : ZMod p) :=
      orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨p - 1, by omega,
        ZMod.pow_card_sub_one_eq_one hpq0⟩)
    have hle : orderOf ((Nat.card K : ℕ) : ZMod p) ≤
        Nat.lcm (orderOf ((Nat.card K : ℕ) : ZMod p)) 2 :=
      Nat.le_of_dvd (Nat.lcm_pos hordpos (by norm_num)) (Nat.dvd_lcm_left _ _)
    have hne1 : orderOf ((Nat.card K : ℕ) : ZMod p) ≠ 1 := fun h => hq (orderOf_eq_one_iff.1 h)
    have hdvd4 : orderOf ((Nat.card K : ℕ) : ZMod p) ∣ 4 := by
      set e := orderOf ((Nat.card K : ℕ) : ZMod p) with he
      have he4 : e ≤ 4 := by omega
      interval_cases e
      · exact absurd rfl hne1
      · norm_num
      · exfalso
        norm_num [Nat.lcm] at hlcm
      · norm_num
    have h4 : ((Nat.card K : ℕ) : ZMod p) ^ 4 = 1 := orderOf_dvd_iff_pow_eq_one.1 hdvd4
    obtain ⟨P, hP⟩ := exists_fixed_hypPair_quadMinus_four hirr hp hp2 (E := G)
      (hGΩ.trans hΩO)
      (isElemAbelian_map_subtype E hcomm hexp).2 h4 hq
    have hmem : ∀ v, (∀ g ∈ G, g v = v) → v ∈ planeFixSpace E := fun v hv => hv
    have hle' : elementaryGroup (quadMinus 4 K b c) ≤ orthCentralizerSpan (quadMinus 4 K b c) E :=
      elementaryGroup_le_orthCentralizerSpan_of_hypPair hp hQ hT hK P
        (hmem _ fun g hg => (hP g hg).1) (hmem _ fun g hg => (hP g hg).2)
    exact closure_centralizers_eq_top_of_le E (hΩ ▸ hle')

end CFSG.RankThree.PartOne.CTP
