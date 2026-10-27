module

public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab
import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowAmbient

public section
namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG
open CFSG.Assembly.RankThreeEven (localRank)

variable {G : Type} [Group G] [Finite G]

theorem ff79_four_le_pRank {A H : Subgroup G} (hA : IsElemAb 3 4 A) (hAH : A ≤ H) :
    4 ≤ CFSG.Open.pRank 3 H := by
  haveI := hA.1
  refine le_csSup ⟨Nat.card G, ?_⟩ ⟨A, hAH, ⟨hA.1.toIsMulCommutative, ?_⟩, hA.2⟩
  · rintro k ⟨E, -, -, hE⟩
    have h1 : 3 ^ k ≤ Nat.card G := hE ▸ Subgroup.card_le_card_group E
    exact (Nat.lt_pow_self (by norm_num)).le.trans h1
  · intro x hx
    exact elemPow_eq_one_of_isElementaryAbelian (A := A) x hx

theorem ff79_pRank_le_card (H : Subgroup G) : CFSG.Open.pRank 3 H ≤ Nat.card G := by
  refine csSup_le' ?_
  rintro k ⟨E, -, -, hE⟩
  have h1 : 3 ^ k ≤ Nat.card G := hE ▸ Subgroup.card_le_card_group E
  exact (Nat.lt_pow_self (by norm_num)).le.trans h1

theorem ff79_no_rank_four_in_two_local {W A : Subgroup G} (hW : W ≠ ⊥) (hW2 : IsPGroup 2 W)
    (hA : IsElemAb 3 4 A) (hr : localRank 3 G = 3) : ¬ A ≤ Nor W := by
  intro hAN
  have h4 : 4 ≤ CFSG.Open.pRank 3 (Nor W) := ff79_four_le_pRank hA hAN
  have hmem : CFSG.Open.pRank 3 (Nor W) ∈
      {k | ∃ H : Subgroup G, CFSG.Open.IsTwoLocal H ∧ CFSG.Open.pRank 3 H = k} :=
    ⟨Nor W, ⟨W, hW, hW2, rfl⟩, rfl⟩
  have hle : CFSG.Open.pRank 3 (Nor W) ≤ localRank 3 G :=
    le_csSup ⟨Nat.card G, by
      rintro k ⟨H, -, rfl⟩
      exact ff79_pRank_le_card H⟩ hmem
  omega

theorem ff79_le_normalizer_opp {N A : Subgroup G} (hA : A ≤ N) :
    A ≤ Nor (Opp 3 N) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  have aux : ∀ b ∈ A, ∀ o ∈ Opp 3 N, b * o * b⁻¹ ∈ Opp 3 N := by
    intro b hb o ho
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp ho
    refine Subgroup.mem_map.mpr ⟨⟨b, hA hb⟩ * n * ⟨b, hA hb⟩⁻¹, ?_, rfl⟩
    exact (pPrimeCore_normal (p := 3) (G := N)).conj_mem n hn ⟨b, hA hb⟩
  intro h
  refine ⟨fun hh => aux a ha h hh, fun hh => ?_⟩
  have := aux a⁻¹ (A.inv_mem ha) _ hh
  have e : a⁻¹ * (a * h * a⁻¹) * a⁻¹⁻¹ = h := by group
  rwa [e] at this

theorem ff79_opp3_cenS_odd {A U : Subgroup G}
    (hA : IsElemAb 3 4 A) (hU : U ≤ A) (hr : localRank 3 G = 3) :
    Odd (Nat.card (Opp 3 (CenS U))) := by
  haveI : IsElementaryAbelian 3 A := hA.1
  have hAN : A ≤ CenS U := by
    intro a ha u hu
    exact (hA.1.toIsMulCommutative.is_comm.comm ⟨u, hU hu⟩ ⟨a, ha⟩ |> congrArg Subtype.val)
  by_contra hodd
  have h2 : 2 ∣ Nat.card (Opp 3 (CenS U)) := by
    rw [Nat.not_odd_iff_even] at hodd
    exact even_iff_two_dvd.mp hodd
  have hcop : Nat.Coprime 3 (Nat.card (Opp 3 (CenS U))) := by
    have := (pPrimeCore_coprime_card (p := 3) (G := CenS U))
    rwa [Opp, inSubgroup, Subgroup.card_map_of_injective (CenS U).subtype_injective]
  obtain ⟨S, hS, hne⟩ :=
    CFSG.SignalizerFunctor.Helpers.normalized_subgroup_invariant_sylow_nontrivial 3 2
      Nat.prime_three Nat.prime_two A (Opp 3 (CenS U))
      (IsElementaryAbelian.isPGroup 3 A) (ff79_le_normalizer_opp hAN) hcop h2
  have hS2 : IsPGroup 2 (S.map (Opp 3 (CenS U)).subtype) :=
    (S.isPGroup').map _
  exact ff79_no_rank_four_in_two_local hne hS2 hA hr hS

end CFSG.RankThree.PartTwo.Sec21.FF79
