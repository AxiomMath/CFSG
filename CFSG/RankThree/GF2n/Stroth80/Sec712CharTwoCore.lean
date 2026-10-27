module

public import CFSG.RankThree.GF2n.Stroth80.Sec712OddCentralizer
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG

theorem charTwo_of_centralizer_core {H : Type} [Group H] [Finite H] (R N : Subgroup H)
    [R.Normal] [N.Normal] (hN : IsPGroup 2 N)
    (hDR : Subgroup.centralizer (N : Set H) ⊓ R ≤ N) (Λ : Subgroup H) (hΛR : Λ ≤ R)
    (hodd : ∀ x ∈ Subgroup.centralizer (N : Set H), Odd (orderOf x) →
      (∀ l ∈ Λ, l * x = x * l) → x = 1) :
    generalizedFitting H = pCore 2 H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hkey : ∀ y ∈ Subgroup.centralizer (N : Set H), Odd (orderOf y) → y = 1 := by
    intro y hy hyodd
    have hcent : ∀ x ∈ Subgroup.centralizer (N : Set H), ∀ c ∈ N, x * c = c * x := by
      intro x hx c hc
      exact ((Subgroup.mem_centralizer_iff.mp hx) c hc).symm
    have hcomm : ∀ r ∈ R, r * y = y * r :=
      commOfOddCentralizer_holds H R N (Subgroup.centralizer (N : Set H)) inferInstance
        inferInstance hN hcent hDR y hy hyodd
    exact hodd y hy hyodd (fun l hl => hcomm l (hΛR hl))
  have hD2 : IsPGroup 2 (Subgroup.centralizer (N : Set H)) := by
    intro g
    obtain ⟨a, m, hm, hn⟩ :=
      Nat.exists_eq_two_pow_mul_odd (isOfFinOrder_of_finite (g : H)).orderOf_pos.ne'
    refine ⟨a, Subtype.ext ?_⟩
    have hy : (g : H) ^ 2 ^ a ∈ Subgroup.centralizer (N : Set H) := pow_mem g.2 (2 ^ a)
    have hpow : ((g : H) ^ 2 ^ a) ^ m = 1 := by
      rw [← pow_mul, ← hn, pow_orderOf_eq_one]
    have hodd' : Odd (orderOf ((g : H) ^ 2 ^ a)) :=
      Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one hpow)
    simpa using hkey _ hy hodd'
  have hDle : Subgroup.centralizer (N : Set H) ≤ pCore 2 H :=
    le_sSup (⟨inferInstance, hD2⟩ : Subgroup.centralizer (N : Set H) ∈
      {K : Subgroup H | K.Normal ∧ IsPGroup 2 K})
  have hNle : N ≤ pCore 2 H :=
    le_sSup (⟨inferInstance, hN⟩ : N ∈ {K : Subgroup H | K.Normal ∧ IsPGroup 2 K})
  have hchar : IsCharacteristicP 2 H :=
    (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hNle)).trans hDle
  exact (CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore H 2).mp hchar

end CFSG.RankThree.GF2n.Stroth80
