module

public import CFSG.Permutation.FiveTransitive.Degree24SylowFixedAction
public import CFSG.Permutation.FiveTransitive.Degree24FiveOrderIncidence
public import CFSG.Permutation.FiveTransitive.Degree14

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup

theorem sylow_five_fixedPoints_card_eq_nine_or_fourteen
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 5 (fixingSubgroup P s))
    (hScard : Nat.card S = 5) :
    Nat.card (sylowFixedPoints X P s S) = 9 ∨
      Nat.card (sylowFixedPoints X P s S) = 14 := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let H : Subgroup P := fixingSubgroup P s
  letI : IsCyclic S :=
    isCyclic_of_prime_card hScard
  obtain ⟨u, huRaw⟩ :=
    IsCyclic.exists_ofOrder_eq_natCard (α := S)
  have hu : orderOf u = 5 :=
    huRaw.trans hScard
  have huNe : u ≠ 1 := by
    intro huOne
    rw [huOne, orderOf_one] at hu
    omega
  let SP : Subgroup P := sylowImage X P s S
  let N : Subgroup P := sylowNormalizer X P s S
  let SN : Subgroup N := sylowInNormalizer X P s S
  let F := MulAction.fixedPoints SN X
  let uP : P := (u : H)
  let g : Equiv.Perm X := uP
  have huH : orderOf (u : H) = 5 := by
    calc
      orderOf (u : H) = orderOf u :=
        Subgroup.orderOf_coe _
      _ = 5 := hu
  have huP : orderOf uP = 5 := by
    calc
      orderOf uP = orderOf (u : H) :=
        Subgroup.orderOf_coe _
      _ = 5 := huH
  have hg : orderOf g = 5 := by
    calc
      orderOf g = orderOf uP :=
        Subgroup.orderOf_coe _
      _ = 5 := huP
  have hfixedEq :
      F = Function.fixedPoints g := by
    ext x
    rw [MulAction.mem_fixedPoints,
      Function.mem_fixedPoints_iff]
    constructor
    · intro hx
      have huSP : uP ∈ SP :=
        Subgroup.mem_map_of_mem H.subtype u.prop
      let uN : N := ⟨uP, SP.le_normalizer huSP⟩
      let uSN : SN := ⟨uN, huSP⟩
      change uP • x = x
      exact hx uSN
    · intro hx z
      obtain ⟨zH, hzS, hzEq⟩ :=
        Subgroup.mem_map.mp z.prop
      let zS : S := ⟨zH, hzS⟩
      have hzPow : zS ∈ Subgroup.zpowers u :=
        mem_zpowers_of_prime_card hScard huNe
      obtain ⟨j, hj⟩ :=
        Subgroup.mem_zpowers_iff.mp hzPow
      have huStab :
          uP ∈ MulAction.stabilizer P x := by
        rw [MulAction.mem_stabilizer_iff]
        change g x = x at hx
        exact hx
      have hzPowers :
          ((zH : H) : P) ∈
            Subgroup.zpowers uP := by
        rw [Subgroup.mem_zpowers_iff]
        refine ⟨j, ?_⟩
        let inclusion : S →* P :=
          H.subtype.comp (S : Subgroup H).subtype
        have hjP := congrArg inclusion hj
        rw [map_zpow] at hjP
        exact hjP
      have hzStab :
          ((zH : H) : P) ∈
            MulAction.stabilizer P x :=
        (Subgroup.zpowers_le.mpr huStab) hzPowers
      have hzFix :
          ((zH : H) : P) • x = x :=
        MulAction.mem_stabilizer_iff.mp hzStab
      have hzEqP :
          ((zH : H) : P) = ((z : N) : P) :=
        hzEq
      rw [hzEqP] at hzFix
      exact hzFix
  have hsupport :
      g.support.card = 10 ∨ g.support.card = 15 := by
    simpa only [H, uP, g] using
      order_five_mem_five_stabilizer_support_eq_ten_or_fifteen
        X P hcard h5 hnotAlt s hs (u : H) huH
  rcases hsupport with hten | hfifteen
  · right
    change Nat.card F = 14
    rw [hfixedEq, Nat.card_eq_fintype_card,
      Equiv.Perm.card_fixedPoints,
      Equiv.Perm.sum_cycleType, hcard, hten]
  · left
    change Nat.card F = 9
    rw [hfixedEq, Nat.card_eq_fintype_card,
      Equiv.Perm.card_fixedPoints,
      Equiv.Perm.sum_cycleType, hcard, hfifteen]

theorem sylow_five_local_normalizer_lower_cases
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 5 (fixingSubgroup P s))
    (hScard : Nat.card S = 5) :
    (Nat.card (sylowFixedPoints X P s S) = 9 ∧
        60 ≤ Nat.card
          (Subgroup.normalizer
            (S : Set (fixingSubgroup P s)))) ∨
      (Nat.card (sylowFixedPoints X P s S) = 14 ∧
        907200 ≤ Nat.card
          (Subgroup.normalizer
            (S : Set (fixingSubgroup P s)))) := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let H : Subgroup P := fixingSubgroup P s
  let N : Subgroup P := sylowNormalizer X P s S
  let SN : Subgroup N := sylowInNormalizer X P s S
  let F := MulAction.fixedPoints SN X
  let ρ : N →* Equiv.Perm F :=
    MulAction.toPermHom N F
  let J : Subgroup (Equiv.Perm F) := ρ.range
  let NL : Subgroup H :=
    Subgroup.normalizer (S : Set H)
  have hJ5 :
      ∀ a b : Fin 5 → F, Function.Injective a →
        Function.Injective b →
        ∃ q : J, ∀ i, q • a i = b i := by
    intro a b ha hb
    obtain ⟨q, hq⟩ :=
      sylowNormalizer_five_transitive_on_fixedPoints
        X P h5 s hs S a b ha hb
    let qJ : J := ⟨ρ q, ⟨q, rfl⟩⟩
    refine ⟨qJ, ?_⟩
    intro i
    exact hq i
  have hbound :
      5 * Nat.card J ≤
        (Nat.card F).descFactorial 5 * Nat.card NL := by
    simpa only [H, N, SN, F, ρ, J, NL, hScard] using
      sylow_card_mul_fixed_action_card_le
        X P h5 s hs S
  have hFcases :
      Nat.card F = 9 ∨ Nat.card F = 14 := by
    simpa only [N, SN, F] using
      sylow_five_fixedPoints_card_eq_nine_or_fourteen
        X P hcard h5 hnotAlt s hs S hScard
  rcases hFcases with hFnine | hFfourteen
  · left
    refine ⟨hFnine, ?_⟩
    change 60 ≤ Nat.card NL
    have hFtype : Fintype.card F = 9 := by
      rw [← Nat.card_eq_fintype_card]
      exact hFnine
    have hAlt :
        alternatingGroup F ≤
          (MulAction.toPermHom J F).range :=
      Helpers.alternatingGroup_le_of_five_transitive_of_card_eq_nine
        J F hFtype hJ5
    have hAltDvdRange :
        Nat.card (alternatingGroup F) ∣
          Nat.card (MulAction.toPermHom J F).range :=
      Subgroup.card_dvd_of_le hAlt
    have hAltDvdJ :
        Nat.card (alternatingGroup F) ∣ Nat.card J :=
      hAltDvdRange.trans
        (Subgroup.card_range_dvd
          (MulAction.toPermHom J F))
    have hAltCard :
        Nat.card (alternatingGroup F) = 181440 := by
      letI : Nontrivial F :=
        Fintype.one_lt_card_iff_nontrivial.mp (by
          rw [hFtype]
          norm_num)
      rw [Nat.card_eq_fintype_card,
        card_alternatingGroup, hFtype]
      norm_num
    have hJlower : 181440 ≤ Nat.card J := by
      rw [← hAltCard]
      exact Nat.le_of_dvd Nat.card_pos hAltDvdJ
    rw [hFnine] at hbound
    norm_num [Nat.descFactorial] at hbound
    rw [Nat.card_eq_fintype_card] at hJlower
    rw [Nat.card_eq_fintype_card]
    omega
  · right
    refine ⟨hFfourteen, ?_⟩
    change 907200 ≤ Nat.card NL
    have hFtype : Fintype.card F = 14 := by
      rw [← Nat.card_eq_fintype_card]
      exact hFfourteen
    have hAlt :
        alternatingGroup F ≤ J :=
      Degree14.alternatingGroup_le_of_five_transitive_of_card_eq_fourteen
        F J hFtype hJ5
    have hAltDvdJ :
        Nat.card (alternatingGroup F) ∣ Nat.card J :=
      Subgroup.card_dvd_of_le hAlt
    have hAltCard :
        Nat.card (alternatingGroup F) = 43589145600 := by
      letI : Nontrivial F :=
        Fintype.one_lt_card_iff_nontrivial.mp (by
          rw [hFtype]
          norm_num)
      rw [Nat.card_eq_fintype_card,
        card_alternatingGroup, hFtype]
      norm_num
    have hJlower : 43589145600 ≤ Nat.card J := by
      rw [← hAltCard]
      exact Nat.le_of_dvd Nat.card_pos hAltDvdJ
    rw [hFfourteen] at hbound
    norm_num [Nat.descFactorial] at hbound
    rw [Nat.card_eq_fintype_card] at hJlower
    rw [Nat.card_eq_fintype_card]
    omega

end FiveTransitive.Degree24

end CFSG
