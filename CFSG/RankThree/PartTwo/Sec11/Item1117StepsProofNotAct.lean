module

public import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofTools
public import CFSG.RankThree.PartTwo.Sec11.Item1117Proof

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Statements

@[expose] def Gap1117NotActXNormal : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d x s r g : G), Sec11Data G A c L a R Y d x s r g →
      Subgroup.zpowers s = Subgroup.zpowers c →
      Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s} →
      (orderOf x = 9 ∨ KFacts.InducesStdKind Y c .field) →
      g * x ^ 3 * g⁻¹ = x ^ 3 → g * x * g⁻¹ ∈ Subgroup.zpowers x →
      ⁅sec11P R g, sec11P R g⁆ = Subgroup.zpowers d →
        Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
          Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G)

end Statements

namespace Item1117StepsProof

section Data

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g : G}

theorem commutator_eq_zpowers_d (h117 : Item117) (h : Sec11Data G A c L a R Y d x s r g)
    (hsc : Subgroup.zpowers s = Subgroup.zpowers c)
    (hrs : Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s})
    (hgx3 : g * x ^ 3 * g⁻¹ = x ^ 3) (hgx : g * x * g⁻¹ ∈ Subgroup.zpowers x) :
    ⁅sec11P R g, sec11P R g⁆ = Subgroup.zpowers d := by
  have heA := Item1117Proof.commutator_g_x_mem h hsc hrs hgx3
  have hex : g * x * g⁻¹ * x⁻¹ ∈ Subgroup.zpowers x :=
    Subgroup.mul_mem _ hgx (Subgroup.inv_mem _ (Subgroup.mem_zpowers x))
  have hed : g * x * g⁻¹ * x⁻¹ ∈ Subgroup.zpowers d :=
    Item1117Proof.mem_zpowers_of_pow_three_eq_one (Item1117Proof.d_mem_zpowers_x h)
      (Item1117Proof.orderOf_d h) hex (Item1117Proof.pow_three_of_mem_A h heA)
  rw [Item1117Proof.commutator_eq_closure h117 h hsc hrs heA]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact hed
    · exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le]
    exact Subgroup.subset_closure (by simp)

end Data

end Item1117StepsProof

section Main

open Item1117StepsProof in
theorem gap1117NotActX_of (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (h118 : Item118) (h119 : Item119) (h82 : Sec8.Item82One) (hND : KFact1117Cube)
    (hN : Gap1117NotActXNormal) : Gap1117NotActX := by
  intro G _ _ A c L a R Y d x s r g h hsc hrs hgx
  by_cases hcase : orderOf x = 9 ∨ KFacts.InducesStdKind Y c .field
  swap
  · push Not at hcase
    have h9 : 9 ≤ orderOf x := Nat.le_of_dvd (orderOf_pos_iff.mpr (isOfFinOrder_of_finite x))
      (Item1117Proof.nine_dvd_orderOf_x h)
    exact Item1117Proof.false_of_not_field h119 hND h hsc hrs hcase.2 (by omega)
  have hgx3 := Item1117Proof.conj_g_x_cube h117 h118 h119 h82 hND h hsc hrs
  have hPP := commutator_eq_zpowers_d h117 h hsc hrs hgx3 hgx
  have hcdN := hN G A c L a R Y d x s r g h hsc hrs hcase hgx3 hgx hPP
  refine false_of_commutator_le_closure_c_d h45 h113 h117 h hrs ?_ hcdN
  rw [hPP, Subgroup.zpowers_le]
  exact Subgroup.subset_closure (by simp)

end Main

end CFSG.RankThree.PartTwo.Sec11
