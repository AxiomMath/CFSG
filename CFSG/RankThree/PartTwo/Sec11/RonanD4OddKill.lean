module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie2ProofOuter
import CFSG.RankThree.PartTwo.Sec16.KS16ProofGTwo
import CFSG.RankThree.PartTwo.Sec11.KS11LieProofSylow

public section

namespace CFSG.RankThree.PartTwo.Sec11.RonanD4Odd

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open scoped commutatorElement

theorem le_of_perfect_of_solvable_quotient' {C : Type} [Group C] {J P : Subgroup C} [J.Normal]
    (hsol : Group.IsSolvable (C ⧸ J)) (hP : Group.IsPerfect P) : P ≤ J := by
  intro x hx
  let π : P →* C ⧸ J := (QuotientGroup.mk' J).comp P.subtype
  have hf : π.range = ⊥ := by
    by_contra hne
    haveI : Nontrivial ↥π.range := (Subgroup.nontrivial_iff_ne_bot _).2 hne
    haveI : Group.IsSolvable ↥π.range :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.subtype_injective _)
    haveI : Group.IsPerfect ↥π.range := Group.IsPerfect.range _
    exact Group.IsPerfect.not_isSolvable (↥π.range) inferInstance
  have hmem : π ⟨x, hx⟩ ∈ π.range := ⟨_, rfl⟩
  rw [hf, Subgroup.mem_bot] at hmem
  exact (QuotientGroup.eq_one_iff x).1 hmem

theorem not_hasType424_of_quasisimple {Γ : Type} [Group Γ] [Finite Γ] (N : Subgroup Γ)
    [N.Normal] (hNq : CFSG.IsQuasisimple N) (hsol : Group.IsSolvable (Γ ⧸ N)) {x y : Γ}
    (hxN : x ∈ N) (hyN : y ∈ N) (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1)
    (hcx : Commute ⁅x, y⁆ x) (hcy : Commute ⁅x, y⁆ y) (hyx : y ∉ Subgroup.zpowers x) :
    ¬ KS11Lie2Proof.HasType424 Γ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rintro ⟨L, ⟨hLp, hLsn, hLq⟩, hT⟩
  have hLN : L ≤ N := le_of_perfect_of_solvable_quotient' hsol hLp
  have hNc : CFSG.IsComponent N := ⟨hNq, Subgroup.Normal.isSubnormal inferInstance⟩
  rcases CFSG.LocalCores.component_subnormal_subgroup hNc hLsn with hNL | hcomm
  · have hxL : x ∈ L := hNL hxN
    have hyL : y ∈ L := hNL hyN
    set π := QuotientGroup.mk' (aschbacherSolvableCore 3 L) with hπ
    set xb := π ⟨x, hxL⟩ with hxb
    set yb := π ⟨y, hyL⟩ with hyb
    have hcube := Sec16.KS1622GTwoProof.pow_three_eq_one_of_mem_closure hx3 hy3 hcx hcy
    have hxb1 : xb ≠ 1 := by
      intro h1
      rw [hxb, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      have h2 := eq_one_of_mem_theta_of_pow_eq_one h1 (k := 1)
        (Subtype.ext (by simpa using hx3))
      exact hx1 (congrArg Subtype.val h2)
    have hxb3 : xb ^ 3 = 1 := by
      rw [hxb, ← map_pow]
      have : (⟨x, hxL⟩ : L) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
      rw [this, map_one]
    have hyb3 : yb ^ 3 = 1 := by
      rw [hyb, ← map_pow]
      have : (⟨y, hyL⟩ : L) ^ 3 = 1 := Subtype.ext (by simpa using hy3)
      rw [this, map_one]
    have hP : IsPGroup 3 (Subgroup.closure ({xb, yb} : Set (L ⧸ aschbacherSolvableCore 3 L))) := by
      intro g
      refine ⟨1, Subtype.ext ?_⟩
      rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
      have hle : Subgroup.closure ({xb, yb} : Set (L ⧸ aschbacherSolvableCore 3 L)) ≤
          (Subgroup.closure ({⟨x, hxL⟩, ⟨y, hyL⟩} : Set L)).map π := by
        rw [Subgroup.closure_le]
        rintro _ (rfl | rfl)
        · exact ⟨_, Subgroup.subset_closure (by simp), rfl⟩
        · exact ⟨_, Subgroup.subset_closure (by simp), rfl⟩
      obtain ⟨w, hw, hwg⟩ := hle g.2
      have hw' : (w : Γ) ∈ Subgroup.closure ({x, y} : Set Γ) := by
        have hmap : (Subgroup.closure ({⟨x, hxL⟩, ⟨y, hyL⟩} : Set L)).map L.subtype ≤
            Subgroup.closure ({x, y} : Set Γ) := by
          rw [MonoidHom.map_closure, Subgroup.closure_le]
          rintro _ ⟨u, hu, rfl⟩
          rcases hu with rfl | rfl
          · exact Subgroup.subset_closure (by simp)
          · exact Subgroup.subset_closure (by simp)
        exact hmap ⟨w, hw, rfl⟩
      rw [← hwg, ← map_pow]
      have : w ^ 3 = 1 := Subtype.ext (by simpa using hcube _ hw')
      rw [this, map_one]
    obtain ⟨S, hS⟩ := hP.exists_le_sylow
    have hSc : IsCyclic S := KS11LieProof.isCyclic_sylow_three_of_isType424 hT hLq S
    have hxS : xb ∈ S := hS (Subgroup.subset_closure (by simp))
    have hyS : yb ∈ S := hS (Subgroup.subset_closure (by simp))
    have hyb1 : yb ≠ 1 := by
      intro h1
      apply hyx
      rw [hyb, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      have h2 := eq_one_of_mem_theta_of_pow_eq_one h1 (k := 1)
        (Subtype.ext (by simpa using hy3))
      have h3 : y = 1 := congrArg Subtype.val h2
      rw [h3]
      exact Subgroup.one_mem _
    have hox : orderOf xb = 3 := orderOf_eq_prime hxb3 hxb1
    have hoy : orderOf yb = 3 := orderOf_eq_prime hyb3 hyb1
    have hzS : (Subgroup.zpowers (⟨xb, hxS⟩ : S)) = Subgroup.zpowers ⟨yb, hyS⟩ := by
      rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers,
        Subgroup.orderOf_mk, Subgroup.orderOf_mk, hox, hoy]
    have hyx' : (⟨yb, hyS⟩ : S) ∈ Subgroup.zpowers ⟨xb, hxS⟩ := by
      rw [hzS]
      exact Subgroup.mem_zpowers _
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hyx'
    have hi' : xb ^ i = yb := congrArg Subtype.val hi
    apply hyx
    have hθ : (⟨y, hyL⟩ : L) * ((⟨x, hxL⟩ : L) ^ i)⁻¹ ∈ aschbacherSolvableCore 3 L := by
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_mul, map_inv, map_zpow, ← hπ,
        ← hxb, ← hyb, hi', mul_inv_cancel]
    have hmem : y * (x ^ i)⁻¹ ∈ Subgroup.closure ({x, y} : Set Γ) :=
      Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.inv_mem _ (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) _))
    have h3 : ((⟨y, hyL⟩ : L) * ((⟨x, hxL⟩ : L) ^ i)⁻¹) ^ 3 ^ 1 = 1 :=
      Subtype.ext (by simpa using hcube _ hmem)
    have h4 := congrArg Subtype.val (eq_one_of_mem_theta_of_pow_eq_one hθ h3)
    have h5 : y * (x ^ i)⁻¹ = 1 := by simpa using h4
    rw [mul_inv_eq_one] at h5
    rw [h5]
    exact Subgroup.zpow_mem_zpowers x i
  · exfalso
    have hLb : L = ⊥ := by
      have h1 : ⁅L, L⁆ = L := Subgroup.commutator_eq_self
      have h2 : ⁅L, L⁆ ≤ ⁅N, L⁆ := Subgroup.commutator_mono hLN le_rfl
      rw [hcomm] at h2
      rw [← h1]
      exact le_bot_iff.mp h2
    subst hLb
    obtain ⟨-, -, u, v, huv⟩ := hLq
    exact huv (Subsingleton.elim _ _)

end CFSG.RankThree.PartTwo.Sec11.RonanD4Odd
