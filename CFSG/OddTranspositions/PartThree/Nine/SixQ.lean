module

public import CFSG.OddTranspositions.PartThree.Nine.Delta

public section

namespace CFSG.OddTranspositions.PartThree.Nine

open CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex (cosetNormalizerPerm)
open CFSG.ProperTwoGeneratedCore.CosetNormalizerSinger (translationGroup mem_translationGroup
  mul_constVAdd_mul_inv)
open CFSG.ProperTwoGeneratedCore.RankOnePair (cosetCoordinates cosetAffinePerm
  cosetAffinePerm_injective cosetAffinePerm_comp_eq)
open scoped IsMulCommutative MatrixGroups

theorem isRegularCore_comap_translationGroup {G : Type} [Group G] {U : Subgroup G}
    [IsElementaryAbelian 2 U] {u : G}
    (φ : Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G)) →*
      (Additive U ≃ᵃ[ZMod 2] Additive U))
    (hφ : ∀ (n : Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G))) (v : U),
      (n : G) * (u * v) * (n : G)⁻¹ = u * ((Additive.toMul (φ n (Additive.ofMul v)) : U) : G))
    (htr : ∀ g ∈ translationGroup (Additive U), (cosetCoordinates U u).permCongr g.toEquiv ∈
      (cosetNormalizerPerm ((fun v : G => u * v) '' (U : Set G))).range)
    (h2 : IsPGroup 2 (Subgroup.centralizer ((fun v : G => u * v) '' (U : Set G)))) :
    IsRegularCore ((fun v : G => u * v) '' (U : Set G))
      (((translationGroup (Additive U)).comap φ).map
        (Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G))).subtype) := by
  have hker := affine_eq_one_iff φ hφ
  have hww : ∀ w : Additive U, w + w = 0 := fun w => by
    rw [← two_smul (ZMod 2) w, show (2 : ZMod 2) = 0 by decide, zero_smul]
  refine ⟨Subgroup.map_subtype_le _, ?_, ?_, ?_, ?_, ?_⟩
  · rintro n hn _ ⟨m, hm, rfl⟩
    refine ⟨⟨n, hn⟩ * m * ⟨n, hn⟩⁻¹, ?_, rfl⟩
    obtain ⟨w, hw⟩ := mem_translationGroup.mp hm
    change φ (⟨n, hn⟩ * m * ⟨n, hn⟩⁻¹) ∈ translationGroup (Additive U)
    rw [map_mul, map_mul, map_inv, ← hw, mul_constVAdd_mul_inv]
    exact mem_translationGroup.mpr ⟨_, rfl⟩
  · rintro ⟨_, m, hm, rfl⟩
    obtain ⟨w, hw⟩ := mem_translationGroup.mp hm
    have hm2 : φ (m * m) = 1 := by
      rw [map_mul, ← hw, ← pow_two, ← AffineEquiv.constVAdd_nsmul, two_nsmul, hww,
        AffineEquiv.constVAdd_zero]
      rfl
    obtain ⟨k, hk⟩ := h2 ⟨_, (hker (m * m)).mp hm2⟩
    refine ⟨k + 1, Subtype.ext ?_⟩
    have hk' : ((m : G) * m) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [pow_succ', pow_mul, pow_two]
    exact hk'
  · intro c hc
    have hcN := Subgroup.centralizer_le_normalizer _ hc
    refine ⟨⟨c, hcN⟩, ?_, rfl⟩
    change φ ⟨c, hcN⟩ ∈ translationGroup (Additive U)
    rw [(hker ⟨c, hcN⟩).mpr hc]
    exact Subgroup.one_mem _
  · rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩
    set t := AffineEquiv.constVAdd (ZMod 2) (Additive U)
      (Additive.ofMul (⟨w, hw⟩ : U) - Additive.ofMul ⟨v, hv⟩) with htdef
    have ht : t ∈ translationGroup (Additive U) := mem_translationGroup.mpr ⟨_, rfl⟩
    obtain ⟨n, hn⟩ := htr t ht
    have hφn : φ n = t := by
      apply cosetAffinePerm_injective U u
      have hcomp := DFunLike.congr_fun (cosetAffinePerm_comp_eq φ hφ) n
      rw [MonoidHom.comp_apply] at hcomp
      rw [hcomp, hn]
      rfl
    refine ⟨n, ⟨n, show φ n ∈ translationGroup (Additive U) by rw [hφn]; exact ht, rfl⟩, ?_⟩
    change (n : G) * (u * v) * (n : G)⁻¹ = u * w
    rw [hφ n ⟨v, hv⟩, hφn, htdef, AffineEquiv.constVAdd_apply, vadd_eq_add, sub_add_cancel]
    rfl
  · rintro _ ⟨m, hm, rfl⟩ _ ⟨v, hv, rfl⟩ hfix
    obtain ⟨w, hw⟩ := mem_translationGroup.mp hm
    change (m : G) * (u * v) * (m : G)⁻¹ = u * v at hfix
    rw [hφ m ⟨v, hv⟩, ← hw, AffineEquiv.constVAdd_apply, vadd_eq_add] at hfix
    have h1 : w + Additive.ofMul (⟨v, hv⟩ : U) = Additive.ofMul ⟨v, hv⟩ :=
      Additive.toMul.injective (Subtype.ext (mul_left_cancel hfix))
    refine (hker m).mp ?_
    rw [← hw, add_eq_right.mp h1, AffineEquiv.constVAdd_zero]
    rfl

local instance factPrimeSevenSixQ : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩

private theorem not_isSolvable_psl_two_zmod_seven : ¬ Group.IsSolvable PSL(2, ZMod 7) := by
  have : Group.IsPerfect PSL(2, ZMod 7) :=
    ⟨SL2Simple.PSL_commutator_eq_top ⟨3, by decide, by decide⟩⟩
  exact Group.IsPerfect.not_isSolvable _

theorem lemma9_6Q : Lemma9_6Q := by
  intro G _ _ D hC hH _ h3 T S hTS _ h5 hsolv
  obtain ⟨U, hU⟩ := exists_deltaSetup hC hH h3 T S hTS
  have := hU.isElementaryAbelian
  have hΔ := hU.sylow_inter
  obtain ⟨hcent, -⟩ := h5
  rw [hΔ] at hsolv hcent ⊢
  obtain ⟨-, -, ⟨φ, -, hφ⟩, -⟩ := hU.affine h3
  have htr : ∀ g ∈ translationGroup (Additive U), (cosetCoordinates U hC.d).permCongr
      g.toEquiv ∈ (cosetNormalizerPerm ((fun v : G => hC.d * v) '' (U : Set G))).range := by
    rcases hU.solvable_or_projective_seven h3 with ⟨-, htr⟩ | ⟨-, ⟨e⟩⟩
    · exact htr
    · have he : Function.Surjective e.toMonoidHom := e.surjective
      exact absurd (Group.isSolvable_of_surjective he) not_isSolvable_psl_two_zmod_seven
  have h2 : IsPGroup 2 (Subgroup.centralizer ((fun v : G => hC.d * v) '' (U : Set G))) := by
    rw [hcent]
    exact T.isPGroup'.map _
  exact ⟨_, isRegularCore_comap_translationGroup φ hφ htr h2⟩

end CFSG.OddTranspositions.PartThree.Nine
