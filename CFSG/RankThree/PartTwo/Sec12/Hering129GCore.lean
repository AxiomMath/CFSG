module

import CFSG.ClassicalInvolution.SubnormalCommutator
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.RankThree.PartTwo.Sec6.Item612Local

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem commutator_eq_self_of_not_mem_thetaQuotCentralizer {x c : G} {Y : Subgroup G}
    (hY : Y ∈ thetaComponentsAt 3 x) (hcN : c ∈ Subgroup.normalizer (Y : Set G))
    (hc : c ∉ Sec4.thetaQuotCentralizer Y) : ⁅Y, Subgroup.zpowers c⁆ = Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set M : Subgroup G := ⁅Y, Subgroup.zpowers c⁆ with hM
  set θ : Subgroup Y := aschbacherSolvableCore 3 Y with hθ
  have hzY : Subgroup.zpowers c ≤ Subgroup.normalizer (Y : Set G) := Subgroup.zpowers_le.mpr hcN
  have hMY : M ≤ Y := by
    rw [hM, Subgroup.commutator_le]
    intro u hu g hg
    exact CFSG.ClassicalInvolution.commutatorElement_mem_of_mem_normalizer hu (hzY hg)
  have hMn : ∀ y ∈ Y, ∀ m ∈ M, y * m * y⁻¹ ∈ M := by
    intro y hy m hm
    have hgen : ∀ (u : G) (hu : u ∈ Y) (k : G) (hk : k ∈ Subgroup.zpowers c), ⁅u, k⁆ ∈ M :=
      fun u hu k hk => Subgroup.commutator_mem_commutator hu hk
    rw [hM, Subgroup.commutator_def] at hm
    induction hm using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨u, hu, k, hk, rfl⟩ := hg
      have e : y * ⁅u, k⁆ * y⁻¹ = ⁅y * u, k⁆ * ⁅y, k⁆⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact M.mul_mem (hgen _ (Y.mul_mem hy hu) k hk) (M.inv_mem (hgen _ hy k hk))
    | one => simpa using M.one_mem
    | mul a b _ _ iha ihb =>
      have e : y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) := by group
      rw [e]
      exact M.mul_mem iha ihb
    | inv a _ iha =>
      have e : y * a⁻¹ * y⁻¹ = (y * a * y⁻¹)⁻¹ := by group
      rw [e]
      exact M.inv_mem iha
  set R : Subgroup Y := M.subgroupOf Y with hR
  have hRn : R.Normal := ⟨fun n hn g => by
    rw [hR, Subgroup.mem_subgroupOf] at hn ⊢
    exact hMn g g.2 n hn⟩
  have hQ : IsQuasisimple (Y ⧸ θ) := Sec6.isQuasisimple_of_mem_thetaComponentsAt hY
  have hYp : Group.IsPerfect Y := Sec6.isPerfect_of_mem_thetaComponentsAt hY
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ
      (hRn.map (QuotientGroup.mk' θ) (QuotientGroup.mk'_surjective θ)) with htop | hcent
  ·
    have hRθ : ∀ y : Y, ∃ r ∈ R, ∃ t ∈ θ, y = r * t := by
      intro y
      have : QuotientGroup.mk' θ y ∈ R.map (QuotientGroup.mk' θ) := by
        rw [htop]; exact Subgroup.mem_top _
      obtain ⟨r, hr, hry⟩ := this
      refine ⟨r, hr, r⁻¹ * y, ?_, by group⟩
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hry
      simpa using hry
    haveI : Group.IsPerfect (Y ⧸ R) := inferInstance
    have hsolv : Group.IsSolvable (Y ⧸ R) := by
      have hθs : Group.IsSolvable θ :=
        (solvable_prime_complement_core_characterization (H := Y) Nat.prime_three).1
      refine Group.isSolvable_of_surjective (f := (QuotientGroup.mk' R).comp θ.subtype) ?_
      intro q
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective R q
      obtain ⟨r, hr, t, ht, rfl⟩ := hRθ y
      refine ⟨⟨t, ht⟩, ?_⟩
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, map_mul]
      have h1 : QuotientGroup.mk' R r = 1 := (QuotientGroup.eq_one_iff r).mpr hr
      rw [h1, one_mul]
    have hsub : Subsingleton (Y ⧸ R) := by
      by_contra hns
      haveI : Nontrivial (Y ⧸ R) := not_subsingleton_iff_nontrivial.mp hns
      exact Group.IsPerfect.not_isSolvable (Y ⧸ R) hsolv
    have hRtop : R = ⊤ := by
      rw [eq_top_iff]
      intro y _
      have h1 : (y : Y ⧸ R) = 1 := Subsingleton.elim _ _
      exact (QuotientGroup.eq_one_iff y).mp h1
    refine le_antisymm hMY ?_
    intro y hy
    have : (⟨y, hy⟩ : Y) ∈ R := hRtop ▸ Subgroup.mem_top _
    exact this
  ·
    exfalso
    apply hc
    let σ : Y →* Y := (Y.normalizerMonoidHom ⟨c, hcN⟩).toMonoidHom
    have hσ : ∀ l : Y, (σ l : G) = c * l * c⁻¹ := fun l => rfl
    have hval : ∀ l : Y, QuotientGroup.mk' θ (l⁻¹ * σ l) ∈ Subgroup.center (Y ⧸ θ) := by
      intro l
      apply hcent
      refine ⟨l⁻¹ * σ l, ?_, rfl⟩
      change l⁻¹ * σ l ∈ M.subgroupOf Y
      rw [Subgroup.mem_subgroupOf]
      have := Subgroup.commutator_mem_commutator (H₁ := Y) (H₂ := Subgroup.zpowers c)
        (Y.inv_mem l.2) (Subgroup.mem_zpowers c)
      have e : (⁅(l : G)⁻¹, c⁆ : G) = ((l⁻¹ * σ l : Y) : G) := by
        rw [commutatorElement_def]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hσ]
        group
      rw [← e]
      exact this
    let g : Y →* Subgroup.center (Y ⧸ θ) :=
      { toFun := fun l => ⟨QuotientGroup.mk' θ (l⁻¹ * σ l), hval l⟩
        map_one' := by
          apply Subtype.ext
          simp
        map_mul' := fun l l' => by
          apply Subtype.ext
          have hz := Subgroup.mem_center_iff.mp (hval l)
          change QuotientGroup.mk' θ ((l * l')⁻¹ * σ (l * l')) =
            QuotientGroup.mk' θ (l⁻¹ * σ l) * QuotientGroup.mk' θ (l'⁻¹ * σ l')
          have e : (l * l')⁻¹ * σ (l * l') = l'⁻¹ * (l⁻¹ * σ l) * σ l' := by
            rw [map_mul]; group
          rw [e, map_mul, map_mul, hz (QuotientGroup.mk' θ l'⁻¹), mul_assoc, ← map_mul] }
    haveI : Group.IsPerfect g.range := Group.IsPerfect.range g
    haveI : IsMulCommutative g.range := ⟨⟨fun a b => Subtype.ext (Subtype.ext (by
      obtain ⟨_, l, rfl⟩ := a
      obtain ⟨_, l', rfl⟩ := b
      exact (Subgroup.mem_center_iff.mp (g l).2 (g l').1).symm))⟩⟩
    haveI : Subsingleton g.range := inferInstance
    refine Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨hcN, fun l hl => ?_⟩
    have h1 : g ⟨l, hl⟩ = 1 := by
      have := Subsingleton.elim (⟨g ⟨l, hl⟩, ⟨l, hl⟩, rfl⟩ : g.range) 1
      exact congrArg Subtype.val this
    have h2 : QuotientGroup.mk' θ (⟨l, hl⟩⁻¹ * σ ⟨l, hl⟩) = 1 := congrArg Subtype.val h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    refine ⟨_, h2, ?_⟩
    change ((⟨l, hl⟩⁻¹ * σ ⟨l, hl⟩ : Y) : G) = l⁻¹ * (c * l * c⁻¹)
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hσ]

end CFSG.RankThree.PartTwo.Sec12
