module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.InvolutionCore
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.StrongEmbeddingFusion

public section

namespace CFSG.BenderSuzuki

open PFAppendixIII
open scoped Pointwise

noncomputable section

theorem normal_subgroup_isPretransitive_of_unique_involution_fixed_point
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    [MulAction.IsPretransitive G Ω] (N : Subgroup G) [N.Normal]
    {t : G} (htN : t ∈ N) (ht : IsInvolution t)
    {α : Ω} (hα : t • α = α)
    (hunique : ∀ β : Ω, t • β = β → β = α) :
    MulAction.IsPretransitive N Ω := by
  classical
  let C : Subgroup G := Subgroup.zpowers t
  have hCN : C ≤ N := Subgroup.zpowers_le.mpr htN
  let O (β : Ω) : SubMulAction C Ω :=
    { carrier := MulAction.orbit N β
      smul_mem' := fun c γ hγ =>
        MulAction.mapsTo_smul_orbit (⟨c, hCN c.property⟩ : N) β hγ }
  have hCp : IsPGroup 2 C := isPGroup_zpowers_of_involution ht
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hαfixed : (⟨α, MulAction.mem_orbit_self α⟩ : O α) ∈
      MulAction.fixedPoints C (O α) := by
    apply MulAction.mem_fixedPoints.mpr
    intro c
    apply Subtype.ext
    have htstab : t ∈ MulAction.stabilizer G α := hα
    exact MulAction.mem_stabilizer_iff.mp
      ((Subgroup.zpowers_le.mpr htstab) c.property)
  have hfixedCard : Nat.card (MulAction.fixedPoints C (O α)) = 1 := by
    apply Nat.card_eq_one_iff_exists.mpr
    refine ⟨⟨⟨α, MulAction.mem_orbit_self α⟩, hαfixed⟩, ?_⟩
    intro β
    apply Subtype.ext
    apply Subtype.ext
    apply hunique
    exact congrArg Subtype.val
      (MulAction.mem_fixedPoints.mp β.property
        (⟨t, Subgroup.mem_zpowers t⟩ : C))
  have hodd : ¬ 2 ∣ Nat.card (O α) := by
    have hmod := hCp.card_modEq_card_fixedPoints (O α)
    rw [hfixedCard] at hmod
    intro hdiv
    have hzero := Nat.modEq_zero_iff_dvd.mpr hdiv
    have : 0 ≡ 1 [MOD 2] := hzero.symm.trans hmod
    norm_num [Nat.ModEq] at this
  apply MulAction.IsPretransitive.of_orbit (x₀ := α)
  intro β
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G α β
  have horbit : g • MulAction.orbit N α = MulAction.orbit N β := by
    simpa [hg] using MulAction.smul_orbit_eq_orbit_smul N α g
  let e : O α ≃ O β :=
    { toFun := fun γ => ⟨g • γ.val, by
        change g • γ.val ∈ MulAction.orbit N β
        rw [← horbit]
        exact Set.smul_mem_smul_set γ.property⟩
      invFun := fun γ => ⟨g⁻¹ • γ.val, by
        change g⁻¹ • γ.val ∈ MulAction.orbit N α
        apply Set.mem_smul_set_iff_inv_smul_mem.mp
        rw [horbit]
        exact γ.property⟩
      left_inv := fun γ => Subtype.ext (inv_smul_smul g γ.val)
      right_inv := fun γ => Subtype.ext (smul_inv_smul g γ.val) }
  have hoddβ : ¬ 2 ∣ Nat.card (O β) := by
    rwa [← Nat.card_congr e]
  obtain ⟨γ, hγ⟩ := hCp.nonempty_fixed_point_of_prime_not_dvd_card (O β) hoddβ
  have htγ : t • γ.val = γ.val := congrArg Subtype.val
    (MulAction.mem_fixedPoints.mp hγ (⟨t, Subgroup.mem_zpowers t⟩ : C))
  have hαorbit : α ∈ MulAction.orbit N β := hunique γ.val htγ ▸ γ.property
  exact MulAction.mem_orbit_iff.mp (MulAction.mem_orbit_symm.mp hαorbit)

theorem IsStronglyEmbedded.involutionCore_isPretransitive
    {X : Type*} [Group X] [Finite X] {H : Subgroup X}
    (hH : IsStronglyEmbedded H) :
    MulAction.IsPretransitive (involutionCore X) (conjugateCosetSpace H) := by
  obtain ⟨t, _htH, ht⟩ := hH.exists_involution
  obtain ⟨α, hα, hunique⟩ := hH.involution_fixed_coset_unique ht
  have htcore : t ∈ involutionCore X := by
    rw [involutionCore_eq_closure]
    exact Subgroup.subset_closure ht
  exact normal_subgroup_isPretransitive_of_unique_involution_fixed_point
    (involutionCore X) htcore ht hα hunique

end

end CFSG.BenderSuzuki
