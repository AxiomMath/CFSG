module

public import CFSG.Quasithin.EmptyFaithful.S146zYFOUnit
public import CFSG.Quasithin.EmptyFaithful.S146zYFOCount
public import CFSG.Quasithin.EmptyFaithful.S146zYFOOrd

public section

namespace CFSG.Quasithin.S146zY

namespace FiveOdd

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.Assembly.LowTwoRank

open CFSG.LieType.BorelTits in
theorem card_proj_suid_five {K : Type} [Field K] [Finite K] [Fact (Nat.Prime 5)] [CharP K 5]
    (hK : Nat.card K = (5 ^ 1) ^ 2) :
    Nat.card (StatedProj (SUid (unitaryInvolution K 5 1) 3)) = 126000 := by
  rw [SUid_eq_statedSU hK 3, pow_one, card_statedProj_statedSU_three Nat.prime_five
    (by rwa [pow_one] at hK)]
  norm_num

variable {K : Type} [Field K] {σ : K ≃+* K}

@[expose] noncomputable def projPerm (σ : K ≃+* K) :
    StatedProj (SUid σ 3) →* Equiv.Perm (isoPts σ 3) :=
  QuotientGroup.lift ((StatedScalars (Fin 3) K).subgroupOf (SUid σ 3))
    (MulAction.toPermHom (SUid σ 3) (isoPts σ 3)) (by
      intro g hg
      rw [MonoidHom.mem_ker]
      refine Equiv.ext fun x => ?_
      exact smul_eq_of_mem_scalars hg x)

@[expose, instance_reducible] noncomputable def projAction (σ : K ≃+* K) :
    MulAction (StatedProj (SUid σ 3)) (isoPts σ 3) :=
  MulAction.compHom _ (projPerm σ)

attribute [local instance] projAction

theorem pow_three_of_mem_scalars {z : SUid σ 3}
    (hz : z ∈ (StatedScalars (Fin 3) K).subgroupOf (SUid σ 3)) : z ^ 3 = 1 := by
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 hz
  have hdet : ((Matrix.GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K).det = (c : K) ^ 3 := by
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hz1 : ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := z.2.1
  have hc3 : c ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, ← hdet, hc, hz1, Units.val_one]
  apply Subtype.ext
  rw [Subgroup.coe_pow, ← hc, ← map_pow, hc3, map_one, Subgroup.coe_one]

theorem exists_lift_pow_five {gbar : StatedProj (SUid σ 3)} (hg : gbar ^ 5 = 1) :
    ∃ g : SUid σ 3, g ^ 5 = 1 ∧ (QuotientGroup.mk g : StatedProj (SUid σ 3)) = gbar := by
  obtain ⟨g0, rfl⟩ := QuotientGroup.mk_surjective gbar
  have hz : g0 ^ 5 ∈ (StatedScalars (Fin 3) K).subgroupOf (SUid σ 3) := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hg
  have h3 := pow_three_of_mem_scalars hz
  refine ⟨g0 ^ 6, ?_, ?_⟩
  · rw [← pow_mul, show 6 * 5 = 5 * 3 * 2 by norm_num, pow_mul, pow_mul, h3, one_pow]
  · rw [QuotientGroup.mk_pow, show 6 = 5 + 1 by norm_num, pow_succ, hg, one_mul]

variable (hσ : IsUnitaryInvolution σ) [CharP K 5]
include hσ

theorem exists_fixed_pt_proj {gbar : StatedProj (SUid σ 3)} (hg : gbar ^ 5 = 1) :
    ∃ x : isoPts σ 3, gbar • x = x := by
  obtain ⟨g, hg5, rfl⟩ := exists_lift_pow_five hg
  obtain ⟨x, hx⟩ := exists_fixed_pt_of_pow_five hσ hg5
  exact ⟨x, hx⟩

theorem eq_one_of_fixes_two_proj {gbar : StatedProj (SUid σ 3)} (hg : gbar ^ 5 = 1)
    {x y : isoPts σ 3} (hxy : x ≠ y) (hx : gbar • x = x) (hy : gbar • y = y) : gbar = 1 := by
  obtain ⟨g, hg5, rfl⟩ := exists_lift_pow_five hg
  have := eq_one_of_pow_five_of_fixes_two hσ hg5 hxy hx hy
  rw [this]
  rfl

omit hσ [CharP K 5] in
theorem isPretransitive_proj (hσ : IsUnitaryInvolution σ) :
    MulAction.IsPretransitive (StatedProj (SUid σ 3)) (isoPts σ 3) := by
  have h := isPretransitive_isoPts hσ (le_refl 3)
  refine ⟨fun x y => ?_⟩
  obtain ⟨g, hg⟩ := h.exists_smul_eq x y
  exact ⟨QuotientGroup.mk g, hg⟩

end FiveOdd

end CFSG.Quasithin.S146zY

namespace CFSG.Quasithin.S146zY

open FiveOdd

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.Assembly.LowTwoRank
open CFSG.LieType.BorelTits

theorem facts134Five_psu3Five :
    NoE25Config fun (X : Type) [Group X] => StatedClassicalModel X .PSU 3 5 1 := by
  intro A _ _ L P T hL hcfg
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hL
  have hK2 : Nat.card K = (5 ^ 1) ^ 2 := hK
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hchar : CharP K 5 := charP_of_card_sq (p := 5) (f := 1) hK2
  have hσ : IsUnitaryInvolution (unitaryInvolution K 5 1) :=
    isUnitaryInvolution_unitaryInvolution hK2
  have e' : ↥L ≃* StatedProj (SUid (unitaryInvolution K 5 1) 3) := by
    rw [SUid_eq_statedSU hK2 3]
    exact e
  obtain ⟨H, k, hHcard, hk, hodd⟩ := hcfg.exists_model e'
  have hX := card_proj_suid_five hK2
  rw [hX] at hk hodd
  have hk4 : k = 4 := by
    have hle : k ≤ 4 := by
      by_contra hlt
      have : 2 ^ 5 ∣ 126000 := (Nat.pow_dvd_pow 2 (by omega)).trans hk
      norm_num at this
    interval_cases k <;> simp_all
  subst hk4
  let _ := projAction (unitaryInvolution K 5 1)
  have _ := isPretransitive_proj hσ
  exact not_card_four_hundred (L := StatedProj (SUid (unitaryInvolution K 5 1) 3))
    (Ω := isoPts (unitaryInvolution K 5 1) 3) hX (one_lt_card_isoPts hσ)
    (fun g hg => exists_fixed_pt_proj hσ hg)
    (fun g hg x y hxy hx hy => eq_one_of_fixes_two_proj hσ hg hxy hx hy) H (by
      rw [hHcard]
      norm_num)

end CFSG.Quasithin.S146zY
