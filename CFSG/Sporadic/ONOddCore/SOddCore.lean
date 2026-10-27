module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSLSemilinearInvolution
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityPureGraph
public import CFSG.Sporadic.ONOddCore.LocalAutOrders

public noncomputable section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

abbrev S3 : Type := LinearFlag.projectiveSL 3 PSL3Four.F4

theorem card_F4 : Nat.card PSL3Four.F4 = 2 ^ 2 := by
  rw [Nat.card_congr PSL3Four.F4.codeEquiv, Nat.card_fin]
  norm_num

theorem card_S3 :
    Nat.card S3 = 20160 := by
  rw [Nat.card_congr thetaX.toEquiv, card_onX]

instance S3_simple : IsSimpleGroup S3 := by
  have := (CFSG.LinearGroups.linear_projective_simple (K := PSL3Four.F4) (n := 3) (by omega)
    (Or.inl (by omega))).2.1
  exact (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 PSL3Four.F4).symm.isSimpleGroup

theorem center_S3 :
    Subgroup.center S3 = ⊥ := by
  rw [eq_bot_iff]
  intro s hs
  rw [Subgroup.mem_bot]
  have hx : ((thetaX s : onX) : Equiv.Perm (Fin 120)) ∈
      Subgroup.centralizer (onX : Set (Equiv.Perm (Fin 120))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h := Subgroup.mem_center_iff.1 hs (thetaX.symm ⟨y, hy⟩)
    have h' := congrArg (fun w => ((thetaX w : onX) : Equiv.Perm (Fin 120))) h
    simpa only [map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul] using h'
  rw [at_on_standard_psl34_action.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, Subgroup.mem_bot] at hx
  apply thetaX.injective
  rw [map_one]
  exact Subtype.ext hx

theorem oddCore_S3 :
    CFSG.oddCore S3 = ⊥ :=
  UnbalancedCatalog.EvenCatalog.oddCore_eq_bot_of_isSimpleGroup
    (by rw [card_S3]; decide)

theorem conj_injective_S3 :
    Function.Injective (MulAut.conj : S3 →* MulAut S3) := by
  rw [← MonoidHom.ker_eq_bot_iff, conj_ker_eq_center, center_S3]

theorem conj_apply_aut {G : Type*} [Group G] (γ : MulAut G) (s : G) :
    MulAut.conj (γ s) = γ * MulAut.conj s * γ⁻¹ := by
  ext y
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.inv_apply,
    MulEquiv.apply_symm_apply]

theorem conj_mem_centralizer_iff
    (γ : MulAut S3) (s : S3) :
    MulAut.conj s ∈ Subgroup.centralizer {γ} ↔ γ s = s := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    apply conj_injective_S3
    rw [conj_apply_aut, ← h]
    group
  · intro h
    have h1 := conj_apply_aut γ s
    rw [h] at h1
    calc MulAut.conj s * γ = γ * MulAut.conj s * γ⁻¹ * γ := by rw [← h1]
      _ = γ * MulAut.conj s := by group

@[expose] def fixInnerHom
    (γ : MulAut S3) :
    fixedSubgroup γ →* (inner S3 ⊓ Subgroup.centralizer {γ} : Subgroup (MulAut S3)) where
  toFun s := ⟨MulAut.conj (s : S3), ⟨s, rfl⟩, (conj_mem_centralizer_iff γ s).2 s.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)

theorem fixInnerHom_bijective
    (γ : MulAut S3) : Function.Bijective (fixInnerHom γ) := by
  constructor
  · intro a b h
    exact Subtype.ext (conj_injective_S3 (congrArg Subtype.val h))
  · intro c
    obtain ⟨⟨s, hs⟩, hc⟩ := Subgroup.mem_inf.1 c.2
    rw [← hs] at hc
    refine ⟨⟨s, (conj_mem_centralizer_iff γ s).1 hc⟩, Subtype.ext ?_⟩
    exact hs

@[expose] def fixInnerEquiv
    (γ : MulAut S3) :
    fixedSubgroup γ ≃* (inner S3 ⊓ Subgroup.centralizer {γ} : Subgroup (MulAut S3)) :=
  MulEquiv.ofBijective _ (fixInnerHom_bijective γ)

theorem fixedSubgroup_one {G : Type*} [Group G] : fixedSubgroup (1 : MulAut G) = ⊤ := by
  ext x
  exact ⟨fun _ => trivial, fun _ => rfl⟩

open UnbalancedCatalog.EvenCatalog in
theorem oddCore_fixed_S
    {γ : MulAut S3} (hγ : γ * γ = 1)
    (hform : (∃ A, γ = LinearFlag.conjAut 3 PSL3Four.F4 A * LinearFlag.dualAut 3 PSL3Four.F4) ∨
      ∃ A, γ = LinearFlag.conjAut 3 PSL3Four.F4 A *
        LinearFlag.fieldAut 3 PSL3Four.F4 PSL3Four.frob) :
    CFSG.oddCore (fixedSubgroup γ) = ⊥ := by
  by_cases h1 : γ = 1
  · subst h1
    rw [fixedSubgroup_one]
    exact oddCore_eq_bot_of_mulEquiv Subgroup.topEquiv.symm oddCore_S3
  have hγ2 : γ ^ 2 = 1 := by rw [pow_two, hγ]
  have hord : orderOf γ = 2 := orderOf_eq_prime hγ2 h1
  refine oddCore_eq_bot_of_mulEquiv (fixInnerEquiv γ).symm ?_
  rcases hform with ⟨A, rfl⟩ | ⟨A, rfl⟩
  ·
    obtain ⟨-, ⟨H, C, -, hHC, hC⟩, -⟩ :=
      UnitaryHigher.even_linear_pure_graph_involution_normal_forms (K := PSL3Four.F4) (by norm_num)
        card_F4 (le_refl 3) A hγ2
    have hC1 : (C : Matrix (Fin 3) (Fin 3) PSL3Four.F4) = 1 := by
      rcases hC with ⟨h, -⟩ | ⟨r, hr, -⟩
      · exact h
      · omega
    have hcan := (UnbalancedCatalog.even_linear_canonical_graph_symplectic_centralizers
      (K := PSL3Four.F4) (by norm_num) card_F4 (le_refl 3) C (Or.inl hC1)).2.2.2.2.2.2
      (Or.inr ⟨hC1, by decide⟩)
    rw [hHC]
    refine oddCore_eq_bot_of_mulEquiv (centralizerConjEquivMap (inner S3)
      (LinearFlag.conjAut 3 PSL3Four.F4 H)
      (LinearFlag.conjAut 3 PSL3Four.F4 C * LinearFlag.dualAut 3 PSL3Four.F4)).symm ?_
    refine hcan.2 _ (inner_le_map_conj (le_refl _) _) ?_
    rintro ⟨-, hK2, -⟩
    rw [card_F4] at hK2
    norm_num at hK2
  ·
    have hE : LinearFlag.conjAut 3 PSL3Four.F4 A *
        LinearFlag.fieldAut 3 PSL3Four.F4 PSL3Four.frob ∈
          LinearFlag.semilinearAutGroup 3 PSL3Four.F4 :=
      mul_mem (LinearFlag.linearAutGroup_le_semilinearAutGroup
        (LinearFlag.conjAut_mem_linearAutGroup A)) (LinearFlag.fieldAut_mem_semilinearAutGroup _)
    exact UnbalancedCatalog.even_linear_semilinear_involution_full_centralizer_odd_core
      (le_refl 3) (by norm_num) card_F4 (le_refl _) hE hord

end CFSG.Sporadic.ONOddCore
