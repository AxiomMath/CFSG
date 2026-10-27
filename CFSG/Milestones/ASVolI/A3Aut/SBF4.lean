module

public import CFSG.Milestones.ASVolI.A3Aut.SBBase

public section

namespace CFSG.ASVolI

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.QuasithinUnique.Setup.X6
open CFSG.LieType.Ree.LargeReeCover (pairedTorusHom pairedTorusHom_apply f4i torusPair
  torusPair_apply torusPair_mem_reeGamma)
open scoped commutatorElement

theorem burnsideAut_not_isSolvable_of_isSimpleGroup {S : Type*} [Group S] [IsSimpleGroup S]
    (h : ∃ x y : S, x * y ≠ y * x) : ¬ Group.IsSolvable S := by
  obtain ⟨x, y, hxy⟩ := h
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator S) with hb | ht
  · exfalso
    apply hxy
    have hmem : ⁅x, y⁆ ∈ commutator S := by
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
    rw [hb, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem
  · haveI : Group.IsPerfect S := ⟨ht⟩
    exact Group.IsPerfect.not_isSolvable S

theorem burnsideAut_uSL_one_ne_one {K : Type*} [Field K] : uSL (1 : K) ≠ 1 := by
  intro h
  have h1 := congrArg (fun g : SL2 K => (g : Matrix (Fin 2) (Fin 2) K) 0 1) h
  simp [uSL] at h1

section LargeRee

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem burnsideAut_rankOneTorusTwo_le_reeFixedTorus
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    LargeReeInvolution.rankOneTorusTwo K a ≤ F4.reeFixedTorus K a := by
  rintro _ ⟨u, rfl⟩
  have h1 : torusPair (K := K) a (1, u) = pairedTorusHom (K := K) a (f4i 1) (f4i 2) u := by
    rw [torusPair_apply, pairedTorusHom_apply]
    simp [torusElt_one]
  have h2 : pairedTorusHom (K := K) a (f4i 1) (f4i 2) u ∈ torusGroup F4.tag K := by
    rw [pairedTorusHom_apply]
    exact mul_mem (torusElt_mem_torusGroup _ _) (torusElt_mem_torusGroup _ _)
  refine Subgroup.mem_inf.2 ⟨h2, ?_⟩
  rw [← h1]
  exact torusPair_mem_reeGamma a hK (1, u)

theorem burnsideAut_reeLocalBlock_one_eq
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    F4.reeLocalBlock K a ⟨1, by decide⟩ = LargeReeInvolution.rankOneGroupTwo K a := by
  have hn : canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨1, by decide⟩) ∈
      LargeReeInvolution.rankOneGroupTwo K a := Subgroup.subset_closure (Or.inr rfl)
  have hX : F4.reeFixedOrbitUnipotent K a ⟨1, by decide⟩ ≤
      LargeReeInvolution.rankOneGroupTwo K a := fun x hx =>
    Subgroup.subset_closure (Or.inl (Or.inl hx))
  have hle : F4.reeLocalBlock K a ⟨1, by decide⟩ ≤ LargeReeInvolution.rankOneGroupTwo K a := by
    refine sup_le hX ?_
    rw [← map_conj_reeFixedOrbitUnipotent]
    rintro _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem hn (hX hx)) (inv_mem hn)
  refine le_antisymm hle ?_
  have hnorm : ((F4.reeLocalBlock K a ⟨1, by decide⟩).subgroupOf
      (LargeReeInvolution.rankOneGroupTwo K a)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ((hx | hx) | hx)
    · exact Subgroup.le_normalizer (Subgroup.mem_sup_left hx)
    · exact reeFixedTorus_le_normalizer_reeLocalBlock ⟨1, by decide⟩
        (burnsideAut_rankOneTorusTwo_le_reeFixedTorus hK hx)
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      have hmap : (F4.reeLocalBlock K a ⟨1, by decide⟩).map
          (MulAut.conj (canonicalRep (coxeterSystem F4.tag) K
            (F4.fixedOrbitElement ⟨1, by decide⟩))).toMonoidHom =
            F4.reeLocalBlock K a ⟨1, by decide⟩ := by
        unfold reeLocalBlock
        rw [Subgroup.map_sup, map_conj_reeFixedOrbitUnipotent, map_conj_reeFixedOrbitNegUnipotent,
          sup_comm]
      exact CFSG.LieType.Chevalley.mem_normalizer_of_map_eq hmap
  have := (LargeReeInvolution.isSimpleGroup_rankOneGroupTwo ha hK).1
  have := hnorm
  have hdich : (F4.reeLocalBlock K a ⟨1, by decide⟩).subgroupOf
        (LargeReeInvolution.rankOneGroupTwo K a) = ⊥ ∨
      (F4.reeLocalBlock K a ⟨1, by decide⟩).subgroupOf
        (LargeReeInvolution.rankOneGroupTwo K a) = ⊤ :=
    IsSimpleGroup.eq_bot_or_eq_top_of_normal _
  rcases hdich with hbot | htop
  · exfalso
    obtain ⟨u, hu, hu1⟩ :=
      exists_ne_one_mem_reeFixedOrbitUnipotent (t := F4) (K := K) (a := a) ⟨1, by decide⟩
    have hmem : (⟨u, hX hu⟩ : ↥(LargeReeInvolution.rankOneGroupTwo K a)) ∈
        (F4.reeLocalBlock K a ⟨1, by decide⟩).subgroupOf (LargeReeInvolution.rankOneGroupTwo K a) :=
      Subgroup.mem_subgroupOf.2 (reeFixedOrbitUnipotent_le_reeLocalBlock ⟨1, by decide⟩ hu)
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hu1 (congrArg Subtype.val hmem)
  · intro g hg
    have hmem : (⟨g, hg⟩ : ↥(LargeReeInvolution.rankOneGroupTwo K a)) ∈
        (F4.reeLocalBlock K a ⟨1, by decide⟩).subgroupOf (LargeReeInvolution.rankOneGroupTwo K a) := by
      rw [htop]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 hmem

theorem burnsideAut_reeLocalBlock_not_isSolvable
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (j : Fin F4.fixedOrbitCount) : ¬ Group.IsSolvable ↥(F4.reeLocalBlock K a j) := by
  have hcases : j = ⟨0, by decide⟩ ∨ j = ⟨1, by decide⟩ := by
    have : ∀ j : Fin F4.fixedOrbitCount, j = ⟨0, by decide⟩ ∨ j = ⟨1, by decide⟩ := by decide
    exact this j
  rcases hcases with rfl | rfl
  · have hK4 : 4 ≤ Nat.card K := by
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    haveI := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hK4
    have hR : (largeReeA1Hom K a).range ≤ F4.reeLocalBlock K a ⟨0, by decide⟩ :=
      (largeReeA1Hom_range hK).le
    refine burnsideAut_not_isSolvable_of_perfect_hom (largeReeA1Hom K a) (g := uSL 1) ?_ hR
    intro h
    exact burnsideAut_uSL_one_ne_one (eq_one_of_largeReeA1Hom_eq_one a h)
  · have h2 : F4.reeLocalBlock K a ⟨1, by decide⟩ = LargeReeInvolution.rankOneGroupTwo K a :=
      burnsideAut_reeLocalBlock_one_eq ha hK
    rw [h2]
    obtain ⟨hs, hnc⟩ := LargeReeInvolution.isSimpleGroup_rankOneGroupTwo ha hK
    haveI := hs
    exact burnsideAut_not_isSolvable_of_isSimpleGroup hnc

theorem burnsideAut_solvBorel_largeRee
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    burnsideAut_SolvBorel ↥(F4.reeGamma K a)
      ((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a)) := by
  intro Y hUY hYs
  set Y' : Subgroup (ModGL F4.tag K) := Y.map (F4.reeGamma K a).subtype with hY'
  have hY'Γ : Y' ≤ F4.reeGamma K a := Subgroup.map_subtype_le Y
  have hUY' : F4.reeFixedPosUnipotent K a ≤ Y' := fun u hu =>
    ⟨⟨u, reeFixedPosUnipotent_le_reeGamma hu⟩, hUY (Subgroup.mem_subgroupOf.2 hu), rfl⟩
  have hY's : Group.IsSolvable ↥Y' :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.equivMapOfInjective Y _ Subtype.val_injective).symm.toMonoidHom)
      (MulEquiv.injective _)
  have hJ : ∀ j, j ∉ {j | canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j) ∈ Y'} := by
    intro j hj
    have hX : F4.reeFixedOrbitUnipotent K a j ≤ Y' :=
      (reeFixedOrbitUnipotent_le_reeFixedPosUnipotent j).trans hUY'
    have hY : F4.reeFixedOrbitNegUnipotent K a j ≤ Y' :=
      reeFixedOrbitNegUnipotent_le_of_posUnipotent hUY' (fixedOrbitElement_mem j) (h := 1)
        (one_mem _) (by rwa [one_mul]) (fun α hα => by
          rw [fixedOrbitElement_inv]
          exact height_fixedOrbitElement_smul_neg hα)
    have hle : F4.reeLocalBlock K a j ≤ Y' := sup_le hX hY
    exact burnsideAut_reeLocalBlock_not_isSolvable ha hK j
      (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle))
  have hY'B : Y' ≤ F4.reeFixedBorel K a := by
    have h := le_reeParabolic_of_posUnipotent_le hY'Γ hUY'
    rwa [Set.eq_empty_of_forall_notMem hJ, reeParabolic, Set.image_empty,
      Subgroup.closure_empty, sup_bot_eq] at h
  have hBN : F4.reeFixedBorel K a ≤
      Subgroup.normalizer (F4.reeFixedPosUnipotent K a : Set (ModGL F4.tag K)) := by
    intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨(sup_le torusGroup_le_normalizer_posUnipotent Subgroup.le_normalizer : borelGroup F4.tag K ≤ _)
        hx.1, Subgroup.le_normalizer hx.2⟩
  intro y hy
  rw [← Subgroup.subgroupOf_normalizer_eq reeFixedPosUnipotent_le_reeGamma]
  exact Subgroup.mem_subgroupOf.2 (hBN (hY'B ⟨y, hy, rfl⟩))

theorem burnsideAut_isSylowTwoOf_reeFixedPosUnipotent
    (a : ℕ) :
    CFSG.QuasithinUnique.IsSylowTwoOf
      ((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a)) ⊤ := by
  have : Finite (ModGL F4.tag K) := finite_modGL
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem F4.tag).length
  obtain ⟨PU, hPU⟩ := (large_Ree_Sylow_opposition F4 a K w₀ hw₀).1
  rw [← hPU]
  exact CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow PU

end LargeRee

theorem burnsideAut_solvBorel_2F4 :
    ∀ (X : Type) [Group X] [Finite X] (f : ℕ), Odd f → 3 ≤ f → CFSG.Quasithin.Is2F4 f X →
      ∀ S : Subgroup X, CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ → burnsideAut_SolvBorel X S := by
  intro X _ _ f _ _ hX S hS
  obtain ⟨a, K, _, _, _, ha, hfa, hK, ⟨e⟩⟩ := exists_mulEquiv_largeRee_model hX
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  have : Finite (ModGL F4.tag K) := finite_modGL
  exact burnsideAut_solvBorel_of_isSylow e (burnsideAut_isSylowTwoOf_reeFixedPosUnipotent a)
    (burnsideAut_solvBorel_largeRee ha hK') hS

end CFSG.ASVolI
