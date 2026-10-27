module

public import CFSG.RankThree.Chevalley.EvenTwistedE6FourCommutingSL2
public import CFSG.RankThree.Chevalley.CubicMonomialElementaryNine
public import CFSG.LieType.Chevalley.EvenTrialityParameterData
public import CFSG.Walter.PSL2Facts.Even

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint

@[expose] def d4Vec (c : Fin 4 → ℤ) : Fin TwistTag.D4.tag.rank → ℤ := c

theorem d4_fold_root :
    [⟨0, by decide⟩, ⟨1, by decide⟩].foldl (fun v a => TwistTag.D4.orbitReflection a • v)
      (Pi.single ⟨2, by decide⟩ 1) = d4Vec ![1, 1, 2, 1] := by
  simp only [TwistTag.orbitReflection, wordProd_smul]
  decide +kernel

theorem d4_outer_theta_check :
    RootOps.isRootB TwistTag.D4.tag (d4Vec ![1, 1, 2, 1]) = true ∧
    ∀ j : Fin TwistTag.D4.tag.rank, j ≠ ⟨2, by decide⟩ →
      RootOps.isRootB TwistTag.D4.tag (Pi.single j 1) = true ∧
      iform (Pi.single j 1) (d4Vec ![1, 1, 2, 1]) = 0 ∧
      RootOps.isRootB TwistTag.D4.tag (Pi.single j 1 + d4Vec ![1, 1, 2, 1]) = false ∧
      RootOps.isRootB TwistTag.D4.tag (Pi.single j 1 - d4Vec ![1, 1, 2, 1]) = false := by
  decide +kernel

theorem injective_of_ker_scalar_of_charTwo {L : Type*} [Field L] [CharP L 2] {G : Type*} [Group G]
    {R : SL2 L →* G}
    (hR : ∀ g ∈ R.ker, ∃ l : Lˣ, (l : L) ^ 2 = 1 ∧
      (g : Matrix (Fin 2) (Fin 2) L) = (l : L) • (1 : Matrix (Fin 2) (Fin 2) L)) :
    Function.Injective R := by
  rw [injective_iff_map_eq_one]
  intro g hg
  obtain ⟨l, hl, hgl⟩ := hR g (MonoidHom.mem_ker.2 hg)
  have hl1 : (l : L) = 1 := CharTwo.sq_injective (show (l : L) ^ 2 = 1 ^ 2 by rw [hl, one_pow])
  refine Subtype.ext ?_
  rw [hgl, hl1, one_smul, Matrix.SpecialLinearGroup.coe_one]

theorem SL2_map_injective {F F' : Type*} [Field F] [Field F'] (f : F →+* F') :
    Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin 2) f) := fun A B h => by
  ext p q
  have := congrArg (fun C : SL2 F' => (C : Matrix (Fin 2) (Fin 2) F') p q) h
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    Matrix.map_apply] at this
  exact f.injective this

@[expose] def cubeSL (F : Type*) [Field F] [CharP F 2] : SL2 F :=
  ⟨!![0, 1; 1, 1], by simp [Matrix.det_fin_two, CharTwo.neg_eq]⟩

theorem cubeSL_pow_three (F : Type*) [Field F] [CharP F 2] : cubeSL F ^ 3 = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  ext p q
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  fin_cases p <;> fin_cases q <;>
    simp [cubeSL, pow_succ, Matrix.mul_apply, Fin.sum_univ_two] <;>
    rw [one_add_one_eq_two, h2]

theorem cubeSL_ne_one (F : Type*) [Field F] [CharP F 2] : cubeSL F ≠ 1 := by
  intro h
  have := congrArg (fun C : SL2 F => (C : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp [cubeSL] at this

theorem cubeSL_sq_ne_one (F : Type*) [Field F] [CharP F 2] : cubeSL F ^ 2 ≠ 1 := by
  intro h
  have := congrArg (fun C : SL2 F => (C : Matrix (Fin 2) (Fin 2) F) 0 1) h
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one] at this
  simp [cubeSL, sq, Matrix.mul_apply, Fin.sum_univ_two] at this

theorem even_triality_commuting_rank_one_product_and_elementary_nine (K : Type) [Field K]
    [CharP K 2] (σ : K →+* K) (hσ : ∀ c, σ (σ (σ c)) = c) :
    (∃ Ψ : SL2 K × SL2 (trialityFixedField K σ) →* graphFixedRootGroup .D4 K σ,
      Function.Injective Ψ) ∧
    ∃ E : Subgroup (graphFixedRootGroup .D4 K σ), IsElementaryAbelian 3 E ∧ Nat.card E = 9 := by
  obtain ⟨Ro, -, -, -, -, -, hRorange, hRoC, hRoker, -⟩ :=
    exceptional_fixed_rank_one_central_image .D4 K σ ⟨0, by decide⟩
  obtain ⟨Rm, -, -, -, -, -, hRmrange, hRmC, hRmker, -⟩ :=
    exceptional_fixed_rank_one_central_image .D4 K σ ⟨1, by decide⟩
  have hLo : ∀ c : K, c ∈ orbitField .D4 K σ ⟨0, by decide⟩ := fun c => by
    rw [mem_orbitField, show (TwistTag.D4.orbit ⟨0, by decide⟩).card = 3 by decide]
    exact hσ c
  have hLm : trialityFixedField K σ ≤ orbitField .D4 K σ ⟨1, by decide⟩ := fun c hc => by
    rw [mem_orbitField, show (TwistTag.D4.orbit ⟨1, by decide⟩).card = 1 by decide, pow_one]
    exact hc
  let ιo : SL2 K →* SL2 (orbitField .D4 K σ ⟨0, by decide⟩) :=
    Matrix.SpecialLinearGroup.map ((RingHom.id K).codRestrict _ hLo)
  let ιm : SL2 (trialityFixedField K σ) →* SL2 (orbitField .D4 K σ ⟨1, by decide⟩) :=
    Matrix.SpecialLinearGroup.map (Subfield.inclusion hLm)
  let Ro' : SL2 K →* ModGL TwistTag.D4.tag K := Ro.comp ιo
  let Rm' : SL2 (trialityFixedField K σ) →* ModGL TwistTag.D4.tag K := Rm.comp ιm
  have hRo'inj : Function.Injective Ro' := fun A B h =>
    SL2_map_injective _ (injective_of_ker_scalar_of_charTwo hRoker h)
  have hRm'inj : Function.Injective Rm' := fun A B h =>
    SL2_map_injective _ (injective_of_ker_scalar_of_charTwo hRmker h)
  have hRoC' : Ro.range ≤ graphFixedRootGroup .D4 K σ := hRorange ▸ hRoC
  have hRmC' : Rm.range ≤ graphFixedRootGroup .D4 K σ := hRmrange ▸ hRmC
  have hNC : ∀ a, (orbitN .D4 K σ a 1 : ModGL TwistTag.D4.tag K) ∈
      graphFixedRootGroup .D4 K σ := fun a => by
    rw [orbitN, Subgroup.coe_mul, Subgroup.coe_mul]
    exact mul_mem (mul_mem (graphFixedPosUnipotent_le_graphFixedRootGroup _ K σ
      (orbitX_mem_graphFixedPosUnipotent _ σ a _)) (graphFixedNegUnipotent_le_graphFixedRootGroup
        _ K σ (orbitY_mem_graphFixedNegUnipotent _ σ a _)))
      (graphFixedPosUnipotent_le_graphFixedRootGroup _ K σ
        (orbitX_mem_graphFixedPosUnipotent _ σ a _))
  let ω : List (Fin TwistTag.D4.foldedTag.rank) := [⟨0, by decide⟩, ⟨1, by decide⟩]
  let n : ModGL TwistTag.D4.tag K :=
    (ω.map fun a => (orbitN .D4 K σ a 1 : ModGL TwistTag.D4.tag K)).reverse.prod
  have hnC : n ∈ graphFixedRootGroup .D4 K σ :=
    Subgroup.list_prod_mem _ fun x hx => by
      obtain ⟨a, -, rfl⟩ := List.mem_map.1 (List.mem_reverse.1 hx)
      exact hNC a
  have hj2 : ∀ k, (TwistTag.D4.perm ^ k) (TwistTag.D4.orbitMin ⟨1, by decide⟩) =
      ⟨2, by decide⟩ := fun k => by
    have h := TwistTag.D4.perm_pow_mem_orbit (TwistTag.D4.orbitMin_mem ⟨1, by decide⟩) k
    have h3 : TwistTag.D4.orbit ⟨1, by decide⟩ = {⟨2, by decide⟩} := by decide
    rwa [h3, Finset.mem_singleton] at h
  have hRmQ : Rm.range ≤ rootSubgroup TwistTag.D4.tag K (Pi.single ⟨2, by decide⟩ 1) ⊔
      rootSubgroup TwistTag.D4.tag K (-Pi.single ⟨2, by decide⟩ 1) := by
    rw [hRmrange, Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · rw [SetLike.mem_coe]
      dsimp only
      rw [coe_orbitX]
      refine Subgroup.list_prod_mem _ fun x hx => ?_
      obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
      rw [hj2 k, ← pinnedX_single]
      exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨_, rfl⟩)
    · rw [SetLike.mem_coe]
      dsimp only
      rw [coe_orbitY]
      refine Subgroup.list_prod_mem _ fun x hx => ?_
      obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
      rw [hj2 k, ← pinnedX_neg_single]
      exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨_, rfl⟩)
  have hθ : ∀ h, n * Rm' h * n⁻¹ ∈ rootSubgroup TwistTag.D4.tag K (d4Vec ![1, 1, 2, 1]) ⊔
      rootSubgroup TwistTag.D4.tag K (-d4Vec ![1, 1, 2, 1]) := fun h => by
    have hfold : ω.foldl (fun v a => TwistTag.D4.orbitReflection a • v)
        (Pi.single ⟨2, by decide⟩ 1) = d4Vec ![1, 1, 2, 1] := d4_fold_root
    rw [← hfold, ← map_conj_orbitN_list_rootPair .D4 σ ω (isRoot_single _ _)]
    exact ⟨_, hRmQ ⟨_, rfl⟩, rfl⟩
  obtain ⟨hθr, hcheck⟩ := d4_outer_theta_check
  have hcomm : ∀ g h, Ro' g * (n * Rm' h * n⁻¹) = (n * Rm' h * n⁻¹) * Ro' g := by
    intro g h
    have hy := hθ h
    have hle : Ro.range ≤ Subgroup.centralizer {n * Rm' h * n⁻¹} := by
      rw [hRorange, Subgroup.closure_le]
      have hj : ∀ k, (TwistTag.D4.perm ^ k) (TwistTag.D4.orbitMin ⟨0, by decide⟩) ≠
          ⟨2, by decide⟩ := fun k hk => by
        have h := TwistTag.D4.perm_pow_mem_orbit (TwistTag.D4.orbitMin_mem ⟨0, by decide⟩) k
        rw [hk] at h
        exact absurd h (by decide)
      rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · rw [SetLike.mem_coe]
        dsimp only
        rw [coe_orbitX]
        refine Subgroup.list_prod_mem _ fun x hx => ?_
        obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
        obtain ⟨hjr, h0, hp, hm⟩ := hcheck _ (hj k)
        rw [Subgroup.mem_centralizer_singleton_iff, ← pinnedX_single]
        exact commute_of_mem_rootPair_of_check hjr hθr h0 hp hm
          (Subgroup.mem_sup_left (Subgroup.subset_closure ⟨_, rfl⟩)) hy
      · rw [SetLike.mem_coe]
        dsimp only
        rw [coe_orbitY]
        refine Subgroup.list_prod_mem _ fun x hx => ?_
        obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
        obtain ⟨hjr, h0, hp, hm⟩ := hcheck _ (hj k)
        rw [Subgroup.mem_centralizer_singleton_iff, ← pinnedX_neg_single]
        exact commute_of_mem_rootPair_of_check hjr hθr h0 hp hm
          (Subgroup.mem_sup_right (Subgroup.subset_closure ⟨_, rfl⟩)) hy
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle ⟨_, rfl⟩)
  let A : SL2 K →* graphFixedRootGroup .D4 K σ := Ro'.codRestrict _ fun g => hRoC' ⟨_, rfl⟩
  let B : SL2 (trialityFixedField K σ) →* graphFixedRootGroup .D4 K σ :=
    ((MulAut.conj n).toMonoidHom.comp Rm').codRestrict _ fun h =>
      mul_mem (mul_mem hnC (hRmC' ⟨_, rfl⟩)) (inv_mem hnC)
  have hAB : ∀ g h, Commute (A g) (B h) := fun g h => Subtype.ext (hcomm g h)
  let Ψ : SL2 K × SL2 (trialityFixedField K σ) →* graphFixedRootGroup .D4 K σ :=
    MonoidHom.noncommCoprod A B hAB
  have hΨinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨g, h⟩ hgh
    have h1 : Ro' g * (n * Rm' h * n⁻¹) = 1 := congrArg Subtype.val hgh
    have hg : Ro' g = (n * Rm' h * n⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have hgc : g ∈ Subgroup.center (SL2 K) := Subgroup.mem_center_iff.2 fun x => by
      apply hRo'inj
      rw [map_mul, map_mul, hg]
      exact (Commute.inv_right (hcomm x h)).eq
    rw [CFSG.Walter.sl2_center_eq_bot_of_charTwo, Subgroup.mem_bot] at hgc
    subst hgc
    rw [map_one, one_mul] at h1
    have h2 : Rm' h = 1 := by
      calc Rm' h = n⁻¹ * (n * Rm' h * n⁻¹) * n := by group
        _ = 1 := by rw [h1]; group
    have h3 : h = 1 := hRm'inj (by rw [h2, map_one])
    rw [h3]
    rfl
  refine ⟨⟨Ψ, hΨinj⟩, ?_⟩
  have hpair : ∀ i j : ℕ, (cubeSL K, (1 : SL2 (trialityFixedField K σ))) ^ i *
      ((1 : SL2 K), cubeSL (trialityFixedField K σ)) ^ j =
        (cubeSL K ^ i, cubeSL (trialityFixedField K σ) ^ j) := fun i j => by
    rw [Prod.pow_mk, Prod.pow_mk, one_pow, one_pow, Prod.mk_mul_mk, mul_one, one_mul]
  have hcube : ∀ (F : Type) [Field F] [CharP F 2] (i : ℕ), i < 3 → cubeSL F ^ i = 1 → i = 0 :=
    fun F _ _ i hi h => by
      interval_cases i
      · rfl
      · exact absurd (by simpa using h) (cubeSL_ne_one F)
      · exact absurd h (cubeSL_sq_ne_one F)
  refine exists_isElementaryAbelian_nine_of_pair (x := Ψ (cubeSL K, 1))
    (y := Ψ (1, cubeSL (trialityFixedField K σ))) ?_ ?_ ?_ ?_
  · rw [← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk, mul_one, one_mul, mul_one, one_mul]
  · rw [← map_pow, Prod.pow_mk, cubeSL_pow_three, one_pow, Prod.mk_one_one, map_one]
  · rw [← map_pow, Prod.pow_mk, cubeSL_pow_three, one_pow, Prod.mk_one_one, map_one]
  · intro i j hi hj h
    rw [← map_pow, ← map_pow, ← map_mul, hpair] at h
    have h' := hΨinj (h.trans (map_one Ψ).symm)
    rw [Prod.mk_eq_one] at h'
    exact ⟨hcube K i hi h'.1, hcube _ j hj h'.2⟩

end CFSG.RankThree.Chevalley
