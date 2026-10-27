module

public import CFSG.RankThree.Chevalley.EvenTrialityElementaryNine
public import CFSG.LieType.Chevalley.TrialityAllCharTorusCoordinates
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate117
public import CFSG.RankThree.Chevalley.EvenFourCommutingSL2
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Lemma83
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Cardinalities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
public import CFSG.Walter.Defs

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

theorem triality_D4_commuting_faithful_extension_and_fixed_SL2 (K : Type) [Field K]
    (σ : K ≃+* K) (hσ : σ ^ 3 = 1) :
    ∃ (ι : SL2 K →* graphFixedRootGroup .D4 K σ.toRingHom)
      (η : SL2 (fixSubfield σ) →* graphFixedRootGroup .D4 K σ.toRingHom),
      Function.Injective ι ∧ Function.Injective η ∧ ∀ A B, ι A * η B = η B * ι A := by
  obtain ⟨-, -, -, -, hfixed, -⟩ := triality_all_characteristic_faithful_torus_coordinates K σ hσ
  have h3 : ∀ c : K, σ (σ (σ c)) = c := fun c => by rw [← ringEquiv_pow_three_apply, hσ]; rfl
  set a₁ : Fin TwistTag.D4.foldedTag.rank := ⟨0, by decide⟩
  set a₂ : Fin TwistTag.D4.foldedTag.rank := ⟨1, by decide⟩
  set R₁ := orbitRankOneHom TwistTag.D4 K σ.toRingHom a₁
  set R₂ := orbitRankOneHom TwistTag.D4 K σ.toRingHom a₂
  have hL₁ : ∀ c : K, c ∈ orbitField TwistTag.D4 K σ.toRingHom a₁ := fun c => by
    rw [orbitField_D4_zero_eq_top σ h3]
    exact Subfield.mem_top c
  let f₁ : K →+* orbitField TwistTag.D4 K σ.toRingHom a₁ := (RingHom.id K).codRestrict _ hL₁
  have hle : fixSubfield σ ≤ orbitField TwistTag.D4 K σ.toRingHom a₂ := fun c hc =>
    (mem_orbitField_D4_one σ).2 hc
  let f₂ : fixSubfield σ →+* orbitField TwistTag.D4 K σ.toRingHom a₂ := Subfield.inclusion hle
  have hj : ∀ k, (TwistTag.D4.perm ^ k) (TwistTag.D4.orbitMin a₂) = ⟨2, by decide⟩ := fun k => by
    have h := TwistTag.D4.perm_pow_mem_orbit (TwistTag.D4.orbitMin_mem a₂) k
    have h3' : TwistTag.D4.orbit a₂ = {⟨2, by decide⟩} := by decide
    rwa [h3', Finset.mem_singleton] at h
  have hR₂Q : R₂.range ≤ rootSubgroup TwistTag.D4.tag K (Pi.single ⟨2, by decide⟩ 1) ⊔
      rootSubgroup TwistTag.D4.tag K (-Pi.single ⟨2, by decide⟩ 1) := by
    rw [orbitRankOneHom_range, Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · rw [SetLike.mem_coe]
      dsimp only
      rw [coe_orbitX]
      refine Subgroup.list_prod_mem _ fun x hx => ?_
      obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
      rw [hj k, ← pinnedX_single]
      exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨_, rfl⟩)
    · rw [SetLike.mem_coe]
      dsimp only
      rw [coe_orbitY]
      refine Subgroup.list_prod_mem _ fun x hx => ?_
      obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
      rw [hj k, ← pinnedX_neg_single]
      exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨_, rfl⟩)
  set J : Subgroup (ModGL TwistTag.D4.tag K) := Subgroup.closure
    {g | ∃ i ∈ TwistTag.D4.orbit a₁, ∃ c : K, g = xUnit TwistTag.D4.tag K i c ∨
      g = yUnit TwistTag.D4.tag K i c} with hJ
  have hR₁J : R₁.range ≤ J := by
    rw [orbitRankOneHom_range, Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · rw [SetLike.mem_coe]
      dsimp only
      rw [coe_orbitX]
      refine Subgroup.list_prod_mem _ fun x hx => ?_
      obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
      exact Subgroup.subset_closure ⟨_, TwistTag.D4.perm_pow_mem_orbit
        (TwistTag.D4.orbitMin_mem a₁) k, _, Or.inl rfl⟩
    · rw [SetLike.mem_coe]
      dsimp only
      rw [coe_orbitY]
      refine Subgroup.list_prod_mem _ fun x hx => ?_
      obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
      exact Subgroup.subset_closure ⟨_, TwistTag.D4.perm_pow_mem_orbit
        (TwistTag.D4.orbitMin_mem a₁) k, _, Or.inr rfl⟩
  have hNC : ∀ a, (orbitN .D4 K σ.toRingHom a 1 : ModGL TwistTag.D4.tag K) ∈
      graphFixedRootGroup .D4 K σ.toRingHom := fun a => by
    rw [orbitN, Subgroup.coe_mul, Subgroup.coe_mul]
    exact mul_mem (mul_mem (graphFixedPosUnipotent_le_graphFixedRootGroup _ K σ.toRingHom
      (orbitX_mem_graphFixedPosUnipotent _ σ.toRingHom a _))
      (graphFixedNegUnipotent_le_graphFixedRootGroup _ K σ.toRingHom
        (orbitY_mem_graphFixedNegUnipotent _ σ.toRingHom a _)))
      (graphFixedPosUnipotent_le_graphFixedRootGroup _ K σ.toRingHom
        (orbitX_mem_graphFixedPosUnipotent _ σ.toRingHom a _))
  set seq : List (Fin TwistTag.D4.foldedTag.rank) := [a₁, a₂]
  set h : ModGL TwistTag.D4.tag K :=
    (seq.map fun a => (orbitN .D4 K σ.toRingHom a 1 : ModGL TwistTag.D4.tag K)).reverse.prod
  have hhC : h ∈ graphFixedRootGroup .D4 K σ.toRingHom :=
    Subgroup.list_prod_mem _ fun x hx => by
      obtain ⟨a, -, rfl⟩ := List.mem_map.1 (List.mem_reverse.1 hx)
      exact hNC a
  have hηQ : ∀ x, (MulAut.conj h).toMonoidHom.comp R₂ x ∈
      rootSubgroup TwistTag.D4.tag K (d4Vec ![1, 1, 2, 1]) ⊔
        rootSubgroup TwistTag.D4.tag K (-d4Vec ![1, 1, 2, 1]) := fun x => by
    rw [← d4_fold_root, ← map_conj_orbitN_list_rootPair .D4 σ.toRingHom seq
      (isRoot_single _ _)]
    exact ⟨_, hR₂Q ⟨_, rfl⟩, rfl⟩
  have hR₁C : ∀ A, R₁ A ∈ graphFixedRootGroup .D4 K σ.toRingHom := fun A => (hfixed a₁).1 ⟨A, rfl⟩
  have hR₂C : ∀ A, R₂ A ∈ graphFixedRootGroup .D4 K σ.toRingHom := fun A => (hfixed a₂).1 ⟨A, rfl⟩
  refine ⟨(R₁.comp (Matrix.SpecialLinearGroup.map f₁)).codRestrict _ fun A => hR₁C _,
    ((MulAut.conj h).toMonoidHom.comp (R₂.comp (Matrix.SpecialLinearGroup.map f₂))).codRestrict
      _ fun A => mul_mem (mul_mem hhC (hR₂C _)) (inv_mem hhC), fun A B hAB => ?_,
    fun A B hAB => ?_, fun A B => ?_⟩
  · exact SL2_map_injective f₁ ((hfixed a₁).2 (congrArg Subtype.val hAB))
  · exact SL2_map_injective f₂
      ((hfixed a₂).2 ((MulAut.conj h).injective (congrArg Subtype.val hAB)))
  ·
    obtain ⟨hθ, hcheck⟩ := d4_outer_theta_check
    have hgen : ∀ x ∈ {g | ∃ i ∈ TwistTag.D4.orbit a₁, ∃ c : K,
        g = xUnit TwistTag.D4.tag K i c ∨ g = yUnit TwistTag.D4.tag K i c},
        ∀ y ∈ ((rootSubgroup TwistTag.D4.tag K (d4Vec ![1, 1, 2, 1]) ⊔
          rootSubgroup TwistTag.D4.tag K (-d4Vec ![1, 1, 2, 1]) : Subgroup _) :
            Set (ModGL TwistTag.D4.tag K)), x * y = y * x := by
      rintro x ⟨i, hi, c, hx⟩ y hy
      have hi2 : i ≠ ⟨2, by decide⟩ := by
        rintro rfl
        exact absurd hi (by decide)
      obtain ⟨hi1, h0, hp, hm⟩ := hcheck i hi2
      have hxQ : x ∈ rootSubgroup TwistTag.D4.tag K (Pi.single i 1) ⊔
          rootSubgroup TwistTag.D4.tag K (-Pi.single i 1) := by
        rcases hx with rfl | rfl
        · rw [← pinnedX_single]
          exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨_, rfl⟩)
        · rw [← pinnedX_neg_single]
          exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨_, rfl⟩)
      exact commute_of_mem_rootPair_of_check hi1 hθ h0 hp hm hxQ hy
    have hcomm := closure_commute hgen
    rw [Subgroup.closure_eq] at hcomm
    exact Subtype.ext (hcomm _ (hR₁J ⟨_, rfl⟩) _ (hηQ _))

end CFSG.RankThree.Chevalley
