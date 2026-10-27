module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofSplit

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.HighestRoot

namespace KS11Lie4Proof

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Chevalley CFSG.ComponentClassification.UnbalancedCatalog

variable {K : Type} [Field K]

section LongTorusFive

variable {ζ : Kˣ} (hζ : 5 ≤ orderOf ζ)
include hζ

theorem eq_zero_of_zpow_eq_one_of_small_five {d : ℤ} (hd : -4 ≤ d ∧ d ≤ 4) (h : ζ ^ d = 1) :
    d = 0 := by
  rw [← orderOf_dvd_iff_zpow_eq_one] at h
  by_contra hd0
  have h1 := Int.le_of_dvd (abs_pos.mpr hd0) ((dvd_abs _ _).mpr h)
  have h2 : (5 : ℤ) ≤ orderOf ζ := by exact_mod_cast hζ
  have h3 : |d| ≤ 4 := abs_le.mpr ⟨by omega, by omega⟩
  omega

theorem rootCharKernel_torusA_of_five_le :
    rootCharKernel (fun j => ζ ^ Tag.G2.cartan g2ia j) = {g2v, -g2v} := by
  ext α
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hα, hχ⟩
    rw [rootChar_torusA] at hχ
    have hb : -4 ≤ 2 * α g2ia + -1 * α g2ir ∧ 2 * α g2ia + -1 * α g2ir ≤ 4 := by
      rcases g2_root_cases hα with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;> decide
    have h0 := eq_zero_of_zpow_eq_one_of_small_five hζ hb hχ
    rcases g2_root_cases hα with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> first | exact Or.inl rfl | exact Or.inr rfl | (revert h0; decide)
  · rintro (rfl | rfl)
    · refine ⟨isRoot_g2v, ?_⟩
      rw [rootChar_torusA]
      exact zpow_zero ζ
    · refine ⟨IsRoot.neg isRoot_g2v, ?_⟩
      rw [rootChar_torusA]
      exact zpow_zero ζ

theorem stabilizer_le_torusA_of_five_le :
    rootCharStabilizerSubgroup (fun j => ζ ^ Tag.G2.cartan g2ia j) ≤
      kernelReflectionGroup (fun j => ζ ^ Tag.G2.cartan g2ia j) := by
  intro w hw
  have hf : ∀ (u : Fin Tag.G2.rank → ℤ), IsRoot .G2 u →
      -2 ≤ 2 * u g2ia + -1 * u g2ir ∧ 2 * u g2ia + -1 * u g2ir ≤ 2 := fun u hu => by
    rcases g2_root_cases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> decide
  have key : ∀ (v : Fin Tag.G2.rank → ℤ), IsRoot .G2 v →
      (2 * (w • v) g2ia + -1 * (w • v) g2ir) - (2 * v g2ia + -1 * v g2ir) = 0 :=
    fun v hv => by
      have h0 : rootChar (fun j => ζ ^ Tag.G2.cartan g2ia j) (w • v) =
          rootChar (fun j => ζ ^ Tag.G2.cartan g2ia j) v := hw v
      rw [rootChar_torusA, rootChar_torusA] at h0
      have h1 : ζ ^ ((2 * (w • v) g2ia + -1 * (w • v) g2ir) -
          (2 * v g2ia + -1 * v g2ir)) = 1 := by
        rw [zpow_sub, h0, mul_inv_cancel]
      have h2 := hf v hv
      have h3 := hf (w • v) (IsRoot.smul hv w)
      refine eq_zero_of_zpow_eq_one_of_small_five hζ ?_ h1
      omega
  have ka := key g2a isRoot_g2a
  have kr := key g2r isRoot_g2r
  have hinv : ∀ i : Fin Tag.G2.rank, (simple .G2 i)⁻¹ = simple .G2 i :=
    (coxeterSystem .G2).inv_simple
  rcases g2_weyl_cases w with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [weyl_G2_ext (w := w) (w' := 1) (by rw [h1, one_smul]) (by rw [h2, one_smul])]
    exact one_mem _
  rotate_left 9
  ·
    refine Subgroup.subset_closure ⟨simple .G2 g2ir * simple .G2 g2ia, g2ir, ?_,
      weyl_G2_ext ?_ ?_⟩
    · have e : (simple .G2 g2ir * simple .G2 g2ia) • (Pi.single g2ir 1 : Fin Tag.G2.rank → ℤ) =
          g2v := by
        rw [mul_smul, simple_smul, simple_smul]
        exact List.ofFn_injective (by decide +kernel)
      rw [e, rootCharKernel_torusA_of_five_le hζ]
      exact Or.inl rfl
    · rw [h1]
      simp only [mul_inv_rev, hinv, mul_smul, simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    · rw [h2]
      simp only [mul_inv_rev, hinv, mul_smul, simple_smul]
      exact List.ofFn_injective (by decide +kernel)
  all_goals
    exfalso
    rw [h1] at ka
    rw [h2] at kr
    revert ka kr
    decide

section CertContext


theorem toralCentralizer_torusA_of_five_le :
    toralCentralizer .G2 K (fun j => ζ ^ Tag.G2.cartan g2ia j) =
      torusGroup .G2 K ⊔ (rootSubgroup .G2 K g2δ ⊔ rootSubgroup .G2 K (-g2δ)) := by
  rw [toralCentralizer_eq_toralRootGroup_of_le (stabilizer_le_torusA_of_five_le hζ),
    toralRootGroup, rootCharKernel_torusA_of_five_le hζ, rootSpan_pair]
  rfl

end CertContext

end LongTorusFive

section Cent


theorem mem_range_rhoV_of_torus {t : ModGL .G2 K} (ht : t ∈ torusGroup .G2 K)
    (htc : t * pinnedX .G2 K g2e0 1 = pinnedX .G2 K g2e0 1 * t) :
    t ∈ (rhoV K).range := by
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  have his : IsRoot .G2 g2e0 := isRoot_single .G2 g2l
  have h1 := rootDiagUnit_conj_pinnedX l his 1
  rw [htc, mul_inv_cancel_right] at h1
  have h2 := pinnedX_injective .G2 K g2e0 h1
  rw [mul_one] at h2
  have hχ : rootChar l g2e0 = 1 := Units.ext (by rw [Units.val_one]; exact h2.symm)
  rw [rootChar_g2] at hχ
  have e1 : g2e0 g2ia = 1 := by decide
  have e2 : g2e0 g2ir = 0 := by decide
  rw [e1, e2, zpow_one, zpow_zero, mul_one] at hχ
  refine ⟨HSL (l g2ir), ?_⟩
  rw [rhoV_HSL]
  congr 1
  funext j
  rcases fin_G2_cases j with rfl | rfl
  · rw [Pi.mulSingle_eq_of_ne (by decide : g2ia ≠ g2ir)]
    exact hχ.symm
  · rw [Pi.mulSingle_eq_same]

theorem mem_g2ShortSL2_of_mem_sup {x : adjointGroup .G2 K}
    (hx : (x : ModGL .G2 K) ∈
      torusGroup .G2 K ⊔ (rootSubgroup .G2 K g2δ ⊔ rootSubgroup .G2 K (-g2δ)))
    (hxM : x ∈ Subgroup.centralizer (g2LongSL2 K : Set (adjointGroup .G2 K))) :
    x ∈ g2ShortSL2 K := by
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right _ _
    (torusGroup_le_normalizer_rootPair (K := K) (isRoot_g2δ))
  have hx' : (x : ModGL .G2 K) ∈
      ((torusGroup .G2 K ⊔ (rootSubgroup .G2 K g2δ ⊔ rootSubgroup .G2 K (-g2δ)) :
        Subgroup (ModGL .G2 K)) : Set (ModGL .G2 K)) := hx
  rw [hset] at hx'
  obtain ⟨t', ht', u, hu, htu⟩ := hx'
  have hv1 : pinnedX .G2 K g2e0 1 ∈ rootSubgroup .G2 K g2e0 ⊔ rootSubgroup .G2 K (-g2e0) :=
    Subgroup.mem_sup_left (mem_rootSubgroup.mpr ⟨1, rfl⟩)
  have hv1C : pinnedX .G2 K g2e0 1 ∈ adjointGroup .G2 K := pinnedX_mem_adjointGroup _ _
  have hc1 : (x : ModGL .G2 K) * pinnedX .G2 K g2e0 1 = pinnedX .G2 K g2e0 1 * x :=
    (congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hxM ⟨_, hv1C⟩ hv1)).symm
  have hc2 : Commute u (pinnedX .G2 K g2e0 1) :=
    (KS11Lie2Proof.g2_commute' hv1 hu).symm
  have htc : t' * pinnedX .G2 K g2e0 1 = pinnedX .G2 K g2e0 1 * t' := by
    have e : t' = (x : ModGL .G2 K) * u⁻¹ := by
      rw [← htu]
      group
    rw [e]
    calc (x : ModGL .G2 K) * u⁻¹ * pinnedX .G2 K g2e0 1 =
        (x : ModGL .G2 K) * (u⁻¹ * pinnedX .G2 K g2e0 1) := by group
      _ = (x : ModGL .G2 K) * (pinnedX .G2 K g2e0 1 * u⁻¹) := by
          rw [(Commute.inv_left hc2).eq]
      _ = pinnedX .G2 K g2e0 1 * ((x : ModGL .G2 K) * u⁻¹) := by
          rw [← mul_assoc, hc1, mul_assoc]
  have ht'M := mem_range_rhoV_of_torus ht' htc
  rw [← range_rhoV] at hu
  rw [mem_g2ShortSL2_iff, ← htu]
  exact mul_mem ht'M hu

theorem mem_g2ShortSL2_of_mem_centralizer [Finite K] (hK6 : 6 ≤ Nat.card K)
    {x : adjointGroup .G2 K}
    (hxM : x ∈ Subgroup.centralizer (g2LongSL2 K : Set (adjointGroup .G2 K))) :
    x ∈ g2ShortSL2 K := by
  obtain ⟨μ, hμ⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hμo : orderOf μ = Nat.card K - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hμ, Nat.card_units]
  have hμ5 : 5 ≤ orderOf μ := by omega
  set y : adjointGroup .G2 K :=
    ⟨simpleRootSL2 .G2 K g2ia (HSL μ), simpleRootSL2_mem_adjointGroup _ _⟩
  have hyM : y ∈ g2LongSL2 K := mem_g2LongSL2_iff.mpr ⟨HSL μ, rfl⟩
  have hy : (y : ModGL .G2 K) = rootDiagUnit .G2 (fun j => μ ^ Tag.G2.cartan g2ia j) :=
    rhoA_HSL μ
  have hxy : x ∈ Subgroup.centralizer ({y} : Set (adjointGroup .G2 K)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hxM y hyM).symm
  have hxeq : toralCentralizer .G2 K (fun j => μ ^ Tag.G2.cartan g2ia j) =
      torusGroup .G2 K ⊔ (rootSubgroup .G2 K g2δ ⊔ rootSubgroup .G2 K (-g2δ)) :=
    toralCentralizer_torusA_of_five_le hμ5
  have hx : (x : ModGL .G2 K) ∈
      torusGroup .G2 K ⊔ (rootSubgroup .G2 K g2δ ⊔ rootSubgroup .G2 K (-g2δ)) := by
    rw [← hxeq, ← mem_centralizer_iff_toral hy]
    exact hxy
  exact mem_g2ShortSL2_of_mem_sup hx hxM

end Cent

end KS11Lie4Proof

end CFSG.RankThree.PartTwo.Sec11
