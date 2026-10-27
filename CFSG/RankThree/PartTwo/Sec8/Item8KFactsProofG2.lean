module

public import CFSG.RankThree.PartTwo.Sec8.Item83ProofDefs
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofG2
import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofTwist
import CFSG.RankThree.PartTwo.Sec8.Item86Res2ProofIndep

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item83Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.HighestRoot
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof


theorem map_baseChangeGL_rootSubgroup_le {τ : Tag} {k K : Type} [Field k] [Field K]
    (ι : k →+* K) (α : Fin τ.rank → ℤ) :
    (rootSubgroup τ k α).map (baseChangeGL ι) ≤ rootSubgroup τ K α := by
  rw [rootSubgroup, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
  rw [baseChangeGL_pinnedX]
  exact Subgroup.subset_closure ⟨ι c, rfl⟩


theorem g2Incl_mem_g2LongSL2 {K : Type} [Field K] (σ : K ≃+* K)
    {y : adjointGroup .G2 (fixSubfield σ)} (hy : y ∈ g2LongSL2 (fixSubfield σ)) :
    KFacts.g2Incl σ y ∈ g2LongSL2 K := by
  have hle : (rootSubgroup .G2 (fixSubfield σ) g2e0 ⊔ rootSubgroup .G2 (fixSubfield σ) (-g2e0)).map
      (baseChangeGL (fixSubfield σ).subtype) ≤
        rootSubgroup .G2 K g2e0 ⊔ rootSubgroup .G2 K (-g2e0) := by
    rw [Subgroup.map_sup]
    exact sup_le_sup (map_baseChangeGL_rootSubgroup_le _ _)
      (map_baseChangeGL_rootSubgroup_le _ _)
  exact hle ⟨_, hy, rfl⟩

theorem eq_one_of_mem_g2LongSL2_of_mem_g2ShortSL2 {F : Type} [Field F] [CharP F 2]
    {y : adjointGroup .G2 F} (hyM : y ∈ g2LongSL2 F) (hyS : y ∈ g2ShortSL2 F) : y = 1 := by
  obtain ⟨eM⟩ := nonempty_mulEquiv_g2LongSL2 (K := F)
  set w := eM.symm ⟨y, hyM⟩ with hw
  have hwc : w ∈ Subgroup.center (SL2 F) := by
    rw [Subgroup.mem_center_iff]
    intro A
    apply eM.injective
    rw [map_mul, map_mul, hw, MulEquiv.apply_symm_apply]
    exact Subtype.ext (g2Short_commute_g2Long (m := ((eM A : g2LongSL2 F) : adjointGroup .G2 F))
      hyS (eM A).2).symm
  rw [Item86ResProof.center_specialLinearGroup_two_eq_bot, Subgroup.mem_bot] at hwc
  have : (⟨y, hyM⟩ : g2LongSL2 F) = 1 := by
    rw [← MulEquiv.apply_symm_apply eM ⟨y, hyM⟩, ← hw, hwc, map_one]
  exact congrArg Subtype.val this


theorem inSubgroup_perfectResidual_centralizer_eq_g2ShortSL2 {K : Type} [Field K] [Finite K]
    (hK3 : ringChar K ≠ 3) (hK4 : 4 ≤ Nat.card K) {z : adjointGroup .G2 K}
    (hz : z ∈ g2LongSL2 K) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    inSubgroup perfectResidual (Subgroup.centralizer ({z} : Set (adjointGroup .G2 K))) =
      g2ShortSL2 K := by
  have : Finite (ModGL .G2 K) := finite_modGL
  set C := Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)) with hC
  obtain ⟨hcomm, -⟩ := g2ThreeBCent_holds K hK3 hK4 z hz hz3 hz1
  refine le_antisymm ?_ ?_
  ·
    rintro _ ⟨x, hx, rfl⟩
    have h1 : perfectResidual C ≤ derivedSeries C 1 := iInf_le _ 1
    have h2 : derivedSeries C 1 ≤ (g2ShortSL2 K).comap C.subtype := by
      rw [derivedSeries_one, commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [Subgroup.mem_comap, commutatorElement_def, map_mul, map_mul, map_mul, map_inv,
        map_inv]
      exact hcomm a a.2 b b.2
    exact h2 (h1 hx)
  ·
    have hSC : g2ShortSL2 K ≤ C := by
      intro s hs
      rw [hC, Subgroup.mem_centralizer_singleton_iff]
      exact g2Short_commute_g2Long hs hz
    exact KFacts.le_inSubgroup_perfectResidual (isQuasisimple_g2ShortSL2 hK4).1 hSC

theorem kF83GTwo_holds : KF83GTwo := by
  intro K _ _ n hn hK σ hσ
  have hn1 : 1 ≤ n := hn.pos
  obtain ⟨-, hcardk⟩ :=
    CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield Nat.prime_two (by omega) hK σ
  rw [hσ, Nat.mul_div_cancel_left _ (by norm_num)] at hcardk
  have : Finite (fixSubfield σ) := Subtype.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP (fixSubfield σ) 2 := by
    have : Fintype (fixSubfield σ) := Fintype.ofFinite _
    exact charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hcardk])
  have : CharP K 2 := by
    have : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := 3 * n) (by rw [← Nat.card_eq_fintype_card, hK])
  have hK3 : ringChar K ≠ 3 := by rw [ringChar.eq K 2]; decide
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (3 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨eM⟩ := nonempty_mulEquiv_g2LongSL2 (K := fixSubfield σ)
  obtain ⟨eS⟩ := nonempty_mulEquiv_g2ShortSL2 (K := fixSubfield σ)
  have hM3 := Sec11.KS11Lie2Proof.sl2Three_pow_three (fixSubfield σ)
  have hM1 : Sec11.KS11Lie2Proof.sl2Three (fixSubfield σ) ≠ 1 := by
    intro h
    apply Sec11.KS11Lie2Proof.sl2Three_ne_smul (k := fixSubfield σ) 1
    rw [h, one_smul]
    rfl
  set y₁ : adjointGroup .G2 (fixSubfield σ) :=
    ((eM (Sec11.KS11Lie2Proof.sl2Three _) : g2LongSL2 (fixSubfield σ)) :
      adjointGroup .G2 (fixSubfield σ)) with hy₁
  set y₂ : adjointGroup .G2 (fixSubfield σ) :=
    ((eS (Sec11.KS11Lie2Proof.sl2Three _) : g2ShortSL2 (fixSubfield σ)) :
      adjointGroup .G2 (fixSubfield σ)) with hy₂
  have hy₁M : y₁ ∈ g2LongSL2 (fixSubfield σ) := (eM _).2
  have hy₂S : y₂ ∈ g2ShortSL2 (fixSubfield σ) := (eS _).2
  have hy₁3 : y₁ ^ 3 = 1 := by
    rw [hy₁, ← Subgroup.coe_pow, ← map_pow, hM3, map_one, Subgroup.coe_one]
  have hy₂3 : y₂ ^ 3 = 1 := by
    rw [hy₂, ← Subgroup.coe_pow, ← map_pow, hM3, map_one, Subgroup.coe_one]
  have hy₁1 : y₁ ≠ 1 := by
    intro h
    apply hM1
    apply eM.injective
    rw [map_one]
    exact Subtype.ext h
  have hy₂1 : y₂ ≠ 1 := by
    intro h
    apply hM1
    apply eS.injective
    rw [map_one]
    exact Subtype.ext h
  have hy₁₂ : y₁ * y₂ = y₂ * y₁ := (g2Short_commute_g2Long hy₂S hy₁M).symm
  have hy₂₁ : y₂ ∉ Subgroup.zpowers y₁ := by
    intro h
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp h
    have hy₂M : y₂ ∈ g2LongSL2 (fixSubfield σ) := hj ▸ zpow_mem hy₁M j
    exact hy₂1 (eq_one_of_mem_g2LongSL2_of_mem_g2ShortSL2 hy₂M hy₂S)
  refine ⟨y₁, y₂, hy₁3, hy₂3, hy₁₂, hy₁1, hy₂₁, ?_⟩
  have hz : KFacts.g2Incl σ y₁ ∈ g2LongSL2 K := g2Incl_mem_g2LongSL2 σ hy₁M
  have hz3 : KFacts.g2Incl σ y₁ ^ 3 = 1 := by rw [← map_pow, hy₁3, map_one]
  have hz1 : KFacts.g2Incl σ y₁ ≠ 1 := fun h =>
    hy₁1 (KFacts.g2Incl_injective σ (h.trans (map_one _).symm))
  have heq := inSubgroup_perfectResidual_centralizer_eq_g2ShortSL2 hK3 hK4 hz hz3 hz1
  obtain ⟨eSK⟩ := nonempty_mulEquiv_g2ShortSL2 (K := K)
  obtain ⟨eP⟩ := KFacts.nonempty_sl2_mulEquiv_projSL (F := K) hK
  exact ⟨((MulEquiv.subgroupCongr heq).trans eSK.symm).trans eP⟩

end CFSG.RankThree.PartTwo.Sec8.Item83Proof
