module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotPerfectBasic
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotCentralizerT

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps
  CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_mono map_perfectCore
  le_perfectCore_of_perfect perfectCore_eq_self_of_perfect)
open scoped commutatorElement

local instance twistedE6PilotPerfectTNeZeroTw : NeZero TwistTag.E6.tag.rank := ⟨by decide⟩

section Roots

theorem mem_parabolicRadicalRoots_setA_iff {α : Fin TwistTag.E6.tag.rank → ℤ} :
    α ∈ parabolicRadicalRoots TwistTag.E6.tag E6GraphLevi.setA ↔
      IsRoot TwistTag.E6.tag α ∧ 0 < height α ∧ α 1 ≠ 0 := by
  rw [mem_parabolicRadicalRoots_iff]
  refine and_congr_right fun _ => and_congr_right fun _ => ⟨fun ⟨i, hi, hαi⟩ => ?_, fun h =>
    ⟨1, fun h1 => h1 rfl, h⟩⟩
  have hi1 : i = 1 := by
    by_contra h
    exact hi h
  rw [hi1] at hαi
  exact hαi

theorem permLattice_mem_parabolicRadicalRoots_setA {α : Fin TwistTag.E6.tag.rank → ℤ}
    (hα : α ∈ parabolicRadicalRoots TwistTag.E6.tag E6GraphLevi.setA) :
    permLattice TwistTag.E6.perm α ∈ parabolicRadicalRoots TwistTag.E6.tag E6GraphLevi.setA := by
  rw [mem_parabolicRadicalRoots_setA_iff] at hα ⊢
  refine ⟨hα.1.permLattice TwistTag.E6.cartan_perm, by rw [height_permLattice]; exact hα.2.1, ?_⟩
  have h1 : TwistTag.E6.perm.symm 1 = 1 := by decide
  change α (TwistTag.E6.perm.symm 1) ≠ 0
  rw [h1]
  exact hα.2.2

theorem parabolicRadicalRoots_setA_closed :
    ∀ α ∈ parabolicRadicalRoots TwistTag.E6.tag E6GraphLevi.setA,
      ∀ β ∈ parabolicRadicalRoots TwistTag.E6.tag E6GraphLevi.setA, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
        IsRoot TwistTag.E6.tag (a • α + b • β) →
          a • α + b • β ∈ parabolicRadicalRoots TwistTag.E6.tag E6GraphLevi.setA :=
  fun _ hα _ hβ _ _ ha hb hr => add_mem_parabolicRadicalRoots hα.1 hβ ha hb hr

end Roots

section Torus

variable {K : Type} [Field K]

theorem torusElt_mem_subsystemGroup_setA {j : Fin TwistTag.E6.tag.rank} (hj : j ≠ 1) (u : Kˣ) :
    torusElt TwistTag.E6.tag K j u ∈ subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA := by
  have hx : ∀ c : K, xUnit TwistTag.E6.tag K j c ∈
      subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA := fun c => by
    rw [← pinnedX_single]
    exact pinnedX_mem_subsystemGroup_setA (isRoot_single _ _) (by simp [Ne.symm hj]) c
  have hy : ∀ c : K, yUnit TwistTag.E6.tag K j c ∈
      subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA := fun c => by
    rw [← pinnedX_neg_single]
    exact pinnedX_mem_subsystemGroup_setA (isRoot_neg_single _ _) (by simp [Ne.symm hj]) c
  rw [torusElt, CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul,
    CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul]
  exact mul_mem (mul_mem (mul_mem (hx _) (hy _)) (hx _)) (mul_mem (mul_mem (hx _) (hy _)) (hx _))

theorem rootDiagUnit_twistedE6TorusTuple_mem_su6Levi (σ : K ≃+* K)
    (hσ : σ ^ TwistTag.E6.order = 1) {i : Fin TwistTag.E6.tag.rank}
    (hi : i = ⟨0, by decide⟩ ∨ i = ⟨2, by decide⟩ ∨ i = ⟨3, by decide⟩) (u : Kˣ) :
    rootDiagUnit TwistTag.E6.tag (twistedE6TorusTuple σ.toRingHom i u) ∈ su6Levi σ.toRingHom := by
  refine mem_inf.2 ⟨?_, rootDiagUnit_twistedE6TorusTuple_mem σ hσ hi u⟩
  rw [rootDiagUnit_twistedE6TorusTuple]
  have h1 : i ≠ 1 := by rcases hi with rfl | rfl | rfl <;> decide
  have h2 : TwistTag.E6.perm i ≠ 1 := by rcases hi with rfl | rfl | rfl <;> decide
  exact mul_mem (torusElt_mem_subsystemGroup_setA h1 u) (torusElt_mem_subsystemGroup_setA h2 _)

theorem exists_twistedE6Torus_mem_su6Levi {f : ℕ} (hf : 2 ≤ f) [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : IsRoot TwistTag.E6.tag γ) (hpos : 0 < height γ)
    (hne : γ ≠ e6HighestRoot) :
    ∃ b : Fin TwistTag.E6.tag.rank → Kˣ,
      rootDiagUnit TwistTag.E6.tag b ∈ su6Levi σ.toRingHom ∧
      rootChar b e6HighestRoot = 1 ∧ rootChar b γ ≠ 1 ∧
      rootChar b (permLattice TwistTag.E6.perm γ) ≠ 1 := by
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  rw [Nat.card_units, hK] at hζ
  have hq : 4 ≤ 2 ^ f := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf)
  have hσζ : Units.map σ.toRingHom.toMonoidHom ζ = ζ ^ (2 ^ f) := Units.ext (by
    rw [Units.coe_map, Units.val_pow_eq_pow_val]
    exact hσ ζ)
  obtain ⟨i, hi, hγi, hργi⟩ := exists_twistedE6TorusIndex hγ hpos hne
  have hi' : i = ⟨0, by decide⟩ ∨ i = ⟨2, by decide⟩ ∨ i = ⟨3, by decide⟩ := by
    simpa using hi
  have hργ : IsRoot TwistTag.E6.tag (permLattice TwistTag.E6.perm γ) :=
    hγ.permLattice TwistTag.E6.cartan_perm
  refine ⟨twistedE6TorusTuple σ.toRingHom i ζ, rootDiagUnit_twistedE6TorusTuple_mem_su6Levi σ
    (twistedE6_sigma_pow_order hK hσ) hi' ζ, ?_, ?_, ?_⟩
  · have h1 : i ≠ ⟨1, by decide⟩ := by rcases hi' with rfl | rfl | rfl <;> decide
    have h2 : TwistTag.E6.perm i ≠ ⟨1, by decide⟩ := by
      rcases hi' with rfl | rfl | rfl <;> decide
    rw [rootChar_twistedE6TorusTuple, coPair_e6HighestRoot h1, coPair_e6HighestRoot h2,
      zpow_zero, zpow_zero, mul_one]
  · rw [rootChar_twistedE6TorusTuple, hσζ]
    exact zpow_mul_pow_zpow_ne_one hq hζ (abs_coPair_le_two_E6 hγ _)
      (abs_coPair_le_two_E6 hγ _) hγi
  · rw [rootChar_twistedE6TorusTuple, hσζ]
    exact zpow_mul_pow_zpow_ne_one hq hζ (abs_coPair_le_two_E6 hργ _)
      (abs_coPair_le_two_E6 hργ _) hργi

end Torus

section Core

variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

theorem tRadical_eq_rootSpan_inf (σ : K →+* K) :
    tRadical σ = rootSpan TwistTag.E6.tag K
        (parabolicRadicalRoots TwistTag.E6.tag E6GraphLevi.setA) ⊓
      twistedFixedGroup TwistTag.E6 K σ := by
  refine le_antisymm (inf_le_inf_left _ (graphFixedRootGroup_le _ _ _)) fun g hg => ?_
  exact mem_inf.2 ⟨(mem_inf.1 hg).1, graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
    (mem_inf.2 ⟨parabolicRadical_le_posUnipotent _ (mem_inf.1 hg).1, (mem_inf.1 hg).2⟩)⟩

theorem tRadical_le_perfectCore [CharP K 2] (hf : 2 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    (tRadical σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) ≤
      perfectCore (centralizer ({stdRepC (apply_apply_eq hK hσ) 0} :
        Set (graphFixedRootGroup TwistTag.E6 K σ))) := by
  have hf1 : 1 ≤ f := by omega
  have := finite_of_card hK
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  set C₀ := graphFixedRootGroup TwistTag.E6 K σ with hC₀
  set X := centralizer ({stdRepC (apply_apply_eq hK hσ) 0} : Set C₀) with hX
  set P : Subgroup (ModGL TwistTag.E6.tag K) := (perfectCore X).map C₀.subtype with hP
  have hXeq : X = (tRadical σ).subgroupOf C₀ ⊔ (su6Levi σ).subgroupOf C₀ :=
    centralizer_stdRepC_zero_eq (k := k) hf1 hk hK hσ
  have hL : (su6Levi σ).subgroupOf C₀ ≤ perfectCore X := by
    have h := (isCoreLeviDecomp_stdRepC_zero (k := k) hf1 hk hK hσ).1
    rw [h]
    exact le_sup_right
  have hQX : ∀ v (hv : v ∈ tRadical σ), (⟨v, (mem_inf.1 hv).2⟩ : C₀) ∈ X := by
    intro v hv
    rw [hXeq]
    exact mem_sup_left (mem_subgroupOf.2 hv)
  obtain ⟨σE, rfl⟩ := exists_ringEquiv_toRingHom_eq σ
  have hσσ : ∀ x, σE.toRingHom (σE.toRingHom x) = x := apply_apply_eq hK hσ
  set S : Set (Fin TwistTag.E6.tag.rank → ℤ) :=
    parabolicRadicalRoots TwistTag.E6.tag E6GraphLevi.setA with hS
  have hSpos : ∀ α ∈ S, IsRoot TwistTag.E6.tag α ∧ 0 < height α := fun α hα => hα.1
  have hSρ : ∀ α ∈ S, permLattice TwistTag.E6.perm α ∈ S := fun α hα =>
    permLattice_mem_parabolicRadicalRoots_setA hα
  have horb : ∀ α : Fin TwistTag.E6.tag.rank → ℤ, α ∈ S → α ≠ e6HighestRoot →
      rootSpan TwistTag.E6.tag K (TwistTag.E6.diagramOrbit α : Set _) ⊓
        twistedFixedGroup TwistTag.E6 K σE.toRingHom ≤ P := by
    intro α hαS hθ x hx
    obtain ⟨b, hbL, -, hb1, hb2⟩ := exists_twistedE6Torus_mem_su6Levi hf hK
      (σ := σE) (fun c => hσ c) (hSpos α hαS).1 (hSpos α hαS).2 hθ
    have hbC : rootDiagUnit TwistTag.E6.tag b ∈ C₀ := (mem_inf.1 hbL).2
    have hbchar : ∀ β ∈ TwistTag.E6.diagramOrbit α, rootChar b β ≠ 1 := by
      intro β hβ
      rw [diagramOrbit_eq_pair_twistedE6Classes, Finset.mem_insert, Finset.mem_singleton] at hβ
      rcases hβ with rfl | rfl
      · exact hb1
      · exact hb2
    obtain ⟨v, hv, rfl⟩ := exists_eq_rootDiagUnit_conj_of_mem_orbitGroup σE.toRingHom
      (hSpos α hαS).1 (hSpos α hαS).2 (graphFixedRootGroup_le _ _ _ hbC) hbchar hx
    have hvQ : v ∈ tRadical σE.toRingHom := by
      have h := orbitGroup_le_rootSpan_inf_C0 hSpos hSρ hαS hv
      exact mem_inf.2 ⟨(mem_inf.1 h).1, (mem_inf.1 h).2⟩
    exact mul_conj_inv_mem_map_perfectCore hbC (mem_inf.1 hvQ).2
      (hL (mem_subgroupOf.2 hbL)) (hQX v hvQ)
  have hθ : rootSpan TwistTag.E6.tag K (TwistTag.E6.diagramOrbit e6HighestRoot : Set _) ⊓
      twistedFixedGroup TwistTag.E6 K σE.toRingHom ≤ P := by
    intro x hx
    obtain ⟨c, hc, rfl⟩ := exists_eq_pinnedX_of_mem_fixedOrbitGroup isRoot_e6HighestRoot
      permLattice_e6HighestRoot hx
    have hβ : IsRoot TwistTag.E6.tag e6HighRootSubTwo := isRoot_e6HighRootSubTwo
    have he : IsRoot TwistTag.E6.tag e6NodeTwo := isRoot_single _ _
    have hsum : e6HighRootSubTwo + e6NodeTwo = e6HighestRoot := by decide
    have hcomm := commutator_pinnedX_of_isRoot_add_E6 (K := K) hβ he (by decide)
      (hsum ▸ isRoot_e6HighestRoot) 1 c
    rw [hsum, one_mul] at hcomm
    rw [← hcomm]
    have hβS : e6HighRootSubTwo ∈ S := by
      rw [hS, mem_parabolicRadicalRoots_setA_iff]
      exact ⟨hβ, by decide, by decide⟩
    have heS : e6NodeTwo ∈ S := by
      rw [hS, mem_parabolicRadicalRoots_setA_iff]
      exact ⟨he, by decide, by decide⟩
    have m1 := horb _ hβS (by decide) (pinnedX_mem_orbitGroup_of_fixed σE.toRingHom hβ
      (by decide) (map_one _))
    have m2 := horb _ heS (by decide) (pinnedX_mem_orbitGroup_of_fixed σE.toRingHom he
      (by decide) hc)
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem m1 m2) (inv_mem m1)) (inv_mem m2)
  have hall : rootSpan TwistTag.E6.tag K S ⊓ twistedFixedGroup TwistTag.E6 K σE.toRingHom ≤ P := by
    refine rootSpan_inf_twistedFixedGroup_le_of_forall σE.surjective hSpos hSρ
      parabolicRadicalRoots_setA_closed fun α hα => ?_
    by_cases hα' : α = e6HighestRoot
    · rw [hα']
      exact hθ
    · exact horb α hα hα'
  intro g hg
  have hg' : (g : ModGL TwistTag.E6.tag K) ∈ P := by
    refine hall ?_
    rw [← tRadical_eq_rootSpan_inf]
    exact mem_subgroupOf.1 hg
  obtain ⟨y, hy, hyg⟩ := hg'
  rwa [show g = y from Subtype.ext hyg.symm]

theorem perfectCore_centralizer_stdRepC_zero_eq [CharP K 2] (hf : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    perfectCore (centralizer ({stdRepC (apply_apply_eq hK hσ) 0} :
        Set (graphFixedRootGroup TwistTag.E6 K σ))) =
      centralizer ({stdRepC (apply_apply_eq hK hσ) 0} :
        Set (graphFixedRootGroup TwistTag.E6 K σ)) := by
  refine le_antisymm (perfectCore_le _) ?_
  have hL : (su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) ≤
      perfectCore (centralizer ({stdRepC (apply_apply_eq hK hσ) 0} :
        Set (graphFixedRootGroup TwistTag.E6 K σ))) := by
    have h := (isCoreLeviDecomp_stdRepC_zero (k := k) (by omega) hk hK hσ).1
    rw [h]
    exact le_sup_right
  conv_lhs => rw [centralizer_stdRepC_zero_eq (k := k) (by omega) hk hK hσ]
  exact sup_le (tRadical_le_perfectCore hf hk hK hσ) hL

theorem commutator_centralizer_stdRepC_zero [CharP K 2] (hf : 2 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    ⁅centralizer ({stdRepC (apply_apply_eq hK hσ) 0} : Set (graphFixedRootGroup TwistTag.E6 K σ)),
      centralizer ({stdRepC (apply_apply_eq hK hσ) 0} :
        Set (graphFixedRootGroup TwistTag.E6 K σ))⁆ =
      centralizer ({stdRepC (apply_apply_eq hK hσ) 0} :
        Set (graphFixedRootGroup TwistTag.E6 K σ)) := by
  have := finite_of_card hK
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  rw [← CFSG.Quasithin.perfectCore_eq_self_iff]
  exact perfectCore_centralizer_stdRepC_zero_eq (k := k) hf hk hK hσ

end Core

end CFSG.SeitzReduction.TwistedE6Pilot
