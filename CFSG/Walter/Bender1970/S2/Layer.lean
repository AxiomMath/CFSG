module

public import CFSG.Walter.Bender1970.S2.Components
public import CFSG.Walter.Bender1970.S2.Fitting
public import CFSG.Walter.Bender1970.S1.EqualityOfMaximalLayer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ComponentLayerPerfect
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.FStarSubnormal
import CFSG.GroupTheory.LocalCores.Components
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.NormalizerLeNormalizerCentralizer

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter
open scoped Pointwise commutatorElement

theorem commutator_sSup_le {G : Type*} [Group G] (𝒜 : Set (Subgroup G)) (C D : Subgroup G)
    (hAC : ∀ A ∈ 𝒜, ⁅A, C⁆ ≤ D) (hAD : ∀ A ∈ 𝒜, A ≤ Subgroup.normalizer (D : Set G)) :
    ⁅sSup 𝒜, C⁆ ≤ D := by
  rw [Subgroup.commutator_le]
  intro x hx c hc
  have hsupN : sSup 𝒜 ≤ Subgroup.normalizer (D : Set G) := sSup_le hAD
  rw [sSup_eq_iSup', Subgroup.iSup_eq_closure] at hx
  have hmemN : ∀ y ∈ Subgroup.closure (⋃ A : 𝒜, ((A : Subgroup G) : Set G)),
      y ∈ Subgroup.normalizer (D : Set G) := fun y hy => hsupN (by
    rwa [sSup_eq_iSup', Subgroup.iSup_eq_closure])
  refine Subgroup.closure_induction (k := ⋃ A : 𝒜, ((A : Subgroup G) : Set G))
    (p := fun y _hy => ⁅y, c⁆ ∈ D) ?_ ?_ ?_ ?_ hx
  · intro y hy
    simp only [Set.mem_iUnion] at hy
    obtain ⟨⟨A, hA⟩, hyA⟩ := hy
    exact hAC A hA (Subgroup.commutator_mem_commutator hyA hc)
  · simp
  · intro y z hy _hz hyP hzP
    rw [commutatorElement_mul_left_eq_conj_mul]
    exact D.mul_mem (((Subgroup.mem_normalizer_iff.mp (hmemN y hy)) ⁅z, c⁆).1 hzP) hyP
  · intro y hy hyP
    have hyNinv : y⁻¹ ∈ Subgroup.normalizer (D : Set G) :=
      (Subgroup.normalizer (D : Set G)).inv_mem (hmemN y hy)
    have hcyD : ⁅c, y⁆ ∈ D := by simpa [commutatorElement_inv] using D.inv_mem hyP
    rw [commutatorElement_inv_left]
    simpa using ((Subgroup.mem_normalizer_iff.mp hyNinv) ⁅c, y⁆).1 hcyD

section ComponentsOf

variable {G : Type*} [Group G]

theorem isComponent_subgroupOf_of_isComponentOf {K A : Subgroup G} (hK : IsComponentOf K A) :
    CFSG.IsComponent (K.subgroupOf A) :=
  (isComponent_iff_isComponentOf_top _).mpr (fstar_isComponentOf_subgroupOf_top hK)

theorem subgroupOf_injective_of_le {K K' A : Subgroup G} (hK : K ≤ A) (hK' : K' ≤ A)
    (h : K.subgroupOf A = K'.subgroupOf A) : K = K' := by
  have h1 := congrArg (Subgroup.map A.subtype) h
  rwa [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype, inf_of_le_left hK,
    inf_of_le_left hK'] at h1

variable [Finite G]

theorem isComponentOf_eq_or_commutator_eq_bot {K K' A : Subgroup G} (hK : IsComponentOf K A)
    (hK' : IsComponentOf K' A) : K = K' ∨ ⁅K, K'⁆ = ⊥ := by
  rcases CFSG.LocalCores.distinct_components_commute (isComponent_subgroupOf_of_isComponentOf hK)
      (isComponent_subgroupOf_of_isComponentOf hK') with h | h
  · exact Or.inl (subgroupOf_injective_of_le hK.1 hK'.1 h)
  · right
    have h1 := CFSG.LocalCores.commutator_inf_eq_bot_of_subgroupOf hK.1 h
    rwa [inf_of_le_left hK'.1] at h1

theorem componentLayerOf_le_normalizer_of_isComponentOf {K A : Subgroup G}
    (hK : IsComponentOf K A) : componentLayerOf A ≤ Subgroup.normalizer (K : Set G) := by
  refine sSup_le fun K' hK' => ?_
  rcases isComponentOf_eq_or_commutator_eq_bot hK' hK with rfl | h
  · exact Subgroup.le_normalizer
  · exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h).trans
      (Subgroup.centralizer_le_normalizer _)

theorem isComponentOf_commutator_eq_bot_of_isSolvable {K A R : Subgroup G}
    (hK : IsComponentOf K A) (hR : Group.IsSolvable R) (hRA : R ≤ A)
    (hAR : A ≤ Subgroup.normalizer (R : Set G)) : ⁅K, R⁆ = ⊥ := by
  have hRn : (R.subgroupOf A).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRA).mpr hAR
  have hRs : Group.IsSolvable (R.subgroupOf A) :=
    Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hRA).symm.toMonoidHom)
      (MulEquiv.surjective _)
  have h1 := (CFSG.LocalCores.component_solvable_centralizer hRs hRn.isSubnormal).1 _
    (isComponent_subgroupOf_of_isComponentOf hK)
  have h2 := CFSG.LocalCores.commutator_inf_eq_bot_of_subgroupOf hK.1 h1
  rwa [inf_of_le_left hRA] at h2

omit [Finite G] in
theorem isComponentOf_map_conj {K A : Subgroup G} (hK : IsComponentOf K A) {g : G}
    (hg : g ∈ Subgroup.normalizer (A : Set G)) :
    IsComponentOf (K.map (MulAut.conj g).toMonoidHom) A := by
  set φ : MulAut A := A.normalizerMonoidHom ⟨g, hg⟩ with hφ
  have hmap : (K.subgroupOf A).map φ.toMonoidHom =
      (K.map (MulAut.conj g).toMonoidHom).subgroupOf A := by
    ext x
    rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
      Subgroup.mem_map_equiv]
    have h1 : ((φ.symm x : A) : G) = g⁻¹ * x * g := by
      have h2 : φ (φ.symm x) = x := φ.apply_symm_apply x
      have h3 := congrArg Subtype.val h2
      rw [hφ, Subgroup.normalizerMonoidHom_apply_apply_coe] at h3
      calc ((φ.symm x : A) : G) = g⁻¹ * (g * (φ.symm x : A) * g⁻¹) * g := by group
        _ = g⁻¹ * x * g := by rw [h3]
    rw [h1, MulAut.conj_symm_apply]
  have hKA : K.map (MulAut.conj g).toMonoidHom ≤ A := by
    rintro _ ⟨k, hk, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg k).mp (hK.1 hk)
  have h1 := CFSG.LocalCores.isComponent_map_mulEquiv φ (isComponent_subgroupOf_of_isComponentOf hK)
  rw [hmap] at h1
  have h2 := (isComponent_iff_isComponentOf_top _).mp h1
  refine ⟨hKA, h1.2, ?_⟩
  exact isQuasisimple_of_mulEquiv' (Subgroup.subgroupOfEquivOfLe hKA) h2.2.2

end ComponentsOf

theorem bender1970_2_4_layer {X : Type} [Group X] [Finite X] (hX : IsAStar X) {t : X}
    (ht : orderOf t = 2) {W : Subgroup X}
    (hWt : Subgroup.centralizer ({t} : Set X) ≤ Subgroup.normalizer (W : Set X))
    (hWE : componentLayerOf W = W) (hWcomm : ⁅W, Subgroup.zpowers t⁆ = W) :
    W ≤ componentLayerOf (⊤ : Subgroup X) ∧
      ∀ K : Subgroup X, IsComponentOf K W → IsComponentOf K ⊤ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hWperf : Group.IsPerfect W := hWE ▸ componentLayerOf_isPerfect W
  have htinv : BenderSuzuki.PFAppendixIII.IsInvolution t := by
    refine ⟨fun h => ?_, ?_⟩
    · rw [h, orderOf_one] at ht
      omega
    · have h := pow_orderOf_eq_one t
      rwa [ht] at h
  set F := CFSG.fittingSubgroup X with hF
  have hWWF : W ≤ Subgroup.centralizer ((W ⊓ F : Subgroup X) : Set X) := by
    have hsolv : Group.IsSolvable (W ⊓ F : Subgroup X) := by
      have : Group.IsNilpotent F := CFSG.fittingSubgroup_nilpotent
      have : Group.IsNilpotent ((W ⊓ F).subgroupOf F) := inferInstance
      have : Group.IsNilpotent (W ⊓ F : Subgroup X) := Group.nilpotent_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe (inf_le_right : W ⊓ F ≤ F))
      infer_instance
    have hN : W ≤ Subgroup.normalizer ((W ⊓ F : Subgroup X) : Set X) :=
      (le_inf W.le_normalizer (Subgroup.le_normalizer_of_normal (H := F))).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    have hle : componentLayerOf W ≤ Subgroup.centralizer ((W ⊓ F : Subgroup X) : Set X) := by
      refine sSup_le fun K hK => ?_
      have h1 := isComponentOf_commutator_eq_bot_of_isSolvable hK hsolv inf_le_left
        (hWE.symm ▸ hN)
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1
    rwa [hWE] at hle
  have hfixedF : F ⊓ Subgroup.centralizer ({t} : Set X) ≤ F ⊓ Subgroup.centralizer (W : Set X) := by
    intro s hs
    refine ⟨hs.1, ?_⟩
    have hS : Subgroup.zpowers s ≤ Subgroup.normalizer (W : Set X) :=
      Subgroup.zpowers_le.mpr (hWt hs.2)
    have h1 : ⁅W, Subgroup.zpowers s⁆ ≤ W ⊓ F := by
      rw [Subgroup.commutator_le]
      intro w hw z hz
      refine ⟨?_, ?_⟩
      · rw [commutatorElement_def]
        have h2 : w * z * w⁻¹ * z⁻¹ = w * (z * w⁻¹ * z⁻¹) := by group
        rw [h2]
        exact W.mul_mem hw ((Subgroup.mem_normalizer_iff.mp (hS hz) w⁻¹).mp (W.inv_mem hw))
      · have hzF : z ∈ F := (Subgroup.zpowers_le.mpr hs.1) hz
        rw [commutatorElement_def]
        exact F.mul_mem ((CFSG.fittingSubgroup_normal).conj_mem z hzF w) (F.inv_mem hzF)
    have h2 : ⁅W, Subgroup.zpowers s⁆ = ⊥ := by
      apply CFSG.LocalCores.perfect_double_commutator hWperf
      rw [← le_bot_iff, Subgroup.commutator_comm]
      calc ⁅W, ⁅W, Subgroup.zpowers s⁆⁆ ≤ ⁅W, W ⊓ F⁆ := Subgroup.commutator_mono le_rfl h1
        _ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hWWF
    have h3 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h2
    show s ∈ Subgroup.centralizer (W : Set X)
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (Subgroup.mem_centralizer_iff.mp (h3 hw) s (Subgroup.mem_zpowers s)).symm
  have hWF := le_centralizer_fittingSubgroup_of_isPerfect W hX.1 htinv hWt hWcomm hWperf hfixedF
  have hWX : W ≤ componentLayerOf (⊤ : Subgroup X) :=
    le_componentLayerOf_top_of_odd_index hX.2.1 hWperf hWF
  refine ⟨hWX, fun K hK => ?_⟩
  obtain ⟨L, hL, hKL, hcase⟩ := bender1970_2_3 hX ht hWX hWt hK
  rcases hcase with rfl | ⟨-, -, hKt⟩
  · exact hL
  ·
    exfalso
    obtain ⟨k₁, k₂, hk12⟩ := exists_mul_ne_mul_of_isQuasisimple hK.2.2
    set C := W ⊓ Subgroup.centralizer (K : Set X) with hC
    have hWK : W ≤ Subgroup.normalizer (K : Set X) :=
      hWE ▸ componentLayerOf_le_normalizer_of_isComponentOf hK
    have hWC : W ≤ Subgroup.normalizer (C : Set X) :=
      (le_inf W.le_normalizer (hWK.trans (normalizer_le_normalizer_centralizer_subgroup K))).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    have htC : Subgroup.zpowers t ≤ Subgroup.normalizer (C : Set X) := by
      rw [Subgroup.zpowers_le]
      have htK : t ∈ Subgroup.normalizer (K : Set X) := by
        apply mem_normalizer_of_mem_centralizer
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        exact (Subgroup.mem_centralizer_singleton_iff.mp (hKt hk))
      exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨hWt (Subgroup.mem_centralizer_singleton_iff.mpr rfl),
          normalizer_le_normalizer_centralizer_subgroup K htK⟩
    have hle : ⁅W, Subgroup.zpowers t⁆ ≤ C := by
      rw [← hWE]
      refine commutator_sSup_le _ _ _ (fun K' hK' => ?_) (fun K' hK' => ?_)
      · rcases isComponentOf_eq_or_commutator_eq_bot hK' hK with rfl | h
        · rw [Subgroup.commutator_eq_bot_iff_le_centralizer.mpr]
          · exact bot_le
          · intro k hk
            rw [Subgroup.mem_centralizer_iff]
            intro z hz
            obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
            exact (Commute.zpow_left
              (Subgroup.mem_centralizer_singleton_iff.mp (hKt hk)).symm n).eq
        · have hK'C : K' ≤ C := le_inf hK'.1 (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h)
          rw [Subgroup.commutator_le]
          intro k hk z hz
          rw [commutatorElement_def]
          have h2 : k * z * k⁻¹ * z⁻¹ = k * (z * k⁻¹ * z⁻¹) := by group
          rw [h2]
          exact C.mul_mem (hK'C hk)
            ((Subgroup.mem_normalizer_iff.mp (htC hz) k⁻¹).mp (C.inv_mem (hK'C hk)))
      · exact hK'.1.trans (hWE ▸ hWC)
    rw [hWcomm] at hle
    apply hk12
    have h1 := (hle (hK.1 k₂.2)).2
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp h1 k₁ k₁.2))

end CFSG.Walter
