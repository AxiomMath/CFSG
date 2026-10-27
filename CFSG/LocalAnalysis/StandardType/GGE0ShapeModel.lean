module

public import CFSG.LocalAnalysis.StandardType.GGE0ShapeDefs
public import CFSG.LocalAnalysis.StandardType.GGE0ShapeAction
public import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagConcl
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem shapeModel_isComponentOf_of_map_map {H G : Type*} [Group H] [Group G]
    (f : H →* G) (hf : Function.Injective f) (L K : Subgroup H)
    (h : IsComponentOf (L.map f) (K.map f)) : IsComponentOf L K := by
  obtain ⟨hle, hsub, hq⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨k, hk, hfk⟩ := Subgroup.mem_map.mp (hle (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩))
    rwa [hf hfk] at hk
  · have h' := hsub.comap f
    rwa [Subgroup.comap_map_eq_self_of_injective hf L,
      Subgroup.comap_map_eq_self_of_injective hf K] at h'
  · exact (CFSG.Assembly.IsQuasisimple.congr (L.equivMapOfInjective f hf)).2 hq

theorem ggE0ModelShape_holds {C : Type} [Group C] {I : Subgroup (MulAut C)}
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (halg : letI := ZMod.algebra L 2; Algebra.IsAlgebraic (ZMod 2) L)
    (R : ShapeRealization C I L) :
    ∀ (β : MulAut C) (hβ : β ∈ I) (E : Subgroup (MulAut C)),
      E ≤ I → β ≠ 1 → β ^ 3 = 1 → E ≤ Subgroup.centralizer {β} →
      RigidToralPlane (realizedSubgroup R E) →
      ∀ X : Subgroup (MulAut C),
        CFSG.Assembly.IsComponentOf X ((MulAut.conj : C →* MulAut C).range ⊓
          Subgroup.centralizer {β}) → GGE0Concl E X := by
  intro β hβ E hEI hβ1 hβ3 hEβ hrig X hX
  let βhat : ModGL .E6 L := R.action ⟨β, hβ⟩
  let E' : Subgroup I := E.subgroupOf I
  let X' : Subgroup I := X.subgroupOf I
  have hg3 : (⟨β, hβ⟩ : I) ^ 3 = 1 := by
    apply Subtype.ext
    simpa using hβ3
  have hβhat1 : βhat ≠ 1 := by
    intro h
    apply hβ1
    have hβhat_eq : R.action ⟨β, hβ⟩ = 1 := h
    have h2 : (⟨β, hβ⟩ : I) = 1 := by
      apply R.action_injective
      rw [hβhat_eq, map_one]
    simpa using congrArg Subtype.val h2
  have hβhat3 : βhat ^ 3 = 1 := by
    change R.action ⟨β, hβ⟩ ^ 3 = 1
    rw [← map_pow, hg3, map_one]
  have hβhat_model : βhat ∈ R.setup.D.model := R.action_mem ⟨β, hβ⟩
  have hEhat_model : E'.map R.action ≤ R.setup.D.model := by
    rintro _ ⟨φ, -, rfl⟩
    exact R.action_mem φ
  have hEhatβ : E'.map R.action ≤ Subgroup.centralizer {βhat} := by
    rintro _ ⟨φ, hφ, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hφE : (φ : MulAut C) ∈ E := hφ
    have hcomm : (φ : MulAut C) * β = β * (φ : MulAut C) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hEβ hφE)
    have hcommI : φ * ⟨β, hβ⟩ = ⟨β, hβ⟩ * φ := Subtype.ext hcomm
    have := congrArg R.action hcommI
    simpa only [map_mul, βhat] using this
  have hpair : RigidPair βhat (E'.map R.action) :=
    ⟨hβhat1, hβhat3, hEhatβ, hrig⟩
  have hKsub : (MulAut.conj : C →* MulAut C).range ⊓ Subgroup.centralizer {β} ≤ I :=
    inf_le_left.trans R.inner_le
  have hXsub : X ≤ I := hX.1.trans hKsub
  have hX'_comp : IsComponentOf X'
      (((MulAut.conj : C →* MulAut C).range ⊓ Subgroup.centralizer {β}).subgroupOf I) := by
    have hXmap : X'.map I.subtype = X := Subgroup.map_subgroupOf_eq_of_le hXsub
    have hKmap : (((MulAut.conj : C →* MulAut C).range ⊓
        Subgroup.centralizer {β}).subgroupOf I).map I.subtype =
        (MulAut.conj : C →* MulAut C).range ⊓ Subgroup.centralizer {β} :=
      Subgroup.map_subgroupOf_eq_of_le hKsub
    exact shapeModel_isComponentOf_of_map_map I.subtype I.subtype_injective X' _
      (by rw [hXmap, hKmap]; exact hX)
  have hKmap_hat : (((MulAut.conj : C →* MulAut C).range ⊓
        Subgroup.centralizer {β}).subgroupOf I).map R.action =
      R.setup.Γ ⊓ Subgroup.centralizer {βhat} := by
    ext φ
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxK : (x : MulAut C) ∈ (MulAut.conj : C →* MulAut C).range ⊓
          Subgroup.centralizer {β} := hx
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · obtain ⟨c, hc⟩ := hxK.1
        have hx_eq : R.action x = (R.groupEquiv c : ModGL .E6 L) := by
          have hxe : x = ⟨MulAut.conj c, R.inner_le ⟨c, rfl⟩⟩ := by
            apply Subtype.ext
            exact hc.symm
          rw [hxe, R.inner_compatible c]
        rw [hx_eq]
        exact (R.groupEquiv c).2
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have hcomm : (x : MulAut C) * β = β * (x : MulAut C) :=
          Subgroup.mem_centralizer_singleton_iff.mp hxK.2
        have hcommI : x * ⟨β, hβ⟩ = ⟨β, hβ⟩ * x := Subtype.ext hcomm
        have := congrArg R.action hcommI
        simpa only [map_mul, βhat] using this
    · rintro ⟨hΓ, hcent⟩
      let c : C := R.groupEquiv.symm ⟨φ, hΓ⟩
      have hcφ : (R.groupEquiv c : ModGL .E6 L) = φ := by
        change ((R.groupEquiv c : ↥R.setup.Γ) : ModGL .E6 L) = φ
        rw [MulEquiv.apply_symm_apply]
      refine Subgroup.mem_map.mpr ⟨⟨MulAut.conj c, R.inner_le ⟨c, rfl⟩⟩, ?_, ?_⟩
      · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · exact ⟨c, rfl⟩
        · rw [Subgroup.mem_centralizer_singleton_iff]
          have hcomm_img : R.action ⟨MulAut.conj c, R.inner_le ⟨c, rfl⟩⟩ * βhat =
              βhat * R.action ⟨MulAut.conj c, R.inner_le ⟨c, rfl⟩⟩ := by
            rw [R.inner_compatible c, hcφ]
            exact Subgroup.mem_centralizer_singleton_iff.mp hcent
          have hcommI : (⟨MulAut.conj c, R.inner_le ⟨c, rfl⟩⟩ : I) * ⟨β, hβ⟩ =
              ⟨β, hβ⟩ * ⟨MulAut.conj c, R.inner_le ⟨c, rfl⟩⟩ := by
            apply R.action_injective
            simpa only [map_mul] using hcomm_img
          exact congrArg Subtype.val hcommI
      · rw [R.inner_compatible c]
        exact hcφ
  have hXhat : IsComponentOf (X'.map R.action)
      (R.setup.Γ ⊓ Subgroup.centralizer {βhat}) := by
    have h := isComponentOf_map_of_injective R.action R.action_injective hX'_comp
    rwa [hKmap_hat] at h
  have hshape : GGE0Concl (E'.map R.action) (X'.map R.action) :=
    shape_action halg R.setup βhat (E'.map R.action) (X'.map R.action) hβhat_model hEhat_model
      hpair hXhat
  have h_in_I : GGE0Concl E' X' :=
    (ggE0Concl_map_iff R.action R.action_injective E' X').mp hshape
  have h_back : GGE0Concl (E'.map I.subtype) (X'.map I.subtype) :=
    (ggE0Concl_map_iff I.subtype I.subtype_injective E' X').mpr h_in_I
  rw [Subgroup.map_subgroupOf_eq_of_le hEI, Subgroup.map_subgroupOf_eq_of_le hXsub] at h_back
  exact h_back

end CFSG.StandardType
