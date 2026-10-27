module

public import CFSG.LocalAnalysis.StandardType.GGSixRootCentNotExcLift
public import CFSG.LocalAnalysis.StandardType.GGStructSOnePrimeCent
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142TInd
public import CFSG.LocalAnalysis.StandardType.GGStructSOneHolds

public section

namespace CFSG.StandardType

section StepThree

variable {A : Type} [Group A]

theorem ggRCS_component_inf_lift {K V : Subgroup A} (hK : K.IsSubnormal)
    {D : Subgroup ↥(K ⊓ V)} (hD : CFSG.Open.IsComponentOf D ⊤) :
    CFSG.Open.IsComponentOf ((D.map (K ⊓ V).subtype).subgroupOf V) ⊤ ∧
      Nonempty (↥((D.map (K ⊓ V).subtype).subgroupOf V) ⧸
          Subgroup.center ↥((D.map (K ⊓ V).subtype).subgroupOf V) ≃*
        ↥D ⧸ Subgroup.center ↥D) := by
  have hDV : D.map (K ⊓ V).subtype ≤ V :=
    (Subgroup.map_subtype_le D).trans inf_le_right
  have htop : Subgroup.map (K ⊓ V).subtype (⊤ : Subgroup ↥(K ⊓ V)) = K ⊓ V := by
    rw [← Subgroup.subgroupOf_self (K ⊓ V), Subgroup.map_subgroupOf_eq_of_le le_rfl]
  have hsub : CFSG.Assembly.IsSubnormal (D.map (K ⊓ V).subtype) (K ⊓ V) := by
    have h := (CFSG.Assembly.isSubnormal_iff_open).2 hD.2.1
    have hm := h.map (K ⊓ V).subtype
    rwa [htop] at hm
  have hKV : CFSG.Assembly.IsSubnormal (K ⊓ V) V :=
    (CFSG.Assembly.IsSubnormal.of_mathlib hK).inf_of_le le_top
  have hEsub : CFSG.Open.IsSubnormal ((D.map (K ⊓ V).subtype).subgroupOf V) ⊤ :=
    (CFSG.Open.IsSubnormal.top_iff).2
      ((CFSG.Assembly.IsSubnormal.iff_subgroupOf hDV).1 (hsub.trans hKV))
  have hunit : ↥((D.map (K ⊓ V).subtype).subgroupOf V) ≃* ↥D :=
    (Subgroup.subgroupOfEquivOfLe hDV).trans
      (Subgroup.equivMapOfInjective D (K ⊓ V).subtype (K ⊓ V).subtype_injective).symm
  refine ⟨⟨le_top, hEsub, ?_⟩, ⟨QuotientGroup.congr _ _ hunit (Subgroup.map_center_eq hunit)⟩⟩
  exact (CFSG.Open.IsQuasisimple.congr hunit).mpr hD.2.2

end StepThree

section MapSubtype

variable {A : Type} [Group A]

theorem ggRCS_isComponentOf_map_subtype {V : Subgroup A} {E : Subgroup ↥V}
    (hE : CFSG.Open.IsComponentOf E ⊤) :
    CFSG.Open.IsComponentOf (E.map V.subtype) V := by
  have htop : Subgroup.map V.subtype (⊤ : Subgroup ↥V) = V := by
    rw [← Subgroup.subgroupOf_self V, Subgroup.map_subgroupOf_eq_of_le le_rfl]
  have hsub : CFSG.Assembly.IsSubnormal (E.map V.subtype) V := by
    have h := (CFSG.Assembly.isSubnormal_iff_open).2 hE.2.1
    have hm := h.map V.subtype
    rwa [htop] at hm
  have hq : CFSG.Open.IsQuasisimple ↥(E.map V.subtype) :=
    (CFSG.Open.IsQuasisimple.congr
      (Subgroup.equivMapOfInjective E V.subtype V.subtype_injective)).mp hE.2.2
  exact ⟨Subgroup.map_subtype_le E, (CFSG.Assembly.isSubnormal_iff_open).1 hsub, hq⟩

end MapSubtype

section SubgroupOf

variable {A : Type} [Group A]

theorem ggRCS_isComponentOf_subgroupOf {C Y K : Subgroup A}
    (hC : CFSG.Open.IsComponentOf C K) (hCY : C ≤ Y) (hYK : Y ≤ K) :
    CFSG.Open.IsComponentOf (C.subgroupOf Y) ⊤ := by
  have hCY' : CFSG.Open.IsComponentOf C Y :=
    (CFSG.Assembly.isComponentOf_iff_open).1
      (CFSG.Assembly.IsComponentOf.of_le_of_le
        ((CFSG.Assembly.isComponentOf_iff_open).2 hC) hCY hYK)
  exact (CFSG.LargeExtraspecial.S5.isComponentOf_iff_subgroupOf hCY).1 hCY'

end SubgroupOf

section Schreier

variable {G B : Type} [Group G] [Group B] [Finite G]

theorem ggRCS_component_le_map_of_schreier {N M G₀ : Subgroup G}
    (hM : M ≤ Subgroup.normalizer (G₀ : Set G))
    (hSch : ∀ D : Subgroup G, D ≤ Subgroup.normalizer (G₀ : Set G) → ⁅D, D⁆ = D → D ≤ G₀)
    {π : ↥N →* B} {C : Subgroup B}
    (hC : CFSG.Open.IsComponentOf C ((M.subgroupOf N).map π)) :
    C ≤ (G₀.subgroupOf N).map π := by
  let ρ : ↥(M.subgroupOf N) →* B := π.comp (M.subgroupOf N).subtype
  have hρrange : ρ.range = (M.subgroupOf N).map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hCV' : C ≤ ρ.range := hρrange ▸ hC.1
  let P : Subgroup ↥(M.subgroupOf N) := C.comap ρ
  have hPmap : P.map ρ = C := Subgroup.map_comap_eq_self (f := ρ) (H := C) hCV'
  have hCperf : Group.IsPerfect ↥C := ⟨hC.2.2.1⟩
  have hDmap : ((CFSG.perfectResidual P).map P.subtype).map ρ = C := by
    have h := CFSG.SignalizerFunctorTheorem.Nonsolvable.map_perfectResidual_map ρ P
    rw [hPmap] at h
    rw [h, CFSG.SignalizerFunctorTheorem.Nonsolvable.perfectResidual_map_eq_of_isPerfect hCperf]
  have hDperf : Group.IsPerfect ↥(CFSG.perfectResidual P) :=
    CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_isPerfect
  let Dn : Subgroup ↥N := ((CFSG.perfectResidual P).map P.subtype).map (M.subgroupOf N).subtype
  have hDnperf : Group.IsPerfect ↥Dn := by
    have h1 : Group.IsPerfect ↥((CFSG.perfectResidual P).map P.subtype) :=
      Group.IsPerfect.map (H := CFSG.perfectResidual P) P.subtype
    exact Group.IsPerfect.map (H := (CFSG.perfectResidual P).map P.subtype)
      (M.subgroupOf N).subtype
  let Dg : Subgroup G := Dn.map N.subtype
  have hDgperf : Group.IsPerfect ↥Dg := by
    haveI : Group.IsPerfect ↥Dn := hDnperf
    exact Group.IsPerfect.map (H := Dn) N.subtype
  have hDnM : Dn ≤ M.subgroupOf N := Subgroup.map_subtype_le _
  have hDgM : Dg ≤ M := by
    calc Dg = Dn.map N.subtype := rfl
      _ ≤ (M.subgroupOf N).map N.subtype := Subgroup.map_mono hDnM
      _ = M ⊓ N := Subgroup.subgroupOf_map_subtype M N
      _ ≤ M := inf_le_left
  have hDg0 : Dg ≤ G₀ :=
    hSch Dg (hDgM.trans hM) (Subgroup.isPerfect_iff.mp hDgperf)
  have hDn0 : Dn ≤ G₀.subgroupOf N :=
    Subgroup.map_le_iff_le_comap.mp hDg0
  have hCeq : Dn.map π = C := by
    have h : Dn.map π = ((CFSG.perfectResidual P).map P.subtype).map ρ := by
      rw [show Dn = Subgroup.map (M.subgroupOf N).subtype
          (Subgroup.map P.subtype (CFSG.perfectResidual P)) from rfl, Subgroup.map_map]
    rw [h, hDmap]
  rw [← hCeq]
  exact Subgroup.map_mono hDn0

end Schreier

section Sigma

variable {N : Type} [Group N]

theorem ggRCS_kv_sigma_exists {A₀ : Subgroup N} :
    ∃ σ : ↥(A₀.map (QuotientGroup.mk' (CFSG.pCore 2 N))) →*
        (↥A₀ ⧸ CFSG.pCore 2 ↥A₀),
      Function.Surjective σ ∧ IsPGroup 2 ↥σ.ker := by
  let ρ : ↥A₀ →* N ⧸ CFSG.pCore 2 N :=
    (QuotientGroup.mk' (CFSG.pCore 2 N)).comp A₀.subtype
  have hρrange : ρ.range = A₀.map (QuotientGroup.mk' (CFSG.pCore 2 N)) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hcomap : ρ.ker = (CFSG.pCore 2 N).comap A₀.subtype :=
    (MonoidHom.comap_ker (QuotientGroup.mk' (CFSG.pCore 2 N)) A₀.subtype).symm.trans
      (by rw [QuotientGroup.ker_mk'])
  have hH : IsPGroup 2 ↥((CFSG.pCore 2 N).comap A₀.subtype) := by
    have hmap : IsPGroup 2 ↥(Subgroup.map A₀.subtype ((CFSG.pCore 2 N).comap A₀.subtype)) := by
      apply IsPGroup.to_le (CFSG.pCore_isPGroup (p := 2) (G := N))
      rw [Subgroup.map_comap_eq, Subgroup.range_subtype]
      exact inf_le_right
    exact IsPGroup.of_equiv hmap
      (Subgroup.equivMapOfInjective ((CFSG.pCore 2 N).comap A₀.subtype) A₀.subtype
        A₀.subtype_injective).symm
  have hker_le : ρ.ker ≤ CFSG.pCore 2 ↥A₀ :=
    CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup (MonoidHom.normal_ker ρ)
      (hcomap.symm ▸ hH)
  let g : ↥A₀ ⧸ ρ.ker →* (↥A₀ ⧸ CFSG.pCore 2 ↥A₀) :=
    QuotientGroup.lift ρ.ker (QuotientGroup.mk' (CFSG.pCore 2 ↥A₀))
      (by rw [QuotientGroup.ker_mk']; exact hker_le)
  have hgsurj : Function.Surjective g := by
    intro x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥A₀) x
    exact ⟨QuotientGroup.mk' ρ.ker a, QuotientGroup.lift_mk' ρ.ker _ a⟩
  let e : ↥A₀ ⧸ ρ.ker ≃* ↥(A₀.map (QuotientGroup.mk' (CFSG.pCore 2 N))) :=
    (QuotientGroup.quotientKerEquivRange ρ).trans (MulEquiv.subgroupCongr hρrange)
  refine ⟨g.comp e.symm.toMonoidHom, hgsurj.comp e.symm.surjective, ?_⟩
  have hker_g : g.ker = (CFSG.pCore 2 ↥A₀).map (QuotientGroup.mk' ρ.ker) := by
    rw [show g = QuotientGroup.lift ρ.ker (QuotientGroup.mk' (CFSG.pCore 2 ↥A₀)) _ from rfl,
      QuotientGroup.ker_lift, QuotientGroup.ker_mk']
  have hker_σ : (g.comp e.symm.toMonoidHom).ker =
      (CFSG.pCore 2 ↥A₀).map (e.toMonoidHom.comp (QuotientGroup.mk' ρ.ker)) := by
    have h1 : (g.comp e.symm.toMonoidHom).ker = g.ker.map e.toMonoidHom := by
      simpa using MonoidHom.ker_comp_mulEquiv (g := g) (iso := e.symm)
    rw [h1, hker_g, Subgroup.map_map]
  rw [hker_σ]
  exact (CFSG.pCore_isPGroup (p := 2) (G := ↥A₀)).of_surjective
    ((e.toMonoidHom.comp (QuotientGroup.mk' ρ.ker)).subgroupMap (CFSG.pCore 2 ↥A₀))
    (MonoidHom.subgroupMap_surjective _ _)

end Sigma

theorem ggRCS_kv_sigma_exists_formula {N : Type} [Group N] (A₀ : Subgroup N) :
    ∃ σ : ↥(A₀.map (QuotientGroup.mk' (CFSG.pCore 2 N))) →*
        (↥A₀ ⧸ CFSG.pCore 2 ↥A₀),
      Function.Surjective σ ∧ IsPGroup 2 ↥σ.ker ∧
      ∀ a : ↥A₀,
        σ ⟨(QuotientGroup.mk' (CFSG.pCore 2 N)) a.1,
            Subgroup.mem_map_of_mem _ a.2⟩ =
          (QuotientGroup.mk' (CFSG.pCore 2 ↥A₀)) a := by
  let ρ : ↥A₀ →* N ⧸ CFSG.pCore 2 N :=
    (QuotientGroup.mk' (CFSG.pCore 2 N)).comp A₀.subtype
  have hρrange : ρ.range = A₀.map (QuotientGroup.mk' (CFSG.pCore 2 N)) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hcomap : ρ.ker = (CFSG.pCore 2 N).comap A₀.subtype :=
    (MonoidHom.comap_ker (QuotientGroup.mk' (CFSG.pCore 2 N)) A₀.subtype).symm.trans
      (by rw [QuotientGroup.ker_mk'])
  have hH : IsPGroup 2 ↥((CFSG.pCore 2 N).comap A₀.subtype) := by
    have hmap : IsPGroup 2 ↥(Subgroup.map A₀.subtype ((CFSG.pCore 2 N).comap A₀.subtype)) := by
      apply IsPGroup.to_le (CFSG.pCore_isPGroup (p := 2) (G := N))
      rw [Subgroup.map_comap_eq, Subgroup.range_subtype]
      exact inf_le_right
    exact IsPGroup.of_equiv hmap
      (Subgroup.equivMapOfInjective ((CFSG.pCore 2 N).comap A₀.subtype) A₀.subtype
        A₀.subtype_injective).symm
  have hker_le : ρ.ker ≤ CFSG.pCore 2 ↥A₀ :=
    CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup (MonoidHom.normal_ker ρ)
      (hcomap.symm ▸ hH)
  let g : ↥A₀ ⧸ ρ.ker →* (↥A₀ ⧸ CFSG.pCore 2 ↥A₀) :=
    QuotientGroup.lift ρ.ker (QuotientGroup.mk' (CFSG.pCore 2 ↥A₀))
      (by rw [QuotientGroup.ker_mk']; exact hker_le)
  have hgsurj : Function.Surjective g := by
    intro x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥A₀) x
    exact ⟨QuotientGroup.mk' ρ.ker a, QuotientGroup.lift_mk' ρ.ker _ a⟩
  let e : ↥A₀ ⧸ ρ.ker ≃* ↥(A₀.map (QuotientGroup.mk' (CFSG.pCore 2 N))) :=
    (QuotientGroup.quotientKerEquivRange ρ).trans (MulEquiv.subgroupCongr hρrange)
  refine ⟨g.comp e.symm.toMonoidHom, hgsurj.comp e.symm.surjective, ?_, ?_⟩
  · have hker_g : g.ker = (CFSG.pCore 2 ↥A₀).map (QuotientGroup.mk' ρ.ker) := by
      rw [show g = QuotientGroup.lift ρ.ker (QuotientGroup.mk' (CFSG.pCore 2 ↥A₀)) _ from rfl,
        QuotientGroup.ker_lift, QuotientGroup.ker_mk']
    have hker_σ : (g.comp e.symm.toMonoidHom).ker =
        (CFSG.pCore 2 ↥A₀).map (e.toMonoidHom.comp (QuotientGroup.mk' ρ.ker)) := by
      have h1 : (g.comp e.symm.toMonoidHom).ker = g.ker.map e.toMonoidHom := by
        simpa using MonoidHom.ker_comp_mulEquiv (g := g) (iso := e.symm)
      rw [h1, hker_g, Subgroup.map_map]
    rw [hker_σ]
    exact (CFSG.pCore_isPGroup (p := 2) (G := ↥A₀)).of_surjective
      ((e.toMonoidHom.comp (QuotientGroup.mk' ρ.ker)).subgroupMap (CFSG.pCore 2 ↥A₀))
      (MonoidHom.subgroupMap_surjective _ _)
  · intro a
    have he : e.symm ⟨(QuotientGroup.mk' (CFSG.pCore 2 N)) a.1,
        Subgroup.mem_map_of_mem _ a.2⟩ = QuotientGroup.mk' ρ.ker a := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    change g (e.symm ⟨(QuotientGroup.mk' (CFSG.pCore 2 N)) a.1,
      Subgroup.mem_map_of_mem _ a.2⟩) = QuotientGroup.mk' (CFSG.pCore 2 ↥A₀) a
    rw [he]
    exact QuotientGroup.lift_mk' ρ.ker _ a

section SigmaBar

variable {G : Type} [Group G] [Finite G]

theorem ggRCS_kv_sigma_bar_exists {G₀ : Subgroup G} {r : G} :
    ∃ σ : ↥(ggRCSImg r G₀) →* GGInvolCentBar G₀ r,
      Function.Surjective σ ∧ IsPGroup 2 ↥σ.ker ∧
      ∀ a : ↥(Subgroup.centralizer ({r} : Set G) ⊓ G₀),
        σ ⟨(QuotientGroup.mk' (CFSG.Assembly.pCore 2
              ↥(Subgroup.centralizer ({r} : Set G)))) ⟨a.1, a.2.1⟩,
            Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr a.2.2)⟩ =
          (QuotientGroup.mk' (CFSG.Open.pCore 2
            ↥(Subgroup.centralizer ({r} : Set G) ⊓ G₀))) a := by
  classical
  let N : Subgroup G := Subgroup.centralizer ({r} : Set G)
  let A₀ : Subgroup G := N ⊓ G₀
  obtain ⟨σ₀, hσ₀surj, hσ₀ker, hσ₀formula⟩ :=
    ggRCS_kv_sigma_exists_formula (N := ↥N) (A₀ := G₀.subgroupOf N)
  let eA : ↥(G₀.subgroupOf N) ≃* ↥A₀ :=
    (Subgroup.equivMapOfInjective (G₀.subgroupOf N) N.subtype N.subtype_injective).trans
      (MulEquiv.subgroupCongr (by rw [Subgroup.subgroupOf_map_subtype, inf_comm]))
  have heQ : Subgroup.map (↑eA) (CFSG.pCore 2 ↥(G₀.subgroupOf N)) =
      CFSG.pCore 2 ↥A₀ := by
    convert CFSG.pCore_map_iso 2 eA using 2
    rfl
  let eQ : (↥(G₀.subgroupOf N) ⧸ CFSG.pCore 2 ↥(G₀.subgroupOf N)) ≃*
      (↥A₀ ⧸ CFSG.pCore 2 ↥A₀) :=
    QuotientGroup.congr _ _ eA heQ
  let σ : ↥(ggRCSImg r G₀) →* GGInvolCentBar G₀ r := eQ.toMonoidHom.comp σ₀
  have hσsurj : Function.Surjective σ := eQ.surjective.comp hσ₀surj
  have hσker : IsPGroup 2 ↥σ.ker := by
    have h : σ.ker = σ₀.ker := by
      show (eQ.toMonoidHom.comp σ₀).ker = σ₀.ker
      exact MonoidHom.ker_comp_of_injective σ₀ eQ.toMonoidHom eQ.injective
    rw [h]
    exact hσ₀ker
  refine ⟨σ, hσsurj, hσker, ?_⟩
  intro a
  let a' : ↥(G₀.subgroupOf N) := ⟨⟨a.1, a.2.1⟩, Subgroup.mem_subgroupOf.mpr a.2.2⟩
  have ha'e : eA a' = a := Subtype.ext rfl
  have hx : (⟨(QuotientGroup.mk' (CFSG.Assembly.pCore 2 ↥N)) a'.1,
      Subgroup.mem_map_of_mem _ a'.2⟩ : ↥(ggRCSImg r G₀)) =
      ⟨(QuotientGroup.mk' (CFSG.Assembly.pCore 2 ↥N)) ⟨a.1, a.2.1⟩,
        Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr a.2.2)⟩ := Subtype.ext rfl
  rw [← hx]
  show eQ (σ₀ ⟨(QuotientGroup.mk' (CFSG.Assembly.pCore 2 ↥N)) a'.1,
    Subgroup.mem_map_of_mem _ a'.2⟩) =
    (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥(N ⊓ G₀))) a
  rw [hσ₀formula a']
  have h1 : eQ (QuotientGroup.mk' (CFSG.pCore 2 ↥(G₀.subgroupOf N)) a') =
      QuotientGroup.mk' (CFSG.pCore 2 ↥A₀) (eA a') := by
    change (QuotientGroup.congr (CFSG.pCore 2 ↥(G₀.subgroupOf N))
      (CFSG.pCore 2 ↥A₀) eA heQ) (QuotientGroup.mk a') =
        QuotientGroup.mk' (CFSG.pCore 2 ↥A₀) (eA a')
    rw [QuotientGroup.congr_mk]
    rfl
  rw [h1, ha'e]

end SigmaBar

theorem ggRCS_kv_componentInj_bar {G : Type} [Group G] [Finite G] {G₀ : Subgroup G} {r : G}
    {K : Subgroup (GGRCSNbar r)}
    (hSch : ∀ D : Subgroup G, D ≤ Subgroup.normalizer (G₀ : Set G) → ⁅D, D⁆ = D → D ≤ G₀)
    (hK : K.IsSubnormal) :
    ∃ F : Subgroup ↥(K ⊓ ggRCSImg r (Subgroup.normalizer (G₀ : Set G))) →
        Subgroup (GGInvolCentBar G₀ r),
      Set.InjOn F {C | CFSG.Open.IsComponentOf C ⊤} ∧
      ∀ C, CFSG.Open.IsComponentOf C ⊤ → CFSG.Open.IsComponentOf (F C) ⊤ ∧
        Nonempty (↥(F C) ⧸ Subgroup.center ↥(F C) ≃* ↥C ⧸ Subgroup.center ↥C) := by
  classical
  let N : Subgroup G := Subgroup.centralizer ({r} : Set G)
  let M : Subgroup G := Subgroup.normalizer (G₀ : Set G)
  let V : Subgroup (GGRCSNbar r) := ggRCSImg r M
  let Y : Subgroup (GGRCSNbar r) := ggRCSImg r G₀
  let A₀ : Subgroup G := N ⊓ G₀
  obtain ⟨σ₀, hσ₀surj, hσ₀ker⟩ :=
    ggRCS_kv_sigma_exists (N := ↥N) (A₀ := G₀.subgroupOf N)
  let eA : ↥(G₀.subgroupOf N) ≃* ↥A₀ :=
    (Subgroup.equivMapOfInjective (G₀.subgroupOf N) N.subtype N.subtype_injective).trans
      (MulEquiv.subgroupCongr (by rw [Subgroup.subgroupOf_map_subtype, inf_comm]))
  let eQ : (↥(G₀.subgroupOf N) ⧸ CFSG.pCore 2 ↥(G₀.subgroupOf N)) ≃*
      (↥A₀ ⧸ CFSG.pCore 2 ↥A₀) :=
    QuotientGroup.congr _ _ eA (CFSG.pCore_map_iso 2 eA)
  let σ : ↥Y →* GGInvolCentBar G₀ r := eQ.toMonoidHom.comp σ₀
  have hσsurj : Function.Surjective σ := eQ.surjective.comp hσ₀surj
  have hσker : IsPGroup 2 ↥σ.ker := by
    have h : σ.ker = σ₀.ker := by
      show (eQ.toMonoidHom.comp σ₀).ker = σ₀.ker
      exact MonoidHom.ker_comp_of_injective σ₀ eQ.toMonoidHom eQ.injective
    rw [h]
    exact hσ₀ker
  have hσsol : Group.IsSolvable ↥σ.ker := by
    haveI : Group.IsNilpotent ↥σ.ker := hσker.isNilpotent
    exact IsNilpotent.to_isSolvable
  have hYV : Y ≤ V := by
    apply Subgroup.map_mono
    exact Subgroup.comap_mono (Subgroup.le_normalizer (H := G₀))
  let Gc : Subgroup ↥(K ⊓ V) → Subgroup ↥Y :=
    fun C => (((C.map (K ⊓ V).subtype).subgroupOf V).map V.subtype).subgroupOf Y
  refine ⟨fun C => (Gc C).map σ, ?_, ?_⟩
  · intro C₁ hC₁ C₂ hC₂ heq
    have key : ∀ C : Subgroup ↥(K ⊓ V), CFSG.Open.IsComponentOf C ⊤ →
        CFSG.Open.IsComponentOf (Gc C) ⊤ ∧
          (Gc C).map Y.subtype = C.map (K ⊓ V).subtype := by
      intro C hC
      have hE : CFSG.Open.IsComponentOf
          ((C.map (K ⊓ V).subtype).subgroupOf V) ⊤ :=
        (ggRCS_component_inf_lift hK hC).1
      have hC' : CFSG.Open.IsComponentOf
          (((C.map (K ⊓ V).subtype).subgroupOf V).map V.subtype) V :=
        ggRCS_isComponentOf_map_subtype hE
      have hC'Y : (((C.map (K ⊓ V).subtype).subgroupOf V).map V.subtype) ≤ Y :=
        ggRCS_component_le_map_of_schreier le_rfl hSch hC'
      refine ⟨ggRCS_isComponentOf_subgroupOf hC' hC'Y hYV, ?_⟩
      have h1 : (Gc C).map Y.subtype =
          (((C.map (K ⊓ V).subtype).subgroupOf V).map V.subtype) :=
        Subgroup.map_subgroupOf_eq_of_le hC'Y
      have h2 : (((C.map (K ⊓ V).subtype).subgroupOf V).map V.subtype) =
          C.map (K ⊓ V).subtype :=
        Subgroup.map_subgroupOf_eq_of_le ((Subgroup.map_subtype_le C).trans inf_le_right)
      rw [h1, h2]
    have hσinj := ggRCS_map_injOn_components_of_solvable_ker σ hσsurj hσsol
    have hGeq : Gc C₁ = Gc C₂ := hσinj (key C₁ hC₁).1 (key C₂ hC₂).1 heq
    have hmap := congrArg (Subgroup.map Y.subtype) hGeq
    rw [(key C₁ hC₁).2, (key C₂ hC₂).2] at hmap
    exact Subgroup.map_injective (K ⊓ V).subtype_injective hmap
  · intro C hC
    let E : Subgroup ↥V := (C.map (K ⊓ V).subtype).subgroupOf V
    let C' : Subgroup (GGRCSNbar r) := E.map V.subtype
    have hE : CFSG.Open.IsComponentOf E ⊤ := (ggRCS_component_inf_lift hK hC).1
    obtain ⟨e₁⟩ := (ggRCS_component_inf_lift hK hC).2
    have hC' : CFSG.Open.IsComponentOf C' V := ggRCS_isComponentOf_map_subtype hE
    have hC'Y : C' ≤ Y := ggRCS_component_le_map_of_schreier le_rfl hSch hC'
    have hE'' : CFSG.Open.IsComponentOf (Gc C) ⊤ :=
      ggRCS_isComponentOf_subgroupOf hC' hC'Y hYV
    obtain ⟨hF, e₄⟩ := ggRCS_component_map_solvable_ker σ hσsurj hσsol hE''
    obtain ⟨e₄⟩ := e₄
    have e₂ : ↥C' ⧸ Subgroup.center ↥C' ≃* ↥E ⧸ Subgroup.center ↥E :=
      (QuotientGroup.congr (Subgroup.center ↥E) (Subgroup.center ↥C')
        (Subgroup.equivMapOfInjective E V.subtype V.subtype_injective)
        (Subgroup.map_center_eq _)).symm
    have e₃ : ↥(Gc C) ⧸ Subgroup.center ↥(Gc C) ≃* ↥C' ⧸ Subgroup.center ↥C' :=
      QuotientGroup.congr (Subgroup.center ↥(C'.subgroupOf Y)) (Subgroup.center ↥C')
        (Subgroup.subgroupOfEquivOfLe hC'Y) (Subgroup.map_center_eq _)
    exact ⟨hF, ⟨e₄.trans (e₃.trans (e₂.trans e₁))⟩⟩

end CFSG.StandardType
