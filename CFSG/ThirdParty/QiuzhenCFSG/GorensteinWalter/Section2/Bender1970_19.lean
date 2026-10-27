module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
import Mathlib.GroupTheory.Sylow
import Mathlib.Basic.Nontrivial.Defs

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise commutatorElement BigOperators

namespace CFSG.GorensteinWalter

universe u

noncomputable section

private theorem isQuasisimple_mulEquiv
    {G H : Type u} [Group G] [Group H]
    (e : G ≃* H) (hG : IsQuasisimple G) :
    IsQuasisimple H := by
  have hNontriv : Nontrivial H := by
    let : Nontrivial G := hG.1
    exact e.toEquiv.injective.nontrivial
  have hPerf : Group.IsPerfect H := by
    let : Group.IsPerfect G := (Group.isPerfect_def).2 hG.2.1
    exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.toEquiv.surjective
  have hSimple : IsSimpleGroup (H ⧸ Subgroup.center H) := by
    have he : (Subgroup.center G).map e.toMonoidHom = Subgroup.center H := by
      apply le_antisymm
      · intro x hx
        rcases hx with ⟨y, hy, rfl⟩
        exact (Subgroup.centerCongr e ⟨y, hy⟩).2
      · intro x hx
        refine ⟨e.symm x, ?_, ?_⟩
        · exact ((Subgroup.centerCongr e).symm ⟨x, hx⟩).2
        · exact e.apply_symm_apply x
    exact (MulEquiv.isSimpleGroup_congr
      (QuotientGroup.congr (Subgroup.center G) (Subgroup.center H) e he)).mp hG.2.2
  exact ⟨hNontriv, (Group.isPerfect_def).1 hPerf, hSimple⟩

private theorem isComponentOf_map_of_mulEquiv
    {G H : Type u} [Group G] [Group H] (e : G ≃* H)
    {E : Subgroup G} (hE : IsComponentOf E (⊤ : Subgroup G)) :
    IsComponentOf (E.map e.toMonoidHom) (⊤ : Subgroup H) := by
  refine ⟨le_top, ?_, ?_⟩
  · have hE_sn : E.IsSubnormal := by
      have h' : ((E.subgroupOf (⊤ : Subgroup G)).map (⊤ : Subgroup G).subtype).IsSubnormal :=
        hE.2.1.map (f := (⊤ : Subgroup G).subtype)
          (by intro x; exact ⟨⟨x, trivial⟩, rfl⟩)
      rwa [Subgroup.map_subgroupOf_eq_of_le (le_top : E ≤ (⊤ : Subgroup G))] at h'
    have hmap_sn : (E.map e.toMonoidHom).IsSubnormal :=
      Subgroup.IsSubnormal.map (f := e.toMonoidHom) e.toEquiv.surjective hE_sn
    exact hmap_sn.subgroupOf (K := (⊤ : Subgroup H))
  · exact isQuasisimple_mulEquiv (Subgroup.equivMapOfInjective E e.toMonoidHom e.injective)
      hE.2.2

private theorem componentLayerOf_top_map_of_mulEquiv
    {G H : Type u} [Group G] [Group H] (e : G ≃* H) :
    (componentLayerOf (⊤ : Subgroup G)).map e.toMonoidHom =
      componentLayerOf (⊤ : Subgroup H) := by
  rw [componentLayerOf, componentLayerOf]
  apply le_antisymm
  · have hle : sSup {E : Subgroup G | IsComponentOf E (⊤ : Subgroup G)} ≤
        (sSup {E' : Subgroup H | IsComponentOf E' (⊤ : Subgroup H)}).comap e.toMonoidHom := by
      refine sSup_le ?_
      intro E hE
      exact (Subgroup.map_le_iff_le_comap (K := E)
        (H := (sSup {E' : Subgroup H | IsComponentOf E' (⊤ : Subgroup H)} : Subgroup H))
        (f := e.toMonoidHom)).1
        (le_sSup (s := {E' : Subgroup H | IsComponentOf E' (⊤ : Subgroup H)})
          (isComponentOf_map_of_mulEquiv e hE))
    exact (Subgroup.map_mono (f := e.toMonoidHom) hle).trans
      (Subgroup.map_comap_le (f := e.toMonoidHom)
        (H := (sSup {E' : Subgroup H | IsComponentOf E' (⊤ : Subgroup H)} : Subgroup H)))
  · refine sSup_le ?_
    intro F hF
    have hF' : IsComponentOf (F.map e.symm.toMonoidHom) (⊤ : Subgroup G) :=
      isComponentOf_map_of_mulEquiv e.symm hF
    have hleG : F.map e.symm.toMonoidHom ≤
        sSup {E : Subgroup G | IsComponentOf E (⊤ : Subgroup G)} :=
      le_sSup (s := {E : Subgroup G | IsComponentOf E (⊤ : Subgroup G)}) hF'
    have hmap : (F.map e.symm.toMonoidHom).map e.toMonoidHom = F := by
      rw [Subgroup.map_map]
      have hid : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id H := by
        apply MonoidHom.ext
        intro x
        exact e.apply_symm_apply x
      rw [hid, Subgroup.map_id]
    exact hmap ▸ (Subgroup.map_mono (f := e.toMonoidHom) hleG)

private theorem map_fittingSubgroup_le_of_surjective
    {G H : Type u} [Group G] [Group H] [Finite G] [Finite H]
    (f : G →* H) (hf : Function.Surjective f) :
    (fittingSubgroup G).map f ≤ fittingSubgroup H := by
  have hmap_normal : ((fittingSubgroup G).map f).Normal :=
    Subgroup.Normal.map (H := fittingSubgroup G) inferInstance f hf
  have hmap_nil : Group.IsNilpotent ↥((fittingSubgroup G).map f) := by
    have : Group.IsNilpotent ↥(fittingSubgroup G) := by infer_instance
    let ψ : fittingSubgroup G →* ↥((fittingSubgroup G).map f) :=
      { toFun := fun g => ⟨f g, Subgroup.mem_map.mpr ⟨g.1, g.2, rfl⟩⟩
        map_one' := by ext; simp
        map_mul' := by intro a b; ext; simp [map_mul] }
    have hψsurj : Function.Surjective ψ := by
      intro x
      rcases (Subgroup.mem_map).1 x.2 with ⟨g, hg, hx⟩
      refine ⟨⟨g, hg⟩, ?_⟩
      apply Subtype.ext
      exact hx
    exact Group.nilpotent_of_surjective ψ hψsurj
  exact le_sSup ⟨hmap_normal, hmap_nil⟩

private theorem map_fittingSubgroup_of_mulEquiv
    {G H : Type u} [Group G] [Group H] [Finite G] [Finite H]
    (e : G ≃* H) :
    (fittingSubgroup G).map e.toMonoidHom = fittingSubgroup H := by
  apply le_antisymm
  · exact map_fittingSubgroup_le_of_surjective e.toMonoidHom e.surjective
  · have hback : (fittingSubgroup H).map e.symm.toMonoidHom ≤ fittingSubgroup G :=
      map_fittingSubgroup_le_of_surjective e.symm.toMonoidHom e.symm.surjective
    have hmap : ((fittingSubgroup H).map e.symm.toMonoidHom).map e.toMonoidHom ≤
        (fittingSubgroup G).map e.toMonoidHom :=
      Subgroup.map_mono (f := e.toMonoidHom) hback
    have hleft : ((fittingSubgroup H).map e.symm.toMonoidHom).map e.toMonoidHom =
        fittingSubgroup H := by
      rw [Subgroup.map_map]
      have hcomp : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id H := by
        ext x
        simp
      rw [hcomp, Subgroup.map_id]
    rw [hleft] at hmap
    exact hmap

private theorem generalizedFittingSubgroupOf_top_map_of_mulEquiv
    {G H : Type u} [Group G] [Group H] [Finite G] [Finite H]
    (e : G ≃* H) :
    (generalizedFittingSubgroupOf (⊤ : Subgroup G)).map e.toMonoidHom =
      generalizedFittingSubgroupOf (⊤ : Subgroup H) := by
  rw [generalizedFittingSubgroupOf, generalizedFittingSubgroupOf, Subgroup.map_sup]
  congr 1
  · -- Fitting part
    change ((fittingSubgroup (↥(⊤ : Subgroup G))).map (⊤ : Subgroup G).subtype).map e.toMonoidHom =
      (fittingSubgroup (↥(⊤ : Subgroup H))).map (⊤ : Subgroup H).subtype
    have htopG : (⊤ : Subgroup G).subtype = (Subgroup.topEquiv (G := G)).toMonoidHom := by
      ext x
      rfl
    have htopH : (⊤ : Subgroup H).subtype = (Subgroup.topEquiv (G := H)).toMonoidHom := by
      ext x
      rfl
    let e' : ↥(⊤ : Subgroup G) ≃* ↥(⊤ : Subgroup H) :=
      (Subgroup.topEquiv (G := G)).trans (e.trans (Subgroup.topEquiv (G := H)).symm)
    have hcomp : e.toMonoidHom.comp (Subgroup.topEquiv (G := G)).toMonoidHom =
        (Subgroup.topEquiv (G := H)).toMonoidHom.comp e'.toMonoidHom := by
      ext x
      rfl
    calc
      ((fittingSubgroup (↥(⊤ : Subgroup G))).map (⊤ : Subgroup G).subtype).map e.toMonoidHom
          = ((fittingSubgroup (↥(⊤ : Subgroup G))).map
              (Subgroup.topEquiv (G := G)).toMonoidHom).map e.toMonoidHom := by rw [htopG]
      _ = (fittingSubgroup (↥(⊤ : Subgroup G))).map
            (e.toMonoidHom.comp (Subgroup.topEquiv (G := G)).toMonoidHom) := by
            rw [Subgroup.map_map]
      _ = (fittingSubgroup (↥(⊤ : Subgroup G))).map
            ((Subgroup.topEquiv (G := H)).toMonoidHom.comp e'.toMonoidHom) := by rw [hcomp]
      _ = ((fittingSubgroup (↥(⊤ : Subgroup G))).map e'.toMonoidHom).map
            (Subgroup.topEquiv (G := H)).toMonoidHom := by
            rw [Subgroup.map_map]
      _ = (fittingSubgroup (↥(⊤ : Subgroup H))).map
            (Subgroup.topEquiv (G := H)).toMonoidHom := by
            rw [map_fittingSubgroup_of_mulEquiv e']
      _ = (fittingSubgroup (↥(⊤ : Subgroup H))).map (⊤ : Subgroup H).subtype := by rw [htopH]
  · exact componentLayerOf_top_map_of_mulEquiv e

public theorem componentLayerOf_subgroup_top_eq
    {G : Type u} [Group G] (C : Subgroup G) :
    (componentLayerOf (⊤ : Subgroup (↥C))).map C.subtype = componentLayerOf C := by
  classical
  apply le_antisymm
  · rw [componentLayerOf, componentLayerOf]
    have hle : sSup {E : Subgroup (↥C) | IsComponentOf E (⊤ : Subgroup (↥C))} ≤
        (sSup {E' : Subgroup G | IsComponentOf E' C}).comap C.subtype := by
      refine sSup_le ?_
      intro E hEcomp
      have hE_leC : (E.map C.subtype : Subgroup G) ≤ C := Subgroup.map_subtype_le (H := C) E
      have hE_sn : ((E.map C.subtype : Subgroup G).subgroupOf C).IsSubnormal := by
        have hEq : ((E.map C.subtype : Subgroup G).subgroupOf C) = E := by
          ext x
          constructor
          · intro hx
            rw [Subgroup.mem_subgroupOf] at hx
            rcases (Subgroup.mem_map).1 hx with ⟨y, hy, hyx⟩
            have hyx' : (y : ↥C) = x := C.subtype_injective hyx
            simpa [hyx'] using hy
          · intro hx
            rw [Subgroup.mem_subgroupOf]
            exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
        have hE_sn_top : (E.subgroupOf (⊤ : Subgroup (↥C))).IsSubnormal := hEcomp.2.1
        have hE_snC : E.IsSubnormal := by
          have h' : ((E.subgroupOf (⊤ : Subgroup (↥C))).map (⊤ : Subgroup (↥C)).subtype).IsSubnormal :=
            hE_sn_top.map (f := (⊤ : Subgroup (↥C)).subtype)
              (by intro x; exact ⟨⟨x, trivial⟩, rfl⟩)
          rwa [Subgroup.map_subgroupOf_eq_of_le (le_top : E ≤ (⊤ : Subgroup (↥C)))] at h'
        rwa [hEq]
      have hE_q : IsQuasisimple (E.map C.subtype : Subgroup G) := by
        exact isQuasisimple_mulEquiv (Subgroup.equivMapOfInjective E C.subtype C.subtype_injective)
          hEcomp.2.2
      exact (Subgroup.map_le_iff_le_comap (K := E)
        (H := (sSup {E' : Subgroup G | IsComponentOf E' C} : Subgroup G))
        (f := C.subtype)).1
        (le_sSup (s := {E' : Subgroup G | IsComponentOf E' C})
          ⟨hE_leC, hE_sn, hE_q⟩)
    exact (Subgroup.map_mono (f := C.subtype) hle).trans
      (Subgroup.map_comap_le (f := C.subtype)
        (H := (sSup {E' : Subgroup G | IsComponentOf E' C} : Subgroup G)))
  · rw [componentLayerOf, componentLayerOf]
    refine sSup_le ?_
    intro E hE
    let E0 : Subgroup (↥C) := E.subgroupOf C
    have hE0_le : E0 ≤ (⊤ : Subgroup (↥C)) := le_top
    have hE0_sn : (E0.subgroupOf (⊤ : Subgroup (↥C))).IsSubnormal := by
      exact hE.2.1.subgroupOf (K := (⊤ : Subgroup (↥C)))
    have hE0_q : IsQuasisimple E0 := by
      exact isQuasisimple_mulEquiv (Subgroup.subgroupOfEquivOfLe hE.1).symm hE.2.2
    have hE0_comp : IsComponentOf E0 (⊤ : Subgroup (↥C)) := ⟨hE0_le, hE0_sn, hE0_q⟩
    have hmap : E0.map C.subtype = E := Subgroup.map_subgroupOf_eq_of_le hE.1
    exact (le_of_eq hmap.symm).trans (Subgroup.map_mono (f := C.subtype)
      (le_sSup (s := {E' : Subgroup (↥C) | IsComponentOf E' (⊤ : Subgroup (↥C))}) hE0_comp))

public theorem generalizedFittingSubgroupOf_subgroup_top_eq
    {G : Type u} [Group G] [Finite G] (H : Subgroup G) :
    (generalizedFittingSubgroupOf (⊤ : Subgroup (↥H))).map H.subtype =
      generalizedFittingSubgroupOf H := by
  rw [generalizedFittingSubgroupOf, generalizedFittingSubgroupOf, Subgroup.map_sup]
  congr 1
  · let A : Subgroup (↥H) := ⊤
    let e : ↥A ≃* ↥H := Subgroup.topEquiv (G := ↥H)
    have hA : A.subtype = e.toMonoidHom := by
      ext x
      rfl
    have : Finite (↥A) :=
      Finite.of_equiv (↥H) (Subgroup.topEquiv (G := ↥H)).toEquiv.symm
    calc
      (fittingSubgroupOf (⊤ : Subgroup (↥H))).map H.subtype
          = ((fittingSubgroup (↥A)).map A.subtype).map H.subtype := by rfl
      _ = ((fittingSubgroup (↥A)).map e.toMonoidHom).map H.subtype := by rw [hA]
      _ = (fittingSubgroup (↥H)).map H.subtype := by rw [map_fittingSubgroup_of_mulEquiv e]
      _ = fittingSubgroupOf H := by rfl
  · exact componentLayerOf_subgroup_top_eq H

private theorem generalizedFittingSubgroupOf_map_of_equiv_subgroup
    {G H : Type u} [Group G] [Group H] [Finite G] [Finite H]
    (e : G ≃* H) (K : Subgroup G) :
    (generalizedFittingSubgroupOf K).map e.toMonoidHom =
      generalizedFittingSubgroupOf (K.map e.toMonoidHom) := by
  let K' : Subgroup H := K.map e.toMonoidHom
  let eK : ↥K ≃* ↥K' := Subgroup.equivMapOfInjective K e.toMonoidHom e.injective
  have hTop : (generalizedFittingSubgroupOf (⊤ : Subgroup (↥K))).map eK.toMonoidHom =
      generalizedFittingSubgroupOf (⊤ : Subgroup (↥K')) :=
    generalizedFittingSubgroupOf_top_map_of_mulEquiv eK
  have hKmap : (generalizedFittingSubgroupOf (⊤ : Subgroup (↥K))).map K.subtype =
      generalizedFittingSubgroupOf K :=
    generalizedFittingSubgroupOf_subgroup_top_eq K
  have hK'map : (generalizedFittingSubgroupOf (⊤ : Subgroup (↥K'))).map K'.subtype =
      generalizedFittingSubgroupOf K' :=
    generalizedFittingSubgroupOf_subgroup_top_eq K'
  have hcomp : e.toMonoidHom.comp K.subtype = K'.subtype.comp eK.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    rfl
  calc
    (generalizedFittingSubgroupOf K).map e.toMonoidHom
        = ((generalizedFittingSubgroupOf (⊤ : Subgroup (↥K))).map K.subtype).map e.toMonoidHom := by
          rw [hKmap]
    _ = (generalizedFittingSubgroupOf (⊤ : Subgroup (↥K))).map
          (e.toMonoidHom.comp K.subtype) := by rw [Subgroup.map_map]
    _ = (generalizedFittingSubgroupOf (⊤ : Subgroup (↥K))).map
          (K'.subtype.comp eK.toMonoidHom) := by rw [hcomp]
    _ = ((generalizedFittingSubgroupOf (⊤ : Subgroup (↥K))).map eK.toMonoidHom).map K'.subtype := by
          rw [Subgroup.map_map]
    _ = (generalizedFittingSubgroupOf (⊤ : Subgroup (↥K'))).map K'.subtype := by rw [hTop]
    _ = generalizedFittingSubgroupOf K' := by rw [hK'map]

private theorem isPGroup_of_normal_nilpotent_of_extension
    {G : Type u} [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime) (N : Subgroup G) (hNnorm : N.Normal)
    (R : Subgroup G) (hRnorm : R.Normal) (hRnil : Group.IsNilpotent R)
    (hN : IsPGroup p (generalizedFittingSubgroupOf N))
    (hQ : IsPGroup p (G ⧸ N)) :
    IsPGroup p R := by
  classical
  let : N.Normal := hNnorm
  let : R.Normal := hRnorm
  let K : Subgroup G := R ⊓ N
  have hKleR : K ≤ R := inf_le_left
  have hKleN : K ≤ N := inf_le_right
  have : (K.subgroupOf R).Normal := by
    refine (Subgroup.normal_subgroupOf_iff hKleR).mpr ?_
    intro x hx r hr
    rcases r with ⟨xR, xN⟩
    exact ⟨R.mul_mem (R.mul_mem hr xR) (R.inv_mem hr), hNnorm.conj_mem x xN hx⟩
  have hKnormN : IsNormalIn K N := by
    refine ⟨hKleN, ?_⟩
    intro n hn k hk
    rcases hk with ⟨hkR, hkN⟩
    exact ⟨hRnorm.conj_mem k hkR n, N.mul_mem (N.mul_mem hn hkN) (N.inv_mem hn)⟩
  have hKnil : Group.IsNilpotent K := by
    have : Group.IsNilpotent (↥R) := hRnil
    have : Group.IsNilpotent (↥(K.subgroupOf R)) := inferInstance
    exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKleR)
  have hKleF : K ≤ fittingSubgroupOf N :=
    le_fittingSubgroupOf_of_isNormalIn_nilpotent hKleN hKnormN hKnil
  have hKp : IsPGroup p K :=
    hN.to_le (hKleF.trans (le_sup_left : fittingSubgroupOf N ≤ generalizedFittingSubgroupOf N))
  have hKp' : IsPGroup p (K.subgroupOf R) :=
    hKp.of_equiv (Subgroup.subgroupOfEquivOfLe hKleR).symm
  let φ : ↥R →* G ⧸ N := (QuotientGroup.mk' N).comp R.subtype
  have hker : φ.ker = K.subgroupOf R := by
    ext x
    constructor
    · intro hx
      rw [MonoidHom.mem_ker] at hx
      have hxN : (x : G) ∈ N :=
        (QuotientGroup.eq_one_iff (N := N) (x := (x : G))).1 hx
      exact (Subgroup.mem_subgroupOf).mpr ⟨x.2, hxN⟩
    · intro hx
      rw [MonoidHom.mem_ker]
      have hxK : (x : G) ∈ K := (Subgroup.mem_subgroupOf).1 hx
      exact (QuotientGroup.eq_one_iff (N := N) (x := (x : G))).2 hxK.2
  have hker' : K.subgroupOf R = φ.ker := hker.symm
  have hQR : IsPGroup p (R ⧸ K.subgroupOf R) := by
    have hrange : IsPGroup p φ.range := hQ.to_subgroup φ.range
    let e : R ⧸ K.subgroupOf R ≃* φ.range :=
      (QuotientGroup.quotientMulEquivOfEq hker').trans (QuotientGroup.quotientKerEquivRange φ)
    exact hrange.of_equiv e.symm
  let : Fact p.Prime := ⟨hp⟩
  exact isPGroup_of_subgroup_and_quotient (G := ↥R) (N := K.subgroupOf R) hKp' hQR

private theorem componentLayerOf_eq_bot_of_extension
    {G : Type u} [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime) (N : Subgroup G) (hNnorm : N.Normal)
    (hN : IsPGroup p (generalizedFittingSubgroupOf N))
    (hQ : IsPGroup p (G ⧸ N)) :
    componentLayerOf (⊤ : Subgroup G) = ⊥ := by
  classical
  let : N.Normal := hNnorm
  apply le_bot_iff.mp
  rw [componentLayerOf]
  refine sSup_le ?_
  intro L hL
  let M : Subgroup G := L ⊓ N
  have hMleL : M ≤ L := inf_le_left
  have hMleN : M ≤ N := inf_le_right
  have : (M.subgroupOf L).Normal := by
    refine (Subgroup.normal_subgroupOf_iff hMleL).mpr ?_
    intro x hx l hl
    rcases l with ⟨xL, xN⟩
    exact ⟨L.mul_mem (L.mul_mem hl xL) (L.inv_mem hl), hNnorm.conj_mem x xN hx⟩
  let φ : ↥L →* G ⧸ N := (QuotientGroup.mk' N).comp L.subtype
  have hker : φ.ker = M.subgroupOf L := by
    ext x
    constructor
    · intro hx
      rw [MonoidHom.mem_ker] at hx
      have hxN : (x : G) ∈ N :=
        (QuotientGroup.eq_one_iff (N := N) (x := (x : G))).1 hx
      exact (Subgroup.mem_subgroupOf).mpr ⟨x.2, hxN⟩
    · intro hx
      rw [MonoidHom.mem_ker]
      have hxM : (x : G) ∈ M := (Subgroup.mem_subgroupOf).1 hx
      exact (QuotientGroup.eq_one_iff (N := N) (x := (x : G))).2 hxM.2
  have hker' : M.subgroupOf L = φ.ker := hker.symm
  have hQL : IsPGroup p (L ⧸ M.subgroupOf L) := by
    have hrange : IsPGroup p φ.range := hQ.to_subgroup φ.range
    let e : L ⧸ M.subgroupOf L ≃* φ.range :=
      (QuotientGroup.quotientMulEquivOfEq hker').trans (QuotientGroup.quotientKerEquivRange φ)
    exact hrange.of_equiv e.symm
  have hLperf : Group.IsPerfect L := (Group.isPerfect_def).2 hL.2.2.2.1
  let Q : Type u := L ⧸ M.subgroupOf L
  let : Fact p.Prime := ⟨hp⟩
  have hQnil : Group.IsNilpotent Q := IsPGroup.isNilpotent hQL
  let : Group.IsNilpotent Q := hQnil
  have : Group.IsSolvable Q := inferInstance
  have : Group.IsPerfect Q := inferInstance
  have hQsub : Subsingleton Q := by
    by_contra hnot
    have : Nontrivial Q := (not_subsingleton_iff_nontrivial).mp hnot
    exact (Group.IsPerfect.not_isSolvable Q) inferInstance
  have hLleM : L ≤ M := by
    intro l hl
    let q : Q := QuotientGroup.mk' (M.subgroupOf L) ⟨l, hl⟩
    have hq : q = 1 := Subsingleton.elim q 1
    have hlM' : (⟨l, hl⟩ : ↥L) ∈ M.subgroupOf L :=
      (QuotientGroup.eq_one_iff (N := M.subgroupOf L) (x := (⟨l, hl⟩ : ↥L))).1 hq
    exact (Subgroup.mem_subgroupOf).1 hlM'
  have hLleN : L ≤ N := hLleM.trans hMleN
  have hLsn : L.IsSubnormal := by
    have h' : ((L.subgroupOf (⊤ : Subgroup G)).map (⊤ : Subgroup G).subtype).IsSubnormal :=
      hL.2.1.map (f := (⊤ : Subgroup G).subtype)
        (by intro x; exact ⟨⟨x, trivial⟩, rfl⟩)
    rwa [Subgroup.map_subgroupOf_eq_of_le (le_top : L ≤ (⊤ : Subgroup G))] at h'
  have hLsubN : (L.subgroupOf N).IsSubnormal :=
    isSubnormal_subgroupOf_of_subnormal_of_le hLleN hLsn
  have hLcompN : IsComponentOf L N := ⟨hLleN, hLsubN, hL.2.2⟩
  have hLleLayer : L ≤ componentLayerOf N :=
    le_sSup (s := {E : Subgroup G | IsComponentOf E N}) hLcompN
  have hLleFstar : L ≤ generalizedFittingSubgroupOf N :=
    hLleLayer.trans (le_sup_right : componentLayerOf N ≤ generalizedFittingSubgroupOf N)
  have hLp : IsPGroup p L := hN.to_le hLleFstar
  have hLnil : Group.IsNilpotent L := IsPGroup.isNilpotent hLp
  exact False.elim (not_isNilpotent_of_isQuasisimple L hL.2.2 hLnil)

private theorem isPGroup_fittingSubgroup_of_extension
    {G : Type u} [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime) (N : Subgroup G) (hNnorm : N.Normal)
    (hN : IsPGroup p (generalizedFittingSubgroupOf N))
    (hQ : IsPGroup p (G ⧸ N)) :
    IsPGroup p (fittingSubgroupOf (⊤ : Subgroup G)) := by
  classical
  have hCoreP : ∀ q : ℕ, q ∈ (Nat.card (↥(⊤ : Subgroup G))).primeFactors →
      IsPGroup p (qCoreOf (⊤ : Subgroup G) q) := by
    intro q hq
    have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
    let : Fact q.Prime := ⟨hqprime⟩
    have : (qCoreOf (⊤ : Subgroup G) q).Normal := by
      have h := qCoreOf_normal_in (⊤ : Subgroup G) q
      exact (Subgroup.normalizer_eq_top_iff).mp (top_le_iff.mp (le_normalizer_of_isNormalIn h))
    exact isPGroup_of_normal_nilpotent_of_extension p hp N hNnorm (qCoreOf (⊤ : Subgroup G) q)
      (inferInstance : (qCoreOf (⊤ : Subgroup G) q).Normal)
      (IsPGroup.isNilpotent (qCoreOf_isPGroup (⊤ : Subgroup G) q)) hN hQ
  rw [fittingSubgroupOf_eq_iSup_qCoreOf (⊤ : Subgroup G)]
  let ι := (Nat.card (↥(⊤ : Subgroup G))).primeFactors.attach
  have : ∀ q : ι, (qCoreOf (⊤ : Subgroup G) q.1.1).Normal := by
    intro q
    have h := qCoreOf_normal_in (⊤ : Subgroup G) q.1.1
    exact (Subgroup.normalizer_eq_top_iff).mp (top_le_iff.mp (le_normalizer_of_isNormalIn h))
  exact Sylow.iSup_of_normal (fun q : ι => qCoreOf (⊤ : Subgroup G) q.1.1)
    (fun q => hCoreP q.1.1 q.1.2)

public theorem generalizedFittingSubgroupOf_isPGroup_of_extension
    {G : Type u} [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime) (N : Subgroup G) [N.Normal]
    (hN : IsPGroup p (generalizedFittingSubgroupOf N))
    (hQ : IsPGroup p (G ⧸ N)) :
    IsPGroup p (generalizedFittingSubgroupOf (⊤ : Subgroup G)) := by
  have hE : componentLayerOf (⊤ : Subgroup G) = ⊥ :=
    componentLayerOf_eq_bot_of_extension p hp N (inferInstance : N.Normal) hN hQ
  have hF : IsPGroup p (fittingSubgroupOf (⊤ : Subgroup G)) :=
    isPGroup_fittingSubgroup_of_extension p hp N (inferInstance : N.Normal) hN hQ
  rw [generalizedFittingSubgroupOf, hE, sup_bot_eq]
  exact hF

private theorem generalizedFittingSubgroupOf_map_subtype
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (C : Subgroup (↥H)) :
    (generalizedFittingSubgroupOf C).map H.subtype =
      generalizedFittingSubgroupOf (C.map H.subtype) := by
  let D : Subgroup G := C.map H.subtype
  let e : ↥C ≃* ↥D := Subgroup.equivMapOfInjective C H.subtype H.subtype_injective
  have hTopC : (generalizedFittingSubgroupOf (⊤ : Subgroup (↥C))).map C.subtype =
      generalizedFittingSubgroupOf C :=
    generalizedFittingSubgroupOf_subgroup_top_eq C
  have hTopD : (generalizedFittingSubgroupOf (⊤ : Subgroup (↥D))).map D.subtype =
      generalizedFittingSubgroupOf D :=
    generalizedFittingSubgroupOf_subgroup_top_eq D
  have hTopMap : (generalizedFittingSubgroupOf (⊤ : Subgroup (↥C))).map e.toMonoidHom =
      generalizedFittingSubgroupOf (⊤ : Subgroup (↥D)) :=
    generalizedFittingSubgroupOf_top_map_of_mulEquiv e
  have hcomp : H.subtype.comp C.subtype = D.subtype.comp e.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    rfl
  calc
    (generalizedFittingSubgroupOf C).map H.subtype
        = ((generalizedFittingSubgroupOf (⊤ : Subgroup (↥C))).map C.subtype).map H.subtype := by
          rw [hTopC]
    _ = (generalizedFittingSubgroupOf (⊤ : Subgroup (↥C))).map
          (H.subtype.comp C.subtype) := by rw [Subgroup.map_map]
    _ = (generalizedFittingSubgroupOf (⊤ : Subgroup (↥C))).map
          (D.subtype.comp e.toMonoidHom) := by rw [hcomp]
    _ = ((generalizedFittingSubgroupOf (⊤ : Subgroup (↥C))).map e.toMonoidHom).map D.subtype := by
          rw [Subgroup.map_map]
    _ = (generalizedFittingSubgroupOf (⊤ : Subgroup (↥D))).map D.subtype := by rw [hTopMap]
    _ = generalizedFittingSubgroupOf D := by rw [hTopD]

private theorem centralizer_subgroupOf_map
    {G : Type u} [Group G] (H W : Subgroup G) (hW : W ≤ H) :
    (Subgroup.centralizer ((W.subgroupOf H : Set (↥H)))).map H.subtype =
      Subgroup.centralizer (W : Set G) ⊓ H := by
  ext x
  constructor
  · intro hx
    rcases (Subgroup.mem_map).1 hx with ⟨y, hy, hxy⟩
    have hxH : x ∈ H := by
      rw [← hxy]
      exact y.2
    have hxC : x ∈ Subgroup.centralizer (W : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hyc : y ∈ Subgroup.centralizer ((W.subgroupOf H : Set (↥H))) := hy
      have hwH : (⟨w, hW hw⟩ : ↥H) ∈ W.subgroupOf H := by
        rw [Subgroup.mem_subgroupOf]
        exact hw
      have hwy : (⟨w, hW hw⟩ : ↥H) * y = y * (⟨w, hW hw⟩ : ↥H) :=
        (Subgroup.mem_centralizer_iff.mp hyc (⟨w, hW hw⟩ : ↥H)) hwH
      have hxy' : (y : G) = x := hxy
      have hG : (w : G) * (y : G) = (y : G) * (w : G) := congrArg Subtype.val hwy
      rwa [hxy'] at hG
    exact ⟨hxC, hxH⟩
  · intro hx
    rcases hx with ⟨hxC, hxH⟩
    refine Subgroup.mem_map.mpr ⟨⟨x, hxH⟩, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hwG : (w : G) ∈ W := (Subgroup.mem_subgroupOf).1 hw
    have hxCw : (w : G) * x = x * (w : G) :=
      (Subgroup.mem_centralizer_iff.mp hxC (w : G) hwG)
    apply Subtype.ext
    exact hxCw

private theorem mem_sup_decompose_of_normalizer
    {G : Type u} [Group G] {C W : Subgroup G}
    (hWnormC : W ≤ Subgroup.normalizer (C : Set G)) {x : G} (hx : x ∈ C ⊔ W) :
    ∃ c ∈ C, ∃ w ∈ W, c * w = x := by
  rw [Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction'' ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases hy with hyC | hyW
    · exact ⟨y, hyC, 1, W.one_mem, by simp⟩
    · exact ⟨1, C.one_mem, y, hyW, by simp⟩
  · intro y hy
    rcases hy with hyC | hyW
    · exact ⟨y⁻¹, C.inv_mem hyC, 1, W.one_mem, by simp⟩
    · exact ⟨1, C.one_mem, y⁻¹, W.inv_mem hyW, by simp⟩
  · exact ⟨1, C.one_mem, 1, W.one_mem, by simp⟩
  · intro a b _ _ ha hb
    rcases ha with ⟨c1, hc1, w1, hw1, rfl⟩
    rcases hb with ⟨c2, hc2, w2, hw2, rfl⟩
    have hw1c2 : w1 * c2 * w1⁻¹ ∈ C :=
      (Subgroup.le_normalizer_iff.mp hWnormC w1 hw1) c2 hc2
    refine ⟨c1 * (w1 * c2 * w1⁻¹), C.mul_mem hc1 hw1c2, w1 * w2,
      W.mul_mem hw1 hw2, ?_⟩
    simp [mul_assoc]

private theorem bender1970_1_9_step
    {G : Type u} [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime) (V U : Subgroup G)
    (hVU : V ≤ U) (hUp : IsPGroup p U) (_hVp : IsPGroup p V)
    (hC : IsPGroup p (generalizedFittingSubgroupOf (Subgroup.centralizer (V : Set G)))) :
    IsPGroup p (generalizedFittingSubgroupOf
      (Subgroup.centralizer ((U ⊓ Subgroup.normalizer (V : Set G)) : Set G))) := by
  classical
  let C : Subgroup G := Subgroup.centralizer (V : Set G)
  let W : Subgroup G := U ⊓ Subgroup.normalizer (V : Set G)
  let H : Subgroup G := C ⊔ W
  have hWU : W ≤ U := inf_le_left
  have hVW : V ≤ W := by
    intro v hv
    exact ⟨hVU hv, Subgroup.le_normalizer hv⟩
  have hWp : IsPGroup p W := hUp.to_le hWU
  have hWV : W ≤ Subgroup.normalizer (V : Set G) := inf_le_right
  have hCN : C ≤ Subgroup.normalizer (V : Set G) :=
    Subgroup.centralizer_le_normalizer (V : Set G)
  have hCnormN' : ∀ c n : G, c ∈ C → n ∈ Subgroup.normalizer (V : Set G) → n * c * n⁻¹ ∈ C :=
    (Subgroup.normal_subgroupOf_iff hCN).mp
      (inferInstance : (C.subgroupOf (Subgroup.normalizer (V : Set G))).Normal)
  have hWnormC : W ≤ Subgroup.normalizer (C : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro w hw c hc
    exact hCnormN' c w hc (hWV hw)
  have hCH : C ≤ H := le_sup_left
  have hWH : W ≤ H := le_sup_right
  have hCnormH : IsNormalIn C H := by
    refine ⟨hCH, ?_⟩
    intro h hh c hc
    change h ∈ C ⊔ W at hh
    rcases mem_sup_decompose_of_normalizer hWnormC hh with ⟨c0, hc0, w, hw, hcw⟩
    have hwC : w * c * w⁻¹ ∈ C := (Subgroup.le_normalizer_iff.mp hWnormC w hw) c hc
    have hc0C : c0 * (w * c * w⁻¹) * c0⁻¹ ∈ C :=
      C.mul_mem (C.mul_mem hc0 hwC) (C.inv_mem hc0)
    rw [← hcw]
    simpa [mul_assoc] using hc0C
  let Ht : Type u := ↥H
  let N' : Subgroup Ht := C.subgroupOf H
  have : N'.Normal := by
    refine (Subgroup.normal_subgroupOf_iff hCH).mpr ?_
    intro c n hc hn
    exact hCnormH.2 n hn c hc
  have hFstarMap : (generalizedFittingSubgroupOf N').map H.subtype =
      generalizedFittingSubgroupOf C := by
    let e : ↥N' ≃* ↥C := Subgroup.subgroupOfEquivOfLe hCH
    have hTop := generalizedFittingSubgroupOf_top_map_of_mulEquiv (G := ↥N') (H := ↥C) e
    have hcomp : C.subtype.comp e.toMonoidHom = H.subtype.comp N'.subtype := by
      apply MonoidHom.ext
      intro x
      rfl
    calc
      (generalizedFittingSubgroupOf N').map H.subtype
          = ((generalizedFittingSubgroupOf (⊤ : Subgroup (↥N'))).map N'.subtype).map H.subtype := by
            rw [generalizedFittingSubgroupOf_subgroup_top_eq (G := Ht) (H := N')]
      _ = (generalizedFittingSubgroupOf (⊤ : Subgroup (↥N'))).map
            (H.subtype.comp N'.subtype) := by rw [Subgroup.map_map]
      _ = (generalizedFittingSubgroupOf (⊤ : Subgroup (↥N'))).map
            (C.subtype.comp e.toMonoidHom) := by rw [← hcomp]
      _ = ((generalizedFittingSubgroupOf (⊤ : Subgroup (↥N'))).map e.toMonoidHom).map C.subtype := by
            rw [Subgroup.map_map]
      _ = (generalizedFittingSubgroupOf (⊤ : Subgroup (↥C))).map C.subtype := by rw [hTop]
      _ = generalizedFittingSubgroupOf C := by
            rw [generalizedFittingSubgroupOf_subgroup_top_eq C]
  have hN'star : IsPGroup p (generalizedFittingSubgroupOf N') := by
    let eF : generalizedFittingSubgroupOf N' ≃* generalizedFittingSubgroupOf C :=
      (Subgroup.equivMapOfInjective (generalizedFittingSubgroupOf N') H.subtype H.subtype_injective).trans
        (MulEquiv.subgroupCongr hFstarMap)
    exact hC.of_equiv eF.symm
  let W' : Subgroup Ht := W.subgroupOf H
  have hW'p : IsPGroup p W' :=
    hWp.of_equiv (Subgroup.subgroupOfEquivOfLe hWH).symm
  let φ : ↥W →* Ht ⧸ N' :=
    (QuotientGroup.mk' N').comp (Subgroup.inclusion hWH)
  have hφsurj : Function.Surjective φ := by
    intro q
    rcases QuotientGroup.mk'_surjective N' q with ⟨h, rfl⟩
    have hhH : (h : G) ∈ H := h.2
    change (h : G) ∈ C ⊔ W at hhH
    rcases mem_sup_decompose_of_normalizer hWnormC hhH with ⟨c, hc, w, hw, hcw⟩
    let w' : ↥W := ⟨w, hw⟩
    have hcW : (⟨w, hWH hw⟩ : ↥H)⁻¹ * h ∈ N' := by
      rw [Subgroup.mem_subgroupOf]
      change w⁻¹ * (h : G) ∈ C
      have hwch : (w⁻¹ * (h : G)) = w⁻¹ * c * w := by
        rw [← hcw]
        group
      rw [hwch]
      simpa using (Subgroup.le_normalizer_iff.mp hWnormC (w⁻¹) (W.inv_mem hw)) c hc
    have hφ : φ w' = QuotientGroup.mk' N' h := by
      change QuotientGroup.mk' N' (⟨w, hWH hw⟩ : ↥H) = QuotientGroup.mk' N' h
      exact (QuotientGroup.eq (s := N')).mpr hcW
    exact ⟨w', hφ⟩
  have hQ' : IsPGroup p (Ht ⧸ N') := by
    have hWq : IsPGroup p (W ⧸ φ.ker) := hWp.to_quotient φ.ker
    have hφrange : φ.range = ⊤ := MonoidHom.range_eq_top_of_surjective φ hφsurj
    let eQ : W ⧸ φ.ker ≃* Ht ⧸ N' :=
      (QuotientGroup.quotientKerEquivRange φ).trans
        ((MulEquiv.subgroupCongr hφrange).trans Subgroup.topEquiv)
    exact hWq.of_equiv eQ
  have hHstar : IsPGroup p (generalizedFittingSubgroupOf (⊤ : Subgroup Ht)) :=
    generalizedFittingSubgroupOf_isPGroup_of_extension (G := Ht) p hp N' hN'star hQ'
  have hFstarH : IsPGroup p (generalizedFittingSubgroupOf H) := by
    have hmap : IsPGroup p ((generalizedFittingSubgroupOf (⊤ : Subgroup Ht)).map H.subtype) :=
      IsPGroup.map hHstar H.subtype
    have hEq : (generalizedFittingSubgroupOf (⊤ : Subgroup Ht)).map H.subtype =
        generalizedFittingSubgroupOf H :=
      generalizedFittingSubgroupOf_subgroup_top_eq H
    rwa [hEq] at hmap
  let C' : Subgroup Ht := Subgroup.centralizer (W' : Set Ht)
  obtain ⟨hC'W, hC'N⟩ := bender1970_1_8_centralizerNormalizer_pGroup (G := Ht) p hp hHstar W' hW'p
  have hCWleH : Subgroup.centralizer (W : Set G) ≤ H := by
    exact (Subgroup.centralizer_le (show (V : Set G) ⊆ (W : Set G) from hVW)).trans hCH
  have hCentEq : Subgroup.centralizer (W : Set G) ⊓ H = Subgroup.centralizer (W : Set G) := by
    apply le_antisymm
    · exact inf_le_left
    · intro x hx
      exact ⟨hx, hCWleH hx⟩
  have hEqC : (generalizedFittingSubgroupOf C').map H.subtype =
      generalizedFittingSubgroupOf (Subgroup.centralizer (W : Set G)) := by
    rw [generalizedFittingSubgroupOf_map_subtype H C']
    rw [centralizer_subgroupOf_map H W hWH]
    rw [hCentEq]
  have hmap : IsPGroup p ((generalizedFittingSubgroupOf C').map H.subtype) :=
    IsPGroup.map hC'W H.subtype
  rwa [hEqC] at hmap

public theorem bender1970_1_9_centralizer_pGroup
    {G : Type u} [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime)
    {U V : Subgroup G}
    (hVU : V ≤ U) (hUp : IsPGroup p U) (hVp : IsPGroup p V)
    (hC : IsPGroup p (generalizedFittingSubgroupOf (Subgroup.centralizer (V : Set G)))) :
    IsPGroup p (generalizedFittingSubgroupOf (Subgroup.centralizer (U : Set G))) := by
  classical
  let P : ℕ → Prop := fun d => ∀ U V : Subgroup G,
    V ≤ U → IsPGroup p U → IsPGroup p V →
      IsPGroup p (generalizedFittingSubgroupOf (Subgroup.centralizer (V : Set G))) →
      Nat.card U - Nat.card V = d →
      IsPGroup p (generalizedFittingSubgroupOf (Subgroup.centralizer (U : Set G)))
  have hP : ∀ d : ℕ, P d := by
    intro d
    refine Nat.strong_induction_on d ?_
    intro d ih
    intro U V hVU hUp hVp hC hd
    let W : Subgroup G := U ⊓ Subgroup.normalizer (V : Set G)
    have hVW : V ≤ W := by
      intro v hv
      exact ⟨hVU hv, Subgroup.le_normalizer hv⟩
    have hWU : W ≤ U := inf_le_left
    have hWp : IsPGroup p W := hUp.to_le hWU
    have hWstar : IsPGroup p (generalizedFittingSubgroupOf (Subgroup.centralizer (W : Set G))) :=
      bender1970_1_9_step p hp V U hVU hUp hVp hC
    by_cases hWUeq : W = U
    · rw [hWUeq] at hWstar
      exact hWstar
    · have hVneU : V ≠ U := by
        intro hVUeq
        apply hWUeq
        change U ⊓ Subgroup.normalizer (V : Set G) = U
        rw [hVUeq]
        ext x
        constructor
        · intro hx
          exact hx.1
        · intro hx
          exact ⟨hx, Subgroup.le_normalizer (H := U) hx⟩
      have hVltW : V < W := by
        let : Fact p.Prime := ⟨hp⟩
        have hUnil : Group.IsNilpotent (↥U) := IsPGroup.isNilpotent hUp
        have hnc : NormalizerCondition (↥U) :=
          Group.normalizerCondition_of_isNilpotent (G := ↥U)
        let V' : Subgroup (↥U) := V.subgroupOf U
        have hV'lt : V' < ⊤ := by
          rw [lt_iff_le_and_ne]
          constructor
          · exact le_top
          · intro htop
            apply hVneU
            apply le_antisymm hVU
            exact (Subgroup.subgroupOf_eq_top).mp htop
        have hV'ltN : V' < Subgroup.normalizer (V' : Set (↥U)) := hnc V' hV'lt
        have hne : ∃ n : ↥U, n ∈ Subgroup.normalizer (V' : Set (↥U)) ∧ n ∉ V' := by
          by_contra hnone
          apply hV'ltN.2
          intro x hxN
          by_contra hxV
          exact hnone ⟨x, hxN, hxV⟩
        rcases hne with ⟨n, hnN, hnV⟩
        have hnU : (n : G) ∈ U := n.2
        have hnNorm : (n : G) ∈ Subgroup.normalizer (V : Set G) := by
          rw [Subgroup.mem_normalizer_iff]
          intro v
          constructor
          · intro hv
            have hmem : (⟨v, hVU hv⟩ : ↥U) ∈ V' := by
              rw [Subgroup.mem_subgroupOf]
              exact hv
            have hiff := (Subgroup.mem_normalizer_iff.mp hnN) (⟨v, hVU hv⟩ : ↥U)
            have hconj : n * (⟨v, hVU hv⟩ : ↥U) * n⁻¹ ∈ V' := hiff.mp hmem
            exact (Subgroup.mem_subgroupOf).1 hconj
          · intro hv'
            have hUv : v ∈ U := by
              have hUinv : (n : G)⁻¹ ∈ U := U.inv_mem hnU
              have hprod : (n : G)⁻¹ * (n * v * n⁻¹) * n ∈ U :=
                U.mul_mem (U.mul_mem hUinv (hVU hv')) hnU
              simpa [mul_assoc] using hprod
            have hmem' : (n * (⟨v, hUv⟩ : ↥U) * n⁻¹ : ↥U) ∈ V' := by
              rw [Subgroup.mem_subgroupOf]
              exact hv'
            have hiff := (Subgroup.mem_normalizer_iff.mp hnN) (⟨v, hUv⟩ : ↥U)
            have hconj : (⟨v, hUv⟩ : ↥U) ∈ V' := hiff.mpr hmem'
            exact (Subgroup.mem_subgroupOf).1 hconj
        have hnW : (n : G) ∈ W := ⟨hnU, hnNorm⟩
        rw [lt_iff_le_and_ne]
        constructor
        · exact hVW
        · intro hVWeq
          have hnV' : (n : G) ∈ V := by
            rw [hVWeq]
            exact hnW
          exact hnV hnV'
      have hVcardW : Nat.card V < Nat.card W := by
        have hss : (V : Set G) ⊂ (W : Set G) := by
          rw [Set.ssubset_iff_of_subset (show (V : Set G) ⊆ (W : Set G) from hVW)]
          rcases (lt_iff_le_and_ne.mp hVltW) with ⟨hVWle, hVWne⟩
          by_contra hnone
          apply hVWne
          apply Subgroup.ext
          intro x
          constructor
          · intro hxV
            exact hVWle hxV
          · intro hxW
            by_contra hxV
            exact hnone ⟨x, hxW, hxV⟩
        exact (W : Set G).toFinite.card_lt_card hss
      have hWcardU : Nat.card W ≤ Nat.card U := by
        exact Nat.card_le_card_of_injective (Subgroup.inclusion hWU) (Subgroup.inclusion_injective hWU)
      have hlt : Nat.card U - Nat.card W < Nat.card U - Nat.card V := by omega
      have hltn : Nat.card U - Nat.card W < d := by
        rwa [hd] at hlt
      exact ih (Nat.card U - Nat.card W) hltn U W hWU hUp hWp hWstar rfl
  exact hP (Nat.card U - Nat.card V) U V hVU hUp hVp hC rfl

end

end CFSG.GorensteinWalter
