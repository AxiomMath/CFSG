module

public import CFSG.RankThree.GF2n.Tim79a34QEOutResidual
import CFSG.RankThree.GF2n.Smith81.OrthRootInvol
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentLinUnitParabGroup
import CFSG.Quasithin.Background.F6SQTK

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Quasithin
open CFSG.Timmesfeld.Transvection
open scoped commutatorElement

variable {G : Type} [Group G]

theorem omegaOf_subgroupOf_iff {V H K : Subgroup G} (hVK : V ≤ K) (hHK : H ≤ K)
    (U : Subgroup ↥K) :
    U.map K.subtype ∈ omegaOf V H ↔ U ∈ omegaOf (V.subgroupOf K) (H.subgroupOf K) := by
  constructor
  · rintro ⟨g, hgH, hgU⟩
    have hgK : g ∈ K := hHK hgH
    have hU : U = (conjSubgroup g V).subgroupOf K := by
      rw [← hgU]
      exact (Subgroup.comap_map_eq_self_of_injective K.subtype_injective U).symm
    refine ⟨⟨g, hgK⟩, Subgroup.mem_subgroupOf.mpr hgH, ?_⟩
    rw [hU, conjSubgroup_subgroupOf]
  · rintro ⟨h, hh, rfl⟩
    refine ⟨(h : G), Subgroup.mem_subgroupOf.mp hh, ?_⟩
    calc (conjSubgroup h (V.subgroupOf K)).map K.subtype
        = conjSubgroup (h : G) ((V.subgroupOf K).map K.subtype) :=
          (CFSG.GroupTheory.map_conjSubgroup K.subtype (V.subgroupOf K) h).symm
      _ = conjSubgroup (h : G) V := by rw [Subgroup.map_subgroupOf_eq_of_le hVK]

theorem le_of_mem_omegaOf {V H K : Subgroup G} (hVK : V ≤ K) (hHK : H ≤ K)
    {U : Subgroup G} (hU : U ∈ omegaOf V H) : U ≤ K := by
  obtain ⟨g, hg, rfl⟩ := hU
  exact conjSubgroup_le_of_le_of_mem hVK (hHK hg)

theorem map_xOf_subgroupOf {V H K : Subgroup G} (hVK : V ≤ K) (hHK : H ≤ K)
    (hVH : V ≤ H) :
    (xOf (V.subgroupOf K) (H.subgroupOf K)).map K.subtype = xOf V H := by
  have hle : ∀ U ∈ omegaOf V H, U ≤ K := fun U hU => le_of_mem_omegaOf hVK hHK hU
  unfold xOf
  refine le_antisymm ?_ ?_
  · simp only [Subgroup.map_iSup]
    refine iSup₂_le fun U hU => ?_
    exact le_xOf ((omegaOf_subgroupOf_iff hVK hHK U).mpr hU)
  · simp only [Subgroup.map_iSup]
    refine iSup₂_le fun U hU => ?_
    have hUK : U ≤ K := hle U hU
    have hU₀ : Subgroup.subgroupOf U K ∈
        omegaOf (Subgroup.subgroupOf V K) (Subgroup.subgroupOf H K) :=
      (omegaOf_subgroupOf_iff hVK hHK (Subgroup.subgroupOf U K)).mp (by
        rwa [Subgroup.map_subgroupOf_eq_of_le hUK])
    exact le_iSup₂_of_le (Subgroup.subgroupOf U K) hU₀
      (le_of_eq (Subgroup.map_subgroupOf_eq_of_le hUK).symm)

theorem subgroupOf_xOf {V H K : Subgroup G} (hVK : V ≤ K) (hHK : H ≤ K)
    (hVH : V ≤ H) :
    (xOf V H).subgroupOf K = xOf (V.subgroupOf K) (H.subgroupOf K) := by
  apply Subgroup.map_injective (f := K.subtype) K.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le ((xOf_le_H hVH).trans hHK), map_xOf_subgroupOf hVK hHK hVH]

theorem map_wOf_subgroupOf {V H K : Subgroup G} (hVK : V ≤ K) (hHK : H ≤ K) :
    (wOf (V.subgroupOf K) (H.subgroupOf K)).map K.subtype = wOf V H := by
  have hI : (inSubgroup (pCore 2) (H.subgroupOf K)).map K.subtype = inSubgroup (pCore 2) H :=
    CFSG.Quasithin.F6.map_pCoreOf_subgroupOf (I := K) hHK
  have hle : ∀ U ∈ omegaOf V H, U ≤ K := fun U hU => le_of_mem_omegaOf hVK hHK hU
  unfold wOf
  refine le_antisymm ?_ ?_
  · simp only [Subgroup.map_iSup]
    refine iSup₂_le fun U hU => ?_
    have hmap : U.map K.subtype ∈ omegaOf V H := (omegaOf_subgroupOf_iff hVK hHK U).mpr hU
    have heq : (U ⊓ inSubgroup (pCore 2) (H.subgroupOf K)).map K.subtype =
        U.map K.subtype ⊓ inSubgroup (pCore 2) H := by
      rw [Subgroup.map_inf_eq _ _ K.subtype K.subtype_injective, hI]
    rw [heq]
    exact le_iSup₂_of_le _ hmap le_rfl
  · simp only [Subgroup.map_iSup]
    refine iSup₂_le fun U hU => ?_
    have hUK : U ≤ K := hle U hU
    have hU₀ : Subgroup.subgroupOf U K ∈
        omegaOf (Subgroup.subgroupOf V K) (Subgroup.subgroupOf H K) :=
      (omegaOf_subgroupOf_iff hVK hHK (Subgroup.subgroupOf U K)).mp (by
        rwa [Subgroup.map_subgroupOf_eq_of_le hUK])
    have heq : (Subgroup.subgroupOf U K ⊓ inSubgroup (pCore 2) (H.subgroupOf K)).map K.subtype =
        U ⊓ inSubgroup (pCore 2) H := by
      rw [Subgroup.map_inf_eq _ _ K.subtype K.subtype_injective,
        Subgroup.map_subgroupOf_eq_of_le hUK, hI]
    exact le_iSup₂_of_le (Subgroup.subgroupOf U K) hU₀ (le_of_eq heq.symm)

theorem mem_wOf_subgroupOf_iff {V H K : Subgroup G} (hVK : V ≤ K) (hHK : H ≤ K)
    {x : ↥K} : x ∈ wOf (V.subgroupOf K) (H.subgroupOf K) ↔ (x : G) ∈ wOf V H := by
  have h := Subgroup.mem_map_iff_mem (f := K.subtype) K.subtype_injective
    (K := wOf (V.subgroupOf K) (H.subgroupOf K)) (x := x)
  rw [← h, map_wOf_subgroupOf hVK hHK]
  rfl

theorem mem_xOf_subgroupOf_iff {V H K : Subgroup G} (hVK : V ≤ K) (hHK : H ≤ K)
    (hVH : V ≤ H) {x : ↥K} :
    x ∈ xOf (V.subgroupOf K) (H.subgroupOf K) ↔ (x : G) ∈ xOf V H := by
  have h := Subgroup.mem_map_iff_mem (f := K.subtype) K.subtype_injective
    (K := xOf (V.subgroupOf K) (H.subgroupOf K)) (x := x)
  rw [← h, map_xOf_subgroupOf hVK hHK hVH]
  rfl

theorem map_dOf_subgroupOf {V H K : Subgroup G} (hVK : V ≤ K) (hHK : H ≤ K) :
    K.subtype '' dOf (V.subgroupOf K) (H.subgroupOf K) = dOf V H := by
  have hle : ∀ U ∈ omegaOf V H, U ≤ K := fun U hU => le_of_mem_omegaOf hVK hHK hU
  ext d
  constructor
  · rintro ⟨a, ⟨ha1, U, hU, haU⟩, rfl⟩
    exact ⟨fun h => ha1 (Subtype.ext (by simpa using h)), U.map K.subtype,
      (omegaOf_subgroupOf_iff hVK hHK U).mpr hU, Subgroup.mem_map_of_mem K.subtype haU⟩
  · rintro ⟨hd1, U, hU, hdU⟩
    have hUK : U ≤ K := hle U hU
    have hU₀ : Subgroup.subgroupOf U K ∈
        omegaOf (Subgroup.subgroupOf V K) (Subgroup.subgroupOf H K) :=
      (omegaOf_subgroupOf_iff hVK hHK (Subgroup.subgroupOf U K)).mp (by
        rwa [Subgroup.map_subgroupOf_eq_of_le hUK])
    refine ⟨⟨d, hUK hdU⟩, ?_, rfl⟩
    exact ⟨fun h => hd1 (congrArg Subtype.val h), Subgroup.subgroupOf U K, hU₀,
      Subgroup.mem_subgroupOf.mpr hdU⟩

theorem mem_dOf_subgroupOf_iff {V H K : Subgroup G} (hVK : V ≤ K) (hHK : H ≤ K)
    {x : ↥K} : x ∈ dOf (V.subgroupOf K) (H.subgroupOf K) ↔ (x : G) ∈ dOf V H := by
  have h := Set.ext_iff.mp (map_dOf_subgroupOf hVK hHK) (x : G)
  rw [Set.mem_image] at h
  have h' : (x : G) ∈ K.subtype '' dOf (V.subgroupOf K) (H.subgroupOf K) ↔
      x ∈ dOf (V.subgroupOf K) (H.subgroupOf K) :=
    ⟨fun ⟨y, hy, hxy⟩ => by rwa [← Subtype.ext hxy], fun hx => ⟨x, hx, rfl⟩⟩
  rw [← h']
  exact h

theorem map_cX_subgroupOf {V H K : Subgroup G} (hVK : V ≤ K) (hHK : H ≤ K)
    (hVH : V ≤ H) :
    (cX (V.subgroupOf K) (H.subgroupOf K)).map K.subtype = cX V H := by
  ext x
  constructor
  · rintro ⟨a, ⟨haH, haX⟩, rfl⟩
    refine ⟨Subgroup.mem_subgroupOf.mp haH, fun y hy => ?_⟩
    have hyK : y ∈ K := hHK (xOf_le_H hVH hy)
    have hy' : (⟨y, hyK⟩ : ↥K) ∈ xOf (V.subgroupOf K) (H.subgroupOf K) :=
      (mem_xOf_subgroupOf_iff hVK hHK hVH).mpr hy
    exact (mem_wOf_subgroupOf_iff hVK hHK).mp (haX ⟨y, hyK⟩ hy')
  · rintro ⟨hxH, hxX⟩
    have hxK : x ∈ K := hHK hxH
    refine ⟨⟨x, hxK⟩, ⟨Subgroup.mem_subgroupOf.mpr hxH, fun y hy => ?_⟩, rfl⟩
    have hy' : (y : G) ∈ xOf V H := (mem_xOf_subgroupOf_iff hVK hHK hVH).mp hy
    exact (mem_wOf_subgroupOf_iff hVK hHK).mpr (hxX (y : G) hy')

theorem map_cPbar_subgroupOf {V H P K : Subgroup G} (hVK : V ≤ K) (hHK : H ≤ K)
    (hVH : V ≤ H) (hPK : P ≤ K) :
    (cPbar (V.subgroupOf K) (H.subgroupOf K) (P.subgroupOf K)).map K.subtype = cPbar V H P := by
  rw [cPbar, cPbar, Subgroup.map_inf_eq _ _ K.subtype K.subtype_injective,
    Subgroup.map_subgroupOf_eq_of_le hPK, map_cX_subgroupOf hVK hHK hVH]

theorem map_subgroupOf_subgroupOfEquivOfLe {K H : Subgroup G} (hHK : H ≤ K)
    (S : Subgroup ↥K) :
    (S.subgroupOf (H.subgroupOf K)).map
        (Subgroup.subgroupOfEquivOfLe hHK : ↥(H.subgroupOf K) →* ↥H) =
      (S.map K.subtype).subgroupOf H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map_of_mem K.subtype
      (Subgroup.mem_subgroupOf.mp hy))
  · intro hx
    have hx' : (x : G) ∈ S.map K.subtype := Subgroup.mem_subgroupOf.mp hx
    obtain ⟨s, hs, hsx⟩ := Subgroup.mem_map.mp hx'
    refine ⟨⟨s, ?_⟩, Subgroup.mem_subgroupOf.mpr hs, Subtype.ext hsx⟩
    show K.subtype s ∈ H
    rw [hsx]
    exact x.2

@[expose] noncomputable def hbarEquivSubgroupOf {V H K : Subgroup G} (hVK : V ≤ K)
    (hHK : H ≤ K) :
    Hbar (V.subgroupOf K) (H.subgroupOf K) ≃* Hbar V H :=
  QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hHK) (by
    rw [map_subgroupOf_subgroupOfEquivOfLe hHK, map_wOf_subgroupOf hVK hHK])

theorem hbarEquivSubgroupOf_piBar {V H K : Subgroup G} (hVK : V ≤ K) (hHK : H ≤ K)
    (x : ↥(H.subgroupOf K)) :
    hbarEquivSubgroupOf hVK hHK (piBar (V.subgroupOf K) (H.subgroupOf K) x) =
      piBar V H (Subgroup.subgroupOfEquivOfLe hHK x) := by
  rw [hbarEquivSubgroupOf, piBar, piBar]
  rfl

theorem map_barOf_subgroupOf {V H K : Subgroup G} (hVK : V ≤ K) (hHK : H ≤ K)
    (S : Subgroup G) :
    (barOf (V.subgroupOf K) (H.subgroupOf K) (S.subgroupOf K)).map
        (hbarEquivSubgroupOf hVK hHK).toMonoidHom = barOf V H S := by
  have hcomp : (hbarEquivSubgroupOf hVK hHK).toMonoidHom.comp
      (piBar (V.subgroupOf K) (H.subgroupOf K)) =
      (piBar V H).comp (Subgroup.subgroupOfEquivOfLe hHK : ↥(H.subgroupOf K) →* ↥H) := by
    ext x
    exact hbarEquivSubgroupOf_piBar hVK hHK x
  rw [barOf, barOf, Subgroup.map_map, hcomp, ← Subgroup.map_map,
    map_subgroupOf_subgroupOfEquivOfLe hHK]
  have hinf : ((S.subgroupOf K).map K.subtype).subgroupOf H = S.subgroupOf H := by
    rw [Subgroup.subgroupOf_map_subtype]
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    exact and_iff_left (hHK x.2)
  rw [hinf]

theorem mem_barOf_subgroupOf_iff {V H K : Subgroup G} (hVK : V ≤ K) (hHK : H ≤ K)
    (S : Subgroup G) (y : Hbar (V.subgroupOf K) (H.subgroupOf K)) :
    hbarEquivSubgroupOf hVK hHK y ∈ barOf V H S ↔
      y ∈ barOf (V.subgroupOf K) (H.subgroupOf K) (S.subgroupOf K) := by
  rw [← Subgroup.mem_map_iff_mem (f := (hbarEquivSubgroupOf hVK hHK).toMonoidHom)
    (hbarEquivSubgroupOf hVK hHK).injective, map_barOf_subgroupOf hVK hHK]
  rfl

theorem map_dbarOf_subgroupOf {V H K : Subgroup G} (hVK : V ≤ K) (hHK : H ≤ K) :
    (hbarEquivSubgroupOf hVK hHK) '' dbarOf (V.subgroupOf K) (H.subgroupOf K) =
      dbarOf V H := by
  have hle : ∀ U ∈ omegaOf V H, U ≤ K := fun U hU => le_of_mem_omegaOf hVK hHK hU
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨x, hxD, hxW, rfl⟩ := mem_dbarOf_iff.mp hz
    refine mem_dbarOf_iff.mpr ⟨Subgroup.subgroupOfEquivOfLe hHK x, ?_, ?_, ?_⟩
    · have h := (mem_dOf_subgroupOf_iff hVK hHK (x := (x : ↥K))).mp hxD
      simpa using h
    · have h := (mem_wOf_subgroupOf_iff hVK hHK (x := (x : ↥K))).not.mp hxW
      simpa using h
    · exact hbarEquivSubgroupOf_piBar hVK hHK x
  · intro hy
    obtain ⟨x, hxD, hxW, rfl⟩ := mem_dbarOf_iff.mp hy
    have hxK : (x : G) ∈ K := by
      obtain ⟨U, hU, hxU⟩ := hxD.2
      exact hle U hU hxU
    refine ⟨piBar (V.subgroupOf K) (H.subgroupOf K) ⟨⟨x, hxK⟩, x.2⟩, ?_, ?_⟩
    · refine mem_dbarOf_iff.mpr ⟨⟨⟨x, hxK⟩, x.2⟩, ?_, ?_, rfl⟩
      · have h := (mem_dOf_subgroupOf_iff hVK hHK (x := (⟨x, hxK⟩ : ↥K))).mpr hxD
        simpa using h
      · have h := (mem_wOf_subgroupOf_iff hVK hHK (x := (⟨x, hxK⟩ : ↥K))).not.mpr hxW
        simpa using h
    · rw [hbarEquivSubgroupOf_piBar]
      rfl

theorem mem_dbarOf_subgroupOf_iff {V H K : Subgroup G} (hVK : V ≤ K) (hHK : H ≤ K)
    (y : Hbar (V.subgroupOf K) (H.subgroupOf K)) :
    hbarEquivSubgroupOf hVK hHK y ∈ dbarOf V H ↔
      y ∈ dbarOf (V.subgroupOf K) (H.subgroupOf K) := by
  have h := Set.ext_iff.mp (map_dbarOf_subgroupOf hVK hHK)
    (hbarEquivSubgroupOf hVK hHK y)
  rw [Set.mem_image] at h
  have h' : hbarEquivSubgroupOf hVK hHK y ∈
      hbarEquivSubgroupOf hVK hHK '' dbarOf (V.subgroupOf K) (H.subgroupOf K) ↔
        y ∈ dbarOf (V.subgroupOf K) (H.subgroupOf K) :=
    ⟨fun ⟨z, hz, hzy⟩ => by
      rw [(hbarEquivSubgroupOf hVK hHK).injective hzy] at hz
      exact hz, fun hy => ⟨y, hy, rfl⟩⟩
  exact h.symm.trans h'

theorem map_barOf_xOf_subgroupOf {V H K : Subgroup G} (hVK : V ≤ K) (hHK : H ≤ K)
    (hVH : V ≤ H) :
    (barOf (V.subgroupOf K) (H.subgroupOf K) (xOf (V.subgroupOf K) (H.subgroupOf K))).map
        (hbarEquivSubgroupOf hVK hHK).toMonoidHom = barOf V H (xOf V H) := by
  rw [← subgroupOf_xOf hVK hHK hVH]
  exact map_barOf_subgroupOf hVK hHK (xOf V H)

@[expose] noncomputable def xbarEquivSubgroupOf {V H K : Subgroup G} (hVK : V ≤ K)
    (hHK : H ≤ K) (hVH : V ≤ H) :
    Xbar (V.subgroupOf K) (H.subgroupOf K) ≃* Xbar V H :=
  (Subgroup.equivMapOfInjective
    (barOf (V.subgroupOf K) (H.subgroupOf K) (xOf (V.subgroupOf K) (H.subgroupOf K)))
    (hbarEquivSubgroupOf hVK hHK).toMonoidHom
    (hbarEquivSubgroupOf hVK hHK).injective).trans
    (MulEquiv.subgroupCongr (map_barOf_xOf_subgroupOf hVK hHK hVH))

theorem xbarEquivSubgroupOf_apply {V H K : Subgroup G} (hVK : V ≤ K) (hHK : H ≤ K)
    (hVH : V ≤ H)
    (y : Xbar (V.subgroupOf K) (H.subgroupOf K)) :
    (xbarEquivSubgroupOf hVK hHK hVH y : Hbar V H) =
      hbarEquivSubgroupOf hVK hHK (y : Hbar (V.subgroupOf K) (H.subgroupOf K)) := rfl

theorem mem_Dy_subgroupOf_iff {V H K : Subgroup G} (hVK : V ≤ K) (hHK : H ≤ K)
    (hVH : V ≤ H)
    (d : Xbar (V.subgroupOf K) (H.subgroupOf K)) :
    d ∈ Dy (V.subgroupOf K) (H.subgroupOf K) ↔
      xbarEquivSubgroupOf hVK hHK hVH d ∈ Dy V H := by
  rw [Dy, Dy, Set.mem_setOf_eq, Set.mem_setOf_eq, xbarEquivSubgroupOf_apply,
    mem_dbarOf_subgroupOf_iff hVK hHK]

theorem mem_Vy_subgroupOf_iff {V H K : Subgroup G} (hVK : V ≤ K) (hHK : H ≤ K)
    (hVH : V ≤ H)
    (z : Xbar (V.subgroupOf K) (H.subgroupOf K)) :
    z ∈ Vy (V.subgroupOf K) (H.subgroupOf K) ↔
      xbarEquivSubgroupOf hVK hHK hVH z ∈ Vy V H := by
  rw [Vy, Vy, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, xbarEquivSubgroupOf_apply,
    mem_barOf_subgroupOf_iff hVK hHK V]

theorem map_Vy_subgroupOf {V H K : Subgroup G} (hVK : V ≤ K) (hHK : H ≤ K)
    (hVH : V ≤ H) :
    (Vy (V.subgroupOf K) (H.subgroupOf K)).map
        (xbarEquivSubgroupOf hVK hHK hVH).toMonoidHom = Vy V H := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (mem_Vy_subgroupOf_iff hVK hHK hVH z).1 hz
  · intro hy
    obtain ⟨z, rfl⟩ := (xbarEquivSubgroupOf hVK hHK hVH).surjective y
    exact ⟨z, (mem_Vy_subgroupOf_iff hVK hHK hVH z).2 hy, rfl⟩

theorem mem_Rbar_subgroupOf_iff {V H P K : Subgroup G} (hVK : V ≤ K) (hHK : H ≤ K)
    (hVH : V ≤ H) (hPK : P ≤ K)
    (z : Xbar (V.subgroupOf K) (H.subgroupOf K)) :
    z ∈ Rbar (V.subgroupOf K) (H.subgroupOf K) (P.subgroupOf K) ↔
      xbarEquivSubgroupOf hVK hHK hVH z ∈ Rbar V H P := by
  rw [Rbar, Rbar, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, xbarEquivSubgroupOf_apply,
    mem_barOf_subgroupOf_iff hVK hHK P]

theorem map_Rbar_subgroupOf {V H P K : Subgroup G} (hVK : V ≤ K) (hHK : H ≤ K)
    (hVH : V ≤ H) (hPK : P ≤ K) :
    (Rbar (V.subgroupOf K) (H.subgroupOf K) (P.subgroupOf K)).map
        (xbarEquivSubgroupOf hVK hHK hVH).toMonoidHom = Rbar V H P := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (mem_Rbar_subgroupOf_iff hVK hHK hVH hPK z).1 hz
  · intro hy
    obtain ⟨z, rfl⟩ := (xbarEquivSubgroupOf hVK hHK hVH).surjective y
    exact ⟨z, (mem_Rbar_subgroupOf_iff hVK hHK hVH hPK z).2 hy, rfl⟩

@[expose] noncomputable def xbarZEquivSubgroupOf {V H K : Subgroup G} (hVK : V ≤ K)
    (hHK : H ≤ K) (hVH : V ≤ H) :
    XbarZ (V.subgroupOf K) (H.subgroupOf K) ≃* XbarZ V H :=
  QuotientGroup.congr _ _ (xbarEquivSubgroupOf hVK hHK hVH) (by simp)

theorem projZ_comp_xbarZEquivSubgroupOf {V H K : Subgroup G} (hVK : V ≤ K)
    (hHK : H ≤ K) (hVH : V ≤ H) :
    (xbarZEquivSubgroupOf hVK hHK hVH).toMonoidHom.comp
        (projZ (V.subgroupOf K) (H.subgroupOf K)) =
      (projZ V H).comp (xbarEquivSubgroupOf hVK hHK hVH).toMonoidHom := by
  ext x
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, projZ, projZ, xbarZEquivSubgroupOf]
  rfl

theorem map_VZ_subgroupOf {V H K : Subgroup G} (hVK : V ≤ K) (hHK : H ≤ K)
    (hVH : V ≤ H) :
    (VZ (V.subgroupOf K) (H.subgroupOf K)).map
        (xbarZEquivSubgroupOf hVK hHK hVH).toMonoidHom = VZ V H := by
  rw [VZ, VZ, Subgroup.map_map, projZ_comp_xbarZEquivSubgroupOf, ← Subgroup.map_map,
    map_Vy_subgroupOf]

theorem mem_rootClassZ_subgroupOf_iff {V H K : Subgroup G} (hVK : V ≤ K) (hHK : H ≤ K)
    (hVH : V ≤ H)
    (X : Subgroup (XbarZ (V.subgroupOf K) (H.subgroupOf K))) :
    Subgroup.map (xbarZEquivSubgroupOf hVK hHK hVH).toMonoidHom X ∈ rootClassZ V H ↔
      X ∈ rootClassZ (V.subgroupOf K) (H.subgroupOf K) := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨y, rfl⟩ := (xbarZEquivSubgroupOf hVK hHK hVH).surjective x
    refine ⟨y, ?_⟩
    apply Subgroup.map_injective (f := (xbarZEquivSubgroupOf hVK hHK hVH).toMonoidHom)
      (xbarZEquivSubgroupOf hVK hHK hVH).injective
    rw [hx, ← map_VZ_subgroupOf hVK hHK hVH]
    exact ModelRank.conjSub_map (xbarZEquivSubgroupOf hVK hHK hVH).toMonoidHom
      (VZ (V.subgroupOf K) (H.subgroupOf K)) y
  · rintro ⟨y, hy⟩
    refine ⟨xbarZEquivSubgroupOf hVK hHK hVH y, ?_⟩
    rw [hy, ← map_VZ_subgroupOf hVK hHK hVH]
    exact (ModelRank.conjSub_map (xbarZEquivSubgroupOf hVK hHK hVH).toMonoidHom
      (VZ (V.subgroupOf K) (H.subgroupOf K)) y).symm

theorem map_Rtilde_subgroupOf {V H P K : Subgroup G} (hVK : V ≤ K) (hHK : H ≤ K)
    (hVH : V ≤ H) (hPK : P ≤ K) :
    (Rtilde (V.subgroupOf K) (H.subgroupOf K) (P.subgroupOf K)).map
        (xbarZEquivSubgroupOf hVK hHK hVH).toMonoidHom = Rtilde V H P := by
  rw [Rtilde, Rtilde, Subgroup.map_map, projZ_comp_xbarZEquivSubgroupOf, ← Subgroup.map_map,
    map_Rbar_subgroupOf hVK hHK hVH hPK]

theorem qBar_subgroupOf {V H K : Subgroup G} (hVK : V ≤ K) (hHK : H ≤ K) :
    qBar (V.subgroupOf K) (H.subgroupOf K) = qBar V H := by
  rw [qBar, qBar, ← map_barOf_subgroupOf hVK hHK (S := V)]
  exact Nat.card_congr (Subgroup.equivMapOfInjective _
    (hbarEquivSubgroupOf hVK hHK).toMonoidHom
    (hbarEquivSubgroupOf hVK hHK).injective).toEquiv

theorem card_inf_wOf_subgroupOf {V H K : Subgroup G} (hVK : V ≤ K) (hHK : H ≤ K) :
    Nat.card ↥(V.subgroupOf K ⊓ wOf (V.subgroupOf K) (H.subgroupOf K)) =
      Nat.card ↥(V ⊓ wOf V H) := by
  have h1 : (V.subgroupOf K ⊓ wOf (V.subgroupOf K) (H.subgroupOf K)).map K.subtype =
      V ⊓ wOf V H := by
    rw [Subgroup.map_inf_eq _ _ K.subtype K.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hVK, map_wOf_subgroupOf hVK hHK]
  rw [← h1]
  exact Nat.card_congr (Subgroup.equivMapOfInjective _ K.subtype K.subtype_injective).toEquiv

theorem map_pCoreOf_normalizer_eq {A B : Type} [Group A] [Group B] (e : A ≃* B)
    {R₀ : Subgroup A} {R : Subgroup B} (hR : R₀.map e.toMonoidHom = R) :
    (pCoreOf 2 (Subgroup.normalizer (R₀ : Set A))).map e.toMonoidHom =
      pCoreOf 2 (Subgroup.normalizer (R : Set B)) := by
  rw [← hR, ← Subgroup.map_normalizer_eq_of_bijective R₀ e.bijective,
    CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv]

theorem exists_isConj_of_map_mem_iff {A B : Type} [Group A] [Group B] (e : A ≃* B)
    {D : Set A} {D' : Set B} (hD : ∀ a : A, a ∈ D ↔ e a ∈ D')
    (h : ∃ d₀ : B, D' = {g | IsConj d₀ g}) : ∃ d₀ : A, D = {g | IsConj d₀ g} := by
  obtain ⟨d₀, rfl⟩ := h
  have himg : e.symm '' {g : B | IsConj d₀ g} = D := by
    ext a
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact (hD (e.symm b)).2 (by simpa using hb)
    · intro ha
      exact ⟨e a, (hD a).1 ha, by simp⟩
  rw [← himg, CFSG.Fischer.image_setOf_isConj]
  exact ⟨e.symm d₀, rfl⟩

theorem isRootInvolutionSet_of_map_mem_iff {A B : Type} [Group A] [Group B] (e : A ≃* B)
    {D : Set A} {D' : Set B} (hD : ∀ a : A, a ∈ D ↔ e a ∈ D')
    (h : CFSG.Timmesfeld.IsRootInvolutionSet D') :
    CFSG.Timmesfeld.IsRootInvolutionSet D := by
  have hpre := CFSG.RankThree.GF2n.Smith81.isRootInvolutionSet_preimage e.toMonoidHom
    e.injective h
  have hEq : e.toMonoidHom ⁻¹' D' = D := Set.ext fun a => (hD a).symm
  rwa [hEq] at hpre

theorem closure_eq_top_of_map_mem_iff {A B : Type} [Group A] [Group B] (e : A ≃* B)
    {D : Set A} {D' : Set B} (hD : ∀ a : A, a ∈ D ↔ e a ∈ D')
    (h : Subgroup.closure D' = ⊤) : Subgroup.closure D = ⊤ := by
  have himg : e.symm '' D' = D := by
    ext a
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact (hD (e.symm b)).2 (by simpa using hb)
    · intro ha
      exact ⟨e a, (hD a).1 ha, by simp⟩
  have h' : Subgroup.closure (e.symm '' D') = ⊤ :=
    CFSG.Timmesfeld.Connectivity.closure_image_eq_top (G := B) (Q := A) (D := D') h
      (e.symm : B →* A) e.symm.surjective
  rwa [← himg]

theorem notMem_center_of_map_mem_iff {A B : Type} [Group A] [Group B] (e : A ≃* B)
    {D : Set A} {D' : Set B} (hD : ∀ a : A, a ∈ D ↔ e a ∈ D')
    (h : ∀ d ∈ D', d ∉ Subgroup.center B) : ∀ d ∈ D, d ∉ Subgroup.center A := by
  intro d hd hc
  refine h (e d) ((hD d).1 hd) ?_
  have hgoal : e d ∈ (Subgroup.center A).map (e : A →* B) :=
    Subgroup.mem_map_equiv.mpr (by simpa using hc)
  rwa [Subgroup.map_center_eq (e : A ≃* B)] at hgoal

theorem transvConclusionSp_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    {Δ : Set (Subgroup A)} {Δ' : Set (Subgroup B)}
    (hΔ : ∀ X : Subgroup A, X.map e.toMonoidHom ∈ Δ' ↔ X ∈ Δ)
    {f : ℕ} (h : TransvConclusionSp B Δ' f) : TransvConclusionSp A Δ f := by
  obtain ⟨n, hn, Φ, hΦ, hchar⟩ := h
  have hid : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id A :=
    MonoidHom.ext fun x => e.symm_apply_apply x
  have hid2 : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id B :=
    MonoidHom.ext fun x => e.apply_symm_apply x
  refine ⟨n, hn, e.symm.toMonoidHom.comp Φ, ?_, ?_⟩
  · exact ⟨e.symm.injective.comp hΦ.1, e.symm.surjective.comp hΦ.2⟩
  · intro X
    rw [← hΔ X]
    constructor
    · intro hX
      obtain ⟨g, hg⟩ := (hchar (X.map e.toMonoidHom)).1 hX
      refine ⟨g, ?_⟩
      have h := congrArg (Subgroup.map e.symm.toMonoidHom) hg
      simpa only [Subgroup.map_map, MonoidHom.comp_assoc, hid, Subgroup.map_id,
        Timmesfeld.ARS.conjSub] using h
    · intro hX
      obtain ⟨g, hg⟩ := hX
      refine (hchar (X.map e.toMonoidHom)).2 ⟨g, ?_⟩
      have h := congrArg (Subgroup.map e.toMonoidHom) hg
      simpa only [Subgroup.map_map, ← MonoidHom.comp_assoc, hid2, MonoidHom.id_comp,
        Subgroup.map_id, Timmesfeld.ARS.conjSub] using h

theorem map_conjSubgroup_subgroupOf {V K : Subgroup G} (hVK : V ≤ K) (g : ↥K) :
    (conjSubgroup g (V.subgroupOf K)).map K.subtype = conjSubgroup (g : G) V := by
  rw [conjSubgroup_subgroupOf,
    Subgroup.map_subgroupOf_eq_of_le (conjSubgroup_le_of_le_of_mem hVK g.2)]

theorem subgroupOf_wOf {V H K : Subgroup G} (hVK : V ≤ K) (hHK : H ≤ K) :
    (wOf V H).subgroupOf K = wOf (V.subgroupOf K) (H.subgroupOf K) := by
  apply Subgroup.map_injective (f := K.subtype) K.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le ((wOf_le_H V H).trans hHK),
    map_wOf_subgroupOf hVK hHK]

theorem subgroupOf_cPbar {V H P K : Subgroup G} (hVK : V ≤ K) (hHK : H ≤ K)
    (hVH : V ≤ H) (hPK : P ≤ K) :
    (cPbar V H P).subgroupOf K = cPbar (V.subgroupOf K) (H.subgroupOf K) (P.subgroupOf K) := by
  have hCK : cPbar V H P ≤ K := by
    rw [cPbar]
    exact inf_le_left.trans hPK
  apply Subgroup.map_injective (f := K.subtype) K.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le hCK, map_cPbar_subgroupOf hVK hHK hVH hPK]

open CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent in
theorem sec23Data_subgroupOf {V H K : Subgroup G} (hVK : V ≤ K) (hHK : H ≤ K) (hVH : V ≤ H)
    (h : Sec23Data V H) : Sec23Data (V.subgroupOf K) (H.subgroupOf K) := by
  have hD : ∀ d : Xbar (V.subgroupOf K) (H.subgroupOf K),
      d ∈ Dy (V.subgroupOf K) (H.subgroupOf K) ↔
        xbarEquivSubgroupOf hVK hHK hVH d ∈ Dy V H :=
    fun d => mem_Dy_subgroupOf_iff hVK hHK hVH d
  exact
    { isClass := exists_isConj_of_map_mem_iff (xbarEquivSubgroupOf hVK hHK hVH) hD h.isClass
      root := isRootInvolutionSet_of_map_mem_iff (xbarEquivSubgroupOf hVK hHK hVH) hD h.root
      gen := closure_eq_top_of_map_mem_iff (xbarEquivSubgroupOf hVK hHK hVH) hD h.gen
      solv := LinUnitParab.solvNormalCentral_of_mulEquiv (xbarEquivSubgroupOf hVK hHK hVH).symm
        h.solv
      noncentral :=
        notMem_center_of_map_mem_iff (xbarEquivSubgroupOf hVK hHK hVH) hD h.noncentral }

theorem degenerate_subgroupOf {V H K : Subgroup G} (hVK : V ≤ K) (hHK : H ≤ K) (hVH : V ≤ H)
    (h : ∀ d ∈ Dy V H, ∀ e ∈ Dy V H, orderOf (d * e) ≠ 4) :
    ∀ d ∈ Dy (V.subgroupOf K) (H.subgroupOf K),
      ∀ e ∈ Dy (V.subgroupOf K) (H.subgroupOf K), orderOf (d * e) ≠ 4 := by
  intro d hd e he h4
  apply h (xbarEquivSubgroupOf hVK hHK hVH d) ((mem_Dy_subgroupOf_iff hVK hHK hVH d).1 hd)
    (xbarEquivSubgroupOf hVK hHK hVH e) ((mem_Dy_subgroupOf_iff hVK hHK hVH e).1 he)
  rw [← map_mul, MulEquiv.orderOf_eq]
  exact h4

theorem sec23Three_subgroupOf {V H K : Subgroup G} (hVK : V ≤ K) (hHK : H ≤ K) (hVH : V ≤ H)
    (h : Sec23Three V H) : Sec23Three (V.subgroupOf K) (H.subgroupOf K) := by
  obtain ⟨f, hf, hq, htrans⟩ := h
  refine ⟨f, hf, hq.trans (qBar_subgroupOf hVK hHK).symm, ?_⟩
  refine transvConclusionSp_of_mulEquiv (xbarZEquivSubgroupOf hVK hHK hVH) ?_ htrans
  intro X
  exact mem_rootClassZ_subgroupOf_iff hVK hHK hVH X

theorem sec24bTilde_subgroupOf {V H P K : Subgroup G} (hVK : V ≤ K) (hHK : H ≤ K)
    (hVH : V ≤ H) (hPK : P ≤ K) (h : Sec24bTilde V H P) :
    Sec24bTilde (V.subgroupOf K) (H.subgroupOf K) (P.subgroupOf K) := by
  have hR := map_Rtilde_subgroupOf hVK hHK hVH hPK
  have hZ := map_VZ_subgroupOf hVK hHK hVH
  have hcore := map_pCoreOf_normalizer_eq (xbarZEquivSubgroupOf hVK hHK hVH) hZ
  apply Subgroup.map_injective (f := (xbarZEquivSubgroupOf hVK hHK hVH).toMonoidHom)
    (xbarZEquivSubgroupOf hVK hHK hVH).injective
  rw [hR, hcore]
  exact h

theorem sec25Concl_main_subgroupOf {V H P K : Subgroup G} (hVK : V ≤ K) (hHK : H ≤ K)
    (hVH : V ≤ H) (hPK : P ≤ K)
    (h : Sec25Concl V H P) :
    ∀ g ∈ xOf (V.subgroupOf K) (H.subgroupOf K),
      (∃ u ∈ V.subgroupOf K, ∃ w ∈ conjSubgroup g (V.subgroupOf K),
        ⁅u, w⁆ ∉ wOf (V.subgroupOf K) (H.subgroupOf K)) →
      (P.subgroupOf K ⊓ xOf (V.subgroupOf K) (H.subgroupOf K)) ⊔
          conjSubgroup g (V.subgroupOf K) = xOf (V.subgroupOf K) (H.subgroupOf K) ∧
      (P.subgroupOf K ⊓ wOf (V.subgroupOf K) (H.subgroupOf K)) ⊔
          (conjSubgroup g (V.subgroupOf K) ⊓ wOf (V.subgroupOf K) (H.subgroupOf K)) =
        wOf (V.subgroupOf K) (H.subgroupOf K) ∧
      (P.subgroupOf K ⊓ wOf (V.subgroupOf K) (H.subgroupOf K)) ⊓
          (conjSubgroup g (V.subgroupOf K) ⊓ wOf (V.subgroupOf K) (H.subgroupOf K)) = ⊥ := by
  have hWle : wOf V H ≤ K := (wOf_le_H V H).trans hHK
  have hPx : (P ⊓ xOf V H).subgroupOf K =
      P.subgroupOf K ⊓ xOf (V.subgroupOf K) (H.subgroupOf K) := by
    apply Subgroup.map_injective (f := K.subtype) K.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le (inf_le_left.trans hPK),
      Subgroup.map_inf_eq _ _ K.subtype K.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hPK, map_xOf_subgroupOf hVK hHK hVH]
  have hPw : (P ⊓ wOf V H).subgroupOf K =
      P.subgroupOf K ⊓ wOf (V.subgroupOf K) (H.subgroupOf K) := by
    apply Subgroup.map_injective (f := K.subtype) K.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le (inf_le_left.trans hPK),
      Subgroup.map_inf_eq _ _ K.subtype K.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hPK, map_wOf_subgroupOf hVK hHK]
  have hconj : ∀ g : ↥K, (conjSubgroup (g : G) V).subgroupOf K =
      conjSubgroup g (V.subgroupOf K) := fun g => (conjSubgroup_subgroupOf K V g).symm
  have hconjW : ∀ g : ↥K, (conjSubgroup (g : G) V ⊓ wOf V H).subgroupOf K =
      conjSubgroup g (V.subgroupOf K) ⊓ wOf (V.subgroupOf K) (H.subgroupOf K) := by
    intro g
    apply Subgroup.map_injective (f := K.subtype) K.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le
        (inf_le_left.trans (conjSubgroup_le_of_le_of_mem hVK g.2)),
      Subgroup.map_inf_eq _ _ K.subtype K.subtype_injective,
      map_conjSubgroup_subgroupOf hVK g, map_wOf_subgroupOf hVK hHK]
  intro g₀ hg₀ hbase
  obtain ⟨u₀, hu₀, w₀, hw₀, hc₀⟩ := hbase
  have hg : (g₀ : G) ∈ xOf V H := (mem_xOf_subgroupOf_iff hVK hHK hVH).mp hg₀
  have hconjmap := map_conjSubgroup_subgroupOf hVK g₀
  have hw : (w₀ : G) ∈ conjSubgroup (g₀ : G) V := by
    rw [← hconjmap]
    exact Subgroup.mem_map_of_mem K.subtype hw₀
  have hc : ⁅(u₀ : G), (w₀ : G)⁆ ∉ wOf V H := fun hcontra =>
    hc₀ ((mem_wOf_subgroupOf_iff hVK hHK).mpr hcontra)
  obtain ⟨h1, h2, h3⟩ := h.1 (g₀ : G) hg
    ⟨u₀, Subgroup.mem_subgroupOf.mp hu₀, w₀, hw, hc⟩
  have h1' := congrArg (fun S : Subgroup G => S.subgroupOf K) h1
  rw [Subgroup.subgroupOf_sup (inf_le_left.trans hPK)
    (conjSubgroup_le_of_le_of_mem hVK g₀.2), hPx, hconj g₀,
    subgroupOf_xOf hVK hHK hVH] at h1'
  refine ⟨h1', ?_, ?_⟩
  · have h2' := congrArg (fun S : Subgroup G => S.subgroupOf K) h2
    rw [Subgroup.subgroupOf_sup (inf_le_left.trans hPK) (inf_le_right.trans hWle),
      hPw, hconjW g₀, subgroupOf_wOf hVK hHK] at h2'
    exact h2'
  · have h3' := congrArg (fun S : Subgroup G => S.subgroupOf K) h3
    change (P ⊓ wOf V H).subgroupOf K ⊓
      (conjSubgroup (g₀ : G) V ⊓ wOf V H).subgroupOf K =
        (⊥ : Subgroup G).subgroupOf K at h3'
    rw [hPw, hconjW g₀, Subgroup.bot_subgroupOf] at h3'
    exact h3'

theorem sec25Concl_subgroupOf {V H P K : Subgroup G} (hVK : V ≤ K) (hHK : H ≤ K)
    (hVH : V ≤ H) (hPK : P ≤ K) (h : Sec25Concl V H P) :
    Sec25Concl (V.subgroupOf K) (H.subgroupOf K) (P.subgroupOf K) := by
  have hWle : wOf V H ≤ K := (wOf_le_H V H).trans hHK
  have hPw : (P ⊓ wOf V H).subgroupOf K =
      P.subgroupOf K ⊓ wOf (V.subgroupOf K) (H.subgroupOf K) := by
    apply Subgroup.map_injective (f := K.subtype) K.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le (inf_le_left.trans hPK),
      Subgroup.map_inf_eq _ _ K.subtype K.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hPK, map_wOf_subgroupOf hVK hHK]
  have hconjW : ∀ g : ↥K, (conjSubgroup (g : G) V ⊓ wOf V H).subgroupOf K =
      conjSubgroup g (V.subgroupOf K) ⊓ wOf (V.subgroupOf K) (H.subgroupOf K) := by
    intro g
    apply Subgroup.map_injective (f := K.subtype) K.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le
        (inf_le_left.trans (conjSubgroup_le_of_le_of_mem hVK g.2)),
      Subgroup.map_inf_eq _ _ K.subtype K.subtype_injective,
      map_conjSubgroup_subgroupOf hVK g, map_wOf_subgroupOf hVK hHK]
  have hCK : cPbar V H P ≤ K := by
    rw [cPbar]
    exact inf_le_left.trans hPK
  refine ⟨sec25Concl_main_subgroupOf hVK hHK hVH hPK h, ?_, ?_⟩
  · have hX := congrArg (fun S : Subgroup G => S.subgroupOf K) h.2.1
    rw [Subgroup.subgroupOf_sup ((xOf_le_H hVH).trans hHK) hCK,
      subgroupOf_xOf hVK hHK hVH, subgroupOf_cPbar hVK hHK hVH hPK] at hX
    exact hX
  · have hAb := h.2.2.subgroupOf K
    rw [Subgroup.subgroupOf_sup hWle hCK, subgroupOf_wOf hVK hHK,
      subgroupOf_cPbar hVK hHK hVH hPK] at hAb
    exact hAb

theorem residualBarFields [Finite G] {M V Q P H : Subgroup G} (hH : TwoEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥)
    (hn : ∃ n : ℕ, 3 ≤ n ∧
      Nonempty (↥(StatedSp n (GaloisField 2 1)) ≃* XbarZ V H)) :
    Sec23Data (V.subgroupOf (pResidual 2 G)) (H.subgroupOf (pResidual 2 G)) ∧
    (∀ d ∈ Dy (V.subgroupOf (pResidual 2 G)) (H.subgroupOf (pResidual 2 G)),
      ∀ e ∈ Dy (V.subgroupOf (pResidual 2 G)) (H.subgroupOf (pResidual 2 G)),
        orderOf (d * e) ≠ 4) ∧
    qBar (V.subgroupOf (pResidual 2 G)) (H.subgroupOf (pResidual 2 G)) = 2 ∧
    Sec23Three (V.subgroupOf (pResidual 2 G)) (H.subgroupOf (pResidual 2 G)) ∧
    Sec24bTilde (V.subgroupOf (pResidual 2 G)) (H.subgroupOf (pResidual 2 G))
      (P.subgroupOf (pResidual 2 G)) ∧
    Sec25Concl (V.subgroupOf (pResidual 2 G)) (H.subgroupOf (pResidual 2 G))
      (P.subgroupOf (pResidual 2 G)) ∧
    Nat.card ↥(V.subgroupOf (pResidual 2 G) ⊓
        wOf (V.subgroupOf (pResidual 2 G)) (H.subgroupOf (pResidual 2 G))) =
      qBar (V.subgroupOf (pResidual 2 G)) (H.subgroupOf (pResidual 2 G)) ∧
    Nonempty (Xbar (V.subgroupOf (pResidual 2 G)) (H.subgroupOf (pResidual 2 G)) ≃*
      Xbar V H) := by
  have hVH : V ≤ H := hH.setup.mc.toMinCex.V_le_H
  have hPH : P ≤ H := hH.setup.mc.toMinCex.PleH
  have hV : V ≤ pResidual 2 G := V_le_pResidual_of_twoEnd hH hZ hn
  have hHle : H ≤ pResidual 2 G := H_le_pResidual_of_twoEnd hH hZ hn
  exact ⟨sec23Data_subgroupOf hV hHle hVH hH.setup.data,
    degenerate_subgroupOf hV hHle hVH hH.setup.degenerate,
    (qBar_subgroupOf hV hHle).trans hH.q_two,
    sec23Three_subgroupOf hV hHle hVH hH.three,
    sec24bTilde_subgroupOf hV hHle hVH (hPH.trans hHle) hH.tilde,
    sec25Concl_subgroupOf hV hHle hVH (hPH.trans hHle) hH.concl,
    (card_inf_wOf_subgroupOf hV hHle).trans
      (hH.module.trans (qBar_subgroupOf hV hHle).symm),
    ⟨xbarEquivSubgroupOf hV hHle hVH⟩⟩

end CFSG.RankThree.GF2n.Tim79a

end
