module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91Defs
import CFSG.GH74.GLS.AssemblyComponents
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.ExtraspecialTransport
import CFSG.LocalAnalysis.AGLEmbedding.Norton.OrdinaryProofs.SylowTransport
import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer
import CFSG.HardMathSupport.Malle.OvergroupTransport.Transport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.LocalAnalysis.UniquenessCase.UC22.F08
open CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups (IsExtraspecialExpP)
open scoped commutatorElement

private theorem k891list897_kernel_center_of_commutator_le {X Y : Type} [Group X] [Group Y]
    (O : Subgroup X) [O.Normal] (φ : X →* Y) (hO : O ≤ φ.ker)
    (hcomm : ⁅φ.ker, ⊤⁆ ≤ O) :
    (QuotientGroup.lift O φ hO).ker ≤ center (X ⧸ O) := by
  rw [QuotientGroup.ker_lift]
  rintro _ ⟨k, hk, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨y', rfl⟩ := QuotientGroup.mk'_surjective O y
  have hmem : ⁅k, y'⁆ ∈ O :=
    hcomm (Subgroup.commutator_mem_commutator hk (Subgroup.mem_top y'))
  have h1 : (QuotientGroup.mk' O) ⁅k, y'⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr hmem
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1.symm

private theorem k891list897_derInf8_le {G : Type} [Group G] [Finite G] (X : Subgroup G) :
    DerInf8 X ≤ X := by
  rw [show DerInf8 X = (CFSG.perfectResidual ↥X).map X.subtype from rfl]
  exact Subgroup.map_subtype_le _

private theorem k891list897_Z_le_center_H {G : Type} [Group G] [Finite G] (L S : Subgroup G) :
    (R891Z L S).subgroupOf (R891H L S) ≤ center ↥(R891H L S) := by
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro h
  apply Subtype.ext
  exact (Subgroup.mem_centralizer_iff.mp h.2 z.1 hz).symm

private def k891list897_Y1 {G : Type} [Group G] [Finite G] (L S : Subgroup G)
    (Ys : Subgroup (R891Star (R891H L S) (R891Z L S))) : Subgroup G :=
  (Ys.comap (QuotientGroup.mk' (R891Ker (R891H L S) (R891Z L S)))).map (R891H L S).subtype

private theorem k891list897_Y_le_H {G : Type} [Group G] [Finite G] (L S : Subgroup G)
    (Ys : Subgroup (R891Star (R891H L S) (R891Z L S))) :
    R891Y (R891H L S) (R891Z L S) Ys ≤ R891H L S :=
  (k891list897_derInf8_le (k891list897_Y1 L S Ys)).trans (Subgroup.map_subtype_le _)

private theorem k891list897_perfectResidual_map_equiv {X Y : Type} [Group X] [Group Y]
    (e : X ≃* Y) : (CFSG.perfectResidual X).map e.toMonoidHom = CFSG.perfectResidual Y := by
  rw [CFSG.perfectResidual, CFSG.perfectResidual, Subgroup.map_iInf _ e.injective]
  exact iInf_congr fun n => map_derivedSeries_eq e.surjective n

private theorem k891list897_derInf8_map_subtype {G : Type} [Group G] [Finite G]
    (H : Subgroup G) (P : Subgroup ↥H) :
    DerInf8 (P.map H.subtype) = (DerInf8 P).map H.subtype := by
  let e : ↥P ≃* ↥(P.map H.subtype) :=
    Subgroup.equivMapOfInjective P H.subtype H.subtype_injective
  have he : (P.map H.subtype).subtype.comp e.toMonoidHom = H.subtype.comp P.subtype := by
    ext x
    rfl
  calc DerInf8 (P.map H.subtype)
      = (CFSG.perfectResidual ↥(P.map H.subtype)).map (P.map H.subtype).subtype := rfl
    _ = ((CFSG.perfectResidual ↥P).map e.toMonoidHom).map (P.map H.subtype).subtype := by
          rw [k891list897_perfectResidual_map_equiv e]
    _ = (CFSG.perfectResidual ↥P).map ((P.map H.subtype).subtype.comp e.toMonoidHom) := by
          rw [Subgroup.map_map]
    _ = (CFSG.perfectResidual ↥P).map (H.subtype.comp P.subtype) := by rw [he]
    _ = ((CFSG.perfectResidual ↥P).map P.subtype).map H.subtype := by
          rw [Subgroup.map_map]
    _ = (DerInf8 P).map H.subtype := rfl

private theorem k891list897_derivedSeries_eq_top {X : Type} [Group X] (hX : Group.IsPerfect X)
    (n : ℕ) : derivedSeries X n = ⊤ := by
  induction n with
  | zero => exact derivedSeries_zero X
  | succ n ih =>
      rw [derivedSeries_succ, ih]
      exact hX.commutator_eq_top

private theorem k891list897_Y_map_mk_eq {G : Type} [Group G] [Finite G] (L S : Subgroup G)
    (Ys : Subgroup (R891Star (R891H L S) (R891Z L S))) (hYs : CFSG.Open.IsQuasisimple ↥Ys) :
    ((R891Y (R891H L S) (R891Z L S) Ys).subgroupOf (R891H L S)).map
      (QuotientGroup.mk' (R891Ker (R891H L S) (R891Z L S))) = Ys := by
  let H : Subgroup G := R891H L S
  let Z : Subgroup G := R891Z L S
  let Ker : Subgroup ↥H := R891Ker H Z
  let P : Subgroup ↥H := Ys.comap (QuotientGroup.mk' Ker)
  have hY1 : R891Y H Z Ys = DerInf8 (P.map H.subtype) := rfl
  have hsub : (DerInf8 (P.map H.subtype)).subgroupOf H = DerInf8 P := by
    change (DerInf8 (P.map H.subtype)).comap H.subtype = DerInf8 P
    rw [k891list897_derInf8_map_subtype H P,
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  let g : ↥P →* ↥Ys :=
    { toFun := fun x => ⟨(QuotientGroup.mk' Ker) x.1, Subgroup.mem_comap.mp x.2⟩
      map_one' := Subtype.ext (map_one (QuotientGroup.mk' Ker))
      map_mul' := fun x y => Subtype.ext (map_mul (QuotientGroup.mk' Ker) x.1 y.1) }
  have hg : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨h, hh⟩ := QuotientGroup.mk'_surjective Ker y
    exact ⟨⟨h, Subgroup.mem_comap.mpr (by rw [hh]; exact hy)⟩, Subtype.ext hh⟩
  have hcomp : (QuotientGroup.mk' Ker).comp P.subtype = Ys.subtype.comp g := by
    ext x
    rfl
  have hperf : (CFSG.perfectResidual ↥P).map g = ⊤ := by
    obtain ⟨N, hN, -⟩ := CFSG.exists_perfectResidual_eq_derivedSeries (G := ↥P)
    rw [hN, map_derivedSeries_eq hg N]
    exact k891list897_derivedSeries_eq_top ⟨hYs.1⟩ N
  calc ((R891Y H Z Ys).subgroupOf H).map (QuotientGroup.mk' Ker)
      = (DerInf8 P).map (QuotientGroup.mk' Ker) := by rw [hY1, hsub]
    _ = ((CFSG.perfectResidual ↥P).map P.subtype).map (QuotientGroup.mk' Ker) := rfl
    _ = (CFSG.perfectResidual ↥P).map ((QuotientGroup.mk' Ker).comp P.subtype) := by
          rw [Subgroup.map_map]
    _ = (CFSG.perfectResidual ↥P).map (Ys.subtype.comp g) := by rw [hcomp]
    _ = ((CFSG.perfectResidual ↥P).map g).map Ys.subtype := by
          rw [Subgroup.map_map]
    _ = (⊤ : Subgroup ↥Ys).map Ys.subtype := by rw [hperf]
    _ = Ys := le_antisymm (Subgroup.map_subtype_le (H := Ys) (K := ⊤))
          (fun y hy => Subgroup.mem_map.mpr ⟨⟨y, hy⟩, Subgroup.mem_top _, rfl⟩)

private theorem k891list897_Y_subnormal_H {G : Type} [Group G] [Finite G] (L S : Subgroup G)
    (Ys : Subgroup (R891Star (R891H L S) (R891Z L S)))
    (hcomp : CFSG.Open.IsSubnormal Ys ⊤) :
    CFSG.Open.IsSubnormal (R891Y (R891H L S) (R891Z L S) Ys) (R891H L S) := by
  let H := R891H L S
  let Z := R891Z L S
  let Ker : Subgroup ↥H := R891Ker H Z
  let P : Subgroup ↥H := Ys.comap (QuotientGroup.mk' Ker)
  let Y1 : Subgroup G := P.map H.subtype
  let Y : Subgroup G := R891Y H Z Ys
  have hYeq : Y = DerInf8 Y1 := rfl
  have hPsub : CFSG.Open.IsSubnormal P ⊤ := by
    have := CFSG.Open.IsSubnormal.comap (f := QuotientGroup.mk' Ker) hcomp
    rwa [Subgroup.comap_top] at this
  have hY1subH : CFSG.Open.IsSubnormal Y1 H := by
    have h := CFSG.Open.IsSubnormal.map H.subtype hPsub
    rw [Subgroup.map_top, Subgroup.range_subtype] at h
    exact h
  have hYY1 : Y ≤ Y1 := by rw [hYeq]; exact k891list897_derInf8_le Y1
  have hYnorm : (Y.subgroupOf Y1).Normal := by
    have heq : Y.subgroupOf Y1 = CFSG.perfectResidual ↥Y1 := by
      change Y.comap Y1.subtype = CFSG.perfectResidual ↥Y1
      rw [show Y = (CFSG.perfectResidual ↥Y1).map Y1.subtype from rfl,
        Subgroup.comap_map_eq_self_of_injective Y1.subtype_injective]
    rw [heq]
    infer_instance
  exact CFSG.Open.IsSubnormal.step hYY1 hYnorm hY1subH

private theorem k891list897_pPrimeCore_Y_map_le_H {G : Type} [Group G] [Finite G]
    (L S : Subgroup G) (Ys : Subgroup (R891Star (R891H L S) (R891Z L S)))
    (hsub : CFSG.Open.IsSubnormal (R891Y (R891H L S) (R891Z L S) Ys) (R891H L S)) :
    (CFSG.pPrimeCore 3 ↥(R891Y (R891H L S) (R891Z L S) Ys)).map
        (R891Y (R891H L S) (R891Z L S) Ys).subtype ≤
      (CFSG.pPrimeCore 3 ↥(R891H L S)).map (R891H L S).subtype := by
  let H := R891H L S
  let Z := R891Z L S
  let Y : Subgroup G := R891Y H Z Ys
  let Yh : Subgroup ↥H := Y.subgroupOf H
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hYh : Yh.IsSubnormal :=
    (CFSG.Open.IsSubnormal.iff_subgroupOf (k891list897_Y_le_H L S Ys)).mp hsub
  have hA_sub : ((CFSG.pPrimeCore 3 ↥Yh).map Yh.subtype).IsSubnormal := by
    refine Subgroup.IsSubnormal.step _ Yh (Subgroup.map_subtype_le _) hYh ?_
    rw [show ((CFSG.pPrimeCore 3 ↥Yh).map Yh.subtype).subgroupOf Yh = CFSG.pPrimeCore 3 ↥Yh from
      Subgroup.comap_map_eq_self_of_injective Yh.subtype_injective _]
    infer_instance
  have hA_cop : Nat.Coprime 3 (Nat.card ((CFSG.pPrimeCore 3 ↥Yh).map Yh.subtype)) := by
    rw [Subgroup.card_map_of_injective Yh.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥Yh)
  have hA_le : (CFSG.pPrimeCore 3 ↥Yh).map Yh.subtype ≤ CFSG.pPrimeCore 3 ↥H :=
    CFSG.GH74.GLS.le_pPrimeCore_of_subnormal 3 hA_sub hA_cop
  let e : ↥Y ≃* ↥Yh := (Subgroup.subgroupOfEquivOfLe (k891list897_Y_le_H L S Ys)).symm
  have he : Y.subtype = H.subtype.comp (Yh.subtype.comp e.toMonoidHom) := by
    ext x
    rfl
  have hpY : (CFSG.pPrimeCore 3 ↥Y).map Y.subtype =
      ((CFSG.pPrimeCore 3 ↥Yh).map Yh.subtype).map H.subtype :=
    calc (CFSG.pPrimeCore 3 ↥Y).map Y.subtype
        = (CFSG.pPrimeCore 3 ↥Y).map (H.subtype.comp (Yh.subtype.comp e.toMonoidHom)) := by
            rw [he]
      _ = ((CFSG.pPrimeCore 3 ↥Y).map (Yh.subtype.comp e.toMonoidHom)).map H.subtype :=
            (Subgroup.map_map (CFSG.pPrimeCore 3 ↥Y) H.subtype
              (Yh.subtype.comp e.toMonoidHom)).symm
      _ = (((CFSG.pPrimeCore 3 ↥Y).map e.toMonoidHom).map Yh.subtype).map H.subtype :=
            congrArg (fun K : Subgroup ↥H => K.map H.subtype)
              (Subgroup.map_map (CFSG.pPrimeCore 3 ↥Y) Yh.subtype e.toMonoidHom).symm
      _ = ((CFSG.pPrimeCore 3 ↥Yh).map Yh.subtype).map H.subtype := by
            rw [pPrimeCore_map_iso 3 e]
  calc (CFSG.pPrimeCore 3 ↥Y).map Y.subtype
      = ((CFSG.pPrimeCore 3 ↥Yh).map Yh.subtype).map H.subtype := hpY
    _ ≤ (CFSG.pPrimeCore 3 ↥H).map H.subtype := Subgroup.map_mono hA_le

private noncomputable def k891list897_iota {G : Type} [Group G] [Finite G] (L S : Subgroup G)
    (Ys : Subgroup (R891Star (R891H L S) (R891Z L S))) :
    ↥(R891Y (R891H L S) (R891Z L S) Ys) →* ↥(R891H L S) :=
  { toFun := fun y => ⟨y.1, k891list897_Y_le_H L S Ys y.2⟩
    map_one' := Subtype.ext rfl
    map_mul' := fun _ _ => Subtype.ext rfl }

private theorem k891list897_iota_injective {G : Type} [Group G] [Finite G] (L S : Subgroup G)
    (Ys : Subgroup (R891Star (R891H L S) (R891Z L S))) :
    Function.Injective (k891list897_iota L S Ys) :=
  fun _ _ h => Subtype.ext (by
    have h' := congrArg (fun z : ↥(R891H L S) => (z : G)) h
    simpa [k891list897_iota] using h')

private noncomputable def k891list897_fY {G : Type} [Group G] [Finite G] (L S : Subgroup G)
    (Ys : Subgroup (R891Star (R891H L S) (R891Z L S)))
    (hYs : CFSG.Open.IsQuasisimple ↥Ys) :
    ↥(R891Y (R891H L S) (R891Z L S) Ys) →* ↥Ys :=
  { toFun := fun x =>
      ⟨(QuotientGroup.mk' (R891Ker (R891H L S) (R891Z L S)))
        (k891list897_iota L S Ys x), by
        have h := k891list897_Y_map_mk_eq L S Ys hYs
        have hmem : (QuotientGroup.mk' (R891Ker (R891H L S) (R891Z L S)))
            (k891list897_iota L S Ys x) ∈
            ((R891Y (R891H L S) (R891Z L S) Ys).subgroupOf (R891H L S)).map
              (QuotientGroup.mk' (R891Ker (R891H L S) (R891Z L S))) :=
          Subgroup.mem_map.mpr ⟨k891list897_iota L S Ys x,
            Subgroup.mem_subgroupOf.mpr x.2, rfl⟩
        rwa [h] at hmem⟩
    map_one' := Subtype.ext (by
      change (QuotientGroup.mk' (R891Ker (R891H L S) (R891Z L S)))
        (k891list897_iota L S Ys 1) = 1
      rw [map_one, map_one])
    map_mul' := fun x y => Subtype.ext (by
      change (QuotientGroup.mk' (R891Ker (R891H L S) (R891Z L S)))
        (k891list897_iota L S Ys (x * y)) =
          (QuotientGroup.mk' (R891Ker (R891H L S) (R891Z L S)))
            (k891list897_iota L S Ys x) *
          (QuotientGroup.mk' (R891Ker (R891H L S) (R891Z L S)))
            (k891list897_iota L S Ys y)
      rw [map_mul, map_mul]) }

private theorem k891list897_fY_val {G : Type} [Group G] [Finite G] (L S : Subgroup G)
    (Ys : Subgroup (R891Star (R891H L S) (R891Z L S)))
    (hYs : CFSG.Open.IsQuasisimple ↥Ys)
    (x : ↥(R891Y (R891H L S) (R891Z L S) Ys)) :
    (k891list897_fY L S Ys hYs x).1 =
      (QuotientGroup.mk' (R891Ker (R891H L S) (R891Z L S)))
        (k891list897_iota L S Ys x) :=
  rfl

private theorem k891list897_fY_surjective {G : Type} [Group G] [Finite G] (L S : Subgroup G)
    (Ys : Subgroup (R891Star (R891H L S) (R891Z L S)))
    (hYs : CFSG.Open.IsQuasisimple ↥Ys) :
    Function.Surjective (k891list897_fY L S Ys hYs) := by
  rintro ⟨ys, hys⟩
  have h := k891list897_Y_map_mk_eq L S Ys hYs
  have hmem : ys ∈ ((R891Y (R891H L S) (R891Z L S) Ys).subgroupOf (R891H L S)).map
      (QuotientGroup.mk' (R891Ker (R891H L S) (R891Z L S))) := by
    rw [h]; exact hys
  obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hmem
  refine ⟨⟨x.1, Subgroup.mem_subgroupOf.mp hx⟩, Subtype.ext ?_⟩
  rw [k891list897_fY_val]
  rw [show k891list897_iota L S Ys ⟨x.1, Subgroup.mem_subgroupOf.mp hx⟩ = x from
    Subtype.ext rfl]
  exact hxy

private theorem k891list897_comm_Ker_le_OH {G : Type} [Group G] [Finite G] (L S : Subgroup G) :
    ⁅R891Ker (R891H L S) (R891Z L S), ⊤⁆ ≤ CFSG.pPrimeCore 3 ↥(R891H L S) := by
  let H := R891H L S
  let Z := R891Z L S
  let OH : Subgroup ↥H := CFSG.pPrimeCore 3 ↥H
  let Zh : Subgroup ↥H := Z.subgroupOf H
  have hOHn : OH.Normal := inferInstance
  have hZhn : Zh.Normal := Subgroup.normal_of_le_center (k891list897_Z_le_center_H L S)
  have hsupn : (OH ⊔ Zh).Normal := Subgroup.sup_normal OH Zh
  have hKer_le : R891Ker H Z ≤ OH ⊔ Zh := by
    refine Subgroup.normalClosure_le_normal (N := OH ⊔ Zh) ?_
    intro x hx
    rcases hx with hx | hx
    · exact Subgroup.mem_sup_left hx
    · exact Subgroup.mem_sup_right hx
  have hZh_comm : ⁅Zh, (⊤ : Subgroup ↥H)⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact Subgroup.mem_center_iff.mp (k891list897_Z_le_center_H L S hz) w
  calc ⁅R891Ker H Z, (⊤ : Subgroup ↥H)⁆ ≤ ⁅OH ⊔ Zh, (⊤ : Subgroup ↥H)⁆ :=
        Subgroup.commutator_mono hKer_le le_rfl
    _ = ⁅OH, (⊤ : Subgroup ↥H)⁆ ⊔ ⁅Zh, (⊤ : Subgroup ↥H)⁆ :=
        Subgroup.commutator_sup_right OH Zh (⊤ : Subgroup ↥H)
    _ ≤ OH ⊔ ⊥ := sup_le_sup (Subgroup.commutator_le_left OH (⊤ : Subgroup ↥H))
        (le_of_eq hZh_comm)
    _ = OH := sup_bot_eq OH

private theorem k891list897_O_le_fY_ker {G : Type} [Group G] [Finite G] (L S : Subgroup G)
    (Ys : Subgroup (R891Star (R891H L S) (R891Z L S)))
    (hYs : CFSG.Open.IsQuasisimple ↥Ys)
    (hsub : CFSG.Open.IsSubnormal (R891Y (R891H L S) (R891Z L S) Ys) (R891H L S)) :
    CFSG.pPrimeCore 3 ↥(R891Y (R891H L S) (R891Z L S) Ys) ≤
      (k891list897_fY L S Ys hYs).ker := by
  intro y hy
  rw [MonoidHom.mem_ker]
  apply Subtype.ext
  change (QuotientGroup.mk' (R891Ker (R891H L S) (R891Z L S)))
      (k891list897_iota L S Ys y) = 1
  apply (QuotientGroup.eq_one_iff _).mpr
  have hle := k891list897_pPrimeCore_Y_map_le_H L S Ys hsub
  have hOH : CFSG.pPrimeCore 3 ↥(R891H L S) ≤ R891Ker (R891H L S) (R891Z L S) :=
    fun x hx => Subgroup.subset_normalClosure (Or.inl hx)
  have hmap : (CFSG.pPrimeCore 3 ↥(R891Y (R891H L S) (R891Z L S) Ys)).map
        (R891Y (R891H L S) (R891Z L S) Ys).subtype ≤
      (R891Ker (R891H L S) (R891Z L S)).map (R891H L S).subtype :=
    hle.trans (Subgroup.map_mono hOH)
  have hy' : y.1 ∈ (CFSG.pPrimeCore 3 ↥(R891Y (R891H L S) (R891Z L S) Ys)).map
      (R891Y (R891H L S) (R891Z L S) Ys).subtype :=
    Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
  have hy'' : y.1 ∈ (R891Ker (R891H L S) (R891Z L S)).map (R891H L S).subtype := hmap hy'
  obtain ⟨k, hk, hky⟩ := Subgroup.mem_map.mp hy''
  have : k = k891list897_iota L S Ys y := Subtype.ext hky
  rwa [this] at hk

private theorem k891list897_comm_fY_ker_le_O {G : Type} [Group G] [Finite G] (L S : Subgroup G)
    (Ys : Subgroup (R891Star (R891H L S) (R891Z L S)))
    (hYs : CFSG.Open.IsQuasisimple ↥Ys) :
    ⁅(k891list897_fY L S Ys hYs).ker,
        (⊤ : Subgroup ↥(R891Y (R891H L S) (R891Z L S) Ys))⁆ ≤
      CFSG.pPrimeCore 3 ↥(R891Y (R891H L S) (R891Z L S) Ys) := by
  let Y : Subgroup G := R891Y (R891H L S) (R891Z L S) Ys
  let K : Subgroup ↥Y := (k891list897_fY L S Ys hYs).ker
  let N : Subgroup ↥Y := ⁅K, (⊤ : Subgroup ↥Y)⁆
  have hKmap : K.map (k891list897_iota L S Ys) ≤ R891Ker (R891H L S) (R891Z L S) := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
    have hk1 : k891list897_fY L S Ys hYs k = 1 := MonoidHom.mem_ker.mp hk
    have h1 : (QuotientGroup.mk' (R891Ker (R891H L S) (R891Z L S)))
        (k891list897_iota L S Ys k) = 1 := by
      have := congrArg Subtype.val hk1
      rwa [k891list897_fY_val] at this
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hNmap : N.map (k891list897_iota L S Ys) ≤ CFSG.pPrimeCore 3 ↥(R891H L S) := by
    calc N.map (k891list897_iota L S Ys)
        = ⁅K.map (k891list897_iota L S Ys),
            (⊤ : Subgroup ↥Y).map (k891list897_iota L S Ys)⁆ :=
          Subgroup.map_commutator K (⊤ : Subgroup ↥Y) (k891list897_iota L S Ys)
      _ ≤ ⁅R891Ker (R891H L S) (R891Z L S), (⊤ : Subgroup ↥(R891H L S))⁆ :=
          Subgroup.commutator_mono hKmap le_top
      _ ≤ CFSG.pPrimeCore 3 ↥(R891H L S) := k891list897_comm_Ker_le_OH L S
  have hcard : Nat.card N = Nat.card (N.map (k891list897_iota L S Ys)) :=
    (Subgroup.card_map_of_injective (k891list897_iota_injective L S Ys)).symm
  have hcop : Nat.Coprime 3 (Nat.card N) := by
    rw [hcard]
    exact (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥(R891H L S))).coprime_dvd_right
      (Subgroup.card_dvd_of_le hNmap)
  have hNnormal : N.Normal := Subgroup.commutator_normal K (⊤ : Subgroup ↥Y)
  exact le_sSup ⟨hNnormal, hcop⟩

private theorem k891list897_list896_center_card {X : Type} [Group X] (h : R891List896 X) :
    Nat.card (Subgroup.center X) = 3 := by
  rcases h with h | h | h | h | h
  · exact h.2.1
  · exact h.2.1
  · exact h.2.1
  · rcases h with ⟨p, f, hp, hc⟩ | ⟨p, f, hp, hc⟩
    · exact hc.2.1
    · exact hc.2.1
  · exact h.2.1

private theorem k891list897_Ker_eq_sup {G : Type} [Group G] [Finite G] (L S : Subgroup G) :
    R891Ker (R891H L S) (R891Z L S) =
      CFSG.pPrimeCore 3 ↥(R891H L S) ⊔ (R891Z L S).subgroupOf (R891H L S) := by
  have hZs_center : (R891Z L S).subgroupOf (R891H L S) ≤ Subgroup.center ↥(R891H L S) :=
    k891list897_Z_le_center_H L S
  have hZsN : ((R891Z L S).subgroupOf (R891H L S)).Normal :=
    Subgroup.normal_of_le_center hZs_center
  have hON : (CFSG.pPrimeCore 3 ↥(R891H L S)).Normal := CFSG.pPrimeCore_normal
  unfold R891Ker
  rw [normalClosure_union, normalClosure_eq_self, normalClosure_eq_self]

private noncomputable def k891list897_fbar {G : Type} [Group G] [Finite G]
    {D : Data G} {L S R : Subgroup G} {n : ℕ}
    {Ys : Subgroup (R891Star (R891H L S) (R891Z L S))} (hY : R891YSet D L S n R Ys) :
    (R891Ybar (R891H L S) (R891Z L S) Ys) →* ↥Ys :=
  QuotientGroup.lift (CFSG.pPrimeCore 3 ↥(R891Y (R891H L S) (R891Z L S) Ys))
    (k891list897_fY L S Ys hY.comp.2.2)
    (k891list897_O_le_fY_ker L S Ys hY.comp.2.2
      (k891list897_Y_subnormal_H L S Ys hY.comp.2.1))

private theorem k891list897_fbar_surjective {G : Type} [Group G] [Finite G]
    {D : Data G} {L S R : Subgroup G} {n : ℕ}
    {Ys : Subgroup (R891Star (R891H L S) (R891Z L S))} (hY : R891YSet D L S n R Ys) :
    Function.Surjective (k891list897_fbar hY) := by
  intro y
  obtain ⟨x, hx⟩ := k891list897_fY_surjective L S Ys hY.comp.2.2 y
  refine ⟨QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(R891Y (R891H L S) (R891Z L S) Ys)) x, ?_⟩
  rw [show k891list897_fbar hY
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(R891Y (R891H L S) (R891Z L S) Ys)) x) =
      k891list897_fY L S Ys hY.comp.2.2 x from
    QuotientGroup.lift_mk' _ (φ := k891list897_fY L S Ys hY.comp.2.2) _ x]
  exact hx

private theorem k891list897_center_eq_map_Z {G : Type} [Group G] [Finite G] (D : Data G)
    (L S R A : Subgroup G) (n : ℕ) (hst : R891State D L S R A n)
    (Ys : Subgroup (R891Star (R891H L S) (R891Z L S))) (hY : R891YSet D L S n R Ys)
    (h896 : R891List896 (R891Ybar (R891H L S) (R891Z L S) Ys)) :
    Subgroup.center (R891Ybar (R891H L S) (R891Z L S) Ys) =
      ((R891Z L S).subgroupOf (R891Y (R891H L S) (R891Z L S) Ys)).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(R891Y (R891H L S) (R891Z L S) Ys))) := by
  have hZY : R891Z L S ≤ R891Y (R891H L S) (R891Z L S) Ys := hY.zLe
  have hYH : R891Y (R891H L S) (R891Z L S) Ys ≤ R891H L S := k891list897_Y_le_H L S Ys
  have hZi_center : (R891Z L S).subgroupOf (R891Y (R891H L S) (R891Z L S) Ys) ≤
      Subgroup.center ↥(R891Y (R891H L S) (R891Z L S) Ys) := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (hYH y.2) z.1 (Subgroup.mem_subgroupOf.mp hz)).symm
  let q : ↥(R891Y (R891H L S) (R891Z L S) Ys) →*
      R891Ybar (R891H L S) (R891Z L S) Ys :=
    QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(R891Y (R891H L S) (R891Z L S) Ys))
  have hmap_le : ((R891Z L S).subgroupOf (R891Y (R891H L S) (R891Z L S) Ys)).map q ≤
      Subgroup.center (R891Ybar (R891H L S) (R891Z L S) Ys) :=
    (Subgroup.map_mono hZi_center).trans
      (Subgroup.map_center_le_center (f := q)
        (QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 ↥(R891Y (R891H L S) (R891Z L S) Ys))))
  have hZi_card : Nat.card ((R891Z L S).subgroupOf (R891Y (R891H L S) (R891Z L S) Ys)) = 3 := by
    rw [CFSG.natCard_subgroupOf_eq (R891Z L S) (R891Y (R891H L S) (R891Z L S) Ys) hZY]
    exact hst.basic.zOrder
  have hmap_card_dvd :
      Nat.card (((R891Z L S).subgroupOf (R891Y (R891H L S) (R891Z L S) Ys)).map q) ∣
        Nat.card ((R891Z L S).subgroupOf (R891Y (R891H L S) (R891Z L S) Ys)) :=
    Subgroup.card_map_dvd _ q
  have hmap_card_ne_one :
      Nat.card (((R891Z L S).subgroupOf (R891Y (R891H L S) (R891Z L S) Ys)).map q) ≠ 1 := by
    intro h1
    have hbot : ((R891Z L S).subgroupOf (R891Y (R891H L S) (R891Z L S) Ys)).map q = ⊥ :=
      Subgroup.eq_bot_of_card_eq (H := ((R891Z L S).subgroupOf
        (R891Y (R891H L S) (R891Z L S) Ys)).map q) h1
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
    have h3 : 3 ∣ Nat.card ↥(CFSG.pPrimeCore 3 ↥(R891Y (R891H L S) (R891Z L S) Ys)) := by
      have h3' : Nat.card ((R891Z L S).subgroupOf (R891Y (R891H L S) (R891Z L S) Ys)) ∣
          Nat.card ↥(CFSG.pPrimeCore 3 ↥(R891Y (R891H L S) (R891Z L S) Ys)) :=
        Subgroup.card_dvd_of_le hbot
      rwa [hZi_card] at h3'
    exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥(R891Y (R891H L S) (R891Z L S) Ys)))) h3
  have hmap_card :
      Nat.card (((R891Z L S).subgroupOf (R891Y (R891H L S) (R891Z L S) Ys)).map q) = 3 := by
    have hdvd :
        Nat.card (((R891Z L S).subgroupOf (R891Y (R891H L S) (R891Z L S) Ys)).map q) ∣ 3 := by
      rwa [hZi_card] at hmap_card_dvd
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd h hmap_card_ne_one
    · exact h
  have hcQ3 : Nat.card (Subgroup.center (R891Ybar (R891H L S) (R891Z L S) Ys)) = 3 :=
    k891list897_list896_center_card h896
  exact (Subgroup.eq_of_le_of_card_ge hmap_le (by rw [hmap_card, hcQ3])).symm

private theorem k891list897_Z_subgroupOf_le_fY_ker {G : Type} [Group G] [Finite G]
    (L S : Subgroup G) (Ys : Subgroup (R891Star (R891H L S) (R891Z L S)))
    (hYs : CFSG.Open.IsQuasisimple ↥Ys) :
    (R891Z L S).subgroupOf (R891Y (R891H L S) (R891Z L S) Ys) ≤
      (k891list897_fY L S Ys hYs).ker := by
  intro z hz
  rw [MonoidHom.mem_ker]
  apply Subtype.ext
  change (QuotientGroup.mk' (R891Ker (R891H L S) (R891Z L S)))
      (k891list897_iota L S Ys z) = 1
  refine (QuotientGroup.eq_one_iff (N := R891Ker (R891H L S) (R891Z L S))
    (k891list897_iota L S Ys z)).mpr ?_
  exact Subgroup.subset_normalClosure
    (Or.inr (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hz)))

private theorem k891list897_center_le_fbar_ker {G : Type} [Group G] [Finite G]
    (D : Data G) (L S R A : Subgroup G) (n : ℕ) (hst : R891State D L S R A n)
    (Ys : Subgroup (R891Star (R891H L S) (R891Z L S))) (hY : R891YSet D L S n R Ys)
    (h896 : R891List896 (R891Ybar (R891H L S) (R891Z L S) Ys)) :
    Subgroup.center (R891Ybar (R891H L S) (R891Z L S) Ys) ≤ (k891list897_fbar hY).ker := by
  rw [k891list897_center_eq_map_Z D L S R A n hst Ys hY h896]
  intro z hz
  rw [Subgroup.mem_map] at hz
  obtain ⟨w, hw, hwz⟩ := hz
  rw [← hwz]
  refine MonoidHom.mem_ker.mpr ?_
  rw [show k891list897_fbar hY
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(R891Y (R891H L S) (R891Z L S) Ys)) w) =
      k891list897_fY L S Ys hY.comp.2.2 w from
    QuotientGroup.lift_mk' _ (φ := k891list897_fY L S Ys hY.comp.2.2) _ w]
  exact MonoidHom.mem_ker.mp (k891list897_Z_subgroupOf_le_fY_ker L S Ys hY.comp.2.2 hw)

private theorem k891list897_fbar_ker_le_center {G : Type} [Group G] [Finite G]
    {D : Data G} {L S R : Subgroup G} {n : ℕ}
    {Ys : Subgroup (R891Star (R891H L S) (R891Z L S))} (hY : R891YSet D L S n R Ys) :
    (k891list897_fbar hY).ker ≤
      Subgroup.center (R891Ybar (R891H L S) (R891Z L S) Ys) :=
  k891list897_kernel_center_of_commutator_le
    (CFSG.pPrimeCore 3 ↥(R891Y (R891H L S) (R891Z L S) Ys))
    (k891list897_fY L S Ys hY.comp.2.2)
    (k891list897_O_le_fY_ker L S Ys hY.comp.2.2
      (k891list897_Y_subnormal_H L S Ys hY.comp.2.1))
    (k891list897_comm_fY_ker_le_O L S Ys hY.comp.2.2)

private theorem k891list897_fbar_ker_eq_center {G : Type} [Group G] [Finite G]
    (D : Data G) (L S R A : Subgroup G) (n : ℕ) (hst : R891State D L S R A n)
    (Ys : Subgroup (R891Star (R891H L S) (R891Z L S))) (hY : R891YSet D L S n R Ys)
    (h896 : R891List896 (R891Ybar (R891H L S) (R891Z L S) Ys)) :
    (k891list897_fbar hY).ker =
      Subgroup.center (R891Ybar (R891H L S) (R891Z L S) Ys) :=
  le_antisymm (k891list897_fbar_ker_le_center hY)
    (k891list897_center_le_fbar_ker D L S R A n hst Ys hY h896)

private noncomputable def k891list897_e {G : Type} [Group G] [Finite G]
    (D : Data G) (L S R A : Subgroup G) (n : ℕ) (hst : R891State D L S R A n)
    (Ys : Subgroup (R891Star (R891H L S) (R891Z L S))) (hY : R891YSet D L S n R Ys)
    (h896 : R891List896 (R891Ybar (R891H L S) (R891Z L S) Ys)) :
    (R891Ybar (R891H L S) (R891Z L S) Ys ⧸
        Subgroup.center (R891Ybar (R891H L S) (R891Z L S) Ys)) ≃* ↥Ys :=
  MulEquiv.ofBijective
    (QuotientGroup.lift (Subgroup.center (R891Ybar (R891H L S) (R891Z L S) Ys))
      (k891list897_fbar hY)
      (le_of_eq (k891list897_fbar_ker_eq_center D L S R A n hst Ys hY h896).symm))
    (by
      refine ⟨?_, ?_⟩
      · intro a b hab
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
          (Subgroup.center (R891Ybar (R891H L S) (R891Z L S) Ys)) a
        obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective
          (Subgroup.center (R891Ybar (R891H L S) (R891Z L S) Ys)) b
        simp only [QuotientGroup.mk'_apply, QuotientGroup.lift_mk'] at hab
        simp only [QuotientGroup.mk'_apply]
        rw [QuotientGroup.eq_iff_div_mem]
        have h1 : x / y ∈ (k891list897_fbar hY).ker := by
          rw [MonoidHom.mem_ker, map_div, hab]
          simp
        rwa [k891list897_fbar_ker_eq_center D L S R A n hst Ys hY h896] at h1
      · intro y
        obtain ⟨x, hx⟩ := k891list897_fbar_surjective hY y
        exact ⟨QuotientGroup.mk' (Subgroup.center (R891Ybar (R891H L S) (R891Z L S) Ys)) x,
          by rw [QuotientGroup.mk'_apply, QuotientGroup.lift_mk']; exact hx⟩)

private theorem k891list897_e_mk {G : Type} [Group G] [Finite G]
    (D : Data G) (L S R A : Subgroup G) (n : ℕ) (hst : R891State D L S R A n)
    (Ys : Subgroup (R891Star (R891H L S) (R891Z L S))) (hY : R891YSet D L S n R Ys)
    (h896 : R891List896 (R891Ybar (R891H L S) (R891Z L S) Ys))
    (x : R891Ybar (R891H L S) (R891Z L S) Ys) :
    k891list897_e D L S R A n hst Ys hY h896
        (QuotientGroup.mk' (Subgroup.center (R891Ybar (R891H L S) (R891Z L S) Ys)) x) =
      k891list897_fbar hY x := by
  change (QuotientGroup.lift (Subgroup.center (R891Ybar (R891H L S) (R891Z L S) Ys))
      (k891list897_fbar hY)
      (le_of_eq (k891list897_fbar_ker_eq_center D L S R A n hst Ys hY h896).symm))
      (QuotientGroup.mk' (Subgroup.center (R891Ybar (R891H L S) (R891Z L S) Ys)) x) =
    k891list897_fbar hY x
  rw [QuotientGroup.mk'_apply, QuotientGroup.lift_mk']

private noncomputable def k891list897_Rbar {G : Type} [Group G] [Finite G]
    (L S R : Subgroup G) (Ys : Subgroup (R891Star (R891H L S) (R891Z L S))) :
    Subgroup (R891Ybar (R891H L S) (R891Z L S) Ys) :=
  (R.subgroupOf (R891Y (R891H L S) (R891Z L S) Ys)).map
    (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(R891Y (R891H L S) (R891Z L S) Ys)))

private theorem k891list897_Rbar_extra {G : Type} [Group G] [Finite G] (D : Data G)
    (L S R A : Subgroup G) (n : ℕ) (hst : R891State D L S R A n)
    (Ys : Subgroup (R891Star (R891H L S) (R891Z L S))) (hY : R891YSet D L S n R Ys) :
    IsExtraspecialExpP 3 1 ↥(k891list897_Rbar L S R Ys) := by
  have hRY : R ≤ R891Y (R891H L S) (R891Z L S) Ys := hY.rLe
  have hRS : R ≤ S := hst.ctx.xShape.rSylow.trans inf_le_left
  have hR3 : IsPGroup 3 ↥R := (hst.set.sylow.isPGroup).to_le hRS
  have hRp : IsPGroup 3 ↥(R.subgroupOf (R891Y (R891H L S) (R891Z L S) Ys)) := by
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hR3
    exact (IsPGroup.iff_card).mpr ⟨m, by
      rw [CFSG.natCard_subgroupOf_eq R (R891Y (R891H L S) (R891Z L S) Ys) hRY, hm]⟩
  have hRO : R.subgroupOf (R891Y (R891H L S) (R891Z L S) Ys) ⊓
      CFSG.pPrimeCore 3 ↥(R891Y (R891H L S) (R891Z L S) Ys) = ⊥ := by
    apply Subgroup.inf_eq_bot_of_coprime
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hRp
    rw [hm]
    exact (CFSG.pPrimeCore_coprime_card (p := 3)
      (G := ↥(R891Y (R891H L S) (R891Z L S) Ys))).pow_left m
  let f : ↥(R.subgroupOf (R891Y (R891H L S) (R891Z L S) Ys)) →*
      ↥(k891list897_Rbar L S R Ys) :=
    { toFun := fun x =>
        ⟨(QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(R891Y (R891H L S) (R891Z L S) Ys))) x.1,
          Subgroup.mem_map.mpr ⟨x.1, x.2, rfl⟩⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul _ _ _) }
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      have h1 : (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(R891Y (R891H L S) (R891Z L S) Ys))) a.1 =
          (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(R891Y (R891H L S) (R891Z L S) Ys))) b.1 :=
        congrArg Subtype.val hab
      have h2 : a.1 * b.1⁻¹ ∈ R.subgroupOf (R891Y (R891H L S) (R891Z L S) Ys) ⊓
          CFSG.pPrimeCore 3 ↥(R891Y (R891H L S) (R891Z L S) Ys) := by
        refine ⟨(R.subgroupOf _).mul_mem a.2 ((R.subgroupOf _).inv_mem b.2), ?_⟩
        refine (QuotientGroup.eq_one_iff
          (N := CFSG.pPrimeCore 3 ↥(R891Y (R891H L S) (R891Z L S) Ys))
          (a.1 * b.1⁻¹)).mp ?_
        have h1' : (↑a.1 : ↥(R891Y (R891H L S) (R891Z L S) Ys) ⧸
            CFSG.pPrimeCore 3 ↥(R891Y (R891H L S) (R891Z L S) Ys)) = ↑b.1 := h1
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, h1', mul_inv_cancel]
      rw [hRO] at h2
      have h3 : a.1 = b.1 := by
        have h := Subgroup.mem_bot.mp h2
        rw [← mul_inv_eq_one]
        exact h
      exact Subtype.ext h3
    · rintro ⟨y, hy⟩
      rw [k891list897_Rbar, Subgroup.mem_map] at hy
      obtain ⟨z, hz, hzy⟩ := hy
      exact ⟨⟨z, hz⟩, Subtype.ext hzy⟩
  have eR : ↥R ≃* ↥(k891list897_Rbar L S R Ys) :=
    (Subgroup.subgroupOfEquivOfLe hRY).symm.trans (MulEquiv.ofBijective f hf)
  exact isExtraspecialExpP_of_mulEquiv eR.symm hst.ctx.xShape.rExtra

private theorem k891list897_center_le_Rbar {G : Type} [Group G] [Finite G] (D : Data G)
    (L S R A : Subgroup G) (n : ℕ) (hst : R891State D L S R A n)
    (Ys : Subgroup (R891Star (R891H L S) (R891Z L S))) (hY : R891YSet D L S n R Ys)
    (h896 : R891List896 (R891Ybar (R891H L S) (R891Z L S) Ys)) :
    Subgroup.center (R891Ybar (R891H L S) (R891Z L S) Ys) ≤ k891list897_Rbar L S R Ys := by
  rw [k891list897_center_eq_map_Z D L S R A n hst Ys hY h896]
  apply Subgroup.map_mono
  intro z hz
  exact Subgroup.mem_subgroupOf.mpr (hst.ctx.xShape.zLe (Subgroup.mem_subgroupOf.mp hz))

private theorem k891list897_Rsub_map_iota {G : Type} [Group G] [Finite G]
    (L S R : Subgroup G) (Ys : Subgroup (R891Star (R891H L S) (R891Z L S)))
    (hRY : R ≤ R891Y (R891H L S) (R891Z L S) Ys) :
    (R.subgroupOf (R891Y (R891H L S) (R891Z L S) Ys)).map (k891list897_iota L S Ys) =
      R.subgroupOf (R891H L S) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hy)
  · intro hx
    exact ⟨⟨x.1, hRY (Subgroup.mem_subgroupOf.mp hx)⟩,
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hx), Subtype.ext rfl⟩

private theorem k891list897_fY_R_eq {G : Type} [Group G] [Finite G]
    (L S R : Subgroup G) (Ys : Subgroup (R891Star (R891H L S) (R891Z L S)))
    (hYs : CFSG.Open.IsQuasisimple ↥Ys)
    (hRY : R ≤ R891Y (R891H L S) (R891Z L S) Ys) :
    (R.subgroupOf (R891Y (R891H L S) (R891Z L S) Ys)).map (k891list897_fY L S Ys hYs) =
      (R891Img (R891H L S) (R891Z L S) R).subgroupOf Ys := by
  have hRstar_le_Ys : R891Img (R891H L S) (R891Z L S) R ≤ Ys := by
    rw [R891Img, ← k891list897_Y_map_mk_eq L S Ys hYs]
    exact Subgroup.map_mono (fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hRY (Subgroup.mem_subgroupOf.mp hx)))
  apply Subgroup.map_injective (f := Ys.subtype) Ys.subtype_injective
  rw [Subgroup.map_map]
  have hcomp : Ys.subtype.comp (k891list897_fY L S Ys hYs) =
      (QuotientGroup.mk' (R891Ker (R891H L S) (R891Z L S))).comp
        (k891list897_iota L S Ys) := by
    ext x
    rfl
  rw [hcomp, ← Subgroup.map_map, k891list897_Rsub_map_iota L S R Ys hRY]
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hRstar_le_Ys]
  rfl

private theorem k891list897_e_Rbar {G : Type} [Group G] [Finite G] (D : Data G)
    (L S R A : Subgroup G) (n : ℕ) (hst : R891State D L S R A n)
    (Ys : Subgroup (R891Star (R891H L S) (R891Z L S))) (hY : R891YSet D L S n R Ys)
    (h896 : R891List896 (R891Ybar (R891H L S) (R891Z L S) Ys)) :
    ((k891list897_Rbar L S R Ys).map
        (QuotientGroup.mk' (Subgroup.center (R891Ybar (R891H L S) (R891Z L S) Ys)))).map
        (k891list897_e D L S R A n hst Ys hY h896).toMonoidHom =
      (R891Img (R891H L S) (R891Z L S) R).subgroupOf Ys := by
  have hRY : R ≤ R891Y (R891H L S) (R891Z L S) Ys := hY.rLe
  have he : (k891list897_e D L S R A n hst Ys hY h896).toMonoidHom.comp
      (QuotientGroup.mk' (Subgroup.center (R891Ybar (R891H L S) (R891Z L S) Ys))) =
      k891list897_fbar hY :=
    MonoidHom.ext fun x => k891list897_e_mk D L S R A n hst Ys hY h896 x
  have hf : (k891list897_fbar hY).comp
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(R891Y (R891H L S) (R891Z L S) Ys))) =
      k891list897_fY L S Ys hY.comp.2.2 :=
    MonoidHom.ext fun x => rfl
  rw [k891list897_Rbar, Subgroup.map_map, he, Subgroup.map_map, hf]
  exact k891list897_fY_R_eq L S R Ys hY.comp.2.2 hRY

private theorem k891list897_Ker_le_M {G : Type} [Group G] [Finite G] (D : Data G)
    (L S R A : Subgroup G) (n : ℕ) (hst : R891State D L S R A n)
    (h895 : R891Facts895 D L S n R) :
    R891Ker (R891H L S) (R891Z L S) ≤ D.M.subgroupOf (R891H L S) := by
  have hRleM : R ≤ D.M := (hst.ctx.xShape.rSylow.trans inf_le_left).trans
    (CFSG.ABGLocalTools.IsSylowOf.le hst.set.sylow)
  rw [k891list897_Ker_eq_sup L S]
  apply sup_le
  · intro v hv
    rw [Subgroup.mem_subgroupOf]
    exact h895.gammaO3.2.2 (Subgroup.mem_map_of_mem (R891H L S).subtype hv)
  · intro z hz
    rw [Subgroup.mem_subgroupOf]
    exact hRleM (hst.ctx.xShape.zLe (Subgroup.mem_subgroupOf.mp hz))

private theorem k891list897_inf_eq {G : Type} [Group G] [Finite G] (D : Data G)
    (L S R A : Subgroup G) (n : ℕ) (hst : R891State D L S R A n)
    (Ys : Subgroup (R891Star (R891H L S) (R891Z L S))) (hY : R891YSet D L S n R Ys)
    (h895 : R891Facts895 D L S n R) :
    R891Img (R891H L S) (R891Z L S) D.M ⊓ Ys =
      R891Img (R891H L S) (R891Z L S) (D.M ⊓ R891Y (R891H L S) (R891Z L S) Ys) := by
  have hKer_le := k891list897_Ker_le_M D L S R A n hst h895
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxM, hxY⟩ := hx
    rw [R891Img, Subgroup.mem_map] at hxM
    obtain ⟨m, hm, hxm⟩ := hxM
    have hxY' : x ∈ R891Img (R891H L S) (R891Z L S)
        (R891Y (R891H L S) (R891Z L S) Ys) := by
      rw [R891Img, k891list897_Y_map_mk_eq L S Ys hY.comp.2.2]
      exact hxY
    rw [R891Img, Subgroup.mem_map] at hxY'
    obtain ⟨y, hy, hxy⟩ := hxY'
    have hmk : (QuotientGroup.mk' (R891Ker (R891H L S) (R891Z L S))) m =
        (QuotientGroup.mk' (R891Ker (R891H L S) (R891Z L S))) y :=
      hxm.trans hxy.symm
    have hmk' : (↑m : ↥(R891H L S) ⧸ R891Ker (R891H L S) (R891Z L S)) = ↑y :=
      hmk
    have hker : m * y⁻¹ ∈ R891Ker (R891H L S) (R891Z L S) := by
      refine (QuotientGroup.eq_one_iff (N := R891Ker (R891H L S) (R891Z L S))
        (m * y⁻¹)).mp ?_
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hmk', mul_inv_cancel]
    have hk_sub : m * y⁻¹ ∈ D.M.subgroupOf (R891H L S) := hKer_le hker
    have hy_sub : y ∈ D.M.subgroupOf (R891H L S) := by
      have hyk : y = (m * y⁻¹)⁻¹ * m := by group
      rw [hyk]
      exact (D.M.subgroupOf (R891H L S)).mul_mem
        ((D.M.subgroupOf (R891H L S)).inv_mem hk_sub) hm
    have hyM : (y : G) ∈ D.M := Subgroup.mem_subgroupOf.mp hy_sub
    rw [R891Img, Subgroup.mem_map]
    exact ⟨y, Subgroup.mem_subgroupOf.mpr
      ⟨hyM, Subgroup.mem_subgroupOf.mp hy⟩, hxy⟩
  · intro x hx
    rw [R891Img, Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [Subgroup.mem_inf]
    refine ⟨?_, ?_⟩
    · rw [R891Img]
      exact Subgroup.mem_map.mpr
        ⟨y, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hy).1, rfl⟩
    · rw [← k891list897_Y_map_mk_eq L S Ys hY.comp.2.2]
      exact Subgroup.mem_map.mpr
        ⟨y, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hy).2, rfl⟩

private theorem k891list897_MY_le_Ys {G : Type} [Group G] [Finite G]
    (D : Data G) (L S : Subgroup G) (Ys : Subgroup (R891Star (R891H L S) (R891Z L S)))
    (hYs : CFSG.Open.IsQuasisimple ↥Ys) :
    R891Img (R891H L S) (R891Z L S) (D.M ⊓ R891Y (R891H L S) (R891Z L S) Ys) ≤ Ys := by
  have h : ((D.M ⊓ R891Y (R891H L S) (R891Z L S) Ys).subgroupOf (R891H L S)).map
      (QuotientGroup.mk' (R891Ker (R891H L S) (R891Z L S))) ≤
      ((R891Y (R891H L S) (R891Z L S) Ys).subgroupOf (R891H L S)).map
      (QuotientGroup.mk' (R891Ker (R891H L S) (R891Z L S))) :=
    Subgroup.map_mono (f := QuotientGroup.mk' (R891Ker (R891H L S) (R891Z L S)))
      (fun x hx => Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)).2)
  rw [k891list897_Y_map_mk_eq L S Ys hYs] at h
  exact h

private theorem k891list897_MY_sub_ne_top {G : Type} [Group G] [Finite G] (D : Data G)
    (L S R A : Subgroup G) (n : ℕ) (hst : R891State D L S R A n)
    (Ys : Subgroup (R891Star (R891H L S) (R891Z L S))) (hY : R891YSet D L S n R Ys)
    (h895 : R891Facts895 D L S n R) :
    ((R891Img (R891H L S) (R891Z L S)
        (D.M ⊓ R891Y (R891H L S) (R891Z L S) Ys)).subgroupOf Ys) ≠ ⊤ := by
  have hKer_le := k891list897_Ker_le_M D L S R A n hst h895
  have hMYle := k891list897_MY_le_Ys D L S Ys hY.comp.2.2
  intro htop
  have hMY_eq : R891Img (R891H L S) (R891Z L S)
      (D.M ⊓ R891Y (R891H L S) (R891Z L S) Ys) = Ys := by
    have h2 := congrArg (fun K : Subgroup ↥Ys => K.map Ys.subtype) htop
    rw [Subgroup.subgroupOf_map_subtype, Subgroup.map_top, Subgroup.range_subtype] at h2
    rwa [inf_eq_left.mpr hMYle] at h2
  apply hY.notM
  intro y hy
  have hyH : y ∈ R891H L S := k891list897_Y_le_H L S Ys hy
  have hmy : (QuotientGroup.mk' (R891Ker (R891H L S) (R891Z L S)))
        (⟨y, hyH⟩ : ↥(R891H L S)) ∈
      R891Img (R891H L S) (R891Z L S) (D.M ⊓ R891Y (R891H L S) (R891Z L S) Ys) := by
    rw [hMY_eq, ← k891list897_Y_map_mk_eq L S Ys hY.comp.2.2]
    exact Subgroup.mem_map.mpr ⟨⟨y, hyH⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
  rw [R891Img, Subgroup.mem_map] at hmy
  obtain ⟨m, hm, hmem⟩ := hmy
  have hdiv : m / (⟨y, hyH⟩ : ↥(R891H L S)) ∈ R891Ker (R891H L S) (R891Z L S) :=
    QuotientGroup.eq_iff_div_mem.mp hmem
  have hdivM : m / (⟨y, hyH⟩ : ↥(R891H L S)) ∈ D.M.subgroupOf (R891H L S) := hKer_le hdiv
  have hy_sub : (⟨y, hyH⟩ : ↥(R891H L S)) ∈ D.M.subgroupOf (R891H L S) := by
    have hyk : (⟨y, hyH⟩ : ↥(R891H L S)) =
        (m / (⟨y, hyH⟩ : ↥(R891H L S)))⁻¹ * m := by
      rw [div_eq_mul_inv]
      group
    rw [hyk]
    exact (D.M.subgroupOf (R891H L S)).mul_mem
      ((D.M.subgroupOf (R891H L S)).inv_mem hdivM)
      (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hm).1)
  exact Subgroup.mem_subgroupOf.mp hy_sub

private theorem k891list897_Rstar_le_Ys {G : Type} [Group G] [Finite G]
    (L S R : Subgroup G) (Ys : Subgroup (R891Star (R891H L S) (R891Z L S)))
    (hYs : CFSG.Open.IsQuasisimple ↥Ys)
    (hRY : R ≤ R891Y (R891H L S) (R891Z L S) Ys) :
    R891Img (R891H L S) (R891Z L S) R ≤ Ys := by
  rw [R891Img, ← k891list897_Y_map_mk_eq L S Ys hYs]
  exact Subgroup.map_mono (fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hRY (Subgroup.mem_subgroupOf.mp hx)))

private theorem k891list897_map_normalizer_le {X Y : Type} [Group X] [Group Y]
    (f : X →* Y) (A : Subgroup X) :
    (Subgroup.normalizer A).map f ≤ Subgroup.normalizer ((A.map f : Subgroup Y) : Set Y) := by
  rintro _ ⟨x, hx, rfl⟩
  have hx' : ∀ h, h ∈ A ↔ x * h * x⁻¹ ∈ A := (Subgroup.mem_normalizer_iff).mp hx
  refine (Subgroup.mem_normalizer_iff).mpr ?_
  intro y
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa only [map_mul, map_inv] using Subgroup.mem_map_of_mem f ((hx' a).mp ha)
  · rintro ⟨b, hb, hb_eq⟩
    refine ⟨x⁻¹ * b * x, ?_, ?_⟩
    · exact (hx' (x⁻¹ * b * x)).mpr (by
        have h : x * (x⁻¹ * b * x) * x⁻¹ = b := by group
        rw [h]; exact hb)
    · rw [show f (x⁻¹ * b * x) = (f x)⁻¹ * f b * f x by simp only [map_mul, map_inv],
        hb_eq]
      group

private theorem k891list897_gamma_e_le {G : Type} [Group G] [Finite G] (D : Data G)
    (L S R A : Subgroup G) (n : ℕ) (hst : R891State D L S R A n)
    (h895 : R891Facts895 D L S n R)
    (Ys : Subgroup (R891Star (R891H L S) (R891Z L S))) (hY : R891YSet D L S n R Ys)
    (h896 : R891List896 (R891Ybar (R891H L S) (R891Z L S) Ys)) :
    (rankThreeGamma 1 3 ((k891list897_Rbar L S R Ys).map
        (QuotientGroup.mk' (Subgroup.center (R891Ybar (R891H L S) (R891Z L S) Ys))))).map
        (k891list897_e D L S R A n hst Ys hY h896).toMonoidHom ≤
      ((R891Img (R891H L S) (R891Z L S)
        (D.M ⊓ R891Y (R891H L S) (R891Z L S) Ys)).subgroupOf Ys) := by
  have hRY : R ≤ R891Y (R891H L S) (R891Z L S) Ys := hY.rLe
  have hRstar_le_Ys := k891list897_Rstar_le_Ys L S R Ys hY.comp.2.2 hRY
  have hstep : (rankThreeGamma 1 3 ((k891list897_Rbar L S R Ys).map
        (QuotientGroup.mk' (Subgroup.center (R891Ybar (R891H L S) (R891Z L S) Ys))))).map
        (k891list897_e D L S R A n hst Ys hY h896).toMonoidHom =
      rankThreeGamma 1 3 ((R891Img (R891H L S) (R891Z L S) R).subgroupOf Ys) := by
    change (GLBCore 3 1 ((k891list897_Rbar L S R Ys).map
        (QuotientGroup.mk' (Subgroup.center (R891Ybar (R891H L S) (R891Z L S) Ys))))).map
        (k891list897_e D L S R A n hst Ys hY h896).toMonoidHom =
      GLBCore 3 1 ((R891Img (R891H L S) (R891Z L S) R).subgroupOf Ys)
    rw [← CFSG.AGLEmbedding.Norton.OrdinaryProofs.GLBCore_map_equiv
      (k891list897_e D L S R A n hst Ys hY h896)
      ((k891list897_Rbar L S R Ys).map
        (QuotientGroup.mk' (Subgroup.center (R891Ybar (R891H L S) (R891Z L S) Ys))))]
    rw [k891list897_e_Rbar D L S R A n hst Ys hY h896]
  rw [hstep]
  apply CFSG.HardMathSupport.Solomon.Proving.GLBCore_le_of_forall
  intro Q hQ hQrank x hx
  have hxN : x.1 ∈ Subgroup.normalizer ((Q.map Ys.subtype :
      Subgroup (R891Star (R891H L S) (R891Z L S))) : Set (R891Star (R891H L S) (R891Z L S))) :=
    k891list897_map_normalizer_le Ys.subtype Q ⟨x, hx, rfl⟩
  have hQle : Q.map Ys.subtype ≤ R891Img (R891H L S) (R891Z L S) R := by
    calc Q.map Ys.subtype
        ≤ ((R891Img (R891H L S) (R891Z L S) R).subgroupOf Ys).map Ys.subtype :=
          Subgroup.map_mono hQ
      _ = R891Img (R891H L S) (R891Z L S) R ⊓ Ys :=
          Subgroup.subgroupOf_map_subtype (R891Img (R891H L S) (R891Z L S) R) Ys
      _ = R891Img (R891H L S) (R891Z L S) R := inf_eq_left.mpr hRstar_le_Ys
  have hk : 1 ≤ CFSG.Open.pRank 3 (Q.map Ys.subtype) := by
    rw [CFSG.HardMathSupport.Malle.OvergroupTransport.pRank_map_of_injective 3
      Ys.subtype_injective Q]
    exact hQrank
  have hleΓ : Subgroup.normalizer ((Q.map Ys.subtype :
      Subgroup (R891Star (R891H L S) (R891Z L S))) : Set (R891Star (R891H L S) (R891Z L S))) ≤
      rankThreeGamma 1 3 (R891Img (R891H L S) (R891Z L S) R) :=
    CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore hQle hk
  have hxM : x.1 ∈ R891Img (R891H L S) (R891Z L S) D.M := h895.gammaO3.1 (hleΓ hxN)
  have hxInf : x.1 ∈ R891Img (R891H L S) (R891Z L S) D.M ⊓ Ys := ⟨hxM, x.2⟩
  rw [k891list897_inf_eq D L S R A n hst Ys hY h895] at hxInf
  exact Subgroup.mem_subgroupOf.mpr hxInf

private theorem k891list897_gamma_ne_top {G : Type} [Group G] [Finite G] (D : Data G)
    (L S R A : Subgroup G) (n : ℕ)
    (hst : R891State D L S R A n) (h895 : R891Facts895 D L S n R)
    (Ys : Subgroup (R891Star (R891H L S) (R891Z L S))) (hY : R891YSet D L S n R Ys)
    (h896 : R891List896 (R891Ybar (R891H L S) (R891Z L S) Ys)) :
    rankThreeGamma 1 3 ((k891list897_Rbar L S R Ys).map
      (QuotientGroup.mk' (Subgroup.center (R891Ybar (R891H L S) (R891Z L S) Ys)))) ≠ ⊤ := by
  have hgamma_le_K' := k891list897_gamma_e_le D L S R A n hst h895 Ys hY h896
  have hK'_ne_top := k891list897_MY_sub_ne_top D L S R A n hst Ys hY h895
  intro htop
  apply hK'_ne_top
  have hmap : (rankThreeGamma 1 3 ((k891list897_Rbar L S R Ys).map
      (QuotientGroup.mk' (Subgroup.center (R891Ybar (R891H L S) (R891Z L S) Ys))))).map
      (k891list897_e D L S R A n hst Ys hY h896).toMonoidHom = ⊤ := by
    rw [htop, Subgroup.map_top]
    exact MonoidHom.range_eq_top.mpr
      (k891list897_e D L S R A n hst Ys hY h896).surjective
  exact le_antisymm le_top (hmap ▸ hgamma_le_K')

theorem s891_list897_of_list {G : Type} [Group G] [Finite G] (D : Data G)
    (hList : ∀ (Y : Type) [Group Y] [Finite Y], R891List896 Y → ∀ R : Subgroup Y,
      IsExtraspecialExpP 3 1 ↥R → center Y ≤ R →
      rankThreeGamma 1 3 (R.map (QuotientGroup.mk' (center Y))) ≠ ⊤ → R891List897 Y)
    (L S R A : Subgroup G) (n : ℕ)
    (hst : R891State D L S R A n) (h895 : R891Facts895 D L S n R)
    (Ys : Subgroup (R891Star (R891H L S) (R891Z L S))) (hY : R891YSet D L S n R Ys)
    (h896 : R891List896 (R891Ybar (R891H L S) (R891Z L S) Ys)) :
    R891List897 (R891Ybar (R891H L S) (R891Z L S) Ys) :=
  hList _ h896 (k891list897_Rbar L S R Ys) (k891list897_Rbar_extra D L S R A n hst Ys hY)
    (k891list897_center_le_Rbar D L S R A n hst Ys hY h896)
    (k891list897_gamma_ne_top D L S R A n hst h895 Ys hY h896)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
