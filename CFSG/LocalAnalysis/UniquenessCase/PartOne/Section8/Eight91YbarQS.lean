module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91Defs
import CFSG.GH74.GLS.AssemblyComponents

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.LocalAnalysis.UniquenessCase.UC22.F08
open scoped commutatorElement

private theorem k891ybarqs_nonabelian_of_open_quasisimple {Q : Type} [Group Q]
    (h : CFSG.Open.IsQuasisimple Q) : ∃ a b : Q ⧸ Subgroup.center Q, a * b ≠ b * a := by
  let : Group.IsPerfect Q := ⟨h.1⟩
  let : IsSimpleGroup (Q ⧸ Subgroup.center Q) := h.2
  have hnoncomm := Group.IsPerfect.not_isMulCommutative (Q ⧸ Subgroup.center Q)
  simpa only [isMulCommutative_iff, not_forall] using hnoncomm

private theorem k891ybarqs_native_of_open {Q : Type} [Group Q]
    (h : CFSG.Open.IsQuasisimple Q) : CFSG.IsQuasisimple Q :=
  ⟨⟨h.1⟩, h.2, k891ybarqs_nonabelian_of_open_quasisimple h⟩

private theorem k891ybarqs_isPGroup_center_of_pPrimeCore_eq_bot {X : Type} [Group X] [Finite X]
    (p : ℕ) [Fact p.Prime] (hO : CFSG.pPrimeCore p X = ⊥) : IsPGroup p (center X) := by
  intro z
  obtain ⟨k, m, hm, hzm⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos z).ne' p (Fact.out : Nat.Prime p).ne_one
  refine ⟨k, ?_⟩
  set w : center X := z ^ p ^ k with hw
  have hwo : orderOf w = m := by
    rw [hw, orderOf_pow_of_dvd (by exact pow_ne_zero k (Fact.out : Nat.Prime p).pos.ne')
      (by rw [hzm]; exact dvd_mul_right _ _), hzm,
      Nat.mul_div_cancel_left _ (by exact pow_pos (Fact.out : Nat.Prime p).pos k)]
  have hcop : Nat.Coprime p (Nat.card (Subgroup.zpowers (w : X))) := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hwo, Nat.Prime.coprime_iff_not_dvd Fact.out]
    exact hm
  have hwN : (Subgroup.zpowers (w : X)).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr w.2)
  have hle : Subgroup.zpowers (w : X) ≤ CFSG.pPrimeCore p X := le_sSup ⟨hwN, hcop⟩
  rw [hO] at hle
  have h1 : (w : X) = 1 := by
    have hmem : (w : X) ∈ Subgroup.zpowers (w : X) := Subgroup.mem_zpowers (w : X)
    simpa using hle hmem
  exact Subtype.ext h1

private theorem k891ybarqs_kernel_center_of_commutator_le {X Y : Type} [Group X] [Group Y]
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

private theorem k891ybarqs_derInf8_le {G : Type} [Group G] [Finite G] (X : Subgroup G) :
    DerInf8 X ≤ X := by
  rw [show DerInf8 X = (CFSG.perfectResidual ↥X).map X.subtype from rfl]
  exact Subgroup.map_subtype_le _

private theorem k891ybarqs_derInf8_perfect {G : Type} [Group G] [Finite G] (X : Subgroup G) :
    Group.IsPerfect ↥(DerInf8 X) := by
  have hperf : Group.IsPerfect ↥(CFSG.perfectResidual ↥X) :=
    (CFSG.perfect_residual_characterization (G := ↥X)).2.2.1
  have := hperf
  rw [show DerInf8 X = (CFSG.perfectResidual ↥X).map X.subtype from rfl]
  exact Group.IsPerfect.map X.subtype

private theorem k891ybarqs_Z_card {G : Type} [Group G] [Finite G] (D : Data G)
    (L S : Subgroup G) (hbasic : R891Basic D L S) : Nat.card (R891Z L S) = 3 :=
  hbasic.zOrder

private theorem k891ybarqs_Z_ne_bot {G : Type} [Group G] [Finite G] (D : Data G)
    (L S : Subgroup G) (hbasic : R891Basic D L S) : R891Z L S ≠ ⊥ := by
  intro hbot
  have h1 : Nat.card (R891Z L S) = 1 := by rw [hbot]; exact Subgroup.card_bot
  have h3 := k891ybarqs_Z_card D L S hbasic
  omega

private theorem k891ybarqs_Z_le_center_H {G : Type} [Group G] [Finite G] (L S : Subgroup G) :
    (R891Z L S).subgroupOf (R891H L S) ≤ center ↥(R891H L S) := by
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro h
  apply Subtype.ext
  exact (Subgroup.mem_centralizer_iff.mp h.2 z.1 hz).symm

private theorem k891ybarqs_H_ne_top {G : Type} [Group G] [Finite G] (D : Data G)
    (L S : Subgroup G) (hbasic : R891Basic D L S) : R891H L S ≠ ⊤ := by
  intro hH
  have hZcenter : R891Z L S ≤ center G := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ R891H L S := by rw [hH]; exact Subgroup.mem_top g
    exact (Subgroup.mem_centralizer_iff.mp hg z hz).symm
  have hcenter : center G = ⊥ := by
    have : IsSimpleGroup G := D.standing.simple
    exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup D.standing.nonab).2
  refine k891ybarqs_Z_ne_bot D L S hbasic (le_bot_iff.mp (hZcenter.trans (le_of_eq hcenter)))

private def k891ybarqs_Y1 {G : Type} [Group G] [Finite G] (L S : Subgroup G)
    (Ys : Subgroup (R891Star (R891H L S) (R891Z L S))) : Subgroup G :=
  (Ys.comap (QuotientGroup.mk' (R891Ker (R891H L S) (R891Z L S)))).map (R891H L S).subtype

private theorem k891ybarqs_Y_le_H {G : Type} [Group G] [Finite G] (L S : Subgroup G)
    (Ys : Subgroup (R891Star (R891H L S) (R891Z L S))) :
    R891Y (R891H L S) (R891Z L S) Ys ≤ R891H L S :=
  (k891ybarqs_derInf8_le (k891ybarqs_Y1 L S Ys)).trans (Subgroup.map_subtype_le _)

private theorem k891ybarqs_Y_ne_top {G : Type} [Group G] [Finite G] (D : Data G)
    (L S : Subgroup G) (hbasic : R891Basic D L S)
    (Ys : Subgroup (R891Star (R891H L S) (R891Z L S))) :
    R891Y (R891H L S) (R891Z L S) Ys ≠ ⊤ := by
  intro hY
  exact k891ybarqs_H_ne_top D L S hbasic
    (top_unique (hY ▸ k891ybarqs_Y_le_H L S Ys))

private theorem k891ybarqs_perfectResidual_map_equiv {X Y : Type} [Group X] [Group Y]
    (e : X ≃* Y) : (CFSG.perfectResidual X).map e.toMonoidHom = CFSG.perfectResidual Y := by
  rw [CFSG.perfectResidual, CFSG.perfectResidual, Subgroup.map_iInf _ e.injective]
  exact iInf_congr fun n => map_derivedSeries_eq e.surjective n

private theorem k891ybarqs_derInf8_map_subtype {G : Type} [Group G] [Finite G]
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
          rw [k891ybarqs_perfectResidual_map_equiv e]
    _ = (CFSG.perfectResidual ↥P).map ((P.map H.subtype).subtype.comp e.toMonoidHom) := by
          rw [Subgroup.map_map]
    _ = (CFSG.perfectResidual ↥P).map (H.subtype.comp P.subtype) := by rw [he]
    _ = ((CFSG.perfectResidual ↥P).map P.subtype).map H.subtype := by
          rw [Subgroup.map_map]
    _ = (DerInf8 P).map H.subtype := rfl

private theorem k891ybarqs_derivedSeries_eq_top {X : Type} [Group X] (hX : Group.IsPerfect X)
    (n : ℕ) : derivedSeries X n = ⊤ := by
  induction n with
  | zero => exact derivedSeries_zero X
  | succ n ih =>
      rw [derivedSeries_succ, ih]
      exact hX.commutator_eq_top

private theorem k891ybarqs_Y_map_mk_eq {G : Type} [Group G] [Finite G] (L S : Subgroup G)
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
    rw [k891ybarqs_derInf8_map_subtype H P,
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
    exact k891ybarqs_derivedSeries_eq_top ⟨hYs.1⟩ N
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

private theorem k891ybarqs_Y_subnormal_H {G : Type} [Group G] [Finite G] (L S : Subgroup G)
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
  have hYY1 : Y ≤ Y1 := by rw [hYeq]; exact k891ybarqs_derInf8_le Y1
  have hYnorm : (Y.subgroupOf Y1).Normal := by
    have heq : Y.subgroupOf Y1 = CFSG.perfectResidual ↥Y1 := by
      change Y.comap Y1.subtype = CFSG.perfectResidual ↥Y1
      rw [show Y = (CFSG.perfectResidual ↥Y1).map Y1.subtype from rfl,
        Subgroup.comap_map_eq_self_of_injective Y1.subtype_injective]
    rw [heq]
    infer_instance
  exact CFSG.Open.IsSubnormal.step hYY1 hYnorm hY1subH

private theorem k891ybarqs_pPrimeCore_Y_map_le_H {G : Type} [Group G] [Finite G]
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
    (CFSG.Open.IsSubnormal.iff_subgroupOf (k891ybarqs_Y_le_H L S Ys)).mp hsub
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
  let e : ↥Y ≃* ↥Yh := (Subgroup.subgroupOfEquivOfLe (k891ybarqs_Y_le_H L S Ys)).symm
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

private noncomputable def k891ybarqs_iota {G : Type} [Group G] [Finite G] (L S : Subgroup G)
    (Ys : Subgroup (R891Star (R891H L S) (R891Z L S))) :
    ↥(R891Y (R891H L S) (R891Z L S) Ys) →* ↥(R891H L S) :=
  { toFun := fun y => ⟨y.1, k891ybarqs_Y_le_H L S Ys y.2⟩
    map_one' := Subtype.ext rfl
    map_mul' := fun _ _ => Subtype.ext rfl }

private theorem k891ybarqs_iota_injective {G : Type} [Group G] [Finite G] (L S : Subgroup G)
    (Ys : Subgroup (R891Star (R891H L S) (R891Z L S))) :
    Function.Injective (k891ybarqs_iota L S Ys) :=
  fun _ _ h => Subtype.ext (by
    have h' := congrArg (fun z : ↥(R891H L S) => (z : G)) h
    simpa [k891ybarqs_iota] using h')

private noncomputable def k891ybarqs_fY {G : Type} [Group G] [Finite G] (L S : Subgroup G)
    (Ys : Subgroup (R891Star (R891H L S) (R891Z L S)))
    (hYs : CFSG.Open.IsQuasisimple ↥Ys) :
    ↥(R891Y (R891H L S) (R891Z L S) Ys) →* ↥Ys :=
  { toFun := fun x =>
      ⟨(QuotientGroup.mk' (R891Ker (R891H L S) (R891Z L S)))
        (k891ybarqs_iota L S Ys x), by
        have h := k891ybarqs_Y_map_mk_eq L S Ys hYs
        have hmem : (QuotientGroup.mk' (R891Ker (R891H L S) (R891Z L S)))
            (k891ybarqs_iota L S Ys x) ∈
            ((R891Y (R891H L S) (R891Z L S) Ys).subgroupOf (R891H L S)).map
              (QuotientGroup.mk' (R891Ker (R891H L S) (R891Z L S))) :=
          Subgroup.mem_map.mpr ⟨k891ybarqs_iota L S Ys x,
            Subgroup.mem_subgroupOf.mpr x.2, rfl⟩
        rwa [h] at hmem⟩
    map_one' := Subtype.ext (by
      change (QuotientGroup.mk' (R891Ker (R891H L S) (R891Z L S)))
        (k891ybarqs_iota L S Ys 1) = 1
      rw [map_one, map_one])
    map_mul' := fun x y => Subtype.ext (by
      change (QuotientGroup.mk' (R891Ker (R891H L S) (R891Z L S)))
        (k891ybarqs_iota L S Ys (x * y)) =
          (QuotientGroup.mk' (R891Ker (R891H L S) (R891Z L S)))
            (k891ybarqs_iota L S Ys x) *
          (QuotientGroup.mk' (R891Ker (R891H L S) (R891Z L S)))
            (k891ybarqs_iota L S Ys y)
      rw [map_mul, map_mul]) }

private theorem k891ybarqs_fY_val {G : Type} [Group G] [Finite G] (L S : Subgroup G)
    (Ys : Subgroup (R891Star (R891H L S) (R891Z L S)))
    (hYs : CFSG.Open.IsQuasisimple ↥Ys)
    (x : ↥(R891Y (R891H L S) (R891Z L S) Ys)) :
    (k891ybarqs_fY L S Ys hYs x).1 =
      (QuotientGroup.mk' (R891Ker (R891H L S) (R891Z L S)))
        (k891ybarqs_iota L S Ys x) :=
  rfl

private theorem k891ybarqs_fY_surjective {G : Type} [Group G] [Finite G] (L S : Subgroup G)
    (Ys : Subgroup (R891Star (R891H L S) (R891Z L S)))
    (hYs : CFSG.Open.IsQuasisimple ↥Ys) :
    Function.Surjective (k891ybarqs_fY L S Ys hYs) := by
  rintro ⟨ys, hys⟩
  have h := k891ybarqs_Y_map_mk_eq L S Ys hYs
  have hmem : ys ∈ ((R891Y (R891H L S) (R891Z L S) Ys).subgroupOf (R891H L S)).map
      (QuotientGroup.mk' (R891Ker (R891H L S) (R891Z L S))) := by
    rw [h]; exact hys
  obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hmem
  refine ⟨⟨x.1, Subgroup.mem_subgroupOf.mp hx⟩, Subtype.ext ?_⟩
  rw [k891ybarqs_fY_val]
  rw [show k891ybarqs_iota L S Ys ⟨x.1, Subgroup.mem_subgroupOf.mp hx⟩ = x from
    Subtype.ext rfl]
  exact hxy

private theorem k891ybarqs_comm_Ker_le_OH {G : Type} [Group G] [Finite G] (L S : Subgroup G) :
    ⁅R891Ker (R891H L S) (R891Z L S), ⊤⁆ ≤ CFSG.pPrimeCore 3 ↥(R891H L S) := by
  let H := R891H L S
  let Z := R891Z L S
  let OH : Subgroup ↥H := CFSG.pPrimeCore 3 ↥H
  let Zh : Subgroup ↥H := Z.subgroupOf H
  have hOHn : OH.Normal := inferInstance
  have hZhn : Zh.Normal := Subgroup.normal_of_le_center (k891ybarqs_Z_le_center_H L S)
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
    exact Subgroup.mem_center_iff.mp (k891ybarqs_Z_le_center_H L S hz) w
  calc ⁅R891Ker H Z, (⊤ : Subgroup ↥H)⁆ ≤ ⁅OH ⊔ Zh, (⊤ : Subgroup ↥H)⁆ :=
        Subgroup.commutator_mono hKer_le le_rfl
    _ = ⁅OH, (⊤ : Subgroup ↥H)⁆ ⊔ ⁅Zh, (⊤ : Subgroup ↥H)⁆ :=
        Subgroup.commutator_sup_right OH Zh (⊤ : Subgroup ↥H)
    _ ≤ OH ⊔ ⊥ := sup_le_sup (Subgroup.commutator_le_left OH (⊤ : Subgroup ↥H))
        (le_of_eq hZh_comm)
    _ = OH := sup_bot_eq OH

private theorem k891ybarqs_O_le_fY_ker {G : Type} [Group G] [Finite G] (L S : Subgroup G)
    (Ys : Subgroup (R891Star (R891H L S) (R891Z L S)))
    (hYs : CFSG.Open.IsQuasisimple ↥Ys)
    (hsub : CFSG.Open.IsSubnormal (R891Y (R891H L S) (R891Z L S) Ys) (R891H L S)) :
    CFSG.pPrimeCore 3 ↥(R891Y (R891H L S) (R891Z L S) Ys) ≤
      (k891ybarqs_fY L S Ys hYs).ker := by
  intro y hy
  rw [MonoidHom.mem_ker]
  apply Subtype.ext
  change (QuotientGroup.mk' (R891Ker (R891H L S) (R891Z L S)))
      (k891ybarqs_iota L S Ys y) = 1
  apply (QuotientGroup.eq_one_iff _).mpr
  have hle := k891ybarqs_pPrimeCore_Y_map_le_H L S Ys hsub
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
  have : k = k891ybarqs_iota L S Ys y := Subtype.ext hky
  rwa [this] at hk

private theorem k891ybarqs_comm_fY_ker_le_O {G : Type} [Group G] [Finite G] (L S : Subgroup G)
    (Ys : Subgroup (R891Star (R891H L S) (R891Z L S)))
    (hYs : CFSG.Open.IsQuasisimple ↥Ys) :
    ⁅(k891ybarqs_fY L S Ys hYs).ker,
        (⊤ : Subgroup ↥(R891Y (R891H L S) (R891Z L S) Ys))⁆ ≤
      CFSG.pPrimeCore 3 ↥(R891Y (R891H L S) (R891Z L S) Ys) := by
  let Y : Subgroup G := R891Y (R891H L S) (R891Z L S) Ys
  let K : Subgroup ↥Y := (k891ybarqs_fY L S Ys hYs).ker
  let N : Subgroup ↥Y := ⁅K, (⊤ : Subgroup ↥Y)⁆
  have hKmap : K.map (k891ybarqs_iota L S Ys) ≤ R891Ker (R891H L S) (R891Z L S) := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
    have hk1 : k891ybarqs_fY L S Ys hYs k = 1 := MonoidHom.mem_ker.mp hk
    have h1 : (QuotientGroup.mk' (R891Ker (R891H L S) (R891Z L S)))
        (k891ybarqs_iota L S Ys k) = 1 := by
      have := congrArg Subtype.val hk1
      rwa [k891ybarqs_fY_val] at this
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hNmap : N.map (k891ybarqs_iota L S Ys) ≤ CFSG.pPrimeCore 3 ↥(R891H L S) := by
    calc N.map (k891ybarqs_iota L S Ys)
        = ⁅K.map (k891ybarqs_iota L S Ys),
            (⊤ : Subgroup ↥Y).map (k891ybarqs_iota L S Ys)⁆ :=
          Subgroup.map_commutator K (⊤ : Subgroup ↥Y) (k891ybarqs_iota L S Ys)
      _ ≤ ⁅R891Ker (R891H L S) (R891Z L S), (⊤ : Subgroup ↥(R891H L S))⁆ :=
          Subgroup.commutator_mono hKmap le_top
      _ ≤ CFSG.pPrimeCore 3 ↥(R891H L S) := k891ybarqs_comm_Ker_le_OH L S
  have hcard : Nat.card N = Nat.card (N.map (k891ybarqs_iota L S Ys)) :=
    (Subgroup.card_map_of_injective (k891ybarqs_iota_injective L S Ys)).symm
  have hcop : Nat.Coprime 3 (Nat.card N) := by
    rw [hcard]
    exact (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥(R891H L S))).coprime_dvd_right
      (Subgroup.card_dvd_of_le hNmap)
  have hNnormal : N.Normal := Subgroup.commutator_normal K (⊤ : Subgroup ↥Y)
  exact le_sSup ⟨hNnormal, hcop⟩

theorem s891_ybar_qs {G : Type} [Group G] [Finite G] (D : Data G) (L S R : Subgroup G) (n : ℕ)
    (hbasic : R891Basic D L S)
    (Ys : Subgroup (R891Star (R891H L S) (R891Z L S))) (hY : R891YSet D L S n R Ys) :
    R891YbarQS (R891H L S) (R891Z L S) Ys := by
  let H : Subgroup G := R891H L S
  let Z : Subgroup G := R891Z L S
  let Y : Subgroup G := R891Y H Z Ys
  let O : Subgroup ↥Y := CFSG.pPrimeCore 3 ↥Y
  have hYs_open : CFSG.Open.IsQuasisimple ↥Ys := hY.comp.2.2
  have hYs_native : CFSG.IsQuasisimple ↥Ys := k891ybarqs_native_of_open hYs_open
  have hsub : CFSG.Open.IsSubnormal Y H := k891ybarqs_Y_subnormal_H L S Ys hY.comp.2.1
  have hO_le : O ≤ (k891ybarqs_fY L S Ys hYs_open).ker :=
    k891ybarqs_O_le_fY_ker L S Ys hYs_open hsub
  let fbar : ↥Y ⧸ O →* ↥Ys := QuotientGroup.lift O (k891ybarqs_fY L S Ys hYs_open) hO_le
  have hfbar_surj : Function.Surjective fbar := by
    intro y
    obtain ⟨x, hx⟩ := k891ybarqs_fY_surjective L S Ys hYs_open y
    refine ⟨QuotientGroup.mk' O x, ?_⟩
    rw [show fbar (QuotientGroup.mk' O x) = k891ybarqs_fY L S Ys hYs_open x from
      QuotientGroup.lift_mk' O (φ := k891ybarqs_fY L S Ys hYs_open) hO_le x]
    exact hx
  have hperfY : Group.IsPerfect ↥Y := k891ybarqs_derInf8_perfect (k891ybarqs_Y1 L S Ys)
  have hperfYbar : Group.IsPerfect (↥Y ⧸ O) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective O)
  have hfbar_ker : fbar.ker ≤ center (↥Y ⧸ O) :=
    k891ybarqs_kernel_center_of_commutator_le O (k891ybarqs_fY L S Ys hYs_open) hO_le
      (k891ybarqs_comm_fY_ker_le_O L S Ys hYs_open)
  have hcomap := CFSG.LocalCores.comap_center_eq_of_perfect hperfYbar fbar hfbar_surj hfbar_ker
  have hc : center (↥Y ⧸ O) = ((QuotientGroup.mk' (center ↥Ys)).comp fbar).ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact hcomap.symm
  let e : ((↥Y ⧸ O) ⧸ center (↥Y ⧸ O)) ≃* (↥Ys ⧸ center ↥Ys) :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans
      (QuotientGroup.quotientKerEquivOfSurjective _
        ((QuotientGroup.mk'_surjective _).comp hfbar_surj))
  have hqbar_native : CFSG.IsQuasisimple (↥Y ⧸ O) :=
    (CFSG.LocalCores.isQuasisimple_iff_of_surjective hperfYbar fbar hfbar_surj hfbar_ker).2
      hYs_native
  have hqbar_open : CFSG.Open.IsQuasisimple (↥Y ⧸ O) :=
    ⟨hqbar_native.1.commutator_eq_top, hqbar_native.2.1⟩
  have hsimpleYs : IsSimpleGroup (↥Ys ⧸ center ↥Ys) := hYs_open.2
  have hcatYs : CFSG.Open.IsCatalogGroup (↥Ys ⧸ center ↥Ys) :=
    CFSG.KCore.KProperNonab.catalogue_of_surjective CFSG.Open.isCatalogGroup_isoInvariant
      D.standing.kProper Y (k891ybarqs_Y_ne_top D L S hbasic Ys)
      (k891ybarqs_nonabelian_of_open_quasisimple hYs_open)
      ((QuotientGroup.mk' (center ↥Ys)).comp (k891ybarqs_fY L S Ys hYs_open))
      ((QuotientGroup.mk'_surjective (center ↥Ys)).comp
        (k891ybarqs_fY_surjective L S Ys hYs_open))
  have hcat : CFSG.Open.IsCatalogGroup ((↥Y ⧸ O) ⧸ center (↥Y ⧸ O)) :=
    CFSG.Open.isCatalogGroup_isoInvariant e hcatYs
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hObar : CFSG.pPrimeCore 3 (↥Y ⧸ O) = ⊥ :=
    CFSG.pPrimeCore_quotient_eq_bot (p := 3) Nat.prime_three
  have hcenter_pgroup : IsPGroup 3 (center (↥Y ⧸ O)) :=
    k891ybarqs_isPGroup_center_of_pPrimeCore_eq_bot 3 hObar
  have hcenter_ne : center (↥Y ⧸ O) ≠ ⊥ := by
    intro hbot
    let Zh : Subgroup ↥Y := (R891Z L S).subgroupOf Y
    have hZh_center : Zh ≤ center ↥Y := by
      intro z hz
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp (k891ybarqs_Y_le_H L S Ys y.2) z.1 hz).symm
    have hmap_center : Zh.map (QuotientGroup.mk' O) ≤ center (↥Y ⧸ O) :=
      (Subgroup.map_mono hZh_center).trans
        (Subgroup.map_center_le_center (QuotientGroup.mk'_surjective O))
    have hZh_le_O : Zh ≤ O := by
      have hle : Zh.map (QuotientGroup.mk' O) = ⊥ := le_bot_iff.mp (hmap_center.trans (le_of_eq hbot))
      rw [Subgroup.map_eq_bot_iff] at hle
      rwa [QuotientGroup.ker_mk'] at hle
    have hZh_card : Nat.card Zh = 3 := by
      change Nat.card ↥((R891Z L S).subgroupOf (R891Y H Z Ys)) = 3
      have hcard := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY.zLe).toEquiv
      rw [hcard]
      exact hbasic.zOrder
    have h3 : 3 ∣ Nat.card ↥O := by
      rw [← hZh_card]
      exact Subgroup.card_dvd_of_le hZh_le_O
    exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥Y))) h3
  change CFSG.Open.IsQuasisimple (↥Y ⧸ O) ∧
    CFSG.Open.IsCatalogGroup ((↥Y ⧸ O) ⧸ center (↥Y ⧸ O)) ∧
    IsPGroup 3 (center (↥Y ⧸ O)) ∧ center (↥Y ⧸ O) ≠ ⊥
  exact ⟨hqbar_open, hcat, hcenter_pgroup, hcenter_ne⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
