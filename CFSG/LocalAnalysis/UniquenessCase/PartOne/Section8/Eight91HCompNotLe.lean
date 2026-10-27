module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)

private theorem k891hcompnotle_opp_le {G : Type} [Group G] (p : ℕ) (Y : Subgroup G) :
    Opp p Y ≤ Y := by
  unfold Opp CFSG.RankThree.PartOne.pElementSubgroup
  exact (Subgroup.closure_le Y).mpr fun x hx => hx.1

private theorem k891hcompnotle_derInf8_le {G : Type} [Group G] (Y : Subgroup G) :
    DerInf8 Y ≤ Y := by
  unfold DerInf8
  exact Subgroup.map_subtype_le _

private theorem k891hcompnotle_isPerfect_derInf8 {G : Type} [Group G] [Finite G]
    (X : Subgroup G) : Group.IsPerfect ↥(DerInf8 X) := by
  have hperf : Group.IsPerfect ↥((⨅ n : ℕ, derivedSeries ↥X n) : Subgroup ↥X) :=
    CFSG.perfect_residual_characterization.2.2.1
  unfold DerInf8
  exact Group.IsPerfect.map X.subtype

private theorem k891hcompnotle_X_perfect {G : Type} [Group G] [Finite G]
    (L : Subgroup G) (Z : Subgroup G) (n : ℕ) (hn : 2 ≤ n) :
    Group.IsPerfect ↥(R891X L Z n) := by
  unfold R891X
  rw [if_neg (by omega : n ≠ 1)]
  exact k891hcompnotle_isPerfect_derInf8 (L ⊓ Subgroup.centralizer (Z : Set G))

private theorem k891hcompnotle_X_le_H {G : Type} [Group G] [Finite G]
    (L : Subgroup G) (Z : Subgroup G) (n : ℕ) :
    R891X L Z n ≤ Subgroup.centralizer (Z : Set G) := by
  unfold R891X
  split_ifs
  · exact (k891hcompnotle_opp_le 2 _).trans inf_le_right
  · exact (k891hcompnotle_derInf8_le _).trans inf_le_right

private theorem k891hcompnotle_X_le_Y {G : Type} [Group G] [Finite G] (D : Data G)
    (L S R A : Subgroup G) (n : ℕ) (hn : 2 ≤ n) (_hst : R891State D L S R A n)
    (Ys : Subgroup (R891Star (R891H L S) (R891Z L S)))
    (hx : R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n) ≤ Ys) :
    R891X L (R891Z L S) n ≤ R891Y (R891H L S) (R891Z L S) Ys := by
  let H := R891H L S
  let Z := R891Z L S
  let X := R891X L Z n
  let Ker := R891Ker H Z
  let mk := QuotientGroup.mk' Ker
  let Y₁ := (Ys.comap mk).map H.subtype
  have hXH : X ≤ H := k891hcompnotle_X_le_H L Z n
  have hx' : X.subgroupOf H ≤ Ys.comap mk := by
    rw [← Subgroup.map_le_iff_le_comap]
    simpa only [R891Img, mk, Ker, H, Z, X] using hx
  have hXleY₁ : X ≤ Y₁ := by
    have hmono := Subgroup.map_mono (f := H.subtype) hx'
    rwa [Subgroup.map_subgroupOf_eq_of_le hXH] at hmono
  have hXperf : Group.IsPerfect ↥X := k891hcompnotle_X_perfect L Z n hn
  have hle := CFSG.RankThreeCoreUniqueness.Helpers.perfect_subgroup_le_perfectResidualOf
    X Y₁ hXperf hXleY₁
  simpa only [R891Y, DerInf8, Y₁, H, Z, X,
    CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf,
    CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual] using hle

private theorem k891hcompnotle_R_le_Y {G : Type} [Group G] [Finite G] (D : Data G)
    (L S R A : Subgroup G) (n : ℕ) (hn : 2 ≤ n) (hst : R891State D L S R A n)
    (Ys : Subgroup (R891Star (R891H L S) (R891Z L S)))
    (hx : R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n) ≤ Ys) :
    R ≤ R891Y (R891H L S) (R891Z L S) Ys :=
  hst.ctx.xShape.rLe.trans (k891hcompnotle_X_le_Y D L S R A n hn hst Ys hx)

private theorem k891hcompnotle_Z_le_Y {G : Type} [Group G] [Finite G] (D : Data G)
    (L S R A : Subgroup G) (n : ℕ) (hn : 2 ≤ n) (hst : R891State D L S R A n)
    (Ys : Subgroup (R891Star (R891H L S) (R891Z L S)))
    (hx : R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n) ≤ Ys) :
    R891Z L S ≤ R891Y (R891H L S) (R891Z L S) Ys :=
  hst.ctx.xShape.zLe.trans (k891hcompnotle_R_le_Y D L S R A n hn hst Ys hx)

private theorem k891hcompnotle_subnormal_le_M {G : Type} [Group G] [Finite G]
    {M K H : Subgroup G} (hM : rankThreeIsMaxTwoLocal M)
    (hsub : CFSG.Open.IsSubnormal H K) (hHM : H ≤ M) (hH : H ∈ uniqueSet M) : K ≤ M := by
  revert hHM hH
  induction hsub with
  | refl => exact fun hHM _ => hHM
  | @step A B C hAB hnorm hBC ih =>
    intro hHM hH
    have hNB : B ≤ Subgroup.normalizer (A : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hAB).mp hnorm
    have hBM : B ≤ M :=
      hNB.trans (CFSG.LocalAnalysis.RankThreeUC.normalizer_le_of_mem_uniqueSet hM hH)
    have hB : B ∈ uniqueSet M :=
      CFSG.LocalAnalysis.RankThreeUC.mem_uniqueSet_of_le hH hAB hBM
    exact ih hBM hB

private theorem k891hcompnotle_Y_subnormal {G : Type} [Group G] [Finite G] (D : Data G)
    (L S R A : Subgroup G) (n : ℕ) (_hst : R891State D L S R A n)
    (Ys : Subgroup (R891Star (R891H L S) (R891Z L S))) (hc : IsComponentOf Ys ⊤) :
    CFSG.Open.IsSubnormal (R891Y (R891H L S) (R891Z L S) Ys) (R891H L S) := by
  let H := R891H L S
  let Z := R891Z L S
  let Ker := R891Ker H Z
  let mk := QuotientGroup.mk' Ker
  let Y₁ := (Ys.comap mk).map H.subtype
  have hY₁sub : CFSG.Open.IsSubnormal Y₁ H := by
    have h1 : CFSG.Open.IsSubnormal (Ys.comap mk) (⊤ : Subgroup ↥H) :=
      CFSG.Open.IsSubnormal.comap mk hc.2.1
    have h2 := CFSG.Open.IsSubnormal.map H.subtype h1
    simpa only [Y₁, Subgroup.map_top, Subgroup.range_subtype, H, Z, Ker, mk] using h2
  have hnorm : ((DerInf8 Y₁).subgroupOf Y₁).Normal := by
    have heq : (DerInf8 Y₁).subgroupOf Y₁ =
        CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual ↥Y₁ :=
      Subgroup.comap_map_eq_self_of_injective Y₁.subtype_injective _
    have hchar : (CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual ↥Y₁).Characteristic :=
      CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual_characteristic
    rw [heq]
    exact Subgroup.normal_of_characteristic (h := hchar)
  have hYsub : CFSG.Open.IsSubnormal (DerInf8 Y₁) Y₁ :=
    CFSG.Open.IsSubnormal.step (k891hcompnotle_derInf8_le Y₁) hnorm
      (CFSG.Open.IsSubnormal.refl Y₁)
  exact (show CFSG.Open.IsSubnormal (DerInf8 Y₁) H from hYsub.trans hY₁sub)

theorem s891_h_comp_not_le {G : Type} [Group G] [Finite G] (D : Data G) (L S R A : Subgroup G) (n : ℕ)
    (hn : 2 ≤ n) (hst : R891State D L S R A n) (hgam : R891Gamma895 D L S R)
    (Ys : Subgroup (R891Star (R891H L S) (R891Z L S))) (hc : IsComponentOf Ys ⊤) (hx : R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n) ≤ Ys) :
    R ≤ R891Y (R891H L S) (R891Z L S) Ys ∧ ¬ R891Y (R891H L S) (R891Z L S) Ys ≤ D.M ∧ R891Z L S ≤ R891Y (R891H L S) (R891Z L S) Ys := by
  refine ⟨k891hcompnotle_R_le_Y D L S R A n hn hst Ys hx, ?_,
    k891hcompnotle_Z_le_Y D L S R A n hn hst Ys hx⟩
  intro hY
  have _hgam : R891Gamma895 D L S R := hgam
  have hRM : R ≤ D.M :=
    hst.ctx.xShape.rSylow.trans (inf_le_left.trans hst.set.sylow.le)
  have hRuniq : R ∈ uniqueSet D.M :=
    CFSG.LocalAnalysis.RankThreeUC.mem_uniqueSet_of_le hst.uniq hst.ctx.aLeR hRM
  have hRY : R ≤ R891Y (R891H L S) (R891Z L S) Ys :=
    k891hcompnotle_R_le_Y D L S R A n hn hst Ys hx
  have hYuniq : R891Y (R891H L S) (R891Z L S) Ys ∈ uniqueSet D.M :=
    CFSG.LocalAnalysis.RankThreeUC.mem_uniqueSet_of_le hRuniq hRY hY
  exact hst.f893.normZ.2.2
    (k891hcompnotle_subnormal_le_M D.maxLocal
      (k891hcompnotle_Y_subnormal D L S R A n hst Ys hc) hY hYuniq)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
