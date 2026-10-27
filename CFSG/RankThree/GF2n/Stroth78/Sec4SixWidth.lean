module

public import CFSG.RankThree.GF2n.Stroth78.Sec3LbarBound
public import CFSG.RankThree.GF2n.Stroth78.Sec4ThreeAct
public import CFSG.RankThree.GF2n.Stroth78.Sec4ThreeZQ
public import CFSG.ClassicalGroups.Symplectic.SmallF2Module
public import CFSG.GroupTheory.ThreeTranspositions.FischerResidualProj
public import CFSG.RankThree.PartOne.LIT.RankAbstract

import CFSG.GroupTheory.ThreeTranspositions.TransvectionSpRigid
import CFSG.RankThree.GF2n.Stroth78.Sec4Three
import CFSG.RankThree.GF2n.Stroth78.Sec4Six
import CFSG.RankThree.GF2n.Stroth78.Sec4PlusFixedSq
import CFSG.RankThree.GF2n.Stroth78.Sec2SeventeenClaim
import CFSG.RankThree.GF2n.Stroth78.Sec3Five
import CFSG.RankThree.GF2n.Stroth78.Sec4Two
import CFSG.GroupTheory.KerSupOddKernel
import CFSG.ClassicalGroups.Symplectic.ProjectivePerfect

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions CFSG.GroupTheory.ThreeTranspositions Module
open CFSG.Blueprint.Fischer CFSG.Fischer.Classification Matrix
open CFSG.GroupTheory.ThreeTranspositions.TransvectionSpRigid
open scoped Pointwise commutatorElement

namespace Sec4SixW

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

attribute [local instance] Xsub_normal

theorem rhoLin_mul_self_of_mem_Lbar (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    {β : Hbar z} (hβ : β ∈ Lbar S a) : rhoLin S β * rhoLin S β = 1 := by
  rw [← rhoLin_mul, ← pow_two, sq_eq_one_of_mem_Lbar S h.mem_Q h.isConj hβ]
  simp [rhoLin]

theorem finrank_commSpace_rhoLin_le (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    {β : Hbar z} (hβ : β ∈ Lbar S a) :
    finrank (ZMod 2) (commSpace (rhoLin S β)) ≤ w := by
  have h1 := two_mul_finrank_commSpace_le (K := ZMod 2) (rhoLin_mul_self_of_mem_Lbar S h hβ)
  have h2 := finrank_QbarOf_eq_two_mul S h.card_F
  omega

noncomputable abbrev WtoH (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    {α₀ : Hbar z} (hα₀ : α₀ ∈ Rbar S a) :
    ↥(threeResidualJoin (alphaInX S h hα₀)) →* Hbar z :=
  (Xsub S a).subtype.comp (threeResidualJoin (alphaInX S h hα₀)).subtype

theorem WtoH_apply (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    {α₀ : Hbar z} (hα₀ : α₀ ∈ Rbar S a)
    (x : ↥(threeResidualJoin (alphaInX S h hα₀))) :
    WtoH S h hα₀ x = ((x : ↥(Xsub S a)) : Hbar z) := rfl

theorem WtoH_injective (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    {α₀ : Hbar z} (hα₀ : α₀ ∈ Rbar S a) : Function.Injective (WtoH S h hα₀) :=
  (Xsub S a).subtype_injective.comp (threeResidualJoin (alphaInX S h hα₀)).subtype_injective

noncomputable abbrev rhoLinW (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    {α₀ : Hbar z} (hα₀ : α₀ ∈ Rbar S a) :
    ↥(threeResidualJoin (alphaInX S h hα₀)) →*
      (Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)) :=
  (rhoGL S).comp (WtoH S h hα₀)

theorem rhoLinW_apply (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    {α₀ : Hbar z} (hα₀ : α₀ ∈ Rbar S a)
    (x : ↥(threeResidualJoin (alphaInX S h hα₀))) :
    rhoLinW S h hα₀ x = rhoLin S ((x : ↥(Xsub S a)) : Hbar z) := rfl

theorem commute_rhoLinW (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    {α₀ : Hbar z} (hα₀ : α₀ ∈ Rbar S a) {β : Hbar z}
    (hβX : ∀ x ∈ threeResidualJoin (alphaInX S h hα₀),
      β * ((x : ↥(Xsub S a)) : Hbar z) = ((x : ↥(Xsub S a)) : Hbar z) * β)
    (x : ↥(threeResidualJoin (alphaInX S h hα₀))) :
    rhoLinW S h hα₀ x * rhoLin S β = rhoLin S β * rhoLinW S h hα₀ x := by
  simp only [rhoLinW_apply, ← rhoLin_mul]
  rw [hβX x x.2]

theorem map_mem_commSpace_rhoLinW (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    {α₀ : Hbar z} (hα₀ : α₀ ∈ Rbar S a) {β : Hbar z}
    (hβX : ∀ x ∈ threeResidualJoin (alphaInX S h hα₀),
      β * ((x : ↥(Xsub S a)) : Hbar z) = ((x : ↥(Xsub S a)) : Hbar z) * β)
    (x : ↥(threeResidualJoin (alphaInX S h hα₀))) {v : Additive (QbarOf S)}
    (hv : v ∈ commSpace (rhoLin S β)) :
    rhoLinW S h hα₀ x v ∈ commSpace (rhoLin S β) := by
  obtain ⟨u, rfl⟩ := mem_commSpace.mp hv
  refine mem_commSpace.mpr ⟨rhoLinW S h hα₀ x u, ?_⟩
  have hcomm := LinearEquiv.congr_fun (commute_rhoLinW S h hα₀ hβX x) u
  simp only [LinearEquiv.mul_apply] at hcomm
  rw [map_sub, hcomm]

noncomputable abbrev rhoV (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    {α₀ : Hbar z} (hα₀ : α₀ ∈ Rbar S a) {β : Hbar z}
    (hβX : ∀ x ∈ threeResidualJoin (alphaInX S h hα₀),
      β * ((x : ↥(Xsub S a)) : Hbar z) = ((x : ↥(Xsub S a)) : Hbar z) * β) :
    ↥(threeResidualJoin (alphaInX S h hα₀)) →*
      (↥(commSpace (rhoLin S β)) ≃ₗ[ZMod 2] ↥(commSpace (rhoLin S β))) :=
  _root_.CFSG.RankThree.PartOne.LIT.restrictAction (rhoLinW S h hα₀) (commSpace (rhoLin S β))
    fun x _v hv => map_mem_commSpace_rhoLinW S h hα₀ hβX x hv

theorem rhoV_apply_coe (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    {α₀ : Hbar z} (hα₀ : α₀ ∈ Rbar S a) {β : Hbar z}
    (hβX : ∀ x ∈ threeResidualJoin (alphaInX S h hα₀),
      β * ((x : ↥(Xsub S a)) : Hbar z) = ((x : ↥(Xsub S a)) : Hbar z) * β)
    (x : ↥(threeResidualJoin (alphaInX S h hα₀)))
    (v : ↥(commSpace (rhoLin S β))) :
    ((rhoV S h hα₀ hβX x v : ↥(commSpace (rhoLin S β))) : Additive (QbarOf S)) =
      rhoLin S ((x : ↥(Xsub S a)) : Hbar z) v :=
  _root_.CFSG.RankThree.PartOne.LIT.restrictAction_apply _ _ _ x v

noncomputable def fixSubgroup (S : Setting z E F)
    (V : Submodule (ZMod 2) (Additive (QbarOf S))) : Subgroup (Hbar z) where
  carrier := {m | ∀ v ∈ V, rhoLin S m v = v}
  one_mem' := by intro v _; simp [rhoLin]
  mul_mem' := by
    intro p q hp hq v hv
    rw [rhoLin_mul, LinearEquiv.mul_apply, hq v hv, hp v hv]
  inv_mem' := by
    intro p hp v hv
    have h1 : rhoLin S p v = v := hp v hv
    calc rhoLin S p⁻¹ v = rhoLin S p⁻¹ (rhoLin S p v) := by rw [h1]
      _ = (rhoLin S p⁻¹ * rhoLin S p) v := (LinearEquiv.mul_apply _ _ _).symm
      _ = v := by rw [← rhoLin_mul, inv_mul_cancel]; simp [rhoLin]

theorem map_WtoH_le_normalizer_zpowers (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w) {α₀ : Hbar z} (hα₀ : α₀ ∈ Rbar S a) {β : Hbar z}
    (hβX : ∀ x ∈ threeResidualJoin (alphaInX S h hα₀),
      β * ((x : ↥(Xsub S a)) : Hbar z) = ((x : ↥(Xsub S a)) : Hbar z) * β) :
    (threeResidualJoin (alphaInX S h hα₀)).map (Xsub S a).subtype ≤
      Subgroup.normalizer (Subgroup.zpowers β : Set (Hbar z)) := by
  intro x hx
  obtain ⟨ww, hww, rfl⟩ := Subgroup.mem_map.mp hx
  have hconjβ : MulAut.conj (((ww : ↥(Xsub S a)) : Hbar z)) β = β := by
    rw [MulAut.conj_apply, ← hβX ww hww]
    group
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  calc (Subgroup.zpowers β).map (MulAut.conj (((ww : ↥(Xsub S a)) : Hbar z))).toMonoidHom
      = Subgroup.zpowers (MulAut.conj (((ww : ↥(Xsub S a)) : Hbar z)) β) :=
        MonoidHom.map_zpowers _ _
    _ = Subgroup.zpowers β := by rw [hconjβ]

theorem rhoLin_eq_self_of_mem_Lbar (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    {α₀ : Hbar z} (hα₀ : α₀ ∈ Rbar S a) {β : Hbar z} (hβ : β ∈ Lbar S a)
    (hβX : ∀ x ∈ threeResidualJoin (alphaInX S h hα₀),
      β * ((x : ↥(Xsub S a)) : Hbar z) = ((x : ↥(Xsub S a)) : Hbar z) * β)
    (hLW : Lbar S a ≤ (threeResidualJoin (alphaInX S h hα₀)).map (Xsub S a).subtype ⊔
      Subgroup.zpowers β)
    (hW : ∀ x : ↥(threeResidualJoin (alphaInX S h hα₀)), x ^ 2 = 1 →
      ∀ v ∈ commSpace (rhoLin S β), rhoLin S ((x : ↥(Xsub S a)) : Hbar z) v = v)
    {l : Hbar z} (hl : l ∈ Lbar S a) {v : Additive (QbarOf S)}
    (hv : v ∈ commSpace (rhoLin S β)) : rhoLin S l v = v := by
  classical
  have hβT : β ∈ fixSubgroup S (commSpace (rhoLin S β)) := fun v hv' =>
    mem_fixSpace.mp (commSpace_le_fixSpace (rhoLin_mul_self_of_mem_Lbar S h hβ) hv')
  have hT : ∀ m ∈ Subgroup.zpowers β, ∀ v ∈ commSpace (rhoLin S β), rhoLin S m v = v :=
    fun m hm => Subgroup.zpowers_le.mpr hβT hm
  have hset : (↑((threeResidualJoin (alphaInX S h hα₀)).map (Xsub S a).subtype ⊔
      Subgroup.zpowers β) : Set (Hbar z)) =
      (((threeResidualJoin (alphaInX S h hα₀)).map (Xsub S a).subtype : Set (Hbar z)) *
        (Subgroup.zpowers β : Set (Hbar z)) : Set (Hbar z)) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _
      (map_WtoH_le_normalizer_zpowers S h hα₀ hβX)
  have hl' : l ∈ (((threeResidualJoin (alphaInX S h hα₀)).map (Xsub S a).subtype :
      Set (Hbar z)) * (Subgroup.zpowers β : Set (Hbar z)) : Set (Hbar z)) := hset ▸ hLW hl
  obtain ⟨x, hxW, m, hm, hxm⟩ := Set.mem_mul.mp hl'
  obtain ⟨ww, hww, hxw⟩ := Subgroup.mem_map.mp hxW
  have hxl : x ∈ Lbar S a := by
    have heq : x = l * m⁻¹ := by rw [← hxm]; group
    rw [heq]
    exact (Lbar S a).mul_mem hl ((Lbar S a).inv_mem (Subgroup.zpowers_le.mpr hβ hm))
  have hx2 : x ^ 2 = 1 := sq_eq_one_of_mem_Lbar S h.mem_Q h.isConj hxl
  have hxw' : ((ww : ↥(Xsub S a)) : Hbar z) = x := by
    simpa only [Subgroup.coe_subtype] using hxw
  have hw2 : (⟨ww, hww⟩ : ↥(threeResidualJoin (alphaInX S h hα₀))) ^ 2 = 1 := by
    have hcoe : WtoH S h hα₀ ⟨ww, hww⟩ = x := hxw
    refine WtoH_injective S h hα₀ ?_
    rw [map_pow, map_one, hcoe, hx2]
  have hxfix : rhoLin S x v = v := by
    simpa [hxw'] using hW ⟨ww, hww⟩ hw2 v hv
  rw [← hxm, rhoLin_mul, LinearEquiv.mul_apply, hT m hm v hv, hxfix]

theorem rhoLin_sub_mem_span_aVec (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    {β : Hbar z} (hβ : β ∈ Lbar S a)
    (hfixL : ∀ l ∈ Lbar S a, ∀ v ∈ commSpace (rhoLin S β), rhoLin S l v = v)
    {v : Additive (QbarOf S)} (hv : QuadraticMap.polar (qS S) v (aVec S h.mem_Q) = 0) :
    rhoLin S β v - v ∈ (ZMod 2) ∙ aVec S h.mem_Q := by
  classical
  let hmod : Module (ZMod 2) (Additive (Abelianization ↥F)) := modAbF S
  have ha_ne : aVec S h.mem_Q ≠ 0 := aV_ne_zero S h.mem_Q h.not_mem_ZQ
  have hdU : rhoLin S β v - v ∈ QaInterImage S (Q z ⊓ QaOf a) :=
    rhoBar_sub_mem_QaInterImage S h.mem_Q hβ hv
  have hdV : rhoLin S β v - v ∈ commSpace (rhoLin S β) := sub_mem_commSpace _ v
  by_contra hspan
  obtain ⟨y, hyA, hyv⟩ := (mem_QaInterImage_iff S).mp hdU
  have hyQ : (y : G) ∈ Q z := (Subgroup.mem_inf.mp hyA).1
  have hyQa : (y : G) ∈ QaOf a := (Subgroup.mem_inf.mp hyA).2
  have hd_eq : Additive.ofMul (mkQbar S ⟨(y : G), hyQ⟩) = rhoLin S β v - v := by
    have h := congrArg Additive.ofMul hyv
    simpa using h
  have hy_not : Additive.ofMul (mkQbar S ⟨(y : G), hyQ⟩) ∉
      (ZMod 2) ∙ aVec S h.mem_Q := by
    rw [hd_eq]
    exact hspan
  obtain ⟨l, hl, hsub⟩ :=
    exists_lbar_apply_sub_eq S h.mem_Q h.isConj h.mem_Qa hyQ hyQa hy_not
  have hfixd : rhoLin S l (rhoLin S β v - v) = rhoLin S β v - v :=
    hfixL l hl (rhoLin S β v - v) hdV
  rw [hd_eq, hfixd, sub_self] at hsub
  exact ha_ne hsub.symm

theorem aVec_mem_commSpace_rhoLin (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    {β : Hbar z} (hβ : β ∈ Lbar S a) (hβ1 : β ≠ 1)
    (hfixL : ∀ l ∈ Lbar S a, ∀ v ∈ commSpace (rhoLin S β), rhoLin S l v = v) :
    aVec S h.mem_Q ∈ commSpace (rhoLin S β) := by
  classical
  let hmod : Module (ZMod 2) (Additive (Abelianization ↥F)) := modAbF S
  have hsq : rhoLin S β * rhoLin S β = 1 := rhoLin_mul_self_of_mem_Lbar S h hβ
  have hOβ : rhoLin S β ∈ TauCeti.QuadraticMap.orthogonalGroup (qS S) := (rhoBar S β).2
  have hB : (qS S).polarBilin.Nondegenerate := q_nondegenerate S
  have hBrefl : (qS S).polarBilin.IsRefl :=
    CFSG.LargeExtraspecial.OrthoF2.isRefl_polarBilin (qS S)
  by_cases hex : ∃ v, QuadraticMap.polar (qS S) v (aVec S h.mem_Q) = 0 ∧
      rhoLin S β v - v = aVec S h.mem_Q
  · obtain ⟨v, hv, hveq⟩ := hex
    exact mem_commSpace.mpr ⟨v, hveq⟩
  · push Not at hex
    have hfixorth : ∀ v, QuadraticMap.polar (qS S) v (aVec S h.mem_Q) = 0 →
        rhoLin S β v = v := by
      intro v hv
      rcases CFSG.LargeExtraspecial.OrthoF2.mem_span_singleton_iff.mp
        (rhoLin_sub_mem_span_aVec S h hβ hfixL hv) with h0 | h1
      · exact sub_eq_zero.mp h0
      · exact absurd h1 (hex v hv)
    have horth : ∀ u, rhoLin S β u - u ∈ (ZMod 2) ∙ aVec S h.mem_Q := by
      intro u
      rw [← LinearMap.BilinForm.orthogonal_orthogonal hB hBrefl ((ZMod 2) ∙ aVec S h.mem_Q)]
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro n hn
      have hn' : QuadraticMap.polar (qS S) n (aVec S h.mem_Q) = 0 := by
        have h1 := (LinearMap.BilinForm.mem_orthogonal_iff.mp hn) (aVec S h.mem_Q)
          (Submodule.mem_span_singleton_self _)
        simpa [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm] using h1
      have hfixn : rhoLin S β n = n := hfixorth n hn'
      have h2 := polar_sub_eq_polar_sub (Q := qS S) (t := rhoLin S β) hOβ hsq u n
      rw [hfixn, sub_self, QuadraticMap.polar_zero_right] at h2
      rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]
      exact h2
    have hex_ne : ∃ u, rhoLin S β u - u ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hβ1
      apply rhoLin_injective S
      rw [show rhoLin S 1 = 1 from by simp [rhoLin]]
      exact LinearEquiv.ext fun u => sub_eq_zero.mp (hcon u)
    obtain ⟨u, hu⟩ := hex_ne
    rcases CFSG.LargeExtraspecial.OrthoF2.mem_span_singleton_iff.mp (horth u) with h0 | h1
    · exact absurd h0 hu
    · exact mem_commSpace.mpr ⟨u, h1⟩

theorem rhoV_eq_one_of_sq_eq_one (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    {α₀ : Hbar z} (hα₀ : α₀ ∈ Rbar S a) {m : ℕ} (hm : 3 ≤ m)
    (e : ↥(threeResidualQuot (alphaInX S h hα₀)) ≃* StatedSp m (ZMod 2))
    {β : Hbar z}
    (hβX : ∀ x ∈ threeResidualJoin (alphaInX S h hα₀),
      β * ((x : ↥(Xsub S a)) : Hbar z) = ((x : ↥(Xsub S a)) : Hbar z) * β)
    (hdim : finrank (ZMod 2) (commSpace (rhoLin S β)) < 2 * m)
    {x : ↥(threeResidualJoin (alphaInX S h hα₀))} (hx : x ^ 2 = 1) :
    rhoV S h hα₀ hβX x = 1 := by
  let π : ↥(threeResidualJoin (alphaInX S h hα₀)) →* StatedSp m (ZMod 2) :=
    e.toMonoidHom.comp (residualProj (alphaInX S h hα₀))
  have hπ : Function.Surjective π :=
    e.surjective.comp (residualProj_surjective (alphaInX S h hα₀))
  have htop : (rhoV S h hα₀ hβX).ker ⊔ π.ker = ⊤ :=
    CFSG.ClassicalGroups.Symplectic.ker_sup_ker_eq_top_of_statedSp_of_finrank_lt hm π hπ
      (rhoV S h hα₀ hβX) hdim
  have hker : π.ker = (residualProj (alphaInX S h hα₀)).ker := by
    ext y
    simp only [π, MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact e.map_eq_one_iff
  have hodd : Odd (Nat.card ↥(π.ker)) := by
    rw [hker]
    exact odd_card_ker_residualProj _ (odd_card_center_Xsub S a)
  exact CFSG.GroupTheory.map_eq_one_of_sq_eq_one_of_ker_sup_eq_top hodd
    (rhoV S h hα₀ hβX) htop hx

theorem aVec_fixed_of_mem_map_ker (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    {α₀ : Hbar z} (hα₀ : α₀ ∈ Rbar S a) {β : Hbar z}
    (hβX : ∀ x ∈ threeResidualJoin (alphaInX S h hα₀),
      β * ((x : ↥(Xsub S a)) : Hbar z) = ((x : ↥(Xsub S a)) : Hbar z) * β)
    (hã : aVec S h.mem_Q ∈ commSpace (rhoLin S β))
    {y : Hbar z} (hy : y ∈ (rhoV S h hα₀ hβX).ker.map (WtoH S h hα₀)) :
    rhoLin S y (aVec S h.mem_Q) = aVec S h.mem_Q := by
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
  have hx1 : rhoV S h hα₀ hβX x = 1 := hx
  have h2 := rhoV_apply_coe S h hα₀ hβX x ⟨aVec S h.mem_Q, hã⟩
  rw [hx1] at h2
  simp only [LinearEquiv.coe_one, id] at h2
  rw [← WtoH_apply (S := S) (h := h) (hα₀ := hα₀) x] at h2
  exact h2.symm

theorem commute_ZQ_of_mem_map_ker (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (hZ : ∀ x ∈ Xsub S a, rhoZ S x = 1) {α₀ : Hbar z} (hα₀ : α₀ ∈ Rbar S a)
    {β : Hbar z}
    (hβX : ∀ x ∈ threeResidualJoin (alphaInX S h hα₀),
      β * ((x : ↥(Xsub S a)) : Hbar z) = ((x : ↥(Xsub S a)) : Hbar z) * β)
    {x : ↥(H z)} (hx : QuotientGroup.mk x ∈ (rhoV S h hα₀ hβX).ker.map (WtoH S h hα₀)) :
    ∀ v ∈ ZQ z, (x : G) * v * (x : G)⁻¹ = v := by
  have hPbar_le : (rhoV S h hα₀ hβX).ker.map (WtoH S h hα₀) ≤ Xsub S a := by
    intro y hy
    obtain ⟨x', -, rfl⟩ := Subgroup.mem_map.mp hy
    exact (x' : ↥(Xsub S a)).2
  intro v hv
  have h2 := rhoZ_mk S x ⟨v, hv⟩
  rw [hZ (QuotientGroup.mk x) (hPbar_le hx), MulAut.one_apply] at h2
  exact h2.symm

theorem commutator_ker_commute_residualSelf (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w) {α₀ : Hbar z} (hα₀ : α₀ ∈ Rbar S a) (hα₀1 : α₀ ≠ 1)
    (hcardR : Nat.card ↥(Rbar S a) = 2)
    (hZ : ∀ x ∈ Xsub S a, rhoZ S x = 1)
    {β : Hbar z} (hβX : ∀ x ∈ threeResidualJoin (alphaInX S h hα₀),
      β * ((x : ↥(Xsub S a)) : Hbar z) = ((x : ↥(Xsub S a)) : Hbar z) * β)
    (hã : aVec S h.mem_Q ∈ commSpace (rhoLin S β)) :
    ∀ z ∈ ⁅(rhoV S h hα₀ hβX).ker, (rhoV S h hα₀ hβX).ker⁆,
      z * residualSelf (alphaInX S h hα₀) = residualSelf (alphaInX S h hα₀) * z := by
  classical
  set ρV : ↥(threeResidualJoin (alphaInX S h hα₀)) →*
      (↥(commSpace (rhoLin S β)) ≃ₗ[ZMod 2] ↥(commSpace (rhoLin S β))) :=
    rhoV S h hα₀ hβX with hρV
  have hcommCH : ⁅ρV.ker.map (WtoH S h hα₀), ρV.ker.map (WtoH S h hα₀)⁆ ≤ CHbar S a := by
    have h := commutator_le_CH_of_fixes h.mem_Q
      (fun y hy => aVec_fixed_of_mem_map_ker S h hα₀ hβX hã hy)
      (fun x hx => commute_ZQ_of_mem_map_ker S h hZ hα₀ hβX hx)
    simpa [CHbar, CH] using h
  have hcommα₀ : ∀ y ∈ ⁅ρV.ker.map (WtoH S h hα₀), ρV.ker.map (WtoH S h hα₀)⁆,
      y * α₀ = α₀ * y :=
    fun y hy => commute_of_mem_CHbar_of_card_Rbar_eq_two S a hcardR hα₀ hα₀1 (hcommCH hy)
  have hcommφ : ∀ z ∈ ⁅ρV.ker, ρV.ker⁆, WtoH S h hα₀ z * α₀ = α₀ * WtoH S h hα₀ z := by
    intro z hz
    refine hcommα₀ (WtoH S h hα₀ z) ?_
    have hmap : ⁅ρV.ker, ρV.ker⁆.map (WtoH S h hα₀) =
        ⁅ρV.ker.map (WtoH S h hα₀), ρV.ker.map (WtoH S h hα₀)⁆ :=
      Subgroup.map_commutator _ _ _
    rw [← hmap]
    exact Subgroup.mem_map_of_mem (WtoH S h hα₀) hz
  intro z hz
  have hzw : WtoH S h hα₀ (z * residualSelf (alphaInX S h hα₀)) =
      WtoH S h hα₀ z * α₀ := rfl
  have hrsw : WtoH S h hα₀ (residualSelf (alphaInX S h hα₀) * z) =
      α₀ * WtoH S h hα₀ z := rfl
  refine WtoH_injective S h hα₀ ?_
  rw [hzw, hrsw]
  exact hcommφ z hz

theorem central_residualProj_residualSelf (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w) {α₀ : Hbar z} (hα₀ : α₀ ∈ Rbar S a) (hα₀1 : α₀ ≠ 1) {m : ℕ}
    (hm : 3 ≤ m) (e : ↥(threeResidualQuot (alphaInX S h hα₀)) ≃* StatedSp m (ZMod 2))
    (hcardR : Nat.card ↥(Rbar S a) = 2)
    (hZ : ∀ x ∈ Xsub S a, rhoZ S x = 1)
    {β : Hbar z} (hβX : ∀ x ∈ threeResidualJoin (alphaInX S h hα₀),
      β * ((x : ↥(Xsub S a)) : Hbar z) = ((x : ↥(Xsub S a)) : Hbar z) * β)
    (hã : aVec S h.mem_Q ∈ commSpace (rhoLin S β))
    (hdim : finrank (ZMod 2) (commSpace (rhoLin S β)) < 2 * m) :
    e (residualProj (alphaInX S h hα₀) (residualSelf (alphaInX S h hα₀))) ∈
      Subgroup.center (StatedSp m (ZMod 2)) := by
  classical
  set ρV : ↥(threeResidualJoin (alphaInX S h hα₀)) →*
      (↥(commSpace (rhoLin S β)) ≃ₗ[ZMod 2] ↥(commSpace (rhoLin S β))) :=
    rhoV S h hα₀ hβX with hρV
  let π : ↥(threeResidualJoin (alphaInX S h hα₀)) →* StatedSp m (ZMod 2) :=
    e.toMonoidHom.comp (residualProj (alphaInX S h hα₀))
  have hπ : Function.Surjective π :=
    e.surjective.comp (residualProj_surjective (alphaInX S h hα₀))
  have htop : ρV.ker ⊔ π.ker = ⊤ :=
    CFSG.ClassicalGroups.Symplectic.ker_sup_ker_eq_top_of_statedSp_of_finrank_lt hm π hπ
      ρV hdim
  have hker_map : π.ker.map π = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    rw [Subgroup.mem_bot]
    exact MonoidHom.mem_ker.mp hx
  have hPmap : ρV.ker.map π = ⊤ := by
    have h := congrArg (Subgroup.map π) htop
    rw [Subgroup.map_sup, hker_map, Subgroup.map_top, sup_bot_eq,
      MonoidHom.range_eq_top.mpr hπ] at h
    exact h
  have hcmap : ⁅ρV.ker, ρV.ker⁆.map π = ⊤ := by
    have hperf : Group.IsPerfect (StatedSp m (ZMod 2)) :=
      CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp m (ZMod 2)
        (Or.inr (Or.inr ⟨Nat.card_zmod 2, hm⟩))
    rw [Subgroup.map_commutator, hPmap, ← commutator_def, hperf.commutator_eq_top]
  have hcommrs := commutator_ker_commute_residualSelf S h hα₀ hα₀1 hcardR hZ hβX hã
  rw [Subgroup.mem_center_iff]
  intro s
  have hs : s ∈ ⁅ρV.ker, ρV.ker⁆.map π := by
    rw [hcmap]
    exact Subgroup.mem_top s
  obtain ⟨z, hz, hzs⟩ := Subgroup.mem_map.mp hs
  rw [← hzs]
  have hkey := congrArg (fun w => e (residualProj (alphaInX S h hα₀) w)) (hcommrs z hz)
  simpa only [π, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_mul] using hkey

theorem alphaInX_not_mem_center (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    {α₀ : Hbar z} (hα₀ : α₀ ∈ Rbar S a) (hα₀1 : α₀ ≠ 1) :
    alphaInX S h hα₀ ∉ Subgroup.center ↥(Xsub S a) := by
  intro hcenter_mem
  have hd2 : alphaInX S h hα₀ ^ 2 = 1 := by
    apply Subtype.ext
    show ((alphaInX S h hα₀ : ↥(Xsub S a)) : Hbar z) ^ 2 = 1
    simpa using sq_eq_one_of_mem_Lbar S h.mem_Q h.isConj (Rbar_le_Lbar S a hα₀)
  have hd1 : alphaInX S h hα₀ ≠ 1 := fun h1 =>
    hα₀1 (congrArg (fun x : ↥(Xsub S a) => (x : Hbar z)) h1)
  have hdvd2 : orderOf (alphaInX S h hα₀) ∣ 2 := orderOf_dvd_of_pow_eq_one hd2
  have hdvdN : orderOf (alphaInX S h hα₀) ∣
      Nat.card ↥(Subgroup.center ↥(Xsub S a)) :=
    Subgroup.orderOf_dvd_natCard _ hcenter_mem
  have hodd : Odd (orderOf (alphaInX S h hα₀)) :=
    (odd_card_center_Xsub S a).of_dvd_nat hdvdN
  exact hd1 (orderOf_eq_one_iff.mp
    (Nat.Coprime.eq_one_of_dvd hodd.coprime_two_right hdvd2))

theorem false_of_aVec_mem_commSpace (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    {α₀ : Hbar z} (hα₀ : α₀ ∈ Rbar S a) (hα₀1 : α₀ ≠ 1) {m : ℕ} (hm : 3 ≤ m)
    (e : ↥(threeResidualQuot (alphaInX S h hα₀)) ≃* StatedSp m (ZMod 2))
    (hcenter : Subgroup.center ↥(threeResidualQuot (alphaInX S h hα₀)) = ⊥)
    (hcardR : Nat.card ↥(Rbar S a) = 2)
    (hZ : ∀ x ∈ Xsub S a, rhoZ S x = 1)
    {β : Hbar z} (hβX : ∀ x ∈ threeResidualJoin (alphaInX S h hα₀),
      β * ((x : ↥(Xsub S a)) : Hbar z) = ((x : ↥(Xsub S a)) : Hbar z) * β)
    (hã : aVec S h.mem_Q ∈ commSpace (rhoLin S β))
    (hdim : finrank (ZMod 2) (commSpace (rhoLin S β)) < 2 * m) : False := by
  classical
  have hcentral :=
    central_residualProj_residualSelf S h hα₀ hα₀1 hm e hcardR hZ hβX hã hdim
  have hres1 : residualProj (alphaInX S h hα₀) (residualSelf (alphaInX S h hα₀)) = 1 := by
    have hmem : residualProj (alphaInX S h hα₀) (residualSelf (alphaInX S h hα₀)) ∈
        Subgroup.center ↥(threeResidualQuot (alphaInX S h hα₀)) := by
      rw [Subgroup.mem_center_iff]
      intro t
      have h1 : e t * e (residualProj (alphaInX S h hα₀)
          (residualSelf (alphaInX S h hα₀))) =
          e (residualProj (alphaInX S h hα₀) (residualSelf (alphaInX S h hα₀))) * e t :=
        Subgroup.mem_center_iff.mp hcentral (e t)
      have h2 : e (t * residualProj (alphaInX S h hα₀) (residualSelf (alphaInX S h hα₀))) =
          e (residualProj (alphaInX S h hα₀) (residualSelf (alphaInX S h hα₀)) * t) := by
        rw [map_mul, map_mul]
        exact h1
      exact e.injective h2
    rw [hcenter] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hmk : (QuotientGroup.mk (alphaInX S h hα₀) :
      ↥(Xsub S a) ⧸ Subgroup.center ↥(Xsub S a)) = 1 := by
    have hval : ((residualProj (alphaInX S h hα₀) (residualSelf (alphaInX S h hα₀)) :
        ↥(threeResidualQuot (alphaInX S h hα₀))) :
        ↥(Xsub S a) ⧸ Subgroup.center ↥(Xsub S a)) =
        QuotientGroup.mk (alphaInX S h hα₀) := by
      rw [residualProj_apply]
      rfl
    rw [← hval, hres1]
    rfl
  exact alphaInX_not_mem_center S h hα₀ hα₀1 (by
    rw [← QuotientGroup.eq_one_iff]
    exact hmk)

theorem two_mul_le_of_mem_centralizer (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {α₀ : Hbar z} (hα₀ : α₀ ∈ Rbar S a) (hα₀1 : α₀ ≠ 1) {m : ℕ} (hm : 3 ≤ m)
    {b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (halt : ∀ x, b x x = 0) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (hsp : fischerLinearModel (threeResidualClass (alphaInX S h hα₀))
      (fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y)
      (fischerTransvections (fun x y => b x y) fun v => v ≠ 0))
    (hZ : ∀ x ∈ Xsub S a, rhoZ S x = 1)
    {β : Hbar z} (hβ : β ∈ Lbar S a) (hβ1 : β ≠ 1)
    (hβX : ∀ x ∈ threeResidualJoin (alphaInX S h hα₀),
      β * ((x : ↥(Xsub S a)) : Hbar z) = ((x : ↥(Xsub S a)) : Hbar z) * β)
    (hLW : Lbar S a ≤ (threeResidualJoin (alphaInX S h hα₀)).map (Xsub S a).subtype ⊔
      Subgroup.zpowers β) :
    2 * m ≤ w := by
  classical
  by_contra hcon
  have hdim : finrank (ZMod 2) (commSpace (rhoLin S β)) < 2 * m := by
    have h1 := finrank_commSpace_rhoLin_le S h hβ
    omega
  obtain ⟨e⟩ := Sec4Six.exists_mulEquiv_statedSp_of_fischerLinearModel halt hnd hsp
  have hW : ∀ x : ↥(threeResidualJoin (alphaInX S h hα₀)), x ^ 2 = 1 →
      ∀ v ∈ commSpace (rhoLin S β), rhoLin S ((x : ↥(Xsub S a)) : Hbar z) v = v := by
    intro x hx v hv
    have h1 : rhoV S h hα₀ hβX x = 1 :=
      rhoV_eq_one_of_sq_eq_one S h hα₀ hm e hβX hdim hx
    have h2 := rhoV_apply_coe S h hα₀ hβX x ⟨v, hv⟩
    rw [h1] at h2
    simpa using h2.symm
  have hfixL : ∀ l ∈ Lbar S a, ∀ v ∈ commSpace (rhoLin S β), rhoLin S l v = v :=
    fun l hl v hv => rhoLin_eq_self_of_mem_Lbar S h hα₀ hβ hβX hLW hW hl hv
  have hã : aVec S h.mem_Q ∈ commSpace (rhoLin S β) :=
    aVec_mem_commSpace_rhoLin S h hβ hβ1 hfixL
  exact false_of_aVec_mem_commSpace S h hα₀ hα₀1 hm e
    (hyp_Wbar S h h217 h3 hα₀ hα₀1).center
    (card_Rbar_eq_two S h h217 h3) hZ hβX hã hdim

end Sec4SixW

end CFSG.RankThree.GF2n.Stroth78

end
