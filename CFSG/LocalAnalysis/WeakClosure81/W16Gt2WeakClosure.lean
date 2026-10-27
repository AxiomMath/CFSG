module

public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2G1Seven
public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2WeakClosureAux2
public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2WeakClosureAux3

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Cfg1620

variable {M V₀ V U S R H : Subgroup G} {g : G} {B : Subgroup G}

section Certified


theorem comm_of_isPGroup (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G) (hS : Std15 G)
    (c : Cfg1620 M V₀ V U S R H g B) (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) {h : G}
    (hh : h ∈ H) (hhM : h ∉ M) (hP : IsPGroup 2 ↥(Mo.img (V ⊔ conjSubgroup V h))) :
    (⁅V, conjSubgroup V₀ h⁆ = ⊥ ∧ ⁅conjSubgroup V h, V₀⁆ = ⊥ ∧ V ≤ conjSubgroup M h ∧
        conjSubgroup V h ≤ M) ∧
      (⁅U, conjSubgroup V h⁆ ≤ V ⊓ conjSubgroup V₀ h ∧ ⁅U, conjSubgroup V h⁆ ≠ ⊥) ∧
      ¬ conjSubgroup V h ≤ CFSG.LocalAnalysis.UniquenessCase.UC22.F11.CTilde M V₀ V := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcommV, hcommW, -⟩ := hat_commute_of_isPGroup h1 h5 h15 hS c Mo hh hP
  have hcomm1 : ⁅V, conjSubgroup V₀ h⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (hcommV x hx w hw).symm
  have hcomm2 : ⁅conjSubgroup V h, V₀⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (hcommW w hw x hx).symm
  have hnorm : Subgroup.normalizer (conjSubgroup V₀ h : Set G) = conjSubgroup M h := by
    rw [← E3.conjSubgroup_normalizer, c.cex.hyp.normalizer₀]
  have hVleMh : V ≤ conjSubgroup M h :=
    ((Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm1).trans
      (Subgroup.centralizer_le_normalizer (conjSubgroup V₀ h : Set G))).trans (le_of_eq hnorm)
  have hWleM : conjSubgroup V h ≤ M :=
    ((Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm2).trans
      (Subgroup.centralizer_le_normalizer (V₀ : Set G))).trans
      (le_of_eq c.cex.hyp.normalizer₀)
  have hI_le : U ≤ conjClosure (U ⊔ V₀) H :=
    (le_sup_left : U ≤ U ⊔ V₀).trans (le_conjClosure (U ⊔ V₀) H)
  have hWnormV : conjSubgroup V h ≤ Subgroup.normalizer (V : Set G) :=
    hWleM.trans (le_of_eq c.cex.hyp.h6.normalizer_eq.symm)
  have hcommUW_V₀ : ⁅U, conjSubgroup V h⁆ ≤ conjSubgroup V₀ h := by
    calc ⁅U, conjSubgroup V h⁆ ≤ ⁅conjClosure (U ⊔ V₀) H, conjSubgroup V h⁆ :=
          Subgroup.commutator_mono hI_le le_rfl
      _ = ⁅conjSubgroup V h, conjClosure (U ⊔ V₀) H⁆ := Subgroup.commutator_comm _ _
      _ ≤ conjSubgroup V₀ h := comm_conj_conjClosure_le h1 hS c hh
  have hcommUW_V : ⁅U, conjSubgroup V h⁆ ≤ V :=
    (Subgroup.commutator_mono c.cex.le le_rfl).trans
      ((Subgroup.le_normalizer_iff_commutator_le_left).1 hWnormV)
  have hcommUW : ⁅U, conjSubgroup V h⁆ ≤ V ⊓ conjSubgroup V₀ h := le_inf hcommUW_V hcommUW_V₀
  have hcommUW_ne : ⁅U, conjSubgroup V h⁆ ≠ ⊥ := by
    intro hbot
    have hUleC : U ≤ Subgroup.centralizer (conjSubgroup V h : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 hbot
    have hWleCU : conjSubgroup V h ≤ Subgroup.centralizer (U : Set G) :=
      (Subgroup.le_centralizer_iff).1 hUleC
    exact hhM (Cex16.mem_of_conj_le_centralizer h15 hS c.cex (le_inf hWleM hWleCU))
  refine ⟨⟨hcomm1, hcomm2, hVleMh, hWleM⟩, ⟨hcommUW, hcommUW_ne⟩, ?_⟩
  intro hWct
  let W : Subgroup G := conjSubgroup V h
  let V₀' : Subgroup G := conjSubgroup V₀ h
  have hW : IsElemAbelian 2 W := E3.isElemAbelian_conjSubgroup c.cex.hyp.h6.elemAbelian h
  have hVc : IsElemAbelian 2 V := c.cex.hyp.h6.elemAbelian
  have hMnormV : M ≤ Subgroup.normalizer (V : Set G) :=
    le_of_eq c.cex.hyp.h6.normalizer_eq.symm
  have hMh_stab : conjSubgroup M h ≤ stabTil V₀' W := by
    refine le_inf ?_ ?_
    · have hconj := E3.conjSubgroup_mono_left h hMnormV
      rw [E3.conjSubgroup_normalizer] at hconj
      exact hconj
    · have hconj := E3.conjSubgroup_mono_left h c.cex.hyp.h6.le_normalizer₀
      rw [E3.conjSubgroup_normalizer] at hconj
      exact hconj
  have hWV_le_V₀ : ⁅W, V⁆ ≤ V₀ :=
    Subgroup.commutator_le.2 fun w hw v hv =>
      (FourteenTwo.mem_cTilde_iff_comm.1 (hWct (show w ∈ conjSubgroup V h from hw))).2.2 v hv
  have hhinv : h⁻¹ ∉ M := fun hmem => hhM (by simpa using M.inv_mem hmem)
  have hWrk : rk ↥(V₀ ⊓ W) ≤ E3.mQuot V (U ⊔ V₀) := by
    have heq : conjSubgroup (conjSubgroup V₀ h⁻¹ ⊓ V) h = V₀ ⊓ W := by
      change conjSubgroup (conjSubgroup V₀ h⁻¹ ⊓ V) h = V₀ ⊓ conjSubgroup V h
      rw [E3.conjSubgroup_inf, conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
    have hcard : Nat.card ↥(V₀ ⊓ W) = Nat.card ↥(conjSubgroup V₀ h⁻¹ ⊓ V) := by
      rw [← heq, E3.card_conjSubgroup]
    have hbound := c.rk_conjSubgroup_inf_le (x := h⁻¹) hhinv
    have hrk : rk ↥(V₀ ⊓ W) = rk ↥(conjSubgroup V₀ h⁻¹ ⊓ V) := by
      unfold rk
      rw [hcard]
    rw [hrk]
    exact hbound
  have hbnd : ∀ (v : G) (hv : v ∈ V) (st : v ∈ stabTil V₀' W),
      rk ↥(commV (Subgroup.zpowers (actTil V₀' W hW ⟨v, st⟩))) ≤ E3.mQuot V (U ⊔ V₀) := by
    intro v hv st
    have hvN : Subgroup.zpowers v ≤ Subgroup.normalizer (W : Set G) :=
      (Subgroup.zpowers_le.2 (hMh_stab (hVleMh hv))).trans (stabTil_le_normalizer V₀' W)
    have hcommWV : ⁅W, Subgroup.zpowers v⁆ ≤ V₀ :=
      (Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.2 hv)).trans hWV_le_V₀
    have hcommWvW : ⁅W, Subgroup.zpowers v⁆ ≤ W := by
      rw [Subgroup.commutator_comm]
      exact (Subgroup.le_normalizer_iff_commutator_le_right).1 hvN
    exact (rk_commV_actTil_le_of_commutator_le hW st (le_inf hcommWV hcommWvW)).trans hWrk
  have htriv : ∀ (v : G) (hv : v ∈ V),
      actTil V₀' W hW ⟨v, hMh_stab (hVleMh hv)⟩ = 1 := by
    intro v hv
    by_contra hne
    have hvst : v ∈ stabTil V₀' W := hMh_stab (hVleMh hv)
    have hA1 : Subgroup.zpowers (actTil V₀' W hW ⟨v, hvst⟩) ≠ ⊥ := by
      intro hbot
      refine hne ?_
      have hmem := Subgroup.mem_zpowers (actTil V₀' W hW ⟨v, hvst⟩)
      rw [hbot] at hmem
      exact Subgroup.mem_bot.1 hmem
    have hsqSt : (⟨v, hvst⟩ : stabTil V₀' W) * ⟨v, hvst⟩ = 1 := by
      apply Subtype.ext
      show v * v = 1
      simpa [pow_two] using c.cex.hyp.h6.elemAbelian.2 v hv
    have hsq : actTil V₀' W hW ⟨v, hvst⟩ * actTil V₀' W hW ⟨v, hvst⟩ = 1 := by
      rw [← map_mul, hsqSt, map_one]
    have hAp : IsPGroup 2 (Subgroup.zpowers (actTil V₀' W hW ⟨v, hvst⟩)) := by
      have ho2 : orderOf (actTil V₀' W hW ⟨v, hvst⟩) ∣ 2 :=
        orderOf_dvd_iff_pow_eq_one.2 (by rw [pow_two]; exact hsq)
      rcases (Nat.dvd_prime Nat.prime_two).1 ho2 with ho1 | ho2'
      · exact absurd (orderOf_eq_one_iff.1 ho1) hne
      · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ho2', pow_one])
    have hmem : actTil V₀' W hW ⟨v, hvst⟩ ∈ Mbar (conjSubgroup M h) V₀' W hW :=
      actTil_mem_barSub V₀' W hW (hVleMh hv) hvst
    have hAle : Subgroup.zpowers (actTil V₀' W hW ⟨v, hvst⟩) ≤
        Mbar (conjSubgroup M h) V₀' W hW := Subgroup.zpowers_le.2 hmem
    have hmp : mBar (conjSubgroup M h) V₀' W hW ≤
        rkIdx (fixV (Subgroup.zpowers (actTil V₀' W hW ⟨v, hvst⟩))) :=
      E3.mParam_le_rkIdx_fixV hAle hAp hA1
    have hrk : rkIdx (fixV (Subgroup.zpowers (actTil V₀' W hW ⟨v, hvst⟩))) =
        rk ↥(commV (Subgroup.zpowers (actTil V₀' W hW ⟨v, hvst⟩))) :=
      rkIdx_fixV_zpowers _
    have hconjμ : mBar (conjSubgroup M h) V₀' W hW = mBar M V₀ V hVc := by
      have hMc : M ≤ Subgroup.normalizer (V : Set G) :=
        le_of_eq c.cex.hyp.h6.normalizer_eq.symm
      have hM₀c : M ≤ Subgroup.normalizer (V₀ : Set G) := c.cex.hyp.h6.le_normalizer₀
      change mBar (conjSubgroup M h) (conjSubgroup V₀ h) (conjSubgroup V h)
          (E3.isElemAbelian_conjSubgroup hVc h) = mBar M V₀ V hVc
      exact mBar_conj M V₀ V hVc c.cex.hyp.h6.le hMc hM₀c h
    have hbound := hbnd v hv hvst
    have hle : mBar M V₀ V hVc ≤ E3.mQuot V (U ⊔ V₀) := by
      rw [← hconjμ]
      exact (hmp.trans (le_of_eq hrk)).trans hbound
    exact absurd (lt_of_lt_of_le c.cex.n_lt_mBar hle) (lt_irrefl _)
  have hVW_V₀' : ⁅V, W⁆ ≤ V₀' :=
    Subgroup.commutator_le.2 fun v hv w hw =>
      (actTil_eq_one_iff V₀' W hW ⟨v, hMh_stab (hVleMh hv)⟩).1 (htriv v hv) w hw
  have hbot : V₀ ⊓ V₀' = ⊥ := by
    change V₀ ⊓ conjSubgroup V₀ h = ⊥
    rw [inf_comm]
    exact c.cex.hyp.conj_inf_eq_bot hhM
  have hVW_V₀ : ⁅V, W⁆ ≤ V₀ := by
    rw [Subgroup.commutator_comm V W]
    exact hWV_le_V₀
  have hUW : ⁅U, W⁆ = ⊥ := by
    refine le_bot_iff.1 ?_
    calc ⁅U, W⁆ ≤ ⁅V, W⁆ := Subgroup.commutator_mono c.cex.le le_rfl
      _ ≤ V₀ ⊓ V₀' := le_inf hVW_V₀ hVW_V₀'
      _ = ⊥ := hbot
  exact hcommUW_ne (show ⁅U, conjSubgroup V h⁆ = ⊥ from hUW)

theorem mBar_le_two_mul_mQuot (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G)
    (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) {h : G} (hh : h ∈ H) (hhM : h ∉ M)
    (hP : IsPGroup 2 ↥(Mo.img (V ⊔ conjSubgroup V h))) :
    mBar M V₀ V c.cex.hyp.h6.elemAbelian ≤ 2 * E3.mQuot V (U ⊔ V₀) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hP1, -, hP3⟩ := comm_of_isPGroup h1 h5 h15 hS c Mo hh hhM hP
  obtain ⟨-, -, -, hWleM⟩ := hP1
  obtain ⟨w, hwW, hwct⟩ := SetLike.not_le_iff_exists.1 hP3
  have hVc : IsElemAbelian 2 V := c.cex.hyp.h6.elemAbelian
  have hMnormV : M ≤ Subgroup.normalizer (V : Set G) :=
    le_of_eq c.cex.hyp.h6.normalizer_eq.symm
  have hMstab : M ≤ stabTil V₀ V := le_stabTil hMnormV c.cex.hyp.h6.le_normalizer₀
  have hwM : w ∈ M := hWleM hwW
  have hwst : w ∈ stabTil V₀ V := hMstab hwM
  have hne : actTil V₀ V hVc ⟨w, hwst⟩ ≠ 1 := by
    intro h1'
    exact hwct ((mem_cTilde_iff hVc hMnormV).2 ⟨hwM, ⟨hwst, h1'⟩⟩)
  have hWab : IsElemAbelian 2 (conjSubgroup V h) := E3.isElemAbelian_conjSubgroup hVc h
  have hsqSt : (⟨w, hwst⟩ : stabTil V₀ V) * ⟨w, hwst⟩ = 1 := by
    apply Subtype.ext
    show w * w = 1
    simpa [pow_two] using hWab.2 w hwW
  have hA1 : Subgroup.zpowers (actTil V₀ V hVc ⟨w, hwst⟩) ≠ ⊥ := by
    intro hbot
    refine hne ?_
    have hmemz := Subgroup.mem_zpowers (actTil V₀ V hVc ⟨w, hwst⟩)
    rw [hbot] at hmemz
    exact Subgroup.mem_bot.1 hmemz
  have hsq : actTil V₀ V hVc ⟨w, hwst⟩ * actTil V₀ V hVc ⟨w, hwst⟩ = 1 := by
    rw [← map_mul, hsqSt, map_one]
  have hAp : IsPGroup 2 (Subgroup.zpowers (actTil V₀ V hVc ⟨w, hwst⟩)) := by
    have ho2 : orderOf (actTil V₀ V hVc ⟨w, hwst⟩) ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.2 (by rw [pow_two]; exact hsq)
    rcases (Nat.dvd_prime Nat.prime_two).1 ho2 with ho1 | ho2'
    · exact absurd (orderOf_eq_one_iff.1 ho1) hne
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ho2', pow_one])
  have hmem : actTil V₀ V hVc ⟨w, hwst⟩ ∈ Mbar M V₀ V hVc :=
    actTil_mem_barSub V₀ V hVc hwM hwst
  have hAle : Subgroup.zpowers (actTil V₀ V hVc ⟨w, hwst⟩) ≤ Mbar M V₀ V hVc :=
    Subgroup.zpowers_le.2 hmem
  have hmp : mBar M V₀ V hVc ≤
      rkIdx (fixV (Subgroup.zpowers (actTil V₀ V hVc ⟨w, hwst⟩))) :=
    E3.mParam_le_rkIdx_fixV hAle hAp hA1
  set C : Subgroup G := preTil V₀ V hVc
    (fixV (Subgroup.zpowers (actTil V₀ V hVc ⟨w, hwst⟩))) with hCdef
  have hlow : mBar M V₀ V hVc ≤ E3.mQuot V C := by
    rw [hCdef, mQuot_preTil]
    exact hmp
  have hB := mQuot_sup_inf_centralizer_le h1 h5 h15 hS c hh hhM hwM hwW
  have hCeq := preTil_fixV_inf_sup_eq_centralizer h1 h5 h15 hS c hh hhM hwM hwW hwst
  have hU'V : U ⊔ V₀ ≤ V := sup_le c.cex.le c.cex.hyp.h6.le
  have hupper : E3.mQuot V C ≤ 2 * E3.mQuot V (U ⊔ V₀) := by
    have hstep1 : E3.mQuot V C ≤ E3.mQuot V (C ⊓ (U ⊔ V₀)) :=
      E3.mQuot_mono (inf_le_left : C ⊓ (U ⊔ V₀) ≤ C)
    have hstep2 : E3.mQuot V (C ⊓ (U ⊔ V₀)) =
        E3.mQuot (U ⊔ V₀) (C ⊓ (U ⊔ V₀)) + E3.mQuot V (U ⊔ V₀) :=
      E3.mQuot_add (inf_le_right : C ⊓ (U ⊔ V₀) ≤ U ⊔ V₀) hU'V
    have hstep3 : E3.mQuot (U ⊔ V₀) (C ⊓ (U ⊔ V₀)) ≤ E3.mQuot V (U ⊔ V₀) := by
      rw [hCdef, hCeq]
      exact hB
    omega
  exact hlow.trans hupper

theorem mem_of_conjSubgroup_le_sup (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G)
    (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B) {P : Subgroup G} (hP : IsSylowIn 2 P H)
    (hRP : R ≤ P) (hμ : 2 * E3.mQuot V (U ⊔ V₀) < mBar M V₀ V c.cex.hyp.h6.elemAbelian) {h : G}
    (hh : h ∈ H)
    (hle : conjSubgroup V h ≤ P ⊔ (H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G))) :
    h ∈ M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Mo⟩ := exists_modDataE (Fam16Q.isElemAbelian c.cex c.mem)
    (le_normalizer_conjClosure (U ⊔ V₀) H)
  obtain ⟨c₀, hc₀CH, hc₀P⟩ :=
    exists_mem_inf_centralizer_conjSubgroup_le h1 h5 h15 hS c hP hRP hle
  have hc₀H : c₀ ∈ H := hc₀CH.1
  have hhc₀H : h * c₀ ∈ H := H.mul_mem hh hc₀H
  have hVleP : V ≤ P := c.V_le_R.trans hRP
  have h2g : IsPGroup 2 ↥(Mo.img (V ⊔ conjSubgroup V (h * c₀))) := by
    have hsupP : V ⊔ conjSubgroup V (h * c₀) ≤ P := sup_le hVleP hc₀P
    have himgP : Mo.img (V ⊔ conjSubgroup V (h * c₀)) ≤ Mo.img P := Mo.img_mono hsupP
    exact (Mo.isPGroup_img hP.isPGroup).to_le himgP
  have hhc₀M : h * c₀ ∈ M := by
    by_contra hnot
    have hmb := mBar_le_two_mul_mQuot h1 h5 h15 hS c Mo hhc₀H hnot h2g
    exact absurd (lt_of_lt_of_le hμ hmb) (lt_irrefl _)
  have hc₀M : c₀ ∈ M := by
    have hmem := Cex16.centralizer_conjClosure_le_conj c.cex hc₀CH.2 (Subgroup.one_mem H)
    rwa [conjSubgroup_one] at hmem
  have heq : (h * c₀) * c₀⁻¹ = h := by group
  rw [← heq]
  exact M.mul_mem hhc₀M (M.inv_mem hc₀M)

end Certified

end Cfg1620

end CFSG.LocalAnalysis.WeakClosure81
