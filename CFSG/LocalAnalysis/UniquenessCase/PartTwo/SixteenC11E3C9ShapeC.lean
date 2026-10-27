module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3C9ShapeB
public import CFSG.GH74.GLS.Stage1.Main.NoFAutProof

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

theorem s1611e3_shape_of_normal_solvable_quotient {P : Type} [Group P] [Finite P]
    {R Ehat : Subgroup P} [R.Normal] [Ehat.Normal] (hRE : R ≤ Ehat)
    (hRsol : Group.IsSolvable ↥R) (hPE : Group.IsSolvable (P ⧸ Ehat))
    {L : Type} [Group L] [Finite L] (hL : IsL3 L 1)
    (f : L × L →* (↥Ehat ⧸ R.subgroupOf Ehat)) (hf : Function.Surjective f)
    (X : Subgroup P) (hXn : X.Normal) (hXne : X ≠ ⊥)
    (hXmin : ∀ N : Subgroup P, N.Normal → N ≤ X → N = ⊥ ∨ N = X)
    (hXnc : ¬ IsMulCommutative X) :
    ∀ L0 : Subgroup P, CFSG.Open.IsComponentOf L0 X → IsL3 ↥L0 1 := by
  classical
  haveI hLsimple : IsSimpleGroup L := isSimpleGroup_of_isL3 hL
  have hXcomm : ⁅X, X⁆ = X := by
    have hcomm_le : ⁅X, X⁆ ≤ X := Subgroup.commutator_le_left X X
    have hcomm_normal : (⁅X, X⁆).Normal := inferInstance
    rcases hXmin ⁅X, X⁆ hcomm_normal hcomm_le with hbot | htop
    · exfalso
      apply hXnc
      rw [isMulCommutative_iff]
      intro u v
      have hcent : X ≤ Subgroup.centralizer (X : Set P) :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hbot
      have huv : (v : P) * (u : P) = (u : P) * (v : P) :=
        Subgroup.mem_centralizer_iff.mp (hcent u.2) v v.2
      exact Subtype.ext huv.symm
    · exact htop
  have hXperf : Group.IsPerfect ↥X := Subgroup.isPerfect_iff.mpr hXcomm
  have hXleE : X ≤ Ehat :=
    CFSG.GH74.GLS.Stage1.Main.le_of_perfect_of_solvable_quotient_top hPE hXperf
  have hXR : X ⊓ R = ⊥ := by
    have hnormal : (X ⊓ R).Normal := inferInstance
    rcases hXmin (X ⊓ R) hnormal inf_le_left with hbot | htop
    · exact hbot
    · exfalso
      have hXleR : X ≤ R := by rw [← htop]; exact inf_le_right
      haveI := hRsol
      have hXsol : Group.IsSolvable ↥X :=
        Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hXleR)
      haveI : Nontrivial ↥X := (Subgroup.nontrivial_iff_ne_bot X).mpr hXne
      haveI := hXperf
      exact Group.IsPerfect.not_isSolvable ↥X hXsol
  let Xsub : Subgroup ↥Ehat := X.subgroupOf Ehat
  have hXsubn : Xsub.Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hXleE).mpr ?_
    rw [Subgroup.normalizer_eq_top_iff.mpr hXn]
    exact le_top
  let qR : ↥Ehat →* (↥Ehat ⧸ R.subgroupOf Ehat) := QuotientGroup.mk' (R.subgroupOf Ehat)
  let Xbar : Subgroup (↥Ehat ⧸ R.subgroupOf Ehat) := Xsub.map qR
  have hXbarn : Xbar.Normal := hXsubn.map qR (QuotientGroup.mk'_surjective _)
  haveI : Xbar.Normal := hXbarn
  have hXisoXbar : Nonempty (↥X ≃* ↥Xbar) := by
    let fX : ↥Xsub →* ↥Xbar :=
      (qR.comp Xsub.subtype).codRestrict Xbar fun x => Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩
    have hfXsurj : Function.Surjective fX := by
      intro y
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
    have hXker : fX.ker = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [MonoidHom.mem_ker] at hx
      have hx1 : (x : ↥Ehat) ∈ R.subgroupOf Ehat :=
        (QuotientGroup.eq_one_iff (x : ↥Ehat)).mp (congrArg Subtype.val hx)
      have hx2 : (x : ↥Ehat) ∈ Xsub := x.2
      have hxX : ((x : ↥Ehat) : P) ∈ X := Subgroup.mem_subgroupOf.mp hx2
      have hxR : ((x : ↥Ehat) : P) ∈ R := Subgroup.mem_subgroupOf.mp hx1
      have hxXR : ((x : ↥Ehat) : P) ∈ X ⊓ R := Subgroup.mem_inf.mpr ⟨hxX, hxR⟩
      rw [hXR] at hxXR
      have hxone : (x : ↥Ehat) = (1 : ↥Ehat) := Subtype.ext (Subgroup.mem_bot.mp hxXR)
      exact Subtype.ext hxone
    have e1 : ↥Xsub ≃* ↥Xbar :=
      ((QuotientGroup.quotientBot).symm.trans
        ((QuotientGroup.quotientMulEquivOfEq hXker).symm.trans
          (QuotientGroup.quotientKerEquivOfSurjective fX hfXsurj)))
    exact ⟨(Subgroup.subgroupOfEquivOfLe hXleE).symm.trans e1⟩
  have hXbarnc : ¬ IsMulCommutative ↥Xbar := by
    intro h
    apply hXnc
    obtain ⟨eX⟩ := hXisoXbar
    exact (CFSG.SignalizerFunctorTheorem.McBride.isMulCommutative_congr eX).mpr h
  let N' : Subgroup (L × L) := Xbar.comap f
  have hN'n : N'.Normal := hXbarn.comap f
  haveI : N'.Normal := hN'n
  let fN : ↥N' →* ↥Xbar :=
    (f.comp N'.subtype).codRestrict Xbar fun x => Subgroup.mem_comap.mp x.2
  have hfNsurj : Function.Surjective fN := by
    intro y
    obtain ⟨z, hz⟩ := hf y.1
    exact ⟨⟨z, Subgroup.mem_comap.mpr (by rw [hz]; exact y.2)⟩, Subtype.ext hz⟩
  have hXbarQuot : ↥N' ⧸ fN.ker ≃* ↥Xbar :=
    QuotientGroup.quotientKerEquivOfSurjective fN hfNsurj
  have hN'cases := s1611e3_normal_subgroup_prod_l3 (center_eq_bot_of_isL3 hL) N'
  have hXbarClass : Nonempty (↥Xbar ≃* L) ∨ Nonempty (↥Xbar ≃* L × L) := by
    rcases hN'cases with hbot | hL1 | h1L | htop
    · exfalso
      haveI : Subsingleton ↥N' := by rw [hbot]; infer_instance
      haveI : Subsingleton (↥N' ⧸ fN.ker) := inferInstance
      haveI : Subsingleton ↥Xbar := hXbarQuot.symm.injective.subsingleton
      exact hXbarnc (IsMulCommutative.of_comm (fun a b => Subsingleton.elim _ _))
    · left
      have hN'iso : ↥N' ≃* L := by
        rw [hL1]
        exact (Subgroup.prodEquiv (⊤ : Subgroup L) (⊥ : Subgroup L)).trans
          (MulEquiv.prodUnique.trans Subgroup.topEquiv)
      haveI : IsSimpleGroup ↥N' := hN'iso.isSimpleGroup_congr.mpr (isSimpleGroup_of_isL3 hL)
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal fN.ker with hK | hK
      · refine ⟨hXbarQuot.symm.trans ?_⟩
        exact (QuotientGroup.quotientMulEquivOfEq hK).trans
          ((QuotientGroup.quotientBot).trans hN'iso)
      · exfalso
        haveI : Subsingleton (↥N' ⧸ (⊤ : Subgroup ↥N')) :=
          QuotientGroup.subsingleton_quotient_top
        haveI : Subsingleton (↥N' ⧸ fN.ker) :=
          (QuotientGroup.quotientMulEquivOfEq hK).injective.subsingleton
        haveI : Subsingleton ↥Xbar := hXbarQuot.symm.injective.subsingleton
        exact hXbarnc (IsMulCommutative.of_comm (fun a b => Subsingleton.elim _ _))
    · left
      have hN'iso : ↥N' ≃* L := by
        rw [h1L]
        exact (Subgroup.prodEquiv (⊥ : Subgroup L) (⊤ : Subgroup L)).trans
          (MulEquiv.uniqueProd.trans Subgroup.topEquiv)
      haveI : IsSimpleGroup ↥N' := hN'iso.isSimpleGroup_congr.mpr (isSimpleGroup_of_isL3 hL)
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal fN.ker with hK | hK
      · refine ⟨hXbarQuot.symm.trans ?_⟩
        exact (QuotientGroup.quotientMulEquivOfEq hK).trans
          ((QuotientGroup.quotientBot).trans hN'iso)
      · exfalso
        haveI : Subsingleton (↥N' ⧸ (⊤ : Subgroup ↥N')) :=
          QuotientGroup.subsingleton_quotient_top
        haveI : Subsingleton (↥N' ⧸ fN.ker) :=
          (QuotientGroup.quotientMulEquivOfEq hK).injective.subsingleton
        haveI : Subsingleton ↥Xbar := hXbarQuot.symm.injective.subsingleton
        exact hXbarnc (IsMulCommutative.of_comm (fun a b => Subsingleton.elim _ _))
    ·
      have hXbarTop : Xbar = ⊤ := by
        rw [eq_top_iff]
        intro y _
        obtain ⟨z, hz⟩ := hf y
        rw [← hz]
        have hzmem : z ∈ Xbar.comap f := by
          change z ∈ N'
          rw [htop]
          exact Subgroup.mem_top z
        exact Subgroup.mem_comap.mp hzmem
      have eTop : ↥Xbar ≃* (↥Ehat ⧸ R.subgroupOf Ehat) := by
        rw [hXbarTop]
        exact Subgroup.topEquiv
      rcases s1611e3_quotient_prod_l3 (center_eq_bot_of_isL3 hL) (K := f.ker) with hK | h | h
      · exfalso
        haveI : Subsingleton ((L × L) ⧸ (⊤ : Subgroup (L × L))) :=
          QuotientGroup.subsingleton_quotient_top
        haveI : Subsingleton ((L × L) ⧸ f.ker) :=
          (QuotientGroup.quotientMulEquivOfEq hK).injective.subsingleton
        haveI : Subsingleton (↥Ehat ⧸ R.subgroupOf Ehat) :=
          (QuotientGroup.quotientKerEquivOfSurjective f hf).symm.injective.subsingleton
        haveI : Subsingleton ↥Xbar := eTop.injective.subsingleton
        exact hXbarnc (IsMulCommutative.of_comm (fun a b => Subsingleton.elim _ _))
      · obtain ⟨e⟩ := h
        exact Or.inl ⟨eTop.trans ((QuotientGroup.quotientKerEquivOfSurjective f hf).symm.trans e)⟩
      · obtain ⟨e⟩ := h
        exact Or.inr ⟨eTop.trans ((QuotientGroup.quotientKerEquivOfSurjective f hf).symm.trans e)⟩
  obtain ⟨eX⟩ := hXisoXbar
  have hXiso : Nonempty (↥X ≃* L) ∨ Nonempty (↥X ≃* L × L) := by
    rcases hXbarClass with h | h
    · obtain ⟨e⟩ := h
      exact Or.inl ⟨eX.trans e⟩
    · obtain ⟨e⟩ := h
      exact Or.inr ⟨eX.trans e⟩
  intro L0 hL0
  exact s1611e3_components_of_iso_l3_or_sq hL hXiso L0 hL0

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
