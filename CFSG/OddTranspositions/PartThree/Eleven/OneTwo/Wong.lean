module

public import CFSG.OddTranspositions.PartThree.Eleven.Statements
public import CFSG.OddTranspositions.PartThree.Eleven.OneOne.Hyp
public import CFSG.OddTranspositions.PartThree.Eleven.Minus.Pair
public import CFSG.OddTranspositions.PartThree.Eleven.Minus.Quandle
public import CFSG.OddTranspositions.PartThree.EightFive.KBarSetup
public import Certificates.Certificate2326
public import CFSG.OddTranspositions.PartThree.Eleven.OneTwo.KCover
public import CFSG.OddTranspositions.PartThree.Eleven.OneTwo.Index

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ

section Wong

variable {G : Type} [Group G] [Finite G] {D : Set G}

namespace ElevenTwoFrame

variable {hC : HypothesisC D} {S : Sylow 2 G} {T : Sylow 2 (Halpha D hC.alpha)}
  {r : Fin 3 → Halpha D hC.alpha}

private theorem Halpha_commute_d (x : Halpha D hC.alpha) : Commute (x : G) hC.d := by
  have h : Commute hC.d (x : G) := by
    refine Subgroup.closure_induction (p := fun y _ => Commute hC.d y) ?_ ?_ ?_ ?_ x.2
    · intro y hy
      exact (hC.DalphaStar_subset_commute hy).2.symm
    · exact Commute.one_right hC.d
    · intro y z _ _ hy hz
      exact hy.mul_right hz
    · intro y _ hy
      exact hy.inv_right
  exact h.symm

private theorem frameT_commute_d : Commute (frameT hC r) hC.d := by
  have h0 := Halpha_commute_d (r 0)
  have h1 := Halpha_commute_d (r 1)
  have h2 := Halpha_commute_d (r 2)
  simpa only [frameT, Subgroup.coe_mul] using (h0.mul_left h1).mul_left h2

private theorem frameE_commute_d : Commute hC.d (frameE hC r) :=
  (Commute.refl hC.d).mul_right frameT_commute_d.symm

private theorem frame_mem_Dstar (hF : ElevenTwoFrame hC S T r) (i : Fin 3) :
    r i ∈ DstarH hC := by
  have hri : r i ∈ (((T : Subgroup (Halpha D hC.alpha)) : Set (Halpha D hC.alpha)) ∩
      DstarH hC) := by
    rw [hF.frame.inter_eq]
    exact Set.mem_range_self i
  exact hri.2

theorem frameE_mem_commutator (h : ElevenTwoHyp hC) (hF : ElevenTwoFrame hC S T r) :
    frameE hC r ∈ commutator G := by
  have hrmem : ∀ i : Fin 3, ((r i : Halpha D hC.alpha) : G) ∈ D :=
    fun i => DalphaStar_subset hC.isBlock_alpha
      ((mem_DstarH_iff hC).mp (frame_mem_Dstar hF i))
  have h1 : hC.d * ((r 0 : Halpha D hC.alpha) : G) ∈ commutator G :=
    Setup.mul_mem_commutator hC.setup hC.hd (hrmem 0)
  have h2 : ((r 1 : Halpha D hC.alpha) : G) * ((r 2 : Halpha D hC.alpha) : G) ∈
      commutator G :=
    Setup.mul_mem_commutator hC.setup (hrmem 1) (hrmem 2)
  have heq : frameE hC r = (hC.d * ((r 0 : Halpha D hC.alpha) : G)) *
      (((r 1 : Halpha D hC.alpha) : G) * ((r 2 : Halpha D hC.alpha) : G)) := by
    simp only [frameE, frameT, Subgroup.coe_mul]
    group
  rw [heq]
  exact (commutator G).mul_mem h1 h2

theorem exists_conj_commute (h : ElevenTwoHyp hC) (hF : ElevenTwoFrame hC S T r) :
    ∃ g ∈ commutator G, g * frameE hC r * g⁻¹ ≠ frameE hC r ∧
      Commute (frameE hC r) (g * frameE hC r * g⁻¹) := by
  obtain ⟨x, hxne, hxcomm⟩ := hF.frame.conj_commute
  have hxG : Commute (x : G) hC.d := Halpha_commute_d x
  have htG : Commute (frameT hC r) hC.d := frameT_commute_d
  have htyG : Commute (frameT hC r) ((x : G) * frameT hC r * (x : G)⁻¹) := by
    rw [commute_iff_eq] at hxcomm ⊢
    have h := congrArg (Subtype.val : Halpha D hC.alpha → G) hxcomm
    simpa only [frameT, Subgroup.coe_mul, Subgroup.coe_inv] using h
  have hy_ne : (x : G) * frameT hC r * (x : G)⁻¹ ≠ frameT hC r := by
    intro hy
    apply hxne
    apply Subtype.ext
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, frameT] using hy
  have huy : Commute hC.d ((x : G) * frameT hC r * (x : G)⁻¹) :=
    (hxG.symm.mul_right htG.symm).mul_right hxG.symm.inv_right
  have heq_x : (x : G) * frameE hC r * (x : G)⁻¹ =
      hC.d * ((x : G) * frameT hC r * (x : G)⁻¹) := by
    simp only [frameE]
    calc (x : G) * (hC.d * frameT hC r) * (x : G)⁻¹
        = ((x : G) * hC.d) * frameT hC r * (x : G)⁻¹ := by group
      _ = (hC.d * (x : G)) * frameT hC r * (x : G)⁻¹ := by rw [hxG.eq]
      _ = hC.d * ((x : G) * frameT hC r * (x : G)⁻¹) := by group
  have hne : hC.d * ((x : G) * frameT hC r * (x : G)⁻¹) ≠ frameE hC r := by
    intro hd
    apply hy_ne
    exact mul_left_cancel (by rw [hd, frameE])
  have hcomm : Commute (frameE hC r) (hC.d * ((x : G) * frameT hC r * (x : G)⁻¹)) := by
    have h1 : Commute (hC.d * frameT hC r) hC.d :=
      (Commute.refl hC.d).mul_left htG
    have h2 : Commute (hC.d * frameT hC r) ((x : G) * frameT hC r * (x : G)⁻¹) :=
      huy.mul_left htyG
    simpa only [frameE] using h1.mul_right h2
  have hde : Commute hC.d (frameE hC r) := (Commute.refl hC.d).mul_right htG.symm
  have hded : hC.d * frameE hC r * hC.d⁻¹ = frameE hC r := by
    rw [hde.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hu_not : hC.d ∉ commutator G := h.not_mem_commutator hC.d hC.hd
  have hdec : (x : G) ∈ commutator G ∨ (x : G) * hC.d ∈ commutator G := by
    by_cases hx : (x : G) ∈ commutator G
    · exact Or.inl hx
    · right
      rw [Subgroup.mul_mem_iff_of_index_two h.index_commutator]
      exact iff_of_false hx hu_not
  rcases hdec with hxg | hxug
  · exact ⟨(x : G), hxg, by rw [heq_x]; exact hne, by rw [heq_x]; exact hcomm⟩
  · have hg : ((x : G) * hC.d) * frameE hC r * ((x : G) * hC.d)⁻¹ =
        hC.d * ((x : G) * frameT hC r * (x : G)⁻¹) := by
      calc ((x : G) * hC.d) * frameE hC r * ((x : G) * hC.d)⁻¹
          = (x : G) * (hC.d * frameE hC r * hC.d⁻¹) * (x : G)⁻¹ := by group
        _ = (x : G) * frameE hC r * (x : G)⁻¹ := by rw [hded]
        _ = hC.d * ((x : G) * frameT hC r * (x : G)⁻¹) := heq_x
    exact ⟨(x : G) * hC.d, hxug, by rw [hg]; exact hne, by rw [hg]; exact hcomm⟩

theorem centralizer_sup_oddCore_ne_top (h : ElevenTwoHyp hC) (hF : ElevenTwoFrame hC S T r) :
    Subgroup.centralizer {(⟨frameE hC r, hF.frameE_mem_commutator h⟩ : ↥(commutator G))} ⊔
      CFSG.oddCore ↥(commutator G) ≠ ⊤ := by
  intro hsup
  obtain ⟨g, hg, hgne, hgcomm⟩ := exists_conj_commute h hF
  let e : ↥(commutator G) := ⟨frameE hC r, hF.frameE_mem_commutator h⟩
  let C : Subgroup ↥(commutator G) := Subgroup.centralizer {e}
  let O : Subgroup ↥(commutator G) := CFSG.oddCore ↥(commutator G)
  haveI : O.Normal := inferInstance
  let g' : ↥(commutator G) := ⟨g, hg⟩
  have hgmem : g' ∈ O ⊔ C := by
    rw [sup_comm, hsup]
    exact Subgroup.mem_top g'
  rw [Subgroup.mem_sup_of_normal_left] at hgmem
  obtain ⟨o, ho, c, hc, hoc⟩ := hgmem
  have hce : c * e * c⁻¹ = e := by
    have h1 := (Subgroup.mem_centralizer_iff.mp hc) e (Set.mem_singleton e)
    rw [← h1, mul_assoc, mul_inv_cancel, mul_one]
  have he'_eq : g' * e * g'⁻¹ = o * e * o⁻¹ := by
    rw [← hoc]
    calc (o * c) * e * (o * c)⁻¹ = o * (c * e * c⁻¹) * o⁻¹ := by group
      _ = o * e * o⁻¹ := by rw [hce]
  have he2 : e * e = 1 := by
    have h2 : orderOf e = 2 := by
      rw [Subgroup.orderOf_mk]
      exact hF.orderOf_frameE h
    have := pow_orderOf_eq_one e
    rwa [h2, pow_two] at this
  have he_inv : e⁻¹ = e := inv_eq_of_mul_eq_one_left he2
  have hmem : e * (g' * e * g'⁻¹) ∈ O := by
    rw [he'_eq]
    have hconj : e * o * e⁻¹ ∈ O := (inferInstance : O.Normal).conj_mem o ho e
    have h1 : (e * o * e⁻¹) * o⁻¹ ∈ O := O.mul_mem hconj (O.inv_mem ho)
    convert h1 using 1
    rw [he_inv]
    group
  have he'2 : (g' * e * g'⁻¹) * (g' * e * g'⁻¹) = 1 := by
    calc (g' * e * g'⁻¹) * (g' * e * g'⁻¹) = g' * (e * e) * g'⁻¹ := by group
      _ = 1 := by rw [he2]; group
  have hcomm' : Commute e (g' * e * g'⁻¹) := by
    rw [commute_iff_eq]
    apply Subtype.ext
    change frameE hC r * (g * frameE hC r * g⁻¹) =
      (g * frameE hC r * g⁻¹) * frameE hC r
    exact hgcomm.eq
  have hne' : g' * e * g'⁻¹ ≠ e := by
    intro hEq
    apply hgne
    have := congrArg Subtype.val hEq
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this
  have hsq : (e * (g' * e * g'⁻¹)) * (e * (g' * e * g'⁻¹)) = 1 := by
    have h3 := hcomm'.mul_pow 2
    rw [pow_two, pow_two, pow_two] at h3
    rw [h3, he2, he'2, mul_one]
  have hne1 : e * (g' * e * g'⁻¹) ≠ 1 := by
    intro h1
    apply hne'
    have h2 : g' * e * g'⁻¹ = e := by
      apply mul_left_cancel (a := e)
      rw [h1, he2]
    exact h2
  have horder : orderOf (e * (g' * e * g'⁻¹)) = 2 :=
    orderOf_eq_prime (by rwa [pow_two]) hne1
  exact CFSG.Adapters.not_mem_oddCore_of_orderOf_eq_two horder hmem

theorem not_isConj_commutator (h : ElevenTwoHyp hC) (hF : ElevenTwoFrame hC S T r) :
    ∃ a b : ↥(commutator G), orderOf a = 2 ∧ orderOf b = 2 ∧ ¬ IsConj a b := by
  have hr0Dstar : ((r 0 : Halpha D hC.alpha) : G) ∈ DalphaStar D hC.alpha :=
    (mem_DstarH_iff hC).mp (frame_mem_Dstar hF 0)
  have hr0D : ((r 0 : Halpha D hC.alpha) : G) ∈ D :=
    DalphaStar_subset hC.isBlock_alpha hr0Dstar
  have hr0G : orderOf ((r 0 : Halpha D hC.alpha) : G) = 2 :=
    hC.setup.oddT.1 _ hr0D
  have hcomm_ur0 : Commute hC.d ((r 0 : Halpha D hC.alpha) : G) :=
    (hC.DalphaStar_subset_commute hr0Dstar).2.symm
  have hu2 : hC.d * hC.d = 1 := by
    have hh := pow_orderOf_eq_one hC.d
    rwa [hC.setup.oddT.1 hC.d hC.hd, pow_two] at hh
  have hr02 : ((r 0 : Halpha D hC.alpha) : G) * ((r 0 : Halpha D hC.alpha) : G) = 1 := by
    have hh := pow_orderOf_eq_one ((r 0 : Halpha D hC.alpha) : G)
    rwa [hr0G, pow_two] at hh
  have hne_ur0 : hC.d ≠ ((r 0 : Halpha D hC.alpha) : G) := by
    intro heq
    have hr0E : ((r 0 : Halpha D hC.alpha) : G) ∈ hC.E := by
      rw [← hC.DalphaStar_alpha]
      exact hr0Dstar
    have hd_notE : hC.d ∉ hC.E := by
      have hd := hC.d_mem_alpha
      rw [hC.alpha_eq_normSet_diff] at hd
      exact hd.2
    exact hd_notE (heq ▸ hr0E)
  have hsq : (hC.d * ((r 0 : Halpha D hC.alpha) : G)) *
      (hC.d * ((r 0 : Halpha D hC.alpha) : G)) = 1 := by
    have hh := hcomm_ur0.mul_pow 2
    rw [pow_two, pow_two, pow_two] at hh
    rw [hh, hu2, hr02, mul_one]
  have hne1 : hC.d * ((r 0 : Halpha D hC.alpha) : G) ≠ 1 := by
    intro h1
    apply hne_ur0
    have h2 : ((r 0 : Halpha D hC.alpha) : G) = hC.d⁻¹ := eq_inv_of_mul_eq_one_right h1
    have h3 : hC.d⁻¹ = hC.d := inv_eq_of_mul_eq_one_left hu2
    rw [h2, h3]
  have horder_a : orderOf (hC.d * ((r 0 : Halpha D hC.alpha) : G)) = 2 :=
    orderOf_eq_prime (by rwa [pow_two]) hne1
  refine ⟨⟨hC.d * ((r 0 : Halpha D hC.alpha) : G),
      Setup.mul_mem_commutator hC.setup hC.hd hr0D⟩,
    ⟨frameE hC r, hF.frameE_mem_commutator h⟩, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_mk]
    exact horder_a
  · rw [Subgroup.orderOf_mk]
    exact hF.orderOf_frameE h
  · rintro ⟨g, hg⟩
    have hgG : (g : G) * (hC.d * ((r 0 : Halpha D hC.alpha) : G)) * (g : G)⁻¹ =
        frameE hC r := by
      have h := congrArg Subtype.val hg.eq
      simp only [Subgroup.coe_mul] at h
      calc (g : G) * (hC.d * ((r 0 : Halpha D hC.alpha) : G)) * (g : G)⁻¹
          = (frameE hC r * (g : G)) * (g : G)⁻¹ := by rw [h]
        _ = frameE hC r := by group
    let c : G := (g : G) * hC.d * (g : G)⁻¹
    let d : G := (g : G) * ((r 0 : Halpha D hC.alpha) : G) * (g : G)⁻¹
    have hcD : c ∈ D := hC.setup.conj_mem (g : G) hC.hd
    have hdD : d ∈ D := hC.setup.conj_mem (g : G) hr0D
    have hcomm_cd : Commute c d := by
      show Commute ((g : G) * hC.d * (g : G)⁻¹)
        ((g : G) * ((r 0 : Halpha D hC.alpha) : G) * (g : G)⁻¹)
      rw [commute_iff_eq]
      calc (g : G) * hC.d * (g : G)⁻¹ *
            ((g : G) * ((r 0 : Halpha D hC.alpha) : G) * (g : G)⁻¹)
          = (g : G) * (hC.d * ((r 0 : Halpha D hC.alpha) : G)) * (g : G)⁻¹ := by group
        _ = (g : G) * (((r 0 : Halpha D hC.alpha) : G) * hC.d) * (g : G)⁻¹ := by
              rw [hcomm_ur0.eq]
        _ = (g : G) * ((r 0 : Halpha D hC.alpha) : G) * (g : G)⁻¹ *
              ((g : G) * hC.d * (g : G)⁻¹) := by group
    have hcd : c * d = frameE hC r := by
      show ((g : G) * hC.d * (g : G)⁻¹) *
          ((g : G) * ((r 0 : Halpha D hC.alpha) : G) * (g : G)⁻¹) = frameE hC r
      calc ((g : G) * hC.d * (g : G)⁻¹) *
            ((g : G) * ((r 0 : Halpha D hC.alpha) : G) * (g : G)⁻¹)
          = (g : G) * (hC.d * ((r 0 : Halpha D hC.alpha) : G)) * (g : G)⁻¹ := by group
        _ = frameE hC r := hgG
    have hc_cent : c ∈ centSet D (frameE hC r) :=
      ⟨hcD, hcd ▸ (Commute.refl c).mul_right hcomm_cd⟩
    have hd_cent : d ∈ centSet D (frameE hC r) :=
      ⟨hdD, hcd ▸ hcomm_cd.symm.mul_right (Commute.refl d)⟩
    have hd2G : d * d = 1 := by
      show ((g : G) * ((r 0 : Halpha D hC.alpha) : G) * (g : G)⁻¹) *
          ((g : G) * ((r 0 : Halpha D hC.alpha) : G) * (g : G)⁻¹) = 1
      calc ((g : G) * ((r 0 : Halpha D hC.alpha) : G) * (g : G)⁻¹) *
            ((g : G) * ((r 0 : Halpha D hC.alpha) : G) * (g : G)⁻¹)
          = (g : G) * (((r 0 : Halpha D hC.alpha) : G) *
              ((r 0 : Halpha D hC.alpha) : G)) * (g : G)⁻¹ := by group
        _ = 1 := by rw [hr02]; group
    let K : Subgroup G := localGroup D (frameE hC r)
    let R : Subgroup K := CFSG.solvableRadical K
    have heR : (⟨frameE hC r, hF.frameE_mem_localGroup h⟩ : K) ∈ R := by
      have hmem : frameE hC r ∈ (CFSG.solvableRadical K).map K.subtype := by
        rw [hF.solvableRadical_localGroup h]
        exact Subgroup.mem_zpowers (frameE hC r)
      obtain ⟨x, hx, hxval⟩ := hmem
      have hxeq : x = (⟨frameE hC r, hF.frameE_mem_localGroup h⟩ : K) := Subtype.ext hxval
      rwa [hxeq] at hx
    have hcd_eq : (⟨c, mem_localGroup_of_mem hc_cent⟩ : K) =
        ⟨d, mem_localGroup_of_mem hd_cent⟩ := by
      apply hF.injOn_kbar h
      · exact hc_cent
      · exact hd_cent
      · have hprod : QuotientGroup.mk' R (⟨c, mem_localGroup_of_mem hc_cent⟩ : K) *
            QuotientGroup.mk' R (⟨d, mem_localGroup_of_mem hd_cent⟩ : K) = 1 := by
          rw [← map_mul]
          have h1 : (⟨c, mem_localGroup_of_mem hc_cent⟩ : K) *
              ⟨d, mem_localGroup_of_mem hd_cent⟩ =
              ⟨frameE hC r, hF.frameE_mem_localGroup h⟩ := by
            apply Subtype.ext
            simpa only [Subgroup.coe_mul] using hcd
          rw [h1]
          exact (QuotientGroup.eq_one_iff _).mpr heR
        have hd2 : QuotientGroup.mk' R (⟨d, mem_localGroup_of_mem hd_cent⟩ : K) *
            QuotientGroup.mk' R (⟨d, mem_localGroup_of_mem hd_cent⟩ : K) = 1 := by
          rw [← map_mul]
          have h1 : (⟨d, mem_localGroup_of_mem hd_cent⟩ : K) *
              ⟨d, mem_localGroup_of_mem hd_cent⟩ = 1 := by
            apply Subtype.ext
            simpa only [Subgroup.coe_mul, Subgroup.coe_one] using hd2G
          rw [h1, map_one]
        calc QuotientGroup.mk' R (⟨c, mem_localGroup_of_mem hc_cent⟩ : K)
            = (QuotientGroup.mk' R (⟨d, mem_localGroup_of_mem hd_cent⟩ : K))⁻¹ :=
              eq_inv_of_mul_eq_one_left hprod
          _ = QuotientGroup.mk' R (⟨d, mem_localGroup_of_mem hd_cent⟩ : K) :=
              inv_eq_of_mul_eq_one_right hd2
    have hc_eq_d : c = d := congrArg Subtype.val hcd_eq
    have hc_eq_d' : (g : G) * hC.d * (g : G)⁻¹ =
        (g : G) * ((r 0 : Halpha D hC.alpha) : G) * (g : G)⁻¹ := hc_eq_d
    apply hne_ur0
    calc hC.d = (g : G)⁻¹ * ((g : G) * hC.d * (g : G)⁻¹) * (g : G) := by group
      _ = (g : G)⁻¹ * ((g : G) * ((r 0 : Halpha D hC.alpha) : G) * (g : G)⁻¹) *
            (g : G) := by rw [hc_eq_d']
      _ = ((r 0 : Halpha D hC.alpha) : G) := by group

end ElevenTwoFrame

theorem ElevenTwoHyp.statedClassicalModel_commutator (h91 : Theorem9_1) (hW : WongPSp4Five)
    {hC : HypothesisC D} (h : ElevenTwoHyp hC) :
    CFSG.Open.StatedClassicalModel ↥(commutator G) .PSp 2 5 1 := by
  obtain ⟨S, T, r, hF⟩ := h.exists_frame
  obtain ⟨L₁, L₂, hL1e, hL2e, hcomm, hinf, hleK, hleG', hcardK⟩ := hF.exists_sl25 h91 h
  have hcardC := hF.card_centralizer_e h91 h
  have hidx := h.index_commutator
  let e : ↥(commutator G) := ⟨frameE hC r, hF.frameE_mem_commutator h⟩
  let L₁' : Subgroup ↥(commutator G) := L₁.subgroupOf (commutator G)
  let L₂' : Subgroup ↥(commutator G) := L₂.subgroupOf (commutator G)
  set B : Subgroup G := L₁ ⊔ L₂ with hBdef
  set C : Subgroup G := Subgroup.centralizer ({frameE hC r} : Set G) with hCdef
  have hB_le_C : B ≤ C := by
    rw [hBdef, hCdef]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact (commute_of_mem_localGroup (hleK hx)).eq.symm
  have hB_le_G' : B ≤ commutator G := by rw [hBdef]; exact hleG'
  have hL1'e : Nonempty (L₁' ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) :=
    hL1e.map fun f => (Subgroup.subgroupOfEquivOfLe (le_sup_left.trans hleG')).trans f
  have hL2'e : Nonempty (L₂' ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) :=
    hL2e.map fun f => (Subgroup.subgroupOfEquivOfLe (le_sup_right.trans hleG')).trans f
  have hcomm' : ∀ a ∈ L₁', ∀ b ∈ L₂', Commute a b := by
    intro a ha b hb
    rw [commute_iff_eq]
    apply Subtype.ext
    change (a : G) * (b : G) = (b : G) * (a : G)
    exact (hcomm (a : G) ha (b : G) hb).eq
  have hinf' : L₁' ⊓ L₂' = Subgroup.zpowers e := by
    have h1 : L₁' ⊓ L₂' = (L₁ ⊓ L₂).subgroupOf (commutator G) := by
      show L₁.subgroupOf (commutator G) ⊓ L₂.subgroupOf (commutator G) =
        (L₁ ⊓ L₂).subgroupOf (commutator G)
      rw [Subgroup.subgroupOf, Subgroup.subgroupOf, Subgroup.subgroupOf, Subgroup.comap_inf]
    rw [h1, hinf]
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, Subtype.ext (by simpa using hn)⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  have he2 : orderOf e = 2 := by
    show orderOf (⟨frameE hC r, hF.frameE_mem_commutator h⟩ : ↥(commutator G)) = 2
    rw [Subgroup.orderOf_mk]
    exact hF.orderOf_frameE h
  have htop' : Subgroup.centralizer ({e} : Set ↥(commutator G)) ⊔
      CFSG.oddCore ↥(commutator G) ≠ ⊤ := hF.centralizer_sup_oddCore_ne_top h
  have hrel' : (L₁' ⊔ L₂').relIndex (Subgroup.centralizer ({e} : Set ↥(commutator G))) = 2 := by
    have hB'eq : L₁' ⊔ L₂' = B.subgroupOf (commutator G) := by
      rw [hBdef]
      show L₁.subgroupOf (commutator G) ⊔ L₂.subgroupOf (commutator G) =
        (L₁ ⊔ L₂).subgroupOf (commutator G)
      exact (Subgroup.subgroupOf_sup (le_sup_left.trans hleG')
        (le_sup_right.trans hleG')).symm
    have hC'eq : Subgroup.centralizer ({e} : Set ↥(commutator G)) =
        C.subgroupOf (commutator G) := by
      rw [hCdef]
      show Subgroup.centralizer ({e} : Set ↥(commutator G)) =
        (Subgroup.centralizer ({frameE hC r} : Set G)).subgroupOf (commutator G)
      ext x
      simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq,
        Subgroup.mem_subgroupOf]
      constructor
      · intro hx
        simpa only [Subgroup.coe_mul] using congrArg Subtype.val hx
      · intro hx
        exact Subtype.ext (by simpa only [Subgroup.coe_mul] using hx)
    rw [hB'eq, hC'eq]
    have hrelC : (commutator G).relIndex C = 2 := by
      rw [Subgroup.relIndex_eq_two_iff_exists_notMem_and]
      refine ⟨hC.d, ?_, h.not_mem_commutator hC.d hC.hd, ?_⟩
      · rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact Commute.eq ElevenTwoFrame.frameE_commute_d.symm
      · intro b hbC
        rw [Subgroup.mul_mem_iff_of_index_two hidx]
        by_cases hb : b ∈ commutator G
        · exact Or.inr hb
        · exact Or.inl (iff_of_false hb (h.not_mem_commutator hC.d hC.hd))
    have hcardCinf : Nat.card (C ⊓ commutator G : Subgroup G) =
        Nat.card (localGroup D (frameE hC r)) := by
      have h := Subgroup.relIndex_mul_card (H := commutator G) (K := C)
      rw [hrelC, hcardC] at h
      rw [inf_comm] at h
      omega
    have hcardC' : Nat.card (C.subgroupOf (commutator G)) =
        Nat.card (localGroup D (frameE hC r)) := by
      rw [← Subgroup.inf_subgroupOf_right (H := C) (K := commutator G)]
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right)).toEquiv]
      exact hcardCinf
    have hcardB' : Nat.card (B.subgroupOf (commutator G)) = Nat.card B :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB_le_G').toEquiv
    have hcardK' : Nat.card (localGroup D (frameE hC r)) = 2 * Nat.card B := by
      rw [hBdef]
      exact hcardK
    have hB'_le_C' : B.subgroupOf (commutator G) ≤ C.subgroupOf (commutator G) :=
      Subgroup.subgroupOf_mono (commutator G) hB_le_C
    have hrel := Subgroup.relIndex_mul_card (H := B.subgroupOf (commutator G))
      (K := C.subgroupOf (commutator G))
    rw [inf_eq_left.mpr hB'_le_C', hcardC', hcardB', hcardK'] at hrel
    have hBpos : 0 < Nat.card B := by
      have hKne : Nat.card (localGroup D (frameE hC r)) ≠ 0 :=
        Nat.card_ne_zero.mpr ⟨⟨⟨frameE hC r, hF.frameE_mem_localGroup h⟩⟩, inferInstance⟩
      have hBne : Nat.card B ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hcardK'
        exact hKne hcardK'
      exact Nat.pos_of_ne_zero hBne
    exact Nat.mul_right_cancel hBpos hrel
  rcases hW ↥(commutator G) e L₁' L₂' he2 hL1'e hL2'e hcomm' hinf' hrel' htop' with
    hclass | hmodel
  · obtain ⟨a, b, ha2, hb2, hnab⟩ := ElevenTwoFrame.not_isConj_commutator h hF
    exact (hnab (hclass.1 a b ha2 hb2)).elim
  · exact hmodel

end Wong

end CFSG.OddTranspositions.PartThree
