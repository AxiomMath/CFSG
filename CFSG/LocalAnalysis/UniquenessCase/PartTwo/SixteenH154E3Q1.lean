module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Q1A
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Std
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154UThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

private theorem s16h_conjSubgroup_le_of_mem {A M : Subgroup G} (hA : A ≤ M) {x : G}
    (hx : x ∈ M) : conjSubgroup A x ≤ M := by
  intro y hy
  rw [mem_conjSubgroup_iff] at hy
  have h1 : x⁻¹ * (x * y * x⁻¹) * x ∈ M := M.mul_mem (M.mul_mem (M.inv_mem hx) (hA hy)) hx
  have e : x⁻¹ * (x * y * x⁻¹) * x = y := by group
  rwa [e] at h1

private theorem s16h_barSub_sup {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    {A B : Subgroup G} (hA : A ≤ stabTil V₀ V) (hB : B ≤ stabTil V₀ V) :
    barSub V₀ V hV (A ⊔ B) = barSub V₀ V hV A ⊔ barSub V₀ V hV B := by
  unfold barSub
  rw [Subgroup.subgroupOf_sup hA hB, Subgroup.map_sup]

private theorem s16h_e3_le_preBarSub_conj
    (D : Data G) {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L) {x : G} (hx : x ∈ D.M)
    {E : Subgroup G} (hE : E ≤ conjSubgroup L x ⊔ F11.CTilde D.M V₀ V) :
    E ≤ preBarSub D.M V₀ V h.hyp151.isElemAbelian
      (barSub V₀ V h.hyp151.isElemAbelian (conjSubgroup L x)) := by
  have hV := h.hyp151.isElemAbelian
  have hnorm : D.M ≤ normalizer (V : Set G) := h.hyp151.hyp125.pairFacts.le_normalizer
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil hnorm h.hyp151.hyp125.pairFacts.le_normalizer₀
  have hLxM : conjSubgroup L x ≤ D.M := s16h_conjSubgroup_le_of_mem h.hyp151.le hx
  have hCTM : F11.CTilde D.M V₀ V ≤ D.M := fun g hg => ((mem_cTilde_iff hV hnorm).1 hg).1
  have hEM : E ≤ D.M := hE.trans (sup_le hLxM hCTM)
  have hsub : (conjSubgroup L x ⊔ F11.CTilde D.M V₀ V).subgroupOf (stabTil V₀ V) ≤
      (barSub V₀ V hV (conjSubgroup L x)).comap (actTil V₀ V hV) := by
    rw [Subgroup.subgroupOf_sup (hLxM.trans hMs) (hCTM.trans hMs)]
    refine sup_le ?_ ?_
    · intro g hg
      exact actTil_mem_barSub V₀ V hV (Subgroup.mem_subgroupOf.1 hg) g.2
    · intro g hg
      have hgc : (g : G) ∈ F11.CTilde D.M V₀ V := Subgroup.mem_subgroupOf.1 hg
      obtain ⟨-, hgs', hb1⟩ := (mem_cTilde_iff hV hnorm).1 hgc
      show actTil V₀ V hV g ∈ barSub V₀ V hV (conjSubgroup L x)
      rw [show g = (⟨(g : G), hgs'⟩ : stabTil V₀ V) from Subtype.ext rfl, hb1]
      exact Subgroup.one_mem _
  intro e he
  have heM : e ∈ D.M := hEM he
  have hes : e ∈ stabTil V₀ V := hMs heM
  refine (mem_preBarSub D.M V₀ V hV _).2 ⟨heM, hes, ?_⟩
  exact hsub (Subgroup.mem_subgroupOf.2 (hE he))

private theorem s16h_e3_preBarSub_conj_le_cElt
    (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L) {x : G} (hx : x ∈ D.M)
    (hxn : x ∉ nBar D.M V₀ V h.isElemAbelian L) {w : G}
    (hw : w ∈ wSub V₀ V h.isElemAbelian L ⊔ v1Sub D.M V₀ V h.isElemAbelian L) :
    preBarSub D.M V₀ V h.isElemAbelian
        (barSub V₀ V h.isElemAbelian (conjSubgroup L x)) ≤ F11.CElt D.M V₀ w := by
  have hV := h.isElemAbelian
  have hle : wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L ≤
      preTil V₀ V hV (fixV (barSub V₀ V hV (conjSubgroup L x))) :=
    sup_le (s16c34_wSub_le_preTil_fixV hV (h.commute x hx hxn).2)
      (s16c34_v1Sub_le_preTil_fixV D h hx)
  obtain ⟨y, hyval, hyfix⟩ := (mem_preTil V₀ V hV _).1 (hle hw)
  have := s16c34_preBarSub_le_cElt (M := D.M) hV hyfix
  rwa [hyval] at this

theorem s16h_e3_unique₁_of_rank_two_LxC (D : Data G) (S : s16h_Std D) {V₀ V L : Subgroup G}
    (h : Setting16 D V₀ V L) (hs2 : s15 D.M V₀ V h.hyp151.isElemAbelian L = 2) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpσ : p ∈ D.sig ∨ (p = 3 ∧ IsStronglyPEmbedded 3 D.M))
    {x : G} (hx : x ∈ D.M) (hxn : x ∉ nBar D.M V₀ V h.hyp151.isElemAbelian L)
    {E : Subgroup G} (hEab : IsElemAbelian p E) (hEcard : p ^ 2 ≤ Nat.card ↥E)
    (hE : E ≤ conjSubgroup L x ⊔ F11.CTilde D.M V₀ V) :
    ∀ w ∈ wSub V₀ V h.hyp151.isElemAbelian L ⊔ v1Sub D.M V₀ V h.hyp151.isElemAbelian L,
      w ≠ 1 → UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  have hV := h.hyp151.isElemAbelian
  have hEpre := s16h_e3_le_preBarSub_conj D h hx hE
  intro w hw hw1
  by_cases hw0 : w ∈ V₀
  · obtain ⟨q, hq⟩ := S.hx.sig_nonempty
    exact s16h_v0_good D S.h61 h.hyp16 ⟨q, hq, S.hx.three_le q hq⟩ w hw0 hw1
  · have hpre := s16h_e3_preBarSub_conj_le_cElt D h.hyp151 hx hxn hw
    have hECE : E ≤ F11.CElt D.M V₀ w := hEpre.trans hpre
    have hwV : w ∈ V := (sup_le (preTil_le V₀ V hV (wTil V₀ V hV L))
      (fun v hv => s15_Infra_v1Sub_le h.hyp151.hyp125 hV hv)) hw
    have hEp : IsPGroup p E := hEab.isPGroup
    have hEnc : ¬ IsCyclic ↥E := s16c7_not_isCyclic_of_elemAbelian hp hEab hEcard
    rcases hpσ with hpσ | ⟨rfl, hk⟩
    · exact s16c34_uniqueMax_cent_of_cElt D S.h61 S.h127 h.hyp16 hpσ hEp hEnc hwV hw0 hECE
    · exact s16h_uniqueMax_cent_of_cElt_three D S.h61 S.h63 S.h127 hk h.hyp16 hEp hEnc hwV hw0
        hECE

theorem s16h_e3_unique₁_of_dvd_cTil (D : Data G) (S : s16h_Std D) {V₀ V L : Subgroup G}
    (h : Setting16 D V₀ V L) (hs2 : s15 D.M V₀ V h.hyp151.isElemAbelian L = 2)
    (hcomp : IsComponentOf (lBar V₀ V h.hyp151.isElemAbelian L)
      (Mbar D.M V₀ V h.hyp151.isElemAbelian)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpσ : p ∈ D.sig ∨ (p = 3 ∧ IsStronglyPEmbedded 3 D.M))
    (hpL : p ∣ Nat.card ↥(lBar V₀ V h.hyp151.isElemAbelian L))
    (hpC : p ∣ Nat.card ↥(F11.CTilde D.M V₀ V)) :
    ∀ w ∈ wSub V₀ V h.hyp151.isElemAbelian L ⊔ v1Sub D.M V₀ V h.hyp151.isElemAbelian L,
      w ≠ 1 → UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  have hV := h.hyp151.isElemAbelian
  have hnorm : D.M ≤ normalizer (V : Set G) := h.hyp151.hyp125.pairFacts.le_normalizer
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil hnorm h.hyp151.hyp125.pairFacts.le_normalizer₀
  obtain ⟨x, hx, hxn⟩ := s16c34_exists_not_mem_nBar D h.hyp151 (by rw [hs2]; norm_num)
  have hLxM : conjSubgroup L x ≤ D.M := s16h_conjSubgroup_le_of_mem h.hyp151.le hx
  have hCTM : F11.CTilde D.M V₀ V ≤ D.M := fun g hg => ((mem_cTilde_iff hV hnorm).1 hg).1
  let Hsub : Subgroup G := conjSubgroup L x ⊔ F11.CTilde D.M V₀ V
  have hHM : Hsub ≤ D.M := sup_le hLxM hCTM
  have hHstab : Hsub ≤ stabTil V₀ V := sup_le (hLxM.trans hMs) (hCTM.trans hMs)
  let φ : ↥Hsub →* MulAut (Vtil V₀ V hV) :=
    (actTil V₀ V hV).comp (Subgroup.inclusion hHstab)
  have hker : φ.ker = (F11.CTilde D.M V₀ V).subgroupOf Hsub := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hg
      refine (mem_cTilde_iff hV hnorm).2 ⟨hHM g.2, hHstab g.2, ?_⟩
      show actTil V₀ V hV (Subgroup.inclusion hHstab g) = 1
      exact hg
    · intro hg
      obtain ⟨-, hgs, h1⟩ := (mem_cTilde_iff hV hnorm).1 hg
      show φ g = 1
      change actTil V₀ V hV (Subgroup.inclusion hHstab g) = 1
      rw [show Subgroup.inclusion hHstab g = (⟨(g : G), hgs⟩ : stabTil V₀ V) from
        Subtype.ext rfl, h1]
  have hrangeH : φ.range = barSub V₀ V hV Hsub := by
    ext ψ
    constructor
    · rintro ⟨g, rfl⟩
      exact actTil_mem_barSub V₀ V hV g.2 (hHstab g.2)
    · intro hψ
      obtain ⟨g, hgH, hgψ⟩ := (mem_barSub V₀ V hV Hsub ψ).1 hψ
      exact ⟨⟨g, hgH⟩, hgψ⟩
  have hCT_le_H : F11.CTilde D.M V₀ V ≤ Hsub := le_sup_right
  have hbarCT : barSub V₀ V hV (F11.CTilde D.M V₀ V) = ⊥ := by
    rw [cTilde_eq_preBarSub_bot hV hnorm, barSub_preBarSub]
    exact (bot_inf_eq (Mbar D.M V₀ V hV) : (⊥ : Subgroup (MulAut (Vtil V₀ V hV))) ⊓
      Mbar D.M V₀ V hV = ⊥)
  have hrange : φ.range = barSub V₀ V hV (conjSubgroup L x) := by
    rw [hrangeH]
    change barSub V₀ V hV (conjSubgroup L x ⊔ F11.CTilde D.M V₀ V) =
      barSub V₀ V hV (conjSubgroup L x)
    rw [s16h_barSub_sup hV (hLxM.trans hMs) (hCTM.trans hMs), hbarCT, sup_bot_eq]
  haveI : Group.IsPerfect ↥(barSub V₀ V hV L) := ⟨hcomp.2.2.1⟩
  have hperfBar : Group.IsPerfect ↥(barSub V₀ V hV (conjSubgroup L x)) := by
    rw [s15_Infra_barSub_conjSubgroup V₀ V hV (hMs hx) L]
    exact Group.IsPerfect.map (MulAut.conj (actTil V₀ V hV ⟨x, hMs hx⟩)⁻¹).toMonoidHom
  have hiso : (↥Hsub ⧸ φ.ker) ≃*
      ↥(barSub V₀ V hV (conjSubgroup L x)) :=
    (QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hrange)
  have hperf : Group.IsPerfect (↥Hsub ⧸ φ.ker) :=
    Group.IsPerfect.ofSurjective (f := hiso.symm.toMonoidHom) hiso.symm.surjective
  have hcard1 : Nat.card (↥Hsub ⧸ φ.ker) =
      Nat.card ↥(barSub V₀ V hV (conjSubgroup L x)) := Nat.card_congr hiso.toEquiv
  have hcard2 : Nat.card ↥(barSub V₀ V hV (conjSubgroup L x)) =
      Nat.card ↥(lBar V₀ V hV L) := by
    rw [s15_Infra_barSub_conjSubgroup V₀ V hV (hMs hx) L]
    exact Subgroup.card_map_of_injective (MulAut.conj _).injective
  have h1 : p ∣ Nat.card (↥Hsub ⧸ φ.ker) := by
    rw [hcard1, hcard2]; exact hpL
  have hcardC : Nat.card ↥φ.ker = Nat.card ↥(F11.CTilde D.M V₀ V) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCT_le_H).toEquiv
  have h2 : p ∣ Nat.card ↥φ.ker := by
    rw [hcardC]; exact hpC
  obtain ⟨P, hPp, hPc⟩ := s16h_exists_noncyclic_pgroup_of_perfect_quotient
    (H := ↥Hsub) (C := φ.ker) hp hp2 hperf h1 h2
  let P' : Subgroup G := P.map Hsub.subtype
  have hP'le : P' ≤ Hsub := Subgroup.map_subtype_le P
  have hPe : P ≃* P' := Subgroup.equivMapOfInjective P Hsub.subtype Hsub.subtype_injective
  have hP'p : IsPGroup p P' := hPp.of_equiv hPe
  have hP'c : ¬ IsCyclic ↥P' := fun hc => hPc (hPe.isCyclic.2 hc)
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (IsPGroup p ↥P') := ⟨hP'p⟩
  obtain ⟨E', _, hE'card, hE'el⟩ := CFSG.lemma_4_5_a (p := p) (R := ↥P') hp2 hP'c
  let E : Subgroup G := E'.map P'.subtype
  have hE_le_P' : E ≤ P' := Subgroup.map_subtype_le E'
  have hEP : E ≤ Hsub := hE_le_P'.trans hP'le
  have hEab : IsElemAbelian p E := by
    have hE'ab : IsElemAbelian p E' :=
      (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p E').mp hE'el
    exact CFSG.SectionRank.isElemAbelian_map (E := E') hE'ab P'.subtype
  have hEcard : p ^ 2 ≤ Nat.card ↥E := by
    rw [Subgroup.card_subtype P' E', hE'card]
  exact s16h_e3_unique₁_of_rank_two_LxC D S h hs2 hp hp2 hpσ hx hxn hEab hEcard
    (show E ≤ conjSubgroup L x ⊔ F11.CTilde D.M V₀ V from hEP)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
