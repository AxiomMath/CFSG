module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInfra
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Q1A
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s16h_sl28_conjSubgroup_le_of_mem {A M : Subgroup G} (hA : A ≤ M) {x : G}
    (hx : x ∈ M) : conjSubgroup A x ≤ M := by
  intro y hy
  rw [mem_conjSubgroup_iff] at hy
  have h1 : x⁻¹ * (x * y * x⁻¹) * x ∈ M :=
    M.mul_mem (M.mul_mem (M.inv_mem hx) (hA hy)) hx
  have e : x⁻¹ * (x * y * x⁻¹) * x = y := by group
  rwa [e] at h1

private theorem s16h_sl28_barSub_sup {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    {A B : Subgroup G} (hA : A ≤ stabTil V₀ V) (hB : B ≤ stabTil V₀ V) :
    barSub V₀ V hV (A ⊔ B) = barSub V₀ V hV A ⊔ barSub V₀ V hV B := by
  unfold barSub
  rw [Subgroup.subgroupOf_sup hA hB, Subgroup.map_sup]

theorem s16h_exists_Eb_of_dvd_cTil
    (D : Data G) {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L)
    (hcomp : IsComponentOf (lBar V₀ V h.hyp151.isElemAbelian L)
      (Mbar D.M V₀ V h.hyp151.isElemAbelian)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hpL : p ∣ Nat.card ↥(lBar V₀ V h.hyp151.isElemAbelian L))
    (hpC : p ∣ Nat.card ↥(F11.CTilde D.M V₀ V)) {x : G} (hx : x ∈ D.M)
    (hxn : x ∉ nBar D.M V₀ V h.hyp151.isElemAbelian L) :
    ∃ E : Subgroup G, E ≤ D.M ∧ IsElemAbelian p E ∧
      p ^ 2 ≤ Nat.card ↥(E ⊓ preBarSub D.M V₀ V h.hyp151.isElemAbelian
        (centSub (wTil V₀ V h.hyp151.isElemAbelian L))) := by
  have hV := h.hyp151.isElemAbelian
  have hnorm : D.M ≤ normalizer (V : Set G) := h.hyp151.hyp125.pairFacts.le_normalizer
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil hnorm h.hyp151.hyp125.pairFacts.le_normalizer₀
  have hLxM : conjSubgroup L x ≤ D.M := s16h_sl28_conjSubgroup_le_of_mem h.hyp151.le hx
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
    exact bot_inf_eq _
  have hrange : φ.range = barSub V₀ V hV (conjSubgroup L x) := by
    rw [hrangeH]
    change barSub V₀ V hV (conjSubgroup L x ⊔ F11.CTilde D.M V₀ V) =
      barSub V₀ V hV (conjSubgroup L x)
    rw [s16h_sl28_barSub_sup hV (hLxM.trans hMs) (hCTM.trans hMs), hbarCT, sup_bot_eq]
  have hbarHsub : barSub V₀ V hV Hsub = barSub V₀ V hV (conjSubgroup L x) :=
    hrangeH.symm.trans hrange
  haveI : Group.IsPerfect ↥(barSub V₀ V hV L) := ⟨hcomp.2.2.1⟩
  have hperfBar : Group.IsPerfect ↥(barSub V₀ V hV (conjSubgroup L x)) := by
    rw [s15_Infra_barSub_conjSubgroup V₀ V hV (hMs hx) L]
    exact Group.IsPerfect.map (MulAut.conj (actTil V₀ V hV ⟨x, hMs hx⟩)⁻¹).toMonoidHom
  have hiso : (↥Hsub ⧸ φ.ker) ≃* ↥(barSub V₀ V hV (conjSubgroup L x)) :=
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
  have hcomm : commSub (wTil V₀ V hV L) (barSub V₀ V hV (conjSubgroup L x)) = ⊥ :=
    (h.hyp151.commute x hx hxn).2
  have hcentLx : barSub V₀ V hV (conjSubgroup L x) ≤ centSub (wTil V₀ V hV L) := by
    intro g hg
    rw [mem_centSub]
    intro u hu
    exact (commSub_eq_bot_iff.mp hcomm) hu g hg
  have hHsubX : Hsub ≤ preBarSub D.M V₀ V hV (centSub (wTil V₀ V hV L)) := by
    intro g hg
    refine (mem_preBarSub D.M V₀ V hV _).2 ⟨hHM hg, hHstab hg, ?_⟩
    have hmem : actTil V₀ V hV ⟨g, hHstab hg⟩ ∈ barSub V₀ V hV Hsub :=
      actTil_mem_barSub V₀ V hV hg (hHstab hg)
    rw [hbarHsub] at hmem
    exact hcentLx hmem
  refine ⟨E, hEP.trans hHM, hEab, ?_⟩
  rw [inf_eq_left.mpr (hEP.trans hHsubX)]
  exact hEcard

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
