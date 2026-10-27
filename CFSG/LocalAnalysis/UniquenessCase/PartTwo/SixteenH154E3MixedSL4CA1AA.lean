module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154ThreeDvdLie
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInfra
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Q1A
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Cfg

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s16h_sl4ca1aa_conjSubgroup_le_of_mem {A M : Subgroup G} (hA : A ≤ M) {x : G}
    (hx : x ∈ M) : conjSubgroup A x ≤ M := by
  intro y hy
  rw [mem_conjSubgroup_iff] at hy
  have h1 : x⁻¹ * (x * y * x⁻¹) * x ∈ M := M.mul_mem (M.mul_mem (M.inv_mem hx) (hA hy)) hx
  have e : x⁻¹ * (x * y * x⁻¹) * x = y := by group
  rwa [e] at h1

private theorem s16h_sl4ca1aa_barSub_sup {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    {A B : Subgroup G} (hA : A ≤ stabTil V₀ V) (hB : B ≤ stabTil V₀ V) :
    barSub V₀ V hV (A ⊔ B) = barSub V₀ V hV A ⊔ barSub V₀ V hV B := by
  unfold barSub
  rw [Subgroup.subgroupOf_sup hA hB, Subgroup.map_sup]

theorem s16h_sl4_engine_b_three_dvd_kernel_rank_two
    (D : Data G) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hcomp : IsComponentOf (lBar ⊥ V h.hyp151.isElemAbelian L)
      (Mbar D.M ⊥ V h.hyp151.isElemAbelian))
    (hrow : s16h_H5RowSL2 (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 2)
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L)
    (h3 : 3 ∣ Nat.card ↥(F11.CTilde D.M ⊥ V)) :
    ∃ E : Subgroup G, E ≤ D.M ∧
      E ≤ preBarSub D.M ⊥ V h.hyp151.isElemAbelian
        (centSub (wTil ⊥ V h.hyp151.isElemAbelian L)) ∧
      IsElemAbelian 3 E ∧ Nat.card ↥E = 9 := by
  have hV := h.hyp151.isElemAbelian
  have hnorm : D.M ≤ normalizer (V : Set G) := h.hyp151.hyp125.pairFacts.le_normalizer
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil hnorm h.hyp151.hyp125.pairFacts.le_normalizer₀
  have hLxM : conjSubgroup L x ≤ D.M := s16h_sl4ca1aa_conjSubgroup_le_of_mem h.hyp151.le hxM
  have hCTM : F11.CTilde D.M ⊥ V ≤ D.M := fun g hg => ((mem_cTilde_iff hV hnorm).1 hg).1
  let Hsub : Subgroup G := conjSubgroup L x ⊔ F11.CTilde D.M ⊥ V
  have hHM : Hsub ≤ D.M := sup_le hLxM hCTM
  have hHstab : Hsub ≤ stabTil ⊥ V := sup_le (hLxM.trans hMs) (hCTM.trans hMs)
  let φ : ↥Hsub →* MulAut (Vtil ⊥ V hV) :=
    (actTil ⊥ V hV).comp (Subgroup.inclusion hHstab)
  have hker : φ.ker = (F11.CTilde D.M ⊥ V).subgroupOf Hsub := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hg
      refine (mem_cTilde_iff hV hnorm).2 ⟨hHM g.2, hHstab g.2, ?_⟩
      show actTil ⊥ V hV (Subgroup.inclusion hHstab g) = 1
      exact hg
    · intro hg
      obtain ⟨-, hgs, h1⟩ := (mem_cTilde_iff hV hnorm).1 hg
      show φ g = 1
      change actTil ⊥ V hV (Subgroup.inclusion hHstab g) = 1
      rw [show Subgroup.inclusion hHstab g = (⟨(g : G), hgs⟩ : stabTil ⊥ V) from
        Subtype.ext rfl, h1]
  have hrangeH : φ.range = barSub ⊥ V hV Hsub := by
    ext ψ
    constructor
    · rintro ⟨g, rfl⟩
      exact actTil_mem_barSub ⊥ V hV g.2 (hHstab g.2)
    · intro hψ
      obtain ⟨g, hgH, hgψ⟩ := (mem_barSub ⊥ V hV Hsub ψ).1 hψ
      exact ⟨⟨g, hgH⟩, hgψ⟩
  have hbarCT : barSub ⊥ V hV (F11.CTilde D.M ⊥ V) = ⊥ := by
    rw [cTilde_eq_preBarSub_bot hV hnorm, barSub_preBarSub]
    exact (bot_inf_eq (Mbar D.M ⊥ V hV) :
      (⊥ : Subgroup (MulAut (Vtil ⊥ V hV))) ⊓ Mbar D.M ⊥ V hV = ⊥)
  have hrange : φ.range = barSub ⊥ V hV (conjSubgroup L x) := by
    rw [hrangeH]
    change barSub ⊥ V hV (conjSubgroup L x ⊔ F11.CTilde D.M ⊥ V) =
      barSub ⊥ V hV (conjSubgroup L x)
    rw [s16h_sl4ca1aa_barSub_sup hV (hLxM.trans hMs) (hCTM.trans hMs), hbarCT, sup_bot_eq]
  haveI : Group.IsPerfect ↥(barSub ⊥ V hV L) := ⟨hcomp.2.2.1⟩
  have hperfBar : Group.IsPerfect ↥(barSub ⊥ V hV (conjSubgroup L x)) := by
    rw [s15_Infra_barSub_conjSubgroup ⊥ V hV (hMs hxM) L]
    exact Group.IsPerfect.map (MulAut.conj (actTil ⊥ V hV ⟨x, hMs hxM⟩)⁻¹).toMonoidHom
  have hiso : (↥Hsub ⧸ φ.ker) ≃* ↥(barSub ⊥ V hV (conjSubgroup L x)) :=
    (QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hrange)
  have hperf : Group.IsPerfect (↥Hsub ⧸ φ.ker) :=
    Group.IsPerfect.ofSurjective (f := hiso.symm.toMonoidHom) hiso.symm.surjective
  have hcard1 : Nat.card (↥Hsub ⧸ φ.ker) =
      Nat.card ↥(barSub ⊥ V hV (conjSubgroup L x)) := Nat.card_congr hiso.toEquiv
  have hcard2 : Nat.card ↥(barSub ⊥ V hV (conjSubgroup L x)) =
      Nat.card ↥(lBar ⊥ V hV L) := by
    rw [s15_Infra_barSub_conjSubgroup ⊥ V hV (hMs hxM) L]
    exact Subgroup.card_map_of_injective (MulAut.conj _).injective
  have hpL : 3 ∣ Nat.card ↥(lBar ⊥ V hV L) :=
    s16h_three_dvd_of_isSLn hcomp.2.2 hrow.1
  have h1 : 3 ∣ Nat.card (↥Hsub ⧸ φ.ker) := by rw [hcard1, hcard2]; exact hpL
  have hCT_le_H : F11.CTilde D.M ⊥ V ≤ Hsub := le_sup_right
  have hcardC : Nat.card ↥φ.ker = Nat.card ↥(F11.CTilde D.M ⊥ V) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCT_le_H).toEquiv
  have h2 : 3 ∣ Nat.card ↥φ.ker := by rw [hcardC]; exact h3
  obtain ⟨P, hPp, hPc⟩ := s16h_exists_noncyclic_pgroup_of_perfect_quotient
    (H := ↥Hsub) (C := φ.ker) (p := 3) Nat.prime_three (by norm_num) hperf h1 h2
  let P' : Subgroup G := P.map Hsub.subtype
  have hP'le : P' ≤ Hsub := Subgroup.map_subtype_le P
  have hPe : P ≃* P' := Subgroup.equivMapOfInjective P Hsub.subtype Hsub.subtype_injective
  have hP'p : IsPGroup 3 P' := hPp.of_equiv hPe
  have hP'c : ¬ IsCyclic ↥P' := fun hc => hPc (hPe.isCyclic.2 hc)
  haveI : Fact (IsPGroup 3 ↥P') := ⟨hP'p⟩
  obtain ⟨E', -, hE'card, hE'el⟩ := CFSG.lemma_4_5_a (p := 3) (R := ↥P') (by norm_num) hP'c
  let E : Subgroup G := E'.map P'.subtype
  have hE_le_P' : E ≤ P' := Subgroup.map_subtype_le E'
  have hEP : E ≤ Hsub := hE_le_P'.trans hP'le
  have hEe : E' ≃* E := Subgroup.equivMapOfInjective E' P'.subtype P'.subtype_injective
  have hEcard9 : Nat.card ↥E = 9 := by
    rw [← Nat.card_congr hEe.toEquiv, hE'card]
    norm_num
  have hEab : IsElemAbelian 3 E := by
    have hE'ab : IsElemAbelian 3 E' :=
      (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 E').mp hE'el
    exact CFSG.SectionRank.isElemAbelian_map (E := E') hE'ab P'.subtype
  have hHX : Hsub ≤ preBarSub D.M ⊥ V hV (centSub (wTil ⊥ V hV L)) := by
    refine sup_le ?_ ?_
    · have hcomm := (h.hyp151.commute x hxM hxn).2
      rw [commSub_eq_bot_iff] at hcomm
      intro g hg
      refine (mem_preBarSub D.M ⊥ V hV (centSub (wTil ⊥ V hV L))).2
        ⟨hLxM hg, hMs (hLxM hg), ?_⟩
      refine (mem_centSub).2 fun w hw => ?_
      exact (mem_fixV.1 (hcomm hw)) (actTil ⊥ V hV ⟨g, hMs (hLxM hg)⟩)
        (actTil_mem_barSub ⊥ V hV (X := conjSubgroup L x) hg (hMs (hLxM hg)))
    · intro g hg
      rw [cTilde_eq_preBarSub_bot hV hnorm] at hg
      obtain ⟨hgM, hgs, hx⟩ := (mem_preBarSub D.M ⊥ V hV ⊥).1 hg
      refine (mem_preBarSub D.M ⊥ V hV (centSub (wTil ⊥ V hV L))).2 ⟨hgM, hgs, ?_⟩
      rw [Subgroup.mem_bot.1 hx]
      exact Subgroup.one_mem _
  exact ⟨E, hEP.trans hHM, hEP.trans hHX, hEab, hEcard9⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
