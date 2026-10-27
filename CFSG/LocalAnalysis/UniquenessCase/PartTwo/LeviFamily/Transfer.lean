module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.Cover
import CFSG.Quasithin.SteinbergCDBestOffenderRestriction
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.Lift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {Q S : Type} [Group Q] [Group S] [Finite Q] [Finite S]

omit [Finite S] in
theorem isNontrivialParabolic_map_of_le_center {ρ : Q →* S} (hρ : Function.Surjective ρ)
    (hZ : ρ.ker ≤ center Q) (hZodd : Odd (Nat.card ρ.ker)) {P : Subgroup Q}
    (hP : S19.IsNontrivialParabolic Q P) : S19.IsNontrivialParabolic S (P.map ρ) := by
  obtain ⟨-, hPtop, T, hT⟩ := hP
  have hodd : ∀ x ∈ ρ.ker, Odd (orderOf x) := fun x hx =>
    Odd.of_dvd_nat hZodd (by
      rw [← Nat.card_zpowers x]
      exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hx))
  have hkerN : ρ.ker ≤ normalizer (T : Set Q) :=
    hZ.trans (Subgroup.center_le_normalizer (T : Set Q))
  have hkerP : ρ.ker ≤ P := hkerN.trans hT.le
  have hcomap : (P.map ρ).comap ρ = P := by
    rw [Subgroup.comap_map_eq, sup_eq_left.mpr hkerP]
  have hset : ((T.mapSurjective hρ : Sylow 2 S) : Set S) = ((T : Subgroup Q).map ρ : Set S) :=
    congrArg (fun H : Subgroup S => (H : Set S)) (Sylow.coe_mapSurjective hρ T)
  have hN : normalizer ((T.mapSurjective hρ : Sylow 2 S) : Set S) =
      (normalizer (T : Set Q)).map ρ := by
    rw [hset]
    exact le_antisymm
      (CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KPGen.normalizer_map_le ρ hρ hZ hodd T)
      (Subgroup.le_normalizer_map ρ)
  have hPtop' : P.map ρ ≠ ⊤ := by
    intro htop
    apply hPtop
    have hle : (⊤ : Subgroup S).comap ρ ≤ (P.map ρ).comap ρ := by rw [htop]
    rw [Subgroup.comap_top, hcomap] at hle
    exact top_le_iff.mp hle
  refine ⟨⟨T.mapSurjective hρ, ?_⟩, hPtop', ⟨T.mapSurjective hρ, ?_⟩⟩
  · rw [hN]
    exact Subgroup.map_mono hT.le
  · refine lt_of_le_of_ne ?_ ?_
    · rw [hN]
      exact Subgroup.map_mono hT.le
    · intro heq
      have h2 : (normalizer (T : Set Q)).map ρ = P.map ρ := by rw [← hN]; exact heq
      have h3 := congrArg (fun H : Subgroup S => H.comap ρ) h2
      rw [Subgroup.comap_map_eq, Subgroup.comap_map_eq, sup_eq_left.mpr hkerN,
        sup_eq_left.mpr hkerP] at h3
      exact ne_of_lt hT h3

omit [Finite Q] in
private theorem isNontrivialParabolic_map_symm (e : Q ≃* S) {P : Subgroup S}
    (hP : S19.IsNontrivialParabolic S P) :
    S19.IsNontrivialParabolic Q (P.map e.symm.toMonoidHom) ∧
      (P.map e.symm.toMonoidHom).map e.toMonoidHom = P := by
  have hker : e.symm.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr e.symm.injective
  have hodd : Odd (Nat.card e.symm.toMonoidHom.ker) := by
    rw [hker, Subgroup.card_bot]
    exact odd_one
  have hZ : e.symm.toMonoidHom.ker ≤ center S := by
    rw [hker]
    exact bot_le
  have hcomp : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id S :=
    MonoidHom.ext e.apply_symm_apply
  exact ⟨isNontrivialParabolic_map_of_le_center e.symm.surjective hZ hodd hP, by
    rw [Subgroup.map_map, hcomp, Subgroup.map_id]⟩

theorem HasLeviFamilies.of_mulEquiv (e : Q ≃* S) (h : HasLeviFamilies Q) : HasLeviFamilies S := by
  intro P hP
  obtain ⟨hP', hbase⟩ := isNontrivialParabolic_map_symm e hP
  obtain ⟨d, L, hL⟩ := h _ hP'
  have hL' := IsLeviFamily.map (φ := e.toMonoidHom) e.injective hL
  rw [hbase] at hL'
  exact ⟨d, _, hL'⟩

theorem HasLeviFamiliesAlt.of_mulEquiv (e : Q ≃* S) (h : HasLeviFamiliesAlt Q) :
    HasLeviFamiliesAlt S := by
  intro P hP
  obtain ⟨hP', hbase⟩ := isNontrivialParabolic_map_symm e hP
  obtain ⟨d, L, hL, hAlt⟩ := h _ hP'
  have hL' := IsLeviFamily.map (φ := e.toMonoidHom) e.injective hL
  rw [hbase] at hL'
  have hAlt' := LeviAlt.map (φ := e.toMonoidHom) e.injective hAlt
  rw [hbase] at hAlt'
  exact ⟨d, _, hL', hAlt'⟩

theorem HasLeviFamiliesBlk.of_mulEquiv {two big : Prop} (e : Q ≃* S)
    (h : HasLeviFamiliesBlk two big Q) : HasLeviFamiliesBlk two big S := by
  intro P hP
  obtain ⟨hP', hbase⟩ := isNontrivialParabolic_map_symm e hP
  obtain ⟨d, L, hL, hAlt, hBlk⟩ := h _ hP'
  have hL' := IsLeviFamily.map (φ := e.toMonoidHom) e.injective hL
  rw [hbase] at hL'
  have hAlt' := LeviAlt.map (φ := e.toMonoidHom) e.injective hAlt
  rw [hbase] at hAlt'
  exact ⟨d, _, hL', hAlt', hBlk.map (φ := e.toMonoidHom) e.injective⟩

private theorem ker_mk'_center_facts (hS : CFSG.pCore 2 S = ⊥) {P : Subgroup S}
    (hP : S19.IsNontrivialParabolic S P) :
    (QuotientGroup.mk' (center S)).ker ≤ center S ∧
      Odd (Nat.card (QuotientGroup.mk' (center S)).ker) ∧
      (QuotientGroup.mk' (center S)).ker ≤ P := by
  rw [QuotientGroup.ker_mk']
  obtain ⟨-, -, T, hT⟩ := hP
  exact ⟨le_rfl, CFSG.Quasithin.SteinbergCD.odd_card_center_of_pCore_eq_bot hS,
    (Subgroup.center_le_normalizer (T : Set S)).trans hT.le⟩

theorem HasLeviFamilies.of_quotient_center (hS : CFSG.pCore 2 S = ⊥)
    (h : HasLeviFamilies (S ⧸ center S)) : HasLeviFamilies S := by
  intro P hP
  have hρ := QuotientGroup.mk'_surjective (center S)
  obtain ⟨hZ, hZodd, hkerP⟩ := ker_mk'_center_facts hS hP
  obtain ⟨d, L, hL⟩ := h _ (isNontrivialParabolic_map_of_le_center hρ hZ hZodd hP)
  exact ⟨d, _, hL.lift_of_le_center hρ hZ hZodd hkerP⟩

theorem HasLeviFamiliesAlt.of_quotient_center (hS : CFSG.pCore 2 S = ⊥)
    (h : HasLeviFamiliesAlt (S ⧸ center S)) : HasLeviFamiliesAlt S := by
  intro P hP
  have hρ := QuotientGroup.mk'_surjective (center S)
  obtain ⟨hZ, hZodd, hkerP⟩ := ker_mk'_center_facts hS hP
  obtain ⟨d, L, hL, hAlt⟩ := h _ (isNontrivialParabolic_map_of_le_center hρ hZ hZodd hP)
  exact ⟨d, _, hL.lift_of_le_center hρ hZ hZodd hkerP,
    hAlt.lift_of_le_center hρ hZ hZodd hkerP hL⟩

theorem HasLeviFamiliesBlk.of_quotient_center {two big : Prop} (hS : CFSG.pCore 2 S = ⊥)
    (h : HasLeviFamiliesBlk two big (S ⧸ center S)) : HasLeviFamiliesBlk two big S := by
  intro P hP
  have hρ := QuotientGroup.mk'_surjective (center S)
  obtain ⟨hZ, hZodd, hkerP⟩ := ker_mk'_center_facts hS hP
  obtain ⟨d, L, hL, hAlt, hBlk⟩ := h _ (isNontrivialParabolic_map_of_le_center hρ hZ hZodd hP)
  exact ⟨d, _, hL.lift_of_le_center hρ hZ hZodd hkerP,
    hAlt.lift_of_le_center hρ hZ hZodd hkerP hL, hBlk.lift_of_le_center hρ hZ hZodd hkerP hL⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily
