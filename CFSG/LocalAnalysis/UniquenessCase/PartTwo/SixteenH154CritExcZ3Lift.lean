module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritExcZ3PStarA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7Eseven

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_card_mul_card_barSub_inf {V₀ V M E : Subgroup G} (hV : IsElemAbelian 2 V)
    (hEM : E ≤ M) (hM : M ≤ normalizer (V : Set G)) (hMs : M ≤ stabTil V₀ V)
    (Xbar : Subgroup (MulAut (Vtil V₀ V hV))) :
    Nat.card ↥E * Nat.card ↥(barSub V₀ V hV E ⊓ Xbar) =
      Nat.card ↥(barSub V₀ V hV E) * Nat.card ↥(E ⊓ preBarSub M V₀ V hV Xbar) := by
  classical
  have hEs : E ≤ stabTil V₀ V := hEM.trans hMs
  have hCtilde_le_X : F11.CTilde M V₀ V ≤ preBarSub M V₀ V hV Xbar := by
    intro c hc
    obtain ⟨hcM, hcs, hc1⟩ := (mem_cTilde_iff hV hM).1 hc
    exact (mem_preBarSub M V₀ V hV Xbar).2
      ⟨hcM, hcs, by rw [hc1]; exact Subgroup.one_mem Xbar⟩
  have hbar : barSub V₀ V hV (E ⊓ preBarSub M V₀ V hV Xbar) = barSub V₀ V hV E ⊓ Xbar := by
    refine le_antisymm ?_ ?_
    · refine le_inf (barSub_mono V₀ V hV inf_le_left) ?_
      intro φ hφ
      obtain ⟨g, hg, rfl⟩ := (mem_barSub V₀ V hV _ φ).1 hφ
      obtain ⟨-, hh, hhx⟩ := (mem_preBarSub M V₀ V hV Xbar).1 hg.2
      have hgg : (⟨(g : G), hh⟩ : stabTil V₀ V) = g := Subtype.ext rfl
      rwa [hgg] at hhx
    · intro φ hφ
      obtain ⟨hφE, hφX⟩ := Subgroup.mem_inf.1 hφ
      obtain ⟨e, he, rfl⟩ := (mem_barSub V₀ V hV E φ).1 hφE
      exact (mem_barSub V₀ V hV _ _).2
        ⟨e, ⟨he, (mem_preBarSub M V₀ V hV Xbar).2 ⟨hEM he, e.2, hφX⟩⟩, rfl⟩
  have hinf : (E ⊓ preBarSub M V₀ V hV Xbar) ⊓ F11.CTilde M V₀ V = E ⊓ F11.CTilde M V₀ V := by
    rw [inf_assoc, inf_eq_right.2 hCtilde_le_X]
  have h1 : Nat.card ↥E =
      Nat.card ↥(barSub V₀ V hV E) * Nat.card ↥(E ⊓ F11.CTilde M V₀ V) :=
    s16h_z3_card_eq_barSub_mul hV hEM hM hEs
  have h2 : Nat.card ↥(E ⊓ preBarSub M V₀ V hV Xbar) =
      Nat.card ↥(barSub V₀ V hV (E ⊓ preBarSub M V₀ V hV Xbar)) *
        Nat.card ↥((E ⊓ preBarSub M V₀ V hV Xbar) ⊓ F11.CTilde M V₀ V) :=
    s16h_z3_card_eq_barSub_mul hV (inf_le_left.trans hEM) hM
      (inf_le_left.trans hEs)
  rw [hbar, hinf] at h2
  rw [h1, h2]
  ring

theorem s16h_exists_noncyclic_le_preBarSub {V₀ V M : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMs : M ≤ stabTil V₀ V) {q : ℕ} (hq : q.Prime)
    (Pbar : Subgroup (MulAut (Vtil V₀ V hV))) (hPM : Pbar ≤ Mbar M V₀ V hV)
    (hPe : IsElemAbelian q Pbar) (hP : q ^ 2 ≤ Nat.card ↥Pbar) :
    ∃ R : Subgroup G, R ≤ preBarSub M V₀ V hV Pbar ∧ IsPGroup q R ∧ ¬ IsCyclic ↥R := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  let Y : Subgroup G := preBarSub M V₀ V hV Pbar
  have hYstab : Y ≤ stabTil V₀ V := by
    intro g hg
    exact hMs ((mem_preBarSub M V₀ V hV Pbar).1 hg).1
  let f : ↥Y →* MulAut (Vtil V₀ V hV) :=
    (actTil V₀ V hV).comp (Subgroup.inclusion hYstab)
  have hfbar : f.range = barSub V₀ V hV Y := by
    change ((actTil V₀ V hV).comp (Subgroup.inclusion hYstab)).range =
      barSub V₀ V hV Y
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  have hfrange : f.range = Pbar := by
    rw [hfbar]
    change barSub V₀ V hV (preBarSub M V₀ V hV Pbar) = Pbar
    rw [barSub_preBarSub, inf_eq_left.2 hPM]
  let φ : ↥Y →* ↥Pbar :=
    MonoidHom.codRestrict f Pbar (fun g => by
      show f g ∈ Pbar
      rw [← hfrange]
      exact MonoidHom.mem_range.2 ⟨g, rfl⟩)
  have hφ : Function.Surjective φ := by
    rintro ⟨ψ, hψ⟩
    have hmem : ψ ∈ f.range := by rw [hfrange]; exact hψ
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.1 hmem
    exact ⟨g, Subtype.ext hg⟩
  have hPgrp : IsPGroup q ↥Pbar := IsElemAbelian.isPGroup hPe
  obtain ⟨S⟩ : Nonempty (Sylow q ↥Y) := inferInstance
  have htop : ((S.mapSurjective hφ : Sylow q ↥Pbar) : Subgroup ↥Pbar) = ⊤ :=
    ((S.mapSurjective hφ).is_maximal' (Q := ⊤)
      (hPgrp.of_equiv Subgroup.topEquiv.symm) le_top).symm
  let πS : ↥S →* ↥Pbar := φ.comp (S : Subgroup ↥Y).subtype
  have hπS : Function.Surjective πS := by
    intro p
    have hmem : p ∈ ((S.mapSurjective hφ : Sylow q ↥Pbar) : Subgroup ↥Pbar) := by
      rw [htop]
      exact Subgroup.mem_top p
    rw [Sylow.coe_mapSurjective] at hmem
    obtain ⟨s, hs, hsp⟩ := hmem
    exact ⟨⟨s, hs⟩, hsp⟩
  let R : Subgroup G := (S : Subgroup ↥Y).map Y.subtype
  refine ⟨R, ?_, ?_, ?_⟩
  · show R ≤ Y
    exact Subgroup.map_subtype_le (S : Subgroup ↥Y)
  · exact (S.isPGroup').map Y.subtype
  · intro hcyc
    have hcycS : IsCyclic ↥S :=
      ((Subgroup.equivMapOfInjective (S : Subgroup ↥Y) Y.subtype
        Y.subtype_injective).isCyclic).mpr hcyc
    haveI : IsCyclic ↥S := hcycS
    exact s16c7_not_isCyclic_of_elemAbelian hq hPe hP (isCyclic_of_surjective πS hπS)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
