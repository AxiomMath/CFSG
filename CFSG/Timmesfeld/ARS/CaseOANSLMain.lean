module

public import CFSG.Timmesfeld.ARS.CaseOANSLAssembleMinus

public section

open scoped commutatorElement

namespace CFSG.Timmesfeld.ARS

@[expose] def OAStarInput : Prop :=
  ∀ (G : Type) [Group G] (R : Set (Subgroup G)) (A A₀ : Subgroup G) (Δ₁ Δ₂ : Set (Subgroup G)),
    CaseOASetting G R A A₀ Δ₁ Δ₂ → (∃ X ∈ Δ₁, ∃ Y ∈ Δ₁, Special R X Y) →
      ∀ B ∈ lambdaStar R A A₀, ∀ D ∈ lambdaStar R A A₀, D ∈ lambdaSet R B →
        (deltaSet R A A₀ B ∩ deltaSet R A A₀ D ∩ Δ₁).Nonempty

namespace CaseOANSL

section Quot

variable {G : Type} [Group G] {R : Set (Subgroup G)} {A A₀ : Subgroup G}
  {Δ₁ Δ₂ : Set (Subgroup G)}
variable (h : Hyp G R) (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
  (hA₀ : A₀ ∈ omegaSet R A) (hΔ₁ : Δ₁ ∈ leviComps R A A₀)
include h hA hAne hA₀ hΔ₁

theorem mem_lambdaSet_of_quot₁ (hnd : ∃ X ∈ Δ₁, ∃ Y ∈ Δ₁, Special R X Y) {E F : Subgroup G}
    (hE : E ∈ Δ₁) (hF : F ∈ Δ₁)
    (hEF : quotMap (gen Δ₁) F ∈ lambdaSet (quotClass (gen Δ₁) Δ₁) (quotMap (gen Δ₁) E)) :
    F ∈ lambdaSet R E := by
  have := h.finite
  obtain ⟨E₀, hE₀, rfl⟩ := hΔ₁
  have hq := Levi.quotHyp h hA hAne hA₀ hE₀ hnd
  have := hq.finite
  have hR' := hq.root
  have hiso' := hq.noIsolated
  set V := gen (Levi.comp R A A₀ E₀)
  set R' := quotClass V (Levi.comp R A A₀ E₀)
  have hER' : quotMap V E ∈ R' := ⟨E, hE, rfl⟩
  have hFR' : quotMap V F ∈ R' := ⟨F, hF, rfl⟩
  have hEF' : quotMap V E ∈ lambdaSet R' (quotMap V F) := mem_lambdaSet_comm hER' hEF
  obtain ⟨Q, hQ, hQle, hQE, hQF⟩ :=
    exists_mem_le_sup_ne_ne hR' hiso' hFR' hEF' (quotMap V E) (quotMap V F)
  obtain ⟨U', hU', u, hu, hEu⟩ := exists_mem_lambdaSet_conjSub_eq hR' hiso' hFR' hEF' hER'
    le_sup_right (Ne.symm hEF.1.2.1) hQ hQle hQF
  have hUE : U' ≠ quotMap V E := by
    rintro rfl
    exact hQE (hEu ▸ conjSub_eq_self_iff.2 (Subgroup.le_normalizer hu))
  rcases commuting_or_commutator_eq_of_mem_lambdaSet hq hFR' hU' hEF' hUE with hc | ⟨hs, hcomm⟩
  · exact absurd (hEu ▸ conjSub_of_forall_commute fun e he => hc u hu e he) hQE
  · obtain ⟨U, hU, rfl⟩ := hU'.1.1
    have hsU : Special R U E := Levi.quot_hspec h hA hAne hA₀ hE₀ U hU E hE hs
    obtain ⟨hUEΔ, hUEq⟩ := Levi.quot_hcl h hA hAne hA₀ hE₀ U hU E hE hsU
    have hUEF : ⁅U, E⁆ = F := Levi.quot_hinj h hA hAne hA₀ hE₀ hUEΔ hF (hUEq.trans hcomm)
    have := (mem_lambdaSet_commutator h.root h.noIsolated (Levi.comp_subset_R h hA hAne hA₀ hE₀ hU)
      (Levi.comp_subset_R h hA hAne hA₀ hE₀ hE) hsU).2
    rw [hUEF] at this
    exact mem_lambdaSet_comm (Levi.comp_subset_R h hA hAne hA₀ hE₀ hF) this

end Quot

section Star

variable {G : Type} [Group G] {R : Set (Subgroup G)} {A A₀ : Subgroup G}
  {Δ₁ Δ₂ : Set (Subgroup G)}

theorem not_sigmaEqLambda_quot₁ (hstar : OAStarInput) (hset : CaseOASetting G R A A₀ Δ₁ Δ₂)
    (hnd : ∃ X ∈ Δ₁, ∃ Y ∈ Δ₁, Special R X Y) :
    ¬ SigmaEqLambda (quotClass (gen Δ₁) Δ₁) := by
  intro hSL
  have hset' := hset
  obtain ⟨h, hA, -, hAne, hmax, hA₀, h2, hΔ₁, hΔ₂, hne, -, -⟩ := hset
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hl₁ := fun {X : Subgroup G} (hX : X ∈ Δ₁) =>
    Sec9.mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₁ hX
  obtain ⟨B, hB⟩ := CaseD4.lambdaStar_nonempty h hA hA₀
  obtain ⟨X, hX, hXB⟩ : ∃ X ∈ Δ₁, ¬ Commuting X B := by
    by_contra! hall
    exact Sec9.not_forall_commuting h hA hAne hA₀ hmax hΔ₁ hB hall
  have hBX : Special R B X :=
    special_of_not_commuting_of_mem_leviSet h hA hB (hl₁ hX) fun hc => hXB hc.symm
  obtain ⟨x, hx, hx1⟩ := hR.exists_ne_one (hl₁ hX).1.1
  have hxV : x ∈ levi R A A₀ := le_gen (hl₁ hX) hx
  have hneB : conjSub B x ≠ B :=
    Sec3.conjSub_ne_of_special hR hiso (hl₁ hX).1.1 hB.1.1.1 hBX.symm hx hx1
  have hBx : conjSub B x ∈ lambdaStar R A A₀ := conjSub_mem_lambdaStar_of_mem_levi hR hB hxV
  have hBxB : conjSub B x ∈ lambdaSet R B := by
    have hle : conjSub B x ≤ B ⊔ ⁅B, X⁆ :=
      (conjSub_le_commutator_sup (A := B) hx).trans (sup_comm _ _).le
    obtain ⟨-, hCB, -⟩ := commutator_mem_lambdaStar h hA hAne hA₀ hB (hl₁ hX) hBX
    exact (mem_lambdaSet_of_le_sup hR hiso hB.1.1.1 hCB hB.1.1.1 le_sup_left
      hBx.1.1.1 hle hneB.symm).1
  obtain ⟨F, ⟨hFB, hFBx⟩, hF⟩ := hstar G R A A₀ Δ₁ Δ₂ hset' hnd B hB _ hBx hBxB
  obtain ⟨E, hE, hEBx⟩ : ∃ E ∈ deltaSet R A A₀ B, ¬ Commuting E (conjSub B x) := by
    by_contra! hall
    exact hneB (eq_of_forall_commuting' h hA hAne hA₀ (fun _ hB' _ hC' hBC =>
      CaseOA.lambdaStar_inter_nonempty h hA hAne hmax hA₀ hΔ₁ hΔ₂ hne hB' hC' hBC) hmax
        (B := conjSub B x) (C := B) hBx hB hall).symm
  have hE₁ : E ∈ Δ₁ := by
    have hEc : Levi.comp R A A₀ E ∈ leviComps R A A₀ := ⟨E, hE.1, rfl⟩
    rcases CaseOA.eq_or_eq_of_card_two h2 hΔ₁ hΔ₂ hne hEc with e | e
    · exact e ▸ Sec9.self_mem_comp A A₀ E
    · exfalso
      have hE₂ : E ∈ Δ₂ := e ▸ Sec9.self_mem_comp A A₀ E
      have hEx : conjSub E x = E := conjSub_of_forall_commute fun y hy =>
        (Sec9.commuting_gen_of_ne h hA hAne hA₀ hΔ₁ hΔ₂ hne x (le_gen hX hx) y (le_gen hE₂ hy))
      have hc := (hE.2.1.2.2.symm : Commuting E B).conjSub x
      rw [hEx] at hc
      exact hEBx hc
  have hFc : Commuting F (conjSub B x) := hFBx.2.1.2.2.symm
  have hEF : E ≠ F := fun e => hEBx (e ▸ hFc)
  have hFE : F ∉ lambdaSet R E := fun hFE =>
    hEBx (commuting_of_mem_deltaSet_of_mem_lambdaSet h hA hA₀ hBx hFBx hE.1
      (mem_lambdaSet_comm hE.1.1.1 hFE))
  refine hFE (mem_lambdaSet_of_quot₁ h hA hAne hA₀ hΔ₁ hnd hE₁ hF ?_)
  have hc : Commuting E F := commuting_of_mem_deltaSet h hA hA₀ hB hE hFB
  have hσ : quotMap (gen Δ₁) F ∈ sigmaSet (quotClass (gen Δ₁) Δ₁) (quotMap (gen Δ₁) E) :=
    ⟨⟨F, hF, rfl⟩, fun e => hEF (quot_injOn₁ h hA hAne hA₀ hΔ₁ hE₁ hF e.symm),
      LeviQuot.commuting_quotMap hc⟩
  rwa [hSL _ ⟨E, hE₁, rfl⟩] at hσ

end Star

end CaseOANSL

open CaseOANSL in
theorem oaNonSimplyLacedInput_of (hstar : OAStarInput) : OANonSimplyLacedInput := by
  intro G _ R A A₀ Δ₁ Δ₂ hset _ hnd _ hdata
  rcases hdata with hSL | hF
  · exact absurd hSL (not_sigmaEqLambda_quot₁ hstar hset hnd)
  · obtain ⟨F⟩ : Nonempty (NSLFrameData (CompBar Δ₁) (quotClass (gen Δ₁) Δ₁)) := hF
    obtain ⟨h, hA, -, hAne, hmax, hA₀, h2, hΔ₁, hΔ₂, hne, -, -⟩ := id hset
    rcases (exists_attach h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne F).1 with hCt | hCt
    · exact output_of_frame_minus hset F hCt
    · exact output_of_frame_C hset F hCt

end CFSG.Timmesfeld.ARS
