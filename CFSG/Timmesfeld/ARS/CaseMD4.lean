module

public import CFSG.Timmesfeld.ARS.Sec12Frame

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace Sec12

variable {A A₀ : Subgroup G} (hS : Sec12 R A A₀)
include hS

theorem special_of_commuting_of_opposite {X P' Q' : Subgroup G} (hX : X ∈ lambdaStar R A A₀)
    (hP' : P' ∈ leviSet R A A₀) (hQ' : Q' ∈ leviSet R A A₀) (hPQ : Opposite P' Q')
    (hQX : Commuting Q' X) : Special R P' X := by
  have := hS.hyp.finite
  have hnc : ¬ Commuting X P' := fun hc =>
    hS.not_commuting_and_commuting hX hP' hQ' hPQ hc hQX.symm
  exact (special_of_not_commuting_of_mem_leviSet hS.hyp hS.mem hX hP' hnc).symm

theorem natural_of_commuting {X P' Q' : Subgroup G} (hX : X ∈ lambdaStar R A A₀)
    (hP' : P' ∈ leviSet R A A₀) (hQ' : Q' ∈ leviSet R A A₀) (hPQ : Opposite P' Q')
    (hQX : Commuting Q' X) :
    Special R P' X ∧ (∀ u ∈ Q' ⊔ P', conjSub (X ⊔ ⁅P', X⁆) u = X ⊔ ⁅P', X⁆) ∧
      (∀ n ∈ X ⊔ ⁅P', X⁆, (∀ y ∈ Q', Commute y n) → n ∈ X) := by
  have := hS.hyp.finite
  have hR := hS.hyp.root
  have hiso := hS.hyp.noIsolated
  have hs := hS.special_of_commuting_of_opposite hX hP' hQ' hPQ hQX
  have hl : X ∈ lambdaSet R Q' := hS.mem_lambdaSet_of_commuting hX hQ' hQX.symm
  exact ⟨hs, fun u hu => Sec3.conjSub_sup_commutator_eq hR hiso hQ'.1.1 hP'.1.1 hPQ.symm hl
    ⟨hX.1.1.1, hs⟩ hu, fun n hn hnQ => Sec3.mem_of_forall_commute_of_mem_sup hR hiso hQ'.1.1
      hP'.1.1 hPQ.symm hl ⟨hX.1.1.1, hs⟩ hn hnQ⟩

theorem config {E F P' Q' : Subgroup G} (hP' : P' ∈ leviSet R A A₀) (hQ' : Q' ∈ leviSet R A A₀)
    (hPQ : Opposite P' Q') (hE : E ∈ lambdaStar R A A₀) (hEQ : Commuting Q' E)
    (hF : F ∈ lambdaStar R A₀ A) (hFP : Commuting P' F) (hEF : Opposite E F) :
    Special R P' E ∧ Commuting Q' E ∧ ⁅Q', ⁅P', E⁆⁆ = E ∧ Commuting P' F ∧
      ⁅⁅P', E⁆, F⁆ = P' ∧ Special R Q' F := by
  have := hS.hyp.finite
  have hR := hS.hyp.root
  have hiso := hS.hyp.noIsolated
  have hA := hS.mem
  have hS₀ : Sec12 R A₀ A := hS.of_mem_omegaSet hS.opp.1 ⟨hA, hS.opp.2.symm⟩
  have hlevi : leviSet R A₀ A = leviSet R A A₀ := Set.inter_comm _ _
  have hP'₀ : P' ∈ leviSet R A₀ A := hlevi ▸ hP'
  have hQ'₀ : Q' ∈ leviSet R A₀ A := hlevi ▸ hQ'
  have hPR : P' ∈ R := hP'.1.1
  have hER : E ∈ R := hE.1.1.1
  have hFR : F ∈ R := hF.1.1.1
  obtain ⟨hsPE, hinv, hfix⟩ := hS.natural_of_commuting hE hP' hQ' hPQ hEQ
  set D := ⁅P', E⁆ with hDdef
  have hDR : D ∈ R := hsPE.1
  have hD : D ∈ lambdaStar R A A₀ := by
    have := (exists_opposite_of_mem_lambdaStar hS.hyp hA hS.sec8.2 hS.opp hP' hE
      hsPE.symm).1 D hDR
    rw [Subgroup.commutator_comm E P'] at this
    exact this le_sup_right
  have hDE : D ≠ E := by
    have := hsPE.symm.ne_commutator hR
    rw [Subgroup.commutator_comm E P'] at this
    exact this.symm
  have hQN : Q' ≤ Subgroup.normalizer ((E ⊔ D : Subgroup G) : Set G) := fun y hy =>
    conjSub_eq_self_iff.1 (hinv y (Subgroup.mem_sup_left hy))
  have hsQD : Special R Q' D := by
    have hnc : ¬ Commuting Q' D := by
      intro hc
      refine hDE (Subgroup.eq_of_le_of_card_ge (fun d hd => ?_) (hR.card_eq hER hDR).le)
      exact hfix d (Subgroup.mem_sup_right hd) fun y hy => hc y hy d hd
    have hne : Q' ≠ D := fun e => hnc (by rw [← e]; exact hR.commuting_self hQ'.1.1)
    rcases hR.rel _ hQ'.1.1 _ hDR hne with hc | ho | hs
    · exact absurd hc hnc
    · exact absurd ho (CaseD4.not_opposite_of_mem_leviSet hR hA hD hQ')
    · exact hs
  have h3 : ⁅Q', D⁆ = E := by
    refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) (hR.card_eq hER hsQD.1).le
    exact hfix x (Linear.commutator_le_of_le_normalizer hQN le_sup_right hx) fun y hy =>
      (hsQD.2.1 x hx y hy).symm
  have hFl : F ∈ lambdaSet R P' := hS₀.mem_lambdaSet_of_commuting hF hP'₀ hFP.symm
  have hPFl : P' ∈ lambdaSet R F := mem_lambdaSet_comm hPR hFl
  have hPψ : P' ∈ psiSet R E := ⟨hPR, hsPE.symm⟩
  have hinv' : ∀ x ∈ F ⊔ E, conjSub (P' ⊔ ⁅E, P'⁆) x = P' ⊔ ⁅E, P'⁆ := fun x hx =>
    Sec3.conjSub_sup_commutator_eq hR hiso hFR hER hEF.symm hPFl hPψ hx
  have hfix' : ∀ n ∈ P' ⊔ ⁅E, P'⁆, (∀ a ∈ F, Commute a n) → n ∈ P' := fun n hn hnF =>
    Sec3.mem_of_forall_commute_of_mem_sup hR hiso hFR hER hEF.symm hPFl hPψ hn hnF
  rw [Subgroup.commutator_comm E P'] at hinv' hfix'
  have hFN : F ≤ Subgroup.normalizer ((P' ⊔ D : Subgroup G) : Set G) := fun f hf =>
    conjSub_eq_self_iff.1 (hinv' f (Subgroup.mem_sup_left hf))
  have hsDF : Special R D F := by
    have hnc : ¬ Commuting D F := by
      intro hc
      have hDP : D = P' := (Subgroup.eq_of_le_of_card_ge (fun d hd =>
        hfix' d (Subgroup.mem_sup_right hd) fun f hf => (hc d hd f hf).symm)
        (hR.card_eq hPR hDR).le)
      exact hD.2.2.not_commuting hR (hDP ▸ hP'.2.2.2)
    have hne : D ≠ F := fun e => hnc (by rw [← e]; exact hR.commuting_self hDR)
    rcases hR.rel _ hDR _ hFR hne with hc | ho | hs
    · exact absurd hc hnc
    · exact absurd hsPE.2.1 (not_commuting_of_opposite_of_mem_lambdaSet hR hDR ho hPFl)
    · exact hs
  have h5 : ⁅D, F⁆ = P' := by
    refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) (hR.card_eq hPR hsDF.1).le
    exact hfix' x (commutator_le_of_le_normalizer le_sup_right hFN hx) fun f hf =>
      (hsDF.2.2 x hx f hf).symm
  exact ⟨hsPE, hEQ, h3, hFP, h5,
    hS₀.special_of_commuting_of_opposite hF hQ'₀ hP'₀ hPQ.symm hFP⟩

theorem IsSubframe.isConfig {E C : Subgroup G} {P Q : Fin 3 → Subgroup G}
    (hfr : IsSubframe R A A₀ E C P Q) :
    ⁅A₀, C⁆ ∈ lambdaStar R A₀ A ∧ Opposite E ⁅A₀, C⁆ ∧
      IsConfig R (edgeD 4) ![P 0, E, P 1, P 2] ![Q 0, ⁅A₀, C⁆, Q 1, Q 2] := by
  have := hS.hyp.finite
  have hR := hS.hyp.root
  have hiso := hS.hyp.noIsolated
  have hA := hS.mem
  have hE := hfr.memE
  have hC := hfr.memC
  have hPR : ∀ i, P i ∈ R := fun i => (hfr.memP i).1.1.1
  have hQR : ∀ i, Q i ∈ R := fun i => (hfr.memQ i).1.1.1
  have hEQ : ∀ i, Commuting (Q i) E := fun i => (hfr.memQ i).2.1.2.2.symm
  have hCP : ∀ i, Commuting (P i) C := fun i => (hfr.memP i).2.1.2.2.symm
  have hER : E ∈ R := hE.1.1.1
  have hECne : E ≠ C := fun e => hR.ne_bot _ hfr.special.1
    (commuting_iff_commutator_eq_bot.1 (e ▸ hR.commuting_self hER))
  obtain ⟨-, hECA⟩ := (commuting_or_commutator_eq_of_mem_lambdaSet hS.hyp hA hE.1 hC.1
    hECne).resolve_left fun hc => hR.ne_bot _ hfr.special.1 (commuting_iff_commutator_eq_bot.1 hc)
  obtain ⟨hF, hFC, hAFC, hFlevi⟩ := CaseD4.commutator_props hS.hyp hA hS.opp hC
  set F := ⁅A₀, C⁆ with hFdef
  have hFP : ∀ i, Commuting (P i) F := fun i => hFlevi _ (hfr.memP i).1 (hCP i)
  have hFR : F ∈ R := hF.1.1.1
  have hEF : Opposite E F := CaseD4.opposite_of_extremal hR hiso hA hC.1.1.1 hER hFR
    hC.1.1.2.2 hE.1.1.2.2.symm hfr.special hECA hFC hF.2.2 hAFC
  have hcfg : ∀ i, Special R (P i) E ∧ Commuting (Q i) E ∧ ⁅Q i, ⁅P i, E⁆⁆ = E ∧
      Commuting (P i) F ∧ ⁅⁅P i, E⁆, F⁆ = P i ∧ Special R (Q i) F := fun i =>
    hS.config (hfr.memP i).1 (hfr.memQ i).1 (hfr.opposite i) hE (hEQ i) hF (hFP i) hEF
  have hright : ∀ i : Fin 3, Special R E (P i) ∧ Commuting F (P i) ∧ ⁅F, ⁅E, P i⁆⁆ = P i ∧
      Commuting E (Q i) ∧ ⁅⁅E, P i⁆, Q i⁆ = E ∧ Special R F (Q i) := by
    intro i
    obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hcfg i
    refine ⟨d1.symm, d4.symm, ?_, d2.symm, ?_, d6.symm⟩
    · rw [Subgroup.commutator_comm E, Subgroup.commutator_comm F]
      exact d5
    · rw [Subgroup.commutator_comm E, Subgroup.commutator_comm _ (Q i)]
      exact d3
  have hcm : ∀ a b : Fin 3, a ≠ b → ∀ {S T : Subgroup G}, S ≤ P a ⊔ Q a → T ≤ P b ⊔ Q b →
      Commuting S T := fun a b hab S T hS hT => (hfr.commuting a b hab).mono hS hT
  refine ⟨hF, hEF, fun k => ?_, fun k => ?_, fun k => ?_, fun i j hij => ?_,
    fun i j hij h1 h2 => ?_⟩
  · fin_cases k
    exacts [hPR 0, hER, hPR 1, hPR 2]
  · fin_cases k
    exacts [hQR 0, hFR, hQR 1, hQR 2]
  · fin_cases k
    exacts [hfr.opposite 0, hEF, hfr.opposite 1, hfr.opposite 2]
  · fin_cases i <;> fin_cases j <;> simp [edgeD] at hij
    · exact hcfg 0
    · exact hright 1
    · exact hright 2
  · fin_cases i <;> fin_cases j <;> simp [edgeD] at hij h1 h2 <;>
      exact ⟨hcm _ _ (by decide) le_sup_left le_sup_left,
        hcm _ _ (by decide) le_sup_left le_sup_right, hcm _ _ (by decide) le_sup_right le_sup_left,
        hcm _ _ (by decide) le_sup_right le_sup_right⟩

end Sec12

end CFSG.Timmesfeld.ARS
