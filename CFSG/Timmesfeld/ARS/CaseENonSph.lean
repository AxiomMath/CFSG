module

public import CFSG.Timmesfeld.ARS.CaseECollinear
public import CFSG.Timmesfeld.ARS.CaseENodeLemma
public import CFSG.Timmesfeld.ARS.Sec13Commuting

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg

variable {G : Type} [Group G] {R : Set (Subgroup G)} {K : Type*} [Group K] {A A₀ : Subgroup G}
  {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {Ψ : K →* G}

@[expose] def StarAt {I : Type} [Fintype I] [DecidableEq I] (A : Matrix I I ℤ)
    (hA : TauCeti.IsFiniteType A) (j : I) : Prop :=
  ∀ γ ∈ roots hA ∅, γ j = 1 → ∃ β₁ β₂ : I → ℤ, β₁ ≠ β₂ ∧
    ∀ β ∈ ({β₁, β₂} : Set (I → ℤ)), β ∈ roots hA ∅ ∧ β j = 1 ∧ coroot A j β = 0 ∧
      cartanPair A β γ = 0

theorem commutator_commutator_eq_of_mem_lambdaSet (h : Hyp G R) (hA : A ∈ R)
    (hAne : sigmaSet R A ≠ lambdaSet R A) (hA₀ : A₀ ∈ omegaSet R A) {X P Q : Subgroup G}
    (hX : X ∈ lambdaStar R A A₀) (hP : P ∈ leviSet R A A₀) (hQ : Q ∈ leviSet R A A₀)
    (hQP : Opposite Q P) (hXl : X ∈ lambdaSet R Q) (hsXP : Special R X P) :
    ⁅Q, ⁅P, X⁆⁆ = X := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hXR : X ∈ R := hX.1.1.1
  have hPR : P ∈ R := hP.1.1
  have hQR : Q ∈ R := hQ.1.1
  have hXψ : X ∈ psiSet R P := ⟨hXR, hsXP.symm⟩
  have hinv : ∀ x ∈ Q ⊔ P, conjSub (X ⊔ ⁅P, X⁆) x = X ⊔ ⁅P, X⁆ := fun x hx =>
    Sec3.conjSub_sup_commutator_eq hR hiso hQR hPR hQP hXl hXψ hx
  have hfix : ∀ m ∈ X ⊔ ⁅P, X⁆, (∀ y ∈ Q, Commute y m) → m ∈ X := fun m hm hmQ =>
    Sec3.mem_of_forall_commute_of_mem_sup hR hiso hQR hPR hQP hXl hXψ hm hmQ
  have hD : ⁅X, P⁆ ∈ lambdaStar R A A₀ := (commutator_mem_lambdaStar h hA hAne hA₀ hX hP hsXP).1
  have hDR : ⁅P, X⁆ ∈ R := hsXP.symm.1
  have hDX : ⁅P, X⁆ ≠ X := by
    have := hsXP.ne_commutator hR
    rw [Subgroup.commutator_comm X P] at this
    exact this.symm
  have hsQD : Special R Q ⁅P, X⁆ := by
    have hnc : ¬ Commuting Q ⁅P, X⁆ := by
      intro hc
      refine hDX (Subgroup.eq_of_le_of_card_ge (fun d hd => ?_) (hR.card_eq hXR hDR).le)
      exact hfix d (Subgroup.mem_sup_right hd) fun y hy => hc y hy d hd
    have hne : Q ≠ ⁅P, X⁆ := fun e => hnc (by rw [← e]; exact hR.commuting_self hQR)
    rcases hR.rel _ hQR _ hDR hne with hc | ho | hs
    · exact absurd hc hnc
    · rw [Subgroup.commutator_comm] at ho
      exact absurd ho (CaseD4.not_opposite_of_mem_leviSet hR hA hD hQ)
    · exact hs
  have hQN : Q ≤ Subgroup.normalizer ((X ⊔ ⁅P, X⁆ : Subgroup G) : Set G) := fun y hy =>
    conjSub_eq_self_iff.1 (hinv y (Subgroup.mem_sup_left hy))
  refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) (hR.card_eq hXR hsQD.1).le
  exact hfix x (Linear.commutator_le_of_le_normalizer hQN le_sup_right hx) fun y hy =>
    (hsQD.2.1 x hx y hy).symm

theorem highest_pattern (h : Hyp G R) (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
    (hmax : IsSigmaMaximal R (centralGroup R A)) (hA₀ : A₀ ∈ omegaSet R A)
    (hF : CompFrame R A A₀ D n H Ψ) (hpd : (D.cartan.map (Int.cast : ℤ → ℚ)).PosDef)
    {adj : Fin D.rank → Fin D.rank → Prop}
    (hX : IsConfig R adj (fun k => (D.rootGroup (Pi.single k 1)).map Ψ)
      (fun k => (D.rootGroup (-Pi.single k 1)).map Ψ))
    (hadj : ∀ a b, D.cartan a b = -1 → adj a b ∨ adj b a) {E : Subgroup G}
    (hE : E ∈ lambdaStar R A A₀) (hEU : Commuting E ((negUnipotent D).map Ψ)) {j : Fin D.rank}
    (hj : ∀ k, ¬ Commuting E ((D.rootGroup (Pi.single k 1)).map Ψ) ↔ k = j)
    {w₀ : (coxeterMatrix D.isFiniteType).Group} {σ : Fin D.rank → Fin D.rank}
    (hσ : ∀ k, weylAction D.isFiniteType w₀ (Pi.single k 1) = -Pi.single (σ k) 1)
    (hσinj : Function.Injective σ) (hσj : σ j = j) {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots)
    (hnc : ¬ Commuting (conjSub E (Ψ (nrep hF.hct w₀))⁻¹) ((D.rootGroup γ).map Ψ)) :
    γ j = -1 := by
  set Φ := RootSystem.ofCartan D.isFiniteType D.divisible
  set δ := weylAction D.isFiniteType w₀ γ with hδ
  have hδr : δ ∈ D.roots := weylAction_mem_roots _ _ hγ
  have hEδ : ¬ Commuting E ((D.rootGroup δ).map Ψ) := by
    intro hc
    refine hnc ?_
    rw [← commuting_conjSub_iff' (Ψ (nrep hF.hct w₀)), ← conjSub_mul, mul_inv_cancel,
      conjSub_one, map_conjSub_eq, actsAs_nrep hF.hct w₀ _ hγ]
    exact hc
  have hS : ∀ k, k ∈ ({j} : Finset (Fin D.rank)) ↔
      ¬ Commuting E ((D.rootGroup (Pi.single k 1)).map Ψ) := fun k => by
    rw [Finset.mem_singleton, hj]
  have hδj : δ j = 1 := by
    rcases Φ.sign δ hδr with h0 | h0
    · have h1 := (level_zero_or_one h hA hAne hmax hA₀ hF hpd hE hEU hS hδr h0).1
      have h2 := level_le_one h hA hAne hmax hA₀ hF hpd hE hEU hX hadj hS hδr h0
      simp only [Finset.sum_singleton] at h1 h2
      have h3 := h0 j
      by_contra hne
      exact hEδ (h1 (by omega))
    · exfalso
      refine hEδ (hEU.mono le_rfl (map_rootGroup_le_map_negUnipotent hδr ?_))
      exact ht_neg_of_nonpos hδr fun k => by simpa using h0 k
  have e := weylAction_inv_apply_self_of_neg D.isFiniteType hσ hσinj hσj δ
  rw [hδ, weylAction_inv_apply_apply] at e
  rw [e, ← hδ, hδj]

theorem false_of_levelInv (hS : Sec13 R A A₀) (hF : LeviFrame R A A₀ D n H Ψ)
    (hpd : (D.cartan.map (Int.cast : ℤ → ℚ)).PosDef) {adj : Fin D.rank → Fin D.rank → Prop}
    (hX : IsConfig R adj (fun k => (D.rootGroup (Pi.single k 1)).map Ψ)
      (fun k => (D.rootGroup (-Pi.single k 1)).map Ψ))
    (hadj : ∀ a b, D.cartan a b = -1 → adj a b ∨ adj b a) {E : Subgroup G}
    (hE : E ∈ lambdaStar R A A₀) (hEU : Commuting E ((negUnipotent D).map Ψ)) {j : Fin D.rank}
    (hj : ∀ k, ¬ Commuting E ((D.rootGroup (Pi.single k 1)).map Ψ) ↔ k = j)
    (hstar : StarAt D.cartan D.isFiniteType j) : False := by
  have h := hS.hyp
  have := h.finite
  have hR := h.root
  set Φ := RootSystem.ofCartan D.isFiniteType D.divisible
  obtain ⟨w₀, σ, -, hσ, hσinj, hσj, hC, hCU, hCT, -, -, hCQ, hCPl, -⟩ :=
    exists_caseENode_highest h hS.mem hS.sec8.2 hS.max hS.opp hF hpd hX hadj hE hEU hj
  set C := conjSub E (Ψ (nrep hF.hct w₀))⁻¹ with hCdef
  have hpat : ∀ γ ∈ D.roots, ¬ Commuting C ((D.rootGroup γ).map Ψ) → γ j = -1 :=
    fun γ hγ hnc => highest_pattern h hS.mem hS.sec8.2 hS.max hS.opp hF.toCompFrame hpd hX hadj
      hE hEU hj hσ hσinj hσj hγ hnc
  have hB : borel D H ≤ stabOf Ψ C := borel_le_stabOf hCT hCU
  have hPk : ∀ k, Commuting C ((D.rootGroup (Pi.single k 1)).map Ψ) := fun k =>
    hCU.mono le_rfl (Subgroup.map_mono (rootGroup_le_posUnipotent (Φ.single_mem k)
      (ht_single_pos k)))
  have hQj : ¬ Commuting C ((D.rootGroup (-Pi.single j 1)).map Ψ) := fun hc =>
    ((hCQ j).1 hc) rfl
  have hn : ∀ k, k ≠ j → n k ∈ stabOf Ψ C := fun k hk =>
    n_mem_stabOf hF.toCompFrame k (hPk k) ((hCQ k).2 hk)
  have hpar := mem_parabolic_of_nrep_mem_stabOf hF.hct hCU hQj hn
  have hSt : ∀ g ∈ stabOf Ψ C, g ∈ cellUnion hF.hct
      ((coxeterMatrix D.isFiniteType).toCoxeterSystem.parabolic {k | k ≠ j} : Set _) :=
    fun g hg => stabOf_subset_cellUnion hF.hct hF.hext hB hpar hg
  set w₃ := (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple j * w₀ with hw₃
  set C' := conjSub C (Ψ (nrep hF.hct w₃)) with hC'def
  have hC' : C' ∈ lambdaStar R A A₀ := conjSub_mem_lambdaStar_of_mem_levi hR hC (hF.range _)
  have hαj : (Pi.single j 1 : Fin D.rank → ℤ) ∈ D.roots := Φ.single_mem j
  have hw₃α : weylAction D.isFiniteType w₃⁻¹ (Pi.single j 1) = Pi.single j 1 := by
    have h1 : weylAction D.isFiniteType w₀ (Pi.single j 1) = -Pi.single j 1 := by
      rw [hσ j, hσj]
    rw [hw₃, mul_inv_rev, CoxeterSystem.inv_simple, weylAction_mul_apply,
      weylAction_simple_single, ← h1, weylAction_inv_apply_apply]
  have hC'P : Commuting C' ((D.rootGroup (Pi.single j 1)).map Ψ) := by
    rw [← commuting_conjSub_iff' (Ψ (nrep hF.hct w₃))⁻¹, hC'def, ← conjSub_mul, inv_mul_cancel,
      conjSub_one, ← map_inv, map_conjSub_eq, (actsAs_nrep hF.hct w₃).inv _ hαj, hw₃α]
    exact hPk j
  have hCC' : Commuting C C' := by
    have hPl := hF.mem _ hαj
    have hQl := hF.mem _ (Φ.neg_mem _ hαj)
    have hsCQ : Special R C ((D.rootGroup (-Pi.single j 1)).map Ψ) :=
      special_of_not_commuting_of_mem_leviSet h hS.mem hC hQl hQj
    have hid := commutator_commutator_eq_of_mem_lambdaSet h hS.mem hS.sec8.2 hS.opp hC hQl hPl
      (hF.opp j) hCPl hsCQ
    have hDs : ⁅(D.rootGroup (-Pi.single j 1)).map Ψ, C⁆ ∈ lambdaStar R A A₀ := by
      have := (commutator_mem_lambdaStar h hS.mem hS.sec8.2 hS.opp hC hQl hsCQ).1
      rwa [Subgroup.commutator_comm] at this
    obtain ⟨-, -, hcommA, -, -⟩ := Q_eq_M h hS.mem
    have hle : ⁅⁅(D.rootGroup (-Pi.single j 1)).map Ψ, C⁆, C'⁆ ≤ A := by
      rw [← hcommA]
      exact Subgroup.commutator_mono (QD.le_M hDs.1) (QD.le_M hC'.1)
    have hAP : ⁅A, (D.rootGroup (Pi.single j 1)).map Ψ⁆ = ⊥ :=
      commuting_iff_commutator_eq_bot.1 hPl.1.2.2
    rw [commuting_iff_commutator_eq_bot, ← hid]
    refine Subgroup.commutator_commutator_eq_bot_of_rotate ?_ ?_
    · exact eq_bot_iff.2 ((Subgroup.commutator_mono hle le_rfl).trans hAP.le)
    · rw [commuting_iff_commutator_eq_bot.1 hC'P, Subgroup.commutator_bot_left]
  obtain ⟨Dm, ⟨hDm, hDC⟩, hDC'⟩ := hS.lambdaStar_inter_nonempty hS.leviClosed hC hC' hCC'
  obtain ⟨v, hv, hvD⟩ :=
    exists_mem_levi_conjSub_eq_of_isSigmaMaximal h hS.mem hS.sec8.2 hS.max hS.opp hC hDm
  obtain ⟨g, rfl⟩ := hF.surj v hv
  have hDCl : conjSub C (Ψ g) ∈ lambdaSet R C := by
    rw [hvD]
    exact hDC
  obtain ⟨a₁, ha₁, b₁, hb₁, hg⟩ :=
    exists_eq_mul_n_mul_of_mem_lambdaSet hS hF hpd hC hCU hCT hCQ hCPl hpat hDCl
  have hC'l : conjSub C (Ψ (g⁻¹ * nrep hF.hct w₃)) ∈ lambdaSet R C := by
    have h1 : C' ∈ lambdaSet R Dm := mem_lambdaSet_comm hC'.1.1.1 hDC'
    have h2 := conjSub_mem_lambdaSet hR h1 (Ψ g)⁻¹
    rw [← hvD, ← conjSub_mul, inv_mul_cancel, conjSub_one, hC'def, ← conjSub_mul, ← map_inv,
      ← map_mul] at h2
    exact h2
  obtain ⟨a₂, ha₂, b₂, hb₂, hg'⟩ :=
    exists_eq_mul_n_mul_of_mem_lambdaSet hS hF hpd hC hCU hCT hCQ hCPl hpat hC'l
  have hw : nrep hF.hct w₃ = a₁ * n j * (b₁ * a₂) * n j * b₂ := by
    calc nrep hF.hct w₃ = g * (g⁻¹ * nrep hF.hct w₃) := by group
      _ = _ := by rw [hg', hg]; group
  have hcell := mem_cellUnion_twoStep hF.hct hF.hext hSt ha₁ (mul_mem hb₁ ha₂) hb₂
  rw [← hw] at hcell
  obtain ⟨y, hy, hny⟩ := (mem_cellUnion hF.hct).1 hcell
  have hyw : w₃ = y := eq_of_mem_bruhatCell hF.hct hF.hext (nrep_mem_bruhatCell hF.hct w₃) hny
  obtain ⟨u, hu, v', hv', z, hz, hyz⟩ := hy
  obtain ⟨β₁, β₂, hne, h1, h2⟩ := exists_two_mem_levelInv D.isFiniteType hpd hstar hu hv' hz
  rw [← hyz, ← hyw] at h1 h2
  exact hne ((levelInv_simple_mul_subset D.isFiniteType hpd hσ hσinj hσj h1).trans
    (levelInv_simple_mul_subset D.isFiniteType hpd hσ hσinj hσj h2).symm)

end CFSG.Timmesfeld.ARS
