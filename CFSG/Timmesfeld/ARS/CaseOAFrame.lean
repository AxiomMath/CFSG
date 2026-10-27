module

public import CFSG.Timmesfeld.ARS.CaseEFrame
public import CFSG.Timmesfeld.ARS.Induction
public import CFSG.Timmesfeld.ARS.Sec9Two

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open _root_.CFSG.Timmesfeld.ARS.Levi

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace CaseOA

theorem edgeRel_of_natural (h : Hyp G R) {A A₀ P Q E F : Subgroup G} (hA : A ∈ R)
    (hAne : sigmaSet R A ≠ lambdaSet R A) (hA₀ : A₀ ∈ omegaSet R A)
    (hPl : P ∈ leviSet R A A₀) (hQl : Q ∈ leviSet R A A₀) (hPQ : Opposite P Q)
    (hE : E ∈ lambdaStar R A A₀) (hEQ : E ∈ lambdaSet R Q) (hsPE : Special R P E)
    (hF : F ∈ lambdaStar R A₀ A) (hFP : F ∈ lambdaSet R P) (hsQF : Special R Q F)
    (hEF : Opposite E F) : EdgeRel R P E Q F := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hPR : P ∈ R := hPl.1.1
  have hQR : Q ∈ R := hQl.1.1
  have hER : E ∈ R := hE.1.1.1
  have hFR : F ∈ R := hF.1.1.1
  have hop : Opposite Q P := hPQ.symm
  have hEψ : E ∈ psiSet R P := ⟨hER, hsPE⟩
  have hinv : ∀ x ∈ Q ⊔ P, conjSub (E ⊔ ⁅P, E⁆) x = E ⊔ ⁅P, E⁆ := fun x hx =>
    Sec3.conjSub_sup_commutator_eq hR hiso hQR hPR hop hEQ hEψ hx
  have hfix : ∀ n ∈ E ⊔ ⁅P, E⁆, (∀ y ∈ Q, Commute y n) → n ∈ E := fun n hn hnQ =>
    Sec3.mem_of_forall_commute_of_mem_sup hR hiso hQR hPR hop hEQ hEψ hn hnQ
  set D := ⁅P, E⁆ with hDdef
  have hDR : D ∈ R := hsPE.1
  have hD : D ∈ lambdaStar R A A₀ := by
    have := (exists_opposite_of_mem_lambdaStar h hA hAne hA₀ hPl hE hsPE.symm).1 D hDR
    rw [Subgroup.commutator_comm E P] at this
    exact this le_sup_right
  have hDE : D ≠ E := by
    have := hsPE.symm.ne_commutator hR
    rw [Subgroup.commutator_comm E P] at this
    exact this.symm
  have hQN : Q ≤ Subgroup.normalizer ((E ⊔ D : Subgroup G) : Set G) := fun y hy =>
    conjSub_eq_self_iff.1 (hinv y (Subgroup.mem_sup_left hy))
  have hsQD : Special R Q D := by
    have hnc : ¬ Commuting Q D := by
      intro hc
      refine hDE (Subgroup.eq_of_le_of_card_ge (fun d hd => ?_) (hR.card_eq hER hDR).le)
      exact hfix d (Subgroup.mem_sup_right hd) fun y hy => hc y hy d hd
    have hne : Q ≠ D := fun e => hnc (by rw [← e]; exact hR.commuting_self hQR)
    rcases hR.rel _ hQR _ hDR hne with hc | ho | hs
    · exact absurd hc hnc
    · exact absurd ho (CaseD4.not_opposite_of_mem_leviSet hR hA hD hQl)
    · exact hs
  have h3 : ⁅Q, D⁆ = E := by
    refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) (hR.card_eq hER hsQD.1).le
    exact hfix x (Linear.commutator_le_of_le_normalizer hQN le_sup_right hx) fun y hy =>
      (hsQD.2.1 x hx y hy).symm
  have hPFl : P ∈ lambdaSet R F := mem_lambdaSet_comm hPR hFP
  have hPψ : P ∈ psiSet R E := ⟨hPR, hsPE.symm⟩
  have hinv' : ∀ x ∈ F ⊔ E, conjSub (P ⊔ ⁅E, P⁆) x = P ⊔ ⁅E, P⁆ := fun x hx =>
    Sec3.conjSub_sup_commutator_eq hR hiso hFR hER hEF.symm hPFl hPψ hx
  have hfix' : ∀ n ∈ P ⊔ ⁅E, P⁆, (∀ a ∈ F, Commute a n) → n ∈ P := fun n hn hnF =>
    Sec3.mem_of_forall_commute_of_mem_sup hR hiso hFR hER hEF.symm hPFl hPψ hn hnF
  rw [Subgroup.commutator_comm E P] at hinv' hfix'
  have hFN : F ≤ Subgroup.normalizer ((P ⊔ D : Subgroup G) : Set G) := fun f hf =>
    conjSub_eq_self_iff.1 (hinv' f (Subgroup.mem_sup_left hf))
  have hsDF : Special R D F := by
    have hnc : ¬ Commuting D F := by
      intro hc
      have hDP : D = P := Subgroup.eq_of_le_of_card_ge (fun d hd =>
        hfix' d (Subgroup.mem_sup_right hd) fun f hf => (hc d hd f hf).symm)
        (hR.card_eq hPR hDR).le
      exact hD.2.2.not_commuting hR (hDP ▸ hPl.2.2.2)
    have hne : D ≠ F := fun e => hnc (by rw [← e]; exact hR.commuting_self hDR)
    rcases hR.rel _ hDR _ hFR hne with hc | ho | hs
    · exact absurd hc hnc
    · exact absurd hsPE.2.1 (not_commuting_of_opposite_of_mem_lambdaSet hR hDR ho hPFl)
    · exact hs
  have h5 : ⁅D, F⁆ = P := by
    refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) (hR.card_eq hPR hsDF.1).le
    exact hfix' x (commutator_le_of_le_normalizer le_sup_right hFN hx) fun f hf =>
      (hsDF.2.2 x hx f hf).symm
  exact ⟨hsPE, hEQ.1.2.2, h3, hFP.1.2.2, h5, hsQF⟩

section SL2

variable (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
  (hmax : IsSigmaMaximal R (centralGroup R A)) (hA₀ : A₀ ∈ omegaSet R A)
  {Δ : Set (Subgroup G)} (hΔ : Δ ∈ leviComps R A A₀) {P Q : Subgroup G} (hP : P ∈ Δ)
  (hQ : Q ∈ Δ) (hPQ : Opposite P Q) (hgen : gen Δ = P ⊔ Q)
include h hA hAne hmax hA₀ hΔ hP hQ hPQ hgen

theorem natural_of_sl2 {X : Subgroup G} (hX : X ∈ lambdaStar R A A₀) (hQX : Commuting Q X) :
    X ∈ lambdaSet R Q ∧ Special R P X := by
  have := h.finite
  have hPl := Sec9.mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ hP
  have hQl := Sec9.mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ hQ
  have hfix : ∀ T ∈ lambdaStar R A A₀, Commuting P T → Commuting Q T → False := by
    intro T hT hPT hQT
    refine Sec9.not_forall_commuting h hA hAne hA₀ hmax hΔ hT fun Y hY => ?_
    exact (Commuting.sup_left hPT hQT).mono (hgen ▸ le_gen hY) le_rfl
  exact ⟨CaseD4.mem_lambdaSet_of_commuting_of_not h hA hAne hA₀ hQl hPl hPQ.symm hfix hX hQX,
    CaseD4.special_of_commuting_of_not h.root hA hX hPl (fun hc hc' => hfix X hX hc' hc) hQX⟩

theorem edgeRel_sl2 {E F : Subgroup G} (hE : E ∈ lambdaStar R A A₀) (hQE : Commuting Q E)
    (hF : F ∈ lambdaStar R A₀ A) (hPF : Commuting P F) (hEF : Opposite E F) :
    EdgeRel R P E Q F := by
  have hR := h.root
  have hPl := Sec9.mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ hP
  have hQl := Sec9.mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ hQ
  obtain ⟨hEQ, hsPE⟩ := natural_of_sl2 h hA hAne hmax hA₀ hΔ hP hQ hPQ hgen hE hQE
  have hA₀R : A₀ ∈ R := hA₀.1
  have hl : leviSet R A₀ A = leviSet R A A₀ := Set.inter_comm _ _
  have hΔ' : Δ ∈ leviComps R A₀ A := by
    obtain ⟨E₀, hE₀, rfl⟩ := hΔ
    refine ⟨E₀, hl ▸ hE₀, ?_⟩
    simp only [comp, hl]
  have hgen' : gen Δ = Q ⊔ P := by rw [hgen, sup_comm]
  obtain ⟨hFP, hsQF⟩ := natural_of_sl2 h hA₀R (sigmaSet_ne_lambdaSet_of_mem hR hA hA₀R hAne)
    (isSigmaMaximal_centralGroup_of_mem hR hA hA₀R hmax) ⟨hA, hA₀.2.symm⟩ hΔ' hQ hP hPQ.symm
    hgen' hF hPF
  exact edgeRel_of_natural h hA hAne hA₀ hPl hQl hPQ hE hEQ hsPE hF hFP hsQF hEF

end SL2

theorem levi_sup_sup_eq_top (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R)
    (hAne : sigmaSet R A ≠ lambdaSet R A) (hmax : IsSigmaMaximal R (centralGroup R A))
    (hA₀ : A₀ ∈ omegaSet R A) {E F : Subgroup G} (hE : E ∈ lambdaStar R A A₀)
    (hF : F ∈ lambdaStar R A₀ A) : levi R A A₀ ⊔ E ⊔ F = ⊤ := by
  have hR := h.root
  have hA₀R : A₀ ∈ R := hA₀.1
  have hAΩ : A ∈ omegaSet R A₀ := ⟨hA, hA₀.2.symm⟩
  set H := levi R A A₀ ⊔ E ⊔ F with hH
  have hV : levi R A A₀ ≤ H := le_sup_left.trans le_sup_left
  have hV' : levi R A₀ A ≤ H := by
    have e : levi R A₀ A = levi R A A₀ := by simp only [levi, leviSet, Set.inter_comm]
    rw [e]
    exact hV
  have hMA : M R A ≤ H := by
    rw [M_eq_gen_lambdaStar h hA hA₀]
    refine gen_le fun Y hY => ?_
    obtain ⟨v, hv, rfl⟩ := exists_mem_levi_conjSub_eq_of_isSigmaMaximal h hA hAne hmax hA₀ hE hY
    exact conjSub_le (le_sup_right.trans le_sup_left) (hV hv)
  have hMA₀ : M R A₀ ≤ H := by
    rw [M_eq_gen_lambdaStar h hA₀R hAΩ]
    refine gen_le fun Y hY => ?_
    obtain ⟨v, hv, rfl⟩ := exists_mem_levi_conjSub_eq_of_isSigmaMaximal h hA₀R
      (sigmaSet_ne_lambdaSet_of_mem hR hA hA₀R hAne)
      (isSigmaMaximal_centralGroup_of_mem hR hA hA₀R hmax) hAΩ hF hY
    exact conjSub_le le_sup_right (hV' hv)
  rw [eq_top_iff, ← gen_lambdaSet_sup_eq_top h hA hA₀]
  exact sup_le ((gen_le fun B hB => QD.le_M hB).trans hMA) (QD.le_M_self.trans hMA₀)

theorem levi_le_sup_of_card_two (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R)
    (hAne : sigmaSet R A ≠ lambdaSet R A) (hA₀ : A₀ ∈ omegaSet R A)
    (h2 : Nat.card (leviComps R A A₀) = 2) {Δ₁ Δ₂ : Set (Subgroup G)}
    (hΔ₁ : Δ₁ ∈ leviComps R A A₀) (hΔ₂ : Δ₂ ∈ leviComps R A A₀) (hne : Δ₁ ≠ Δ₂) :
    levi R A A₀ ≤ gen Δ₁ ⊔ gen Δ₂ := by
  have := h.finite
  have hcard : Nat.card (leviComps R A A₀) = (leviComps R A A₀).ncard := Nat.card_coe_set_eq _
  rw [hcard, Set.ncard_eq_two] at h2
  obtain ⟨X, Y, hXY, hXYs⟩ := h2
  have hmem : ∀ Δ ∈ leviComps R A A₀, Δ = Δ₁ ∨ Δ = Δ₂ := by
    have h1 : Δ₁ = X ∨ Δ₁ = Y := by rw [hXYs] at hΔ₁; simpa using hΔ₁
    have h2' : Δ₂ = X ∨ Δ₂ = Y := by rw [hXYs] at hΔ₂; simpa using hΔ₂
    intro Δ hΔ
    have h3 : Δ = X ∨ Δ = Y := by rw [hXYs] at hΔ; simpa using hΔ
    rcases h1 with rfl | rfl <;> rcases h2' with rfl | rfl <;> rcases h3 with rfl | rfl <;>
      simp_all
  rw [Sec9.levi_eq_iSup_gen h hA hAne hA₀]
  refine iSup_le fun Δ => ?_
  rcases hmem Δ Δ.2 with e | e
  · rw [e]; exact le_sup_left
  · rw [e]; exact le_sup_right

end CaseOA

theorem IsConfig.extend_D {n : ℕ} (hn : 4 ≤ n) {P Q : Fin n → Subgroup G}
    (hX : IsConfig R (edgeD n) P Q) {E F : Subgroup G} (hER : E ∈ R) (hFR : F ∈ R)
    (hEF : Opposite E F)
    (hcomm : ∀ k : Fin n, k ≠ ⟨0, by omega⟩ → Commuting E (P k) ∧ Commuting E (Q k) ∧
      Commuting F (P k) ∧ Commuting F (Q k))
    (hedge : EdgeRel R E (P ⟨0, by omega⟩) F (Q ⟨0, by omega⟩)) :
    IsConfig R (edgeD (n + 1)) (Fin.cons E P) (Fin.cons F Q) := by
  refine hX.extend hER hFR hEF hcomm hedge Fin.succ 0 (fun k => Fin.succ_ne_zero k)
    (fun x => ?_) (fun a b hab => ?_) (fun a b hab => ?_) (fun k hk => ?_) ?_ ?_
    (fun k => Fin.cons_succ _ _ k) (fun k => Fin.cons_succ _ _ k) rfl rfl
  · refine Fin.cases (Or.inl rfl) (fun k => Or.inr ⟨k, rfl⟩) x
  · left
    simp only [edgeD, Fin.val_succ] at hab ⊢
    omega
  · left
    simp only [edgeD, Fin.val_succ] at hab ⊢
    omega
  · simp only [edgeD, Fin.val_succ, Fin.val_zero] at hk
    exact Fin.ext (by simp only; omega)
  · left
    simp only [edgeD, Fin.val_succ, Fin.val_zero, true_and]
    omega
  · simp only [edgeD, Fin.val_zero]
    omega

theorem IsConfig.extend_A3 {P Q : Fin 3 → Subgroup G} (hX : IsConfig R (edgeA 3) P Q)
    {E F : Subgroup G} (hER : E ∈ R) (hFR : F ∈ R) (hEF : Opposite E F)
    (hcomm : ∀ k : Fin 3, k ≠ 1 → Commuting E (P k) ∧ Commuting E (Q k) ∧
      Commuting F (P k) ∧ Commuting F (Q k))
    (hedge : EdgeRel R E (P 1) F (Q 1)) :
    IsConfig R (edgeD 4) ![E, P 1, P 0, P 2] ![F, Q 1, Q 0, Q 2] :=
  hX.extend hER hFR hEF hcomm hedge ![2, 1, 3] 0 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by intro k; fin_cases k <;> rfl)
    (by intro k; fin_cases k <;> rfl) rfl rfl

namespace CaseOA

variable (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
  (hmax : IsSigmaMaximal R (centralGroup R A)) (hA₀ : A₀ ∈ omegaSet R A)
  (h2 : Nat.card (leviComps R A A₀) = 2) {Δ₁ Δ₂ : Set (Subgroup G)}
  (hΔ₁ : Δ₁ ∈ leviComps R A A₀) (hΔ₂ : Δ₂ ∈ leviComps R A A₀) (hne : Δ₁ ≠ Δ₂)
  {P₂ Q₂ : Subgroup G} (hP₂ : P₂ ∈ Δ₂) (hQ₂ : Q₂ ∈ Δ₂) (hPQ₂ : Opposite P₂ Q₂)
  (hgen₂ : gen Δ₂ = P₂ ⊔ Q₂) {E F : Subgroup G} (hE : E ∈ lambdaStar R A A₀)
  (hF : F ∈ lambdaStar R A₀ A) (hEF : Opposite E F) (hQE : Commuting Q₂ E)
  (hPF : Commuting P₂ F)
include h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hP₂ hQ₂ hPQ₂ hgen₂ hE hF hEF hQE hPF

theorem hasGenConfig_D {m : ℕ} (hm : 4 ≤ m) {P Q : Fin m → Subgroup G}
    (hX : IsConfig R (edgeD m) P Q) (hPQ : ∀ k, P k ∈ Δ₁ ∧ Q k ∈ Δ₁)
    (hgen₁ : ⨆ k, (P k ⊔ Q k) = gen Δ₁)
    (hcomm : ∀ k : Fin m, k ≠ ⟨0, by omega⟩ → Commuting E (P k) ∧ Commuting E (Q k) ∧
      Commuting F (P k) ∧ Commuting F (Q k))
    (hedge : EdgeRel R (P ⟨0, by omega⟩) E (Q ⟨0, by omega⟩) F) :
    HasGenConfig R (edgeD (m + 2)) := by
  have hR := h.root
  have hER : E ∈ R := hE.1.1.1
  have hFR : F ∈ R := hF.1.1.1
  have hP₂R : P₂ ∈ R := (Sec9.mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₂ hP₂).1.1
  have hQ₂R : Q₂ ∈ R := (Sec9.mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₂ hQ₂).1.1
  have hX₁ : IsConfig R (edgeD (m + 1)) (Fin.cons E P) (Fin.cons F Q) :=
    hX.extend_D hm hER hFR hEF hcomm hedge.symm
  have hcomm₂ : ∀ k : Fin (m + 1), k ≠ ⟨0, by omega⟩ →
      Commuting P₂ ((Fin.cons E P : Fin (m + 1) → Subgroup G) k) ∧
      Commuting P₂ ((Fin.cons F Q : Fin (m + 1) → Subgroup G) k) ∧
      Commuting Q₂ ((Fin.cons E P : Fin (m + 1) → Subgroup G) k) ∧
      Commuting Q₂ ((Fin.cons F Q : Fin (m + 1) → Subgroup G) k) := by
    intro k hk
    obtain ⟨k', rfl⟩ : ∃ k', Fin.succ k' = k := Fin.exists_succ_eq.2 fun e => hk (e ▸ rfl)
    simp only [Fin.cons_succ]
    have c := fun {X Y : Subgroup G} (hX : X ∈ Δ₂) (hY : Y ∈ Δ₁) =>
      Sec9.commuting_of_ne h hA hAne hA₀ hΔ₂ hΔ₁ (Ne.symm hne) hX hY
    exact ⟨c hP₂ (hPQ k').1, c hP₂ (hPQ k').2, c hQ₂ (hPQ k').1, c hQ₂ (hPQ k').2⟩
  have hedge₂ : EdgeRel R P₂ ((Fin.cons E P : Fin (m + 1) → Subgroup G) ⟨0, by omega⟩) Q₂
      ((Fin.cons F Q : Fin (m + 1) → Subgroup G) ⟨0, by omega⟩) :=
    edgeRel_sl2 h hA hAne hmax hA₀ hΔ₂ hP₂ hQ₂ hPQ₂ hgen₂ hE hQE hF hPF hEF
  have hX₂ := hX₁.extend_D (by omega) hP₂R hQ₂R hPQ₂ hcomm₂ hedge₂
  refine ⟨_, _, hX₂, eq_top_iff.2 ?_⟩
  rw [← levi_sup_sup_eq_top h hA hAne hmax hA₀ hE hF]
  set S := ⨆ x, ((Fin.cons P₂ (Fin.cons E P) : Fin (m + 2) → Subgroup G) x ⊔
    (Fin.cons Q₂ (Fin.cons F Q) : Fin (m + 2) → Subgroup G) x) with hS
  have hle : ∀ x : Fin (m + 2), (Fin.cons P₂ (Fin.cons E P) : Fin (m + 2) → Subgroup G) x ⊔
      (Fin.cons Q₂ (Fin.cons F Q) : Fin (m + 2) → Subgroup G) x ≤ S := fun x =>
    le_iSup (fun x => (Fin.cons P₂ (Fin.cons E P) : Fin (m + 2) → Subgroup G) x ⊔
      (Fin.cons Q₂ (Fin.cons F Q) : Fin (m + 2) → Subgroup G) x) x
  have h0 : P₂ ⊔ Q₂ ≤ S := hle 0
  have h1 : E ⊔ F ≤ S := hle (Fin.succ 0)
  have hk : ∀ k, P k ⊔ Q k ≤ S := fun k => hle (Fin.succ (Fin.succ k))
  refine sup_le (sup_le ((levi_le_sup_of_card_two h hA hAne hA₀ h2 hΔ₁ hΔ₂ hne).trans
    (sup_le (hgen₁ ▸ iSup_le hk) (hgen₂ ▸ h0))) (le_sup_left.trans h1))
    (le_sup_right.trans h1)

theorem hasGenConfig_A3 {P Q : Fin 3 → Subgroup G} (hX : IsConfig R (edgeA 3) P Q)
    (hPQ : ∀ k, P k ∈ Δ₁ ∧ Q k ∈ Δ₁) (hgen₁ : ⨆ k, (P k ⊔ Q k) = gen Δ₁)
    (hcomm : ∀ k : Fin 3, k ≠ 1 → Commuting E (P k) ∧ Commuting E (Q k) ∧
      Commuting F (P k) ∧ Commuting F (Q k))
    (hedge : EdgeRel R (P 1) E (Q 1) F) : HasGenConfig R (edgeD 5) := by
  have hR := h.root
  have hER : E ∈ R := hE.1.1.1
  have hFR : F ∈ R := hF.1.1.1
  have hP₂R : P₂ ∈ R := (Sec9.mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₂ hP₂).1.1
  have hQ₂R : Q₂ ∈ R := (Sec9.mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₂ hQ₂).1.1
  have hX₁ := hX.extend_A3 hER hFR hEF hcomm hedge.symm
  have c := fun {X Y : Subgroup G} (hX : X ∈ Δ₂) (hY : Y ∈ Δ₁) =>
    Sec9.commuting_of_ne h hA hAne hA₀ hΔ₂ hΔ₁ (Ne.symm hne) hX hY
  have hcomm₂ : ∀ k : Fin 4, k ≠ ⟨0, by omega⟩ →
      Commuting P₂ (![E, P 1, P 0, P 2] k) ∧ Commuting P₂ (![F, Q 1, Q 0, Q 2] k) ∧
      Commuting Q₂ (![E, P 1, P 0, P 2] k) ∧ Commuting Q₂ (![F, Q 1, Q 0, Q 2] k) := by
    intro k hk
    fin_cases k
    · exact absurd rfl hk
    · exact ⟨c hP₂ (hPQ 1).1, c hP₂ (hPQ 1).2, c hQ₂ (hPQ 1).1, c hQ₂ (hPQ 1).2⟩
    · exact ⟨c hP₂ (hPQ 0).1, c hP₂ (hPQ 0).2, c hQ₂ (hPQ 0).1, c hQ₂ (hPQ 0).2⟩
    · exact ⟨c hP₂ (hPQ 2).1, c hP₂ (hPQ 2).2, c hQ₂ (hPQ 2).1, c hQ₂ (hPQ 2).2⟩
  have hedge₂ : EdgeRel R P₂ (![E, P 1, P 0, P 2] ⟨0, by omega⟩) Q₂
      (![F, Q 1, Q 0, Q 2] ⟨0, by omega⟩) :=
    edgeRel_sl2 h hA hAne hmax hA₀ hΔ₂ hP₂ hQ₂ hPQ₂ hgen₂ hE hQE hF hPF hEF
  have hX₂ := hX₁.extend_D le_rfl hP₂R hQ₂R hPQ₂ hcomm₂ hedge₂
  refine ⟨_, _, hX₂, eq_top_iff.2 ?_⟩
  rw [← levi_sup_sup_eq_top h hA hAne hmax hA₀ hE hF]
  set S := ⨆ x, ((Fin.cons P₂ ![E, P 1, P 0, P 2] : Fin 5 → Subgroup G) x ⊔
    (Fin.cons Q₂ ![F, Q 1, Q 0, Q 2] : Fin 5 → Subgroup G) x) with hS
  have hle : ∀ x : Fin 5, (Fin.cons P₂ ![E, P 1, P 0, P 2] : Fin 5 → Subgroup G) x ⊔
      (Fin.cons Q₂ ![F, Q 1, Q 0, Q 2] : Fin 5 → Subgroup G) x ≤ S := fun x =>
    le_iSup (fun x => (Fin.cons P₂ ![E, P 1, P 0, P 2] : Fin 5 → Subgroup G) x ⊔
      (Fin.cons Q₂ ![F, Q 1, Q 0, Q 2] : Fin 5 → Subgroup G) x) x
  have hk : ∀ k, P k ⊔ Q k ≤ S := by
    intro k
    fin_cases k
    · exact hle 3
    · exact hle 2
    · exact hle 4
  refine sup_le (sup_le ((levi_le_sup_of_card_two h hA hAne hA₀ h2 hΔ₁ hΔ₂ hne).trans
    (sup_le (hgen₁ ▸ iSup_le hk) (hgen₂ ▸ hle 0))) (le_sup_left.trans (hle 1)))
    (le_sup_right.trans (hle 1))

end CaseOA

end CFSG.Timmesfeld.ARS
