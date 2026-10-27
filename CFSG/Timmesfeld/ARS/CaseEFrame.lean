module

public import CFSG.Timmesfeld.ARS.SimplyLacedConfig
public import CFSG.Timmesfeld.Outcome
public import CFSG.Timmesfeld.ARS.Sec13Basic

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

section Edge

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

abbrev EdgeRel (R : Set (Subgroup G)) (X Y X' Y' : Subgroup G) : Prop :=
  Special R X Y ∧ Commuting X' Y ∧ ⁅X', ⁅X, Y⁆⁆ = Y ∧ Commuting X Y' ∧ ⁅⁅X, Y⁆, Y'⁆ = X ∧
    Special R X' Y'

theorem EdgeRel.symm {X Y X' Y' : Subgroup G} (h : EdgeRel R X Y X' Y') :
    EdgeRel R Y X Y' X' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨h1.symm, h4.symm, ?_, h2.symm, ?_, h6.symm⟩
  · rw [Subgroup.commutator_comm Y X, Subgroup.commutator_comm Y' ⁅X, Y⁆]
    exact h5
  · rw [Subgroup.commutator_comm Y X, ← Subgroup.commutator_comm X' ⁅X, Y⁆]
    exact h3

theorem IsConfig.extend {r r' : ℕ} {adj : Fin r → Fin r → Prop}
    {adj' : Fin r' → Fin r' → Prop} {P Q : Fin r → Subgroup G} (hX : IsConfig R adj P Q)
    {E F : Subgroup G} (hER : E ∈ R) (hFR : F ∈ R) (hEF : Opposite E F) {j : Fin r}
    (hcomm : ∀ k, k ≠ j → Commuting E (P k) ∧ Commuting E (Q k) ∧ Commuting F (P k) ∧
      Commuting F (Q k))
    (hedge : EdgeRel R E (P j) F (Q j)) (ι : Fin r → Fin r') (n₀ : Fin r')
    (hn₀ : ∀ k, ι k ≠ n₀) (hcover : ∀ x, x = n₀ ∨ ∃ k, ι k = x)
    (hadj : ∀ a b, adj' (ι a) (ι b) → adj a b ∨ adj b a)
    (hadj' : ∀ a b, adj a b → adj' (ι a) (ι b) ∨ adj' (ι b) (ι a))
    (hnew : ∀ k, adj' n₀ (ι k) ∨ adj' (ι k) n₀ → k = j) (hnewj : adj' n₀ (ι j) ∨ adj' (ι j) n₀)
    (hnn : ¬ adj' n₀ n₀) {A' B' : Fin r' → Subgroup G} (hA'ι : ∀ k, A' (ι k) = P k)
    (hB'ι : ∀ k, B' (ι k) = Q k) (hA'n : A' n₀ = E) (hB'n : B' n₀ = F) :
    IsConfig R adj' A' B' := by
  have hmemA : ∀ x, A' x ∈ R := fun x => by
    rcases hcover x with rfl | ⟨k, rfl⟩
    · rw [hA'n]; exact hER
    · rw [hA'ι]; exact hX.memA k
  have hmemB : ∀ x, B' x ∈ R := fun x => by
    rcases hcover x with rfl | ⟨k, rfl⟩
    · rw [hB'n]; exact hFR
    · rw [hB'ι]; exact hX.memB k
  refine ⟨hmemA, hmemB, fun x => ?_, fun x y hxy => ?_, fun x y hxy h1 h2 => ?_⟩
  · rcases hcover x with rfl | ⟨k, rfl⟩
    · rw [hA'n, hB'n]; exact hEF
    · rw [hA'ι, hB'ι]; exact hX.opp k
  · change EdgeRel R (A' x) (A' y) (B' x) (B' y)
    rcases hcover x with rfl | ⟨a, rfl⟩ <;> rcases hcover y with rfl | ⟨b, rfl⟩
    · exact absurd hxy hnn
    · rw [hA'n, hB'n, hA'ι, hB'ι, hnew b (Or.inl hxy)]
      exact hedge
    · rw [hA'n, hB'n, hA'ι, hB'ι, hnew a (Or.inr hxy)]
      exact hedge.symm
    · rw [hA'ι, hA'ι, hB'ι, hB'ι]
      rcases hadj a b hxy with h | h
      · exact hX.edge a b h
      · exact (show EdgeRel R (P b) (P a) (Q b) (Q a) from hX.edge b a h).symm
  · rcases hcover x with rfl | ⟨a, rfl⟩ <;> rcases hcover y with rfl | ⟨b, rfl⟩
    · exact absurd rfl hxy
    · have hb : b ≠ j := fun e => by
        subst e
        rcases hnewj with h | h
        · exact h1 h
        · exact h2 h
      obtain ⟨c1, c2, c3, c4⟩ := hcomm b hb
      rw [hA'n, hB'n, hA'ι, hB'ι]
      exact ⟨c1, c2, c3, c4⟩
    · have ha : a ≠ j := fun e => by
        subst e
        rcases hnewj with h | h
        · exact h2 h
        · exact h1 h
      obtain ⟨c1, c2, c3, c4⟩ := hcomm a ha
      rw [hA'n, hB'n, hA'ι, hB'ι]
      exact ⟨c1.symm, c3.symm, c2.symm, c4.symm⟩
    · have hab : a ≠ b := fun e => hxy (e ▸ rfl)
      have na : ¬ adj a b := fun h => by
        rcases hadj' a b h with h' | h'
        · exact h1 h'
        · exact h2 h'
      have nb : ¬ adj b a := fun h => by
        rcases hadj' b a h with h' | h'
        · exact h2 h'
        · exact h1 h'
      rw [hA'ι, hA'ι, hB'ι, hB'ι]
      exact hX.nonadj a b hab na nb

end Edge

section Gen

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

theorem Sec13.levi_sup_sup_eq_top {A A₀ : Subgroup G} (hS : Sec13 R A A₀) {E F : Subgroup G}
    (hE : E ∈ lambdaStar R A A₀) (hF : F ∈ lambdaStar R A₀ A) :
    levi R A A₀ ⊔ E ⊔ F = ⊤ := by
  have h := hS.hyp
  have hR := h.root
  have hA := hS.mem
  have hA₀ := hS.opp
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
    obtain ⟨v, hv, rfl⟩ := exists_mem_levi_conjSub_eq_of_isSigmaMaximal h hA hS.sec8.2 hS.max
      hA₀ hE hY
    exact conjSub_le (le_sup_right.trans le_sup_left) (hV hv)
  have hMA₀ : M R A₀ ≤ H := by
    rw [M_eq_gen_lambdaStar h hA₀R hAΩ]
    refine gen_le fun Y hY => ?_
    obtain ⟨v, hv, rfl⟩ := exists_mem_levi_conjSub_eq_of_isSigmaMaximal h hA₀R
      (Sec8.of_mem hR hA hA₀R hS.sec8).2 (isSigmaMaximal_centralGroup_of_mem hR hA hA₀R hS.max)
      hAΩ hF hY
    exact conjSub_le le_sup_right (hV' hv)
  rw [eq_top_iff, ← gen_lambdaSet_sup_eq_top h hA hA₀]
  exact sup_le ((gen_le fun B hB => QD.le_M hB).trans hMA) (QD.le_M_self.trans hMA₀)

end Gen

section Types

variable {G : Type} [Group G] {R : Set (Subgroup G)}

structure CaseENode (R : Set (Subgroup G)) (A A₀ : Subgroup G) {r : ℕ} (P Q : Fin r → Subgroup G)
    (E F : Subgroup G) (j : Fin r) : Prop where
  memE : E ∈ lambdaStar R A A₀
  memF : F ∈ lambdaStar R A₀ A
  opp : Opposite E F
  comm : ∀ k, k ≠ j → Commuting E (P k) ∧ Commuting E (Q k) ∧ Commuting F (P k) ∧
    Commuting F (Q k)
  edge : EdgeRel R E (P j) F (Q j)

variable {A A₀ : Subgroup G}

theorem iSup_eq_top_of_extend (hS : Sec13 R A A₀) {r r' : ℕ} {P Q : Fin r → Subgroup G}
    (hgen : ⨆ k, (P k ⊔ Q k) = levi R A A₀) {E F : Subgroup G} {j : Fin r}
    (hN : CaseENode R A A₀ P Q E F j) (ι : Fin r → Fin r') (n₀ : Fin r')
    {A' B' : Fin r' → Subgroup G} (hA'ι : ∀ k, A' (ι k) = P k) (hB'ι : ∀ k, B' (ι k) = Q k)
    (hA'n : A' n₀ = E) (hB'n : B' n₀ = F) : ⨆ x, (A' x ⊔ B' x) = ⊤ := by
  rw [eq_top_iff, ← hS.levi_sup_sup_eq_top hN.memE hN.memF, ← hgen]
  refine sup_le (sup_le (iSup_le fun k => ?_) ?_) ?_
  · rw [← hA'ι, ← hB'ι]
    exact le_iSup (fun x => A' x ⊔ B' x) (ι k)
  · rw [← hA'n]
    exact le_sup_left.trans (le_iSup (fun x => A' x ⊔ B' x) n₀)
  · rw [← hB'n]
    exact le_sup_right.trans (le_iSup (fun x => A' x ⊔ B' x) n₀)

theorem lieModel_E6_of_caseENode (hS : Sec13 R A A₀) {P Q : Fin 5 → Subgroup G}
    (hX : IsConfig R (fun i j => j.val = i.val + 1) P Q) (hgen : ⨆ k, (P k ⊔ Q k) = levi R A A₀)
    {E F : Subgroup G} (hN : CaseENode R A A₀ P Q E F 2) :
    ∃ f : ℕ, 1 ≤ f ∧ (∀ X ∈ R, Nat.card X = 2 ^ f) ∧ Blueprint.LieModel G .E6 0 2 f := by
  have := hS.hyp.finite
  set ι : Fin 5 → Fin 6 := ![0, 2, 3, 4, 5] with hιdef
  set A' : Fin 6 → Subgroup G := ![P 0, E, P 1, P 2, P 3, P 4]
  set B' : Fin 6 → Subgroup G := ![Q 0, F, Q 1, Q 2, Q 3, Q 4]
  have hA'ι : ∀ k, A' (ι k) = P k := by intro k; fin_cases k <;> rfl
  have hB'ι : ∀ k, B' (ι k) = Q k := by intro k; fin_cases k <;> rfl
  have hX' : IsConfig R (edgeE 6) A' B' :=
    hX.extend hN.memE.1.1.1 hN.memF.1.1.1 hN.opp hN.comm hN.edge ι 1 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) hA'ι hB'ι rfl rfl
  exact hX'.lieModel_E6 hS.hyp.root hS.hyp.noIsolated hS.hyp.center
    (iSup_eq_top_of_extend hS hgen hN ι 1 hA'ι hB'ι rfl rfl)

theorem lieModel_E7_of_caseENode (hS : Sec13 R A A₀) {P Q : Fin 6 → Subgroup G}
    (hX : IsConfig R (edgeD 6) P Q) (hgen : ⨆ k, (P k ⊔ Q k) = levi R A A₀)
    {E F : Subgroup G} {j : Fin 6} (hj : j = 4 ∨ j = 5) (hN : CaseENode R A A₀ P Q E F j) :
    ∃ f : ℕ, 1 ≤ f ∧ (∀ X ∈ R, Nat.card X = 2 ^ f) ∧ Blueprint.LieModel G .E7 0 2 f := by
  have := hS.hyp.finite
  rcases hj with rfl | rfl
  · set ι : Fin 6 → Fin 7 := ![6, 5, 4, 3, 2, 1] with hιdef
    set A' : Fin 7 → Subgroup G := ![E, P 5, P 4, P 3, P 2, P 1, P 0]
    set B' : Fin 7 → Subgroup G := ![F, Q 5, Q 4, Q 3, Q 2, Q 1, Q 0]
    have hA'ι : ∀ k, A' (ι k) = P k := by intro k; fin_cases k <;> rfl
    have hB'ι : ∀ k, B' (ι k) = Q k := by intro k; fin_cases k <;> rfl
    have hX' : IsConfig R (edgeE 7) A' B' :=
      hX.extend hN.memE.1.1.1 hN.memF.1.1.1 hN.opp hN.comm hN.edge ι 0 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) hA'ι hB'ι rfl rfl
    exact hX'.lieModel_E7 hS.hyp.root hS.hyp.noIsolated hS.hyp.center
      (iSup_eq_top_of_extend hS hgen hN ι 0 hA'ι hB'ι rfl rfl)
  · set ι : Fin 6 → Fin 7 := ![6, 5, 4, 3, 1, 2] with hιdef
    set A' : Fin 7 → Subgroup G := ![E, P 4, P 5, P 3, P 2, P 1, P 0]
    set B' : Fin 7 → Subgroup G := ![F, Q 4, Q 5, Q 3, Q 2, Q 1, Q 0]
    have hA'ι : ∀ k, A' (ι k) = P k := by intro k; fin_cases k <;> rfl
    have hB'ι : ∀ k, B' (ι k) = Q k := by intro k; fin_cases k <;> rfl
    have hX' : IsConfig R (edgeE 7) A' B' :=
      hX.extend hN.memE.1.1.1 hN.memF.1.1.1 hN.opp hN.comm hN.edge ι 0 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) hA'ι hB'ι rfl rfl
    exact hX'.lieModel_E7 hS.hyp.root hS.hyp.noIsolated hS.hyp.center
      (iSup_eq_top_of_extend hS hgen hN ι 0 hA'ι hB'ι rfl rfl)

theorem lieModel_E8_of_caseENode (hS : Sec13 R A A₀) {P Q : Fin 7 → Subgroup G}
    (hX : IsConfig R (edgeE 7) P Q) (hgen : ⨆ k, (P k ⊔ Q k) = levi R A A₀)
    {E F : Subgroup G} (hN : CaseENode R A A₀ P Q E F 6) :
    ∃ f : ℕ, 1 ≤ f ∧ (∀ X ∈ R, Nat.card X = 2 ^ f) ∧ Blueprint.LieModel G .E8 0 2 f := by
  have := hS.hyp.finite
  set ι : Fin 7 → Fin 8 := ![0, 1, 2, 3, 4, 5, 6] with hιdef
  set A' : Fin 8 → Subgroup G := ![P 0, P 1, P 2, P 3, P 4, P 5, P 6, E]
  set B' : Fin 8 → Subgroup G := ![Q 0, Q 1, Q 2, Q 3, Q 4, Q 5, Q 6, F]
  have hA'ι : ∀ k, A' (ι k) = P k := by intro k; fin_cases k <;> rfl
  have hB'ι : ∀ k, B' (ι k) = Q k := by intro k; fin_cases k <;> rfl
  have hX' : IsConfig R (edgeE 8) A' B' :=
    hX.extend hN.memE.1.1.1 hN.memF.1.1.1 hN.opp hN.comm hN.edge ι 7 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) hA'ι hB'ι rfl rfl
  exact hX'.lieModel_E8 hS.hyp.root hS.hyp.noIsolated hS.hyp.center
    (iSup_eq_top_of_extend hS hgen hN ι 7 hA'ι hB'ι rfl rfl)

theorem outcome_of_caseENode (hS : Sec13 R A A₀) {r : ℕ} {adj : Fin r → Fin r → Prop}
    {P Q : Fin r → Subgroup G} (hX : IsConfig R adj P Q) (hgen : ⨆ k, (P k ⊔ Q k) = levi R A A₀)
    {E F : Subgroup G} {j : Fin r} (hN : CaseENode R A A₀ P Q E F j)
    (htype : (r = 5 ∧ adj = (fun i j => j.val = i.val + 1) ∧ j.val = 2) ∨
      (r = 6 ∧ adj = edgeD r ∧ (j.val = 4 ∨ j.val = 5)) ∨
      (r = 7 ∧ adj = edgeE r ∧ j.val = 6)) :
    Outcome G := by
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
  rcases htype with ⟨rfl, rfl, hj⟩ | ⟨rfl, rfl, hj⟩ | ⟨rfl, rfl, hj⟩
  · obtain rfl : j = 2 := Fin.ext hj
    obtain ⟨f, hf, -, hL⟩ := lieModel_E6_of_caseENode hS hX hgen hN
    exact ⟨f, hf, .E6, by decide, hL⟩
  · have hj' : j = 4 ∨ j = 5 := hj.imp (fun h => Fin.ext h) (fun h => Fin.ext h)
    obtain ⟨f, hf, -, hL⟩ := lieModel_E7_of_caseENode hS hX hgen hj' hN
    exact ⟨f, hf, .E7, by decide, hL⟩
  · obtain rfl : j = 6 := Fin.ext hj
    obtain ⟨f, hf, -, hL⟩ := lieModel_E8_of_caseENode hS hX hgen hN
    exact ⟨f, hf, .E8, by decide, hL⟩

end Types

end CFSG.Timmesfeld.ARS
