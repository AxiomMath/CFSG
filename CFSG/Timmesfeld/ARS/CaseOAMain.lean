module

public import CFSG.Timmesfeld.ARS.CaseOAFrame
public import CFSG.Timmesfeld.ARS.Sec9Orbits

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open _root_.CFSG.Timmesfeld.ARS.Levi

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

theorem IsConfig.reindex {r : ℕ} {adj adj' : Fin r → Fin r → Prop} {P Q : Fin r → Subgroup G}
    (hX : IsConfig R adj P Q) (σ : Fin r ≃ Fin r)
    (hσ : ∀ a b, adj' (σ a) (σ b) → adj a b ∨ adj b a)
    (hσ' : ∀ a b, adj a b → adj' (σ a) (σ b) ∨ adj' (σ b) (σ a)) :
    IsConfig R adj' (P ∘ σ.symm) (Q ∘ σ.symm) := by
  refine ⟨fun k => hX.memA _, fun k => hX.memB _, fun k => hX.opp _, fun x y hxy => ?_,
    fun x y hxy h1 h2 => ?_⟩
  · have e : adj' (σ (σ.symm x)) (σ (σ.symm y)) := by simpa using hxy
    change EdgeRel R (P (σ.symm x)) (P (σ.symm y)) (Q (σ.symm x)) (Q (σ.symm y))
    rcases hσ _ _ e with h | h
    · exact hX.edge _ _ h
    · exact (show EdgeRel R _ _ _ _ from hX.edge _ _ h).symm
  · have hne : σ.symm x ≠ σ.symm y := fun e => hxy (σ.symm.injective e)
    refine hX.nonadj _ _ hne (fun h => ?_) (fun h => ?_)
    · rcases hσ' _ _ h with h' | h' <;> simp only [Equiv.apply_symm_apply] at h'
      · exact h1 h'
      · exact h2 h'
    · rcases hσ' _ _ h with h' | h' <;> simp only [Equiv.apply_symm_apply] at h'
      · exact h2 h'
      · exact h1 h'

namespace CaseOA

structure Extremal (R : Set (Subgroup G)) (A A₀ : Subgroup G) {r : ℕ} (P Q : Fin r → Subgroup G)
    (P₂ Q₂ E C : Subgroup G) : Prop where
  memE : E ∈ lambdaStar R A A₀
  memC : C ∈ lambdaStar R A A₀
  commE₂ : Commuting Q₂ E
  commC₂ : Commuting P₂ C
  commE : ∀ k, Commuting (Q k) E
  commC : ∀ k, Commuting (P k) C
  lowE : ∀ k, Commuting E (P k) ∨ (E ∈ lambdaSet R (Q k) ∧ Special R E (P k))
  highC : ∀ k, Commuting C (Q k) ∨ (C ∈ lambdaSet R (P k) ∧ Special R C (Q k))
  special : Special R E C
  commutator : ⁅E, C⁆ = A

variable (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
  (hA₀ : A₀ ∈ omegaSet R A)
include h hA hAne hA₀

omit hAne in
theorem mem_lambdaSet_commutator_of_mem_lambdaSet {Y C : Subgroup G} (hY : Y ∈ leviSet R A A₀)
    (hC : C ∈ lambdaStar R A A₀) (hCY : C ∈ lambdaSet R Y) : ⁅A₀, C⁆ ∈ lambdaSet R Y := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hYR : Y ∈ R := hY.1.1
  have hCR : C ∈ R := hC.1.1.1
  obtain ⟨hFst, -, -, -⟩ := CaseD4.commutator_props h hA hA₀ hC
  have hsC : Special R C A₀ := hC.2.2.symm
  obtain ⟨a, ha, ha1⟩ := hR.exists_ne_one hA₀.1
  have hCa : conjSub C a ∈ lambdaSet R Y := by
    have := conjSub_mem_lambdaSet hR hCY a
    rwa [conjSub_of_forall_commute fun y hy => hY.2.2.2 a ha y hy] at this
  have hle : ⁅A₀, C⁆ ≤ M R Y := by
    have h1 : ⁅A₀, C⁆ ≤ C ⊔ conjSub C a := by
      rw [sup_conjSub_eq_sup_commutator hR hiso hCR hA₀.1 hsC ha ha1, Subgroup.commutator_comm]
      exact le_sup_right
    exact h1.trans (sup_le (QD.le_M hCY) (QD.le_M hCa))
  have hmem : ⁅A₀, C⁆ ∈ {X | X ∈ R ∧ X ≤ M R Y} := ⟨hFst.1.1.1, hle⟩
  rw [(Q_eq_M h hYR).2.1] at hmem
  refine hmem.resolve_left fun e => ?_
  have hYl : Y ∈ leviSet R A₀ A := ⟨hY.2, hY.1⟩
  exact Sec9.ne_of_mem_leviSet h hA₀.1 ⟨hA, hA₀.2.symm⟩ hFst hYl e.symm

omit hAne in
theorem special_commutator_of_special {Y C : Subgroup G} (hY : Y ∈ leviSet R A A₀)
    (hC : C ∈ lambdaStar R A A₀) (hCY : Special R C Y) : Special R Y ⁅A₀, C⁆ := by
  have := h.finite
  have hR := h.root
  obtain ⟨hFst, -, hAFC, -⟩ := CaseD4.commutator_props h hA hA₀ hC
  have hnc : ¬ Commuting Y ⁅A₀, C⁆ := by
    intro hc
    have h1 : Commuting ⁅A, ⁅A₀, C⁆⁆ Y :=
      commuting_commutator_of_commuting hY.1.2.2 hc.symm
    rw [hAFC] at h1
    exact hCY.not_commuting hR h1
  have hYl : Y ∈ leviSet R A₀ A := ⟨hY.2, hY.1⟩
  have hne : Y ≠ ⁅A₀, C⁆ := fun e => hnc (by rw [← e]; exact hR.commuting_self hY.1.1)
  rcases hR.rel _ hY.1.1 _ hFst.1.1.1 hne with hc | ho | hs
  · exact absurd hc hnc
  · exact absurd ho (CaseD4.not_opposite_of_mem_leviSet hR hA₀.1 hFst hYl)
  · exact hs

omit hAne in
theorem opposite_of_extremal {E C : Subgroup G} (hE : E ∈ lambdaStar R A A₀)
    (hC : C ∈ lambdaStar R A A₀) (hEC : Special R E C) (hECA : ⁅E, C⁆ = A) :
    Opposite E ⁅A₀, C⁆ := by
  have := h.finite
  obtain ⟨hFst, hFC, hAFC, -⟩ := CaseD4.commutator_props h hA hA₀ hC
  exact CaseD4.opposite_of_extremal h.root h.noIsolated hA hC.1.1.1 hE.1.1.1 hFst.1.1.1
    hC.1.1.2.2 hE.1.1.2.2.symm hEC hECA hFC hFst.2.2 hAFC

theorem edgeRel_of_extremal {Y Y' E C : Subgroup G} (hY : Y ∈ leviSet R A A₀)
    (hY' : Y' ∈ leviSet R A A₀) (hYY' : Opposite Y Y') (hE : E ∈ lambdaStar R A A₀)
    (hC : C ∈ lambdaStar R A A₀) (hEY' : E ∈ lambdaSet R Y') (hsEY : Special R E Y)
    (hCY : C ∈ lambdaSet R Y) (hsCY' : Special R C Y') (hEC : Special R E C)
    (hECA : ⁅E, C⁆ = A) : EdgeRel R Y E Y' ⁅A₀, C⁆ := by
  obtain ⟨hFst, -, -, -⟩ := CaseD4.commutator_props h hA hA₀ hC
  exact edgeRel_of_natural h hA hAne hA₀ hY hY' hYY' hE hEY' hsEY.symm hFst
    (mem_lambdaSet_commutator_of_mem_lambdaSet h hA hA₀ hY hC hCY)
    (special_commutator_of_special h hA hA₀ hY' hC hsCY')
    (opposite_of_extremal h hA hA₀ hE hC hEC hECA)

omit h hA hAne hA₀ in
theorem Extremal.reindex {r : ℕ} {P Q : Fin r → Subgroup G} {P₂ Q₂ E C : Subgroup G}
    (hEC : Extremal R A A₀ P Q P₂ Q₂ E C) (σ : Fin r ≃ Fin r) :
    Extremal R A A₀ (P ∘ σ.symm) (Q ∘ σ.symm) P₂ Q₂ E C :=
  ⟨hEC.memE, hEC.memC, hEC.commE₂, hEC.commC₂, fun _ => hEC.commE _, fun _ => hEC.commC _,
    fun _ => hEC.lowE _, fun _ => hEC.highC _, hEC.special, hEC.commutator⟩

theorem node_of_extremal {r : ℕ} {adj : Fin r → Fin r → Prop} {P Q : Fin r → Subgroup G}
    (hX : IsConfig R adj P Q)
    (hPQ : ∀ k, P k ∈ leviSet R A A₀ ∧ Q k ∈ leviSet R A A₀) {P₂ Q₂ E C : Subgroup G}
    (hEC : Extremal R A A₀ P Q P₂ Q₂ E C) {j : Fin r}
    (hjE : ∀ k, ¬ Commuting E (P k) ↔ k = j) (hjC : ∀ k, ¬ Commuting C (Q k) ↔ k = j) :
    (∀ k, k ≠ j → Commuting E (P k) ∧ Commuting E (Q k) ∧ Commuting ⁅A₀, C⁆ (P k) ∧
      Commuting ⁅A₀, C⁆ (Q k)) ∧ EdgeRel R (P j) E (Q j) ⁅A₀, C⁆ := by
  obtain ⟨-, -, -, hFY⟩ := CaseD4.commutator_props h hA hA₀ hEC.memC
  refine ⟨fun k hk => ⟨?_, (hEC.commE k).symm, (hFY _ (hPQ k).1 (hEC.commC k)).symm,
    (hFY _ (hPQ k).2 ?_).symm⟩, ?_⟩
  · by_contra hc
    exact hk ((hjE k).1 hc)
  · by_contra hc
    exact hk ((hjC k).1 fun h' => hc h'.symm)
  · obtain ⟨hEQ, hsEP⟩ := (hEC.lowE j).resolve_left ((hjE j).2 rfl)
    obtain ⟨hCP, hsCQ⟩ := (hEC.highC j).resolve_left ((hjC j).2 rfl)
    exact edgeRel_of_extremal h hA hAne hA₀ (hPQ j).1 (hPQ j).2 (hX.opp j) hEC.memE hEC.memC
      hEQ hsEP hCP hsCQ hEC.special hEC.commutator

theorem hasGenConfig_D_of_extremal (hmax : IsSigmaMaximal R (centralGroup R A))
    (h2 : Nat.card (leviComps R A A₀) = 2) {Δ₁ Δ₂ : Set (Subgroup G)}
    (hΔ₁ : Δ₁ ∈ leviComps R A A₀) (hΔ₂ : Δ₂ ∈ leviComps R A A₀) (hne : Δ₁ ≠ Δ₂)
    {P₂ Q₂ : Subgroup G} (hP₂ : P₂ ∈ Δ₂) (hQ₂ : Q₂ ∈ Δ₂) (hPQ₂ : Opposite P₂ Q₂)
    (hgen₂ : gen Δ₂ = P₂ ⊔ Q₂) {m : ℕ} (hm : 4 ≤ m) {P Q : Fin m → Subgroup G}
    (hX : IsConfig R (edgeD m) P Q) (hPQ : ∀ k, P k ∈ Δ₁ ∧ Q k ∈ Δ₁)
    (hgen₁ : ⨆ k, (P k ⊔ Q k) = gen Δ₁) {E C : Subgroup G}
    (hEC : Extremal R A A₀ P Q P₂ Q₂ E C)
    (hjE : ∀ k, ¬ Commuting E (P k) ↔ k = ⟨0, by omega⟩)
    (hjC : ∀ k, ¬ Commuting C (Q k) ↔ k = ⟨0, by omega⟩) : HasGenConfig R (edgeD (m + 2)) := by
  have hl := fun {X : Subgroup G} (hX : X ∈ Δ₁) =>
    Sec9.mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₁ hX
  obtain ⟨hcomm, hedge⟩ := node_of_extremal h hA hAne hA₀ hX (fun k => ⟨hl (hPQ k).1,
    hl (hPQ k).2⟩) hEC hjE hjC
  obtain ⟨hFst, -, -, hFY⟩ := CaseD4.commutator_props h hA hA₀ hEC.memC
  exact hasGenConfig_D h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hP₂ hQ₂ hPQ₂ hgen₂ hEC.memE hFst
    (opposite_of_extremal h hA hA₀ hEC.memE hEC.memC hEC.special hEC.commutator) hEC.commE₂
    (hFY P₂ (Sec9.mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₂ hP₂) hEC.commC₂) hm hX hPQ
    hgen₁ hcomm hedge

theorem hasGenConfig_A3_of_extremal (hmax : IsSigmaMaximal R (centralGroup R A))
    (h2 : Nat.card (leviComps R A A₀) = 2) {Δ₁ Δ₂ : Set (Subgroup G)}
    (hΔ₁ : Δ₁ ∈ leviComps R A A₀) (hΔ₂ : Δ₂ ∈ leviComps R A A₀) (hne : Δ₁ ≠ Δ₂)
    {P₂ Q₂ : Subgroup G} (hP₂ : P₂ ∈ Δ₂) (hQ₂ : Q₂ ∈ Δ₂) (hPQ₂ : Opposite P₂ Q₂)
    (hgen₂ : gen Δ₂ = P₂ ⊔ Q₂) {P Q : Fin 3 → Subgroup G}
    (hX : IsConfig R (edgeA 3) P Q) (hPQ : ∀ k, P k ∈ Δ₁ ∧ Q k ∈ Δ₁)
    (hgen₁ : ⨆ k, (P k ⊔ Q k) = gen Δ₁) {E C : Subgroup G}
    (hEC : Extremal R A A₀ P Q P₂ Q₂ E C) (hjE : ∀ k, ¬ Commuting E (P k) ↔ k = 1)
    (hjC : ∀ k, ¬ Commuting C (Q k) ↔ k = 1) : HasGenConfig R (edgeD 5) := by
  have hl := fun {X : Subgroup G} (hX : X ∈ Δ₁) =>
    Sec9.mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₁ hX
  obtain ⟨hcomm, hedge⟩ := node_of_extremal h hA hAne hA₀ hX (fun k => ⟨hl (hPQ k).1,
    hl (hPQ k).2⟩) hEC hjE hjC
  obtain ⟨hFst, -, -, hFY⟩ := CaseD4.commutator_props h hA hA₀ hEC.memC
  exact hasGenConfig_A3 h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hP₂ hQ₂ hPQ₂ hgen₂ hEC.memE hFst
    (opposite_of_extremal h hA hA₀ hEC.memE hEC.memC hEC.special hEC.commutator) hEC.commE₂
    (hFY P₂ (Sec9.mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₂ hP₂) hEC.commC₂) hX hPQ
    hgen₁ hcomm hedge

end CaseOA

abbrev CaseOASetting (G : Type) [Group G] (R : Set (Subgroup G)) (A A₀ : Subgroup G)
    (Δ₁ Δ₂ : Set (Subgroup G)) : Prop :=
  Hyp G R ∧ A ∈ R ∧ IsCoatom (Subgroup.normalizer (A : Set G)) ∧
    sigmaSet R A ≠ lambdaSet R A ∧ IsSigmaMaximal R (centralGroup R A) ∧ A₀ ∈ omegaSet R A ∧
    Nat.card (leviComps R A A₀) = 2 ∧ Δ₁ ∈ leviComps R A A₀ ∧ Δ₂ ∈ leviComps R A A₀ ∧
    Δ₁ ≠ Δ₂ ∧ ¬ IsSL2Comp Δ₁ ∧ IsSL2Comp Δ₂

@[expose] def OAExclInput : Prop :=
  ∀ (G : Type) [Group G] (R : Set (Subgroup G)) (A A₀ : Subgroup G) (Δ₁ Δ₂ : Set (Subgroup G)),
    CaseOASetting G R A A₀ Δ₁ Δ₂ → IndHyp G →
      ((∃ m, 2 ≤ m ∧ m ≠ 3 ∧ HasConfigIn R Δ₁ (edgeA m)) ∨ HasConfigIn R Δ₁ (edgeE 6) ∨
        HasConfigIn R Δ₁ (edgeE 7) ∨ HasConfigIn R Δ₁ (edgeE 8)) → Output G R

@[expose] def OANonSimplyLacedInput : Prop :=
  ∀ (G : Type) [Group G] (R : Set (Subgroup G)) (A A₀ : Subgroup G) (Δ₁ Δ₂ : Set (Subgroup G)),
    CaseOASetting G R A A₀ Δ₁ Δ₂ → IndHyp G → (∃ X ∈ Δ₁, ∃ Y ∈ Δ₁, Special R X Y) →
      NonSimplyLacedOutcome (↥(gen Δ₁) ⧸ Subgroup.center ↥(gen Δ₁)) →
        NSLData (↥(gen Δ₁) ⧸ Subgroup.center ↥(gen Δ₁)) (quotClass (gen Δ₁) Δ₁) → Output G R

@[expose] def OADegenerateInput : Prop :=
  ∀ (G : Type) [Group G] (R : Set (Subgroup G)) (A A₀ : Subgroup G) (Δ₁ Δ₂ : Set (Subgroup G)),
    CaseOASetting G R A A₀ Δ₁ Δ₂ → (∀ X ∈ Δ₁, ∀ Y ∈ Δ₁, ¬ Special R X Y) → Output G R

end CFSG.Timmesfeld.ARS
