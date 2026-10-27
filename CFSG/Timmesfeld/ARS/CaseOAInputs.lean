module

public import CFSG.Timmesfeld.ARS.CaseOAMain
public import CFSG.Timmesfeld.ARS.InductionMax

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open _root_.CFSG.Timmesfeld.ARS.Levi

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace CaseOA

structure Lowest (R : Set (Subgroup G)) (A A₀ : Subgroup G) {r : ℕ} (P Q : Fin r → Subgroup G)
    (P₂ Q₂ E C : Subgroup G) : Prop where
  memE : E ∈ lambdaStar R A A₀
  memC : C ∈ lambdaStar R A A₀
  commE₂ : Commuting Q₂ E
  commC₂ : Commuting P₂ C
  commE : ∀ k, Commuting (Q k) E
  commC : ∀ k, Commuting (P k) C
  lowE : ∀ k, Commuting E (P k) ∨ (E ∈ lambdaSet R (Q k) ∧ Special R E (P k))
  highC : ∀ k, Commuting C (Q k) ∨ (C ∈ lambdaSet R (P k) ∧ Special R C (Q k))

theorem Lowest.extremal {A A₀ : Subgroup G} {r : ℕ} {P Q : Fin r → Subgroup G}
    {P₂ Q₂ E C : Subgroup G} (hEC : Lowest R A A₀ P Q P₂ Q₂ E C) (hA : A ∈ R)
    (hcomm : ⁅E, C⁆ = A) : Extremal R A A₀ P Q P₂ Q₂ E C := by
  refine ⟨hEC.memE, hEC.memC, hEC.commE₂, hEC.commC₂, hEC.commE, hEC.commC, hEC.lowE, hEC.highC,
    ?_, hcomm⟩
  rw [Special, hcomm]
  exact ⟨hA, hEC.memE.1.1.2.2, hEC.memC.1.1.2.2⟩

section Node

variable (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R)
include h hA

omit hA in
theorem commutator_commutator_eq {X X' Z Z' : Subgroup G} (hX : X ∈ R) (hZ : Z ∈ R)
    (hZ' : Z' ∈ R) (hZZ' : Opposite Z Z') (hXl : X ∈ lambdaSet R Z') (hsXZ : Special R X Z)
    (hAZ : Commuting A Z) (hAZ' : Commuting A Z') (hZX' : Commuting Z X') (hZ'X' : Commuting Z' X')
    (hXX' : ⁅X, X'⁆ = A) : ⁅⁅Z, X⁆, X'⁆ = A := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hDR : ⁅Z, X⁆ ∈ R := by
    rw [Subgroup.commutator_comm]
    exact hsXZ.1
  obtain ⟨d, hd, hd1⟩ := hR.exists_ne_one hDR
  obtain ⟨x, hx, hdx⟩ := Sec3.exists_mem_conjSub_of_mem_sup hR hiso hZ' hZ hZZ'.symm hXl
    ⟨hX, hsXZ.symm⟩ (Subgroup.mem_sup_right hd) hd1
  have hDx : conjSub X x = ⁅Z, X⁆ :=
    Sec3.eq_of_mem_of_mem hR hiso (hR.conjSub_mem hX x) hDR hdx hd hd1
  have hX'x : conjSub X' x = X' :=
    conjSub_of_forall_commute fun y hy => (hZ'X'.sup_left hZX') x hx y hy
  have hAx : conjSub A x = A :=
    conjSub_of_forall_commute fun a ha => ((hAZ'.sup_right hAZ) a ha x hx).symm
  rw [← hDx, ← hX'x, ← Subgroup.map_commutator, hXX']
  exact hAx

theorem not_commuting_iff_of_commutator_eq {Y Y' E C : Subgroup G} (hY : Y ∈ leviSet R A A₀)
    (hY' : Y' ∈ leviSet R A A₀) (hYY' : Opposite Y Y') (hE : E ∈ lambdaStar R A A₀)
    (hC : C ∈ lambdaStar R A A₀) (hY'E : Commuting Y' E) (hYC : Commuting Y C)
    (hlow : Commuting E Y ∨ (E ∈ lambdaSet R Y' ∧ Special R E Y))
    (hhigh : Commuting C Y' ∨ (C ∈ lambdaSet R Y ∧ Special R C Y')) (hEC : ⁅E, C⁆ = A) :
    ¬ Commuting E Y ↔ ¬ Commuting C Y' := by
  have hR := h.root
  have hAbot : A ≠ ⊥ := hR.ne_bot A hA
  have hAY : Commuting A Y := hY.1.2.2
  have hAY' : Commuting A Y' := hY'.1.2.2
  constructor
  · intro hEY hCY'
    obtain ⟨hEl, hsEY⟩ := hlow.resolve_left hEY
    have h1 := commutator_commutator_eq h hE.1.1.1 hY.1.1 hY'.1.1 hYY' hEl hsEY hAY hAY'
      hYC hCY'.symm hEC
    have h2 : ⁅⁅Y, E⁆, C⁆ = ⊥ := by
      refine Subgroup.commutator_commutator_eq_bot_of_rotate ?_ ?_
      · rw [hEC]
        exact commuting_iff_commutator_eq_bot.1 hAY
      · rw [commuting_iff_commutator_eq_bot.1 hYC.symm, Subgroup.commutator_bot_left]
    exact hAbot (h1.symm.trans h2)
  · intro hCY' hEY
    obtain ⟨hCl, hsCY'⟩ := hhigh.resolve_left hCY'
    have hCE : ⁅C, E⁆ = A := by
      rw [Subgroup.commutator_comm]
      exact hEC
    have h1 := commutator_commutator_eq h hC.1.1.1 hY'.1.1 hY.1.1 hYY'.symm hCl hsCY' hAY'
      hAY hY'E hEY.symm hCE
    have h2 : ⁅⁅Y', C⁆, E⁆ = ⊥ := by
      refine Subgroup.commutator_commutator_eq_bot_of_rotate ?_ ?_
      · rw [hCE]
        exact commuting_iff_commutator_eq_bot.1 hAY'
      · rw [commuting_iff_commutator_eq_bot.1 hY'E.symm, Subgroup.commutator_bot_left]
    exact hAbot (h1.symm.trans h2)

theorem Lowest.not_commuting_iff {r : ℕ} {adj : Fin r → Fin r → Prop} {P Q : Fin r → Subgroup G}
    (hX : IsConfig R adj P Q) (hPQ : ∀ k, P k ∈ leviSet R A A₀ ∧ Q k ∈ leviSet R A A₀)
    {P₂ Q₂ E C : Subgroup G} (hEC : Lowest R A A₀ P Q P₂ Q₂ E C) (hcomm : ⁅E, C⁆ = A)
    (k : Fin r) : ¬ Commuting E (P k) ↔ ¬ Commuting C (Q k) :=
  not_commuting_iff_of_commutator_eq h hA (hPQ k).1 (hPQ k).2 (hX.opp k) hEC.memE hEC.memC
    (hEC.commE k) (hEC.commC k) (hEC.lowE k) (hEC.highC k) hcomm

theorem exists_not_commuting (hAne : sigmaSet R A ≠ lambdaSet R A)
    (hmax : IsSigmaMaximal R (centralGroup R A)) (hA₀ : A₀ ∈ omegaSet R A)
    {Δ₁ : Set (Subgroup G)} (hΔ₁ : Δ₁ ∈ leviComps R A A₀) (hS : ¬ IsSL2Comp Δ₁)
    (hnd : ∃ X ∈ Δ₁, ∃ Y ∈ Δ₁, Special R X Y) {r : ℕ} {P Q : Fin r → Subgroup G}
    (hgen₁ : ⨆ k, (P k ⊔ Q k) = gen Δ₁) {E : Subgroup G} (hE : E ∈ lambdaStar R A A₀)
    (hQE : ∀ k, Commuting (Q k) E) : ∃ k, ¬ Commuting E (P k) := by
  have := h.finite
  have hR := h.root
  by_contra hcon
  push Not at hcon
  have hEV : Commuting E (gen Δ₁) := by
    rw [← hgen₁, commuting_iff_le_centralizer]
    exact iSup_le fun k => sup_le (commuting_iff_le_centralizer.1 (hcon k))
      (commuting_iff_le_centralizer.1 (hQE k).symm)
  have hOC : Sec9.OrbitCollinear R A A₀ Δ₁ := by
    refine Sec9.orbitCollinear_of_not_isSL2Comp h hA hAne hmax hA₀ hΔ₁ hS fun hdeg => ?_
    obtain ⟨X, hX, Y, hY, hXY⟩ := hnd
    exact absurd hXY (hdeg X hX Y hY)
  have hEB : ∀ B ∈ lambdaStar R A A₀, Commuting E B := by
    intro B hB
    obtain ⟨Y, hYo, hYB⟩ := hOC B hB E hE
    obtain ⟨y, hy, rfl⟩ := hYo
    change conjSub E y ∈ lambdaSet R B at hYB
    have hEy : conjSub E y = E := conjSub_of_forall_commute fun e he => (hEV e he y hy).symm
    rw [hEy] at hYB
    exact hYB.1.2.2.symm
  have hEM : Commuting E (M R A) := by
    rw [M_eq_gen_lambdaStar h hA hA₀, commuting_iff_le_centralizer]
    exact gen_le fun B hB => commuting_iff_le_centralizer.1 (hEB B hB)
  have hmem : E ∈ {B | B ∈ R ∧ Commuting B (M R A)} := ⟨hE.1.1.1, hEM⟩
  rw [(Q_eq_M h hA).2.2.2.1, Set.mem_singleton_iff] at hmem
  exact hE.1.1.2.1 hmem

end Node

end CaseOA

@[expose] def OAInputD' : Prop :=
  ∀ (G : Type) [Group G] (R : Set (Subgroup G)), Hyp G R → ∀ A ∈ R,
    sigmaSet R A ≠ lambdaSet R A → IsSigmaMaximal R (centralGroup R A) → ∀ A₀ ∈ omegaSet R A,
      Nat.card (leviComps R A A₀) = 2 → ∀ Δ₁ ∈ leviComps R A A₀, ∀ Δ₂ ∈ leviComps R A A₀,
        Δ₁ ≠ Δ₂ → ¬ IsSL2Comp Δ₁ → ∀ P₂ ∈ Δ₂, ∀ Q₂ ∈ Δ₂, Opposite P₂ Q₂ → gen Δ₂ = P₂ ⊔ Q₂ →
          ∀ (m : ℕ), 4 ≤ m → ∀ (P Q : Fin m → Subgroup G), IsConfig R (edgeD m) P Q →
            (∀ k, P k ∈ Δ₁ ∧ Q k ∈ Δ₁) → ⨆ k, (P k ⊔ Q k) = gen Δ₁ →
              ∃ E C, CaseOA.Lowest R A A₀ P Q P₂ Q₂ E C ∧ ⁅E, C⁆ = A ∧
                ∃ j : Fin m, (∀ k, ¬ Commuting E (P k) ↔ k = j) ∧
                  (j.val = 0 ∨ (m = 4 ∧ (j.val = 2 ∨ j.val = 3)))

@[expose] def OAInputA3' : Prop :=
  ∀ (G : Type) [Group G] (R : Set (Subgroup G)), Hyp G R → ∀ A ∈ R,
    sigmaSet R A ≠ lambdaSet R A → IsSigmaMaximal R (centralGroup R A) → ∀ A₀ ∈ omegaSet R A,
      Nat.card (leviComps R A A₀) = 2 → ∀ Δ₁ ∈ leviComps R A A₀, ∀ Δ₂ ∈ leviComps R A A₀,
        Δ₁ ≠ Δ₂ → ¬ IsSL2Comp Δ₁ → ∀ P₂ ∈ Δ₂, ∀ Q₂ ∈ Δ₂, Opposite P₂ Q₂ → gen Δ₂ = P₂ ⊔ Q₂ →
          ∀ (P Q : Fin 3 → Subgroup G), IsConfig R (edgeA 3) P Q →
            (∀ k, P k ∈ Δ₁ ∧ Q k ∈ Δ₁) → ⨆ k, (P k ⊔ Q k) = gen Δ₁ →
              ∃ E C, CaseOA.Lowest R A A₀ P Q P₂ Q₂ E C ∧ ⁅E, C⁆ = A ∧
                ∀ k, ¬ Commuting E (P k) ↔ k = 1

theorem caseOAStep_of_inputs' (hD : OAInputD') (hA3 : OAInputA3') (hexcl : OAExclInput)
    (hns : OANonSimplyLacedInput) (hdeg : OADegenerateInput) : CaseOAStep := by
  intro G _ R h IH A hA hcoat hAne hmax A₀ hA₀ h2 Δ₁ hΔ₁ Δ₂ hΔ₂ hne hS₁ hS₂
  have hset : CaseOASetting G R A A₀ Δ₁ Δ₂ :=
    ⟨h, hA, hcoat, hAne, hmax, hA₀, h2, hΔ₁, hΔ₂, hne, hS₁, hS₂⟩
  obtain ⟨P₂, hP₂, Q₂, hQ₂, hPQ₂, hgen₂⟩ := hS₂
  by_cases hnd : ∃ X ∈ Δ₁, ∃ Y ∈ Δ₁, Special R X Y
  swap
  · push Not at hnd
    exact hdeg G R A A₀ Δ₁ Δ₂ hset hnd
  obtain ⟨E₀, hE₀, hΔ₁e⟩ := id hΔ₁
  have hout := Levi.output IH h hA hAne hA₀ hE₀ (hΔ₁e ▸ hnd)
  rw [← hΔ₁e] at hout
  have hl := fun {X : Subgroup G} (hX : X ∈ Δ₁) =>
    Sec9.mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₁ hX
  have hjC : ∀ {r : ℕ} {adj : Fin r → Fin r → Prop} {P Q : Fin r → Subgroup G} {E C : Subgroup G},
      IsConfig R adj P Q → (∀ k, P k ∈ Δ₁ ∧ Q k ∈ Δ₁) → CaseOA.Lowest R A A₀ P Q P₂ Q₂ E C →
        ⁅E, C⁆ = A → ∀ {j : Fin r}, (∀ k, ¬ Commuting E (P k) ↔ k = j) →
          ∀ k, ¬ Commuting C (Q k) ↔ k = j := by
    intro r adj P Q E C hX hPQ hEC hcomm j hjE k
    rw [← CaseOA.Lowest.not_commuting_iff h hA hX (fun k => ⟨hl (hPQ k).1, hl (hPQ k).2⟩) hEC
      hcomm k]
    exact hjE k
  have hDm : ∀ m, 4 ≤ m → HasConfigIn R Δ₁ (edgeD m) → Output G R := by
    rintro m hm ⟨P, Q, hX, hPQ, hgen₁⟩
    obtain ⟨E, C, hEC, hcomm, j, hjE, hj⟩ := hD G R h A hA hAne hmax A₀ hA₀ h2 Δ₁ hΔ₁ Δ₂ hΔ₂ hne
      hS₁ P₂ hP₂ Q₂ hQ₂ hPQ₂ hgen₂ m hm P Q hX hPQ hgen₁
    have hjC' := hjC hX hPQ hEC hcomm hjE
    have hEC' := hEC.extremal hA hcomm
    refine .inr (.inl ⟨m + 2, by omega, ?_⟩)
    rcases hj with hj0 | ⟨rfl, hj23⟩
    · have e : j = ⟨0, by omega⟩ := Fin.ext hj0
      rw [e] at hjE hjC'
      exact CaseOA.hasGenConfig_D_of_extremal h hA hAne hA₀ hmax h2 hΔ₁ hΔ₂ hne hP₂ hQ₂ hPQ₂
        hgen₂ hm hX hPQ hgen₁ hEC' hjE hjC'
    ·
      have key : ∀ (i : Fin 4), (i = 2 ∨ i = 3) → (∀ k, ¬ Commuting E (P k) ↔ k = i) →
          (∀ k, ¬ Commuting C (Q k) ↔ k = i) → HasGenConfig R (edgeD (4 + 2)) := by
        intro i hi hiE hiC
        set σ : Fin 4 ≃ Fin 4 := Equiv.swap 0 i with hσdef
        have hσi : ∀ k, σ.symm k = i ↔ k = 0 := by
          intro k
          rcases hi with rfl | rfl <;> fin_cases k <;> decide
        have hX' : IsConfig R (edgeD 4) (P ∘ σ.symm) (Q ∘ σ.symm) := by
          refine hX.reindex σ ?_ ?_ <;> rcases hi with rfl | rfl <;> decide
        refine CaseOA.hasGenConfig_D_of_extremal h hA hAne hA₀ hmax h2 hΔ₁ hΔ₂ hne hP₂ hQ₂ hPQ₂
          hgen₂ le_rfl hX' (fun k => hPQ _) ?_ (hEC'.reindex σ) (fun k => ?_) (fun k => ?_)
        · rw [← hgen₁]
          exact σ.symm.iSup_comp (g := fun k => P k ⊔ Q k)
        · change ¬ Commuting E (P (σ.symm k)) ↔ k = 0
          rw [hiE, hσi]
        · change ¬ Commuting C (Q (σ.symm k)) ↔ k = 0
          rw [hiC, hσi]
      rcases hj23 with h2' | h3'
      · exact key 2 (Or.inl rfl) (by simpa [Fin.ext_iff, h2'] using hjE)
          (by simpa [Fin.ext_iff, h2'] using hjC')
      · exact key 3 (Or.inr rfl) (by simpa [Fin.ext_iff, h3'] using hjE)
          (by simpa [Fin.ext_iff, h3'] using hjC')
  rcases hout with ⟨m, hm, hc⟩ | ⟨m, hm, hc⟩ | hc | hc | hc | hns'
  · by_cases hm3 : m = 3
    · subst hm3
      obtain ⟨P, Q, hX, hPQ, hgen₁⟩ := hc
      obtain ⟨E, C, hEC, hcomm, hjE⟩ := hA3 G R h A hA hAne hmax A₀ hA₀ h2 Δ₁ hΔ₁ Δ₂ hΔ₂ hne
        hS₁ P₂ hP₂ Q₂ hQ₂ hPQ₂ hgen₂ P Q hX hPQ hgen₁
      exact .inr (.inl ⟨5, by omega, CaseOA.hasGenConfig_A3_of_extremal h hA hAne hA₀ hmax h2
        hΔ₁ hΔ₂ hne hP₂ hQ₂ hPQ₂ hgen₂ hX hPQ hgen₁ (hEC.extremal hA hcomm) hjE
        (hjC hX hPQ hEC hcomm hjE)⟩)
    · exact hexcl G R A A₀ Δ₁ Δ₂ hset IH (Or.inl ⟨m, hm, hm3, hc⟩)
  · exact hDm m hm hc
  · exact hexcl G R A A₀ Δ₁ Δ₂ hset IH (Or.inr (Or.inl hc))
  · exact hexcl G R A A₀ Δ₁ Δ₂ hset IH (Or.inr (Or.inr (Or.inl hc)))
  · exact hexcl G R A A₀ Δ₁ Δ₂ hset IH (Or.inr (Or.inr (Or.inr hc)))
  · exact hns G R A A₀ Δ₁ Δ₂ hset IH hnd (hΔ₁e ▸ hns'.1) (hΔ₁e ▸ hns'.2)

end CFSG.Timmesfeld.ARS
