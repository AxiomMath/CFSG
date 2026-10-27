module

public import CFSG.Timmesfeld.ARS.CaseOANode
public import CFSG.Timmesfeld.ARS.CaseOASurj
public import CFSG.Timmesfeld.ARS.CaseEFrameOf
public import CFSG.Timmesfeld.ARS.CaseOAWeyl

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg

variable {G : Type} [Group G] {R : Set (Subgroup G)}

namespace CaseOA

section Node

variable (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
  (hmax : IsSigmaMaximal R (centralGroup R A)) (hA₀ : A₀ ∈ omegaSet R A)
  (h2 : Nat.card (leviComps R A A₀) = 2) {Δ₁ Δ₂ : Set (Subgroup G)}
  (hΔ₁ : Δ₁ ∈ leviComps R A A₀) (hΔ₂ : Δ₂ ∈ leviComps R A A₀) (hne : Δ₁ ≠ Δ₂)
  (hS₁ : ¬ IsSL2Comp Δ₁) {P₂ Q₂ : Subgroup G} (hP₂ : P₂ ∈ Δ₂) (hQ₂ : Q₂ ∈ Δ₂)
  (hPQ₂ : Opposite P₂ Q₂) (hgen₂ : gen Δ₂ = P₂ ⊔ Q₂)
include h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hS₁ hP₂ hQ₂ hPQ₂ hgen₂

theorem exists_node_A3 {P Q : Fin 3 → Subgroup G}
    (hX : IsConfig R (edgeA 3) P Q) (hPQ : ∀ k, P k ∈ Δ₁ ∧ Q k ∈ Δ₁)
    (hgen₁ : ⨆ k, (P k ⊔ Q k) = gen Δ₁) :
    ∃ E C, Lowest R A A₀ P Q P₂ Q₂ E C ∧ ⁅E, C⁆ = A ∧
      ∃ j : Fin 3, (∀ k, ¬ Commuting E (P k) ↔ k = j) ∧
        ∃ w₀ : (coxeterMatrix (SpecialLinear.isFiniteType_A 3)).Group,
          (∀ w, (coxeterMatrix (SpecialLinear.isFiniteType_A 3)).toCoxeterSystem.length w ≤
            (coxeterMatrix (SpecialLinear.isFiniteType_A 3)).toCoxeterSystem.length w₀) ∧
          weylAction (SpecialLinear.isFiniteType_A 3) w₀ (Pi.single j 1) = -Pi.single j 1 := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hinv : ∀ X ∈ Δ₁, ∀ v ∈ gen Δ₁, conjSub X v ∈ Δ₁ := fun X hX v hv =>
    Sec9.conjSub_mem h hA hAne hA₀ hΔ₁ hX
      (Sec9.gen_le_levi (fun _ hY => Sec9.mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₁ hY) hv)
  obtain ⟨f, -, Ψ₀, hP, hQ, hsurj⟩ := hX.exists_surjective_A_le hR hiso le_rfl hgen₁
  have hct := SpecialLinear.isCTGroupDatum 3 (GaloisField 2 f)
  obtain ⟨hP', hQ', hmem, hrange, hsurj', -⟩ := frame_of_surjective
    (D := SpecialLinear.rootDatum 3 (GaloisField 2 f)) hinv hct rfl hX hPQ Ψ₀ hP hQ hsurj
  have hnd : ∃ X ∈ Δ₁, ∃ Y ∈ Δ₁, Special R X Y :=
    ⟨P 0, (hPQ _).1, P 1, (hPQ _).1, (hX.edge 0 1 (by decide)).1⟩
  obtain ⟨E, C, hLow, hEC, -, j, -, hjE, w₀, hw₀, hjw⟩ := exists_node h hA hAne hmax hA₀ h2 hΔ₁
    hΔ₂ hne hS₁ hnd hP₂ hQ₂ hPQ₂ hgen₂ hct (SpecialLinear.steinbergExtras 3 (GaloisField 2 f))
    rfl (TauCeti.posDef_map_intCast_cartanMatrix_A 3) hmem hrange hsurj' hP' hQ' hX CaseE.adj_A
    hgen₁ (CaseE.highest_mem_A (by norm_num) (GaloisField 2 f)) (fun _ => le_rfl)
  exact ⟨E, C, hLow, hEC, j, hjE, w₀, hw₀, hjw⟩

end Node

end CaseOA

@[expose] def OAEndInputA3 : Prop :=
  ∀ (G : Type) [Group G] (R : Set (Subgroup G)), Hyp G R → ∀ A ∈ R,
    sigmaSet R A ≠ lambdaSet R A → IsSigmaMaximal R (centralGroup R A) → ∀ A₀ ∈ omegaSet R A,
      Nat.card (leviComps R A A₀) = 2 → ∀ Δ₁ ∈ leviComps R A A₀, ∀ Δ₂ ∈ leviComps R A A₀,
        Δ₁ ≠ Δ₂ → ¬ IsSL2Comp Δ₁ → ∀ P₂ ∈ Δ₂, ∀ Q₂ ∈ Δ₂, Opposite P₂ Q₂ → gen Δ₂ = P₂ ⊔ Q₂ →
          ∀ (P Q : Fin 3 → Subgroup G), IsConfig R (edgeA 3) P Q →
            (∀ k, P k ∈ Δ₁ ∧ Q k ∈ Δ₁) → ⨆ k, (P k ⊔ Q k) = gen Δ₁ →
              ∀ E C, CaseOA.Lowest R A A₀ P Q P₂ Q₂ E C → ⁅E, C⁆ = A →
                ∀ j : Fin 3, j ≠ 1 → (∀ k, ¬ Commuting E (P k) ↔ k = j) →
                  ∀ w₀ : (coxeterMatrix (SpecialLinear.isFiniteType_A 3)).Group,
                    (∀ w, (coxeterMatrix (SpecialLinear.isFiniteType_A 3)).toCoxeterSystem.length
                      w ≤ (coxeterMatrix (SpecialLinear.isFiniteType_A 3)).toCoxeterSystem.length
                        w₀) →
                    weylAction (SpecialLinear.isFiniteType_A 3) w₀ (Pi.single j 1) =
                      -Pi.single j 1 → False

theorem oaInputA3'_of_end (hend : OAEndInputA3) : OAInputA3' := by
  intro G _ R h A hA hAne hmax A₀ hA₀ h2 Δ₁ hΔ₁ Δ₂ hΔ₂ hne hS₁ P₂ hP₂ Q₂ hQ₂ hPQ₂ hgen₂ P Q hX
    hPQ hgen₁
  obtain ⟨E, C, hLow, hEC, j, hjE, w₀, hw₀, hjw⟩ := CaseOA.exists_node_A3 h hA hAne hmax hA₀
    h2 hΔ₁ hΔ₂ hne hS₁ hP₂ hQ₂ hPQ₂ hgen₂ hX hPQ hgen₁
  refine ⟨E, C, hLow, hEC, ?_⟩
  by_cases hj1 : j = 1
  · subst hj1
    exact hjE
  · exact (hend G R h A hA hAne hmax A₀ hA₀ h2 Δ₁ hΔ₁ Δ₂ hΔ₂ hne hS₁ P₂ hP₂ Q₂ hQ₂ hPQ₂ hgen₂ P Q
      hX hPQ hgen₁ E C hLow hEC j hj1 hjE w₀ hw₀ hjw).elim

theorem oaEndInputA3 : OAEndInputA3 := by
  intro G _ R h A hA hAne hmax A₀ hA₀ h2 Δ₁ hΔ₁ Δ₂ hΔ₂ hne hS₁ P₂ hP₂ Q₂ hQ₂ hPQ₂ hgen₂ P Q hX
    hPQ hgen₁ E C hLow hEC j hj hjE w₀ hw₀ hjw
  exact CaseOA.weylAction_longest_ne_A3 hw₀ hj hjw

end CFSG.Timmesfeld.ARS
