module

public import CFSG.Timmesfeld.ARS.CaseD4Frame
public import CFSG.Timmesfeld.ARS.LinearChain
public import CFSG.Timmesfeld.RankTwo.LevisSpin
public import CFSG.Timmesfeld.RankTwo.LeviData
public import CFSG.Timmesfeld.Outcome

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.Timmesfeld.RankOne CFSG.LieType CFSG.LieType.Universal Matrix

namespace CaseD4

theorem commute_of_mem {G : Type*} [Group G] {R : Set (Subgroup G)} {A A₀ : Subgroup G}
    {P Q : Fin 3 → Subgroup G} (hPQ : LeviSL2Cube R A A₀ P Q) {i j : Fin 3} (hij : i ≠ j)
    {x y : G} (hx : x ∈ P i ⊔ Q i) (hy : y ∈ P j ⊔ Q j) : Commute x y :=
  hPQ.commuting i j hij x hx y hy

end CaseD4

open CaseD4 in
theorem lieModel_caseD4 {G : Type} [Group G] {R : Set (Subgroup G)} (h : Hyp G R)
    {A A₀ : Subgroup G} (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
    (hmax : IsSigmaMaximal R (centralGroup R A)) (hA₀ : A₀ ∈ omegaSet R A)
    {P Q : Fin 3 → Subgroup G} (hPQ : LeviSL2Cube R A A₀ P Q) :
    ∃ f : ℕ, 1 ≤ f ∧ (∀ E ∈ R, Nat.card E = 2 ^ f) ∧
      Blueprint.LieModel G .POmegaPlus 4 2 f := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hPR : ∀ i, P i ∈ R := fun i => (hPQ.mem_left i).1.1
  have hQR : ∀ i, Q i ∈ R := fun i => (hPQ.mem_right i).1.1
  have hpair : ∀ (X : Fin 3 → Subgroup G), (∀ i, X i ∈ R) → (∀ i, X i ≤ P i ⊔ Q i) →
      ∀ i j, Commuting (X i) (X j) := by
    intro X hX hXle i j
    by_cases hij : i = j
    · subst hij
      exact hR.commuting_self (hX i)
    · exact hPQ.commuting_of_le hij (hXle i) (hXle j)
  obtain ⟨E, hE, hEQ⟩ := exists_mem_lambdaStar_forall_commuting h hA hAne hA₀ hPQ.mem_right
    (hpair Q hQR fun _ => le_sup_right) (lambdaStar_nonempty h hA hA₀) Finset.univ
  obtain ⟨C, hC, hCP⟩ := exists_mem_lambdaStar_forall_commuting h hA hAne hA₀ hPQ.mem_left
    (hpair P hPR fun _ => le_sup_left) (lambdaStar_nonempty h hA hA₀) Finset.univ
  replace hEQ : ∀ i, Commuting (Q i) E := fun i => hEQ i (Finset.mem_univ i)
  replace hCP : ∀ i, Commuting (P i) C := fun i => hCP i (Finset.mem_univ i)
  obtain ⟨hsEC, hECA⟩ := commutator_eq_of_extremal h hA hAne hmax hA₀ hPQ hE hEQ hC hCP
  obtain ⟨hF, hFC, hAFC, hFlevi⟩ := commutator_props h hA hA₀ hC
  set F := ⁅A₀, C⁆ with hFdef
  have hFP : ∀ i, Commuting (P i) F := fun i => hFlevi _ (hPQ.mem_left i) (hCP i)
  have hER : E ∈ R := hE.1.1.1
  have hFR : F ∈ R := hF.1.1.1
  have hEF : Opposite E F := opposite_of_extremal hR hiso hA hC.1.1.1 hER hFR hC.1.1.2.2
    hE.1.1.2.2.symm hsEC hECA hFC hF.2.2 hAFC
  have hcfg := config h hA hAne hmax hA₀ hPQ hE hEQ hF hFP hEF
  obtain ⟨n, hn, hqE, φ₀, hφ₀, hφ₀'⟩ := hEF.exists_mulEquiv_SL2' hR hER
  obtain ⟨hinj₀, hup₀, hlow₀⟩ := Linear.injective_of_mulEquiv φ₀ hφ₀ hφ₀'
  set ρ₀ := (E ⊔ F).subtype.comp φ₀.symm.toMonoidHom with hρ₀
  set K := GaloisField 2 n with hK
  have hcard : ∀ X ∈ R, Nat.card X = 2 ^ n := fun X hX => (hR.card_eq hX hER).trans hqE
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hcfg 0
  obtain ⟨ψ₀, ρ₁, ⟨hinj₁, hup₁, hlow₁⟩, hψ₀⟩ := Linear.exists_sl3_left hR hiso (hPR 0) hER
    (hQR 0) hFR c1 (hPQ.opposite 0) hEF c2 c3 c4 c5 c6 (hcard _ (hPR 0)) hinj₀ hup₀ hlow₀
  have hright : ∀ i : Fin 3, ∃ (ψ : SpecialLinearGroup (Fin 3) K →* G)
      (ρ : SpecialLinearGroup (Fin 2) K →* G),
      (Function.Injective ρ ∧ (upperUnipotent K).map ρ = P i ∧
        (lowerUnipotent K).map ρ = Q i) ∧
      ∀ c, ψ (tv 0 1 c) = ρ₀ (tv 0 1 c) ∧ ψ (tv 1 0 c) = ρ₀ (tv 1 0 c) ∧
        ψ (tv 1 2 c) = ρ (tv 0 1 c) ∧ ψ (tv 2 1 c) = ρ (tv 1 0 c) := by
    intro i
    obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hcfg i
    refine Linear.exists_sl3_right hR hiso hER (hPR i) hFR (hQR i) d1.symm hEF (hPQ.opposite i)
      d4.symm ?_ d2.symm ?_ d6.symm hqE hinj₀ hup₀ hlow₀
    · rw [Subgroup.commutator_comm E, Subgroup.commutator_comm F]
      exact d5
    · rw [Subgroup.commutator_comm E, Subgroup.commutator_comm _ (Q i)]
      exact d3
  obtain ⟨ψ₂, ρ₂, ⟨-, hup₂, hlow₂⟩, hψ₂⟩ := hright 1
  obtain ⟨ψ₃, ρ₃, ⟨-, hup₃, hlow₃⟩, hψ₃⟩ := hright 2
  let ρ : Fin 4 → SpecialLinearGroup (Fin 2) K →* G := ![ρ₁, ρ₀, ρ₂, ρ₃]
  let X : Fin 4 → Subgroup G := ![P 0, E, P 1, P 2]
  let Y : Fin 4 → Subgroup G := ![Q 0, F, Q 1, Q 2]
  have hρX : ∀ k, (upperUnipotent K).map (ρ k) = X k := by
    intro k
    fin_cases k
    exacts [hup₁, hup₀, hup₂, hup₃]
  have hρY : ∀ k, (lowerUnipotent K).map (ρ k) = Y k := by
    intro k
    fin_cases k
    exacts [hlow₁, hlow₀, hlow₂, hlow₃]
  have hu : ∀ k c, ρ k (tv 0 1 c) ∈ X k ⊔ Y k := fun k c => by
    rw [← hρX k]
    exact Subgroup.mem_sup_left (Subgroup.mem_map_of_mem _ (Linear.tv_mem_upperUnipotent K c))
  have hv : ∀ k c, ρ k (tv 1 0 c) ∈ X k ⊔ Y k := fun k c => by
    rw [← hρY k]
    exact Subgroup.mem_sup_right (Subgroup.mem_map_of_mem _ (Linear.tv_mem_lowerUnipotent K c))
  have hleaf : ∀ (k l : Fin 4) (a b : Fin 3), X k ⊔ Y k = P a ⊔ Q a → X l ⊔ Y l = P b ⊔ Q b →
      a ≠ b → ∀ c d, Commute (ρ k (tv 0 1 c)) (ρ l (tv 0 1 d)) ∧
        Commute (ρ k (tv 0 1 c)) (ρ l (tv 1 0 d)) ∧ Commute (ρ k (tv 1 0 c)) (ρ l (tv 0 1 d)) ∧
        Commute (ρ k (tv 1 0 c)) (ρ l (tv 1 0 d)) := by
    intro k l a b hk hl hab c d
    exact ⟨commute_of_mem hPQ hab (hk ▸ hu k c) (hl ▸ hu l d),
      commute_of_mem hPQ hab (hk ▸ hu k c) (hl ▸ hv l d),
      commute_of_mem hPQ hab (hk ▸ hv k c) (hl ▸ hu l d),
      commute_of_mem hPQ hab (hk ▸ hv k c) (hl ▸ hv l d)⟩
  have hcom4 : ∀ i j : Fin 4, i ≠ j → ¬ edgeD 4 i j → ¬ edgeD 4 j i → ∀ c d,
      Commute (ρ i (tv 0 1 c)) (ρ j (tv 0 1 d)) ∧ Commute (ρ i (tv 0 1 c)) (ρ j (tv 1 0 d)) ∧
        Commute (ρ i (tv 1 0 c)) (ρ j (tv 0 1 d)) ∧ Commute (ρ i (tv 1 0 c)) (ρ j (tv 1 0 d)) := by
    intro i j hij h1 h2 c d
    fin_cases i <;> fin_cases j <;> simp [edgeD] at hij h1 h2
    · exact hleaf 0 2 0 1 rfl rfl (by decide) c d
    · exact hleaf 0 3 0 2 rfl rfl (by decide) c d
    · exact hleaf 2 0 1 0 rfl rfl (by decide) c d
    · exact hleaf 2 3 1 2 rfl rfl (by decide) c d
    · exact hleaf 3 0 2 0 rfl rfl (by decide) c d
    · exact hleaf 3 2 2 1 rfl rfl (by decide) c d
  have hfr : SimplyLacedFrame (Spin.plusDatum 4 K (by norm_num)) K (edgeD 4)
      (fun k c => ρ k (tv 0 1 c)) (fun k c => ρ k (tv 1 0 c)) := by
    refine ⟨fun i j hij => ?_, fun k => ⟨ρ k, fun c => ⟨rfl, rfl⟩⟩,
      fun i j hij h1 h2 c d => ?_⟩
    · change Fin 4 at i j
      fin_cases i <;> fin_cases j <;> simp [edgeD] at hij
      · exact ⟨ψ₀, hψ₀⟩
      · exact ⟨ψ₂, hψ₂⟩
      · exact ⟨ψ₃, hψ₃⟩
    · exact hcom4 i j hij h1 h2 c d
  have hgen : Subgroup.closure (⋃ k, Set.range (fun c => ρ k (tv 0 1 c)) ∪
      Set.range (fun c => ρ k (tv 1 0 c))) = ⊤ := by
    rw [Subgroup.closure_iUnion]
    simp_rw [Subgroup.closure_union, Linear.range_tv_upper, Linear.range_tv_lower,
      Subgroup.closure_eq, hρX, hρY]
    rw [eq_top_iff, ← iSup_sup_sup_eq_top h hA hAne hmax hA₀ hPQ hE hF]
    refine sup_le (sup_le (iSup_le fun i => ?_) ?_) ?_
    · fin_cases i
      · exact le_iSup (fun k => X k ⊔ Y k) 0
      · exact le_iSup (fun k => X k ⊔ Y k) 2
      · exact le_iSup (fun k => X k ⊔ Y k) 3
    · exact le_sup_left.trans (le_iSup (fun k => X k ⊔ Y k) 1)
    · exact le_sup_right.trans (le_iSup (fun k => X k ⊔ Y k) 1)
  have hnt : ∃ k c, ρ k (tv 0 1 c) ≠ 1 := by
    obtain ⟨e, he, he1⟩ := hR.exists_ne_one hER
    have he' : e ∈ ((upperUnipotent K).map (ρ 1) : Set G) := by rw [hρX 1]; exact he
    rw [← Linear.range_tv_upper] at he'
    obtain ⟨c, rfl⟩ := he'
    exact ⟨1, c, he1⟩
  have hK4 : Nat.card K = 2 ^ n := GaloisField.card 2 n (by omega)
  refine ⟨n, hn, hcard, ?_⟩
  exact lieModel_of_simplyLacedFrame
    (CurtisTits.curtisTitsConclusion_spinPlus ⟨Nat.prime_two, hn, le_rfl⟩ hK4 (by norm_num))
    (leviConePresented_spinPlus K (by norm_num)) (simplyLacedLevis_spinPlus_four K) h.center hfr
    hgen hnt

theorem outcome_caseD4 {G : Type} [Group G] {R : Set (Subgroup G)} (h : Hyp G R)
    {A A₀ : Subgroup G} (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
    (hmax : IsSigmaMaximal R (centralGroup R A)) (hA₀ : A₀ ∈ omegaSet R A)
    {P Q : Fin 3 → Subgroup G} (hPQ : LeviSL2Cube R A A₀ P Q) :
    ∃ n f : ℕ, 4 ≤ n ∧ 1 ≤ f ∧
      (Blueprint.LieModel G .POmegaPlus n 2 f ∨ Blueprint.LieModel G .POmegaMinus n 2 f) := by
  obtain ⟨f, hf, -, hL⟩ := lieModel_caseD4 h hA hAne hmax hA₀ hPQ
  exact ⟨4, f, le_rfl, hf, Or.inl hL⟩

theorem outcome_of_leviSL2Cube {G : Type} [Group G] {R : Set (Subgroup G)} (h : Hyp G R)
    {A A₀ : Subgroup G} (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
    (hmax : IsSigmaMaximal R (centralGroup R A)) (hA₀ : A₀ ∈ omegaSet R A)
    {P Q : Fin 3 → Subgroup G} (hPQ : LeviSL2Cube R A A₀ P Q) : Outcome G :=
  .inr (.inr (.inl (outcome_caseD4 h hA hAne hmax hA₀ hPQ)))

end CFSG.Timmesfeld.ARS
