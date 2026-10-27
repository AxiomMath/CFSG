module

public import CFSG.Timmesfeld.ARS.CaseOACells
public import CFSG.Timmesfeld.ARS.CaseOAStarRoots
public import CFSG.Timmesfeld.ARS.CaseOASurjE
public import CFSG.Timmesfeld.ARS.CaseOAAttach

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.Blueprint.Chevalley

variable {G : Type} [Group G] {R : Set (Subgroup G)}

namespace CaseOA

theorem special_of_isConfig_E {Δ₁ : Set (Subgroup G)} {r : ℕ} (hr : 3 ≤ r)
    {P Q : Fin r → Subgroup G} (hX : IsConfig R (edgeE r) P Q) (hPQ : ∀ k, P k ∈ Δ₁ ∧ Q k ∈ Δ₁) :
    ∃ X ∈ Δ₁, ∃ Y ∈ Δ₁, Special R X Y := by
  refine ⟨P ⟨0, by omega⟩, (hPQ _).1, P ⟨2, by omega⟩, (hPQ _).1, ?_⟩
  have hedge : edgeE r ⟨0, by omega⟩ ⟨2, by omega⟩ := Or.inl ⟨rfl, rfl⟩
  exact (hX.edge _ _ hedge).1

section Node

variable (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
  (hmax : IsSigmaMaximal R (centralGroup R A)) (hA₀ : A₀ ∈ omegaSet R A)
  (h2 : Nat.card (leviComps R A A₀) = 2) {Δ₁ Δ₂ : Set (Subgroup G)}
  (hΔ₁ : Δ₁ ∈ leviComps R A A₀) (hΔ₂ : Δ₂ ∈ leviComps R A A₀) (hne : Δ₁ ≠ Δ₂)
  (hS₁ : ¬ IsSL2Comp Δ₁) {P₂ Q₂ : Subgroup G} (hP₂ : P₂ ∈ Δ₂) (hQ₂ : Q₂ ∈ Δ₂)
  (hPQ₂ : Opposite P₂ Q₂) (hgen₂ : gen Δ₂ = P₂ ⊔ Q₂)
include h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hS₁ hP₂ hQ₂ hPQ₂ hgen₂

theorem exists_node_star_of_surjective {K : Type*} [Group K] {D : UniversalRootDatum K}
    {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hdiv : D.divisible = ∅)
    (hpd : (D.cartan.map (Int.cast : ℤ → ℚ)).PosDef) {adj : Fin D.rank → Fin D.rank → Prop}
    (hadj : ∀ a b, D.cartan a b = -1 → adj a b ∨ adj b a) {θ : Fin D.rank → ℤ}
    (hθ : θ ∈ D.roots) (hθ1 : ∀ i, 1 ≤ θ i) {P Q : Fin D.rank → Subgroup G}
    (hX : IsConfig R adj P Q) (hPQ : ∀ k, P k ∈ Δ₁ ∧ Q k ∈ Δ₁)
    (hgen₁ : ⨆ k, (P k ⊔ Q k) = gen Δ₁) (hnd : ∃ X ∈ Δ₁, ∃ Y ∈ Δ₁, Special R X Y)
    (Ψ₀ : K →* ↥(gen Δ₁))
    (hP : ∀ k, (D.rootGroup (Pi.single k 1)).map Ψ₀ = (P k).subgroupOf (gen Δ₁))
    (hQ : ∀ k, (D.rootGroup (-Pi.single k 1)).map Ψ₀ = (Q k).subgroupOf (gen Δ₁))
    (hsurj : Function.Surjective Ψ₀) :
    ∃ E C, Lowest R A A₀ P Q P₂ Q₂ E C ∧ ⁅E, C⁆ = A ∧
      ∃ j, θ j = 1 ∧ (∀ k, ¬ Commuting E (P k) ↔ k = j) ∧
        ¬ StarOneAt D.cartan D.isFiniteType j ∧
        ∃ w₀ : (coxeterMatrix D.isFiniteType).Group,
          (∀ w, (coxeterMatrix D.isFiniteType).toCoxeterSystem.length w ≤
            (coxeterMatrix D.isFiniteType).toCoxeterSystem.length w₀) ∧
          weylAction D.isFiniteType w₀ (Pi.single j 1) = -Pi.single j 1 := by
  have hinv : ∀ X ∈ Δ₁, ∀ v ∈ gen Δ₁, conjSub X v ∈ Δ₁ := fun X hX v hv =>
    Sec9.conjSub_mem h hA hAne hA₀ hΔ₁ hX
      (Sec9.gen_le_levi (fun _ hY => Sec9.mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₁ hY) hv)
  obtain ⟨hP', hQ', hmem, hrange, hsurj', -⟩ :=
    frame_of_surjective hinv hct hdiv hX hPQ Ψ₀ hP hQ hsurj
  exact exists_node_star h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hS₁ hnd hP₂ hQ₂ hPQ₂ hgen₂ hct hext
    hdiv hpd hmem hrange hsurj' hP' hQ' hX hadj hgen₁ hθ hθ1

theorem exists_node_star_D {m : ℕ} (hm : 4 ≤ m) {P Q : Fin m → Subgroup G}
    (hX : IsConfig R (edgeD m) P Q) (hPQ : ∀ k, P k ∈ Δ₁ ∧ Q k ∈ Δ₁)
    (hgen₁ : ⨆ k, (P k ⊔ Q k) = gen Δ₁) :
    ∃ E C, Lowest R A A₀ P Q P₂ Q₂ E C ∧ ⁅E, C⁆ = A ∧
      ∃ j : Fin m, (j.val = 0 ∨ j.val + 2 = m ∨ j.val + 1 = m) ∧
        (∀ k, ¬ Commuting E (P k) ↔ k = j) ∧
        ¬ StarOneAt (Spin.cartanD m) (Spin.isFiniteType_cartanD m) j ∧
        ∃ w₀ : (coxeterMatrix (Spin.isFiniteType_cartanD m)).Group,
          (∀ w, (coxeterMatrix (Spin.isFiniteType_cartanD m)).toCoxeterSystem.length w ≤
            (coxeterMatrix (Spin.isFiniteType_cartanD m)).toCoxeterSystem.length w₀) ∧
          weylAction (Spin.isFiniteType_cartanD m) w₀ (Pi.single j 1) = -Pi.single j 1 := by
  have := h.finite
  obtain ⟨f, -, Ψ₀, hP, hQ, hsurj⟩ := hX.exists_surjective_D_le h.root h.noIsolated hm hgen₁
  have hnd : ∃ X ∈ Δ₁, ∃ Y ∈ Δ₁, Special R X Y := by
    refine ⟨P ⟨0, by omega⟩, (hPQ _).1, P ⟨1, by omega⟩, (hPQ _).1, ?_⟩
    have hedge : edgeD m ⟨0, by omega⟩ ⟨1, by omega⟩ :=
      Or.inl ⟨rfl, show 1 + 1 < m by omega⟩
    exact (hX.edge _ _ hedge).1
  obtain ⟨E, C, hLow, hEC, j, hj, hjE, hns, w₀, hw₀, hjw⟩ := exists_node_star_of_surjective h hA
    hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hS₁ hP₂ hQ₂ hPQ₂ hgen₂
    (Spin.plusDatum_isCTGroupDatum (n := m) (K := GaloisField 2 f) (by omega)
      (Spin.plusDatum_iSup_eq_top m _ (by omega)))
    (Spin.plusDatum_steinbergExtras (n := m) (by omega)) rfl (CaseE.posDef_D m) CaseE.adj_D
    (CaseE.highestD_mem (n := m) hm (GaloisField 2 f) (by omega)) CaseE.one_le_highestD hX hPQ
    hgen₁ hnd Ψ₀ hP hQ hsurj
  refine ⟨E, C, hLow, hEC, j, ?_, hjE, hns, w₀, hw₀, hjw⟩
  unfold CaseE.highestD at hj
  split_ifs at hj with h'
  · exact h'
  · omega

theorem exists_node_star_A {m : ℕ} (hm : 2 ≤ m) {P Q : Fin m → Subgroup G}
    (hX : IsConfig R (edgeA m) P Q) (hPQ : ∀ k, P k ∈ Δ₁ ∧ Q k ∈ Δ₁)
    (hgen₁ : ⨆ k, (P k ⊔ Q k) = gen Δ₁) :
    ∃ j : Fin m, ¬ StarOneAt (CartanMatrix.A m) (SpecialLinear.isFiniteType_A m) j ∧
      ∃ w₀ : (coxeterMatrix (SpecialLinear.isFiniteType_A m)).Group,
        (∀ w, (coxeterMatrix (SpecialLinear.isFiniteType_A m)).toCoxeterSystem.length w ≤
          (coxeterMatrix (SpecialLinear.isFiniteType_A m)).toCoxeterSystem.length w₀) ∧
        weylAction (SpecialLinear.isFiniteType_A m) w₀ (Pi.single j 1) = -Pi.single j 1 := by
  have := h.finite
  have hnd : ∃ X ∈ Δ₁, ∃ Y ∈ Δ₁, Special R X Y := by
    refine ⟨P ⟨0, by omega⟩, (hPQ _).1, P ⟨1, by omega⟩, (hPQ _).1, ?_⟩
    have hedge : edgeA m ⟨0, by omega⟩ ⟨1, by omega⟩ := rfl
    exact (hX.edge _ _ hedge).1
  have key : ∀ (f : ℕ) (Ψ₀ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f) →*
      ↥(gen Δ₁)),
      (∀ k, ((SpecialLinear.rootDatum m (GaloisField 2 f)).rootGroup (sroot k)).map Ψ₀ =
        (P k).subgroupOf (gen Δ₁)) →
      (∀ k, ((SpecialLinear.rootDatum m (GaloisField 2 f)).rootGroup (-sroot k)).map Ψ₀ =
        (Q k).subgroupOf (gen Δ₁)) → Function.Surjective Ψ₀ →
      ∃ j : Fin m, ¬ StarOneAt (CartanMatrix.A m) (SpecialLinear.isFiniteType_A m) j ∧
        ∃ w₀ : (coxeterMatrix (SpecialLinear.isFiniteType_A m)).Group,
          (∀ w, (coxeterMatrix (SpecialLinear.isFiniteType_A m)).toCoxeterSystem.length w ≤
            (coxeterMatrix (SpecialLinear.isFiniteType_A m)).toCoxeterSystem.length w₀) ∧
          weylAction (SpecialLinear.isFiniteType_A m) w₀ (Pi.single j 1) = -Pi.single j 1 :=
    fun f Ψ₀ hP hQ hsurj => by
      obtain ⟨-, -, -, -, j, -, -, hns, w₀, hw₀, hjw⟩ := exists_node_star_of_surjective h hA hAne
        hmax hA₀ h2 hΔ₁ hΔ₂ hne hS₁ hP₂ hQ₂ hPQ₂ hgen₂
        (SpecialLinear.isCTGroupDatum m (GaloisField 2 f))
        (SpecialLinear.steinbergExtras m (GaloisField 2 f)) rfl
        (TauCeti.posDef_map_intCast_cartanMatrix_A m) CaseE.adj_A
        (CaseE.highest_mem_A (by omega) (GaloisField 2 f)) (fun _ => le_rfl) hX hPQ hgen₁ hnd Ψ₀
        hP hQ hsurj
      exact ⟨j, hns, w₀, hw₀, hjw⟩
  rcases Nat.lt_or_ge m 3 with hm3 | hm3
  · obtain rfl : m = 2 := by omega
    obtain ⟨f, -, Ψ₀, hP, hQ, hsurj⟩ :=
      hX.exists_surjective_A_two_le h.root h.noIsolated hgen₁
    exact key f Ψ₀ hP hQ hsurj
  · obtain ⟨f, -, Ψ₀, hP, hQ, hsurj⟩ :=
      hX.exists_surjective_A_le h.root h.noIsolated hm3 hgen₁
    exact key f Ψ₀ hP hQ hsurj

theorem false_of_hasConfigIn_A {m : ℕ} (hm : 2 ≤ m) (hm3 : m ≠ 3)
    (hc : HasConfigIn R Δ₁ (edgeA m)) : False := by
  obtain ⟨P, Q, hX, hPQ, hgen₁⟩ := hc
  obtain ⟨j, hns, w₀, hw₀, hjw⟩ := exists_node_star_A h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hS₁ hP₂
    hQ₂ hPQ₂ hgen₂ hm hX hPQ hgen₁
  have hmj := eq_of_weylAction_longest_A hw₀ hjw
  exact hns (starOneAt_A (by omega) (by omega))

theorem false_of_hasConfigIn_E6 (hc : HasConfigIn R Δ₁ (edgeE 6)) : False := by
  have := h.finite
  obtain ⟨P, Q, hX, hPQ, hgen₁⟩ := hc
  obtain ⟨f, -, Ψ₀, hP, hQ, hsurj⟩ := hX.exists_surjective_E6_le h.root h.noIsolated hgen₁
  obtain ⟨-, -, -, -, j, hj, -, -, w₀, hw₀, hjw⟩ := exists_node_star_of_surjective h hA hAne
    hmax hA₀ h2 hΔ₁ hΔ₂ hne hS₁ hP₂ hQ₂ hPQ₂ hgen₂ (Minuscule.e6Datum_isCTGroupDatum _)
    (Minuscule.e6Datum_steinbergExtras _) rfl Minuscule.posDef_cartan_E6 CaseE.adj_E6
    (CaseE.highest_mem_E6 (GaloisField 2 f)) CaseE.one_le_highest_E6 hX hPQ hgen₁
    (special_of_isConfig_E (by norm_num) hX hPQ) Ψ₀ hP hQ hsurj
  exact weylAction_longest_ne_E6 Minuscule.posDef_cartan_E6 hw₀ (CaseE.eq_of_highest_E6 j hj)
    hjw

theorem false_of_hasConfigIn_E7 (hc : HasConfigIn R Δ₁ (edgeE 7)) : False := by
  have := h.finite
  obtain ⟨P, Q, hX, hPQ, hgen₁⟩ := hc
  obtain ⟨f, -, Ψ₀, hP, hQ, hsurj⟩ := hX.exists_surjective_E7_le h.root h.noIsolated hgen₁
  obtain ⟨-, -, -, -, j, hj, -, hns, -⟩ := exists_node_star_of_surjective h hA hAne hmax hA₀ h2
    hΔ₁ hΔ₂ hne hS₁ hP₂ hQ₂ hPQ₂ hgen₂ (Minuscule.e7Datum_isCTGroupDatum _)
    (Minuscule.e7Datum_steinbergExtras _) rfl Minuscule.posDef_cartan_E7 CaseE.adj_E7
    (CaseE.highest_mem_E7 (GaloisField 2 f)) CaseE.one_le_highest_E7 hX hPQ hgen₁
    (special_of_isConfig_E (by norm_num) hX hPQ) Ψ₀ hP hQ hsurj
  exact hns (starOneAt_E7 (CaseE.eq_of_highest_E7 j hj))

theorem false_of_hasConfigIn_E8 (hc : HasConfigIn R Δ₁ (edgeE 8)) : False := by
  have := h.finite
  obtain ⟨P, Q, hX, hPQ, hgen₁⟩ := hc
  obtain ⟨f, -, Ψ₀, hP, hQ, hsurj⟩ := hX.exists_surjective_E8_le h.root h.noIsolated hgen₁
  obtain ⟨-, -, -, -, j, hj, -⟩ := exists_node_star_of_surjective h hA hAne hmax hA₀ h2
    hΔ₁ hΔ₂ hne hS₁ hP₂ hQ₂ hPQ₂ hgen₂ (Adjoint.e8_isCTGroupDatum _)
    (Adjoint.e8_steinbergExtras _) rfl CaseE.posDef_E8 CaseE.adj_E8
    (CaseE.highest_mem_E8 (GaloisField 2 f)) CaseE.one_le_highest_E8 hX hPQ hgen₁
    (special_of_isConfig_E (by norm_num) hX hPQ) Ψ₀ hP hQ hsurj
  exact CaseE.ne_one_highest_E8 j hj

end Node

end CaseOA

theorem oaInputD' : OAInputD' := by
  intro G _ R h A hA hAne hmax A₀ hA₀ h2 Δ₁ hΔ₁ Δ₂ hΔ₂ hne hS₁ P₂ hP₂ Q₂ hQ₂ hPQ₂ hgen₂ m hm P Q
    hX hPQ hgen₁
  obtain ⟨E, C, hLow, hEC, j, hj, hjE, hns, w₀, hw₀, hjw⟩ := CaseOA.exists_node_star_D h hA hAne
    hmax hA₀ h2 hΔ₁ hΔ₂ hne hS₁ hP₂ hQ₂ hPQ₂ hgen₂ hm hX hPQ hgen₁
  refine ⟨E, C, hLow, hEC, j, hjE, ?_⟩
  rcases hj with h0 | hs
  · exact Or.inl h0
  · by_cases hm4 : m = 4
    · subst hm4
      exact Or.inr ⟨rfl, by omega⟩
    · exfalso
      rcases Nat.even_or_odd m with he | ho
      · exact hns (CaseOA.starOneAt_D (by obtain ⟨r, rfl⟩ := he; omega) hs)
      · exact CaseOA.weylAction_longest_spin_ne (by omega) ho hw₀ hs hjw

theorem oaExclInput : OAExclInput := by
  intro G _ R A A₀ Δ₁ Δ₂ hset _ hc
  obtain ⟨h, hA, -, hAne, hmax, hA₀, h2, hΔ₁, hΔ₂, hne, hS₁, P₂, hP₂, Q₂, hQ₂, hPQ₂, hgen₂⟩ :=
    hset
  exfalso
  rcases hc with ⟨m, hm, hm3, hcm⟩ | hc | hc | hc
  · exact CaseOA.false_of_hasConfigIn_A h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hS₁ hP₂ hQ₂ hPQ₂ hgen₂
      hm hm3 hcm
  · exact CaseOA.false_of_hasConfigIn_E6 h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hS₁ hP₂ hQ₂ hPQ₂
      hgen₂ hc
  · exact CaseOA.false_of_hasConfigIn_E7 h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hS₁ hP₂ hQ₂ hPQ₂
      hgen₂ hc
  · exact CaseOA.false_of_hasConfigIn_E8 h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hS₁ hP₂ hQ₂ hPQ₂
      hgen₂ hc

theorem caseOAStep_of_inputs₄ (hns : OANonSimplyLacedInput) (hdeg : OADegenerateInput) :
    CaseOAStep :=
  caseOAStep_of_inputs' oaInputD' (oaInputA3'_of_end oaEndInputA3) oaExclInput hns hdeg

end CFSG.Timmesfeld.ARS
