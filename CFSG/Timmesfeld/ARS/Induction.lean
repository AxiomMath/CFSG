module

public import CFSG.Timmesfeld.ARS.SimplyLacedConfigA
public import CFSG.Timmesfeld.ARS.Sec8Hyp
public import CFSG.Timmesfeld.ARS.CaseD4
public import CFSG.Timmesfeld.ARS.LinearMain
public import CFSG.Timmesfeld.ARS.ExclNSDefs

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.Timmesfeld.RankOne CFSG.LieType CFSG.LieType.Universal Matrix CFSG.Blueprint
open CFSG.Assembly.LowTwoRank

section Output

variable {G : Type*} [Group G]

@[expose] def HasGenConfig (R : Set (Subgroup G)) {r : ℕ} (adj : Fin r → Fin r → Prop) : Prop :=
  ∃ A B : Fin r → Subgroup G, IsConfig R adj A B ∧ ⨆ k, (A k ⊔ B k) = ⊤

@[expose] def HasConfigIn (R Δ : Set (Subgroup G)) {r : ℕ} (adj : Fin r → Fin r → Prop) :
    Prop :=
  ∃ A B : Fin r → Subgroup G, IsConfig R adj A B ∧ (∀ k, A k ∈ Δ ∧ B k ∈ Δ) ∧
    ⨆ k, (A k ⊔ B k) = gen Δ

end Output

@[expose] def NonSimplyLacedOutcome (G : Type) [Group G] : Prop :=
  (∃ n f : ℕ, 3 ≤ n ∧ 1 ≤ f ∧ LieModel G .PSp n 2 f) ∨
  (∃ n f : ℕ, 4 ≤ n ∧ 1 ≤ f ∧ LieModel G .POmegaMinus n 2 f) ∨
  (∃ f : ℕ, 2 ≤ f ∧ LieModel G .G2 0 2 f) ∨
  (∃ f : ℕ, 1 ≤ f ∧ ∃ t ∈ ({.trialityD4, .F4, .twistedE6} : Finset StatedLieTag),
    LieModel G t 0 2 f) ∨
  LieModel G .PSU 3 3 1

@[expose] def Output (G : Type) [Group G] (R : Set (Subgroup G)) : Prop :=
  (∃ m, 2 ≤ m ∧ HasGenConfig R (edgeA m)) ∨ (∃ m, 4 ≤ m ∧ HasGenConfig R (edgeD m)) ∨
    HasGenConfig R (edgeE 6) ∨ HasGenConfig R (edgeE 7) ∨ HasGenConfig R (edgeE 8) ∨
    (NonSimplyLacedOutcome G ∧ NSLData G R)

theorem Output.of_nonSimplyLaced {G : Type} [Group G] {R : Set (Subgroup G)}
    (h : NonSimplyLacedOutcome G) (hd : NSLData G R) : Output G R :=
  .inr (.inr (.inr (.inr (.inr ⟨h, hd⟩))))

theorem IsConfig.lieModel_A_two {G : Type} [Group G] [Finite G] {R : Set (Subgroup G)}
    (hR : IsRootClass R) (hiso : NoIsolated R) (hZ : Subgroup.center G = ⊥)
    {A B : Fin 2 → Subgroup G} (hX : IsConfig R (edgeA 2) A B) (hgen : ⨆ k, (A k ⊔ B k) = ⊤) :
    ∃ f : ℕ, 1 ≤ f ∧ (∀ E ∈ R, Nat.card E = 2 ^ f) ∧ LieModel G .PSL 3 2 f := by
  obtain ⟨f, hf, hcard, ρ, hρ, hedge⟩ := hX.exists_frame hR hiso (isRootedTree_A (by omega))
  set F := GaloisField 2 f
  have hF : Nat.card F = 2 ^ f := GaloisField.card 2 f (by omega)
  obtain ⟨ψ, hψ⟩ := hedge 0 1 (by decide)
  have hu : ∀ k, Set.range (fun c => ρ k (tv 0 1 c)) = (A k : Set G) := fun k => by
    rw [← (hρ k).2.1]
    exact Linear.range_tv_upper (ρ k)
  have hv : ∀ k, Set.range (fun c => ρ k (tv 1 0 c)) = (B k : Set G) := fun k => by
    rw [← (hρ k).2.2]
    exact Linear.range_tv_lower (ρ k)
  have hsurj : Function.Surjective ψ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hgen]
    refine iSup_le fun k => sup_le ?_ ?_
    · intro a ha
      rw [← SetLike.mem_coe, ← hu] at ha
      obtain ⟨c, rfl⟩ := ha
      fin_cases k
      · exact ⟨tv 0 1 c, (hψ c).1⟩
      · exact ⟨tv 1 2 c, (hψ c).2.2.1⟩
    · intro b hb
      rw [← SetLike.mem_coe, ← hv] at hb
      obtain ⟨c, rfl⟩ := hb
      fin_cases k
      · exact ⟨tv 1 0 c, (hψ c).2.1⟩
      · exact ⟨tv 2 1 c, (hψ c).2.2.2⟩
  obtain ⟨a, ha, ha1⟩ := hR.exists_ne_one (hX.memA 0)
  obtain ⟨g, hg⟩ := hsurj a
  exact ⟨f, hf, hcard, lieModel_of_center_eq_bot hZ (lieModel_quotient_of_surjective
    (SpecialLinear.isQuasisimple 2 F le_rfl) (lieModel_SL3_quotient Nat.prime_two hf hF) hsurj
    ⟨g, by rw [hg]; exact ha1⟩)⟩

theorem Output.outcome {G : Type} [Group G] {R : Set (Subgroup G)} (h : Hyp G R)
    (ho : Output G R) : Outcome G := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hZ := h.center
  rcases ho with ⟨m, hm, A, B, hX, hgen⟩ | ⟨m, hm, A, B, hX, hgen⟩ | ⟨A, B, hX, hgen⟩ |
    ⟨A, B, hX, hgen⟩ | ⟨A, B, hX, hgen⟩ | ⟨hns, -⟩
  · rcases Nat.lt_or_ge m 3 with hm3 | hm3
    · obtain rfl : m = 2 := by omega
      obtain ⟨f, hf, -, hL⟩ := hX.lieModel_A_two hR hiso hZ hgen
      exact Or.inl ⟨3, f, le_rfl, hf, hL⟩
    · obtain ⟨f, hf, -, hL⟩ := hX.lieModel_A hR hiso hZ hm3 hgen
      exact Or.inl ⟨m + 1, f, by omega, hf, hL⟩
  · obtain ⟨f, hf, -, hL⟩ := hX.lieModel_D hR hiso hZ hm hgen
    exact .inr (.inr (.inl ⟨m, f, hm, hf, Or.inl hL⟩))
  · obtain ⟨f, hf, -, hL⟩ := hX.lieModel_E6 hR hiso hZ hgen
    exact .inr (.inr (.inr (.inr (.inl ⟨f, hf, .E6, by decide, hL⟩))))
  · obtain ⟨f, hf, -, hL⟩ := hX.lieModel_E7 hR hiso hZ hgen
    exact .inr (.inr (.inr (.inr (.inl ⟨f, hf, .E7, by decide, hL⟩))))
  · obtain ⟨f, hf, -, hL⟩ := hX.lieModel_E8 hR hiso hZ hgen
    exact .inr (.inr (.inr (.inr (.inl ⟨f, hf, .E8, by decide, hL⟩))))
  · rcases hns with ⟨n, f, hn, hf, hL⟩ | ⟨n, f, hn, hf, hL⟩ | ⟨f, hf, hL⟩ |
      ⟨f, hf, t, ht, hL⟩ | hL
    · exact .inr (.inl ⟨n, f, hn, hf, hL⟩)
    · exact .inr (.inr (.inl ⟨n, f, hn, hf, Or.inr hL⟩))
    · exact .inr (.inr (.inr (.inl ⟨f, hf, hL⟩)))
    · refine .inr (.inr (.inr (.inr (.inl ⟨f, hf, t, ?_, hL⟩))))
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl <;> decide
    · exact .inr (.inr (.inr (.inr (.inr (.inl hL)))))

abbrev IndHyp (G : Type) [Group G] : Prop :=
  ∀ (G' : Type) [Group G'] (R' : Set (Subgroup G')), Hyp G' R' → Nat.card G' < Nat.card G →
    Output G' R'

@[expose] def InductionStep : Prop :=
  ∀ (G : Type) [Group G] (R : Set (Subgroup G)), Hyp G R → IndHyp G → Output G R

theorem output_of_step (hs : InductionStep) (G : Type) [Group G] (R : Set (Subgroup G))
    (h : Hyp G R) : Output G R := by
  suffices key : ∀ n (G : Type) [Group G] (R : Set (Subgroup G)), Nat.card G ≤ n → Hyp G R →
      Output G R from key _ G R le_rfl h
  intro n
  induction n with
  | zero =>
    intro G _ R hn h
    have := h.finite
    have := Nat.card_pos (α := G)
    omega
  | succ n ih =>
    intro G _ R hn h
    exact hs G R h fun G' _ R' h' hlt => ih G' R' (by omega) h'

theorem arsInput_of_step (hs : InductionStep) : ARSInput :=
  fun G _ R h => (output_of_step hs G R h).outcome h

@[expose] def CaseLStep : Prop :=
  ∀ (G : Type) [Group G] (R : Set (Subgroup G)), Hyp G R → IndHyp G → ∀ A ∈ R,
    ¬ IsCoatom (Subgroup.normalizer (A : Set G)) → Output G R

@[expose] def CaseHStep : Prop :=
  ∀ (G : Type) [Group G] (R : Set (Subgroup G)), Hyp G R → IndHyp G → ∀ A ∈ R,
    IsCoatom (Subgroup.normalizer (A : Set G)) → sigmaSet R A = lambdaSet R A → Output G R

@[expose] def CaseBStep : Prop :=
  ∀ (G : Type) [Group G] (R : Set (Subgroup G)), Hyp G R → IndHyp G → ∀ A ∈ R,
    IsCoatom (Subgroup.normalizer (A : Set G)) → sigmaSet R A ≠ lambdaSet R A →
      ¬ IsSigmaMaximal R (centralGroup R A) → Output G R

@[expose] def CaseMaxStep : Prop :=
  ∀ (G : Type) [Group G] (R : Set (Subgroup G)), Hyp G R → IndHyp G → ∀ A ∈ R,
    IsCoatom (Subgroup.normalizer (A : Set G)) → sigmaSet R A ≠ lambdaSet R A →
      IsSigmaMaximal R (centralGroup R A) → Output G R

theorem inductionStep_of_cases (hL : CaseLStep) (hH : CaseHStep) (hB : CaseBStep)
    (hM : CaseMaxStep) : InductionStep := by
  intro G _ R h IH
  obtain ⟨A, hA, -⟩ := h.nondeg
  by_cases hmax : IsCoatom (Subgroup.normalizer (A : Set G))
  · by_cases hSig : sigmaSet R A = lambdaSet R A
    · exact hH G R h IH A hA hmax hSig
    · by_cases hC : IsSigmaMaximal R (centralGroup R A)
      · exact hM G R h IH A hA hmax hSig hC
      · exact hB G R h IH A hA hmax hSig hC
  · exact hL G R h IH A hA hmax

theorem arsInput_of_caseSteps (hL : CaseLStep) (hH : CaseHStep) (hB : CaseBStep)
    (hM : CaseMaxStep) : ARSInput :=
  arsInput_of_step (inductionStep_of_cases hL hH hB hM)

namespace Linear.IsRootFrame

variable {G : Type*} [Group G] {R : Set (Subgroup G)} {m : ℕ}
  {X : Fin (m + 1) → Fin (m + 1) → Subgroup G}

theorem isConfig (hX : IsRootFrame R (m + 1) X) :
    IsConfig R (edgeA m) (fun k => X k.castSucc k.succ) (fun k => X k.succ k.castSucc) := by
  have hne : ∀ k : Fin m, k.castSucc ≠ k.succ := fun k => Fin.castSucc_lt_succ.ne
  have hv' : ∀ a b : Fin (m + 1), a.val ≠ b.val → a ≠ b := fun a b h e => h (congrArg Fin.val e)
  refine ⟨fun k => hX.mem _ _ (hne k), fun k => hX.mem _ _ (hne k).symm,
    fun k => hX.opposite _ _ (hne k), fun i j hij => hX.config hij, fun i j hij h1 h2 => ?_⟩
  have hij' : i.val ≠ j.val := fun e => hij (Fin.ext e)
  simp only [edgeA] at h1 h2
  refine ⟨hX.commuting _ _ _ _ (hne i) (hne j) (hv' _ _ ?_) (hv' _ _ ?_),
    hX.commuting _ _ _ _ (hne i) (hne j).symm (hv' _ _ ?_) (hv' _ _ ?_),
    hX.commuting _ _ _ _ (hne i).symm (hne j) (hv' _ _ ?_) (hv' _ _ ?_),
    hX.commuting _ _ _ _ (hne i).symm (hne j).symm (hv' _ _ ?_) (hv' _ _ ?_)⟩ <;>
    simp only [Fin.val_castSucc, Fin.val_succ] <;> omega

end Linear.IsRootFrame

theorem caseLStep : CaseLStep := by
  intro G _ R h _ A hA hmax
  obtain ⟨Δ, hΔ, hAΔ⟩ := (exists_isTI_iff h hA).1 hmax
  have := h.finite
  have hΩ : ∀ A ∈ R, ∀ B ∈ R, omegaSet R B = omegaSet R A → B = A :=
    fun _ hA _ hB e => eq_of_omegaSet_eq h hA hB e
  obtain ⟨m, hm⟩ := Sec5.exists_card_gen_eq_pow h.root h.noIsolated h.nondeg hΩ hΔ.isWeakTI hAΔ
  obtain ⟨hm2, X, hX⟩ := Linear.exists_isRootFrame h.root h.noIsolated h.nondeg hΩ hΔ hAΔ hm
  exact Or.inl ⟨m, hm2, _, _, hX.isConfig, hX.iSup_adj_eq_top⟩

open CaseD4 in
theorem CaseD4.hasGenConfig {G : Type} [Group G] {R : Set (Subgroup G)} (h : Hyp G R)
    {A A₀ : Subgroup G} (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
    (hmax : IsSigmaMaximal R (centralGroup R A)) (hA₀ : A₀ ∈ omegaSet R A)
    {P Q : Fin 3 → Subgroup G} (hPQ : LeviSL2Cube R A A₀ P Q) : HasGenConfig R (edgeD 4) := by
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
      Commuting S T := fun a b hab S T hS hT x hx y hy => commute_of_mem hPQ hab (hS hx) (hT hy)
  let X : Fin 4 → Subgroup G := ![P 0, E, P 1, P 2]
  let Y : Fin 4 → Subgroup G := ![Q 0, F, Q 1, Q 2]
  refine ⟨X, Y, ⟨fun k => ?_, fun k => ?_, fun k => ?_, fun i j hij => ?_,
    fun i j hij h1 h2 => ?_⟩, ?_⟩
  · fin_cases k
    exacts [hPR 0, hER, hPR 1, hPR 2]
  · fin_cases k
    exacts [hQR 0, hFR, hQR 1, hQR 2]
  · fin_cases k
    exacts [hPQ.opposite 0, hEF, hPQ.opposite 1, hPQ.opposite 2]
  · fin_cases i <;> fin_cases j <;> simp [edgeD] at hij
    · exact hcfg 0
    · exact hright 1
    · exact hright 2
  · fin_cases i <;> fin_cases j <;> simp [edgeD] at hij h1 h2 <;>
      exact ⟨hcm _ _ (by decide) le_sup_left le_sup_left,
        hcm _ _ (by decide) le_sup_left le_sup_right, hcm _ _ (by decide) le_sup_right le_sup_left,
        hcm _ _ (by decide) le_sup_right le_sup_right⟩
  · rw [eq_top_iff, ← iSup_sup_sup_eq_top h hA hAne hmax hA₀ hPQ hE hF]
    refine sup_le (sup_le (iSup_le fun i => ?_) ?_) ?_
    · fin_cases i
      · exact le_iSup (fun k => X k ⊔ Y k) 0
      · exact le_iSup (fun k => X k ⊔ Y k) 2
      · exact le_iSup (fun k => X k ⊔ Y k) 3
    · exact le_sup_left.trans (le_iSup (fun k => X k ⊔ Y k) 1)
    · exact le_sup_right.trans (le_iSup (fun k => X k ⊔ Y k) 1)

namespace Levi

variable {G : Type} [Group G] {R : Set (Subgroup G)}

theorem output (IH : IndHyp G) (h : Hyp G R) {A A₀ E₀ : Subgroup G} (hA : A ∈ R)
    (hAne : sigmaSet R A ≠ lambdaSet R A) (hA₀ : A₀ ∈ omegaSet R A)
    (hE₀ : E₀ ∈ leviSet R A A₀)
    (hnd : ∃ X ∈ comp R A A₀ E₀, ∃ Y ∈ comp R A A₀ E₀, Special R X Y) :
    (∃ m, 2 ≤ m ∧ HasConfigIn R (comp R A A₀ E₀) (edgeA m)) ∨
      (∃ m, 4 ≤ m ∧ HasConfigIn R (comp R A A₀ E₀) (edgeD m)) ∨
      HasConfigIn R (comp R A A₀ E₀) (edgeE 6) ∨ HasConfigIn R (comp R A A₀ E₀) (edgeE 7) ∨
      HasConfigIn R (comp R A A₀ E₀) (edgeE 8) ∨
      (NonSimplyLacedOutcome
        (↥(gen (comp R A A₀ E₀)) ⧸ Subgroup.center ↥(gen (comp R A A₀ E₀))) ∧
        NSLData (↥(gen (comp R A A₀ E₀)) ⧸ Subgroup.center ↥(gen (comp R A A₀ E₀)))
          (quotClass (gen (comp R A A₀ E₀)) (comp R A A₀ E₀))) := by
  have hq := quotHyp h hA hAne hA₀ hE₀ hnd
  have hlt := card_quot_lt h hA hAne hA₀ hE₀
  have lift : ∀ {r : ℕ} {adj : Fin r → Fin r → Prop},
      HasGenConfig (quotClass (gen (comp R A A₀ E₀)) (comp R A A₀ E₀)) adj →
        HasConfigIn R (comp R A A₀ E₀) adj := by
    rintro r adj ⟨A', B', hX', hgen'⟩
    obtain ⟨A₁, B₁, hX₁, hmem⟩ := exists_isConfig_of_quot h hA hAne hA₀ hE₀ hX'
    refine ⟨A₁, B₁, hX₁, fun k => ⟨(hmem k).1, (hmem k).2.1⟩,
      iSup_eq_of_iSup_quotMap_eq_top h hA hAne hA₀ hE₀ (fun k => (hmem k).1)
        (fun k => (hmem k).2.1) ?_⟩
    have e : ∀ k, quotMap (gen (comp R A A₀ E₀)) (A₁ k) ⊔ quotMap (gen (comp R A A₀ E₀)) (B₁ k) =
        A' k ⊔ B' k := fun k => by rw [(hmem k).2.2.1, (hmem k).2.2.2]
    rw [iSup_congr e]
    exact hgen'
  rcases IH _ _ hq hlt with ⟨m, hm, hc⟩ | ⟨m, hm, hc⟩ | hc | hc | hc | hns
  · exact Or.inl ⟨m, hm, lift hc⟩
  · exact .inr (.inl ⟨m, hm, lift hc⟩)
  · exact .inr (.inr (.inl (lift hc)))
  · exact .inr (.inr (.inr (.inl (lift hc))))
  · exact .inr (.inr (.inr (.inr (.inl (lift hc)))))
  · exact .inr (.inr (.inr (.inr (.inr hns))))

end Levi

end CFSG.Timmesfeld.ARS
