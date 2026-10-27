module

public import CFSG.Quasithin.Background.A318PL3Asm
public import CFSG.Quasithin.Background.A318PQuotes
public import CFSG.RankThree.PartTwo.KFacts.K72SylowL3
public import CFSG.Adapters.RankTwoModelTransports
public import CFSG.RankThree.SteinbergR3ELinearUnitaryOuterOrder
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdRank
public import CFSG.Open.PGLModelStated
public import CFSG.Quasithin.Background.A318PL3Iso
public import CFSG.Quasithin.Background.A318PL3Unit

public section

namespace CFSG.Quasithin

namespace A318P

open Matrix
open scoped Matrix
open CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Adapters.RankTwoModelTransports
  (glCongr glCongr_statedScalars glCongr_statedSU statedProjCongr statedProjEquivMapMk)

theorem statedSL_eq_det_ker' (n : ℕ) (K : Type) [Field K] :
    StatedSL n K = (GeneralLinearGroup.det : GL (Fin n) K →* Kˣ).ker :=
  CFSG.Open.StatedAPI.statedSL_eq_ker_det n K

theorem statedSU_eq_closure_det' (n q : ℕ) (K : Type) [Field K] :
    StatedSU n q K = Subgroup.closure {A : GL (Fin n) K | GeneralLinearGroup.det A = 1 ∧
      ((A : Matrix (Fin n) (Fin n) K).map (· ^ q))ᵀ * (A : Matrix (Fin n) (Fin n) K) = 1} :=
  CFSG.PGLModel.statedSU_eq_closure_det n q K

theorem projSL_of_statedClassicalModel_gen {G : Type} [Group G] {n p f : ℕ}
    (h : StatedClassicalModel G .PSL n p f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ f ∧
      Nonempty (G ≃* projSL n K) := by
  obtain ⟨-, K, hK, hKf, hcard, ⟨e⟩⟩ := h
  refine ⟨K, hK, hKf, hcard, ⟨e.trans ((statedProjEquivMapMk (StatedSL n K)).trans
    (MulEquiv.subgroupCongr ?_))⟩⟩
  rw [statedSL_eq_det_ker']
  rfl

theorem projSU_of_statedClassicalModel_gen {G : Type} [Group G] {n p f : ℕ} [Fact p.Prime]
    (h : StatedClassicalModel G .PSU n p f) : Nonempty (G ≃* projSU n p f) := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := h
  have hf1 : 1 ≤ f := hadm.2.1
  have hf : 0 < 2 * f := by omega
  have hK' : Nat.card K = p ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  let φ : K ≃+* GaloisField p (2 * f) :=
    CFSG.ClassicalModels.finiteFieldEquivGaloisField K p (2 * f) hf hK'
  refine ⟨e.trans ((statedProjCongr (glCongr φ) (glCongr_statedSU φ n (p ^ f))
    (glCongr_statedScalars φ)).trans ((statedProjEquivMapMk _).trans
      (MulEquiv.subgroupCongr ?_)))⟩
  rw [statedSU_eq_closure_det']
  rfl

theorem pRank_three_le_one_linear {S : Type} [Group S] [Finite S] {p₀ e₀ : ℕ}
    (hS : StatedClassicalModel S .PSL 3 p₀ e₀) (hq : p₀ ^ e₀ % 3 = 2) :
    CFSG.Open.pRank 3 (⊤ : Subgroup S) ≤ 1 := by
  obtain ⟨K, _, _, hK, ⟨e1⟩⟩ := projSL_of_statedClassicalModel_gen hS
  have hKmod : Nat.card K % 3 = 2 := by rw [hK]; exact hq
  exact CFSG.QuasithinUnique.Id2519.pRank_le_one_of_sylow_cyclic Nat.prime_three
    (fun Q => isCyclic_sylow_three_of_mulEquiv_projSL hKmod e1 Q)

theorem pRank_three_le_one_unitary {S : Type} [Group S] [Finite S] {p₀ e₀ : ℕ}
    (hS : StatedClassicalModel S .PSU 3 p₀ e₀) (hq : p₀ ^ e₀ % 3 = 1) :
    CFSG.Open.pRank 3 (⊤ : Subgroup S) ≤ 1 := by
  have : Fact p₀.Prime := ⟨hS.1.1⟩
  obtain ⟨φ⟩ := projSU_of_statedClassicalModel_gen hS
  have hf : e₀ ≠ 0 := by have := hS.1.2.1; omega
  exact CFSG.QuasithinUnique.Id2519.pRank_le_one_of_sylow_cyclic Nat.prime_three
    (fun Q => isCyclic_sylow_three_of_mulEquiv_projSU hf hq φ Q)

theorem outer_dvd_linear {S : Type} [Group S] [Finite S] {p₀ e₀ : ℕ}
    (hS : StatedClassicalModel S .PSL 3 p₀ e₀) :
    Nat.card (Outer S) ∣ 2 * e₀ * Nat.gcd 3 (p₀ ^ e₀ - 1) :=
  (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound (Or.inl rfl)
    (le_refl 3) hS.1.1 hS.1.2.1 hS).1

theorem outer_dvd_unitary {S : Type} [Group S] [Finite S] {p₀ e₀ : ℕ}
    (hS : StatedClassicalModel S .PSU 3 p₀ e₀) :
    Nat.card (Outer S) ∣ 2 * e₀ * Nat.gcd 3 (p₀ ^ e₀ + 1) :=
  (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound (Or.inr rfl)
    (le_refl 3) hS.1.1 hS.1.2.1 hS).1

theorem dvd_of_dvd_two_mul_gcd {r e₀ g : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3)
    (hg : g ∣ 3) (h : r ∣ 2 * e₀ * g) : r ∣ e₀ := by
  rcases (Nat.Prime.dvd_mul hr).1 h with h1 | h1
  · rcases (Nat.Prime.dvd_mul hr).1 h1 with h2 | h2
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h2) hr2
    · exact h2
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 (h1.trans hg)) hr3

theorem five_le_of_prime {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3) : 5 ≤ r := by
  have h2 := hr.two_le
  by_contra h
  have : r = 4 := by omega
  subst this
  exact absurd hr (by norm_num)

theorem aut_L3_linear (ql : QLiePRank) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {X : Type} [Group X]
    [Finite X] {S : Subgroup X} [S.Normal] (hC : ∀ c : X, (∀ s ∈ S, c * s = s * c) → c = 1)
    [IsSimpleGroup ↥S] {p₀ e₀ : ℕ} (hpe : p₀ = 2 ∨ e₀ = 1)
    (hS : StatedClassicalModel ↥S .PSL 3 p₀ e₀) (hrS : 1 < CFSG.Open.pRank r S)
    (hX : CFSG.Open.pRank r (⊤ : Subgroup X) ≤ 2) :
    oPrimeResidualOf r (⊤ : Subgroup X) = S ∨ (r = 3 ∧ A318Case2 S) := by
  have hrdvd := dvd_card_of_one_lt_pRank hr hrS
  by_cases hout : r ∣ Nat.card (Outer ↥S)
  swap
  · exact Or.inl (oPrimeResidualOf_eq_of_not_dvd_outer hC hr hrdvd hout)
  have hp₀ : p₀.Prime := hS.1.1
  have he₀ : 1 ≤ e₀ := hS.1.2.1
  have h1 := hout.trans (outer_dvd_linear hS)
  by_cases hr3 : r = 3
  · subst hr3
    have hmod3 : p₀ ^ e₀ % 3 = 0 ∨ p₀ ^ e₀ % 3 = 1 ∨ p₀ ^ e₀ % 3 = 2 := by omega
    rcases hmod3 with h0 | hq | hq
    · exfalso
      have hp3 : 3 = p₀ := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp₀).1
        (Nat.Prime.dvd_of_dvd_pow Nat.prime_three (Nat.dvd_of_mod_eq_zero h0))
      have he1 : e₀ = 1 := by
        rcases hpe with h | h
        · omega
        · exact h
      subst he1
      subst hp3
      norm_num at h1
    · obtain ⟨hadm, K, hKfield, hKfin, hK, ⟨e⟩⟩ := id hS
      have h3K : 3 ∣ Nat.card K - 1 := by rw [hK]; omega
      let e' : ↥S ≃* LinearFlag.projectiveSL 3 K :=
        e.trans ((projectiveSpecialLinearGroupEquivStatedProj 3 K).symm.trans
          (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K))
      let F := (l3FrameLinear h3K).ofMulEquiv e'
      have hcyc := card_ringAut_and_isCyclic hp₀ K hK
      have : IsCyclic (K ≃+* K) := hcyc.2
      have hPGL : ∀ (T : Type) [Group T], Nonempty (T ≃* ↥F.D) →
          IsPGLEps3 true (p₀ ^ e₀) T := by
        intro T _ ⟨φ⟩
        exact ⟨K, hKfield, hKfin, hK, ⟨φ.trans ((comapEquivOfMulEquiv (MulAut.congr e')
          (LinearFlag.linearAutGroup 3 K)).trans (pglEquivLinearAut K).symm)⟩⟩
      have hcirc : (∃ c : K ≃+* K, orderOf c = 3) →
          ∃ m : ℕ, p₀ ^ e₀ = 2 ^ (3 * m) ∧ IsPSLEps3 true 2 (3 * m) ↥S := by
        rintro ⟨c, hc⟩
        have hdvd : 3 ∣ e₀ := by
          have := orderOf_dvd_natCard c
          rw [hc, hcyc.1] at this
          exact this
        obtain ⟨m, hm⟩ := hdvd
        have hp2 : p₀ = 2 := by
          rcases hpe with h | h
          · exact h
          · omega
        subst hp2
        subst hm
        exact ⟨m, rfl, hS⟩
      have hmod : Int.ModEq 3 ((p₀ ^ e₀ : ℕ) : ℤ) (if true = true then 1 else -1) := by
        simp only [↓reduceIte]
        unfold Int.ModEq
        omega
      exact (a318Case2_of_frame hC hrdvd F hX hmod ⟨p₀, e₀, hp₀, he₀, rfl, hS⟩ hPGL hcirc).imp_right
        (fun h => ⟨rfl, h⟩)
    · exfalso
      have h1' := pRank_three_le_one_linear hS hq
      rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup S] at hrS
      omega
  · have hr5 := five_le_of_prime hr hr2 hr3
    have hdvd : r ∣ e₀ := dvd_of_dvd_two_mul_gcd hr hr2 hr3 (Nat.gcd_dvd_left 3 _) h1
    have he5 : 5 ≤ e₀ := hr5.trans (Nat.le_of_dvd (by omega) hdvd)
    have hp2 : p₀ = 2 := by
      rcases hpe with h | h
      · exact h
      · omega
    subst hp2
    have hfam : LieTwoFamily ↥S := Or.inl ⟨e₀, he₀, hS⟩
    left
    exact oPrimeResidualOf_eq_of_forall hr hrdvd fun x k hk =>
      ql r hr hr5 X S hC inferInstance hfam hrS hX x ⟨k, hk⟩

theorem aut_L3_unitary (ql : QLiePRank) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {X : Type} [Group X]
    [Finite X] {S : Subgroup X} [S.Normal] (hC : ∀ c : X, (∀ s ∈ S, c * s = s * c) → c = 1)
    [IsSimpleGroup ↥S] {p₀ e₀ : ℕ} (hpe : p₀ = 2 ∨ e₀ = 1)
    (hS : StatedClassicalModel ↥S .PSU 3 p₀ e₀) (hrS : 1 < CFSG.Open.pRank r S)
    (hX : CFSG.Open.pRank r (⊤ : Subgroup X) ≤ 2) :
    oPrimeResidualOf r (⊤ : Subgroup X) = S ∨ (r = 3 ∧ A318Case2 S) := by
  have hrdvd := dvd_card_of_one_lt_pRank hr hrS
  by_cases hout : r ∣ Nat.card (Outer ↥S)
  swap
  · exact Or.inl (oPrimeResidualOf_eq_of_not_dvd_outer hC hr hrdvd hout)
  have hp₀ : p₀.Prime := hS.1.1
  have he₀ : 1 ≤ e₀ := hS.1.2.1
  have h1 := hout.trans (outer_dvd_unitary hS)
  by_cases hr3 : r = 3
  · subst hr3
    have hmod3 : p₀ ^ e₀ % 3 = 0 ∨ p₀ ^ e₀ % 3 = 1 ∨ p₀ ^ e₀ % 3 = 2 := by omega
    rcases hmod3 with h0 | hq | hq
    · exfalso
      have hp3 : 3 = p₀ := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp₀).1
        (Nat.Prime.dvd_of_dvd_pow Nat.prime_three (Nat.dvd_of_mod_eq_zero h0))
      have he1 : e₀ = 1 := by
        rcases hpe with h | h
        · omega
        · exact h
      subst he1
      subst hp3
      norm_num at h1
    · exfalso
      have h1' := pRank_three_le_one_unitary hS hq
      rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup S] at hrS
      omega
    · obtain ⟨⟨-, -, hadm⟩, K, hKfield, hKfin, hK, ⟨e⟩⟩ := id hS
      have hne : p₀ ^ e₀ ≠ 2 := fun h => (show 3 ≤ 3 ∧ (3, p₀ ^ e₀) ≠ (3, 2) from hadm).2
        (by rw [h])
      have hq2 : 2 < p₀ ^ e₀ := by omega
      have h3 : 3 ∣ p₀ ^ e₀ + 1 := by omega
      have hKU : UnitaryFieldData p₀ e₀ K := ⟨hp₀, he₀, by rw [hK, ← pow_mul, mul_comm]⟩
      let e' : ↥S ≃* unitaryPSU hKU 3 :=
        e.trans (unitaryPSUEquiv hKU (by norm_num)).symm
      let F := (l3FramePSU hKU hq2 h3).ofMulEquiv e'
      have hK' : Nat.card K = p₀ ^ (2 * e₀) := hKU.card
      have hcyc := card_ringAut_and_isCyclic hp₀ K hK'
      have : IsCyclic (K ≃+* K) := hcyc.2
      have hPGL : ∀ (T : Type) [Group T], Nonempty (T ≃* ↥F.D) →
          IsPGLEps3 false (p₀ ^ e₀) T := by
        intro T _ ⟨φ⟩
        exact ⟨K, hKfield, hKfin, hK, ⟨φ.trans ((comapEquivOfMulEquiv (MulAut.congr e')
          (psuConj hKU).range).trans (pguEquivPsuConj hKU).symm)⟩⟩
      have hcirc : (∃ c : K ≃+* K, orderOf c = 3) →
          ∃ m : ℕ, p₀ ^ e₀ = 2 ^ (3 * m) ∧ IsPSLEps3 false 2 (3 * m) ↥S := by
        rintro ⟨c, hc⟩
        have hdvd : 3 ∣ 2 * e₀ := by
          have := orderOf_dvd_natCard c
          rw [hc, hcyc.1] at this
          exact this
        obtain ⟨m, hm⟩ : 3 ∣ e₀ := by omega
        have hp2 : p₀ = 2 := by
          rcases hpe with h | h
          · exact h
          · omega
        subst hp2
        subst hm
        exact ⟨m, rfl, hS⟩
      have hmod : Int.ModEq 3 ((p₀ ^ e₀ : ℕ) : ℤ) (if false = true then 1 else -1) := by
        simp only [Bool.false_eq_true, ↓reduceIte]
        unfold Int.ModEq
        omega
      exact (a318Case2_of_frame hC hrdvd F hX hmod ⟨p₀, e₀, hp₀, he₀, rfl, hS⟩ hPGL hcirc).imp_right
        (fun h => ⟨rfl, h⟩)
  · have hr5 := five_le_of_prime hr hr2 hr3
    have hdvd : r ∣ e₀ := dvd_of_dvd_two_mul_gcd hr hr2 hr3 (Nat.gcd_dvd_left 3 _) h1
    have he5 : 5 ≤ e₀ := hr5.trans (Nat.le_of_dvd (by omega) hdvd)
    have hp2 : p₀ = 2 := by
      rcases hpe with h | h
      · exact h
      · omega
    subst hp2
    have hfam : LieTwoFamily ↥S := Or.inr (Or.inl ⟨e₀, by omega, hS⟩)
    left
    exact oPrimeResidualOf_eq_of_forall hr hrdvd fun x k hk =>
      ql r hr hr5 X S hC inferInstance hfam hrS hX x ⟨k, hk⟩

end A318P

end CFSG.Quasithin
