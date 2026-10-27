module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeCycSeven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeCycThreeCoord
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeCycThreeFix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeCycThreeFrame
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeTools
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154ZpFacts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

section ThreeFour

variable {W : Type} [CommGroup W]

theorem s168e3_z3_four_dichotomy [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    (hcard : Nat.card W = 2 ^ 4) {A L : Subgroup (MulAut W)} {t : MulAut W} (hLA : L ≤ A)
    (hLn : ∀ g ∈ A, L.map (MulAut.conj g).toMonoidHom = L) (hL : IsElemAbelianOfRank 3 1 ↥L)
    (hWL : commSub ⊤ L = ⊤) (hind : IsIndivisible A)
    (hO2 : ∀ P : Subgroup (MulAut W), P ≤ A → (P.subgroupOf A).Normal → IsPGroup 2 ↥P → P = ⊥)
    (ht : t ∈ A) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1)
    (htr : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3) (hW' : Conc4_136W A t L) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hqm : 2 ≤ CFSG.Open.pRank q A) :
    S168e3Tool A q ∨ ∃ K : Subgroup (MulAut W), Conc4_136W A t K ∧ IsCyclicOrd ↥K 3 ∧
      rk ↥(commSub ⊤ K) = 2 ∧
      Set.ncard {X : Subgroup (MulAut W) | ∃ φ ∈ A, X = K.map (MulAut.conj φ).toMonoidHom} = 2 ∧
      ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ 3 → CFSG.Open.pRank r A < 2 := by
  obtain ⟨x, hLx, hxo⟩ := s168e3_cyc_gen Nat.prime_three hL
  have hLcard : Nat.card ↥L = 3 := by rw [hLx, Nat.card_zpowers, hxo]
  have h133 := s16h_conc4_133_of_prime_card Nat.prime_three hLcard hW'
  obtain ⟨p', hp', -, hne, -⟩ := h133
  have hinv : t * x * t⁻¹ = x⁻¹ :=
    s168e3_cyc_inv Nat.prime_three hLx hxo ht ht2 hLn hne
  have hfpf : ∀ w : W, x w = w → w = 1 :=
    s168e3_cyc_fpf hW hLx (by rw [hxo]; decide) hWL
  have hq3 : q = 3 := by
    by_contra hq3
    have h5 : 5 ≤ q := hq.five_le_of_ne_two_of_ne_three hq2 hq3
    have hlt := s168e3_pRank_lt_two_of_rk_le_four hW (d := 4) le_rfl hcard hq h5 A
    omega
  subst q
  obtain ⟨E, hEA, hLE, hE9, hEc, hE3, h27⟩ :=
    s168e3_cyc3_sylow hW hcard hLA hLn hLcard hqm
  have hxE : x ∈ E := hLE (by rw [hLx]; exact Subgroup.mem_zpowers x)
  obtain ⟨y₁, y₂, Z₁, Z₂, hy₁E, hy₂E, hy₁, hy₂, hfix₁, hfix₂, hcom₁, hcom₂,
    hZ₁, hZ₂, hZ, hZtop⟩ := s168e3_cyc3_frame hW hcard hxE hE9 hEc hE3 hfpf
  by_cases hperm : ∀ g ∈ A, (Z₁.map g.toMonoidHom = Z₁ ∧ Z₂.map g.toMonoidHom = Z₂) ∨
      (Z₁.map g.toMonoidHom = Z₂ ∧ Z₂.map g.toMonoidHom = Z₁)
  · have hswap : ∃ g ∈ A, Z₁.map g.toMonoidHom = Z₂ := by
      by_contra hno
      have hall : ∀ g ∈ A, Z₁.map g.toMonoidHom = Z₁ ∧ Z₂.map g.toMonoidHom = Z₂ := by
        intro g hgA
        rcases hperm g hgA with h | h
        · exact h
        · exact absurd ⟨g, hgA, h.1⟩ hno
      have hstab₁ : StableUnder A Z₁ := by
        intro g hgA u hu
        have hmem : g.toMonoidHom u ∈ Z₁.map g.toMonoidHom :=
          Subgroup.mem_map_of_mem g.toMonoidHom hu
        rwa [(hall g hgA).1] at hmem
      have hstab₂ : StableUnder A Z₂ := by
        intro g hgA u hu
        have hmem : g.toMonoidHom u ∈ Z₂.map g.toMonoidHom :=
          Subgroup.mem_map_of_mem g.toMonoidHom hu
        rwa [(hall g hgA).2] at hmem
      rcases hind Z₁ Z₂ hstab₁ hstab₂ hZtop with h | h
      · rw [h, Subgroup.card_top, hcard] at hZ₁
        norm_num at hZ₁
      · rw [h, Subgroup.card_top, hcard] at hZ₂
        norm_num at hZ₂
    set B : Subgroup (MulAut W) :=
      A ⊓ Subgroup.centralizer (L : Set (MulAut W)) ⊓ stabSub Z₁ ⊓ stabSub Z₂ with hBdef
    set K : Subgroup (MulAut W) := B ⊓ centSub Z₂ with hKdef
    have hBcoord : B = A ⊓ Subgroup.centralizer
        ((Subgroup.zpowers x : Subgroup (MulAut W)) : Set (MulAut W)) ⊓ stabSub Z₁ ⊓
          stabSub Z₂ := by
      rw [hBdef, hLx]
    obtain ⟨hBp, hBc, hKy⟩ := s168e3_cyc3_coord (B := B) (K := K) hW hEA hEc hE3 hxE
      hy₂E hy₂ hfpf hfix₂ hcom₂ hZ₁ hZ₂ hZtop hBcoord hKdef
    have hy₂3 : y₂ ^ 3 = 1 := hE3 y₂ hy₂E
    have hKc : IsCyclicOrd ↥K 3 := by
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have horder : orderOf y₂ = 3 := orderOf_eq_prime hy₂3 hy₂
      have hKcard : Nat.card ↥K = 3 := by rw [hKy, Nat.card_zpowers, horder]
      exact ⟨isCyclic_of_prime_card hKcard, hKcard⟩
    have hKW : commSub ⊤ K = Z₁ := by rw [hKy, hcom₂]
    have hKt : ⁅K, Subgroup.zpowers t⁆ ≠ ⊥ := by
      rw [hKy]
      exact s168e3_cyc3_not_commute hW hEc hE3 hxE hy₂E hfpf hinv hcom₂ hZ₁
    have hrk : rk ↥Z₁ = 2 := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      unfold rk
      rw [hZ₁, show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact padicValNat.prime_pow 2
    obtain ⟨hconc, hcnt⟩ := s168e3_cyc_conc (p := 3) (d := 2) (Or.inl ⟨rfl, rfl⟩) hZ hZtop
      hrk hLn hperm hswap hBdef hKdef hBp hBc hKc hKW hKt
    refine Or.inr ⟨K, hconc, hKc, ?_, hcnt, ?_⟩
    · rw [hKW]; exact hrk
    · intro r hr hr2 hr3
      have hr5 : 5 ≤ r := hr.five_le_of_ne_two_of_ne_three hr2 hr3
      exact s168e3_pRank_lt_two_of_rk_le_four hW (d := 4) le_rfl hcard hr hr5 A
  · exact Or.inl (Or.inr (s168e3_kernel_of_cube Nat.prime_three A h27
      (s168e3_cyc3_fix hW hEA hEc hE3 hxE hy₁E hy₂E hy₁ hy₂ hLx hLn hfpf hfix₁ hfix₂
        hcom₁ hcom₂ hZ₁ hZ₂ hZ hZtop hperm)))

end ThreeFour

section SevenSix

variable {W : Type} [CommGroup W]

theorem s168e3_z7_six_dichotomy [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    (hcard : Nat.card W = 2 ^ 6) {A L : Subgroup (MulAut W)} {t : MulAut W} (hLA : L ≤ A)
    (hLn : ∀ g ∈ A, L.map (MulAut.conj g).toMonoidHom = L) (hL : IsElemAbelianOfRank 7 1 ↥L)
    (hWL : commSub ⊤ L = ⊤) (hind : IsIndivisible A)
    (hO2 : ∀ P : Subgroup (MulAut W), P ≤ A → (P.subgroupOf A).Normal → IsPGroup 2 ↥P → P = ⊥)
    (ht : t ∈ A) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1)
    (htr : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3) (hW' : Conc4_136W A t L) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hqm : 2 ≤ CFSG.Open.pRank q A) :
    S168e3Tool A q ∨ ∃ K : Subgroup (MulAut W), Conc4_136W A t K ∧ IsCyclicOrd ↥K 7 ∧
      rk ↥(commSub ⊤ K) = 3 ∧
      Set.ncard {X : Subgroup (MulAut W) | ∃ φ ∈ A, X = K.map (MulAut.conj φ).toMonoidHom} = 2 ∧
      ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ 7 → CFSG.Open.pRank r A < 2 := by
  obtain ⟨x, hLx, hxo⟩ := s168e3_cyc_gen (by norm_num : Nat.Prime 7) hL
  have hLcard : Nat.card ↥L = 7 := by rw [hLx, Nat.card_zpowers, hxo]
  have h133 := s16h_conc4_133_of_prime_card (by norm_num : Nat.Prime 7) hLcard hW'
  obtain ⟨p', hp', -, hne, -⟩ := h133
  have hinv : t * x * t⁻¹ = x⁻¹ :=
    s168e3_cyc_inv (by norm_num : Nat.Prime 7) hLx hxo ht ht2 hLn hne
  have hfpf : ∀ w : W, x w = w → w = 1 :=
    s168e3_cyc_fpf hW hLx (by rw [hxo]; decide) hWL
  exact Or.inr (s168e3_cyc7_main hW hcard hLx hxo hLn hfpf ht hinv hq hq2 hqm)

end SevenSix

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
