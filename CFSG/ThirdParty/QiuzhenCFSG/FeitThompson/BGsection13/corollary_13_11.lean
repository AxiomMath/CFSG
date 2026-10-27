module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection13.theorem_13_10
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Conjugacy
import Mathlib.Data.Finset.NatDivisors
import Mathlib.GroupTheory.Schreier

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-! # Corollary 13 11 from BG Section 13 -/

section Section13

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]
private theorem CFSG.section13_corollary_13_11_tau2_empty
    {M E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hE₃ne : E₃ ≠ ⊥)
    (hnotRegular : ¬ section13ActsRegularlyOn E₃ (section10Msigma M)) :
    section12Tau2Primes M = ∅ := by
  classical
  have hprime :
      section13ActsPrimeManner E₃ (section10Msigma M) :=
    corollary_13_3_b (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE
  have hCne : subgroupCentralizerIn (section10Msigma M) E₃ ≠ ⊥ :=
    section13_centralizer_ne_bot_of_prime_manner_not_regular
      (G := G) hprime hnotRegular
  rcases Subgroup.ne_bot_iff_exists_ne_one.mp hCne with ⟨y, hyne⟩
  have hyC : (y : G) ∈ subgroupCentralizerIn (section10Msigma M) E₃ := y.property
  have hyneG : (y : G) ≠ 1 := by
    intro hy
    exact hyne (Subtype.ext hy)
  rcases Subgroup.ne_bot_iff_exists_ne_one.mp hE₃ne with ⟨z, hzne⟩
  have hzE₃ : (z : G) ∈ E₃ := z.property
  have hzneG : (z : G) ≠ 1 := by
    intro hz
    exact hzne (Subtype.ext hz)
  ext q
  constructor
  · intro hqτ2
    rcases section12_exists_rankTwo_in_E_of_tau2
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) hM hE hqτ2 with
      ⟨A, hA⟩
    have hz_bot :
        elementCentralizerIn (section10Msigma M) (z : G) = ⊥ :=
      corollary_12_6_d
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) (A := A) (p := q)
        hM hE hqτ2 hA (z : G) hzE₃ hzneG
    have hyCz : (y : G) ∈ elementCentralizerIn (section10Msigma M) (z : G) := by
      refine ⟨hyC.1, ?_⟩
      change (y : G) ∈ Subgroup.centralizer ({(z : G)} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      rw [Set.mem_singleton_iff] at ht
      subst t
      exact Subgroup.mem_centralizer_iff.mp hyC.2 (z : G) z.property
    have hybot : (y : G) ∈ (⊥ : Subgroup G) := by
      simpa [hz_bot] using hyCz
    exact False.elim <| hyneG (by simpa using hybot)
  · intro hqempty
    cases hqempty

private theorem CFSG.section13_corollary_13_11_E1_not_regular_on_E3
    {M E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hE₁ne : E₁ ≠ ⊥)
    (hE₃ne : E₃ ≠ ⊥)
    (hnotRegular : ¬ section13ActsRegularlyOn E₃ (section10Msigma M)) :
    ¬ section13ActsRegularlyOn E₁ E₃ := by
  classical
  intro hregular
  rcases section13_exists_prime_order_subgroup_le_of_ne_bot
      (G := G) (P := E₁) hE₁ne with
    ⟨p, P, hP_le_E₁, hPcard⟩
  have hP : P ∈ section10PrimeOrderSubgroupsIn p E₁ := by
    simpa [section10PrimeOrderSubgroupsIn] using ⟨hP_le_E₁, hPcard⟩
  have hP_cent_E₃ : P ≤ Subgroup.centralizer (E₃ : Set G) := by
    by_contra hnotCent
    exact hnotRegular
      (theorem_13_10_b (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (P := P) (p := p)
        hM hE hP hnotCent)
  have hPne : P ≠ ⊥ := section13_ne_bot_of_prime_order (G := G) hPcard
  rcases Subgroup.ne_bot_iff_exists_ne_one.mp hPne with ⟨a, hane⟩
  have haP : (a : G) ∈ P := a.property
  have haE₁ : (a : G) ∈ E₁ := hP_le_E₁ haP
  have haneG : (a : G) ≠ 1 := by
    intro ha
    exact hane (Subtype.ext ha)
  have hEa_bot : elementCentralizerIn E₃ (a : G) = ⊥ :=
    hregular.2 (a : G) haE₁ haneG
  have hE₃_le_Ca : E₃ ≤ elementCentralizerIn E₃ (a : G) := by
    intro z hz
    refine ⟨hz, ?_⟩
    change z ∈ Subgroup.centralizer ({(a : G)} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    subst t
    exact (Subgroup.mem_centralizer_iff.mp (hP_cent_E₃ haP) z hz).symm
  exact hE₃ne (le_bot_iff.mp (by simpa [hEa_bot] using hE₃_le_Ca))

/-- Corollary 13.11(a): if `E₃ ≠ 1` and `E₃` does not act regularly
on `M_σ`, then `E₁ ≠ 1`. -/
public theorem CFSG.corollary_13_11_a
    {M E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hE₃ne : E₃ ≠ ⊥)
    (hnotRegular : ¬ section13ActsRegularlyOn E₃ (section10Msigma M)) :
    E₁ ≠ ⊥ := by
  have hτ2empty : section12Tau2Primes M = ∅ :=
    section13_corollary_13_11_tau2_empty
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) hM hE hE₃ne hnotRegular
  have hE₂bot : E₂ = ⊥ :=
    section13_E2_eq_bot_of_tau2_empty
      (G := G) (M := M) (E₁₂ := E₁₂) (E₂ := E₂) hE.2.2.2.1 hτ2empty
  exact lemma_12_1_c (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
    (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE hE₂bot

/-- Corollary 13.11(b): if `E₃ ≠ 1` and `E₃` does not act regularly
on `M_σ`, then `E = E₁E₃`. -/
public theorem CFSG.corollary_13_11_b
    {M E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hE₃ne : E₃ ≠ ⊥)
    (hnotRegular : ¬ section13ActsRegularlyOn E₃ (section10Msigma M)) :
    E = E₁ ⊔ E₃ := by
  have hτ2empty : section12Tau2Primes M = ∅ :=
    section13_corollary_13_11_tau2_empty
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) hM hE hE₃ne hnotRegular
  have hE₂bot : E₂ = ⊥ :=
    section13_E2_eq_bot_of_tau2_empty
      (G := G) (M := M) (E₁₂ := E₁₂) (E₂ := E₂) hE.2.2.2.1 hτ2empty
  have hEfull : E = E₁ ⊔ E₂ ⊔ E₃ :=
    (lemma_12_1_e (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE).1
  calc
    E = E₁ ⊔ E₂ ⊔ E₃ := hEfull
    _ = E₁ ⊔ E₃ := by
      rw [hE₂bot]
      simp

/-- Corollary 13.11(c): if `E₃ ≠ 1` and `E₃` does not act regularly
on `M_σ`, then `E` acts in a prime manner on `M_σ`. -/
public theorem CFSG.corollary_13_11_c
    {M E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hE₃ne : E₃ ≠ ⊥)
    (hnotRegular : ¬ section13ActsRegularlyOn E₃ (section10Msigma M)) :
    section13ActsPrimeManner E (section10Msigma M) := by
  have hE₁ne : E₁ ≠ ⊥ :=
    corollary_13_11_a (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE hE₃ne hnotRegular
  have hE_eq : E = E₁ ⊔ E₃ :=
    corollary_13_11_b (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE hE₃ne hnotRegular
  have hE₁_not_regular : ¬ section13ActsRegularlyOn E₁ E₃ :=
    section13_corollary_13_11_E1_not_regular_on_E3
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) hM hE hE₁ne hE₃ne hnotRegular
  have hjoin_prime :
      section13ActsPrimeManner (E₁ ⊔ E₃) (section10Msigma M) :=
    lemma_13_7 (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE hE₁ne hE₁_not_regular
  simpa [hE_eq] using hjoin_prime

private theorem CFSG.section13_corollary_13_11_normalIn_of_prime_le_E1
    {M E E₁₂ E₁ E₂ E₃ X : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hE_eq : E = E₁ ⊔ E₃)
    (hnotRegular : ¬ section13ActsRegularlyOn E₃ (section10Msigma M))
    (hX : X ∈ section10PrimeOrderSubgroupsIn p E₁) :
    section10NormalIn X E := by
  classical
  have hE₁cyc : IsCyclic E₁ :=
    (lemma_12_1_d (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE).1
  have hNormE₁_le_NormX :
      Subgroup.normalizer (E₁ : Set G) ≤ Subgroup.normalizer (X : Set G) := by
    letI : IsCyclic E₁ := hE₁cyc
    have hXchar : (X.subgroupOf E₁).Characteristic :=
      section12_subgroup_characteristic_of_cyclic (X.subgroupOf E₁)
    letI : (X.subgroupOf E₁).Characteristic := hXchar
    have hmap : (X.subgroupOf E₁).map E₁.subtype = X :=
      Subgroup.map_subgroupOf_eq_of_le hX.1
    simpa [hmap] using
      (section8_normalizer_map_subtype_le_of_characteristic
        (G := G) (H := E₁) (K := X.subgroupOf E₁))
  have hE₁_norm_X : E₁ ≤ Subgroup.normalizer (X : Set G) :=
    (Subgroup.le_normalizer (H := E₁)).trans hNormE₁_le_NormX
  have hX_cent_E₃ : X ≤ Subgroup.centralizer (E₃ : Set G) := by
    by_contra hnotCent
    exact hnotRegular
      (theorem_13_10_b (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (P := X) (p := p)
        hM hE hX hnotCent)
  have hE₃_cent_X : E₃ ≤ Subgroup.centralizer (X : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp (hX_cent_E₃ hx) z hz).symm
  have hE₃_norm_X : E₃ ≤ Subgroup.normalizer (X : Set G) :=
    hE₃_cent_X.trans (centralizer_le_normalizer X)
  have hE_norm_X : E ≤ Subgroup.normalizer (X : Set G) := by
    rw [hE_eq]
    exact sup_le hE₁_norm_X hE₃_norm_X
  have hXE : X ≤ E := hX.1.trans (hE.2.2.1.1.trans hE.2.1.1)
  exact ⟨hXE, (Subgroup.normal_subgroupOf_iff_le_normalizer hXE).2 hE_norm_X⟩

private theorem CFSG.section13_corollary_13_11_normalIn_of_prime_le_E3
    {M E E₁₂ E₁ E₂ E₃ X : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hX : X ∈ section10PrimeOrderSubgroupsIn p E₃) :
    section10NormalIn X E := by
  classical
  have hE₃cyc : IsCyclic E₃ :=
    (lemma_12_1_d (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE).2
  have hNormE₃_le_NormX :
      Subgroup.normalizer (E₃ : Set G) ≤ Subgroup.normalizer (X : Set G) := by
    letI : IsCyclic E₃ := hE₃cyc
    have hXchar : (X.subgroupOf E₃).Characteristic :=
      section12_subgroup_characteristic_of_cyclic (X.subgroupOf E₃)
    letI : (X.subgroupOf E₃).Characteristic := hXchar
    have hmap : (X.subgroupOf E₃).map E₃.subtype = X :=
      Subgroup.map_subgroupOf_eq_of_le hX.1
    simpa [hmap] using
      (section8_normalizer_map_subtype_le_of_characteristic
        (G := G) (H := E₃) (K := X.subgroupOf E₃))
  have hE₃norm : section10NormalIn E₃ E :=
    (lemma_12_1_b (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE).2
  have hE_norm_E₃ : E ≤ Subgroup.normalizer (E₃ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hE₃norm.1).1 hE₃norm.2
  have hE_norm_X : E ≤ Subgroup.normalizer (X : Set G) :=
    hE_norm_E₃.trans hNormE₃_le_NormX
  have hXE : X ≤ E := hX.1.trans hE₃norm.1
  exact ⟨hXE, (Subgroup.normal_subgroupOf_iff_le_normalizer hXE).2 hE_norm_X⟩

omit [IsMinCE G] in
private theorem CFSG.section13_corollary_13_11_normalIn_of_conjBy
    {E X : Subgroup G} {g : G}
    (hgE : g ∈ E) (hXg : section10NormalIn (X.conjBy g) E) :
    section10NormalIn X E := by
  classical
  have hE_norm_Xg : E ≤ Subgroup.normalizer (X.conjBy g : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXg.1).1 hXg.2
  have hg_inv_norm : g⁻¹ ∈ Subgroup.normalizer (X.conjBy g : Set G) :=
    hE_norm_Xg (E.inv_mem hgE)
  have hfix : (X.conjBy g).conjBy g⁻¹ = X.conjBy g :=
    section13_conjBy_eq_of_mem_normalizer (G := G) (H := X.conjBy g)
      hg_inv_norm
  have hback : (X.conjBy g).conjBy g⁻¹ = X := by
    calc
      (X.conjBy g).conjBy g⁻¹ = X.conjBy (g⁻¹ * g) :=
        section8_conjBy_conjBy (G := G) X g g⁻¹
      _ = X.conjBy (1 : G) := by simp
      _ = X := section8_conjBy_one (G := G) X
  have hX_eq : X = X.conjBy g := by
    rw [hfix] at hback
    exact hback.symm
  rw [hX_eq]
  exact hXg

/-- Corollary 13.11(d): if `E₃ ≠ 1` and `E₃` does not act regularly
on `M_σ`, then every `X ∈ 𝓔^1(E)` is normal in `E`. -/
public theorem CFSG.corollary_13_11_d
    {M E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hE₃ne : E₃ ≠ ⊥)
    (hnotRegular : ¬ section13ActsRegularlyOn E₃ (section10Msigma M)) :
    ∀ X : Subgroup G, X ∈ section12PrimeOrderSubgroups E → section10NormalIn X E := by
  classical
  intro X hX
  have hE_eq : E = E₁ ⊔ E₃ :=
    corollary_13_11_b (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE hE₃ne hnotRegular
  have hX_join : X ∈ section12PrimeOrderSubgroups (E₁ ⊔ E₃) := by
    simpa [hE_eq] using hX
  rcases (by simpa [section12PrimeOrderSubgroups] using hX) with
    ⟨_hXE, p, hXcard⟩
  rcases section13_lemma_13_7_prime_conj_le_E1_or_E3
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (X := X) hM hE hX_join with
    ⟨g, hgJ, hXg_factor⟩
  have hgE : g ∈ E := by
    simpa [hE_eq] using hgJ
  have hXgcard : Nat.card (X.conjBy g) = p.val := by
    rw [section13_card_conjBy (G := G) X g, hXcard]
  rcases hXg_factor with hXgE₁ | hXgE₃
  · have hXg_prime : X.conjBy g ∈ section10PrimeOrderSubgroupsIn p E₁ := by
      simpa [section10PrimeOrderSubgroupsIn] using ⟨hXgE₁, hXgcard⟩
    exact
      section13_corollary_13_11_normalIn_of_conjBy
        (G := G) (E := E) (X := X) (g := g) hgE <|
        section13_corollary_13_11_normalIn_of_prime_le_E1
          (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
          (E₂ := E₂) (E₃ := E₃) hM hE hE_eq hnotRegular hXg_prime
  · have hXg_prime : X.conjBy g ∈ section10PrimeOrderSubgroupsIn p E₃ := by
      simpa [section10PrimeOrderSubgroupsIn] using ⟨hXgE₃, hXgcard⟩
    exact
      section13_corollary_13_11_normalIn_of_conjBy
        (G := G) (E := E) (X := X) (g := g) hgE <|
        section13_corollary_13_11_normalIn_of_prime_le_E3
          (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
          (E₂ := E₂) (E₃ := E₃) hM hE hXg_prime

end Section13
