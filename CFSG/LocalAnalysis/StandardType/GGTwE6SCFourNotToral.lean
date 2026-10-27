module

public import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourTypeW0
import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourRetype
import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourCoroot
import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourCover

public section

namespace CFSG.StandardType.SCFourCover

open scoped commutatorElement

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.E6Descent
  CFSG.RankThree.Classical2 CFSG.StandardType.NoOffTwE6Three CFSG.RankThree.PartOne.KE


theorem not_e6AdToral_of_selfCent_derived
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    {n : ℕ} (hn : 1 ≤ n) (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    (h3 : 3 ∣ 2 ^ n + 1) {X : Subgroup (ModGL Tag.E6 Ω)}
    (hXR : X ≤ TwistedDiag.Rgrp Ω Fr)
    (hX3 : ∀ x ∈ X, x ^ 3 = 1) (hcard : Nat.card X = 3 ^ 4)
    (hSC : ∀ u ∈ ⁅TwistedDiag.Rgrp Ω Fr, TwistedDiag.Rgrp Ω Fr⁆,
      u ^ 3 = 1 → (∀ x ∈ X, x * u = u * x) → u ∈ X) :
    ¬ E6AdToral X := by
  intro htor
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite X := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hcard81 : 81 ≤ Nat.card X := by rw [hcard]; norm_num
  have hLang : E6AdLangToral Fr X := e6AdLangToral_of_toral hn Fr hFr hXR htor
  obtain ⟨g0, hg0, hgn, hX⟩ :=
    exists_typeW0_of_e6AdLangToral hn Fr hFr h3 hX3 hcard81 hLang
  have h30 : (3 : Ω) ≠ 0 := by
    have h2 : (2 : Ω) = 0 := CharP.cast_eq_zero Ω 2
    rw [show (3 : Ω) = 1 by linear_combination h2]
    exact one_ne_zero
  obtain ⟨ζ, -, hζ⟩ := TwistedDiag.exists_cube_root (Ω := Ω) h30
  have hζ3 : ζ ^ 3 = 1 := hζ ▸ pow_orderOf_eq_one ζ
  have h5 : 3 ^ 5 ≤ Nat.card X := by
    refine three_pow_five_le_card_of_conj_torusElt_mem (X := X) (g := g0) hζ fun i => ?_
    set u : ModGL Tag.E6 Ω := g0 * torusElt Tag.E6 Ω i ζ * g0⁻¹
    set v : ModGL Tag.E6 Ω := g0 * weylElt Tag.E6 Ω i 1 * g0⁻¹
    have huR : u ∈ TwistedDiag.Rgrp Ω Fr := by
      simpa [u] using conj_torusElt_mem_Rgrp Fr hFr h3 hg0 hgn hζ3 i
    have hvR : v ∈ TwistedDiag.Rgrp Ω Fr := by
      simpa [v] using conj_weylElt_mem_Rgrp Fr hg0 hgn i
    obtain ⟨hu3, -, htu⟩ := inverts_conj_torusElt (CharP.cast_eq_zero Ω 2) g0 hζ3 i
    have hu3' : u ^ 3 = 1 := by simpa [u] using hu3
    have htu' : v * u * v⁻¹ = u⁻¹ := by simpa [u, v] using htu
    have hu_inv : u⁻¹ = u ^ 2 := by
      apply inv_eq_of_mul_eq_one_right
      rw [show u * u ^ 2 = u ^ 3 by group, hu3']
    have hcommu : u = ⁅v, u⁆ := by
      rw [commutatorElement_def, htu', hu_inv]
      calc
        u = u * 1 := by rw [mul_one]
        _ = u * u ^ 3 := by rw [hu3']
        _ = u ^ 2 * u ^ 2 := by group
    have hu_comm : u ∈ ⁅TwistedDiag.Rgrp Ω Fr, TwistedDiag.Rgrp Ω Fr⁆ := by
      rw [hcommu]
      exact Subgroup.commutator_mem_commutator hvR huR
    have hcent : ∀ x ∈ X, x * u = u * x := by
      intro x hx
      obtain ⟨b, hb3, rfl, -⟩ := exists_rootDiagUnit_of_mem_langTorus (hX x hx) (hX3 x hx)
      simpa [u] using (conj_rootDiagUnit_conj_weylElt g0 hb3 hζ i).1
    exact hSC u hu_comm hu3' hcent
  rw [hcard] at h5
  norm_num at h5

variable {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
  (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) {Ω : Type} [Field Ω] [Algebra K Ω]
  [IsAlgClosure K Ω] (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
  (ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* TwE6Delta.RecipeR K n)

theorem not_e6AdToral_rgrpModel
    (hε : ∀ x : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      MulAut.congr ε x ∈ TwE6Delta.RecipeI K n ↔ x ∈ (RecipeExcLang.twConj K σ).range)
    (h3 : 3 ∣ 2 ^ n + 1) {L' : Type} [Group L'] {ψ : L' →* TwE6Delta.RecipeR K n}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : ∀ a ∈ A, a ^ 3 = 1) (hcard : Nat.card A = 3 ^ 4)
    (hAI : ∀ a ∈ A, ∃ φ ∈ TwE6Delta.RecipeI K n, ∀ l, φ (ψ l) = ψ (a l))
    (hSC : GGTorusSelfCent 3 A) :
    ¬ E6AdToral (rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A)) := by
  intro htor
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := n * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, pow_mul])
  haveI : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have hcardH : Nat.card (rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A)) = 3 ^ 4 := by
    rw [card_rgrpModel hn hK σ hσ Fr hFr ε hε (inducedSub_subset hψ hAI),
      TypeA.card_inducedSub hψ hker hperf fun a ha => (hAI a ha).imp fun _ hφ => hφ.2, hcard]
  haveI : Finite (rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A)) :=
    Nat.finite_of_card_ne_zero (by rw [hcardH]; norm_num)
  have hX3 : ∀ x ∈ rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A), x ^ 3 = 1 := by
    intro x hx
    obtain ⟨hxR, hxA⟩ := (mem_rgrpModel hn hK σ hσ Fr hFr ε).1 hx
    obtain ⟨a, ha, hφ⟩ := TypeA.mem_inducedSub.1 hxA
    have h1 : (⟨x, hxR⟩ : ↥(TwistedDiag.Rgrp Ω Fr)) ^ 3 = 1 :=
      rgrpRecipeAut_injective hn hK σ hσ Fr hFr ε (by
        rw [map_pow, map_one]
        refine TypeA.induced_unique ψ hψ (TypeA.induced_pow ψ hφ 3) fun l => ?_
        rw [hA a ha]
        rfl)
    have h := congrArg Subtype.val h1
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at h
  obtain ⟨g1, hg1, hgn, hX⟩ := exists_typeW0_of_e6AdLangToral hn Fr hFr h3 hX3
    (by rw [hcardH]; norm_num)
    (e6AdLangToral_of_toral hn Fr hFr (rgrpModel_le_Rgrp hn hK σ hσ Fr hFr ε _) htor)
  have h30 : (3 : Ω) ≠ 0 := by
    have h2 : (2 : Ω) = 0 := CharP.cast_eq_zero Ω 2
    rw [show (3 : Ω) = 1 by linear_combination h2]
    exact one_ne_zero
  obtain ⟨ζ, -, hζ⟩ := TwistedDiag.exists_cube_root (Ω := Ω) h30
  have h5 := three_pow_five_le_card_of_conj_torusElt_mem hζ fun i =>
    conj_torusElt_mem_rgrpModel hn hK σ hσ Fr hFr ε hε h3 hψ hker hA hAI hSC hg1 hgn hX hζ i
  rw [hcardH] at h5
  norm_num at h5

theorem three_pow_five_le_card_of_e6AdToral_rgrpModel
    (hε : ∀ x : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      MulAut.congr ε x ∈ TwE6Delta.RecipeI K n ↔ x ∈ (RecipeExcLang.twConj K σ).range)
    (h3 : 3 ∣ 2 ^ n + 1) {L' : Type} [Group L'] [Finite L']
    {ψ : L' →* TwE6Delta.RecipeR K n}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) {A : Subgroup (MulAut L')} (hA : CFSG.Open.IsElemAbelian 3 A)
    (hcard : 3 ^ 4 ≤ Nat.card A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ TwE6Delta.RecipeI K n, ∀ l, φ (ψ l) = ψ (a l))
    (hSC : GGTorusSelfCent 3 A)
    (htor : E6AdToral (rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A))) :
    3 ^ 5 ≤ Nat.card A := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨d, hd⟩ := hA.isPGroup.exists_card_eq
  by_contra h5
  have hd4 : 4 ≤ d := by
    apply (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp
    rwa [hd] at hcard
  have hd5 : d < 5 := by
    apply (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp
    have hlt : Nat.card A < 3 ^ 5 := Nat.lt_of_not_ge h5
    rwa [hd] at hlt
  have h4 : Nat.card A = 3 ^ 4 := by
    rw [hd, show d = 4 by omega]
  exact not_e6AdToral_rgrpModel hn hK σ hσ Fr hFr ε hε h3 hψ hker hperf
    hA.2 h4 hAI hSC htor

end CFSG.StandardType.SCFourCover

end
