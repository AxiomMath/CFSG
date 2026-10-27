module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section1
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallDefs

import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Linear characters in the Brauer--Suzuki--Wall configuration

This is the first character-theoretic step of `refs/bender-bsw.tex`, lines
104--110.  When `4 < |K|`, each of the two fibers of evaluation at the
distinguished involution `t` contains a character not fixed by the inverting
involution `s`.

The existence theorem is stated using homomorphisms `K →* ℂˣ` and the stable
condition `χ ^ 2 ≠ 1`.  The final theorem converts that condition to the exact
`conjChar` inequality used by index-two induction, without putting a fragile
normalization proof in the existence statement.
-/

namespace CFSG.GorensteinWalter

open BenderGlauberman
open Theory.Character

noncomputable section

universe u

/-- The identity and `t` are the only elements of `K` whose square is one. -/
private theorem BrauerSuzukiWallHypotheses.eq_one_or_t_of_sq_eq_one
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) (x : h.K) (hx : x ^ 2 = 1) :
    x = 1 ∨ x = ⟨h.t, h.t_mem_K⟩ := by
  classical
  let Z : Subgroup G := Subgroup.zpowers h.t
  have htOrder : orderOf h.t = 2 :=
    orderOf_eq_prime h.t_involution.2 h.t_involution.1
  have hZcard : Nat.card Z = 2 := by
    simp [Z, Nat.card_zpowers, htOrder]
  have htZ : h.t ∈ Z := Subgroup.mem_zpowers h.t
  have htZne : (⟨h.t, htZ⟩ : Z) ≠ 1 := by
    intro heq
    exact h.t_involution.1 (congrArg Subtype.val heq)
  have hZeq : ∀ z : Z, z = 1 ∨ z = ⟨h.t, htZ⟩ := by
    intro z
    by_cases hz : z = 1
    · exact Or.inl hz
    · rcases (Nat.card_eq_two_iff' (1 : Z)).mp hZcard with
        ⟨z0, _hz0ne, hz0uniq⟩
      exact Or.inr
        ((hz0uniq z hz).trans (hz0uniq ⟨h.t, htZ⟩ htZne).symm)
  have hxG2 : (x : G) * (x : G) = 1 := by
    simpa [pow_two] using congrArg Subtype.val hx
  have hxInv : (x : G)⁻¹ = (x : G) :=
    inv_eq_of_mul_eq_one_right hxG2
  have hsfix : h.s * (x : G) * h.s⁻¹ = (x : G) := by
    rw [h.s_inverts_K (x : G) x.2, hxInv]
  have hxcent : (x : G) ∈ Subgroup.centralizer ({h.s} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzs : z = h.s := by simpa using hz
    rw [hzs]
    have hcomm := congrArg (fun q : G => q * h.s) hsfix
    simpa [mul_assoc] using hcomm
  have hxZ : (x : G) ∈ Z := by
    have hxInf :
        (x : G) ∈ h.K ⊓ Subgroup.centralizer ({h.s} : Set G) :=
      ⟨x.2, hxcent⟩
    rw [h.fixed_subgroup_eq] at hxInf
    exact hxInf
  rcases hZeq ⟨(x : G), hxZ⟩ with hx1 | hxt
  · left
    apply Subtype.ext
    exact congrArg (fun z : Z => (z : G)) hx1
  · right
    apply Subtype.ext
    exact congrArg (fun z : Z => (z : G)) hxt

/-- If `4 < |K|`, there are linear characters `ρ, σ` of `K`, not of order
dividing two, with `ρ(t) = 1` and `σ(t) = -1` respectively.  Since `s` acts
on `K` by inversion, `χ ^ 2 ≠ 1` is the proof-independent form of saying
that `χ` is not fixed by `s`. -/
public theorem BrauerSuzukiWallHypotheses.exists_linearCharacters_of_four_lt_card_K
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : 4 < Nat.card h.K) :
    ∃ ρ σ : h.K →* ℂˣ,
      IsLinearCharacter (LambdaChar ρ) ∧
      IsLinearCharacter (LambdaChar σ) ∧
      LambdaChar ρ ⟨h.t, h.t_mem_K⟩ = 1 ∧
      LambdaChar σ ⟨h.t, h.t_mem_K⟩ = -1 ∧
      ρ ^ 2 ≠ 1 ∧ σ ^ 2 ≠ 1 := by
  classical
  let : Fintype h.K := Fintype.ofFinite h.K
  let : IsMulCommutative h.K := h.K_commutative
  let : CommGroup h.K := IsMulCommutative.instCommGroup
  let : Fintype (h.K →* ℂˣ) := instFintypeMonoidHomUnits
  let tK : h.K := ⟨h.t, h.t_mem_K⟩
  let positive := Finset.univ.filter
    (fun χ : h.K →* ℂˣ => ((χ tK : ℂˣ) : ℂ) = 1)
  let negative := Finset.univ.filter
    (fun χ : h.K →* ℂˣ => ((χ tK : ℂˣ) : ℂ) = -1)
  let fixed := Finset.univ.filter (fun χ : h.K →* ℂˣ => χ ^ 2 = 1)
  have htK2 : tK ^ 2 = 1 := by
    apply Subtype.ext
    exact h.t_involution.2
  have htKne : tK ≠ 1 := by
    intro heq
    exact h.t_involution.1 (congrArg Subtype.val heq)
  have hevalSq (χ : h.K →* ℂˣ) : ((χ tK : ℂˣ) : ℂ) ^ 2 = 1 := by
    have hsq : (χ tK) ^ 2 = 1 := by
      calc
        (χ tK) ^ 2 = χ (tK ^ 2) := by rw [map_pow]
        _ = 1 := by rw [htK2]; simp
    exact congrArg (fun z : ℂˣ => (z : ℂ)) hsq
  obtain ⟨χneg, hχnegUnit⟩ :=
    CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity h.K ℂ htKne
  have hχneg : ((χneg tK : ℂˣ) : ℂ) = -1 := by
    rcases sq_eq_one_iff.mp (hevalSq χneg) with h1 | hm1
    · exact False.elim (hχnegUnit (Units.ext h1))
    · exact hm1
  have hnegativePositive : negative.card = positive.card := by
    refine Finset.card_bij (fun χ _ => χneg * χ) ?_ ?_ ?_
    · intro χ hχ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        negative, positive] at hχ ⊢
      simp [hχ, hχneg]
    · intro χ₁ _hχ₁ χ₂ _hχ₂ heq
      exact mul_left_cancel heq
    · intro χ hχ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        positive] at hχ
      refine ⟨χneg⁻¹ * χ, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          negative]
        simp [hχ, hχneg]
      · simp
  have hpartition : Finset.univ = positive ∪ negative := by
    ext χ
    simp only [Finset.mem_univ, true_iff, Finset.mem_union,
      Finset.mem_filter, true_and, positive, negative]
    exact sq_eq_one_iff.mp (hevalSq χ)
  have hdisjoint : Disjoint positive negative := by
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb hab
    have ha1 : ((a tK : ℂˣ) : ℂ) = 1 := (Finset.mem_filter.mp ha).2
    have hb1 : ((b tK : ℂˣ) : ℂ) = -1 :=
      (Finset.mem_filter.mp hb).2
    have hcontra : (1 : ℂ) = -1 :=
      ha1.symm.trans (by simpa [hab] using hb1)
    norm_num at hcontra
  have hsum :
      positive.card + negative.card = Fintype.card (h.K →* ℂˣ) := by
    rw [← Finset.card_union_of_disjoint hdisjoint, ← hpartition]
    simp
  have hdualCard : Fintype.card (h.K →* ℂˣ) = Nat.card h.K := by
    rw [Fintype.card_eq_nat_card]
    exact CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity h.K ℂ
  have hpositiveCard : positive.card * 2 = Nat.card h.K := by
    rw [hnegativePositive] at hsum
    rw [hdualCard] at hsum
    omega
  have hpositiveGt : 2 < positive.card := by omega
  have hnegativeGt : 2 < negative.card := by omega
  let pair : Finset h.K := {1, tK}
  let dualEquiv : (h.K →* ℂˣ) ≃* h.K :=
    Classical.choice
      (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity h.K ℂ)
  have hmaps :
      Set.MapsTo dualEquiv (fixed : Set (h.K →* ℂˣ)) (pair : Set h.K) := by
    intro χ hχ
    have hχsq : χ ^ 2 = 1 := (Finset.mem_filter.mp hχ).2
    have heχsq : (dualEquiv χ) ^ 2 = 1 := by
      rw [← map_pow dualEquiv χ 2, hχsq, map_one]
    rcases h.eq_one_or_t_of_sq_eq_one (dualEquiv χ) heχsq with he1 | het
    · simp [pair, he1]
    · simp [pair, tK, het]
  have hfixedPair : fixed.card ≤ pair.card :=
    Finset.card_le_card_of_injOn
      dualEquiv hmaps dualEquiv.injective.injOn
  have hpairCard : pair.card = 2 := by
    simp [pair, Ne.symm htKne]
  have hfixedLe : fixed.card ≤ 2 := by
    simpa [hpairCard] using hfixedPair
  obtain ⟨ρ, hρPositive, hρFixed⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card
      (lt_of_le_of_lt hfixedLe hpositiveGt)
  obtain ⟨σ, hσNegative, hσFixed⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card
      (lt_of_le_of_lt hfixedLe hnegativeGt)
  have hρt : LambdaChar ρ tK = 1 :=
    (Finset.mem_filter.mp hρPositive).2
  have hσt : LambdaChar σ tK = -1 :=
    (Finset.mem_filter.mp hσNegative).2
  have hρsq : ρ ^ 2 ≠ 1 := by
    intro hsq
    exact hρFixed (by simp [fixed, hsq])
  have hσsq : σ ^ 2 ≠ 1 := by
    intro hsq
    exact hσFixed (by simp [fixed, hsq])
  refine ⟨ρ, σ, ?_, ?_, hρt, hσt, hρsq, hσsq⟩
  · exact isLinearCharacter_of_hom ρ
  · exact isLinearCharacter_of_hom σ

/-- Conjugation by the distinguished involution preserves `K`. -/
public theorem BrauerSuzukiWallHypotheses.s_normalizes_K
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) :
    ∀ x : h.K, h.s * (x : G) * h.s⁻¹ ∈ h.K := by
  intro x
  rw [h.s_inverts_K (x : G) x.2]
  exact h.K.inv_mem x.2

/-- A linear character whose square is nontrivial is not fixed by the
`conjChar` action of `s`.  This is the exact non-fixed hypothesis consumed by
the index-two induction lemmas. -/
public theorem BrauerSuzukiWallHypotheses.conjChar_ne_of_sq_ne_one
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (χ : h.K →* ℂˣ) (hχsq : χ ^ 2 ≠ 1) :
    conjChar h.K h.s_normalizes_K (LambdaChar χ) ≠ LambdaChar χ := by
  intro hfix
  apply hχsq
  apply MonoidHom.ext
  intro x
  have hconj :
      conjMonoidHom h.K h.s h.s_normalizes_K x = x⁻¹ := by
    apply Subtype.ext
    exact h.s_inverts_K (x : G) x.2
  have hval := congrFun hfix x
  change ((χ (conjMonoidHom h.K h.s h.s_normalizes_K x) : ℂˣ) : ℂ) =
    ((χ x : ℂˣ) : ℂ) at hval
  rw [hconj] at hval
  have hunit : χ x⁻¹ = χ x := Units.ext hval
  have hxmul : χ x * χ x = 1 := by
    nth_rw 1 [← hunit]
    rw [map_inv]
    exact inv_mul_cancel (χ x)
  simpa [pow_two] using hxmul

end

end CFSG.GorensteinWalter
