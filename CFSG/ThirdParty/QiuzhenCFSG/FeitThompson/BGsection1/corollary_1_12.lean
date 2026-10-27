module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.theorem_1_13

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

public section

/-
**Kind**: Theorem
**Note**: Corollary 1.12
**Stmt**:
Let $p$ be an odd prime.
Let $G$ be a $p$-group.
Let $E$ be an elementary abelian subgroup of $G$.
Let $A$ be a $p'$-group of operators on $G$.
If $A$ fixes every element of order $p$ in $C_G(E)$, then $A$ acts trivially on $G$.
-/

public theorem CFSG.corollary_1_12 {G A : Type*} [Group G] [Finite G] [Group A] [Finite A]
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2) [Fact (IsPGroup p G)]
    (E : Subgroup G) (hE : ∃ _ : Fact (IsPGroup p (↥E)), IsElementaryAbelian (p := p) (↥E))
    [MulDistribMulAction A G] (hcoprime : Nat.Coprime (Nat.card A) (Nat.card G))
    (hfix : ∀ g : G, g ∈ Subgroup.centralizer (E : Set G) → orderOf g = p → ∀ a : A, a • g = g) :
    ActsTrivially (A := A) (G := G) := by
  let C : Subgroup G := fixedPointSubgroup A G
  let D : Subgroup G := Subgroup.centralizer (C : Set G)
  obtain ⟨_, hElemE⟩ := hE
  haveI : IsElementaryAbelian p (↥E) := hElemE
  have hEpows : ∀ x : E, x ^ p = 1 := by
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p (↥E))
  have hEcent : E ≤ Subgroup.centralizer (E : Set G) := by
    simpa using (Subgroup.le_centralizer (H := E))
  have hE_le_C : E ≤ C := by
    intro x hx
    change x ∈ fixedPointSubgroup A G
    rw [FixedPoints.mem_subgroup]
    intro a
    by_cases hx1 : x = 1
    · simp [hx1]
    · have hxpow : (⟨x, hx⟩ : E) ^ p = 1 := hEpows ⟨x, hx⟩
      have hxordE : orderOf (⟨x, hx⟩ : E) = p := by
        apply orderOf_eq_prime hxpow
        intro hxsub
        exact hx1 (by simpa using congrArg Subtype.val hxsub)
      have hxord : orderOf x = p := by
        simpa [Subgroup.orderOf_coe] using hxordE
      exact hfix x (hEcent hx) hxord a
  have hD_le_centE : D ≤ Subgroup.centralizer (E : Set G) := by
    exact Subgroup.centralizer_le (show (E : Set G) ⊆ (C : Set G) from hE_le_C)
  have hDinv : IsInvariant A G D := by
    refine ⟨?_⟩
    intro a g
    constructor
    · intro hg
      change g ∈ Subgroup.centralizer (C : Set G) at hg
      rw [Subgroup.mem_centralizer_iff] at hg ⊢
      intro c hc
      have hcfix : a • c = c := by
        have : ∀ b : A, b • c = c := by
          simpa [C, FixedPoints.mem_subgroup] using hc
        exact this a
      have hcg : c * g = g * c := hg c hc
      have hsmul := congrArg (fun t : G => a • t) hcg
      simpa [smul_mul_assoc, hcfix] using hsmul
    · intro hg
      change a • g ∈ Subgroup.centralizer (C : Set G) at hg
      change g ∈ Subgroup.centralizer (C : Set G)
      rw [Subgroup.mem_centralizer_iff] at hg ⊢
      intro c hc
      have hcfix : a⁻¹ • c = c := by
        have : ∀ b : A, b • c = c := by
          simpa [C, FixedPoints.mem_subgroup] using hc
        exact this a⁻¹
      have hsmul := congrArg (fun t : G => a⁻¹ • t) (hg c hc)
      simpa [smul_mul_assoc, hcfix] using hsmul
  letI : IsInvariant A G D := hDinv
  letI : Fact (IsPGroup p D) := ⟨(Fact.out : IsPGroup p G).to_subgroup D⟩
  have hΩD : ActsTriviallyOnSubgroup (A := A) (G := D) (omega₁ (G := D) (p := p)) := by
    have hΩD_le : omega₁ (G := D) (p := p) ≤ fixedPointSubgroup A D := by
      rw [omega₁, omega]
      refine (Subgroup.closure_le (K := fixedPointSubgroup A D)).2 ?_
      intro x hx
      change x ∈ fixedPointSubgroup A D
      rw [FixedPoints.mem_subgroup]
      intro a
      apply Subtype.ext
      change a • (x : G) = x
      change x ^ (p ^ 1) = 1 at hx
      have hxpow : x ^ p = 1 := by simpa [pow_one] using hx
      by_cases hx1 : x = 1
      · simp [hx1]
      · have hxordD : orderOf x = p := orderOf_eq_prime hxpow hx1
        have hxord : orderOf (x : G) = p := by
          simpa [Subgroup.orderOf_coe] using hxordD
        exact hfix (x : G) (hD_le_centE x.2) hxord a
    intro a x hx
    exact hΩD_le hx a
  have hDcop : Nat.Coprime (Nat.card A) (Nat.card D) :=
    hcoprime.of_dvd_right (Subgroup.card_subgroup_dvd_card D)
  have htrivD : ActsTrivially (A := A) (G := D) :=
    theorem_1_11 (G := D) (A := A) hpodd hDcop hΩD
  have hD_le_C : D ≤ C := by
    intro x hx
    change x ∈ fixedPointSubgroup A G
    rw [FixedPoints.mem_subgroup]
    intro a
    exact congrArg Subtype.val (htrivD a ⟨x, hx⟩)
  have hnil : Group.IsNilpotent G := (Fact.out : IsPGroup p G).isNilpotent
  exact proposition_1_10 (G := G) (A := A) hnil hcoprime hD_le_C


end
