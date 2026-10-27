module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Hall.lemma_14_4_2

namespace CFSG
end CFSG
open CFSG

/-!
# Hall Lemma 14.4.3

Source interface for Hall's transfer formula in terms of `d*`.
-/

namespace CFSG.BenderSuzuki
namespace External

open scoped BigOperators

universe u

/-- Hall Lemma 14.4.3: for `h ∈ H`, the transfer of `h` is the `[G:H]`-th power of `h` times a
finite product of diagonal-defect terms attached to the cycles of the coset
permutation.  The finite multiset below records that source double product
without turning it into a non-book data structure. -/
public theorem hall_lemma_14_4_3_transfer_diagonal_defect_formula
    {G A : Type u} [Group G] [Finite G]
    {H : Subgroup G} [H.FiniteIndex] [CommGroup A] (φ : H →* A) :
    ∃ defectTerms : (H → Multiset H),
      ∀ h : H,
        MonoidHom.transfer φ (h : G) =
            (φ h) ^ H.index *
              ((defectTerms h).map (fun y => hallDiagonalDefect (H := H) φ y)).prod ∧
          ∀ y : H, y ∈ defectTerms h →
            ∃ n : ℕ, (y : G) = (h : G) ^ n ∨ IsConj ((h : G) ^ n) ((y : G)⁻¹) := by
  classical
  let defectTerms : H → Multiset H := fun h =>
    let Ω := Quotient (MulAction.orbitRel (Subgroup.zpowers (h : G)) (G ⧸ H))
    letI : Fintype Ω := Fintype.ofFinite Ω
    let m : Ω → ℕ := fun q => Function.minimalPeriod ((h : G) • ·) q.out
    let cycleTerm : Ω → H := fun q =>
      ⟨q.out.out⁻¹ * (h : G) ^ m q * q.out.out,
        QuotientGroup.out_conj_pow_minimalPeriod_mem H (h : G) q.out⟩
    let hPower : Ω → H := fun q => ⟨(h : G) ^ m q, H.pow_mem h.property (m q)⟩
    ((Finset.univ : Finset Ω).val.map hPower) +
      ((Finset.univ : Finset Ω).val.map fun q => (cycleTerm q)⁻¹)
  refine ⟨defectTerms, ?_⟩
  intro h
  let Ω := Quotient (MulAction.orbitRel (Subgroup.zpowers (h : G)) (G ⧸ H))
  letI : Fintype Ω := Fintype.ofFinite Ω
  let m : Ω → ℕ := fun q => Function.minimalPeriod ((h : G) • ·) q.out
  let cycleTerm : Ω → H := fun q =>
    ⟨q.out.out⁻¹ * (h : G) ^ m q * q.out.out,
      QuotientGroup.out_conj_pow_minimalPeriod_mem H (h : G) q.out⟩
  let hPower : Ω → H := fun q => ⟨(h : G) ^ m q, H.pow_mem h.property (m q)⟩
  let cycleInv : Ω → H := fun q => (cycleTerm q)⁻¹
  refine ⟨?_, ?_⟩
  · have hcycle_factor : ∀ q : Ω,
        φ (cycleTerm q) =
          φ (hPower q) * hallDiagonalDefect (H := H) φ (hPower q) *
            hallDiagonalDefect (H := H) φ (cycleInv q) := by
      intro q
      let t : Gˣ := ⟨q.out.out⁻¹, q.out.out, by simp, by simp⟩
      have hconj : IsConj ((hPower q : H) : G) ((cycleTerm q : H) : G) := by
        refine ⟨t, ?_⟩
        change (t : G) * ((hPower q : H) : G) = ((cycleTerm q : H) : G) * (t : G)
        simp [t, hPower, cycleTerm, mul_assoc]
      have hdiag_conj :
          hallDiagonalContribution (H := H) φ ((hPower q : H) : G) =
            hallDiagonalContribution (H := H) φ ((cycleTerm q : H) : G) :=
        (hall_lemma_14_4_2_diagonal_contribution_conjugacy (H := H) φ).1
          ((hPower q : H) : G) ((cycleTerm q : H) : G) hconj
      have hdiag_inv :
          hallDiagonalContribution (H := H) φ (((cycleTerm q : H) : G)⁻¹) =
            (hallDiagonalContribution (H := H) φ ((cycleTerm q : H) : G))⁻¹ :=
        (hall_lemma_14_4_2_diagonal_contribution_conjugacy (H := H) φ).2
          ((cycleTerm q : H) : G)
      have hcycleInv_coe : ((cycleInv q : H) : G) = (((cycleTerm q : H) : G)⁻¹) := rfl
      simp [hallDiagonalDefect, cycleInv, hcycleInv_coe, hdiag_inv, hdiag_conj,
        mul_left_comm, mul_comm]
    have hpower_prod :
        (∏ q : Ω, φ (hPower q)) = (φ h) ^ H.index := by
      rw [Subgroup.index_eq_sum_minimalPeriod H (h : G), ← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_congr rfl ?_
      intro q _
      calc
        φ (hPower q) = φ (h ^ m q) := by
          congr 1
        _ = φ h ^ m q := map_pow φ h (m q)
    have hdefect_prod :
        (((defectTerms h).map (fun y => hallDiagonalDefect (H := H) φ y)).prod) =
          (∏ q : Ω, hallDiagonalDefect (H := H) φ (hPower q)) *
            (∏ q : Ω, hallDiagonalDefect (H := H) φ (cycleInv q)) := by
      change ((((Finset.univ : Finset Ω).val.map hPower +
          (Finset.univ : Finset Ω).val.map cycleInv).map
          (fun y => hallDiagonalDefect (H := H) φ y)).prod) = _
      rw [Multiset.map_add, Multiset.prod_add]
      rw [Multiset.map_map, Multiset.map_map]
      simp only [Function.comp_apply, Finset.prod_map_val]
    have htransfer :
        MonoidHom.transfer φ (h : G) = ∏ q : Ω, φ (cycleTerm q) := by
      simpa [Ω, cycleTerm, m] using
        (MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot
          (ϕ := φ) (H := H) (g := (h : G)))
    rw [htransfer]
    calc
      (∏ q : Ω, φ (cycleTerm q)) =
          ∏ q : Ω,
            (φ (hPower q) * hallDiagonalDefect (H := H) φ (hPower q) *
              hallDiagonalDefect (H := H) φ (cycleInv q)) := by
        refine Finset.prod_congr rfl ?_
        intro q _
        exact hcycle_factor q
      _ = (∏ q : Ω, φ (hPower q)) *
            ((∏ q : Ω, hallDiagonalDefect (H := H) φ (hPower q)) *
              (∏ q : Ω, hallDiagonalDefect (H := H) φ (cycleInv q))) := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
        ac_rfl
      _ = (φ h) ^ H.index *
            ((defectTerms h).map (fun y => hallDiagonalDefect (H := H) φ y)).prod := by
        rw [hpower_prod, hdefect_prod]
  · intro y hy
    change y ∈ ((Finset.univ : Finset Ω).val.map hPower) +
      ((Finset.univ : Finset Ω).val.map cycleInv) at hy
    rw [Multiset.mem_add] at hy
    rcases hy with hy | hy
    · rw [Multiset.mem_map] at hy
      rcases hy with ⟨q, _hq, rfl⟩
      exact ⟨m q, Or.inl rfl⟩
    · rw [Multiset.mem_map] at hy
      rcases hy with ⟨q, _hq, rfl⟩
      refine ⟨m q, Or.inr ?_⟩
      let t : Gˣ := ⟨q.out.out⁻¹, q.out.out, by simp, by simp⟩
      refine ⟨t, ?_⟩
      change (t : G) * (h : G) ^ m q = ((cycleInv q : H) : G)⁻¹ * (t : G)
      simp [t, cycleInv, cycleTerm, mul_assoc]
end External
end CFSG.BenderSuzuki
