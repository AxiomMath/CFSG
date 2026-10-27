module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Hall.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# Hall Lemma 14.4.2

Source interface for Hall's diagonal contribution identities in §14.4.
-/

namespace CFSG.BenderSuzuki
namespace External

open scoped BigOperators

universe u

private theorem hallDiagonalContribution_eq_of_isConj
    {G A : Type u} [Group G] [Finite G]
    {H : Subgroup G} [H.FiniteIndex] [CommGroup A] (φ : H →* A)
    {u v : G} (huv : IsConj u v) :
    hallDiagonalContribution (H := H) φ u = hallDiagonalContribution (H := H) φ v := by
  classical
  rcases huv with ⟨t, ht⟩
  have hv : v = (t : G) * u * (t : G)⁻¹ := by
    have h := congrArg (fun x : G => x * (t : G)⁻¹) ht.eq
    simpa [mul_assoc] using h.symm
  subst v
  letI : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
  unfold hallDiagonalContribution
  let e : {q : G ⧸ H // Function.minimalPeriod (u • ·) q = 1} ≃
      {q : G ⧸ H // Function.minimalPeriod (((t : G) * u * (t : G)⁻¹) • ·) q = 1} := {
    toFun := fun q => ⟨(t : G) • q.1, by
      rw [Function.minimalPeriod_eq_one_iff_isFixedPt]
      have hqfix : u • q.1 = q.1 := Function.minimalPeriod_eq_one_iff_isFixedPt.mp q.2
      change ((t : G) * u * (t : G)⁻¹) • ((t : G) • q.1) = (t : G) • q.1
      simpa [smul_smul, mul_assoc] using congrArg (fun x : G ⧸ H => (t : G) • x) hqfix⟩
    invFun := fun q => ⟨(t : G)⁻¹ • q.1, by
      rw [Function.minimalPeriod_eq_one_iff_isFixedPt]
      have hqfix : ((t : G) * u * (t : G)⁻¹) • q.1 = q.1 :=
        Function.minimalPeriod_eq_one_iff_isFixedPt.mp q.2
      change u • ((t : G)⁻¹ • q.1) = (t : G)⁻¹ • q.1
      have h := congrArg (fun x : G ⧸ H => (t : G)⁻¹ • x) hqfix
      simpa [smul_smul, mul_assoc] using h⟩
    left_inv := by
      intro q
      apply Subtype.ext
      simp [smul_smul]
    right_inv := by
      intro q
      apply Subtype.ext
      simp [smul_smul] }
  refine Fintype.prod_equiv e (fun q =>
      φ ⟨q.1.out⁻¹ * u * q.1.out, by
        have hmem := QuotientGroup.out_conj_pow_minimalPeriod_mem (H := H) u q.1
        simpa [q.2] using hmem⟩)
    (fun q =>
      φ ⟨q.1.out⁻¹ * ((t : G) * u * (t : G)⁻¹) * q.1.out, by
        have hmem := QuotientGroup.out_conj_pow_minimalPeriod_mem (H := H)
          ((t : G) * u * (t : G)⁻¹) q.1
        simpa [q.2] using hmem⟩) ?_
  intro q
  let a : G := q.1.out
  let b : G := Quotient.out ((t : G) • q.1)
  change φ ⟨a⁻¹ * u * a, by
        have hmem := QuotientGroup.out_conj_pow_minimalPeriod_mem (H := H) u q.1
        simpa [a, q.2] using hmem⟩ =
      φ ⟨b⁻¹ * ((t : G) * u * (t : G)⁻¹) * b, by
        have hmem := QuotientGroup.out_conj_pow_minimalPeriod_mem (H := H)
          ((t : G) * u * (t : G)⁻¹) ((t : G) • q.1)
        have hq2 : Function.minimalPeriod (((t : G) * u * (t : G)⁻¹) • ·) ((t : G) • q.1) = 1 := (e q).2
        simpa [b, hq2] using hmem⟩
  have hbcoset : b⁻¹ * ((t : G) * a) ∈ H := by
    have hqout : (q.1.out : G ⧸ H) = q.1 := Quotient.out_eq q.1
    have hbout : (b : G ⧸ H) = (t : G) • q.1 := Quotient.out_eq ((t : G) • q.1)
    have hbeq : (b : G ⧸ H) = ((t : G) * a : G) := by
      calc
        (b : G ⧸ H) = (t : G) • q.1 := hbout
        _ = (t : G) • (a : G ⧸ H) := by rw [hqout]
        _ = ((t : G) * a : G) := by simp [MulAction.Quotient.smul_mk]
    exact QuotientGroup.eq.mp hbeq
  let h : H := ⟨b⁻¹ * ((t : G) * a), hbcoset⟩
  have hleft_mem : a⁻¹ * u * a ∈ H := by
    have hmem := QuotientGroup.out_conj_pow_minimalPeriod_mem (H := H) u q.1
    simpa [a, q.2] using hmem
  have hb_eq : b = (t : G) * a * (h : G)⁻¹ := by
    have hh : (h : G) = b⁻¹ * ((t : G) * a) := rfl
    calc
      b = (t : G) * a * ((b⁻¹ * ((t : G) * a))⁻¹) := by group
      _ = (t : G) * a * (h : G)⁻¹ := by rw [hh]
  have hfactor :
      b⁻¹ * ((t : G) * u * (t : G)⁻¹) * b =
        (h : G) * (a⁻¹ * u * a) * (h : G)⁻¹ := by
    rw [hb_eq]
    simp [h, mul_assoc]
  rw [show (⟨b⁻¹ * ((t : G) * u * (t : G)⁻¹) * b, by
        have hmem := QuotientGroup.out_conj_pow_minimalPeriod_mem (H := H)
          ((t : G) * u * (t : G)⁻¹) ((t : G) • q.1)
        have hq2 : Function.minimalPeriod (((t : G) * u * (t : G)⁻¹) • ·) ((t : G) • q.1) = 1 := (e q).2
        simpa [b, hq2] using hmem⟩ : H) =
      ⟨(h : G) * (a⁻¹ * u * a) * (h : G)⁻¹, by
        have hmem : b⁻¹ * ((t : G) * u * (t : G)⁻¹) * b ∈ H := by
          have hmem := QuotientGroup.out_conj_pow_minimalPeriod_mem (H := H)
            ((t : G) * u * (t : G)⁻¹) ((t : G) • q.1)
          have hq2 : Function.minimalPeriod (((t : G) * u * (t : G)⁻¹) • ·) ((t : G) • q.1) = 1 := (e q).2
          simpa [b, hq2] using hmem
        simpa [hfactor.symm] using hmem⟩ by
        apply Subtype.ext
        exact hfactor]
  change φ ⟨a⁻¹ * u * a, hleft_mem⟩ = φ (h * ⟨a⁻¹ * u * a, hleft_mem⟩ * h⁻¹)
  simp

private theorem hallDiagonalContribution_inv
    {G A : Type u} [Group G] [Finite G]
    {H : Subgroup G} [H.FiniteIndex] [CommGroup A] (φ : H →* A) (u : G) :
    hallDiagonalContribution (H := H) φ u⁻¹ =
      (hallDiagonalContribution (H := H) φ u)⁻¹ := by
  classical
  letI : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
  unfold hallDiagonalContribution
  let e : {q : G ⧸ H // Function.minimalPeriod (u⁻¹ • ·) q = 1} ≃
      {q : G ⧸ H // Function.minimalPeriod (u • ·) q = 1} :=
    Equiv.subtypeEquivRight (fun q => by
      rw [Function.minimalPeriod_eq_one_iff_isFixedPt,
        Function.minimalPeriod_eq_one_iff_isFixedPt]
      constructor
      · intro h
        change u⁻¹ • q = q at h
        change u • q = q
        have := congrArg (fun x : G ⧸ H => u • x) h
        simpa [smul_smul] using this.symm
      · intro h
        change u • q = q at h
        change u⁻¹ • q = q
        have := congrArg (fun x : G ⧸ H => u⁻¹ • x) h
        simpa [smul_smul] using this.symm)
  let term : {q : G ⧸ H // Function.minimalPeriod (u • ·) q = 1} → A := fun q =>
    φ ⟨q.1.out⁻¹ * u * q.1.out, by
      have hmem := QuotientGroup.out_conj_pow_minimalPeriod_mem (H := H) u q.1
      simpa [q.2] using hmem⟩
  calc
    (∏ q : {q : G ⧸ H // Function.minimalPeriod (u⁻¹ • ·) q = 1},
      φ ⟨q.1.out⁻¹ * u⁻¹ * q.1.out, by
        have hmem := QuotientGroup.out_conj_pow_minimalPeriod_mem (H := H) u⁻¹ q.1
        simpa [q.2] using hmem⟩) =
        ∏ q : {q : G ⧸ H // Function.minimalPeriod (u • ·) q = 1}, (term q)⁻¹ := by
      refine Fintype.prod_equiv e (fun q =>
        φ ⟨q.1.out⁻¹ * u⁻¹ * q.1.out, by
          have hmem := QuotientGroup.out_conj_pow_minimalPeriod_mem (H := H) u⁻¹ q.1
          simpa [q.2] using hmem⟩)
        (fun q => (term q)⁻¹) ?_
      intro q
      simp only [e, term, Equiv.subtypeEquivRight_apply]
      rw [← map_inv]
      congr
      simp [mul_assoc]
    _ = (∏ q : {q : G ⧸ H // Function.minimalPeriod (u • ·) q = 1}, term q)⁻¹ := by
      exact Finset.prod_inv_distrib (s := Finset.univ) term

/-- Hall Lemma 14.4.2: the diagonal contribution is invariant under conjugacy,
and inversion in the group inverts the diagonal contribution. -/
public theorem hall_lemma_14_4_2_diagonal_contribution_conjugacy
    {G A : Type u} [Group G] [Finite G]
    {H : Subgroup G} [H.FiniteIndex] [CommGroup A] (φ : H →* A) :
    (∀ u v : G, IsConj u v →
        hallDiagonalContribution (H := H) φ u =
          hallDiagonalContribution (H := H) φ v) ∧
      ∀ u : G,
        hallDiagonalContribution (H := H) φ u⁻¹ =
          (hallDiagonalContribution (H := H) φ u)⁻¹ := by
  constructor
  · intro u v huv
    exact hallDiagonalContribution_eq_of_isConj φ huv
  · intro u
    exact hallDiagonalContribution_inv φ u

end External
end CFSG.BenderSuzuki
