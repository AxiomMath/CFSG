module

public import CFSG.Permutation.FiveTransitive.FixedFiveInvolutionGeometry

public section

namespace CFSG

namespace FiveTransitive.ElementaryFourOrbitExclusion

open MulAction

private theorem four_translates_card
    {G X : Type*} [CommGroup G] [MulAction G X]
    (h2 : ∀ g : G, g * g = 1) (a b : G) (t : X)
    (ha : a • t ≠ t) (hb : b • t ≠ t) (hab : (a * b) • t ≠ t) :
    ({t, a • t, b • t, (a * b) • t} : Set X).ncard = 4 := by
  have hh (g : G) (s : X) : g • (g • s) = s := by rw [← mul_smul, h2, one_smul]
  have h12 : a • t ≠ b • t := by
    intro he
    apply hab
    rw [mul_smul, ← he, hh]
  have h13 : a • t ≠ (a * b) • t := by
    intro he
    rw [mul_smul] at he
    exact hb ((MulAction.injective a) he).symm
  have h23 : b • t ≠ (a * b) • t := by
    intro he
    rw [mul_comm a b, mul_smul] at he
    exact ha ((MulAction.injective b) he).symm
  simp [ha.symm, hb.symm, hab.symm, h12, h13, h23]

theorem no_threefold_fixed
    {G X : Type*} [CommGroup G] [Finite X] [MulAction G X]
    (h2 : ∀ g : G, g * g = 1) (T : Set X)
    (hT : ∀ (g : G) (t : X), t ∈ T → g • t ∈ T)
    (a b c d : G)
    (hbound : (fixedBy X (a * b * c) \ T).ncard ≤ 4)
    (ha : ∀ t ∉ T, a • t ≠ t) (hb : ∀ t ∉ T, b • t ≠ t)
    (hab : ∀ t ∉ T, (a * b) • t ≠ t)
    (hd : ∀ t ∉ T, d • t ≠ t)
    (had : ∀ t ∉ T, (a * d) • t ≠ t)
    (hbd : ∀ t ∉ T, (b * d) • t ≠ t)
    (hcd : ∀ t ∉ T, (c * d) • t ≠ t) :
    ∀ t ∉ T, (a * b * c) • t ≠ t := by
  intro t ht hfix
  have hh (g : G) (s : X) : g • (g • s) = s := by rw [← mul_smul, h2, one_smul]
  have hout (g : G) : g • t ∉ T := by
    intro he
    exact ht (by simpa only [hh] using hT g (g • t) he)
  let O : Set X := {t, a • t, b • t, (a * b) • t}
  have hO : O.ncard = 4 := four_translates_card h2 a b t (ha t ht) (hb t ht) (hab t ht)
  have hsub : O ⊆ fixedBy X (a * b * c) \ T := by
    intro s hs
    simp only [O, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    have hstable (g : G) : g • t ∈ fixedBy X (a * b * c) :=
      FixedFiveInvolutionGeometry.mem_fixedBy_smul_of_commute (a * b * c) g (mul_comm _ _) hfix
    rcases hs with rfl | rfl | rfl | rfl
    · exact ⟨hfix, ht⟩
    · exact ⟨hstable a, hout a⟩
    · exact ⟨hstable b, hout b⟩
    · exact ⟨hstable (a * b), hout (a * b)⟩
  have heq : fixedBy X (a * b * c) \ T = O :=
    (Set.eq_of_subset_of_ncard_le hsub (by rwa [hO])).symm
  have hdt : d • t ∈ O := by
    rw [← heq]
    exact ⟨FixedFiveInvolutionGeometry.mem_fixedBy_smul_of_commute
      (a * b * c) d (mul_comm _ _) hfix, hout d⟩
  simp only [O, Set.mem_insert_iff, Set.mem_singleton_iff] at hdt
  rcases hdt with he | he | he | he
  · exact hd t ht he
  · exact had t ht (by rw [mul_smul, he, hh])
  · exact hbd t ht (by rw [mul_smul, he, hh])
  · have hf : (a * b) • (c • t) = t := by simpa only [mul_smul] using hfix
    have hc : c • t = (a * b) • t := by
      have he' := congrArg (fun s : X => (a * b) • s) hf
      rwa [hh] at he'
    exact hcd t ht (by rw [mul_smul, he, ← hc, hh])

end FiveTransitive.ElementaryFourOrbitExclusion

end CFSG
