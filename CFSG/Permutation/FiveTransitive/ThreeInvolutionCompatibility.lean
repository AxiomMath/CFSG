module

public import CFSG.Permutation.FiveTransitive.FixedFiveInvolutionGeometry

public section

namespace CFSG

namespace FiveTransitive.ThreeInvolutionCompatibility

open MulAction

private theorem square_fixes_pair
    {G X : Type*} [Group G] [MulAction G X] (g : G) (u v : X)
    (hstable : ∀ z ∈ ({u, v} : Set X), g • z ∈ ({u, v} : Set X)) :
    (g * g) • u = u ∧ (g * g) • v = v := by
  have hp (u v : X) (hstable : ∀ z ∈ ({u, v} : Set X), g • z ∈ ({u, v} : Set X)) :
      (g * g) • u = u := by
    have hu := hstable u (by simp)
    have hv := hstable v (by simp)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with hu | hu
    · rw [mul_smul, hu, hu]
    · rcases hv with hv | hv
      · rw [mul_smul, hu, hv]
      · have huv : u = v := (MulAction.injective g) (hu.trans hv.symm)
        rw [mul_smul, huv, hv, hv]
  exact ⟨hp u v hstable, hp v u (by simpa only [Set.pair_comm] using hstable)⟩

private theorem commute_product_of_pair_squares
    {G : Type*} [Group G] (a x y z : G)
    (ha : a * a = 1) (hx : x * x = 1) (hy : y * y = 1) (hz : z * z = 1)
    (hay : a * y = y * a)
    (hxy : (x * y) * (x * y) = a) (hxz : (x * z) * (x * z) = a) :
    x * (y * z) = (y * z) * x := by
  have hxy' : x * y * x = a * y := by
    have h := congrArg (fun t : G => t * y) hxy
    simpa only [mul_assoc, hy, mul_one] using h
  have hxz' : x * z * x = a * z := by
    have h := congrArg (fun t : G => t * z) hxz
    simpa only [mul_assoc, hz, mul_one] using h
  have hxx (t : G) : x * (x * t) = t := by rw [← mul_assoc, hx, one_mul]
  have haa (t : G) : a * (a * t) = t := by rw [← mul_assoc, ha, one_mul]
  have he : x * (y * z) * x = y * z := by
    calc
      x * (y * z) * x = (x * y * x) * (x * z * x) := by
        simp only [mul_assoc, hxx]
      _ = (a * y) * (a * z) := by rw [hxy', hxz']
      _ = y * z := by rw [hay]; simp only [mul_assoc, haa]
  have h := congrArg (fun t : G => t * x) he
  simpa only [mul_assoc, hx, mul_one] using h

theorem pair_square_eq_one
    {G X : Type*} [Group G] [MulAction G X] (a x y z : G)
    (ha : a * a = 1) (hx : x * x = 1) (hy : y * y = 1) (hz : z * z = 1)
    (hay : a * y = y * a) (haz : a * z = z * a)
    (hcases : (x * y) * (x * y) = 1 ∨ (x * y) * (x * y) = a)
    (heq1 : (x * z) * (x * z) = (x * y) * (x * y))
    (heq2 : (y * z) * (y * z) = (x * y) * (x * y))
    (htwo : (fixedBy X x \ fixedBy X a).ncard = 2) :
    (x * y) * (x * y) = 1 := by
  rcases hcases with h | h
  · exact h
  have hxb : x * (y * z) = (y * z) * x :=
    commute_product_of_pair_squares a x y z ha hx hy hz hay h (heq1.trans h)
  have hab : a * (y * z) = (y * z) * a := by rw [← mul_assoc, hay, mul_assoc, haz, ← mul_assoc]
  obtain ⟨u, v, huv, huvset⟩ := Set.ncard_eq_two.mp htwo
  have hstable : ∀ w ∈ ({u, v} : Set X), (y * z) • w ∈ ({u, v} : Set X) := by
    intro w hw
    rw [← huvset] at hw ⊢
    refine ⟨FixedFiveInvolutionGeometry.mem_fixedBy_smul_of_commute x (y * z) hxb hw.1, ?_⟩
    intro he
    apply hw.2
    apply (MulAction.injective (y * z))
    change (y * z) • (a • w) = (y * z) • w
    rw [← mul_smul, ← hab, mul_smul]
    exact he
  have hu := (square_fixes_pair (y * z) u v hstable).1
  rw [heq2, h] at hu
  have hnot : u ∉ fixedBy X a := by
    have hu' : u ∈ fixedBy X x \ fixedBy X a := by rw [huvset]; simp
    exact hu'.2
  exact (hnot hu).elim

end FiveTransitive.ThreeInvolutionCompatibility

end CFSG
