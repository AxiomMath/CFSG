module

public import CFSG.Permutation.FiveTransitive.CyclicFourSquareTranslation
public import CFSG.Permutation.FiveTransitive.CyclicFourDoubleSwapGeometry

public section

namespace CFSG

namespace FiveTransitive.CyclicFourCommutingDouble

open MulAction NormalizerFixedComplement

theorem contradiction
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (hmax : ∀ u : G, orderOf u = 2 → (fixedBy X u).ncard ≤ 7)
    (Q : Subgroup G) (hQ : Nat.card Q = 4)
    (hseven : Nat.card (fixedPoints Q X) = 7)
    (hfree : ∀ (q : Q) (t : X), t ∉ fixedPoints Q X → q • t = t → q = 1)
    (hdiv : 8 ∣ Nat.card X - 7) (b : Q) (hb : orderOf b = 4)
    (y z : Normalizer Q) (hy : orderOf y.val = 2) (hz : orderOf z.val = 2)
    (hcommy : ∀ q : Q, Commute q.val y.val)
    (hcommz : ∀ q : Q, Commute q.val z.val)
    (hyz : Commute y.val z.val) (hne : y.val ≠ z.val)
    (hlocal : (fixedBy X y.val ∩ fixedPoints Q X).ncard = 3)
    (t : X) (htF : t ∉ fixedPoints Q X)
    (hyt : y.val • t = t) (hzt : z.val • t = t) : False := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hyfour, _, _, _, _, p, w, _, _, hYeq, hAYeq, hpcard, hwcard, hdis⟩ :=
    CyclicFourDoubleSwapGeometry.exists_two_orbits hmax Q hQ hseven hfree hdiv b hb y hy
      hcommy hlocal ⟨t, htF, hyt⟩
  have hYo := CyclicFourDoubleSwapGeometry.fixed_eq_orbit Q hQ hfree y hcommy
    hyfour (⟨t, htF⟩ : Domain (X := X) Q) hyt
  have hZfirst : ∀ r ∈ orbit Q p.val, z.val • r = r := by
    intro r hr
    rw [← hYeq, hYo] at hr
    obtain ⟨q, rfl⟩ := mem_orbit_iff.mp hr
    change z.val • (q.val • t) = q.val • t
    rw [← mul_smul, ← (hcommz q).eq, mul_smul, hzt]
  have hYfirst : ∀ r ∈ orbit Q p.val, y.val • r = r := by
    intro r hr
    exact (hYeq.ge hr).1
  have hbG : orderOf b.val = 4 := (Subgroup.orderOf_coe b).trans hb
  have hb4 : b.val ^ 4 = 1 := hbG ▸ pow_orderOf_eq_one b.val
  have hb2act (r : X) : b.val ^ 2 • (b.val ^ 2 • r) = r := by
    rw [← mul_smul, ← pow_add, hb4, one_smul]
  have hYsecond : ∀ r ∈ orbit Q w.val, y.val • r = b.val ^ 2 • r := by
    intro r hr
    have hfix := (hAYeq.ge hr).1
    change (b.val ^ 2 * y.val) • r = r at hfix
    rw [mul_smul] at hfix
    have he := congrArg (fun v : X => b.val ^ 2 • v) hfix
    rw [hb2act] at he
    exact he
  have hza : Commute z.val (b.val ^ 2 * y.val) :=
    ((hcommz b).symm.pow_right 2).mul_right hyz.symm
  have hstable : z.val • w.val ∈ orbit Q w.val := by
    rw [← hAYeq]
    refine ⟨?_, (z • w).property⟩
    have hwfix : (b.val ^ 2 * y.val) • w.val = w.val :=
      (hAYeq.ge (mem_orbit_self w.val)).1
    change (b.val ^ 2 * y.val) • (z.val • w.val) = z.val • w.val
    rw [← mul_smul, ← hza.eq, mul_smul, hwfix]
  have hQcomm : ∀ q r : Q, Commute q.val r.val := by
    intro q r
    exact congrArg (fun v : Q => v.val)
      (isMulCommutative_iff.mp
        (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by simpa using hQ)) q r)
  have hz2 : z.val ^ 2 = 1 := hz ▸ pow_orderOf_eq_one z.val
  have hUnionCard : (orbit Q p.val ∪ orbit Q w.val).ncard = 8 := by
    rw [Set.ncard_union_eq hdis, hpcard, hwcard]
  have htoo (g : G) (hg : orderOf g = 2)
      (hgfirst : ∀ r ∈ orbit Q p.val, g • r = r)
      (hgsecond : ∀ r ∈ orbit Q w.val, g • r = r) : False := by
    have h8 : 8 ≤ (fixedBy X g).ncard := by
      rw [← hUnionCard]
      refine Set.ncard_le_ncard ?_ (Set.toFinite _)
      intro r hr
      rcases hr with hr | hr
      · exact hgfirst r hr
      · exact hgsecond r hr
    have h7 := hmax g hg
    omega
  rcases CyclicFourSquareTranslation.orbit_action_cases Q hQ b hb hQcomm z.val hz2 hcommz
      w.val (fun q h => hfree q w.val w.property h) hstable with hZsecond | hZsecond
  · exact htoo z.val hz hZfirst hZsecond
  · have hy2 : y.val ^ 2 = 1 := hy ▸ pow_orderOf_eq_one y.val
    have hyz2 : (y.val * z.val) ^ 2 = 1 := by rw [hyz.mul_pow, hy2, hz2, one_mul]
    have hyzne : y.val * z.val ≠ 1 := by
      intro he
      apply hne
      calc
        y.val = y.val * (z.val * z.val) := by rw [← pow_two, hz2, mul_one]
        _ = (y.val * z.val) * z.val := (mul_assoc _ _ _).symm
        _ = z.val := by rw [he, one_mul]
    have hyzorder : orderOf (y.val * z.val) = 2 := orderOf_eq_prime hyz2 hyzne
    apply htoo (y.val * z.val) hyzorder
    · intro r hr
      rw [mul_smul, hZfirst r hr, hYfirst r hr]
    · intro r hr
      rw [mul_smul, hZsecond r hr, ← mul_smul, ← ((hcommy b).pow_left 2).eq,
        mul_smul, hYsecond r hr, hb2act]

end FiveTransitive.CyclicFourCommutingDouble

end CFSG
