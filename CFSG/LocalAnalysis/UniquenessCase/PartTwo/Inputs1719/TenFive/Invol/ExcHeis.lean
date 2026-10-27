module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.Heis

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3 (Heis)
open scoped commutatorElement

private theorem map_zero_eq_one {K S : Type*} [Field K] [Group S] {f : K → S}
    (hf : ∀ s t, f (s + t) = f s * f t) : f 0 = 1 := by
  have h : f 0 = f 0 * f 0 := by simpa [add_zero] using hf 0 0
  exact left_eq_mul.mp h

private theorem swap_of_comm {K S : Type*} [Field K] [Group S] {xa xb z : K → S}
    (hab : ∀ s t, ⁅xa s, xb t⁆ = z (s * t)) (s t : K) :
    xa s * xb t = z (s * t) * xb t * xa s := by
  rw [← hab s t, commutatorElement_def]
  group

private theorem commute_z_z {K S : Type*} [Field K] [Group S] {xa xb z : K → S}
    (hab : ∀ s t, ⁅xa s, xb t⁆ = z (s * t))
    (hza : ∀ s t, Commute (z s) (xa t)) (hzb : ∀ s t, Commute (z s) (xb t))
    (s t : K) : Commute (z s) (z t) := by
  have ht : z t = xa t * xb 1 * (xa t)⁻¹ * (xb 1)⁻¹ := by
    have h := hab t 1
    rw [mul_one] at h
    rw [← h, commutatorElement_def]
  rw [ht]
  exact (((hza s t).mul_right (hzb s 1)).mul_right (Commute.inv_right (hza s t))).mul_right
    (Commute.inv_right (hzb s 1))

private def heisLift {K S : Type*} [Field K] [Group S] {xa xb z : K → S}
    (hxa : ∀ s t, xa (s + t) = xa s * xa t) (hxb : ∀ s t, xb (s + t) = xb s * xb t)
    (hz : ∀ s t, z (s + t) = z s * z t) (hab : ∀ s t, ⁅xa s, xb t⁆ = z (s * t))
    (hza : ∀ s t, Commute (z s) (xa t)) (hzb : ∀ s t, Commute (z s) (xb t)) :
    Heis K →* S where
  toFun x := xb x.b * xa x.a * z x.c
  map_one' := by
    have hxa0 : xa 0 = 1 := map_zero_eq_one hxa
    have hxb0 : xb 0 = 1 := map_zero_eq_one hxb
    have hz0 : z 0 = 1 := map_zero_eq_one hz
    simp [hxa0, hxb0, hz0]
  map_mul' x y := by
    have hzz : ∀ s t : K, z s * z t = z t * z s := fun s t => (commute_z_z hab hza hzb s t).eq
    have E1 : z x.c * xb y.b = xb y.b * z x.c := (hzb x.c y.b).eq
    have E2 : z x.c * xa y.a = xa y.a * z x.c := (hza x.c y.a).eq
    have E3 : xa x.a * xb y.b = z (x.a * y.b) * xb y.b * xa x.a := swap_of_comm hab x.a y.b
    have E4 : z (x.a * y.b) * xb y.b = xb y.b * z (x.a * y.b) := (hzb (x.a * y.b) y.b).eq
    have E5 : z (x.a * y.b) * xa x.a = xa x.a * z (x.a * y.b) := (hza (x.a * y.b) x.a).eq
    have E6 : z (x.a * y.b) * xa y.a = xa y.a * z (x.a * y.b) := (hza (x.a * y.b) y.a).eq
    have E7 : z (x.a * y.b) * z x.c = z x.c * z (x.a * y.b) := hzz _ _
    have E8 : z (x.a * y.b) * z y.c = z y.c * z (x.a * y.b) := hzz _ _
    simp only [Heis.mul_a, Heis.mul_b, Heis.mul_c]
    rw [hxb, hxa, hz, hz]
    symm
    calc (xb x.b * xa x.a * z x.c) * (xb y.b * xa y.a * z y.c)
        = xb x.b * xa x.a * (z x.c * xb y.b) * xa y.a * z y.c := by group
      _ = xb x.b * xa x.a * (xb y.b * z x.c) * xa y.a * z y.c := by rw [E1]
      _ = xb x.b * xa x.a * xb y.b * (z x.c * xa y.a) * z y.c := by group
      _ = xb x.b * xa x.a * xb y.b * (xa y.a * z x.c) * z y.c := by rw [E2]
      _ = xb x.b * (xa x.a * xb y.b) * xa y.a * z x.c * z y.c := by group
      _ = xb x.b * (z (x.a * y.b) * xb y.b * xa x.a) * xa y.a * z x.c * z y.c := by
            rw [E3]
      _ = xb x.b * (z (x.a * y.b) * xb y.b) * xa x.a * xa y.a * z x.c * z y.c := by
            group
      _ = xb x.b * (xb y.b * z (x.a * y.b)) * xa x.a * xa y.a * z x.c * z y.c := by
            rw [E4]
      _ = xb x.b * xb y.b * (z (x.a * y.b) * xa x.a) * xa y.a * z x.c * z y.c := by
            group
      _ = xb x.b * xb y.b * (xa x.a * z (x.a * y.b)) * xa y.a * z x.c * z y.c := by
            rw [E5]
      _ = xb x.b * xb y.b * xa x.a * (z (x.a * y.b) * xa y.a) * z x.c * z y.c := by
            group
      _ = xb x.b * xb y.b * xa x.a * (xa y.a * z (x.a * y.b)) * z x.c * z y.c := by
            rw [E6]
      _ = xb x.b * xb y.b * xa x.a * xa y.a * (z (x.a * y.b) * z x.c) * z y.c := by
            group
      _ = xb x.b * xb y.b * xa x.a * xa y.a * (z x.c * z (x.a * y.b)) * z y.c := by
            rw [E7]
      _ = xb x.b * xb y.b * xa x.a * xa y.a * z x.c * (z (x.a * y.b) * z y.c) := by
            group
      _ = xb x.b * xb y.b * xa x.a * xa y.a * z x.c * (z y.c * z (x.a * y.b)) := by
            rw [E8]
      _ = xb x.b * xb y.b * (xa x.a * xa y.a) * ((z x.c * z y.c) * z (x.a * y.b)) := by
            group

theorem exists_heis_of_comm {K S : Type*} [Field K] [Group S] {xa xb z : K → S}
    (hxa : ∀ s t, xa (s + t) = xa s * xa t) (hxb : ∀ s t, xb (s + t) = xb s * xb t)
    (hz : ∀ s t, z (s + t) = z s * z t) (hzi : Function.Injective z)
    (hab : ∀ s t, ⁅xa s, xb t⁆ = z (s * t))
    (hza : ∀ s t, Commute (z s) (xa t)) (hzb : ∀ s t, Commute (z s) (xb t)) :
    ∃ ι : Heis K →* S, Function.Injective ι ∧ (∀ s, ι ⟨s, 0, 0⟩ = xa s) ∧
      (∀ s, ι ⟨0, s, 0⟩ = xb s) ∧ ∀ s, ι ⟨0, 0, s⟩ = z s := by
  have hxa0 : xa 0 = 1 := map_zero_eq_one hxa
  have hxb0 : xb 0 = 1 := map_zero_eq_one hxb
  have hz0 : z 0 = 1 := map_zero_eq_one hz
  let φ : Heis K →* S := heisLift hxa hxb hz hab hza hzb
  have hφ_a : ∀ s : K, φ ⟨s, 0, 0⟩ = xa s := by
    intro s
    change xb (0 : K) * xa s * z (0 : K) = xa s
    rw [hxb0, hz0, one_mul, mul_one]
  have hφ_b : ∀ s : K, φ ⟨0, s, 0⟩ = xb s := by
    intro s
    change xb s * xa (0 : K) * z (0 : K) = xb s
    rw [hxa0, hz0, mul_one, mul_one]
  have hφ_c : ∀ s : K, φ ⟨0, 0, s⟩ = z s := by
    intro s
    change xb (0 : K) * xa (0 : K) * z s = z s
    rw [hxb0, hxa0, one_mul, one_mul]
  refine ⟨φ, ?_, hφ_a, hφ_b, hφ_c⟩
  rw [injective_iff_map_eq_one]
  intro x hx
  have ha : x.a = 0 := by
    have h1 : φ ⁅x, (⟨0, 1, 0⟩ : Heis K)⁆ = 1 := by
      rw [map_commutatorElement, hx]
      simp
    have h2 : z x.a = 1 := by
      have h := h1
      rw [Heis.commutator_eq] at h
      simpa [hφ_c] using h
    exact hzi (by rw [h2, hz0])
  have hb : x.b = 0 := by
    have h1 : φ ⁅x, (⟨1, 0, 0⟩ : Heis K)⁆ = 1 := by
      rw [map_commutatorElement, hx]
      simp
    have h2 : z (-x.b) = 1 := by
      have h := h1
      rw [Heis.commutator_eq] at h
      simpa [hφ_c] using h
    exact neg_eq_zero.mp (hzi (by rw [h2, hz0]))
  have hc : x.c = 0 := by
    have h2 : φ x = z x.c := by
      change xb x.b * xa x.a * z x.c = z x.c
      rw [ha, hb, hxb0, hxa0, one_mul, one_mul]
    rw [h2] at hx
    exact hzi (by rw [hx, hz0])
  ext
  · simpa using ha
  · simpa using hb
  · simpa using hc

theorem isSpecialGood_of_comm {K S : Type*} [Field K] [Finite K] [Group S] {p e : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) [CharP K p] (hK : Nat.card K = p ^ e) (h3 : 3 < p ^ e)
    {xa xb z : K → S}
    (hxa : ∀ s t, xa (s + t) = xa s * xa t) (hxb : ∀ s t, xb (s + t) = xb s * xb t)
    (hz : ∀ s t, z (s + t) = z s * z t) (hzi : Function.Injective z)
    (hab : ∀ s t, ⁅xa s, xb t⁆ = z (s * t))
    (hza : ∀ s t, Commute (z s) (xa t)) (hzb : ∀ s t, Commute (z s) (xb t)) (s : K) :
    IsSpecialGood p (xa s) ∧ IsSpecialGood p (xb s) ∧ IsSpecialGood p (z s) := by
  obtain ⟨ι, hι, ha, hb, hc⟩ := exists_heis_of_comm hxa hxb hz hzi hab hza hzb
  refine ⟨?_, ?_, ?_⟩
  · rw [← ha s]
    exact isSpecialGood_of_heis hp hp2 hK h3 hι _
  · rw [← hb s]
    exact isSpecialGood_of_heis hp hp2 hK h3 hι _
  · rw [← hc s]
    exact isSpecialGood_of_heis hp hp2 hK h3 hι _

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
