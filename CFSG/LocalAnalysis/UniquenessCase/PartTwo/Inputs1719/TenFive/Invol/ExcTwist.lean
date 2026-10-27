module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcHeis

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3 (Heis)
open scoped commutatorElement

theorem isSpecialGood_mul_of_comm {K S : Type*} [Field K] [Finite K] [Group S] {p e : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) [CharP K p] (hK : Nat.card K = p ^ e) (h3 : 3 < p ^ e)
    {xa xb z w : K → S}
    (hxa : ∀ s t, xa (s + t) = xa s * xa t) (hxb : ∀ s t, xb (s + t) = xb s * xb t)
    (hz : ∀ s t, z (s + t) = z s * z t) (hzi : Function.Injective z)
    (hab : ∀ s t, ⁅xa s, xb t⁆ = z (s * t))
    (hza : ∀ s t, Commute (z s) (xa t)) (hzb : ∀ s t, Commute (z s) (xb t))
    (hw : ∀ s t, w (s + t) = w s * w t)
    (hwa : ∀ s t, Commute (w s) (xa t)) (hwb : ∀ s t, Commute (w s) (xb t))
    (f : K →+ K) {s : K} (hs : s ≠ 0) :
    orderOf (xb s * w (f s)) = p ∧ IsSpecialGood p (xb s * w (f s)) := by
  have : Fact p.Prime := ⟨hp⟩
  let xb' : K → S := fun t => xb t * w (f t)
  have hxb' : ∀ s t, xb' (s + t) = xb' s * xb' t := by
    intro s t
    have hf : f (s + t) = f s + f t := map_add f s t
    calc xb' (s + t) = xb s * xb t * (w (f s) * w (f t)) := by
          change xb (s + t) * w (f (s + t)) = _
          rw [hxb s t, hf, hw]
      _ = (xb s * w (f s)) * (xb t * w (f t)) :=
          (hwb (f s) t).symm.mul_mul_mul_comm (xb s) (w (f t))
      _ = xb' s * xb' t := rfl
  have hab' : ∀ s t, ⁅xa s, xb' t⁆ = z (s * t) := by
    intro s t
    have H : ⁅xa s, xb t * w (f t)⁆ = ⁅xa s, xb t⁆ := by
      rw [commutatorElement_mul_right_eq_mul_conj,
        (hwa (f t) s).symm.commutator_eq, mul_one]
      group
    change ⁅xa s, xb t * w (f t)⁆ = z (s * t)
    rw [H, hab s t]
  have hzw : ∀ s t, Commute (z s) (w t) := by
    intro s t
    have hz_eq : z s = xa s * xb 1 * (xa s)⁻¹ * (xb 1)⁻¹ := by
      have h := hab s 1
      rw [mul_one] at h
      rw [← h, commutatorElement_def]
    have h' : Commute (w t) (xa s * xb 1 * (xa s)⁻¹ * (xb 1)⁻¹) :=
      (((hwa t s).mul_right (hwb t 1)).mul_right
        (Commute.inv_right (hwa t s))).mul_right (Commute.inv_right (hwb t 1))
    rw [hz_eq]
    exact h'.symm
  have hzb' : ∀ s t, Commute (z s) (xb' t) := fun s t =>
    (hzb s t).mul_right (hzw s (f t))
  obtain ⟨ι, hι, -, hb', -⟩ := exists_heis_of_comm hxa hxb' hz hzi hab' hza hzb'
  have hspec : IsSpecialGood p (xb s * w (f s)) := by
    change IsSpecialGood p (xb' s)
    rw [← hb' s]
    exact isSpecialGood_of_heis hp hp2 hK h3 hι _
  have hxp : (⟨0, s, 0⟩ : Heis K) ^ p = 1 := Heis.pow_prime_eq_one hp hp2 _
  have hxne : (⟨0, s, 0⟩ : Heis K) ≠ 1 := by
    intro h
    exact hs (by simpa using congrArg Heis.b h)
  have hord : orderOf (xb s * w (f s)) = p := by
    change orderOf (xb' s) = p
    rw [← hb' s]
    exact (orderOf_injective ι hι _).trans (orderOf_eq_prime hxp hxne)
  exact ⟨hord, hspec⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
