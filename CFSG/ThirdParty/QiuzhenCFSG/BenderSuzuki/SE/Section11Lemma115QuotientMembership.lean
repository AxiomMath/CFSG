module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115QuotientCore

namespace CFSG
end CFSG
open CFSG

/-!
# Section 11, Lemma 11.5: quotient membership cores

These two generic lemmas isolate the step putting the image of `tu` into the
regular normal subgroup of `N^*/P`: prime order survives a quotient when the
element is not in the kernel, and an odd-order element inverted by an
involution lies in the normal factor of a factorization by that involution's
centralizer.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII

universe u

/-- A prime-order element retains its order after quotienting, provided it
does not lie in the kernel. -/
public theorem lemma115_orderOf_quotient_eq_prime_of_not_mem
    {G : Type u} [Group G]
    (K : Subgroup G) [K.Normal]
    {x : G} {f : ℕ} (hf : f.Prime)
    (hxorder : orderOf x = f) (hxK : x ∉ K) :
    orderOf (QuotientGroup.mk' K x) = f := by
  have hdvd : orderOf (QuotientGroup.mk' K x) ∣ f := by
    rw [← hxorder]
    exact orderOf_map_dvd (QuotientGroup.mk' K) x
  rcases (Nat.dvd_prime hf).mp hdvd with hone | hself
  · exfalso
    apply hxK
    apply (QuotientGroup.eq_one_iff x).mp
    exact orderOf_eq_one_iff.mp hone
  · exact hself

/-- In a factorization `G = Q C_G(u)`, an odd-order element inverted by `u`
belongs to the normal factor `Q`. -/
public theorem lemma115_inverted_odd_order_mem_normal_factor
    {G : Type u} [Group G]
    (Q : Subgroup G) [Q.Normal]
    {u0 x : G}
    (hfactor : Q ⊔ Subgroup.centralizer ({u0} : Set G) = ⊤)
    (hxodd : Odd (orderOf x))
    (hxinv : rightConjugateElem x u0 = x⁻¹) :
    x ∈ Q := by
  let q : G →* G ⧸ Q := QuotientGroup.mk' Q
  have hxSup : x ∈ Q ⊔ Subgroup.centralizer ({u0} : Set G) := by
    rw [hfactor]
    trivial
  rcases Subgroup.mem_sup_of_normal_left.mp hxSup with
    ⟨a, haQ, c, hcC, hac⟩
  have hxprod : x = a * c := hac.symm
  have hqx : q x = q c := by
    rw [hxprod, map_mul]
    have hqa : q a = 1 := by
      exact (QuotientGroup.eq_one_iff a).mpr haQ
    rw [hqa, one_mul]
  have hccomm : c * u0 = u0 * c :=
    Subgroup.mem_centralizer_singleton_iff.mp hcC
  have hqxcomm : q x * q u0 = q u0 * q x := by
    rw [hqx]
    exact congrArg q hccomm
  have hqxinv : rightConjugateElem (q x) (q u0) = (q x)⁻¹ := by
    simpa [q, rightConjugateElem] using congrArg q hxinv
  have hqxfix : rightConjugateElem (q x) (q u0) = q x := by
    dsimp [rightConjugateElem]
    calc
      (q u0)⁻¹ * q x * q u0 =
          (q u0)⁻¹ * (q x * q u0) := by rw [mul_assoc]
      _ = (q u0)⁻¹ * (q u0 * q x) := by rw [hqxcomm]
      _ = q x := by simp
  have hqinvEq : q x = (q x)⁻¹ := hqxfix.symm.trans hqxinv
  have hqSq : (q x) ^ 2 = 1 := by
    calc
      (q x) ^ 2 = q x * q x := pow_two _
      _ = q x * (q x)⁻¹ := congrArg (fun z => q x * z) hqinvEq
      _ = 1 := mul_inv_cancel (q x)
  have horderTwo : orderOf (q x) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one hqSq
  have horderX : orderOf (q x) ∣ orderOf x :=
    orderOf_map_dvd q x
  have horderOdd : Odd (orderOf (q x)) :=
    Odd.of_dvd_nat hxodd horderX
  have horderOne : orderOf (q x) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp horderTwo with hone | htwo
    · exact hone
    · exfalso
      rw [htwo] at horderOdd
      exact (by decide : ¬ Odd 2) horderOdd
  exact (QuotientGroup.eq_one_iff x).mp
    (orderOf_eq_one_iff.mp horderOne)

end CFSG.BenderSuzuki
