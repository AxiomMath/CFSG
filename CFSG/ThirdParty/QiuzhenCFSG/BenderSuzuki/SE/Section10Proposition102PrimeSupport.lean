module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section10Proposition102Support
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section10Lemma106Hall

namespace CFSG
end CFSG
open CFSG

/-!
# Section 10, Proposition 10.2: prime-support bridge

This module packages the exact `[II1; 4.2]` transfer needed before the
Corollary 7.12 ambient-Sylow endpoint.  It does not assume any conclusion of
Proposition 10.2.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise

universe u

/-- A prime dividing the Peterfalvi kernel closure yields an ambient Sylow
subgroup of the two-point stabilizer, via the checked `[II1; 4.2]` transfer. -/
public theorem proposition102_ambient_sylow_of_prime_dvd_kernel
    {X : Type u} [Group X] [Finite X]
    {M : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
    (h42 : II1Lemma42PrimeTransfer (X := X))
    {q : ℕ} (hq : q.Prime)
    (hqK : q ∣ Nat.card (Subgroup.closure
      (peterfalviKSet (M ⊓ rightConjugate M t) t))) :
    ∃ Q : Sylow q X,
      (Q : Subgroup X) ≤ M ⊓ rightConjugate M t := by
  let D : Subgroup X := M ⊓ rightConjugate M t
  have hDodd : Odd (Nat.card D) := by
    simpa [D] using hM.inf_rightConjugate_card_odd htM
  have hDnorm : t ∈ Subgroup.normalizer (D : Set X) := by
    simpa [D] using inf_rightConjugate_mem_normalizer_of_isInvolution M ht
  have hqI : q ∣ Nat.card {x : X //
      x ∈ peterfalviKSet D t} := by
    exact h42 D t hDodd ht hDnorm q hq (by simpa [D] using hqK)
  exact proposition102_ambient_sylow_of_prime_dvd_kset
    hM ht htM d83 hq (by simpa [D] using hqI)

end CFSG.BenderSuzuki
