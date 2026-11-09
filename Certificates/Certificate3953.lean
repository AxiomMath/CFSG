module

public import CFSG.GH74.Filter.Lie.EvenSeriesInputs

public section

open CFSG.GH74.Filter.Lie

namespace CertificateChecks.Batch3953

open CFSG.GH74.Filter.Lie

private theorem witnessF4five_check_0 : witnessF4five.check = true := by
  decide +kernel

private theorem witnessE6five_check_1 : witnessE6five.check = true := by
  decide +kernel

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley in
@[expose] def pfBody (τ : Tag) (α β : Fin τ.rank → ℤ) (c : ℕ) : Bool :=
  (List.range 7).all fun a => (List.range 7).all fun b =>
    !(decide (1 ≤ a) && decide (1 ≤ b) && decide (decodeVec (τ := τ) c = a • α + b • β))

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley in
@[expose] def pfBodyL (τ : Tag) (α β : Fin τ.rank → ℤ) (c : ℕ) : Bool :=
  (List.range 7).all fun a => (List.range 7).all fun b =>
    !(decide (1 ≤ a) && decide (1 ≤ b) &&
      (List.finRange τ.rank).all fun j => decodeVec (τ := τ) c j == (a : ℤ) * α j + (b : ℤ) * β j)

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley in
@[expose] def pairFreeL (τ : Tag) (α β : Fin τ.rank → ℤ) : Bool :=
  τ.rootCertificate.roots.all (pfBodyL τ α β)

theorem all_range_getD (L : List ℕ) (f : ℕ → Bool) :
    ((List.range L.length).all fun k => f (L.getD k 0)) = L.all f := by
  rw [Bool.eq_iff_iff]
  simp only [List.all_eq_true, List.mem_range]
  constructor
  · intro h x hx
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    have := h k hk
    rwa [List.getD_eq_getElem _ _ hk] at this
  · intro h k hk
    rw [List.getD_eq_getElem _ _ hk]
    exact h _ (List.getElem_mem hk)

open CFSG.Blueprint.Chevalley in
theorem decide_vec_eq {τ : Tag} (v α β : Fin τ.rank → ℤ) (a b : ℕ) :
    decide (v = a • α + b • β) =
      (List.finRange τ.rank).all fun j => v j == (a : ℤ) * α j + (b : ℤ) * β j := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, List.all_eq_true]
  simp only [List.mem_finRange, true_implies, beq_iff_eq, funext_iff, Pi.add_apply,
    Pi.smul_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley in
theorem pairFree_eq (τ : Tag) (α β : Fin τ.rank → ℤ) : pairFree τ α β = pairFreeL τ α β := by
  have h1 : pairFree τ α β = (List.range τ.rootCertificate.roots.length).all fun k =>
      pfBody τ α β (τ.rootCertificate.roots.getD k 0) := rfl
  have h2 : pfBody τ α β = pfBodyL τ α β := by
    funext c
    simp only [pfBody, pfBodyL, decide_vec_eq]
  rw [h1, all_range_getD, h2, pairFreeL]

private theorem witnessE7five_check_2 : witnessE7five.check = true := by
  unfold SepWitness.check
  simp only [pairFree_eq]
  decide +kernel

private theorem witnessE8five_check_3 : witnessE8five.check = true := by
  unfold SepWitness.check
  simp only [pairFree_eq]
  decide +kernel

end CertificateChecks.Batch3953

namespace Certificates

open CertificateChecks

open CFSG.GH74.Filter.Lie in
theorem certificate3953 : witnessF4five.check = true ∧ witnessE6five.check = true
    ∧ witnessE7five.check = true ∧ witnessE8five.check = true := by
  exact ⟨CertificateChecks.Batch3953.witnessF4five_check_0, CertificateChecks.Batch3953.witnessE6five_check_1,
    CertificateChecks.Batch3953.witnessE7five_check_2, CertificateChecks.Batch3953.witnessE8five_check_3⟩

end Certificates
