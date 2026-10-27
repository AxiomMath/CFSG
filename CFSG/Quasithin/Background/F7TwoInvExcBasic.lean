module

public import CFSG.Quasithin.Background.F7TwoInvAutWrap

public section

namespace CFSG.Quasithin.F7Two

variable {L : Type*} [Group L]

theorem not_isPGroup_two_zpowers_of_odd_orderOf {y : L} (hodd : Odd (orderOf y)) (h1 : y ≠ 1) :
    ¬ IsPGroup 2 ↥(Subgroup.zpowers y) := by
  rw [isPGroup_two_zpowers_iff]
  rintro ⟨n, hn⟩
  have hdvd : orderOf y ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
  have hcop : Nat.Coprime (orderOf y) (2 ^ n) := (Nat.coprime_two_right.2 hodd).pow_right n
  exact h1 (orderOf_eq_one_iff.1 (hcop.eq_one_of_dvd hdvd))

theorem not_isPGroup_two_zpowers_of_pow_prime {y : L} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : y ^ p = 1) (h1 : y ≠ 1) : ¬ IsPGroup 2 ↥(Subgroup.zpowers y) := by
  have := Fact.mk hp
  exact not_isPGroup_two_zpowers_of_odd_orderOf
    ((orderOf_eq_prime h h1).symm ▸ hp.odd_of_ne_two hp2) h1

theorem mem_invXiAut_conj_iff {u x : L} :
    x ∈ invXiAut (MulAut.conj u) ↔
      ¬ IsPGroup 2 ↥(Subgroup.zpowers (u * x * u⁻¹ * x⁻¹)) := by
  rw [invXiAut, Set.mem_ofPred_eq, MulAut.conj_apply]

theorem invAutGen_conj_of_generators {u : L} {S : Set L}
    (hS : ∀ x ∈ S, ¬ IsPGroup 2 ↥(Subgroup.zpowers (u * x * u⁻¹ * x⁻¹)))
    (hgen : Subgroup.closure S = ⊤) : InvAutGen L (MulAut.conj u) :=
  eq_top_iff.2 (hgen ▸ Subgroup.closure_mono fun x hx => mem_invXiAut_conj_iff.2 (hS x hx))

theorem invAutGen_conj_of_isConj {u r : L} (h : IsConj r u) (hr : InvAutGen L (MulAut.conj r)) :
    InvAutGen L (MulAut.conj u) := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  have h1 := (InvAutGen.conj_iff (MulAut.conj c) (MulAut.conj r)).1 hr
  rwa [← map_inv, ← map_mul, ← map_mul] at h1

theorem invAutGen_of_conj_aut {φ ψ : MulAut L} (c : MulAut L) (h : φ = c * ψ * c⁻¹)
    (hψ : InvAutGen L ψ) : InvAutGen L φ :=
  h ▸ (InvAutGen.conj_iff c ψ).1 hψ

theorem centralizer_le_closure_invXiAut_conj {u : L}
    (hne : (invXiAut (MulAut.conj u)).Nonempty) :
    Subgroup.centralizer {u} ≤ Subgroup.closure (invXiAut (MulAut.conj u)) := fun c hc => by
  refine fixSubgroup_le_closure_invXiAut hne (mem_fixSubgroup_iff.2 ?_)
  rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
  exact (Subgroup.mem_centralizer_singleton_iff.1 hc).symm

theorem invAutGen_conj_of_centralizing {u w : L} {U : Subgroup L}
    (hU : U ≤ Subgroup.centralizer {u}) (hw : w ∈ invXiAut (MulAut.conj u))
    (htop : U ⊔ U.map (MulAut.conj w).toMonoidHom = ⊤) : InvAutGen L (MulAut.conj u) := by
  have hK := centralizer_le_closure_invXiAut_conj ⟨w, hw⟩
  refine eq_top_iff.2 (htop ▸ sup_le (hU.trans hK) ?_)
  rintro _ ⟨y, hy, rfl⟩
  have hwK : w ∈ Subgroup.closure (invXiAut (MulAut.conj u)) := Subgroup.subset_closure hw
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hwK (hU.trans hK hy)) (Subgroup.inv_mem _ hwK)

end CFSG.Quasithin.F7Two
