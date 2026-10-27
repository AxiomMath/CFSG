module

public import CFSG.LieType.Chevalley.ToralCentralizerQuotient

public section

namespace CFSG.StandardType.NTPlane

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem toralCentralizer_cosets_of_index_three
    (τ : Tag) (K : Type) [Field K] (a : Fin τ.rank → Kˣ)
    (h3 : ((kernelReflectionGroup a).subgroupOf (rootCharStabilizerSubgroup a)).index = 3)
    {w : WeylGroup τ} (hw : w ∈ rootCharStabilizerSubgroup a)
    (hwn : w ∉ kernelReflectionGroup a) :
    ∀ g ∈ toralCentralizer τ K a, ∃ i : Fin 3, ∃ m ∈ toralRootGroup τ K a,
      g = m * canonicalRep (coxeterSystem τ) K (w ^ (i : ℕ)) := by
  intro g hg
  obtain ⟨-, hMnorm, -, -, φ, hφ, hφw⟩ :=
    Chevalley_toral_centralizer_root_generated_quotient τ K a
  have hcard : Nat.card (rootCharStabilizerSubgroup a ⧸
      (kernelReflectionGroup a).subgroupOf (rootCharStabilizerSubgroup a)) = 3 := by
    rw [← Subgroup.index_eq_card]; exact h3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set w' : rootCharStabilizerSubgroup a := ⟨w, hw⟩ with hw'
  have hw1 : (QuotientGroup.mk w' : rootCharStabilizerSubgroup a ⧸
      (kernelReflectionGroup a).subgroupOf (rootCharStabilizerSubgroup a)) ≠ 1 := by
    intro h1
    rw [QuotientGroup.eq_one_iff] at h1
    exact hwn (Subgroup.mem_subgroupOf.mp h1)
  have htop := zpowers_eq_top_of_prime_card hcard hw1
  obtain ⟨q, hq⟩ := hφ (QuotientGroup.mk ⟨g, hg⟩)
  have hqmem : q ∈ Subgroup.zpowers (QuotientGroup.mk w' : rootCharStabilizerSubgroup a ⧸
      (kernelReflectionGroup a).subgroupOf (rootCharStabilizerSubgroup a)) := by
    rw [htop]; trivial
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hqmem
  have hord : orderOf (QuotientGroup.mk w' : rootCharStabilizerSubgroup a ⧸
      (kernelReflectionGroup a).subgroupOf (rootCharStabilizerSubgroup a)) = 3 := by
    refine orderOf_eq_prime ?_ hw1
    rw [← hcard]; exact pow_card_eq_one'
  have hk3 : q = (QuotientGroup.mk w' : rootCharStabilizerSubgroup a ⧸
      (kernelReflectionGroup a).subgroupOf (rootCharStabilizerSubgroup a)) ^ ((k % 3).toNat) := by
    rw [← hk, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]
    have := zpow_mod_orderOf (QuotientGroup.mk w' : rootCharStabilizerSubgroup a ⧸
      (kernelReflectionGroup a).subgroupOf (rootCharStabilizerSubgroup a)) k
    rw [hord] at this
    exact_mod_cast this.symm
  have hi : (k % 3).toNat < 3 := by
    have h0 : 0 ≤ k % 3 := Int.emod_nonneg _ (by norm_num)
    have h1 : k % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
    omega
  refine ⟨⟨(k % 3).toNat, hi⟩, ?_⟩
  have hφq : φ q = QuotientGroup.mk ⟨canonicalRep (coxeterSystem τ) K (w ^ ((k % 3).toNat)),
      canonicalRep_mem_toralCentralizer (pow_mem hw _)⟩ := by
    rw [hk3, ← QuotientGroup.mk_pow, hφw]
    rfl
  rw [hφq] at hq
  have hm := QuotientGroup.eq.mp hq
  have hconj := hMnorm.conj_mem _ hm
    ⟨canonicalRep (coxeterSystem τ) K (w ^ ((k % 3).toNat)),
      canonicalRep_mem_toralCentralizer (pow_mem hw _)⟩
  have hmem : g * (canonicalRep (coxeterSystem τ) K (w ^ ((k % 3).toNat)))⁻¹ ∈
      toralRootGroup τ K a := by
    have h1 := Subgroup.mem_subgroupOf.mp hconj
    simpa [mul_assoc] using h1
  exact ⟨_, hmem, (inv_mul_cancel_right g _).symm⟩

end CFSG.StandardType.NTPlane

end
