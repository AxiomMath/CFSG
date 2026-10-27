module

public import CFSG.LocalAnalysis.StandardType.GGTBJNoRankOneDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l48nD_lift_unique {R : Type} [Group R] {L' : Type} [Group L'] {ψ : L' →* R}
    (hψ : Function.Surjective ψ) {c : MulAut L'} {φ φ' : MulAut R}
    (hφ : ∀ l : L', φ (ψ l) = ψ (c l)) (hφ' : ∀ l : L', φ' (ψ l) = ψ (c l)) : φ = φ' := by
  refine MulEquiv.ext fun r => ?_
  obtain ⟨l, rfl⟩ := hψ r
  rw [hφ, hφ']

private theorem l48nD_order_three {R : Type} [Group R] {L' : Type} [Group L'] {ψ : L' →* R}
    (hψ : Function.Surjective ψ) {e : MulAut L'} (he3 : e ^ 3 = 1) {t : MulAut R}
    (ht : ∀ l : L', t (ψ l) = ψ (e l)) : t ^ 3 = 1 := by
  apply l48nD_lift_unique hψ (c := (1 : MulAut L'))
  · intro l
    have h : ∀ k : ℕ, (t ^ k) (ψ l) = ψ ((e ^ k) l) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => simp only [pow_succ', MulAut.mul_apply, ih, ht]
    rw [h 3, he3]
  · intro l
    rfl

theorem ggRankOne_su6_cases_at {R : Type} [Group R] {I : Set (MulAut R)}
    (hb : GGSU6DiagInvertedAt I) {L' : Type} [Group L'] [Finite L'] (ψ : L' →* R)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {e : MulAut L'} {J : Subgroup L'} {n : ℕ} {a : MulAut L'} (hset : GGRankOneSetup I ψ 3 e J n a)
    (houter : ¬ ∃ r : R, ∀ l : L', ψ (e l) = r * ψ l * r⁻¹)
    (hc : ∀ A : Subgroup (MulAut L'), IsElemAbelian 3 A → Nat.card A = 3 ^ 3 → e ∈ A → a ∈ A →
      (∀ c ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (c l)) →
      (∀ c ∈ A, ∀ j ∈ J, c j ∈ J) →
      ∀ V : Subgroup (MulAut R), V ≠ ⊥ → IsPGroup 2 V → V ≤ Subgroup.closure I →
        ¬ ∀ c ∈ A, ∀ φ : MulAut R, (∀ l : L', φ (ψ l) = ψ (c l)) →
            ∀ v ∈ V, φ * v * φ⁻¹ ∈ V)
    (A : Subgroup (MulAut L'))
    (hA : IsElemAbelian 3 A) (hAcard : Nat.card A = 3 ^ 3) (he : e ∈ A) (ha : a ∈ A)
    (hAI : ∀ c ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (c l)) (hAJ : ∀ c ∈ A, ∀ j ∈ J, c j ∈ J)
    (U : Subgroup (MulAut R)) (hU1 : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hAU : ∀ c ∈ A, ∀ φ : MulAut R, (∀ l : L', φ (ψ l) = ψ (c l)) → ∀ u ∈ U, φ * u * φ⁻¹ ∈ U) :
    False := by
  obtain ⟨t, htI, ht⟩ := hset.2.2.2.2.1
  have ht3 : t ^ 3 = 1 := l48nD_order_three hψ hset.2.2.2.1 ht
  have htOut : t ∉ LargeEvenInnSet R := by
    intro hmem
    simp only [LargeEvenInnSet, Set.mem_range] at hmem
    obtain ⟨r, hr⟩ := hmem
    apply houter
    refine ⟨r, fun l => ?_⟩
    rw [← ht l, ← hr, MulAut.conj_apply]
  by_cases hdisj : U ⊓ Subgroup.closure I = ⊥
  · exact (hb t htI ht3 htOut U hU1 hU2 hdisj) (hAU e he t ht)
  · refine (hc A hA hAcard he ha hAI hAJ
      (U ⊓ Subgroup.closure I) hdisj (hU2.to_le inf_le_left) inf_le_right) ?_
    intro c hcA φ hφ v hv
    have hφI : φ ∈ Subgroup.closure I := by
      obtain ⟨φ', hφ'I, hφ'⟩ := hAI c hcA
      rw [← l48nD_lift_unique hψ hφ' hφ]
      exact Subgroup.subset_closure hφ'I
    exact ⟨hAU c hcA φ hφ v hv.1,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hφI hv.2) (Subgroup.inv_mem _ hφI)⟩

end CFSG.StandardType

end
