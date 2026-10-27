module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusNFWeyl

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin
open CFSG.StandardType

theorem exists_omqnfRealizes_of_signedPerm {m : ℕ} (π : Equiv.Perm (Fin m)) {s : Fin m → ℤ}
    (hs : SpIsSign s) :
    ∃ w : (coxeterMatrix (isFiniteType_cartanB m)).Group, omqnfRealizes m w π s := by
  rcases m with _ | r
  · have hπ : π = 1 := Subsingleton.elim _ _
    have hs' : s = 1 := Subsingleton.elim _ _
    subst hπ hs'
    exact ⟨1, omqnfRealizes_one 0⟩
  · let W := (coxeterMatrix (isFiniteType_cartanB (r + 1))).Group
    have hmem_gen : ∀ σ : Equiv.Perm (Fin (r + 1)),
        σ ∈ Submonoid.closure (Set.range fun i : Fin r => Equiv.swap i.castSucc i.succ) := by
      intro σ
      rw [Equiv.Perm.mclosure_swap_castSucc_succ r]
      exact Submonoid.mem_top σ
    have hperm : ∀ σ : Equiv.Perm (Fin (r + 1)), ∃ w : W, omqnfRealizes (r + 1) w σ 1 := by
      intro σ
      refine Submonoid.closure_induction
        (motive := fun σ _ => ∃ w : W, omqnfRealizes (r + 1) w σ 1) ?_ ?_ ?_ (hmem_gen σ)
      · rintro x ⟨i, rfl⟩
        have hlt : i.castSucc.val + 1 < r + 1 := by
          simp only [Fin.val_castSucc]; omega
        have he : (⟨i.castSucc.val + 1, hlt⟩ : Fin (r + 1)) = i.succ := Fin.ext (by simp)
        exact ⟨_, (omqnfRealizes_simple_of_lt (m := r + 1) hlt).congr (by rw [he]) rfl⟩
      · exact ⟨1, omqnfRealizes_one _⟩
      · rintro x y hx hy ⟨w₁, h₁⟩ ⟨w₂, h₂⟩
        exact ⟨w₁ * w₂, (h₁.mul h₂).congr rfl (by funext c; simp)⟩
    have hsgn : ∀ a : Fin (r + 1), ∃ w : W, omqnfRealizes (r + 1) w 1 (spSgn a) := by
      intro a
      let k : Fin (r + 1) := ⟨r, by omega⟩
      have hk : ¬ k.val + 1 < r + 1 := by simp [k]
      obtain ⟨w₁, h₁⟩ := hperm (Equiv.swap k a)
      have hk' := omqnfRealizes_simple_of_not_lt (m := r + 1) hk
      refine ⟨w₁ * (coxeterMatrix (isFiniteType_cartanB (r + 1))).toCoxeterSystem.simple k *
        w₁⁻¹, ?_⟩
      refine (((h₁.mul hk').mul (h₁.inv spIsSign_one))).congr ?_ ?_
      · rw [mul_one, mul_inv_cancel]
      · funext c
        have e : (Equiv.swap k a).symm c = Equiv.swap k a c := by rw [Equiv.symm_swap]
        simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply, Pi.one_apply, mul_one, one_mul, e,
          Equiv.Perm.inv_def, Equiv.symm_swap, Equiv.Perm.coe_one, id_eq]
        unfold spSgn
        have hiff : Equiv.swap k a c = k ↔ c = a := by
          rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]
        simp only [hiff]
    have hsign : ∀ T : Finset (Fin (r + 1)), ∃ w : W, omqnfRealizes (r + 1) w 1 (spSgnOn T) := by
      intro T
      induction T using Finset.induction_on with
      | empty => exact ⟨1, (omqnfRealizes_one _).congr rfl (by funext c; simp [spSgnOn])⟩
      | insert a T ha ih =>
        obtain ⟨w, hw⟩ := ih
        obtain ⟨w', hw'⟩ := hsgn a
        refine ⟨w' * w, (hw'.mul hw).congr (mul_one 1) ?_⟩
        funext c
        simp only [Equiv.Perm.one_apply, Pi.one_apply]
        unfold spSgnOn spSgn
        by_cases hca : c = a
        · subst hca
          simp [ha]
        · by_cases hcT : c ∈ T <;> simp [hca, hcT]
    obtain ⟨w₁, h₁⟩ := hperm π
    obtain ⟨w₂, h₂⟩ := hsign (Finset.univ.filter fun a => s a = -1)
    refine ⟨w₁ * w₂, (h₁.mul h₂).congr (mul_one π) ?_⟩
    funext c
    simp only [Equiv.Perm.one_apply, Pi.one_apply, mul_one]
    unfold spSgnOn
    rcases hs c with h | h <;> simp [h]

end CFSG.LocalAnalysis.WeakClosure81
