module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.F7TwoInvBridge

public section

namespace CFSG.Quasithin.F7Two

open CFSG.Assembly.LowTwoRank

theorem exists_psl2_of_statedClassicalModel {L : Type} [Group L] {p f : ℕ}
    (h : StatedClassicalModel L .PSL 2 p f) :
    p.Prime ∧ 1 ≤ f ∧ 4 ≤ p ^ f ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = p ^ f ∧
        Nonempty (L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := by
  obtain ⟨⟨hp, hf1, -, hne2, hne3⟩, K, _, _, hK, ⟨e⟩⟩ := h
  refine ⟨hp, hf1, ?_, K, inferInstance, inferInstance, hK,
    ⟨e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm⟩⟩
  have h2 : 2 ≤ p ^ f := (hp.two_le).trans (Nat.le_self_pow (by omega) p)
  have h22 : p ^ f ≠ 2 := fun h => hne2 (by rw [h])
  have h23 : p ^ f ≠ 3 := fun h => hne3 (by rw [h])
  omega

theorem two_le_of_four_le_two_pow {f : ℕ} (h : 4 ≤ 2 ^ f) : 2 ≤ f := by
  by_contra hf
  have : f ≤ 1 := by omega
  have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) this
  omega

theorem invAutGen_of_mulEquiv_forall {L L' : Type*} [Group L] [Group L'] (e : L ≃* L')
    (h : ∀ φ' : MulAut L', φ' * φ' = 1 → φ' ≠ 1 → InvAutGen L' φ') :
    ∀ φ : MulAut L, φ * φ = 1 → φ ≠ 1 → InvAutGen L φ := by
  intro φ hφ2 hφ1
  let φ' : MulAut L' := (e.symm.trans φ).trans e
  have hφ'apply : ∀ y, φ' y = e (φ (e.symm y)) := fun _ => rfl
  have hφ'2 : φ' * φ' = 1 := by
    refine MulEquiv.ext fun y => ?_
    have h2 : φ (φ (e.symm y)) = e.symm y := by simpa using MulEquiv.congr_fun hφ2 (e.symm y)
    simp only [MulAut.mul_apply, MulAut.one_apply, hφ'apply, MulEquiv.symm_apply_apply, h2,
      MulEquiv.apply_symm_apply]
  have hφ'1 : φ' ≠ 1 := by
    intro h1
    apply hφ1
    refine MulEquiv.ext fun x => ?_
    have h3 := MulEquiv.congr_fun h1 (e x)
    simp only [hφ'apply, MulEquiv.symm_apply_apply, MulAut.one_apply] at h3
    simpa using congrArg e.symm h3
  have h4 := InvAutGen.congr e.symm (h φ' hφ'2 hφ'1)
  have h5 : (e.symm.symm.trans φ').trans e.symm = φ :=
    MulEquiv.ext fun x => by simp [hφ'apply]
  rwa [h5] at h4

end CFSG.Quasithin.F7Two
