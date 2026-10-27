module

public import CFSG.LocalAnalysis.UniquenessCase.FundamentalLie
import CFSG.ClassicalInvolution.ModelFacts.FundamentalSL2All

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.LocalAnalysis.UniquenessCase (IsFundamentalOver)
open CFSG.ClassicalInvolution.ModelFacts
  (nonempty_equiv_sl2_galoisField_of_mem_fundamentalSubgroups)


private theorem range_comp_symm {M X F : Type} [Group M] [Group X] [Field F] (ψ : M →* X)
    {R : Subgroup M} (φ : ↥R ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    (ψ.comp (R.subtype.comp φ.symm.toMonoidHom)).range = R.map ψ := by
  rw [MonoidHom.range_comp, MonoidHom.range_comp, MonoidHom.range_eq_top.2 φ.symm.surjective,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype]

private theorem ker_comp_symm_le {M X F : Type} [Group M] [Group X] [Field F] (ψ : M →* X)
    (hker : ψ.ker ≤ Subgroup.center M) {R : Subgroup M}
    (φ : ↥R ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    (ψ.comp (R.subtype.comp φ.symm.toMonoidHom)).ker ≤
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  have hc := Subgroup.mem_center_iff.mp (hker hx) ((φ.symm y : ↥R) : M)
  apply φ.symm.injective
  apply Subtype.ext
  simpa [map_mul] using hc

theorem exists_sl2_cover_of_isFundamentalOver {X : Type} [Group X] {q : ℕ} {K : Subgroup X}
    (hK : IsFundamentalOver q K) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (r : ℕ), r.Prime ∧ CharP F r ∧ r ∣ q ∧
      (2 : F) ≠ 0 ∧ q ≤ Nat.card F ∧
      ∃ φ : Matrix.SpecialLinearGroup (Fin 2) F →* X, φ.range = K ∧
        φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
  obtain ⟨t, n, p, e, hp, hp2, hq, hfund, hadm, ψ, -, hker, R, hR, rfl⟩ := hK
  have : Fact p.Prime := ⟨hp⟩
  have he : 1 ≤ e := hadm.2.1
  have h2 : ∀ e' : ℕ, (2 : GaloisField p e') ≠ 0 := fun e' h => by
    have h2 : ((2 : ℕ) : GaloisField p e') = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff (GaloisField p e') p] at h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
  have hpq : p ∣ q := hq ▸ dvd_pow_self p (by omega)
  rcases nonempty_equiv_sl2_galoisField_of_mem_fundamentalSubgroups hp2 hfund hadm hR with
    hφ | ⟨-, hφ⟩
  · obtain ⟨φ⟩ := hφ
    refine ⟨GaloisField p e, inferInstance, inferInstance, p, hp, inferInstance, hpq, h2 e, ?_,
      _, range_comp_symm ψ φ, ker_comp_symm_le ψ hker φ⟩
    rw [GaloisField.card p e (by omega), hq]
  · obtain ⟨φ⟩ := hφ
    refine ⟨GaloisField p (3 * e), inferInstance, inferInstance, p, hp, inferInstance, hpq,
      h2 _, ?_, _, range_comp_symm ψ φ, ker_comp_symm_le ψ hker φ⟩
    rw [GaloisField.card p (3 * e) (by omega), hq]
    exact Nat.pow_le_pow_right hp.pos (by omega)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
