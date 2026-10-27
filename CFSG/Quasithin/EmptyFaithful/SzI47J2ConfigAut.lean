module

public import CFSG.Quasithin.SteinbergCBAlternatingAut

public section

namespace CFSG.Quasithin.SzI47J2C

open Equiv

theorem exists_inner_of_odd_pow_eq_one {G : Type*} [Group G] {M : Subgroup G}
    (e : ↥M ≃* alternatingGroup (Fin 5)) {y : G} (hy : ∀ m ∈ M, y * m * y⁻¹ ∈ M) {n : ℕ}
    (hn : Odd n) (hyn : y ^ n = 1) : ∃ m₀ ∈ M, ∀ m ∈ M, y * m * y⁻¹ = m₀ * m * m₀⁻¹ := by
  have : Finite ↥M := Finite.of_equiv _ e.symm.toEquiv
  have : Finite ↥(M : Set G) := inferInstanceAs (Finite ↥M)
  have hyN : y ∈ Subgroup.normalizer (M : Set G) := Subgroup.mem_normalizer_fintype hy
  set θ : MulAut ↥M := M.normalizerMonoidHom ⟨y, hyN⟩ with hθ
  have hθapply : ∀ m : ↥M, ((θ m : ↥M) : G) = y * m * y⁻¹ := fun m => rfl
  have hθn : θ ^ n = 1 := by
    rw [hθ, ← map_pow]
    have h1 : (⟨y, hyN⟩ : ↥(Subgroup.normalizer (M : Set G))) ^ n = 1 :=
      Subtype.ext (by simpa using hyn)
    rw [h1, map_one]
  set φ : MulAut (alternatingGroup (Fin 5)) := MulAut.congr e θ with hφ
  have hφn : φ ^ n = 1 := by rw [hφ, ← map_pow, hθn, map_one]
  obtain ⟨σ, hσ⟩ := SteinbergCB.conjPerm_surjective (n := 5) (Or.inl rfl) φ
  have hσn : σ ^ n = 1 := by
    apply SteinbergCB.conjPerm_injective (n := 5) (by norm_num)
    rw [map_pow, hσ, hφn, map_one]
  have hsign : Perm.sign σ = 1 := by
    have h1 : (Perm.sign σ) ^ n = 1 := by rw [← map_pow, hσn, map_one]
    rcases Int.units_eq_one_or (Perm.sign σ) with h | h
    · exact h
    · rw [h, Odd.neg_one_pow hn] at h1
      exact absurd h1 (by decide)
  set σ' : alternatingGroup (Fin 5) := ⟨σ, Perm.mem_alternatingGroup.mpr hsign⟩ with hσ'
  refine ⟨((e.symm σ' : ↥M) : G), (e.symm σ').2, fun m hm => ?_⟩
  have hφapply : ∀ a : alternatingGroup (Fin 5), φ a = σ' * a * σ'⁻¹ := fun a => by
    apply Subtype.ext
    rw [← hσ, SteinbergCB.conjPerm_apply]
    rfl
  have key : θ ⟨m, hm⟩ = e.symm σ' * ⟨m, hm⟩ * (e.symm σ')⁻¹ := by
    apply e.injective
    have h1 : φ (e ⟨m, hm⟩) = e (θ ⟨m, hm⟩) := by
      rw [hφ, MulAut.congr_apply]
      simp
    rw [← h1, hφapply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have := congrArg Subtype.val key
  simpa [hθapply] using this

end CFSG.Quasithin.SzI47J2C
