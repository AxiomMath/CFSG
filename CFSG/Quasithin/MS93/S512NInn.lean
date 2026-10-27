module

public import CFSG.Quasithin.MS93.MSPSix
public import CFSG.Quasithin.MS93.MSPLevi

public section

namespace CFSG.Quasithin.MS93.S512N

open Matrix CFSG.Assembly.LowTwoRank MSP

variable {F : Type} [Field F]

theorem transv_zero_vec (c : F) : transv (0 : V4 F) c = 1 :=
  ext_mulVec fun v => by rw [transv_mulVec, smul_zero, add_zero, mat_one, one_mulVec]

theorem transv_one_eq_one_iff {w : V4 F} : transv w 1 = 1 ↔ w = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ transv_zero_vec 1⟩
  by_contra hw
  exact one_ne_zero (transv_injective hw (h.trans (transv_zero w).symm))

theorem commute_transv_iff [CharP F 2] (u v : V4 F) :
    transv u 1 * transv v 1 = transv v 1 * transv u 1 ↔ form F u v = 0 := by
  constructor
  · intro h
    by_cases hu : u = 0
    · subst hu
      simp
    by_cases hv : v = 0
    · subst hv
      simp
    have h1 := mulVec_eq_of_commute_transv hv h
    rw [transv_mulVec, one_mul] at h1
    have h2 : form F u v • u = 0 := by
      have := congrArg (· - v) h1
      simpa using this
    exact (smul_eq_zero.1 h2).resolve_right hu
  · intro h
    have h1 : mat (transv u 1) *ᵥ v = v := by rw [transv_mulVec, h, mul_zero, zero_smul, add_zero]
    have h2 := transv_conj (transv u 1) v 1
    rw [h1] at h2
    calc transv u 1 * transv v 1 = transv u 1 * transv v 1 * (transv u 1)⁻¹ * transv u 1 := by
          group
      _ = transv v 1 * transv u 1 := by rw [h2]

theorem exists_eq_conj_of_transv (hF : Nat.card F = 2) (τ : Sp4 F ≃* Sp4 F) {v₀ w₀ : V4 F}
    (hv₀ : v₀ ≠ 0) (hτ : τ (transv v₀ 1) = transv w₀ 1) :
    ∃ ψ : Sp4 F, ∀ x, τ x = ψ * x * ψ⁻¹ := by
  obtain ⟨c⟩ := nonempty_ringEquiv_of_card_two hF
  have : CharP F 2 := charP_of_ringEquiv c
  have : Finite F := Nat.finite_of_card_ne_zero (by omega)
  have hex : ∀ v : V4 F, ∃ w : V4 F, τ (transv v 1) = transv w 1 := by
    intro v
    by_cases hv : v = 0
    · exact ⟨0, by rw [hv, transv_zero_vec, map_one]⟩
    obtain ⟨g, hg⟩ := exists_mulVec_e₂_eq c hv
    obtain ⟨g₀, hg₀⟩ := exists_mulVec_e₂_eq c hv₀
    obtain ⟨y, hy⟩ : ∃ y : Sp4 F, mat y *ᵥ v₀ = v :=
      ⟨g * g₀⁻¹, by rw [mat_mul_mulVec, ← hg₀, mat_inv_mulVec, hg]⟩
    have e1 : transv v 1 = y * transv v₀ 1 * y⁻¹ := by rw [transv_conj, hy]
    refine ⟨mat (τ y) *ᵥ w₀, ?_⟩
    rw [e1, map_mul, map_mul, map_inv, hτ, transv_conj]
  choose π hπ using hex
  have hπ0 : ∀ v, π v = 0 ↔ v = 0 := fun v => by
    rw [← transv_one_eq_one_iff, ← hπ, MulEquiv.map_eq_one_iff, transv_one_eq_one_iff]
  have hinj : Function.Injective π := by
    intro u v huv
    by_cases hv : v = 0
    · rw [(hπ0 u).1 (huv.trans ((hπ0 v).2 hv)), hv]
    · have h1 : τ (transv u 1) = τ (transv v 1) := by rw [hπ, hπ, huv]
      exact (transv_eq_transv_iff hv).1 (τ.injective h1)
  have hsurj : Function.Surjective π := Finite.injective_iff_surjective.1 hinj
  have hform : ∀ u v, form F (π u) (π v) = form F u v := by
    intro u v
    have key : form F (π u) (π v) = 0 ↔ form F u v = 0 := by
      rw [← commute_transv_iff, ← commute_transv_iff, ← hπ, ← hπ]
      constructor
      · intro h
        exact τ.injective (by rw [map_mul, map_mul, h])
      · intro h
        rw [← map_mul, ← map_mul, h]
    rcases eq_zero_or_eq_one_of_ringEquiv c (form F u v) with h | h
    · rw [h, key.2 h]
    · rcases eq_zero_or_eq_one_of_ringEquiv c (form F (π u) (π v)) with h' | h'
      · exact absurd (h.symm.trans (key.1 h')) one_ne_zero
      · rw [h, h']
  have hadd : ∀ u v, π (u + v) = π u + π v := by
    intro u v
    refine sub_eq_zero.1 (form_nondegenerate.1 _ fun y => ?_)
    obtain ⟨x, rfl⟩ := hsurj y
    simp only [map_sub, map_add, LinearMap.sub_apply, LinearMap.add_apply, hform, sub_self]
  have hsmul : ∀ (a : F) (v : V4 F), π (a • v) = a • π v := by
    intro a v
    rcases eq_zero_or_eq_one_of_ringEquiv c a with rfl | rfl
    · rw [zero_smul, zero_smul, (hπ0 0).2 rfl]
    · rw [one_smul, one_smul]
  set P : V4 F →ₗ[F] V4 F := { toFun := π, map_add' := hadd, map_smul' := hsmul } with hP
  set e : V4 F ≃ₗ[F] V4 F := LinearEquiv.ofBijective P ⟨hinj, hsurj⟩ with he
  set A := LinearMap.toMatrix' (e : V4 F →ₗ[F] V4 F) with hA
  set B := LinearMap.toMatrix' (e.symm : V4 F →ₗ[F] V4 F) with hB
  have hAv : ∀ v, A *ᵥ v = π v := fun v => LinearMap.toMatrix'_mulVec _ v
  have hBv : ∀ v, B *ᵥ v = e.symm v := fun v => LinearMap.toMatrix'_mulVec _ v
  have hAB : A * B = 1 := mat_ext_mulVec fun v => by
    rw [← mulVec_mulVec, hBv, hAv, one_mulVec]
    exact e.apply_symm_apply v
  have hBA : B * A = 1 := mat_ext_mulVec fun v => by
    rw [← mulVec_mulVec, hAv, hBv, one_mulVec]
    exact e.symm_apply_apply v
  have hAform : ∀ u v, form F (A *ᵥ u) (A *ᵥ v) = form F u v := fun u v => by
    rw [hAv, hAv, hform]
  set ψ : Sp4 F := ofMat A B hAB hBA hAform with hψ
  have hψv : ∀ v, mat ψ *ᵥ v = π v := fun v => by rw [hψ, mat_ofMat, hAv]
  have h1 : ∀ (v : V4 F) (a : F), τ (transv v a) = ψ * transv v a * ψ⁻¹ := by
    intro v a
    rcases eq_zero_or_eq_one_of_ringEquiv c a with rfl | rfl
    · rw [transv_zero, map_one, mul_one, mul_inv_cancel]
    · rw [transv_conj, hψv, hπ]
  set G₀ : Subgroup (Sp4 F) := τ.toMonoidHom.eqLocus (MulAut.conj ψ).toMonoidHom with hG₀
  have hmem : ∀ x, x ∈ G₀ ↔ τ x = ψ * x * ψ⁻¹ := fun x => Iff.rfl
  have htop : G₀ = ⊤ := eq_top_of_five G₀ (fun a => (hmem _).2 (h1 _ a))
    (fun a => (hmem _).2 (h1 _ a)) (fun a => (hmem _).2 (h1 _ a)) (fun a => (hmem _).2 (h1 _ a))
    (fun a => (hmem _).2 (h1 _ a))
  exact ⟨ψ, fun x => (hmem x).1 (htop ▸ Subgroup.mem_top x)⟩

end CFSG.Quasithin.MS93.S512N
