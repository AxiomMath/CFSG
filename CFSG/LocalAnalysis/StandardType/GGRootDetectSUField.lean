module

public import CFSG.LocalAnalysis.StandardType.GGRootDetectCore

public section

namespace CFSG.StandardType

namespace RootDetectSU

section Field

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

theorem fixed_of_mul_conj {E M M' : Matrix ι ι K} (hE : E ≠ 0) (hMM' : M * M' = 1)
    {φ : K ≃+* K} {T : Set K} (h1 : (1 : K) ∈ T)
    (h : ∀ t ∈ T, (1 + t • E) * M = M * (1 + φ t • E)) : ∀ t ∈ T, φ t = t := by
  have hs : ∀ t ∈ T, t • (E * M) = φ t • (M * E) := by
    intro t ht
    have h2 := h t ht
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul] at h2
    exact add_left_cancel h2
  have hc : E * M = M * E := by simpa using hs 1 h1
  have hEM : E * M ≠ 0 := by
    intro h0
    apply hE
    calc E = E * M * M' := by rw [Matrix.mul_assoc, hMM', Matrix.mul_one]
      _ = 0 := by rw [h0, Matrix.zero_mul]
  intro t ht
  have h3 : (t - φ t) • (E * M) = 0 := by rw [sub_smul, hs t ht, hc, sub_self]
  rcases smul_eq_zero.mp h3 with h4 | h4
  · exact (sub_eq_zero.mp h4).symm
  · exact absurd h4 hEM

omit [Fintype ι] [DecidableEq ι] in
theorem eq_one_of_fixed_of_pow_eq_one {σ φ : K ≃+* K} (hσ : ∀ x, σ (σ x) = x)
    (hcomm : ∀ x, φ (σ x) = σ (φ x)) (hfix : ∀ x, σ x = x → φ x = x) {p : ℕ} (hp : Odd p)
    (hφp : φ ^ p = 1) : φ = 1 := by
  have hsq : φ * φ = 1 := by
    refine RingEquiv.ext fun x => ?_
    show φ (φ x) = x
    have hs : φ (x + σ x) = x + σ x := hfix _ (by rw [map_add, hσ, add_comm])
    have hm : φ (x * σ x) = x * σ x := hfix _ (by rw [map_mul, hσ, mul_comm])
    have e : φ x * φ x - φ (x + σ x) * φ x + φ (x * σ x) = 0 := by
      rw [← map_mul, ← map_mul, ← map_sub, ← map_add]
      have h0 : x * x - (x + σ x) * x + x * σ x = 0 := by ring
      rw [h0, map_zero]
    rw [hs, hm] at e
    have hroot : (φ x - x) * (φ x - σ x) = 0 := by linear_combination e
    rcases mul_eq_zero.mp hroot with h | h
    · have hx : φ x = x := sub_eq_zero.mp h
      rw [hx, hx]
    · have hx : φ x = σ x := sub_eq_zero.mp h
      rw [hx, hcomm, hx, hσ]
  obtain ⟨k, rfl⟩ := hp
  have hpow : φ ^ (2 * k + 1) = φ := by
    rw [pow_succ, pow_mul, sq, hsq, one_pow, one_mul]
  rw [← hpow, hφp]

theorem eq_of_inv_mul_eq_scalar [CharP K 2] [Nonempty ι] {M M' : GL ι K} {c : Kˣ}
    (h : M⁻¹ * M' = Matrix.GeneralLinearGroup.scalar ι c) (hM : M * M = 1)
    (hM' : M' * M' = 1) : M' = M := by
  have hcomm : ∀ g : GL ι K, g * Matrix.GeneralLinearGroup.scalar ι c =
      Matrix.GeneralLinearGroup.scalar ι c * g := fun g => Units.ext (by
    rw [Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
    exact ((Matrix.scalar_commute (c : K) (fun r => Commute.all _ r)
      (g : Matrix ι ι K)).eq).symm)
  have hM'eq : M' = M * Matrix.GeneralLinearGroup.scalar ι c := by rw [← h, mul_inv_cancel_left]
  set s := Matrix.GeneralLinearGroup.scalar ι c with hs
  have hsq : Matrix.GeneralLinearGroup.scalar ι (c * c) = 1 := by
    calc Matrix.GeneralLinearGroup.scalar ι (c * c) = M * M * (s * s) := by
          rw [hM, one_mul, map_mul]
      _ = M * (M * s) * s := by group
      _ = M * (s * M) * s := by rw [hcomm M]
      _ = M * s * (M * s) := by group
      _ = 1 := by rw [← hM'eq, hM']
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hc : (c : K) * c = 1 := by
    have e := congrArg (fun g : GL ι K => (g : Matrix ι ι K) i i) hsq
    simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using e
  have hc1 : c = 1 := Units.ext (HypSixTypeA.eq_one_of_mul_self_eq_one hc)
  rw [hM'eq, hs, hc1, map_one, mul_one]

end Field

section Quotient

variable {S G : Type*} [Group S] [Group G] {N : Subgroup S} [N.Normal] {ψ : S →* G}

theorem conj_eq_of_quotAut_eq (hN : N = Subgroup.center S)
    (hperf : ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ = ⊤) {c : G}
    (hc : c ∈ Subgroup.normalizer (ψ.range : Set G)) {α : MulAut (S ⧸ N)}
    (hα : ∀ y y' : S, ψ y' = c⁻¹ * ψ y * c → α (y : S ⧸ N) = (y' : S ⧸ N)) {a : S}
    {β : S →* S} (ha : ∀ y : S, α (y : S ⧸ N) = ((a * β y * a⁻¹ : S) : S ⧸ N)) (y : S) :
    (c * ψ a)⁻¹ * ψ y * (c * ψ a) = ψ (β y) := by
  have hratio : ∀ w, ∃ s ∈ Subgroup.center S,
      (ψ (β w))⁻¹ * ((c * ψ a)⁻¹ * ψ w * (c * ψ a)) = ψ s := by
    intro w
    obtain ⟨w', hw'⟩ := RootDetect.exists_conj_preimage hc w
    have hq : ((a * β w * a⁻¹ : S) : S ⧸ N) = (w' : S ⧸ N) := by
      rw [← ha w]
      exact hα w w' hw'
    have hs : (a * β w * a⁻¹)⁻¹ * w' ∈ Subgroup.center S := by
      rw [← hN]
      exact QuotientGroup.eq.mp hq
    obtain ⟨s, hsdef⟩ : ∃ s, s = (a * β w * a⁻¹)⁻¹ * w' := ⟨_, rfl⟩
    rw [← hsdef] at hs
    have hw's : w' = a * β w * a⁻¹ * s := by rw [hsdef]; group
    have hs' : a⁻¹ * s * a = s := by
      rw [mul_assoc, ← Subgroup.mem_center_iff.mp hs a, inv_mul_cancel_left]
    refine ⟨s, hs, ?_⟩
    calc (ψ (β w))⁻¹ * ((c * ψ a)⁻¹ * ψ w * (c * ψ a)) =
        (ψ (β w))⁻¹ * ((ψ a)⁻¹ * (c⁻¹ * ψ w * c) * ψ a) := by group
      _ = ψ ((β w)⁻¹ * (a⁻¹ * w' * a)) := by
        rw [← hw', map_mul, map_mul, map_mul, map_inv, map_inv]
      _ = ψ s := by
        rw [hw's]
        congr 1
        calc (β w)⁻¹ * (a⁻¹ * (a * β w * a⁻¹ * s) * a) = a⁻¹ * s * a := by group
          _ = s := hs'
  have heq := HypSixTypeA.eq_of_inv_mul_comm hperf (H := ψ.range) (ψ.comp β)
    ((MulAut.conj (c * ψ a)⁻¹).toMonoidHom.comp ψ) (fun w => ⟨β w, rfl⟩)
    (fun w => by
      obtain ⟨w', hw'⟩ := RootDetect.exists_conj_preimage hc w
      refine ⟨a⁻¹ * w' * a, ?_⟩
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      rw [map_mul, map_mul, map_inv, hw']
      group)
    (fun w k hk => by
      obtain ⟨s, hs, hsw⟩ := hratio w
      obtain ⟨v, rfl⟩ := hk
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      rw [hsw, ← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hs v])
  have h1 := congrArg (fun φ : S →* G => φ y) heq
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h1
  exact h1.symm

end Quotient

end RootDetectSU

end CFSG.StandardType
