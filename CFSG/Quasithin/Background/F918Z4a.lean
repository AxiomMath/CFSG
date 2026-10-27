module

public import CFSG.Quasithin.Background.D2Basic
public import CFSG.Quasithin.Background.F918Z4aMat

public section

namespace CFSG.Quasithin

open scoped Matrix

theorem rkIdx_fixV_swap_ge {V : Type} [CommGroup V] [Finite V] {F : Type} [Field F] [Finite F]
    [CharP F 2] {e d : ℕ} (hF : Nat.card F = 2 ^ e)
    (β : V ≃* Multiplicative (Matrix (Fin d) (Fin d) F)) (ϑ : F ≃+* F)
    (Q R : Matrix (Fin d) (Fin d) F) (hQ : IsUnit Q) (hR : IsUnit R) {s : MulAut V}
    (hs : ∀ v : V, Multiplicative.toAdd (β (s v)) =
      Q * ((Multiplicative.toAdd (β v)).map ϑ)ᵀ * R)
    (hs2 : s * s = 1) :
    d * (d - 1) * e / 2 ≤ rkIdx (fixV (Subgroup.zpowers s)) := by
  classical
  have _ := hR
  have hneg : ∀ M : Matrix (Fin d) (Fin d) F, -M = M := fun M => by
    ext i j; simp [CharTwo.neg_eq]
  have hV2 : ∀ v : V, v ^ 2 = 1 := by
    intro v
    apply β.injective
    rw [map_pow, map_one]
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, two_nsmul]
    nth_rewrite 2 [← hneg (Multiplicative.toAdd (β v))]
    exact add_neg_cancel _
  set τ : Matrix (Fin d) (Fin d) F → Matrix (Fin d) (Fin d) F := swapMap ϑ Q R with hτ
  have hs' : ∀ v : V, Multiplicative.toAdd (β (s v)) = τ (Multiplicative.toAdd (β v)) := hs
  have hτ2 : ∀ M, τ (τ M) = M := by
    intro M
    obtain ⟨v, hv⟩ : ∃ v : V, Multiplicative.toAdd (β v) = M :=
      ⟨β.symm (Multiplicative.ofAdd M), by simp⟩
    have hss : s (s v) = v := by
      have := congrArg (fun t : MulAut V => t v) hs2
      simpa using this
    rw [← hv, ← hs', ← hs', hss]
  let φ : V →* V := MonoidHom.mk' (fun v => s v * v⁻¹) (by
    intro a b
    simp only [map_mul, mul_inv]
    exact mul_mul_mul_comm _ _ _ _)
  have hker : fixV (Subgroup.zpowers s) ≤ φ.ker := by
    intro v hv
    have hsv : s v = v := mem_fixV.1 hv s (Subgroup.mem_zpowers s)
    rw [MonoidHom.mem_ker]
    show s v * v⁻¹ = 1
    rw [hsv, mul_inv_cancel]
  have hrange : Nat.card F ^ (d * (d - 1) / 2) ≤ Nat.card φ.range := by
    refine (card_range_one_add_swap ϑ Q R hQ hτ2).trans ?_
    have hmem : ∀ M ∈ Set.range (fun M : Matrix (Fin d) (Fin d) F => M + τ M),
        β.symm (Multiplicative.ofAdd M) ∈ φ.range := by
      rintro _ ⟨M, rfl⟩
      refine ⟨β.symm (Multiplicative.ofAdd M), ?_⟩
      have h1 : Multiplicative.toAdd (β (s (β.symm (Multiplicative.ofAdd M)))) = τ M := by
        rw [hs']; simp
      apply β.injective
      apply Multiplicative.toAdd.injective
      simp only [φ, MonoidHom.mk'_apply, map_mul, map_inv, MulEquiv.apply_symm_apply, toAdd_mul,
        toAdd_inv, toAdd_ofAdd, h1, hneg]
      exact add_comm _ _
    let g : Set.range (fun M : Matrix (Fin d) (Fin d) F => M + τ M) → φ.range :=
      fun x => ⟨_, hmem x.1 x.2⟩
    refine Nat.card_le_card_of_injective g ?_
    intro x y hxy
    apply Subtype.ext
    have h : β.symm (Multiplicative.ofAdd x.1) = β.symm (Multiplicative.ofAdd y.1) :=
      congrArg Subtype.val hxy
    exact Multiplicative.ofAdd.injective (β.symm.injective h)
  have hidx : rkIdx φ.ker = rk φ.range := by
    unfold rkIdx rk
    rw [Subgroup.index_ker]
  have hcard : Nat.card φ.range = 2 ^ rk φ.range := card_eq_two_pow hV2 φ.range
  have hexp : e * (d * (d - 1) / 2) ≤ rk φ.range := by
    have h := hrange
    rw [hF, hcard, ← pow_mul] at h
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h
  have harith : d * (d - 1) * e / 2 = e * (d * (d - 1) / 2) := by
    obtain ⟨k, hk⟩ := Nat.even_mul_pred_self d
    rw [hk]
    have h1 : (k + k) * e = 2 * (k * e) := by ring
    have h2 : (k + k) / 2 = k := by omega
    rw [h1, h2, Nat.mul_div_cancel_left _ (by norm_num), mul_comm]
  calc d * (d - 1) * e / 2 = e * (d * (d - 1) / 2) := harith
    _ ≤ rk φ.range := hexp
    _ = rkIdx φ.ker := hidx.symm
    _ ≤ rkIdx (fixV (Subgroup.zpowers s)) := rkIdx_anti hker

end CFSG.Quasithin
