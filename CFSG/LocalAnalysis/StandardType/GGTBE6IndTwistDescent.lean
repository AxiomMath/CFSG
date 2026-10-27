module

public import CFSG.LocalAnalysis.StandardType.GGTBE6IndTwistCover
public import CFSG.LocalAnalysis.StandardType.GGTBE6IndTwistDiagonal
public import TauCeti.GroupTheory.QuotientGroup.MulAut

public noncomputable section

namespace CFSG.StandardType.TBE6IndTwist

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.CentralExt
  CFSG.StandardType.TwE6Lang


variable {K L : Type} [Field K] [Finite K] [CharP K 2] [Group L] [Finite L]

theorem ker_characteristic {f : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2)
    (θ : K ≃+* K) (hθq : ∀ c, θ c = c ^ (2 ^ f))
    (φ : fixedGroup K θ.toRingHom →* L)
    (hφc : φ.ker ≤ Subgroup.center (fixedGroup K θ.toRingHom)) : φ.ker.Characteristic := by
  have hZ : Nat.card (Subgroup.center (fixedGroup K θ.toRingHom)) ∣ 3 := by
    rw [(TwistedE6Closed.card_center_fixedGroup hK (fun c => hθq c)).1]
    exact Nat.gcd_dvd_left _ _
  have hk : φ.ker = ⊥ ∨ φ.ker = Subgroup.center (fixedGroup K θ.toRingHom) := by
    have hd := (Subgroup.card_dvd_of_le hφc).trans hZ
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
    · left
      exact Subgroup.eq_bot_of_card_le (H := φ.ker) (by rw [h])
    · right
      apply Subgroup.eq_of_le_of_card_ge hφc
      rw [h]
      exact Nat.le_of_dvd (by decide : 0 < 3) hZ
  rcases hk with h | h <;> rw [h] <;> infer_instance

theorem exists_diagonal_descent {f : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2)
    (θ : K ≃+* K) (hθq : ∀ c, θ c = c ^ (2 ^ f))
    (hθ : ∀ c, θ.toRingHom (θ.toRingHom c) = c) (l : K) (hl : θ.toRingHom l = l + 1)
    (φ : fixedGroup K θ.toRingHom →* L) (hφs : Function.Surjective φ)
    (hφc : φ.ker ≤ Subgroup.center (fixedGroup K θ.toRingHom)) :
    ∃ δ : (Fin Tag.E6.rank → CFSG.LieType.Steinberg.normOne θ) →* MulAut L,
      ∀ b x, δ b (φ x) = φ (fixedDiagonalHom K (f * 2)
        (by rw [hK, ← pow_mul]) θ hθ l hl b x) := by
  let : φ.ker.Characteristic := ker_characteristic hK θ hθq φ hφc
  let e := QuotientGroup.quotientKerEquivOfSurjective φ hφs
  let α := fixedDiagonalHom K (f * 2) (by rw [hK, ← pow_mul]) θ hθ l hl
  let δ : (Fin Tag.E6.rank → CFSG.LieType.Steinberg.normOne θ) →* MulAut L :=
    (MulAut.congr e).toMonoidHom.comp ((MulAut.mapQuotient φ.ker).comp α)
  refine ⟨δ, ?_⟩
  intro b x
  have he : e.symm (φ x) = (QuotientGroup.mk x : fixedGroup K θ.toRingHom ⧸ φ.ker) := by
    apply e.injective
    rw [e.apply_symm_apply]
    rfl
  change e (MulAut.mapQuotient φ.ker (α b) (e.symm (φ x))) = φ (α b x)
  rw [he, MulAut.mapQuotient_mk]
  rfl

end CFSG.StandardType.TBE6IndTwist
