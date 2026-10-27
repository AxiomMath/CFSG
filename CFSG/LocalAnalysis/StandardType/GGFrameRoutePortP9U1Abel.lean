module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9U2Card

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.RowXUn.Struct

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem card_le_three_pow_finrank_of_abelian_good [Finite K] (hK : Nat.card K = 4)
    [FiniteDimensional K V] {Q : Subgroup (V ≃ₗ[K] V)} (hQ : IsGoodIn (scalars K V) Q)
    (hab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) :
    Nat.card Q ≤ 3 ^ Module.finrank K V := by
  classical
  by_cases h3 : ∀ x ∈ Q, x ^ 3 = 1
  · haveI : Finite (V ≃ₗ[K] V) := finite_linearEquiv
    obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_three hK
    have hcomm : ∀ s t : Q,
        Commute ((s : V ≃ₗ[K] V) : V →ₗ[K] V) ((t : V ≃ₗ[K] V) : V →ₗ[K] V) := by
      intro s t
      have h : ((s : V ≃ₗ[K] V) : V →ₗ[K] V) * ((t : V ≃ₗ[K] V) : V →ₗ[K] V) =
          ((t : V ≃ₗ[K] V) : V →ₗ[K] V) * ((s : V ≃ₗ[K] V) : V →ₗ[K] V) := by
        refine LinearMap.ext fun v => ?_
        have := congrArg (fun e : V ≃ₗ[K] V => e v) (hab s s.2 t t.2)
        simpa using this
      exact h
    have hpow : ∀ t : Q, ((t : V ≃ₗ[K] V) : V →ₗ[K] V) ^ 3 = 1 := fun t =>
      toLinearMap_pow_three (h3 t t.2)
    obtain ⟨b, μ, hb⟩ :=
      CFSG.RankThree.PartOne.exists_basis_common_eigenvectors_of_pow_eq_one hζ
        (fun t : Q => ((t : V ≃ₗ[K] V) : V →ₗ[K] V)) hcomm hpow
    have hμ0 : ∀ t j, μ t j ≠ 0 := by
      intro t j h0
      have h1 := hb t j
      rw [h0, zero_smul] at h1
      exact b.ne_zero j ((t : V ≃ₗ[K] V).map_eq_zero_iff.1 h1)
    have hinj : Function.Injective μ := by
      intro t t' h
      apply Subtype.ext
      have h1 : ((t : V ≃ₗ[K] V) : V →ₗ[K] V) = ((t' : V ≃ₗ[K] V) : V →ₗ[K] V) :=
        b.ext fun j => by rw [hb t j, hb t' j, h]
      exact LinearEquiv.ext fun v => LinearMap.congr_fun h1 v
    have h1 := card_le_three_pow_card_image hK μ hμ0 hinj
    have hk : (Finset.univ.image
          (fun j : Fin (Module.finrank K V) => fun t : Q => μ t j)).card
        ≤ Module.finrank K V := by
      calc (Finset.univ.image
            (fun j : Fin (Module.finrank K V) => fun t : Q => μ t j)).card
          ≤ (Finset.univ : Finset (Fin (Module.finrank K V))).card := Finset.card_image_le
        _ = Module.finrank K V := by simp
    calc Nat.card Q ≤ 3 ^ (Finset.univ.image
            (fun j : Fin (Module.finrank K V) => fun t : Q => μ t j)).card := h1
      _ ≤ 3 ^ Module.finrank K V := Nat.pow_le_pow_right (by norm_num) hk
  · push Not at h3
    obtain ⟨x, hx, hx3⟩ := h3
    obtain ⟨h3dvd, hcard⟩ :=
      three_dvd_finrank_and_card_le_of_abelian_cube hK hQ hab hx hx3
    have hm : Module.finrank K V ≠ 0 := by
      intro h0
      haveI : Subsingleton V := Module.finrank_zero_iff.1 h0
      exact hx3 (LinearEquiv.ext fun v => Subsingleton.elim _ _)
    have hle : 1 + Module.finrank K V / 3 ≤ Module.finrank K V := by
      obtain ⟨d, hd⟩ := h3dvd
      have hd1 : 1 ≤ d := by
        rcases Nat.eq_zero_or_pos d with h | h
        · subst h
          simp at hd
          exact absurd hd hm
        · exact h
      rw [hd, Nat.mul_div_cancel_left d (by norm_num : 0 < 3)]
      omega
    calc Nat.card Q ≤ 3 ^ (1 + Module.finrank K V / 3) := hcard
      _ ≤ 3 ^ Module.finrank K V := Nat.pow_le_pow_right (by norm_num) hle

end CFSG.StandardType.FrameRoute

end
