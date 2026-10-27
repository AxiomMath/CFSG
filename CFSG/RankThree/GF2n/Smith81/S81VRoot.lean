module

public import CFSG.RankThree.GF2n.Smith81.S81VRankOne

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

structure RootDatum (K : Type) [Field K] (Γ : Type) [Group Γ] where
  N : Type
  [acg : AddCommGroup N]
  [mod : Module K N]
  [fin : Module.Finite K N]
  u : N → Γ
  u_add : ∀ n m : N, u (n + m) = u n * u m
  τ : N →ₗ[K] K
  n₁ : N
  τ_n₁ : τ n₁ = 1
  P : Subgroup Γ
  Ad : P →* (N ≃ₗ[K] N)
  u_Ad : ∀ (g : P) (n : N), u (Ad g n) = (g : Γ) * u n * (g : Γ)⁻¹
  d : Kˣ →* P
  Ad_d : ∀ c : Kˣ, Ad (d c) n₁ = (c : K) ^ 2 • n₁
  s : Γ
  s_sq : s * s = 1
  s_d : ∀ c : Kˣ, s * ((d c : P) : Γ) * s = ((d c : P) : Γ)⁻¹
  ker_stab : ∀ n : N, τ n = 0 → ∃ g : P, (g : Γ) = s * u n * s
  lemmaS : ∀ n : N, n ≠ 0 → ∃ g : P, τ (Ad g n) ≠ 0
  braid : s = u ((1 : K) • n₁) * (s * u ((1 : K) • n₁) * s) * u ((1 : K) • n₁)

attribute [instance] RootDatum.acg RootDatum.mod RootDatum.fin

variable {K : Type} [Field K] {Γ : Type} [Group Γ] {V : Type} [AddCommGroup V] [Module K V]

@[expose] def RootDatum.toRankOne (R : RootDatum K Γ) (A : Γ →* (V ≃ₗ[K] V)) : RankOneData K V where
  N := R.N
  ρ n := A (R.u n)
  ρ_add n m := by rw [R.u_add, map_mul]
  τ := R.τ
  n₁ := R.n₁
  τ_n₁ := R.τ_n₁
  Pg := R.P
  a := A.comp R.P.subtype
  Ad := R.Ad
  Ad_spec g n := by
    show A (R.u (R.Ad g n)) = A (g : Γ) * A (R.u n) * (A (g : Γ))⁻¹
    rw [R.u_Ad, map_mul, map_mul, map_inv]
  d := R.d
  Ad_d := R.Ad_d
  s := A R.s
  s_sq := by rw [← map_mul, R.s_sq, map_one]
  s_d c := by
    show A R.s * A ((R.d c : R.P) : Γ) * A R.s = (A ((R.d c : R.P) : Γ))⁻¹
    rw [← map_mul, ← map_mul, R.s_d, map_inv]
  ker_stab n hn := by
    obtain ⟨g, hg⟩ := R.ker_stab n hn
    refine ⟨g, ?_⟩
    show A (g : Γ) = A R.s * A (R.u n) * A R.s
    rw [hg, map_mul, map_mul]
  lemmaS := R.lemmaS

theorem RootDatum.toRankOne_braid (R : RootDatum K Γ) (A : Γ →* (V ≃ₗ[K] V)) :
    (R.toRankOne A).s = (R.toRankOne A).X 1 * ((R.toRankOne A).s * (R.toRankOne A).X 1 *
      (R.toRankOne A).s) * (R.toRankOne A).X 1 := by
  show A R.s = A (R.u ((1 : K) • R.n₁)) * (A R.s * A (R.u ((1 : K) • R.n₁)) * A R.s) *
    A (R.u ((1 : K) • R.n₁))
  rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, ← R.braid]

end CFSG.RankThree.GF2n.Smith81.S81V
