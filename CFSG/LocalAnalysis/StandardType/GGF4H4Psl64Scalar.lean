module

public import CFSG.LocalAnalysis.StandardType.GGF4H4Psl64Fix
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Algebra.GroupWithZero.Units.Fintype

public section

namespace CFSG.StandardType

private lemma ggF4H4Psl64_two_eq_zero {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 4) : (2 : F) = 0 := by
  haveI : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = 4 := by rwa [Nat.card_eq_fintype_card] at hF
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2) (by simpa using hcard)
  exact CharP.cast_eq_zero F 2

private lemma ggF4H4Psl64_cube_eq_zero_or_one {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 4) (t : F) : t ^ 3 = 0 ∨ t ^ 3 = 1 := by
  rcases eq_or_ne t 0 with rfl | ht
  · left; simp
  · right
    have hcard : Nat.card Fˣ = 3 := by rw [Nat.card_units, hF]
    have h := pow_card_eq_one' (x := Units.mk0 t ht)
    rw [hcard] at h
    have h' : ((Units.mk0 t ht : Fˣ) : F) ^ 3 = 1 := by
      have := congrArg (fun u : Fˣ => (u : F)) h
      simpa using this
    simpa using h'

private lemma ggF4H4Psl64_exists_omega {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 4) :
    ∃ ω : F, ω ≠ 1 ∧ ω ^ 3 = 1 ∧ 1 + ω + ω ^ 2 = 0 := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = 4 := by rwa [Nat.card_eq_fintype_card] at hF
  have hunits : Fintype.card Fˣ = 3 := by
    rw [Fintype.card_units, hcard]
  have hlt : 1 < Fintype.card Fˣ := by rw [hunits]; norm_num
  obtain ⟨u, hu1⟩ := Fintype.exists_ne_of_one_lt_card hlt (1 : Fˣ)
  have hω1 : (u : F) ≠ 1 := fun h => hu1 (Units.ext h)
  have hωpow : (u : F) ^ 3 = 1 := by
    have hunits_nat : Nat.card Fˣ = 3 := by rw [Nat.card_eq_fintype_card, hunits]
    have h := pow_card_eq_one' (x := u)
    rw [hunits_nat] at h
    have := congrArg (fun v : Fˣ => (v : F)) h
    simpa using this
  refine ⟨(u : F), hω1, hωpow, ?_⟩
  have hfac : ((u : F) - 1) * (1 + (u : F) + (u : F) ^ 2) = 0 := by
    have h : ((u : F) - 1) * (1 + (u : F) + (u : F) ^ 2) = (u : F) ^ 3 - 1 := by ring
    rw [h, hωpow, sub_self]
  exact (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hω1)

theorem ggF4H4Psl64_cube_two_dim {F U : Type*} [Field F] [Finite F] (hF : Nat.card F = 4)
    [AddCommGroup U] [Module F U] [Module.Finite F U] (hU : Module.finrank F U = 2)
    (y : U →ₗ[F] U) (c : F) (hy : y ^ 3 = c • (1 : U →ₗ[F] U)) : c = 0 ∨ c = 1 := by
  by_cases hc0 : c = 0
  · exact Or.inl hc0
  by_cases hc1 : c = 1
  · exact Or.inr hc1
  exfalso
  have hpos : 0 < Module.finrank F U := by rw [hU]; norm_num
  haveI : Nontrivial U := Module.finrank_pos_iff.mp hpos
  obtain ⟨w, hw⟩ := exists_ne (0 : U)
  by_cases heig : ∃ t : F, y w = t • w
  · obtain ⟨t, ht⟩ := heig
    have hpow : ∀ n : ℕ, (y ^ n) w = (t ^ n) • w := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          rw [pow_succ, Module.End.mul_apply, ht, map_smul, ih, smul_smul, pow_succ']
    have h3' : (y ^ 3) w = c • w := by rw [hy]; simp
    have hct : c = t ^ 3 := by
      have hct' : c • w = t ^ 3 • w := by rw [← h3', hpow 3]
      have hsub : (c - t ^ 3) • w = 0 := by rw [sub_smul, hct', sub_self]
      have hcz : c - t ^ 3 = 0 := by
        rcases smul_eq_zero.mp hsub with h | h
        · exact h
        · exact absurd h hw
      exact sub_eq_zero.mp hcz
    rcases ggF4H4Psl64_cube_eq_zero_or_one hF t with h | h
    · exact hc0 (hct.trans h)
    · exact hc1 (hct.trans h)
  · have hli : LinearIndependent F ![w, y w] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      by_cases ht0 : t = 0
      · subst ht0
        simp only [zero_smul, add_zero] at hst
        have hs : s = 0 := by
          rcases smul_eq_zero.mp hst with h | h
          · exact h
          · exact absurd h hw
        exact ⟨hs, rfl⟩
      · exfalso
        apply heig
        have h1 : t • y w = -(s • w) := eq_neg_of_add_eq_zero_right hst
        have h2 : y w = t⁻¹ • (-(s • w)) := by
          rw [← h1, smul_smul, inv_mul_cancel₀ ht0, one_smul]
        refine ⟨-(t⁻¹ * s), ?_⟩
        rw [h2, smul_neg, smul_smul, neg_smul]
    have htop : Submodule.span F (Set.range ![w, y w]) = ⊤ :=
      hli.span_eq_top_of_card_eq_finrank (by simp [hU])
    have hmem : y (y w) ∈ Submodule.span F ({w, y w} : Set U) := by
      have htop' : y (y w) ∈ Submodule.span F (Set.range ![w, y w]) := by
        rw [htop]; exact Submodule.mem_top
      refine Submodule.span_mono ?_ htop'
      rintro x ⟨i, rfl⟩
      fin_cases i <;> simp
    obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hmem
    have hiter : (y ^ 3) w = y (y (y w)) := by
      rw [Module.End.pow_apply]
      norm_num [Function.iterate_succ]
    have hy3w : (y ^ 3) w = (β * α) • w + (α + β ^ 2) • y w := by
      rw [hiter, ← hαβ, map_add, map_smul, map_smul, ← hαβ, smul_add, smul_smul, smul_smul]
      match_scalars <;> ring
    have hcy : (β * α) • w + (α + β ^ 2) • y w = c • w := by
      have h3' : (y ^ 3) w = c • w := by rw [hy]; simp
      rw [← hy3w]
      exact h3'
    have hzero : (β * α - c) • w + (α + β ^ 2) • y w = 0 := by
      rw [sub_smul]
      rw [show (β * α) • w - c • w + (α + β ^ 2) • y w
          = ((β * α) • w + (α + β ^ 2) • y w) - c • w by abel]
      rw [hcy, sub_self]
    obtain ⟨h1, h2⟩ := (LinearIndependent.pair_iff.mp hli) (β * α - c) (α + β ^ 2) hzero
    have hcβ : c = β * α := (sub_eq_zero.mp h1).symm
    have hnegone : (-1 : F) = 1 := by
      have htwo : (2 : F) = 0 := ggF4H4Psl64_two_eq_zero hF
      have h2eq : (2 : F) = 1 + 1 := by norm_num
      have hone : (1 : F) + 1 = 0 := by rw [← h2eq]; exact htwo
      exact (eq_neg_of_add_eq_zero_left hone).symm
    have hα : α = β ^ 2 := by
      have h : α = -(β ^ 2) := eq_neg_of_add_eq_zero_left h2
      have hneg : -(β ^ 2) = β ^ 2 := by
        calc -(β ^ 2) = (-1 : F) * β ^ 2 := by rw [neg_one_mul]
          _ = 1 * β ^ 2 := by rw [hnegone]
          _ = β ^ 2 := one_mul _
      rwa [hneg] at h
    have hcβ3 : c = β ^ 3 := by
      rw [hcβ, hα]
      ring
    rcases ggF4H4Psl64_cube_eq_zero_or_one hF β with h | h
    · exact hc0 (hcβ3.trans h)
    · exact hc1 (hcβ3.trans h)

theorem ggF4H4Psl64_scalar_of_commute {F V : Type*} [Field F] [Finite F] (hF : Nat.card F = 4)
    [AddCommGroup V] [Module F V] [Module.Finite F V] (hV : Module.finrank F V = 6)
    (a b z : V ≃ₗ[F] V) (ha : a ^ 13 = 1) (ha1 : a ≠ 1) (hb : b ^ 17 = 1) (hb1 : b ≠ 1)
    (haz : a * z = z * a) (hbz : b * z = z * b) (hz3 : ∃ c : F, ∀ v, (z ^ 3) v = c • v) :
    ∃ c : F, ∀ v, z v = c • v := by
  obtain ⟨c, hc⟩ := hz3
  have htwo : (2 : F) = 0 := ggF4H4Psl64_two_eq_zero hF
  haveI : Nontrivial V := by
    rw [← Module.finrank_pos_iff (R := F) (M := V)]
    rw [hV]; norm_num
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
  have hzinj : Function.Injective (z ^ 3 : V ≃ₗ[F] V) := (z ^ 3).injective
  have hc0 : c ≠ 0 := by
    intro h0
    have h : (z ^ 3) v₀ = (z ^ 3) 0 := by
      rw [hc v₀, h0, zero_smul, map_zero]
    exact hv₀ (hzinj h)
  by_cases hc1 : c = 1
  · let Z : Module.End F V := z
    have hZ3 : Z ^ 3 = 1 := by
      ext v
      have h := hc v
      rw [hc1] at h
      have hcoe : ((z ^ 3 : V ≃ₗ[F] V) : V →ₗ[F] V) = Z ^ 3 := by
        have := map_pow (LinearEquiv.automorphismGroup.toLinearMapMonoidHom) z 3
        simpa [Z] using this
      rw [← hcoe]
      simpa using h
    obtain ⟨ω, hω1, hω3, hωsum⟩ := ggF4H4Psl64_exists_omega hF
    have hfactor : (Z - 1) * (Z - ω • 1) * (Z - ω ^ 2 • 1) = Z ^ 3 - 1 := by
      ext v
      simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
        Module.End.one_apply, Module.End.pow_apply, Function.iterate_succ,
        Function.iterate_zero, Function.comp_apply, id_eq, smul_sub, smul_add, smul_smul,
        map_sub, map_smul]
      have hω21 : ω ^ 2 * ω = 1 := by rw [show ω ^ 2 * ω = ω ^ 3 by ring, hω3]
      have hneg : (-1 : F) - ω - ω ^ 2 = 0 := by
        rw [show (-1 : F) - ω - ω ^ 2 = -(1 + ω + ω ^ 2) by ring, hωsum, neg_zero]
      match_scalars
      · rfl
      · rw [hneg]
      · rw [hω21]; ring_nf; rw [hωsum]
      · rw [hω21]; ring_nf
    have hprod0 : (Z - 1) * (Z - ω • 1) * (Z - ω ^ 2 • 1) = 0 := by
      rw [hfactor, hZ3, sub_self]
    have haz' : ∀ v, a (z v) = z (a v) := by
      intro v
      have h := congrArg (fun f : V ≃ₗ[F] V => (f : V → V) v) haz
      simpa [LinearEquiv.mul_apply] using h
    have hinv : ∀ t : F, ∀ u ∈ LinearMap.ker (Z - t • 1), a u ∈ LinearMap.ker (Z - t • 1) := by
      intro t u hu
      rw [LinearMap.mem_ker] at hu ⊢
      have hu' : Z u = t • u := by
        have : Z u - t • u = 0 := by
          simpa [LinearMap.sub_apply] using hu
        exact sub_eq_zero.mp this
      have hcomm : Z (a u) = a (Z u) := (haz' u).symm
      have hsub : Z (a u) - t • a u = 0 := by
        rw [hcomm, hu', map_smul]
        exact sub_self _
      simpa [LinearMap.sub_apply] using hsub
    have hinv1 : ∀ u ∈ LinearMap.ker (Z - 1), a u ∈ LinearMap.ker (Z - 1) := by
      simpa using hinv 1
    have hK1 := ggF4H4Psl64_invariant_bot_or_top hF hV a ha ha1 (LinearMap.ker (Z - 1)) hinv1
    have hKω := ggF4H4Psl64_invariant_bot_or_top hF hV a ha ha1
      (LinearMap.ker (Z - ω • 1)) (hinv ω)
    have hKω2 := ggF4H4Psl64_invariant_bot_or_top hF hV a ha ha1
      (LinearMap.ker (Z - ω ^ 2 • 1)) (hinv (ω ^ 2))
    have hzscalar : ∀ (t : F), LinearMap.ker (Z - t • (1 : Module.End F V)) = ⊤ →
        ∀ v, z v = t • v := by
      intro t h v
      have hv : v ∈ LinearMap.ker (Z - t • (1 : Module.End F V)) := by
        rw [h]; exact Submodule.mem_top
      rw [LinearMap.mem_ker] at hv
      have hsub : Z v - t • v = 0 := by simpa [LinearMap.sub_apply] using hv
      exact sub_eq_zero.mp hsub
    rcases hK1 with h1 | h1
    · rcases hKω with hω | hω
      · rcases hKω2 with hω2 | hω2
        · exfalso
          have h1inj : Function.Injective (⇑(Z - 1) : V → V) :=
            LinearMap.ker_eq_bot.mp h1
          have hωinj : Function.Injective (⇑(Z - ω • (1 : Module.End F V)) : V → V) :=
            LinearMap.ker_eq_bot.mp hω
          have hω2inj : Function.Injective
              (⇑(Z - ω ^ 2 • (1 : Module.End F V)) : V → V) := LinearMap.ker_eq_bot.mp hω2
          have hcomp_inj : Function.Injective
              (⇑((Z - 1) * (Z - ω • 1) * (Z - ω ^ 2 • 1)) : V → V) := by
            intro x y hxy
            simp only [Module.End.mul_apply] at hxy
            exact hω2inj (hωinj (h1inj hxy))
          have hv0 : ((Z - 1) * (Z - ω • 1) * (Z - ω ^ 2 • 1)) v₀ = 0 := by
            rw [hprod0]; simp
          have := hcomp_inj (show ((Z - 1) * (Z - ω • 1) * (Z - ω ^ 2 • 1)) v₀
              = ((Z - 1) * (Z - ω • 1) * (Z - ω ^ 2 • 1)) 0 by rw [hv0]; simp)
          exact hv₀ this
        · exact ⟨ω ^ 2, fun v => by simpa using hzscalar (ω ^ 2) hω2 v⟩
      · exact ⟨ω, fun v => by simpa using hzscalar ω hω v⟩
    · exact ⟨1, fun v => by simpa using hzscalar 1 (by simpa using h1) v⟩
  · exfalso
    have hbz' : ∀ v, b (z v) = z (b v) := by
      intro v
      have h := congrArg (fun f : V ≃ₗ[F] V => (f : V → V) v) hbz
      simpa [LinearEquiv.mul_apply] using h
    let P : Submodule F V := LinearMap.ker ((b : V →ₗ[F] V) - 1)
    have hP2 : Module.finrank F P = 2 :=
      ggF4H4Psl64_fixed_finrank_two hF hV b hb hb1
    have hPinv : ∀ p ∈ P, z p ∈ P := by
      intro p hp
      rw [LinearMap.mem_ker] at hp ⊢
      have hp' : (b : V →ₗ[F] V) p = p := by
        have : (b : V →ₗ[F] V) p - p = 0 := by simpa [LinearMap.sub_apply] using hp
        exact sub_eq_zero.mp this
      have hbz'' : (b : V →ₗ[F] V) (z p) = z ((b : V →ₗ[F] V) p) := hbz' p
      have : (b : V →ₗ[F] V) (z p) = z p := by rw [hbz'', hp']
      exact sub_eq_zero.mpr this
    let y : P →ₗ[F] P := LinearMap.restrict (z : V →ₗ[F] V) hPinv
    have hycube : y ^ 3 = c • (1 : P →ₗ[F] P) := by
      ext p
      have hiter : ∀ n : ℕ, ∀ q : P, ((y ^ n) q : V) = (z ^ n) (q : V) := by
        intro n
        induction n with
        | zero => intro q; simp
        | succ n ih =>
            intro q
            rw [pow_succ, Module.End.mul_apply, ih, show ((y q : P) : V) = z (q : V) from rfl,
              pow_succ, LinearEquiv.mul_apply]
      rw [hiter 3 p, hc (p : V)]
      simp
    have hc01 : c = 0 ∨ c = 1 := ggF4H4Psl64_cube_two_dim hF hP2 y c hycube
    rcases hc01 with h0 | h1
    · exact hc0 h0
    · exact hc1 h1

end CFSG.StandardType
