module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LieType.AlgebraicGroups.E6RationalTwistedFaithful
public import CFSG.LieType.Chevalley.RootWeightFiltration
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.HardMathSupport.C14Exc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups

theorem power_map_of_shape {Z : Type*} [Monoid Z] (γ : Z →* Z) {m p k q₀ : ℕ}
    (hγ : ∀ z, γ^[m] z = z) (hpk : p * k ≡ 1 [MOD m]) (z : Z)
    (hz : (fun y => γ (y ^ q₀))^[p] z = z) :
    (γ (z ^ q₀)) ^ q₀ ^ (p * k) = z ^ q₀ := by
  have hpow : ∀ i (y : Z) (n : ℕ), γ^[i] (y ^ n) = (γ^[i] y) ^ n := by
    intro i
    induction i with
    | zero => intro y n; rfl
    | succ i ih => intro y n; rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
        map_pow]
  have hit : ∀ i (y : Z), (fun y => γ (y ^ q₀))^[i] y = γ^[i] (y ^ q₀ ^ i) := by
    intro i
    induction i with
    | zero => intro y; simp
    | succ i ih =>
      intro y
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply', ← hpow, ← pow_mul,
        ← pow_succ]
  have hγi : ∀ i (y : Z), γ^[i] y = γ^[i % m] y := by
    intro i y
    have hj : ∀ j (y : Z), γ^[m * j] y = y := by
      intro j
      induction j with
      | zero => intro y; rfl
      | succ j ih => intro y; rw [Nat.mul_succ, Function.iterate_add_apply, hγ, ih]
    conv_lhs => rw [← Nat.mod_add_div i m, Function.iterate_add_apply, hj]
  have h1 : γ^[p] (z ^ q₀ ^ p) = z := by rw [← hit]; exact hz
  have hk : ∀ j, γ^[p * j] (z ^ q₀ ^ (p * j)) = z := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Nat.mul_succ, Function.iterate_add_apply, pow_add q₀ (p * j) p, mul_comm (q₀ ^ (p * j)),
        pow_mul, hpow, h1, ih]
  have hmk : γ^[p * k] = γ^[1 % m] := by
    funext y; rw [hγi, show p * k % m = 1 % m from hpk]
  calc (γ (z ^ q₀)) ^ q₀ ^ (p * k) = γ ((z ^ q₀ ^ (p * k)) ^ q₀) := by
        rw [← map_pow, ← pow_mul, ← pow_mul, mul_comm]
    _ = γ^[p * k] ((z ^ q₀ ^ (p * k)) ^ q₀) := by
        rw [hmk, ← hγi 1]; rfl
    _ = z ^ q₀ := by rw [hpow, hk]

theorem norm_surjective_of_lang {Z : Type*} [CommGroup Z] (F₀ : Z →* Z) (p : ℕ)
    (hLang : ∀ y : Z, ∃ x : Z, y = x⁻¹ * F₀^[p] x) (y : Z) (hy : F₀ y = y) :
    ∃ z : Z, F₀^[p] z = z ∧ ∏ i ∈ Finset.range p, F₀^[i] z = y := by
  obtain ⟨x, rfl⟩ := hLang y
  refine ⟨x⁻¹ * F₀ x, ?_, ?_⟩
  · rw [map_mul, map_inv] at hy
    rw [iterate_map_mul, iterate_map_inv, ← Function.iterate_succ_apply,
      Function.iterate_succ_apply']
    calc (F₀^[p] x)⁻¹ * F₀ (F₀^[p] x)
        = (F₀^[p] x)⁻¹ * (F₀ x * ((F₀ x)⁻¹ * F₀ (F₀^[p] x))) := by group
      _ = (F₀^[p] x)⁻¹ * (F₀ x * (x⁻¹ * F₀^[p] x)) := by rw [hy]
      _ = x⁻¹ * F₀ x := by
          rw [mul_left_comm, mul_comm x⁻¹ (F₀^[p] x), inv_mul_cancel_left, mul_comm]
  · have hp : ∀ n, ∏ i ∈ Finset.range n, F₀^[i] (x⁻¹ * F₀ x) = x⁻¹ * F₀^[n] x := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Finset.prod_range_succ, ih, iterate_map_mul, iterate_map_inv,
          ← Function.iterate_succ_apply F₀ n x]
        group
    exact hp p

end CFSG.HardMathSupport.C14Exc
