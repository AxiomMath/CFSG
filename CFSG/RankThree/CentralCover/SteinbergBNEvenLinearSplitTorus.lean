module

public import CFSG.RankThree.CentralCover.SteinbergBNLinearTorus
public import CFSG.RankThree.CentralCover.SteinbergBNCoverPairingCore

public section

namespace CFSG.RankThree.CentralCover

open Matrix CFSG.Assembly CFSG.Assembly.RankThreeEven
open scoped MatrixGroups

theorem even_linear_split_torus_central_cover_two_local_normalizer_rank {f n : ℕ}
    (_hf : 1 ≤ f) (hn : 3 ≤ n) {K : Type} [Field K] [Fintype K] (hK2 : ringChar K = 2)
    (_hq : Fintype.card K = 2 ^ f) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrq : r ∣ Fintype.card K - 1) {Y : Type*} [Group Y] [Finite Y] (φ : Y →* PSL(n, K))
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center Y) :
    ∃ R : Subgroup Y, R ≠ ⊥ ∧ IsPGroup 2 R ∧ ∃ V : Subgroup Y,
      V ≤ Subgroup.normalizer (R : Set Y) ∧ IsElemAbelian r V ∧
      Nat.card V = r ^ (n - 1 - if r ∣ n then 1 else 0) ∧
      n - 1 - (if r ∣ n then 1 else 0) ≤ localRank r Y := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  have : NeZero r := ⟨hr.ne_zero⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm1 : 1 ≤ m := by omega
  set φ' : (⊤ : Subgroup Y) →* PSL(m + 1, K) := φ.comp (Subgroup.topEquiv : _ ≃* Y).toMonoidHom
  have hφ' : Function.Surjective φ' := fun x => by
    obtain ⟨y, rfl⟩ := hφ x
    exact ⟨⟨y, Subgroup.mem_top y⟩, rfl⟩
  have hker' : φ'.ker ≤ Subgroup.center (⊤ : Subgroup Y) := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have := Subgroup.mem_center_iff.1 (hker (x := (x : Y)) hx) y
    exact Subtype.ext this
  have hcard : r ∣ Nat.card Kˣ := by
    rw [Nat.card_units, Nat.card_eq_fintype_card]
    exact hrq
  obtain ⟨ζ, hζo⟩ := exists_prime_orderOf_dvd_card' r hcard
  have hζ : ζ ^ r = 1 := by rw [← hζo, pow_orderOf_eq_one]
  obtain ⟨hDp, hF, hDcard⟩ := torusPSL_package hr hr2 hζo hζ hm1 hφ' hker'
  set i₀ : Fin (m + 1) := ⟨0, by omega⟩
  set i₁ : Fin (m + 1) := ⟨1, by omega⟩
  have h01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  let rootHom : Multiplicative K →* SL(m + 1, K) :=
    { toFun := fun t => rootElem h01 (Multiplicative.toAdd t)
      map_one' := rootElem_zero h01
      map_mul' := fun _ _ => rootElem_add h01 _ _ }
  set π := QuotientGroup.mk' (Subgroup.center SL(m + 1, K))
  set U : Subgroup PSL(m + 1, K) := rootHom.range.map π with hU
  have hmemU : ∀ x ∈ U, ∃ t : K, x = π (rootElem h01 t) := by
    rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
    exact ⟨Multiplicative.toAdd t, rfl⟩
  have hUmem : ∀ t : K, π (rootElem h01 t) ∈ U := fun t =>
    ⟨_, ⟨Multiplicative.ofAdd t, rfl⟩, rfl⟩
  have htwo : (2 : K) = 0 := by
    have h := ringChar.Nat.cast_ringChar (R := K)
    rwa [hK2, Nat.cast_ofNat] at h
  have hU1 : U ≠ ⊥ := by
    intro h
    have h1 := hUmem 1
    rw [h, Subgroup.mem_bot] at h1
    exact rootElem_not_mem_center h01 one_ne_zero ((QuotientGroup.eq_one_iff _).1 h1)
  have hU2 : IsPGroup 2 U := by
    rintro ⟨x, hx⟩
    refine ⟨1, Subtype.ext ?_⟩
    obtain ⟨t, rfl⟩ := hmemU x hx
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, ← map_pow, pow_two, ← rootElem_add,
      ← two_mul, htwo, zero_mul, rootElem_zero, map_one]
  have hDU : ∀ d ∈ (torusPSL ζ hζ m).range, ∀ u ∈ U, d * u * d⁻¹ ∈ U := by
    rintro _ ⟨a, rfl⟩ u hu
    obtain ⟨t, rfl⟩ := hmemU u hu
    change π (torusSL ζ hζ m a) * π (rootElem h01 t) * (π (torusSL ζ hζ m a))⁻¹ ∈ U
    rw [← map_inv, ← map_mul, ← map_mul, diag_conj_rootElem h01 _ t _ rfl]
    exact hUmem _
  obtain ⟨R, -, hR1, hR2, A, hA, hAab, hAcard, -, hrank⟩ :=
    central_cover_normalizer_witness (⊤ : Subgroup Y) hφ' hker' hr hr2 hDp hF hDcard hU1 hU2 hDU
  refine ⟨R, hR1, hR2, A, (le_inf_iff.1 hA).2, hAab, ?_, ?_⟩
  · rw [hAcard]
    congr 1
  · convert hrank using 1
    omega

end CFSG.RankThree.CentralCover
