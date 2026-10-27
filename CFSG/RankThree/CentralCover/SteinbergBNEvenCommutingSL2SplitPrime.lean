module

public import CFSG.RankThree.CentralCover.SteinbergBNSL2InversionBasis
public import CFSG.RankThree.CentralCover.SteinbergBNSL2Elements

public section

namespace CFSG.RankThree.CentralCover

open CFSG.Assembly CFSG.Assembly.RankThreeEven
open scoped MatrixGroups

theorem mem_normalizer_of_conj_mem {T : Type*} [Group T] {U : Subgroup T} {g : T}
    (h1 : ∀ u ∈ U, g * u * g⁻¹ ∈ U) (h2 : ∀ u ∈ U, g⁻¹ * u * g ∈ U) :
    g ∈ Subgroup.normalizer (U : Set T) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h1 x, fun hx => ?_⟩
  have := h2 _ hx
  simpa [mul_assoc] using this

theorem even_commuting_SL2_actual_central_cover_split_prime_local_rank {G : Type*} [Group G]
    [Finite G] (Y : Subgroup G) {H : Type*} [Group H] {K : Type*} [Field K] [Fintype K]
    (hK : ringChar K = 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Fintype.card K - 1) {m : ℕ} (hm : 1 ≤ m) (φ : Y →* H)
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center Y)
    (ι : Fin m → SL(2, K) →* H) (hι : ∀ i, Function.Injective (ι i))
    (hcomm : ∀ i j, i ≠ j → ∀ A B : SL(2, K), ι i A * ι j B = ι j B * ι i A) :
    ∃ R : Subgroup G, R ≤ Y ∧ R ≠ ⊥ ∧ IsPGroup 2 R ∧ ∃ A : Subgroup G,
      A ≤ Y ⊓ Subgroup.normalizer (R : Set G) ∧ IsElemAbelian p A ∧ Nat.card A = p ^ m ∧
      m ≤ localRank p G := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hcard : p ∣ Nat.card Kˣ := by
    rw [Nat.card_units, Nat.card_eq_fintype_card]
    exact hpq
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' p hcard
  obtain ⟨hDab, hDcard, hF⟩ := commuting_SL2_inversion_package hφ hker ι hι hcomm hp hp2
    (h := sl2Diag ζ) (w := sl2Weyl K) (by rw [orderOf_sl2Diag, hζ]) (sl2Weyl_conj_diag ζ)
  set i₀ : Fin m := ⟨0, hm⟩
  set U : Subgroup H := (sl2UpperHom K).range.map (ι i₀) with hU
  have hmemU : ∀ x ∈ U, ∃ c : K, x = ι i₀ (sl2Upper c) := by
    intro x hx
    obtain ⟨_, ⟨c, rfl⟩, rfl⟩ := Subgroup.mem_map.1 hx
    exact ⟨Multiplicative.toAdd c, rfl⟩
  have hUmem : ∀ c : K, ι i₀ (sl2Upper c) ∈ U := fun c =>
    Subgroup.mem_map.2 ⟨_, ⟨Multiplicative.ofAdd c, rfl⟩, rfl⟩
  have htwo : (2 : K) = 0 := by
    have := ringChar.Nat.cast_ringChar (R := K)
    rwa [hK, Nat.cast_ofNat] at this
  have hU1 : U ≠ ⊥ := by
    intro h
    have h1 := hUmem 1
    rw [h, Subgroup.mem_bot, ← map_one (ι i₀)] at h1
    have h2 := sl2Upper_injective ((hι i₀) h1 |>.trans sl2Upper_zero.symm)
    exact one_ne_zero h2
  have hU2 : IsPGroup 2 U := by
    rintro ⟨x, hx⟩
    refine ⟨1, Subtype.ext ?_⟩
    obtain ⟨c, rfl⟩ := hmemU x hx
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, ← map_pow, sl2Upper_pow, Nat.cast_ofNat,
      htwo, zero_mul, sl2Upper_zero, map_one]
  have hgen : ∀ i, ι i (sl2Diag ζ) ∈ Subgroup.normalizer (U : Set H) := by
    intro i
    by_cases hi : i = i₀
    · rw [hi]
      have hconj : ∀ a : Kˣ, ∀ x ∈ U, ι i₀ (sl2Diag a) * x * (ι i₀ (sl2Diag a))⁻¹ ∈ U := by
        intro a x hx
        obtain ⟨c, rfl⟩ := hmemU x hx
        rw [← map_inv, ← map_mul, ← map_mul, sl2Diag_conj_upper]
        exact hUmem _
      refine mem_normalizer_of_conj_mem (hconj ζ) fun x hx => ?_
      have hinv : (ι i₀ (sl2Diag ζ))⁻¹ = ι i₀ (sl2Diag ζ⁻¹) := by
        rw [← sl2DiagHom_apply, ← sl2DiagHom_apply, map_inv, map_inv]
      have := hconj ζ⁻¹ x hx
      rwa [← hinv, inv_inv] at this
    · have hfix : ∀ x ∈ U, ι i (sl2Diag ζ) * x * (ι i (sl2Diag ζ))⁻¹ = x := by
        intro x hx
        obtain ⟨c, rfl⟩ := hmemU x hx
        rw [hcomm i i₀ hi, mul_inv_cancel_right]
      refine mem_normalizer_of_conj_mem (fun x hx => by rw [hfix x hx]; exact hx)
        fun x hx => ?_
      have h1 := hfix x hx
      rw [mul_inv_eq_iff_eq_mul] at h1
      have h2 : (ι i (sl2Diag ζ))⁻¹ * x * ι i (sl2Diag ζ) = x := by
        rw [mul_assoc, ← h1, inv_mul_cancel_left]
      rw [h2]
      exact hx
  have hDN : Subgroup.closure (Set.range fun i => ι i (sl2Diag ζ)) ≤
      Subgroup.normalizer (U : Set H) :=
    (Subgroup.closure_le _).2 (by rintro _ ⟨i, rfl⟩; exact hgen i)
  obtain ⟨R, hRY, hR1, hR2, A, hA, hAab, hAcard, -, hrank⟩ :=
    central_cover_normalizer_witness Y hφ hker hp hp2 hDab.2 hF hDcard.ge hU1 hU2
      (fun d hd u hu => (Subgroup.mem_normalizer_iff.1 (hDN hd) u).1 hu)
  exact ⟨R, hRY, hR1, hR2, A, hA, hAab, hAcard, hrank⟩

end CFSG.RankThree.CentralCover
