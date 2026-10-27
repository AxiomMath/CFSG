module

public import CFSG.RankThree.PartOne.CTP.SU4EvenData
public import CFSG.LieType.Universal.Spin.Twisted.RankOne
public import CFSG.LieType.BorelTits.UnitaryForm

public section

namespace CFSG.RankThree.PartOne.CTP.SU4Even

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.BorelTits

theorem exists_kleinDataEven {F K : Type} [Field F] [Finite F] [CharP F 2] [Field K] [Finite K]
    [CharP K 2] {f : ℕ} (hF : Nat.card F = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    ∃ inst : Algebra F K, Nonempty (@KleinDataEven F K _ _ inst (unitaryInvolution K 2 f) b c) := by
  have := fact_shortField hirr
  have := finite_shortField (b := b) (c := c)
  have hcardE : Nat.card (ShortField b c) = (2 ^ f) ^ 2 := by
    rw [Nat.card_congr (QuadraticAlgebra.equivProd (-c) b), Nat.card_prod, hF]
    ring
  let : Fintype (ShortField b c) := Fintype.ofFinite _
  let : Fintype K := Fintype.ofFinite _
  let : Fintype F := Fintype.ofFinite _
  let φ : ShortField b c ≃+* K :=
    FiniteField.ringEquivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcardE, hK])
  let τ : F →+* K := φ.toRingHom.comp (algebraMap F (ShortField b c))
  let inst : Algebra F K := τ.toAlgebra
  have hτ : ∀ r, algebraMap F K r = φ (algebraMap F (ShortField b c) r) := fun r => rfl
  have hω₀ : (⟨0, 1⟩ : ShortField b c) * ⟨0, 1⟩ =
      algebraMap F (ShortField b c) (-c) + algebraMap F (ShortField b c) b * ⟨0, 1⟩ := by
    ext <;> simp [QuadraticAlgebra.algebraMap_eq]
  have hspanE : ∀ t : ShortField b c, t = algebraMap F (ShortField b c) t.re +
      algebraMap F (ShortField b c) t.im * ⟨0, 1⟩ := by
    intro t
    ext <;> simp [QuadraticAlgebra.algebraMap_eq]
  have hστ : ∀ r : F, unitaryInvolution K 2 f (algebraMap F K r) = algebraMap F K r := by
    intro r
    rw [unitaryInvolution_apply, ← map_pow]
    congr 1
    have h := FiniteField.pow_card r
    rwa [← Nat.card_eq_fintype_card, hF] at h
  have hω_sq : (-φ ⟨0, 1⟩) ^ 2 + algebraMap F K b * (-φ ⟨0, 1⟩) + algebraMap F K c = 0 := by
    have h := congrArg φ hω₀
    simp only [map_mul, map_add, map_neg] at h
    rw [hτ b, hτ c]
    linear_combination h
  have hspan : ∀ x : K, ∃ u v : F,
      x = algebraMap F K u - algebraMap F K v * (-φ ⟨0, 1⟩) := by
    intro x
    refine ⟨(φ.symm x).re, (φ.symm x).im, ?_⟩
    have h := congrArg φ (hspanE (φ.symm x))
    rw [RingEquiv.apply_symm_apply, map_add, map_mul] at h
    refine h.trans ?_
    rw [hτ, hτ]
    ring
  have hσω : unitaryInvolution K 2 f (-φ ⟨0, 1⟩) =
      -algebraMap F K b - (-φ ⟨0, 1⟩) := by
    set ω : K := -φ ⟨0, 1⟩ with hω
    set σ := unitaryInvolution K 2 f with hσ
    have h1 : (σ ω) ^ 2 + algebraMap F K b * σ ω + algebraMap F K c = 0 := by
      have h := congrArg σ hω_sq
      simpa only [map_add, map_mul, map_pow, hστ, map_zero] using h
    have h2 : (σ ω - ω) * (σ ω + ω + algebraMap F K b) = 0 := by
      linear_combination h1 - hω_sq
    rcases mul_eq_zero.mp h2 with h | h
    · exfalso
      have hωσ : σ ω = ω := sub_eq_zero.mp h
      obtain ⟨z, hz⟩ := exists_unitaryInvolution_ne hK
      obtain ⟨u, v, hz'⟩ := hspan z
      apply hz
      rw [hz', map_sub, map_mul, hστ, hστ, hωσ]
    · linear_combination h
  have hb : b ≠ 0 := by
    intro hb0
    obtain ⟨s, hs⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) c
    apply hirr s
    rw [hb0, zero_mul, add_zero, hs, ← sq, CharTwo.add_self_eq_zero]
  have hdisc : b ^ 2 - 4 * c ≠ 0 := by
    have h4 : (4 : F) = 0 := by
      calc (4 : F) = 2 * 2 := by norm_num
        _ = 0 := by rw [CharTwo.two_eq_zero, zero_mul]
    rw [h4, zero_mul, sub_zero]
    exact pow_ne_zero 2 hb
  exact ⟨inst, ⟨{
    ω := -φ ⟨0, 1⟩
    σσ := unitaryInvolution_involutive hK
    σ_alg := hστ
    ω_sq := hω_sq
    σ_ω := hσω
    span := hspan
    disc_ne := hdisc }⟩⟩

end CFSG.RankThree.PartOne.CTP.SU4Even
