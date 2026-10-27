module

public import CFSG.RankThree.Chevalley.SteinbergBID4WeylCert
public import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups

public section

namespace CFSG.RankThree.PartOne.D4RC

open Matrix CFSG.RankThree.Classical2 CFSG.RankThree.Chevalley CFSG.LieType.Universal.Unitary
  CFSG.LieType.Steinberg CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

variable {L : Type} [Field L]

theorem rcl_prod_fin3 (q : ℕ) (hq : 2 ≤ q) :
    (∏ i : Fin 3, (q ^ 3 - q ^ (i : ℕ))) / (q - 1) = q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) := by
  rw [Fin.prod_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
  have h1 : q ≤ q ^ 3 := by nlinarith [Nat.one_le_pow 2 q (by omega)]
  have h2 : q ^ 2 ≤ q ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : 1 ≤ q ^ 2 := Nat.one_le_pow 2 q (by omega)
  have h4 : 1 ≤ q ^ 3 := Nat.one_le_pow 3 q (by omega)
  apply Nat.div_eq_of_eq_mul_left (by omega : 0 < q - 1)
  zify [h1, h2, h3, h4, (by omega : 1 ≤ q)]
  ring

theorem rcl_card_SL3_field (k : Type) [Field k] [Finite k] {q : ℕ} (hk : Nat.card k = q)
    (hq : 2 ≤ q) : Nat.card (SL(3, k)) = q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) := by
  have : Fintype k := Fintype.ofFinite k
  have h := Matrix.card_SL_field (𝔽 := k) 3
  rw [← Nat.card_eq_fintype_card, hk] at h
  rw [h, rcl_prod_fin3 q hq]

theorem rcl_card_fix_split {k : Type} [Field k] [Finite k] [Algebra k L] {q : ℕ}
    (hk : Nat.card k = q) (hq : 2 ≤ q) (Φ' : SL(3, L) ≃* SL(3, L)) (H : SL(3, L))
    (hH : ∀ X : SL(3, L), X ∈ fixSubgroup Φ' ↔
      ∃ Y : SL(3, k), X = H * Matrix.SpecialLinearGroup.map (algebraMap k L) Y * H⁻¹) :
    Nat.card (fixSubgroup Φ') = q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) := by
  set θ : SL(3, k) →* SL(3, L) :=
    (MulAut.conj H).toMonoidHom.comp (Matrix.SpecialLinearGroup.map (algebraMap k L)) with hθ
  have hinj : Function.Injective θ :=
    (MulAut.conj H).injective.comp (specialLinearGroup_map_injective (algebraMap k L).injective)
  have hrange : fixSubgroup Φ' = θ.range := by
    ext X
    rw [hH]
    constructor
    · rintro ⟨Y, rfl⟩
      exact ⟨Y, by simp [hθ, MulAut.conj_apply]⟩
    · rintro ⟨Y, rfl⟩
      exact ⟨Y, by simp [hθ, MulAut.conj_apply]⟩
  rw [hrange, ← rcl_card_SL3_field k hk hq]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem rcl_card_statedSU_three {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    [CharP F p] (hF : Nat.card F = (p ^ f) ^ 2) :
    Nat.card (StatedSU 3 (p ^ f) F) = (p ^ f) ^ 3 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) := by
  rw [← SUid_eq_statedSU hF 3]
  obtain ⟨P₃, hP₃⟩ := exists_wittMatrix hF 3
  rw [← Nat.card_congr (conjEquiv P₃ hP₃).toEquiv, card_SU_three hF]

theorem rcl_card_fix_unitary {k : Type} [Field k] [Algebra k L] [IsAlgClosure k L] {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hk : Nat.card k = ℓ ^ f)
    (Φ' : SL(3, L) ≃* SL(3, L)) (H : SL(3, L))
    (hH : ∀ X : SL(3, L), X ∈ fixSubgroup Φ' ↔ ∃ Y ∈ unitarySet (ℓ ^ f) 3,
      Matrix.SpecialLinearGroup.toGL X = Matrix.SpecialLinearGroup.toGL H * Y *
        (Matrix.SpecialLinearGroup.toGL H)⁻¹) :
    Nat.card (fixSubgroup Φ') = (ℓ ^ f) ^ 3 * ((ℓ ^ f) ^ 2 - 1) * ((ℓ ^ f) ^ 3 + 1) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact (pow_pos hℓ.pos f).ne')
  have : Fintype k := Fintype.ofFinite k
  have : CharP k ℓ := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hk])
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap k L).injective ℓ
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed k
  set F : Subfield L := (iterateFrobenius L ℓ (2 * f)).eqLocusField (RingHom.id L) with hFdef
  have hq2 : (ℓ ^ f) ^ 2 = ℓ ^ (2 * f) := by rw [← pow_mul, mul_comm]
  have hF2 : ∀ c : L, c ∈ F ↔ c ^ ℓ ^ (2 * f) = c := fun c => by
    rw [hFdef, RingHom.mem_eqLocusField, iterateFrobenius_def, RingHom.id_apply]
  have hF : ∀ c : L, c ∈ F ↔ c ^ (ℓ ^ f) ^ 2 = c := fun c => by
    rw [hq2]
    exact hF2 c
  have hFcard : Nat.card F = (ℓ ^ f) ^ 2 := by
    rw [hq2, ← natCard_setOf_pow_eq_self (Ω := L) (ℓ := ℓ) (by omega : 2 * f ≠ 0)]
    exact Nat.card_congr (Equiv.subtypeEquivRight hF2)
  have : Finite F := Nat.finite_of_card_ne_zero (by
    rw [hFcard]
    exact (pow_pos (pow_pos hℓ.pos f) 2).ne')
  have : CharP F ℓ := RingHom.charP F.subtype F.subtype.injective ℓ
  have hrange : fixSubgroup Φ' =
      ((statedSUToSL F 3 (ℓ ^ f)).range).map (MulAut.conj H).toMonoidHom := by
    ext X
    rw [hH, Subgroup.mem_map]
    constructor
    · rintro ⟨Y, hY, hXY⟩
      refine ⟨H⁻¹ * X * H, ?_, by simp [MulAut.conj_apply]; group⟩
      rw [mem_range_statedSUToSL_iff hℓ F hF hFcard (by omega)]
      have : Matrix.SpecialLinearGroup.toGL (H⁻¹ * X * H) = Y := by
        rw [map_mul, map_mul, map_inv, hXY]
        group
      rw [this]
      exact hY
    · rintro ⟨Z, hZ, rfl⟩
      rw [mem_range_statedSUToSL_iff hℓ F hF hFcard (by omega)] at hZ
      exact ⟨Matrix.SpecialLinearGroup.toGL Z, hZ, by simp [MulAut.conj_apply, map_mul, map_inv]⟩
  rw [hrange, Subgroup.card_map_of_injective (MulAut.conj H).injective]
  rw [← Nat.card_congr (MonoidHom.ofInjective (statedSUToSL_injective F 3 (ℓ ^ f))).toEquiv]
  exact rcl_card_statedSU_three hFcard

end CFSG.RankThree.PartOne.D4RC
