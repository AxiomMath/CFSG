module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHyperbolic
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestTorus
public import CFSG.ClassicalGroups.UnitaryFlag.OrderSylow

public section

namespace CFSG.StandardType

open Multiplicative Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly CFSG.Open TableB

section Hyp

variable {n r p : ℕ} {K : Type} [Field K]

theorem exists_hypTorus_le_normalizer_unitHypLift (h : UnitaryFieldData 2 n K) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n - 1) (hr : 1 ≤ r) :
    ∃ E : Subgroup (hypSU h r 0),
      E ≤ Subgroup.normalizer (hypUnitriangular h r 0 : Set (hypSU h r 0)) ∧
      IsElemAbelian p E ∧ Nat.card E = p ^ r ∧ E ⊓ hypScalars h r 0 = ⊥ := by
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_of_dvd_two_pow_sub_one h hp hpq
  have hbar : h.bar ζ = ζ := bar_eq_self_of_pow_eq_one h hpq hζ.pow_eq_one
  obtain ⟨ι, hι⟩ := exists_hypTorusHom (r := r) h hp hζ hbar
  have hcard := card_range_hypTorusHom h hp hζ ι hι
  have hB : hypBorel h r 0 ≤ Subgroup.normalizer (hypUnitriangular h r 0 : Set (hypSU h r 0)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hypUnitriangular_le_hypBorel h)).mp
      (normal_hypUnitriangular (Nat.zero_le 1))
  refine ⟨ι.range, ?_, ?_, hcard, ?_⟩
  · rintro _ ⟨t, rfl⟩
    refine hB (mem_hypBorel_of_blockTriangular h ?_)
    have ht := hι (toAdd t)
    rw [ofAdd_toAdd] at ht
    rw [ht]
    exact blockTriangular_diagonal _
  · refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨s, hs⟩ := a.2
      obtain ⟨t, ht⟩ := b.2
      apply Subtype.ext
      change (a : hypSU h r 0) * b = b * a
      rw [← hs, ← ht, ← map_mul, ← map_mul, mul_comm]
    · obtain ⟨t, rfl⟩ := hx
      have htp : t ^ p = 1 := by
        rw [← toAdd_eq_zero, toAdd_pow]
        funext i
        simp [Pi.smul_apply, nsmul_eq_mul]
      rw [← map_pow, htp, map_one]
  · rw [← Subgroup.card_eq_one]
    have h1 := Subgroup.card_dvd_of_le (inf_le_left (a := ι.range) (b := hypScalars h r 0))
    have h2 := Subgroup.card_dvd_of_le (inf_le_right (a := ι.range) (b := hypScalars h r 0))
    rw [hcard] at h1
    rw [card_hypScalars h (r := r) (ε := 0) (by omega)] at h2
    have hpZ : ¬ p ∣ Nat.gcd (2 * r + 0) (2 ^ n + 1) := fun hd =>
      not_dvd_two_pow_add_one_of_dvd_sub_one hp hp2 hpq (hd.trans (Nat.gcd_dvd_right _ _))
    exact Nat.eq_one_of_dvd_coprimes
      (Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpZ)) h1 h2

end Hyp

section Lift

variable {n r p : ℕ} {K : Type} [Field K] [Finite K]

theorem ggTorusLift_unitaryHypEven (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n - 1) (hr : 2 ≤ r) :
    GGTorusLift p r (LargeEvenProj (LargeEvenSUGroup (Fin (2 * r)) K (2 ^ n))) := by
  have h : UnitaryFieldData 2 n K := TableBU.unitaryFieldData_of_card hK hn
  have hpq' : ¬ p ∣ 2 ^ n + 1 := not_dvd_two_pow_add_one_of_dvd_sub_one hp hp2 hpq
  have hq4 : 4 ≤ 2 ^ n := four_le_two_pow_of_dvd_sub_one hp hp2 hn hpq
  obtain ⟨E₀, hE₀N, hE₀ab, hE₀card, hE₀Z⟩ :=
    exists_hypTorus_le_normalizer_unitHypLift h hp hp2 hpq (by omega : 1 ≤ r)
  obtain ⟨M, hM⟩ := exists_isHypTransport (r := r) (ε := 0) h
  let e := hypPSUEquivStatedProj h hM (by omega)
  let Φ : hypSU h r 0 →* LargeEvenProj (LargeEvenSUGroup (Fin (2 * r)) K (2 ^ n)) :=
    e.toMonoidHom.comp (hypProj h r 0)
  have hΦ : ∀ x : hypSU h r 0, Φ x = 1 → x ∈ hypScalars h r 0 := by
    intro x hx
    have hx' : e (hypProj h r 0 x) = 1 := hx
    have h1 : x ∈ (hypProj h r 0).ker := (MulEquiv.map_eq_one_iff e).mp hx'
    rwa [ker_hypProj] at h1
  have hcardΦ : ∀ H : Subgroup (hypSU h r 0), H ⊓ hypScalars h r 0 = ⊥ →
      Nat.card (H.map Φ) = Nat.card H := by
    intro H hH
    have hinj : Function.Injective (Φ.comp H.subtype) := by
      rw [injective_iff_map_eq_one]
      intro a ha
      have h1 : (a : hypSU h r 0) ∈ H ⊓ hypScalars h r 0 := ⟨a.2, hΦ a ha⟩
      rw [hH, Subgroup.mem_bot] at h1
      exact Subtype.ext h1
    have hrange : (Φ.comp H.subtype).range = H.map Φ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hrange]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hU2 : IsPGroup 2 (hypUnitriangular h r 0) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine IsPGroup.of_card (n := n * ((2 * r + 0) * (2 * r + 0 - 1) / 2)) ?_
    rw [card_hypUnitriangular h (Nat.zero_le 1), ← pow_mul]
  have hUne : (hypUnitriangular h r 0).map Φ ≠ ⊥ := by
    intro hbot
    have h1 := hcardΦ _ (hypUnitriangular_inf_hypScalars h (by omega) (Nat.zero_le 1))
    rw [hbot, Subgroup.card_bot, card_hypUnitriangular h (Nat.zero_le 1)] at h1
    have h2 : 2 * 1 ≤ (2 * r + 0) * (2 * r + 0 - 1) := Nat.mul_le_mul (by omega) (by omega)
    have h3 : 1 < (2 ^ n) ^ ((2 * r + 0) * (2 * r + 0 - 1) / 2) :=
      Nat.one_lt_pow (Nat.div_pos h2 two_pos).ne' (by omega)
    omega
  exact OrthRest.ggTorusLift_of_R hp (center_statedProj_statedSU_eq_bot (d := 2 * r) hK (by omega))
    (ggCenterPrime_psu_even (d := 2 * r) hK (even_two_mul r) (by omega) hq4 hpq') hUne
    (hU2.map Φ) ((Subgroup.map_mono hE₀N).trans (Subgroup.le_normalizer_map Φ))
    (isElemAbelian_map hE₀ab Φ) (by rw [hcardΦ E₀ hE₀Z, hE₀card])

end Lift

theorem ggTorusLift_unitaryHypSix
    {K : Type} [Field K] [Finite K] {n p : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ n - 1) :
    GGTorusLift p 3 (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ n))) :=
  ggTorusLift_unitaryHypEven (r := 3) hK hn hp hp2 hpq (by norm_num)

section Labels

theorem largeEvenLabelAll_torusLift_unitFiveMinus
    {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .twA ∧ lab.rank = 5 ∧ p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift p 3 R := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hl, hpq⟩ := h
  dsimp only at ht hl hpq
  subst ht hl
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  exact ⟨K, i1, i2, hK, hq, ggTorusLift_unitaryHypSix hK hn hp hp2 hpq⟩

end Labels

end CFSG.StandardType
