module

public import CFSG.RankThree.PartTwo.Sec11.SimsR1FieldCentL3Tools
public import CFSG.RankThree.PartTwo.KFacts.K72L3Unitary

public section

namespace CFSG.RankThree.PartTwo.Sec11.SimsR1.FieldCent.L3

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartTwo.KFacts (center_unitarySU_three
  unitaryScalars_three_eq_bot_of_mod_three unitaryProj_three_injective
  nonempty_unitaryPSU_mulEquiv_projSU)
open Matrix

theorem unitaryFieldData_galoisField {m : ℕ} (hm : 1 ≤ m) :
    UnitaryFieldData 2 m (GaloisField 2 (2 * m)) :=
  ⟨Nat.prime_two, hm, GaloisField.card 2 _ (by omega)⟩

theorem nonempty_unitarySU_mulEquiv_projSU {m : ℕ} (hm : 1 ≤ m) (hq : 2 ^ m % 3 = 1) :
    Nonempty (unitarySU 2 m (GaloisField 2 (2 * m)) 3 ≃* projSU 3 2 m) := by
  have h := unitaryFieldData_galoisField hm
  obtain ⟨φ⟩ := nonempty_unitaryPSU_mulEquiv_projSU h
  have hbij : Function.Bijective (unitaryProj h 3) :=
    ⟨unitaryProj_three_injective h hq, unitaryProj_surjective h 3⟩
  exact ⟨(MulEquiv.ofBijective _ hbij).trans φ⟩

theorem isSimpleGroup_unitarySU {m : ℕ} (hm : 2 ≤ m) (hq : 2 ^ m % 3 = 1) :
    IsSimpleGroup (unitarySU 2 m (GaloisField 2 (2 * m)) 3) ∧
      ∃ a b : unitarySU 2 m (GaloisField 2 (2 * m)) 3, a * b ≠ b * a := by
  have h := unitaryFieldData_galoisField (m := m) (by omega)
  have hq2 : 2 < 2 ^ m :=
    lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hm : 2 ^ 2 ≤ 2 ^ m)
  have hcard : Nat.card (GaloisField 2 (2 * m)) = (2 ^ m) ^ 2 := by
    rw [h.card, ← pow_mul, mul_comm]
  have hnq : ((3 : ℕ), 2 ^ m) ≠ (3, 2) := by
    intro h3
    simp only [Prod.mk.injEq, true_and] at h3
    omega
  refine isSimpleGroup_of_quasisimple_center_eq_bot
    (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hcard le_rfl hnq).1 ?_
  rw [center_unitarySU_three (h := h) hq2, unitaryScalars_three_eq_bot_of_mod_three h hq]

theorem bar_mul_self_eq_one {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {r : ℕ}
    (hr : r ∣ p ^ f + 1) {u : Kˣ} (hu : u ^ r = 1) : h.bar (u : K) * (u : K) = 1 := by
  obtain ⟨c, hc⟩ := hr
  have h1 : u ^ (p ^ f + 1) = 1 := by rw [hc, pow_mul, hu, one_pow]
  have h2 : ((u ^ (p ^ f + 1) : Kˣ) : K) = 1 := by rw [h1, Units.val_one]
  rw [Units.val_pow_eq_pow_val, pow_succ] at h2
  rw [UnitaryFieldData.bar_apply]
  exact h2

theorem torusGL_mem_unitarySU {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    {r : ℕ} (hr : r ∣ p ^ f + 1) {x y : Kˣ} (hx : x ^ r = 1) (hy : y ^ r = 1) :
    torusGL K (x, y) ∈ unitarySU p f K 3 := by
  have hz : ((x * y)⁻¹) ^ r = 1 := by rw [inv_pow, mul_pow, hx, hy, one_mul, inv_one]
  refine (mem_unitarySU_iff h).mpr ⟨det_torusMat (x, y), ?_⟩
  change ((Matrix.diagonal ![(x : K), (y : K), (((x * y)⁻¹ : Kˣ) : K)]).map h.bar)ᵀ *
    Matrix.diagonal ![(x : K), (y : K), (((x * y)⁻¹ : Kˣ) : K)] = 1
  rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
    ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i
  · exact bar_mul_self_eq_one h hr hx
  · exact bar_mul_self_eq_one h hr hy
  · exact bar_mul_self_eq_one h hr hz

theorem exists_injective_rankTwo_su {m : ℕ} (hm : 1 ≤ m) {r : ℕ} [Fact r.Prime]
    (hr : r ∣ 2 ^ m + 1) :
    ∃ ψ : Multiplicative (Fin 2 → ZMod r) →* unitarySU 2 m (GaloisField 2 (2 * m)) 3,
      Function.Injective ψ := by
  have h := unitaryFieldData_galoisField hm
  have hdvd : r ∣ Nat.card (GaloisField 2 (2 * m))ˣ := by
    rw [Nat.card_units, h.card, pow_mul']
    refine hr.trans ?_
    obtain ⟨N, hN⟩ : ∃ N, 2 ^ m = N + 1 :=
      ⟨2 ^ m - 1, by have := Nat.one_le_two_pow (n := m); omega⟩
    rw [hN]
    have h2 : (N + 1) ^ 2 = (N + 1 + 1) * N + 1 := by ring
    exact ⟨N, by omega⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' r hdvd
  have hζr : ζ ^ r = 1 := hζ ▸ pow_orderOf_eq_one ζ
  haveI : NeZero r := ⟨(Fact.out : r.Prime).ne_zero⟩
  have hι : ∀ a : Multiplicative (ZMod r), (powZMod r ζ hζr a) ^ r = 1 := fun a => by
    change (ζ ^ (Multiplicative.toAdd a).val) ^ r = 1
    rw [← pow_mul, Nat.mul_comm (Multiplicative.toAdd a).val r, pow_mul, hζr, one_pow]
  have hmem : ∀ v, rankTwoHom (torusGL (GaloisField 2 (2 * m))) r (powZMod r ζ hζr) v ∈
      unitarySU 2 m (GaloisField 2 (2 * m)) 3 :=
    fun v => torusGL_mem_unitarySU h hr (hι _) (hι _)
  refine ⟨(rankTwoHom (torusGL (GaloisField 2 (2 * m))) r (powZMod r ζ hζr)).codRestrict _ hmem,
    ?_⟩
  intro v w hvw
  exact rankTwoHom_injective torusGL_injective (powZMod_injective hζr hζ)
    (congrArg Subtype.val hvw)

theorem exists_prank_su {m : ℕ} (hm : 2 ≤ m) (hq : 2 ^ m % 3 = 1) :
    ∃ r : ℕ, ∃ _ : Fact r.Prime, 5 ≤ r ∧
      ∃ ψ : Multiplicative (Fin 2 → ZMod r) →* projSU 3 2 m, Function.Injective ψ := by
  set N := 2 ^ m with hN
  have h2N : 2 ∣ N := dvd_pow_self 2 (by omega)
  have h4 : 4 ≤ N := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hne : N + 1 ≠ 1 := by omega
  have hpr : (N + 1).minFac.Prime := Nat.minFac_prime hne
  have hdvd : (N + 1).minFac ∣ N + 1 := Nat.minFac_dvd _
  have h5 : 5 ≤ (N + 1).minFac := by
    by_contra hlt
    have hp2 := hpr.two_le
    have hcases : (N + 1).minFac = 2 ∨ (N + 1).minFac = 3 ∨ (N + 1).minFac = 4 := by omega
    rcases hcases with h | h | h
    · rw [h] at hdvd; omega
    · rw [h] at hdvd; omega
    · rw [h] at hpr; norm_num at hpr
  haveI : Fact (N + 1).minFac.Prime := ⟨hpr⟩
  obtain ⟨ψ, hψ⟩ := exists_injective_rankTwo_su (m := m) (by omega) (r := (N + 1).minFac) hdvd
  obtain ⟨ν⟩ := nonempty_unitarySU_mulEquiv_projSU (m := m) (by omega) hq
  exact ⟨_, ⟨hpr⟩, h5, ν.toMonoidHom.comp ψ, ν.injective.comp hψ⟩

end CFSG.RankThree.PartTwo.Sec11.SimsR1.FieldCent.L3
