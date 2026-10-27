module

public import CFSG.RankThree.PartOne.KF.U4Blk
public import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.RankThree.PartOne.KFU

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitaryCoord

theorem coordEmbed_injective {n : ℕ} {K : Type} [Field K] {i j : Fin n} (hij : i ≠ j) :
    Function.Injective (fun X : Matrix (Fin 2) (Fin 2) K => coordEmbed K i j X) := by
  have h := coordProj_mul_coordIncl (K := K) hij
  have key : ∀ Z : Matrix (Fin 2) (Fin 2) K,
      coordProj K i j * coordEmbed K i j Z * coordIncl K i j = Z := by
    intro Z
    have h' : ∀ M : Matrix (Fin 2) (Fin n) K,
        coordProj K i j * (coordIncl K i j * M) = M := fun M => by
      rw [← Matrix.mul_assoc, h, Matrix.one_mul]
    unfold coordEmbed
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_assoc, h, h',
      add_sub_cancel]
  intro X Y hXY
  have := congrArg (fun M => coordProj K i j * M * coordIncl K i j) hXY
  simpa only [key] using this

theorem nonempty_blk_mulEquiv {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    {i j : Fin n} (hij : i ≠ j) : Nonempty (↥(blk h hij) ≃* ↥(gramSU h (idGram K 2))) := by
  have hinj : Function.Injective (coordSUHom h hij) := by
    intro X Y hXY
    have hmat := congrArg (fun A : primeFormUnitary h (idGram K n) =>
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) hXY
    exact Subtype.ext (Units.ext (coordEmbed_injective hij hmat))
  exact ⟨((MonoidHom.ofInjective hinj).trans (Subgroup.equivMapOfInjective (coordSU h hij)
    (primeFormUnitary h (idGram K n)).subtype (Subgroup.subtype_injective _))).symm⟩

theorem nonempty_gramSU_two_mulEquiv_SL2 {ℓ f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) :
    Nonempty (↥(gramSU h (idGram K 2)) ≃* SpecialLinearGroup (Fin 2) h.fixedField) := by
  have hfr : Module.finrank K (Fin 2 → K) = 2 := by rw [Module.finrank_fin_fun]
  obtain ⟨φ⟩ := CFSG.RankThree.CentralLift.nonempty_sesqSpecialUnitaryGroup_mulEquiv_gramSU h
    (B := idForm h 2) (Pi.basisFun K (Fin 2)) (G := idGram K 2) (fun a b => by
      rw [Pi.basisFun_apply, Pi.basisFun_apply]
      exact gramForm_single h (idGram K 2) a b)
  obtain ⟨ψ⟩ := CFSG.RankThree.Classical.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SL2 h
    (idForm_isSymm h 2) (idForm_separatingLeft h 2) hfr
  exact ⟨φ.symm.trans ψ⟩

theorem center_SL2_eq_bot {F : Type} [Field F] [CharP F 2] :
    Subgroup.center (SpecialLinearGroup (Fin 2) F) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  have hr1 : r = 1 := by
    have h0 : (r - 1) ^ 2 = 0 := by linear_combination hr - (r - 1) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h0)
  subst hr1
  ext1
  rw [Matrix.SpecialLinearGroup.coe_one, ← hrA, map_one]

theorem nonempty_SL2_mulEquiv_statedProj {F : Type} [Field F] [CharP F 2] :
    Nonempty (SpecialLinearGroup (Fin 2) F ≃* StatedProj (StatedSL 2 F)) :=
  ⟨((QuotientGroup.quotientMulEquivOfEq center_SL2_eq_bot).trans
    QuotientGroup.quotientBot).symm.trans (projectiveSpecialLinearGroupEquivStatedProj 2 F)⟩

theorem su2_model {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) (hf : 2 ≤ f) :
    CFSG.IsQuasisimple ↥(gramSU h (idGram K 2)) ∧ Subgroup.center ↥(gramSU h (idGram K 2)) = ⊥ ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ f ∧
        Nonempty (↥(gramSU h (idGram K 2)) ≃* StatedProj (StatedSL 2 F)) := by
  obtain ⟨φ⟩ := nonempty_gramSU_two_mulEquiv_SL2 h
  have hfin := h.finite
  have hq : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hcard : Nat.card h.fixedField = 2 ^ f := h.card_fixedField
  have : CharP h.fixedField 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hcard
  have h4 : ∃ s : Finset h.fixedField, s.card = 4 := by
    have := Fintype.ofFinite h.fixedField
    have hle : 4 ≤ (Finset.univ : Finset h.fixedField).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcard]
      exact hq
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq hle
    exact ⟨s, hs⟩
  obtain ⟨e⟩ := nonempty_SL2_mulEquiv_statedProj (F := h.fixedField)
  exact ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv φ.symm
      (CFSG.RankThree.Classical.isQuasisimple_SL2 h4),
    by rw [← Subgroup.map_center_eq φ.symm, center_SL2_eq_bot, Subgroup.map_bot],
    h.fixedField, inferInstance, inferInstance, hcard, ⟨φ.trans e⟩⟩

theorem blk_model {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) (hf : 2 ≤ f)
    {i j : Fin n} (hij : i ≠ j) :
    CFSG.IsQuasisimple ↥(blk h hij) ∧ Subgroup.center ↥(blk h hij) = ⊥ ∧
      CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥(blk h hij) .PSL 2 2 f := by
  obtain ⟨e⟩ := nonempty_blk_mulEquiv h hij
  obtain ⟨hQ, hZ, F, hF, hFin, hcard, ⟨ψ⟩⟩ := su2_model h hf
  have hq : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hQ,
    by rw [← Subgroup.map_center_eq e.symm, hZ, Subgroup.map_bot],
    ⟨Nat.prime_two, by omega, le_rfl, ?_, ?_⟩,
    F, hF, hFin, hcard, ⟨e.trans ψ⟩⟩
  · intro hc
    simp only [Prod.mk.injEq, true_and] at hc
    omega
  · intro hc
    simp only [Prod.mk.injEq, true_and] at hc
    omega

section Orders

open CFSG.Open CFSG.Timmesfeld.ClassicalOrders

theorem ordA_one_two_pow {f : ℕ} (hf : 1 ≤ f) :
    ordA 1 (2 ^ f) = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
  have hg : Nat.gcd 2 (2 ^ f - 1) = 1 :=
    Nat.coprime_two_left.mpr (by simpa using odd_two_pow_pow_sub_one hf (n := 1) le_rfl)
  have h1 : Finset.Icc 2 (1 + 1) = {2} := by decide
  simp only [ordA, h1, Finset.prod_singleton, hg, Nat.div_one, Nat.reduceAdd, Nat.reduceMul,
    Nat.reduceDiv, pow_one]

theorem ordTwistedA_two_mul_gcd (q : ℕ) :
    ordTwistedA 2 q * Nat.gcd 3 (q + 1) = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
  have h2 : Finset.Icc 2 (2 + 1) = {2, 3} := by decide
  simp only [ordTwistedA, h2, Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv]
  rw [Finset.prod_pair (by decide)]
  have e2 : ((q : ℤ) ^ 2 - (-1) ^ 2).toNat = q ^ 2 - 1 := by
    have : ((q : ℤ) ^ 2 - (-1) ^ 2) = ((q ^ 2 : ℕ) : ℤ) - 1 := by push_cast; ring
    rw [this]; omega
  have e3 : ((q : ℤ) ^ 3 - (-1) ^ 3).toNat = q ^ 3 + 1 := by
    have : ((q : ℤ) ^ 3 - (-1) ^ 3) = ((q ^ 3 : ℕ) : ℤ) + 1 := by push_cast; ring
    rw [this]; omega
  rw [e2, e3]
  refine Nat.div_mul_cancel ?_
  have h3 : q + 1 ∣ q ^ 3 + 1 := by
    simpa using Odd.nat_add_dvd_pow_add_pow q 1 (by decide : Odd 3)
  exact Dvd.dvd.mul_left (Dvd.dvd.mul_left ((Nat.gcd_dvd_right 3 (q + 1)).trans h3) _) _

theorem eq_of_two_pow_mul_eq_of_odd {f g m n : ℕ} (hm : Odd m) (hn : Odd n)
    (h : 2 ^ f * m = 2 ^ g * n) : f = g := by
  have h1 : f ≤ g := by
    have h' : 2 ^ f ∣ 2 ^ g * n := ⟨m, h.symm⟩
    have := (Nat.Coprime.pow_left f (Nat.coprime_two_left.mpr hn)).dvd_of_dvd_mul_right h'
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp this
  have h2 : g ≤ f := by
    have h' : 2 ^ g ∣ 2 ^ f * m := ⟨n, h⟩
    have := (Nat.Coprime.pow_left g (Nat.coprime_two_left.mpr hm)).dvd_of_dvd_mul_right h'
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp this
  omega

theorem ordA_one_ne_ordTwistedA_two {f f' : ℕ} (hf : 1 ≤ f) (hf' : 1 ≤ f') :
    CFSG.Open.ordA 1 (2 ^ f) ≠ CFSG.Open.ordTwistedA 2 (2 ^ f') := by
  intro heq
  have hB := ordTwistedA_two_mul_gcd (2 ^ f')
  rw [← heq, ordA_one_two_pow hf] at hB
  generalize hd : Nat.gcd 3 (2 ^ f' + 1) = d at hB
  have hdodd : Odd d := by
    rw [← Nat.coprime_two_left]
    exact Nat.Coprime.coprime_dvd_right (hd ▸ Nat.gcd_dvd_left 3 (2 ^ f' + 1)) (by decide)
  have hd1 : 1 ≤ d := by
    rcases hdodd with ⟨k, rfl⟩
    omega
  have h1 : Odd ((2 ^ f) ^ 2 - 1) := odd_two_pow_pow_sub_one hf (by norm_num)
  have h2 : Odd (((2 ^ f') ^ 2 - 1) * ((2 ^ f') ^ 3 + 1)) :=
    (odd_two_pow_pow_sub_one hf' (by norm_num)).mul (odd_two_pow_pow_add_one hf' (by norm_num))
  have key : 2 ^ f * (((2 ^ f) ^ 2 - 1) * d) = 2 ^ (3 * f') * (((2 ^ f') ^ 2 - 1) *
      ((2 ^ f') ^ 3 + 1)) := by
    rw [pow_mul', ← mul_assoc, hB]
  have hff : f = 3 * f' := eq_of_two_pow_mul_eq_of_odd (h1.mul hdodd) h2 key
  subst hff
  generalize ha : 2 ^ f' = a at hB
  have ha2 : 2 ≤ a := by
    rw [← ha]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f' := Nat.pow_le_pow_right (by norm_num) hf'
  have hb : 2 ^ (3 * f') = a ^ 3 := by rw [pow_mul', ha]
  rw [hb] at hB
  have hapos : 0 < a ^ 3 := by positivity
  have h3 : ((a ^ 3) ^ 2 - 1) * d = (a ^ 2 - 1) * (a ^ 3 + 1) := by
    apply Nat.eq_of_mul_eq_mul_left hapos
    rw [← mul_assoc]
    exact hB
  have hx : 4 ≤ a ^ 2 := by nlinarith
  have hy : 2 * a ^ 2 ≤ a ^ 3 := by nlinarith
  clear hB key heq h1 h2 hb ha hd
  generalize a ^ 2 = x at *
  generalize a ^ 3 = y at *
  have hx1 : 1 ≤ x := by omega
  have hy1 : 1 ≤ y ^ 2 := Nat.one_le_pow _ _ (by omega)
  zify [hx1, hy1] at h3
  have hd1' : (1 : ℤ) ≤ d := by exact_mod_cast hd1
  have hy1' : (1 : ℤ) ≤ (y : ℤ) ^ 2 := by exact_mod_cast hy1
  have e1 : 0 ≤ ((y : ℤ) ^ 2 - 1) * (d - 1) := mul_nonneg (by linarith) (by linarith)
  have e2 : 0 < ((y : ℤ) - x) * (y + 1) := mul_pos (by omega) (by omega)
  nlinarith

end Orders

theorem not_psu_three_quotient_of_psl_two {B : Type} [Group B] {f f' : ℕ}
    (hB : CFSG.Assembly.LowTwoRank.StatedClassicalModel B .PSL 2 2 f)
    (hZ : Subgroup.center B = ⊥) :
    ¬ CFSG.Assembly.LowTwoRank.StatedClassicalModel (B ⧸ Subgroup.center B) .PSU 3 2 f' := by
  intro hU
  have hf : 1 ≤ f := hB.1.2.1
  have hf' : 1 ≤ f' := hU.1.2.1
  have h1 : Nat.card B = CFSG.Open.ordA 1 (2 ^ f) :=
    (CFSG.Timmesfeld.card_statedClassicalModel_two hB).1 rfl
  have h2 : Nat.card (B ⧸ Subgroup.center B) = CFSG.Open.ordTwistedA 2 (2 ^ f') :=
    (CFSG.Timmesfeld.card_statedClassicalModel_two hU).2.1 rfl
  have hc : Nat.card (B ⧸ Subgroup.center B) = Nat.card B :=
    Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans
      QuotientGroup.quotientBot).toEquiv
  rw [hc, h1] at h2
  exact ordA_one_ne_ordTwistedA_two hf hf' h2

end CFSG.RankThree.PartOne.KFU
