module

import CFSG.LieType.Steinberg.Collection
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartTwo.KFacts.K73L27
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2RootSylow

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS10Borel

open CFSG.GorensteinWalter CFSG.LieType.Steinberg CFSG.RankThree.PartTwo.KFacts
open scoped MatrixGroups

variable {K : Type*} [Field K]

@[expose] def sl2Diag {l : K} (hl : l ≠ 0) : SL(2, K) :=
  ⟨!![l, 0; 0, l⁻¹], by simp [Matrix.det_fin_two_of, hl]⟩

theorem sl2Diag_mem_borel {l : K} (hl : l ≠ 0) : sl2Diag hl ∈ sl2Borel K :=
  (sl2_mem_stabilizer_infinity_iff _).mpr rfl

theorem psl2_conj_sl2Diag {l : K} (hl : l ≠ 0) (x : K) :
    psl2QuotientMap K (sl2Diag hl) * psl2QuotientMap K (sl2UpperUnipotent x) *
        (psl2QuotientMap K (sl2Diag hl))⁻¹ =
      psl2QuotientMap K (sl2UpperUnipotent (l ^ 2 * x)) := by
  rw [← map_inv, ← map_mul, ← map_mul, sl2Borel_conj_upperUnipotent (sl2Diag_mem_borel hl)]
  rfl

theorem eq_of_psl2Upper_eq {s t : K}
    (h : psl2QuotientMap K (sl2UpperUnipotent s) = psl2QuotientMap K (sl2UpperUnipotent t)) :
    s = t := by
  have hq : psl2QuotientMap K (sl2UpperUnipotent (s - t)) = 1 := by
    rw [sub_eq_add_neg, ← sl2UpperUnipotent_mul, map_mul, ← sl2UpperUnipotent_inv, map_inv, h,
      mul_inv_cancel]
  have hcenter : sl2UpperUnipotent (s - t) ∈ Subgroup.center (SL(2, K)) :=
    (QuotientGroup.eq_one_iff _).mp hq
  have hscalar := Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center hcenter (0 : Fin 2)
  have h01 := congrFun (congrFun hscalar (0 : Fin 2)) (1 : Fin 2)
  apply sub_eq_zero.mp
  simpa [sl2UpperUnipotent] using h01.symm

theorem sl2Diag_pow_mem_center {l : K} (hl : l ≠ 0) {n : ℕ} (hn : l ^ n = -1) :
    sl2Diag hl ^ n ∈ Subgroup.center (SL(2, K)) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨-1, by simp, ?_⟩
  have hd : (sl2Diag hl : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![l, l⁻¹] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sl2Diag]
  rw [Matrix.SpecialLinearGroup.coe_pow, hd, Matrix.diagonal_pow]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, hn, inv_pow]

theorem exists_psl2_torus_thirteen :
    ∃ h ∈ psl2Borel (GaloisField 3 3), orderOf h = 13 ∧
      ∀ u ∈ psl2UpperUnipotentSubgroup (GaloisField 3 3), h * u * h⁻¹ = u → u = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  set K := GaloisField 3 3
  have hK : Nat.card K = 27 := by rw [GaloisField.card 3 3 (by norm_num)]; norm_num
  have hKu : Nat.card Kˣ = 26 := by
    have := Nat.card_eq_card_units_add_one (α := K)
    omega
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hgo : orderOf g = 26 := by rw [orderOf_eq_card_of_forall_mem_zpowers hg, hKu]
  have hl0 : (g : K) ≠ 0 := g.ne_zero
  have hpow : ∀ n : ℕ, (g : K) ^ n = 1 → 26 ≤ n ∨ n = 0 := by
    intro n hn
    by_cases hn0 : n = 0
    · exact Or.inr hn0
    · left
      have h1 : g ^ n = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hn, Units.val_one])
      rw [← hgo]
      exact orderOf_le_of_pow_eq_one (Nat.pos_of_ne_zero hn0) h1
  have hl13 : (g : K) ^ 13 = -1 := by
    have h26 : (g : K) ^ 13 * (g : K) ^ 13 = 1 := by
      rw [← pow_add, ← Units.val_pow_eq_pow_val, show 13 + 13 = 26 by rfl, ← hgo,
        pow_orderOf_eq_one, Units.val_one]
    rcases mul_self_eq_one_iff.mp h26 with h1 | h1
    · rcases hpow 13 h1 with h | h <;> omega
    · exact h1
  have hl2 : (g : K) ^ 2 ≠ 1 := fun h1 => by rcases hpow 2 h1 with h | h <;> omega
  refine ⟨psl2QuotientMap K (sl2Diag hl0), ?_, ?_, ?_⟩
  · rw [psl2Borel_eq_map]
    exact ⟨_, sl2Diag_mem_borel hl0, rfl⟩
  · apply orderOf_eq_prime
    · rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr (sl2Diag_pow_mem_center hl0 hl13)
    · intro h1
      have h2 := psl2_conj_sl2Diag hl0 1
      rw [h1, one_mul, inv_one, mul_one, mul_one] at h2
      exact hl2 (eq_of_psl2Upper_eq h2).symm
  · intro u hu hfix
    obtain ⟨t, rfl⟩ := (mem_psl2UpperUnipotentSubgroup_iff u).mp hu
    rw [psl2_conj_sl2Diag] at hfix
    have h1 := eq_of_psl2Upper_eq hfix
    have ht : t = 0 := by
      have h2 : ((g : K) ^ 2 - 1) * t = 0 := by rw [sub_mul, one_mul, h1, sub_self]
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd (sub_eq_zero.mp h) hl2
      · exact h
    rw [ht, sl2UpperUnipotent_zero, map_one]

theorem exists_normalizer_orderOf_thirteen {X : Type*} [Group X] [Finite X]
    (e : X ≃* PSL2 (GaloisField 3 3)) {S : Subgroup X} (hS : Nat.card S = 27) :
    ∃ x ∈ Subgroup.normalizer (S : Set X), orderOf x = 13 ∧
      ∀ s ∈ S, x * s * x⁻¹ = s → s = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K := GaloisField 3 3
  have hK : Nat.card K = 3 ^ 3 := GaloisField.card 3 3 (by norm_num)
  set U := psl2UpperUnipotentSubgroup K with hU
  have hUcard : Nat.card U = 27 := by rw [hU, psl2UpperUnipotentSubgroup_card, hK]; norm_num
  set S' := S.map e.toMonoidHom with hS'
  have hS'card : Nat.card S' = 27 := by rw [hS', Subgroup.card_map_of_injective e.injective, hS]
  have hS'3 : IsPGroup 3 S' := IsPGroup.of_card (n := 3) (by rw [hS'card]; norm_num)
  obtain ⟨y, hy⟩ := exists_map_conj_le_psl2UpperUnipotentSubgroup hK hS'3
  have hyU : S'.map (MulAut.conj y).toMonoidHom = U := Subgroup.eq_of_le_of_card_ge hy (by
    rw [Subgroup.card_map_of_injective (MulAut.conj y).injective, hS'card, hUcard])
  obtain ⟨h, hhB, hho, hhfix⟩ := exists_psl2_torus_thirteen
  have hhN : h ∈ Subgroup.normalizer (U : Set (PSL2 K)) := by
    rw [hU, psl2UpperUnipotent_normalizer_eq_borel]
    exact hhB
  set z := y⁻¹ * h * y with hz
  have hzN : z ∈ Subgroup.normalizer (S' : Set (PSL2 K)) := by
    rw [mem_normalizer_iff_map_conj, hz, map_conj_mul, map_conj_mul, hyU,
      mem_normalizer_iff_map_conj.mp hhN, ← hyU, ← map_conj_mul, inv_mul_cancel, map_conj_one]
  refine ⟨e.symm z, ?_, ?_, ?_⟩
  · rw [mem_normalizer_iff_map_conj]
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [Subgroup.map_map]
    have h1 := mem_normalizer_iff_map_conj.mp hzN
    rw [hS'] at h1
    conv_rhs => rw [← h1]
    rw [Subgroup.map_map]
    congr 1
    ext w
    simp [MulAut.conj_apply]
  · rw [MulEquiv.orderOf_eq, hz, ← hho]
    have h1 := orderOf_injective (MulAut.conj y⁻¹).toMonoidHom (MulAut.conj y⁻¹).injective h
    rw [← h1]
    congr 1
    simp
  · intro s hs hfix
    have h1 : z * e s * z⁻¹ = e s := by
      have := congrArg e hfix
      simpa [map_mul, map_inv] using this
    have hsU : y * e s * y⁻¹ ∈ U := by
      rw [← hyU]
      exact ⟨e s, ⟨s, hs, rfl⟩, rfl⟩
    have h2 : h * (y * e s * y⁻¹) * h⁻¹ = y * e s * y⁻¹ := by
      calc h * (y * e s * y⁻¹) * h⁻¹ = y * (z * e s * z⁻¹) * y⁻¹ := by rw [hz]; group
        _ = y * e s * y⁻¹ := by rw [h1]
    have h3 := hhfix _ hsU h2
    have h4 : e s = 1 := by
      have := congrArg (fun w => y⁻¹ * w * y) h3
      simpa [mul_assoc] using this
    exact (MulEquiv.map_eq_one_iff e).mp h4

end CFSG.RankThree.PartTwo.KFacts.KS10Borel
