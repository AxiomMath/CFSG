module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CZF
public import CFSG.Quasithin.Vol2.Ch10SecA1012P5Core
public import CFSG.Quasithin.Vol2.Ch10SecA1012P5Fix

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS.K7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem normalizes_of_mem (hyp : Hyp10 G T L I) {y : G} (hyL0 : y ∈ fsuL0 T L)
    (hyN : y ∈ Subgroup.normalizer (T0 T L : Set G)) :
    y ∈ Subgroup.normalizer (fsuUL T L I : Set G) ∧
      y ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
  ⟨SecA.le_normalizer_commutator (SecA.fsuL0_le_normalizer_fsuVM T L I)
      (SecA.fsuL0_le_normalizer hyp.fsu.maximal.1) hyL0,
    SecA.mem_normalizer_inf_of_mem (SecA.le_fsuL0 T L)
      (SecA.fsuL0_le_normalizer hyp.fsu.maximal.1) hyL0 hyN⟩

theorem pow_fix_V₁ (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h1 : Case10_1_1One T L I n)
    {y : G} (hyL0 : y ∈ fsuL0 T L) (hyN : y ∈ Subgroup.normalizer (T0 T L : Set G))
    (hyo : Odd (orderOf y)) :
    ∀ v ∈ fsuUL T L I, y ^ (2 ^ n - 1) * v * (y ^ (2 ^ n - 1))⁻¹ = v := by
  obtain ⟨hUab, F, _, _, _, -, hF, ⟨nc⟩⟩ := SecA.exists_natCoord hyp h1
  have : Fintype F := Fintype.ofFinite F
  have hFc : Fintype.card F = 2 ^ n := by rw [← Nat.card_eq_fintype_card, hF]
  obtain ⟨hyU, hyT⟩ := normalizes_of_mem hyp hyL0 hyN
  set d := conjAct (fsuUL T L I) ⟨y, hyU⟩ with hd
  have hdL : d ∈ autOn L (fsuUL T L I) :=
    SecA.conjAct_mem_autOn_of_mem_fsuL0 h37 h38 hyp hyL0 hyU
  have hdN := SecA.conjAct_mem_normalizer_autOn hyU hyT
  set γ := nc.eρ.symm ⟨d, hdL⟩ with hγ
  have hγd : ((nc.eρ γ : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I)) = d := by
    rw [hγ, MulEquiv.apply_symm_apply]
  have hc : ∃ c' : F, (nc.g * γ * nc.g⁻¹) * SecA.unipSL 1 * (nc.g * γ * nc.g⁻¹)⁻¹ =
      SecA.unipSL c' := by
    have h1 : ((nc.eρ (nc.g⁻¹ * SecA.unipSL 1 * nc.g) : ↥(autOn L (fsuUL T L I))) :
        MulAut ↥(fsuUL T L I)) ∈ autOn (T ⊓ L) (fsuUL T L I) :=
      (nc.unip _).mpr ⟨1, by group⟩
    have h2 : ((nc.eρ (γ * (nc.g⁻¹ * SecA.unipSL 1 * nc.g) * γ⁻¹) :
        ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I)) ∈ autOn (T ⊓ L) (fsuUL T L I) := by
      rw [map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hγd]
      exact (Subgroup.mem_normalizer_iff.mp hdN _).mp h1
    obtain ⟨c', hc'⟩ := (nc.unip _).mp h2
    exact ⟨c', by rw [← hc']; group⟩
  have hγo : Odd (orderOf γ) := by
    have h1 : orderOf γ = orderOf d := by
      rw [← MulEquiv.orderOf_eq nc.eρ γ, ← Subgroup.orderOf_coe, hγd]
    rw [h1]
    exact SecA.odd_orderOf_conjAct hyU hyo
  have hp := pow_card_sub_one_eq_one hc hγo
  rw [hFc] at hp
  have hdp : d ^ (2 ^ n - 1) = 1 := by
    rw [← hγd, ← Subgroup.coe_pow, ← map_pow, hp, map_one, Subgroup.coe_one]
  intro v hv
  have h := congrArg (fun φ : MulAut ↥(fsuUL T L I) => ((φ ⟨v, hv⟩ : ↥(fsuUL T L I)) : G)) hdp
  simp only [hd, ← map_pow, SecA.coe_conjAct_apply', MulAut.one_apply,
    Subgroup.coe_pow] at h
  exact h

omit [Finite G] in
theorem conj_mem_of_mem {y t : G} (ht : t ∈ T) (hyL0 : y ∈ fsuL0 T L)
    (hyN : y ∈ Subgroup.normalizer (T0 T L : Set G)) :
    t * y * t⁻¹ ∈ fsuL0 T L ∧ t * y * t⁻¹ ∈ Subgroup.normalizer (T0 T L : Set G) :=
  ⟨(Subgroup.mem_normalizer_iff.mp (SecA.le_fsuM T L ht) y).mp hyL0,
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (SecA.le_normalizer_T0 T L ht) hyN)
      (Subgroup.inv_mem _ (SecA.le_normalizer_T0 T L ht))⟩

theorem pow_eq_one (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h1 : Case10_1_1One T L I n)
    {y : G} (hyL0 : y ∈ fsuL0 T L) (hyN : y ∈ Subgroup.normalizer (T0 T L : Set G))
    (hyo : Odd (orderOf y)) : y ^ (2 ^ n - 1) = 1 := by
  obtain ⟨t, ht, htn⟩ : ∃ t ∈ T, t ∉ Subgroup.normalizer (L : Set G) := by
    by_contra h
    push Not at h
    exact hyp.not_normal h
  obtain ⟨h2L0, h2N⟩ := conj_mem_of_mem ht hyL0 hyN
  have h2o : Odd (orderOf (t * y * t⁻¹)) := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hyo
  have h2 := pow_fix_V₁ h37 h38 hyp h1 h2L0 h2N h2o
  have h2' : ∀ u ∈ fsuUL T L I,
      t * y ^ (2 ^ n - 1) * t⁻¹ * u * (t * y ^ (2 ^ n - 1) * t⁻¹)⁻¹ = u := by
    intro u hu
    have := h2 u hu
    rwa [conj_pow] at this
  exact SecA.eq_one_of_forall_conj_eq h37 h38 hyp ht htn ((fsuL0 T L).pow_mem hyL0 _)
    (Odd.of_dvd_nat hyo (orderOf_pow_dvd _)) (pow_fix_V₁ h37 h38 hyp h1 hyL0 hyN hyo)
    (SecA.forall_conj_eq_of_conj h2')

theorem four_pow_mod (k : ℕ) : 4 ^ k % 15 = 1 ∨ 4 ^ k % 15 = 4 := by
  induction k with
  | zero => left; rfl
  | succ k ih =>
    rw [pow_succ, Nat.mul_mod]
    rcases ih with h | h <;> rw [h] <;> norm_num

theorem coprime_two_pow_sub_one {n : ℕ} (hn : Odd n) : Nat.Coprime (2 ^ n - 1) 360 := by
  obtain ⟨k, rfl⟩ := hn
  have e2 : 2 ^ (2 * k + 1) = 2 * 4 ^ k := by
    rw [pow_succ, pow_mul, mul_comm]
    norm_num
  have h15 : (2 ^ (2 * k + 1) - 1) % 15 = 1 ∨ (2 ^ (2 * k + 1) - 1) % 15 = 7 := by
    rw [e2]
    have h1 : 1 ≤ 4 ^ k := Nat.one_le_pow _ _ (by norm_num)
    rcases four_pow_mod k with h | h <;> omega
  have hodd : (2 ^ (2 * k + 1) - 1) % 2 = 1 := by
    rw [e2]
    have h1 : 1 ≤ 4 ^ k := Nat.one_le_pow _ _ (by norm_num)
    omega
  have e : (360 : ℕ) = 2 ^ 3 * 3 ^ 2 * 5 := by norm_num
  rw [e]
  refine Nat.Coprime.mul_right (Nat.Coprime.mul_right ?_ ?_) ?_
  · exact Nat.Coprime.pow_right _ (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd
      Nat.prime_two).mpr (by omega)))
  · exact Nat.Coprime.pow_right _ (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd
      Nat.prime_three).mpr (by omega)))
  · exact Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr (by omega))

end C11AmS.K7

end CFSG.Quasithin.Vol2.Ch10.SecB
