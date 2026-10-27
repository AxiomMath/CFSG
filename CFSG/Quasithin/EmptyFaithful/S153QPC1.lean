module

public import Mathlib.GroupTheory.Transfer
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.Quasithin.QP

section Lift

variable {H K : Type*} [Group H] [Group K] {p : ℕ} [Fact p.Prime]

theorem forall_isCyclic_of_surjective [Finite H] [Finite K] (f : H →* K) (hf : Function.Surjective f)
    (hH : ∀ P : Subgroup H, IsPGroup p P → IsCyclic P) :
    ∀ E : Subgroup K, IsPGroup p E → IsCyclic E := by
  intro E hE
  obtain ⟨P', hEP'⟩ := hE.exists_le_sylow
  obtain ⟨P, rfl⟩ := Sylow.mapSurjective_surjective (p := p) hf P'
  have hP : IsCyclic (P : Subgroup H) := hH _ P.isPGroup'
  have hPf : IsCyclic ((P : Subgroup H).map f) :=
    isCyclic_of_surjective (f.subgroupMap (P : Subgroup H))
      (MonoidHom.subgroupMap_surjective f (P : Subgroup H))
  have hE' : E ≤ (P : Subgroup H).map f := by
    simpa [Sylow.coe_mapSurjective] using hEP'
  have : IsCyclic (E.subgroupOf ((P : Subgroup H).map f)) := inferInstance
  exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hE').toMonoidHom
    (MulEquiv.surjective _)

end Lift

section Center

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem eq_one_of_mem_center_of_isPerfect [Group.IsPerfect G] (P : Sylow p G)
    (hab : ∀ x ∈ (P : Subgroup G), ∀ y ∈ (P : Subgroup G), x * y = y * x) {z : G}
    (hz : z ∈ Subgroup.center G) (hzp : z ^ p = 1) : z = 1 := by
  have hfin : (P : Subgroup G).FiniteIndex := inferInstance
  let ϕ : (P : Subgroup G) →* Abelianization (P : Subgroup G) := Abelianization.of
  have key : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * z ^ k * g₀ ∈ (P : Subgroup G) → g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have h := Subgroup.mem_center_iff.mp (pow_mem hz k) g₀⁻¹
    calc g₀⁻¹ * z ^ k * g₀ = z ^ k * g₀⁻¹ * g₀ := by rw [← h]
      _ = z ^ k := by group
  have hmem : z ^ (P : Subgroup G).index ∈ (P : Subgroup G) := MonoidHom.transfer_eq_pow_aux z key
  have h1 := MonoidHom.transfer_eq_pow ϕ z key
  have h2 : MonoidHom.transfer ϕ z = 1 := by
    have hperf : Group.IsPerfect (MonoidHom.transfer ϕ).range := Group.IsPerfect.range _
    have hsub : Subsingleton (MonoidHom.transfer ϕ).range :=
      Group.IsPerfect.subsingleton_of_isMulCommutative
    exact congrArg Subtype.val (Subsingleton.elim (⟨_, ⟨z, rfl⟩⟩ : (MonoidHom.transfer ϕ).range) 1)
  rw [h1] at h2
  have h3 : (⟨z ^ (P : Subgroup G).index, hmem⟩ : (P : Subgroup G)) ∈ commutator (P : Subgroup G) :=
    (QuotientGroup.eq_one_iff _).1 h2
  have h4 : commutator (P : Subgroup G) ≤ ⊥ := by
    rw [commutator_def]
    refine Subgroup.commutator_le.mpr fun g₁ _ g₂ _ => ?_
    rw [Subgroup.mem_bot, commutatorElement_def]
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one]
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
    exact hab _ g₁.2 _ g₂.2
  have h5 : z ^ (P : Subgroup G).index = 1 := by
    have := h4 h3
    rw [Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  have h6 : z ^ Nat.gcd p (P : Subgroup G).index = 1 := pow_gcd_eq_one.2 ⟨hzp, h5⟩
  have h7 : Nat.gcd p (P : Subgroup G).index = 1 :=
    (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (Fact.out)).2 P.not_dvd_index)).symm
  rwa [h7, pow_one] at h6

end Center

section Arith

theorem five_dvd_two_pow_sub_one_of_seventeen_dvd {n : ℕ}
    (h : 17 ∣ ∏ i : Fin 3, ((2 ^ n) ^ 3 - (2 ^ n) ^ (i : ℕ))) : 5 ∣ 2 ^ n - 1 := by
  have hn8 : (2 : ZMod 17) ^ n = 2 ^ (n % 8) := by
    conv_lhs => rw [← Nat.div_add_mod n 8, pow_add, pow_mul]
    have : (2 : ZMod 17) ^ 8 = 1 := by decide
    rw [this, one_pow, one_mul]
  have h' : ((∏ i : Fin 3, ((2 ^ n) ^ 3 - (2 ^ n) ^ (i : ℕ)) : ℕ) : ZMod 17) = 0 :=
    (ZMod.natCast_eq_zero_iff _ 17).2 h
  rw [Fin.prod_univ_three] at h'
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at h'
  have hle : ∀ i : ℕ, i ≤ 3 → (2 ^ n) ^ i ≤ (2 ^ n) ^ 3 := fun i hi =>
    Nat.pow_le_pow_right (Nat.one_le_two_pow) hi
  have e0 : (((2 ^ n) ^ 3 - (2 ^ n) ^ 0 : ℕ) : ZMod 17) = ((2 : ZMod 17) ^ n) ^ 3 - 1 := by
    rw [Nat.cast_sub (hle 0 (by norm_num))]
    push_cast
    ring
  have e1 : (((2 ^ n) ^ 3 - (2 ^ n) ^ 1 : ℕ) : ZMod 17) = ((2 : ZMod 17) ^ n) ^ 3 - (2 : ZMod 17) ^ n := by
    rw [Nat.cast_sub (hle 1 (by norm_num))]
    push_cast
    ring
  have e2 : (((2 ^ n) ^ 3 - (2 ^ n) ^ 2 : ℕ) : ZMod 17) = ((2 : ZMod 17) ^ n) ^ 3 - ((2 : ZMod 17) ^ n) ^ 2 := by
    rw [Nat.cast_sub (hle 2 (by norm_num))]
    push_cast
    ring
  rw [Nat.cast_mul, Nat.cast_mul, e0, e1, e2, hn8] at h'
  have hr : n % 8 = 0 ∨ n % 8 = 4 := by
    have hlt : n % 8 < 8 := Nat.mod_lt _ (by norm_num)
    generalize n % 8 = r at h' hlt
    interval_cases r <;> first | omega | (exfalso; revert h'; decide)
  have h4 : n % 4 = 0 := by omega
  obtain ⟨m, hm⟩ : ∃ m, n = 4 * m := ⟨n / 4, by omega⟩
  have hmod : 16 ^ m ≡ 1 ^ m [MOD 5] := Nat.ModEq.pow m (by decide)
  rw [one_pow] at hmod
  have : 2 ^ n = 16 ^ m := by rw [hm, pow_mul]; norm_num
  rw [this]
  exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).1 hmod.symm

end Arith

section SL2

open Matrix

theorem sl2_isSimpleGroup {K : Type} [Field K] [CharP K 2] (h4 : 4 ≤ Nat.card K) :
    IsSimpleGroup (SpecialLinearGroup (Fin 2) K) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hc : Subgroup.center (SpecialLinearGroup (Fin 2) K) = ⊥ := by
    refine eq_bot_iff.mpr fun A hA => ?_
    obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
    rw [Fintype.card_fin] at hr
    have h5 : (r - 1) ^ 2 = 0 := by linear_combination hr + (1 - r) * h2
    have hr1 : r = 1 := sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h5)
    subst hr1
    rw [Subgroup.mem_bot]
    ext i j
    have := congrFun (congrFun hrA i) j
    simpa [Matrix.scalar_apply, Matrix.one_apply] using this.symm
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  have e : SpecialLinearGroup (Fin 2) K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hc.symm)
  exact e.isSimpleGroup

theorem card_galoisField_two_four : Nat.card (GaloisField 2 4) = 16 := by
  rw [GaloisField.card 2 4 (by norm_num)]
  norm_num

theorem sl2_sixteen_isSimpleGroup : IsSimpleGroup (SpecialLinearGroup (Fin 2) (GaloisField 2 4)) :=
  sl2_isSimpleGroup (by rw [card_galoisField_two_four]; norm_num)

theorem card_sl2_sixteen : Nat.card (SpecialLinearGroup (Fin 2) (GaloisField 2 4)) = 4080 := by
  have : Fintype (GaloisField 2 4) := Fintype.ofFinite _
  have hq : Fintype.card (GaloisField 2 4) = 16 := by
    rw [← Nat.card_eq_fintype_card, card_galoisField_two_four]
  rw [Matrix.card_SL_field (n := 2), hq, Fin.prod_univ_two]
  norm_num

end SL2

section Shape

variable {X N : Type*} [Group X] [Group N]

theorem isPGroup_two_or_seventeen_dvd [Finite X] (π : X →* N) (hπ : Function.Surjective π)
    {O : Subgroup X} [O.Normal] (hO : IsPGroup 2 O)
    (e : X ⧸ O ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4)) :
    (∀ y : N, ∃ m : ℕ, y ^ 2 ^ m = 1) ∨ 17 ∣ Nat.card N := by
  have hsimple : IsSimpleGroup (X ⧸ O) := by
    have := sl2_sixteen_isSimpleGroup
    exact e.isSimpleGroup
  have hker : (π.ker.map (QuotientGroup.mk' O)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective O)
  have := hker
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (G := X ⧸ O) (π.ker.map (QuotientGroup.mk' O)) with h | h
  ·
    right
    have hKO : π.ker ≤ O := by
      intro k hk
      have : QuotientGroup.mk' O k ∈ π.ker.map (QuotientGroup.mk' O) := ⟨k, hk, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact (QuotientGroup.eq_one_iff k).1 this
    have hK2 : IsPGroup 2 π.ker := hO.to_le hKO
    have h17 : 17 ∣ Nat.card X := by
      have h1 : Nat.card X = Nat.card O * Nat.card (X ⧸ O) := Subgroup.card_eq_card_quotient_mul_card_subgroup O |>.trans (mul_comm _ _)
      have h2 : Nat.card (X ⧸ O) = 4080 := by rw [Nat.card_congr e.toEquiv, card_sl2_sixteen]
      rw [h1, h2]
      exact Dvd.dvd.mul_left (by norm_num) _
    have h3 : Nat.card X = Nat.card π.ker * Nat.card N := by
      rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπ).toEquiv]
      exact (Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker).trans (mul_comm _ _)
    rw [h3] at h17
    have hp : Nat.Prime 17 := by norm_num
    rcases hp.dvd_mul.1 h17 with h | h
    · exfalso
      obtain ⟨k, hk⟩ := hK2.exists_card_eq
      rw [hk] at h
      have := (Nat.Prime.dvd_of_dvd_pow hp h)
      omega
    · exact h
  ·
    left
    intro y
    obtain ⟨x, rfl⟩ := hπ y
    have hx : QuotientGroup.mk' O x ∈ π.ker.map (QuotientGroup.mk' O) := by
      rw [h]
      exact Subgroup.mem_top _
    obtain ⟨k, hk, hkx⟩ := hx
    have hxo : k⁻¹ * x ∈ O := by
      have := (QuotientGroup.eq (a := k) (b := x) (s := O)).1 hkx
      exact this
    obtain ⟨m, hm⟩ := hO ⟨k⁻¹ * x, hxo⟩
    refine ⟨m, ?_⟩
    have h1 : π x = π (k⁻¹ * x) := by
      rw [map_mul, map_inv, MonoidHom.mem_ker.1 hk, inv_one, one_mul]
    rw [h1, ← map_pow]
    have : (k⁻¹ * x) ^ 2 ^ m = 1 := congrArg Subtype.val hm
    rw [this, map_one]

end Shape

end CFSG.Quasithin.QP
