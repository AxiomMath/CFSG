module

public import CFSG.RankThree.PartTwo.Sec15.Wales154KFacts
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.Timmesfeld.Orders.Bang
import CFSG.LocalAnalysis.SteinbergSFLinearUnitaryThreeBaseField
import CFSG.RankThree.PartTwo.KFacts.L34Sections
import CFSG.RankThree.PartTwo.KFacts.K72L3Unitary
import CFSG.Models.PGLSimple

public section

namespace CFSG.RankThree.PartTwo.Sec15.Wales154

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
open scoped commutatorElement

namespace KL3cProof

theorem dvd_of_ppd_dvd {p k a : ℕ} (hk : 0 < k) (hpk : p ∣ 2 ^ k - 1)
    (hprim : ∀ j : ℕ, 0 < j → j < k → ¬ p ∣ 2 ^ j - 1) (hpa : p ∣ 2 ^ a - 1) : k ∣ a := by
  have hg : p ∣ 2 ^ Nat.gcd k a - 1 := by
    rw [← Nat.pow_sub_one_gcd_pow_sub_one]
    exact Nat.dvd_gcd hpk hpa
  have hgpos : 0 < Nat.gcd k a := Nat.gcd_pos_of_pos_left a hk
  have hgle : Nat.gcd k a ≤ k := Nat.le_of_dvd hk (Nat.gcd_dvd_left k a)
  rcases lt_or_eq_of_le hgle with hlt | heq
  · exact absurd hg (hprim _ hgpos hlt)
  · rw [← heq]
    exact Nat.gcd_dvd_right k a

theorem not_two_dvd_two_pow_sub_one {k : ℕ} (hk : 0 < k) : ¬ 2 ∣ 2 ^ k - 1 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hk
  rw [pow_succ]
  have : 1 ≤ 2 ^ (0 + j) := Nat.one_le_two_pow
  omega

theorem ne_two_of_dvd {p k : ℕ} (hk : 0 < k) (hpk : p ∣ 2 ^ k - 1) : p ≠ 2 := by
  rintro rfl
  exact not_two_dvd_two_pow_sub_one hk hpk

theorem ne_three_of_ppd {p k : ℕ} (hk : 3 ≤ k)
    (hprim : ∀ j : ℕ, 0 < j → j < k → ¬ p ∣ 2 ^ j - 1) : p ≠ 3 := by
  rintro rfl
  exact hprim 2 (by norm_num) (by omega) (by norm_num)

theorem dvd_card_of_dvd_mul {p x g N : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hg : g ∣ 3)
    (hN : x * g = N) (hpN : p ∣ N) : p ∣ x := by
  have hcop : Nat.Coprime p g :=
    Nat.Coprime.coprime_dvd_right hg ((Nat.coprime_primes hp Nat.prime_three).mpr hp3)
  exact hcop.dvd_of_dvd_mul_right (hN ▸ hpN)

theorem dvd_two_pow_six_mul_sub_one {p m N : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hN : N = (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) ∨
      N = (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 + 1)))
    (hpN : p ∣ N) : p ∣ 2 ^ (6 * m) - 1 := by
  have hq3 : ¬ p ∣ (2 ^ m) ^ 3 := fun h =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      (hp.dvd_of_dvd_pow (hp.dvd_of_dvd_pow h)))
  have h2 : (2 ^ m) ^ 2 - 1 ∣ 2 ^ (6 * m) - 1 := by
    rw [← pow_mul, mul_comm m 2]
    exact Nat.pow_sub_one_dvd_pow_sub_one 2 ⟨3, by ring⟩
  have h3 : (2 ^ m) ^ 3 - 1 ∣ 2 ^ (6 * m) - 1 := by
    rw [← pow_mul, mul_comm m 3]
    exact Nat.pow_sub_one_dvd_pow_sub_one 2 ⟨2, by ring⟩
  have h3' : (2 ^ m) ^ 3 + 1 ∣ 2 ^ (6 * m) - 1 := by
    rw [show 2 ^ (6 * m) = (2 ^ m) ^ 3 * (2 ^ m) ^ 3 by rw [← pow_mul, ← pow_add]; ring_nf,
      mul_self_tsub_one]
    exact Dvd.intro _ rfl
  rcases hN with rfl | rfl
  · rcases (Nat.Prime.dvd_mul hp).mp hpN with h | h
    · exact absurd h hq3
    · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
      · exact h.trans h2
      · exact h.trans h3
  · rcases (Nat.Prime.dvd_mul hp).mp hpN with h | h
    · exact absurd h hq3
    · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
      · exact h.trans h2
      · exact h.trans h3'

theorem card_eq_of_isLThreeEpsAt_two {X : Type} [Group X] {n : ℕ} (hn : 1 ≤ n)
    (hX : IsLThreeEpsAt X 2 n) :
    (∃ g, g ∣ 3 ∧
      Nat.card X * g = (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1))) ∨
    (2 ≤ n ∧ ∃ g, g ∣ 3 ∧
      Nat.card X * g = (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1))) := by
  rcases hX with ⟨⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩
  · left
    have hc := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField 2 n)
    rw [GaloisField.card 2 n (by omega)] at hc
    exact ⟨_, Nat.gcd_dvd_left 3 _, by rw [Nat.card_congr φ.toEquiv]; exact hc⟩
  · right
    have h2n : 2 ≤ n := by
      by_contra h
      obtain rfl : n = 1 := by omega
      norm_num at hq
    exact ⟨h2n, _, Nat.gcd_dvd_left 3 _, by
      rw [Nat.card_congr φ.toEquiv]; exact KFacts.KS14.card_projSU_three_mul_gcd 2 n hn⟩

theorem dvd_of_isLThreeEpsAt {X : Type} [Group X] {n m : ℕ} (hn : 1 ≤ n)
    (hX : IsLThreeEpsAt X 2 n)
    (h : ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ Nat.card X → p ∣ 2 ^ (6 * m) - 1) : n ∣ m := by
  have key : ∀ k : ℕ, 3 ≤ k → k ≠ 6 → (∀ p : ℕ, p.Prime → p ∣ 2 ^ k - 1 → p ∣ Nat.card X ∨
      (∃ j, 0 < j ∧ j < k ∧ p ∣ 2 ^ j - 1)) → k ∣ 6 * m := by
    intro k hk3 hk6 hX'
    obtain ⟨p, hp, hpk, hprim⟩ := CFSG.Timmesfeld.exists_primitive_prime_dvd_two_pow_sub_one k
      (by omega) hk6
    rcases hX' p hp hpk with hpX | ⟨j, hj0, hjk, hpj⟩
    · exact dvd_of_ppd_dvd (by omega) hpk hprim (h p hp (ne_two_of_dvd (by omega) hpk) hpX)
    · exact absurd hpj (hprim j hj0 hjk)
  rcases card_eq_of_isLThreeEpsAt_two hn hX with ⟨g, hg, hcard⟩ | ⟨hn2, g, hg, hcard⟩
  ·
    rcases Nat.lt_or_ge n 2 with hn1 | hn2
    · obtain rfl : n = 1 := by omega
      exact one_dvd m
    have h3 : n ≠ 2 → 3 * n ∣ 6 * m := fun hn2' => key (3 * n) (by omega) (by omega)
      fun p hp hpk => by
        by_cases hpr : ∃ j, 0 < j ∧ j < 3 * n ∧ p ∣ 2 ^ j - 1
        · exact Or.inr hpr
        push Not at hpr
        refine Or.inl (dvd_card_of_dvd_mul hp
          (ne_three_of_ppd (k := 3 * n) (by omega) hpr) hg hcard ?_)
        rw [show (2 ^ n) ^ 3 = 2 ^ (3 * n) by rw [← pow_mul, mul_comm]]
        exact Dvd.dvd.mul_left (Dvd.dvd.mul_left hpk _) _
    have h2 : n ≠ 3 → 2 * n ∣ 6 * m := fun hn3 => key (2 * n) (by omega) (by omega)
      fun p hp hpk => by
        by_cases hpr : ∃ j, 0 < j ∧ j < 2 * n ∧ p ∣ 2 ^ j - 1
        · exact Or.inr hpr
        push Not at hpr
        refine Or.inl (dvd_card_of_dvd_mul hp
          (ne_three_of_ppd (k := 2 * n) (by omega) hpr) hg hcard ?_)
        rw [show (2 ^ n) ^ 2 = 2 ^ (2 * n) by rw [← pow_mul, mul_comm]]
        exact Dvd.dvd.mul_left (Dvd.dvd.mul_right hpk _) _
    rcases Nat.lt_or_ge n 4 with hn4 | hn4
    · interval_cases n
      · have := h2 (by norm_num)
        omega
      · have := h3 (by norm_num)
        omega
    · have ha : n ∣ 2 * m := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 3)
        (by rw [show 3 * (2 * m) = 6 * m by ring]; exact h3 (by omega))
      have hb : n ∣ 3 * m := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2)
        (by rw [show 2 * (3 * m) = 6 * m by ring]; exact h2 (by omega))
      have := Nat.dvd_sub hb ha
      rwa [show 3 * m - 2 * m = m by omega] at this
  ·
    have h6 : 6 * n ∣ 6 * m := key (6 * n) (by omega) (by omega) fun p hp hpk => by
      by_cases hpr : ∃ j, 0 < j ∧ j < 6 * n ∧ p ∣ 2 ^ j - 1
      · exact Or.inr hpr
      push Not at hpr
      refine Or.inl (dvd_card_of_dvd_mul hp
        (ne_three_of_ppd (k := 6 * n) (by omega) hpr) hg hcard ?_)
      have hp3 : ¬ p ∣ 2 ^ (3 * n) - 1 := hpr (3 * n) (by omega) (by omega)
      have hsplit : 2 ^ (6 * n) - 1 = ((2 ^ n) ^ 3 + 1) * (2 ^ (3 * n) - 1) := by
        rw [show (2 ^ n) ^ 3 = 2 ^ (3 * n) by rw [← pow_mul, mul_comm], ← mul_self_tsub_one,
          ← pow_add]
        ring_nf
      rw [hsplit] at hpk
      have hp1 : p ∣ (2 ^ n) ^ 3 + 1 := ((Nat.Prime.dvd_mul hp).mp hpk).resolve_right hp3
      exact Dvd.dvd.mul_left (Dvd.dvd.mul_left hp1 _) _
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 6) h6

section Generic

variable {G : Type*} [Group G]

theorem exists_mul_ne_of_orderOf_four [IsSimpleGroup G] {x : G} (hx : orderOf x = 4) :
    ∃ a b : G, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have hN : (Subgroup.zpowers (x ^ 2)).Normal := ⟨fun n hn g => by
    rw [hcon g n, mul_inv_cancel_right]
    exact hn⟩
  have ho2 : orderOf (x ^ 2) = 2 := by
    rw [orderOf_pow' x (by norm_num), hx]
    norm_num
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers (x ^ 2)) with h2 | h2
  · have h1 : x ^ 2 = 1 := by
      have := Subgroup.mem_zpowers (x ^ 2)
      rwa [h2, Subgroup.mem_bot] at this
    rw [h1, orderOf_one] at ho2
    norm_num at ho2
  · have hc : Nat.card G = 2 := by
      rw [← Subgroup.card_top (G := G), ← h2, Nat.card_zpowers, ho2]
    have := orderOf_dvd_natCard x
    rw [hx, hc] at this
    norm_num at this

theorem isPerfect_of_orderOf_four [IsSimpleGroup G] {x : G} (hx : orderOf x = 4) :
    Group.IsPerfect G := by
  refine Group.isPerfect_def.2 ?_
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := exists_mul_ne_of_orderOf_four hx
    have hm : ⁅a, b⁆ ∈ commutator G :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot] at hm
    exact hab (commutatorElement_eq_one_iff_mul_comm.1 hm)
  · exact h

theorem conj_injective_of_orderOf_four [IsSimpleGroup G] {x : G} (hx : orderOf x = 4) :
    Function.Injective (MulAut.conj : G →* MulAut G) := by
  rw [injective_iff_map_eq_one]
  intro z hz
  have hzc : z ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := congrArg (fun α : MulAut G => α g) hz
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc g * z = z * g * z⁻¹ * z := by rw [h1]
      _ = z * g := by group
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · rwa [h, Subgroup.mem_bot] at hzc
  · exfalso
    obtain ⟨a, b, hab⟩ := exists_mul_ne_of_orderOf_four hx
    have hb : b ∈ Subgroup.center G := by rw [h]; exact Subgroup.mem_top b
    exact hab (Subgroup.mem_center_iff.mp hb a)

theorem mulAut_conj_conj (φ : MulAut G) (x : G) :
    φ * MulAut.conj x * φ⁻¹ = MulAut.conj (φ x) := by
  ext y
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem congr_mul_self {H : Type*} [Group H] (φ : G ≃* H) {τ : MulAut G} (hτ : τ * τ = 1) :
    MulAut.congr φ τ * MulAut.congr φ τ = 1 := by
  rw [← map_mul, hτ, map_one]

theorem congr_not_mem_range {H : Type*} [Group H] (φ : G ≃* H) {τ : MulAut G}
    (hτ : τ ∉ (MulAut.conj : G →* MulAut G).range) :
    MulAut.congr φ τ ∉ (MulAut.conj : H →* MulAut H).range := by
  rintro ⟨y, hy⟩
  apply hτ
  refine ⟨φ.symm y, ?_⟩
  ext x
  have h1 := congrArg (fun α : MulAut H => α (φ x)) hy
  simp only [MulAut.conj_apply, MulAut.congr_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply] at h1
  rw [MulAut.conj_apply]
  apply φ.injective
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, h1]

theorem map_fixed_of_eq_conj {β γ g : MulAut G} (hβ : β = g * γ * g⁻¹) {X : Subgroup G}
    (hX : ∀ x ∈ X, β x = x) : ∀ y ∈ X.map (g⁻¹ : MulAut G).toMonoidHom, γ y = y := by
  rintro _ ⟨x, hx, rfl⟩
  have h1 := hX x hx
  rw [hβ, MulAut.mul_apply, MulAut.mul_apply] at h1
  change γ (g⁻¹ x) = g⁻¹ x
  calc γ (g⁻¹ x) = g⁻¹ (g (γ (g⁻¹ x))) := (MulAut.inv_apply_self _ _ _).symm
    _ = g⁻¹ x := by rw [h1]

theorem orderOf_ne_four_of_range_SL_two {k : Type*} [Field k] [CharP k 2]
    (j : Matrix.SpecialLinearGroup (Fin 2) k →* G) (hj : Function.Injective j) {y : G}
    (hy : y ∈ j.range) : orderOf y ≠ 4 := by
  obtain ⟨s, rfl⟩ := hy
  rw [orderOf_injective j hj s]
  exact CFSG.LocalAnalysis.SteinbergCD.SL_two_orderOf_ne_four CharTwo.two_eq_zero s

end Generic

section UnitaryModel

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.SymplecticFourStandard.LinearUnitaryThree
open CFSG.ComponentClassification.UnbalancedCatalog.UnitaryFieldTransfer (fixedField_charP)

private theorem unitary_model_false {e : ℕ} {F : Type} [Field F] (h : UnitaryFieldData 2 e F)
    (he : 2 ≤ e) {β : MulAut (unitaryPSU h 3)} (hβ2 : β * β = 1)
    (hβout : β ∉ (MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3)).range)
    {x : unitaryPSU h 3} (hx : β x = x) (hx4 : orderOf x = 4) : False := by
  have hβ1 : β ≠ 1 := by
    rintro rfl
    exact hβout ⟨1, map_one _⟩
  have hβo : orderOf β = 2 := orderOf_eq_prime (by rw [sq]; exact hβ2) hβ1
  obtain ⟨H, hH⟩ := eq_conj_bar_of_not_mem_inner h he hβo hβout
  have hy := map_fixed_of_eq_conj hH (X := Subgroup.zpowers x) (fun z hz => by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [map_zpow, hx]) ((psuConj h H)⁻¹ x) ⟨x, Subgroup.mem_zpowers x, rfl⟩
  obtain ⟨j, hj, hjr⟩ := exists_SL_two_fixed_bar h
  have := fixedField_charP h
  have hmem : (psuConj h H)⁻¹ x ∈ j.range := by
    rw [hjr]
    exact hy
  apply orderOf_ne_four_of_range_SL_two j hj hmem
  rw [MulEquiv.orderOf_eq, hx4]

end UnitaryModel

section LinearModel

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.CatalogueBHigherLinearField
open CFSG.ComponentClassification.CatalogueBGraphField
open CFSG.ComponentClassification.CatalogueBUnitaryIsometry CFSG.LieType.Universal.Unitary
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.SymplecticFourStandard.LinearUnitaryThree

variable {F : Type} [Field F]

private theorem graph_case_false [CharP F 2] (H : GL (Fin 3) F) {β : MulAut (projectiveSL 3 F)}
    (hβ : β = conjAut 3 F H * dualAut 3 F * (conjAut 3 F H)⁻¹) {x : projectiveSL 3 F}
    (hx : β x = x) (hx4 : orderOf x = 4) : False := by
  have hy := map_fixed_of_eq_conj hβ (X := Subgroup.zpowers x) (fun z hz => by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [map_zpow, hx]) ((conjAut 3 F H)⁻¹ x) ⟨x, Subgroup.mem_zpowers x, rfl⟩
  obtain ⟨j, hj, hjr⟩ := exists_SL_two_fixed_dualAut (F := F)
  have hmem : (conjAut 3 F H)⁻¹ x ∈ j.range := by
    rw [hjr]
    exact hy
  apply orderOf_ne_four_of_range_SL_two j hj hmem
  rw [MulEquiv.orderOf_eq, hx4]

private theorem exists_subfield_of_commute [Finite F] (σ : F ≃+* F) (A : GL (Fin 3) F)
    (hc : Commute (fieldAut 3 F σ) (conjAut 3 F A)) :
    ∃ B : GL (Fin 3) (fixedField F σ),
      conjAut 3 F A = conjAut 3 F (subfieldGLMap (Fin 3) F (fixedField F σ) B) := by
  have h1 : conjAut 3 F (GeneralLinearGroup.map (σ : F →+* F) A) = conjAut 3 F A := by
    have := hc.eq
    rw [fieldAut_mul_conjAut] at this
    exact mul_right_cancel this
  obtain ⟨c, hc⟩ := (conjAut_eq_conjAut_iff le_rfl _ _).mp h1
  have hfix : pglFieldAut (Fin 3) F σ (ProjGenLinGroup.mk A) = ProjGenLinGroup.mk A := by
    change ProjGenLinGroup.mk (GeneralLinearGroup.map (σ : F →+* F) A) = _
    rw [hc, map_mul, ProjGenLinGroup.mk_scalar, mul_one]
  obtain ⟨B, hB⟩ := fixed_projective_exists_subfield_matrix (Fin 3) F σ A hfix
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hB
  exact ⟨B, by rw [← hu, map_mul, conjAut_scalar, mul_one]⟩

private theorem exists_unitary_of_commute [Finite F] (σ : F ≃+* F) (hσ2 : σ ^ 2 = 1) (hσ1 : σ ≠ 1)
    (A : GL (Fin 3) F) (hc : Commute (fieldAut 3 F σ * dualAut 3 F) (conjAut 3 F A)) :
    ∃ B ∈ Uid σ 3, conjAut 3 F A = conjAut 3 F B := by
  have hβc : fieldAut 3 F σ * dualAut 3 F * conjAut 3 F A =
      conjAut 3 F (GeneralLinearGroup.map (σ : F →+* F)
        (GeneralLinearGroup.inverseTranspose A)) * (fieldAut 3 F σ * dualAut 3 F) := by
    rw [mul_assoc, dualAut_mul_conjAut, ← mul_assoc, fieldAut_mul_conjAut, mul_assoc]
  have h1 : conjAut 3 F (GeneralLinearGroup.map (σ : F →+* F)
      (GeneralLinearGroup.inverseTranspose A)) = conjAut 3 F A := by
    have := hc.eq
    rw [hβc] at this
    exact mul_right_cancel this
  obtain ⟨c, hc⟩ := (conjAut_eq_conjAut_iff le_rfl _ _).mp h1
  have hfix : ProjGenLinGroup.mk A ∈ fixedPGL 3 F σ := by
    change pglGraphFieldAut 3 F σ (ProjGenLinGroup.mk A) = ProjGenLinGroup.mk A
    rw [pglGraphFieldAut_mk]
    change ProjGenLinGroup.mk (GeneralLinearGroup.map (σ : F →+* F)
      (GeneralLinearGroup.inverseTranspose A)) = _
    rw [hc, map_mul, ProjGenLinGroup.mk_scalar, mul_one]
  rw [fixedPGL_eq_unitary_image 3 F (by omega) σ hσ2 hσ1] at hfix
  obtain ⟨B, hB, hBA⟩ := hfix
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hBA
  exact ⟨B, hB, by rw [← hu, map_mul, conjAut_scalar, mul_one]⟩

private theorem commute_conj_of_fixed {γ : MulAut (projectiveSL 3 F)} {x : projectiveSL 3 F}
    (hx : γ x = x) : Commute γ (MulAut.conj x) := by
  have h := mulAut_conj_conj γ x
  rw [hx] at h
  exact (mul_inv_eq_iff_eq_mul.mp h)

private theorem card_unitaryPSU_three_mul_gcd {e : ℕ} (h : UnitaryFieldData 2 e F) :
    Nat.card (unitaryPSU h 3) * Nat.gcd 3 (2 ^ e + 1) =
      (2 ^ e) ^ 3 * (((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 3 + 1)) := by
  have hc := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_two h.one_le
    h.card_eq_sq (n := 3) (by norm_num)
  rw [← Nat.card_congr (unitaryPSUEquiv h (by norm_num)).toEquiv] at hc
  have hq : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  have hq2 : 1 ≤ (2 ^ e) ^ 2 := Nat.one_le_pow _ _ hq
  have h2 : ((((2 ^ e : ℕ) : ℤ) ^ 2 - (-1) ^ 2)).toNat = (2 ^ e) ^ 2 - 1 := by
    rw [show ((2 ^ e : ℕ) : ℤ) ^ 2 - (-1) ^ 2 = (((2 ^ e) ^ 2 - 1 : ℕ) : ℤ) by
      push_cast [Nat.cast_sub hq2]
      ring, Int.toNat_natCast]
  have h3 : ((((2 ^ e : ℕ) : ℤ) ^ 3 - (-1) ^ 3)).toNat = (2 ^ e) ^ 3 + 1 := by
    rw [show ((2 ^ e : ℕ) : ℤ) ^ 3 - (-1) ^ 3 = (((2 ^ e) ^ 3 + 1 : ℕ) : ℤ) by
      push_cast
      ring, Int.toNat_natCast]
  rw [hc, show 3 * (3 - 1) / 2 = 3 from rfl, show Finset.Icc 2 3 = ({2, 3} : Finset ℕ) by decide,
    Finset.prod_pair (by norm_num), h2, h3]
  refine Nat.div_mul_cancel ?_
  have hd : 2 ^ e + 1 ∣ (2 ^ e) ^ 3 + 1 := by
    simpa using Odd.nat_add_dvd_pow_add_pow (2 ^ e) 1 (n := 3) (by decide)
  exact Dvd.dvd.mul_left (Dvd.dvd.mul_left ((Nat.gcd_dvd_right 3 _).trans hd) _) _

private theorem unitaryFieldData_of_even {f : ℕ} (hf : 1 ≤ f) (hF : Nat.card F = 2 ^ f)
    (hfe : Even f) : UnitaryFieldData 2 (f / 2) F := by
  obtain ⟨r, hr⟩ := hfe
  exact ⟨Nat.prime_two, by omega, by rw [hF]; congr 1; omega⟩

private theorem field_case [Finite F] {f : ℕ} (hF : Nat.card F = 2 ^ f) {σ : F ≃+* F} (hσ1 : σ ≠ 1)
    (hσ2 : σ ^ 2 = 1) (hfe : Even f) (X : Subgroup (projectiveSL 3 F)) [Group.IsPerfect X]
    (hX : ∀ x ∈ X, fieldAut 3 F σ x = x)
    (hconj : Function.Injective (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F))) :
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ Nat.card X → p ∣ 2 ^ (6 * (f / 2)) - 1 := by
  intro p hp hp2 hpX
  set k := fixedField F σ
  set M : Subgroup (MulAut (projectiveSL 3 F)) :=
    ((conjAut 3 F).comp (subfieldGLMap (Fin 3) F k)).range
  set N := (subfieldConj 3 σ).range
  have hZM : X.map (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)) ≤ M := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨g, rfl⟩ := proj_surjective 3 F x
    have hc := commute_conj_of_fixed (hX _ hx)
    rw [← conjAut_toGL] at hc ⊢
    obtain ⟨B, hB⟩ := exists_subfield_of_commute σ _ hc
    exact ⟨B, by rw [MonoidHom.comp_apply, ← hB]⟩
  have hMN : ⁅M, M⁆ ≤ N := by
    rw [Subgroup.commutator_le]
    rintro _ ⟨B₁, rfl⟩ _ ⟨B₂, rfl⟩
    rw [← map_commutatorElement]
    have hdet : ((⁅B₁, B₂⁆ : GL (Fin 3) (fixedField F σ)) :
        Matrix (Fin 3) (Fin 3) (fixedField F σ)).det = 1 := by
      have h1 : GeneralLinearGroup.det ⁅B₁, B₂⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact mul_comm _ _
      rw [← GeneralLinearGroup.val_det_apply, h1, Units.val_one]
    let C : SpecialLinearGroup (Fin 3) (fixedField F σ) := ⟨_, hdet⟩
    have hC : SpecialLinearGroup.toGL C = ⁅B₁, B₂⁆ := Units.ext rfl
    refine ⟨C, ?_⟩
    change conjAut 3 F (subfieldSLIncl 3 σ C) =
      conjAut 3 F (subfieldGLMap (Fin 3) F (fixedField F σ) ⁅B₁, B₂⁆)
    rw [subfieldSLIncl_eq, hC]
  have hZN : X.map (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)) ≤ N := by
    have : Group.IsPerfect
        (X.map (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F))) :=
      Group.IsPerfect.map _
    rw [← Subgroup.commutator_eq_self
      (H := X.map (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)))]
    exact (Subgroup.commutator_mono hZM hZM).trans hMN
  have hdvd : Nat.card X ∣ Nat.card N := by
    rw [← Subgroup.card_map_of_injective hconj]
    exact Subgroup.card_dvd_of_le hZN
  obtain ⟨-, ⟨e, -⟩, -⟩ := linear_quadratic_field_full_centralizer_rigidity σ (n := 3) le_rfl
  have hcardN : Nat.card N = Nat.card (CFSG.Assembly.RankThreeEven.projSL 3 k) :=
    (Nat.card_congr e.toEquiv).symm.trans
      (Nat.card_congr (KFacts.L34.projSLEquivProjectiveSL 3 k).symm.toEquiv)
  have hk : Nat.card k = 2 ^ (f / 2) := by
    have h1 := fixedField_card_square F σ hσ2 hσ1
    rw [hF] at h1
    obtain ⟨r, hr⟩ := hfe
    have h2 : (2 ^ (f / 2)) ^ 2 = Nat.card k ^ 2 := by
      rw [← h1, ← pow_mul]
      congr 1
      omega
    exact (Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) h2).symm
  have hc := KFacts.KS14.card_projSL_three_mul_gcd k
  rw [hk] at hc
  refine dvd_two_pow_six_mul_sub_one hp hp2 (Or.inl rfl) ?_
  rw [← hc, ← hcardN]
  exact Dvd.dvd.mul_right (hpX.trans hdvd) _

private theorem graph_field_case [Finite F] {f : ℕ} (hf : 1 ≤ f) (hF : Nat.card F = 2 ^ f)
    {σ : F ≃+* F} (hσ1 : σ ≠ 1) (hσ : ∀ x, σ x = x ^ 2 ^ (f / 2)) (hfe : Even f)
    (X : Subgroup (projectiveSL 3 F)) [Group.IsPerfect X]
    (hX : ∀ x ∈ X, (fieldAut 3 F σ * dualAut 3 F) x = x)
    (hconj : Function.Injective (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F))) :
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ Nat.card X → p ∣ 2 ^ (6 * (f / 2)) - 1 := by
  intro p hp hp2 hpX
  have h := unitaryFieldData_of_even hf hF hfe
  have hσbar : ∀ x, σ x = h.bar x := fun x => by rw [hσ, UnitaryFieldData.bar_apply]
  have hσ2 : σ ^ 2 = 1 := RingEquiv.ext fun x => by
    rw [pow_two, RingAut.mul_apply, hσbar, hσbar, h.bar_bar]
    rfl
  set M : Subgroup (MulAut (projectiveSL 3 F)) := (Uid σ 3).map (conjAut 3 F)
  set N := (unitarySU 2 (f / 2) F 3).map (conjAut 3 F)
  have hZM : X.map (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)) ≤ M := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨g, rfl⟩ := proj_surjective 3 F x
    have hc := commute_conj_of_fixed (hX _ hx)
    rw [← conjAut_toGL] at hc ⊢
    obtain ⟨B, hB, hAB⟩ := exists_unitary_of_commute σ hσ2 hσ1 _ hc
    exact ⟨B, hB, hAB.symm⟩
  have hmap : ∀ A : Matrix (Fin 3) (Fin 3) F, A.map σ = A.map h.bar := fun A => by
    ext i j
    simp [hσbar]
  have hMN : ⁅M, M⁆ ≤ N := by
    rw [Subgroup.commutator_le]
    rintro _ ⟨B₁, hB₁, rfl⟩ _ ⟨B₂, hB₂, rfl⟩
    rw [← map_commutatorElement]
    refine ⟨⁅B₁, B₂⁆, ?_, rfl⟩
    have hU : ⁅B₁, B₂⁆ ∈ Uid σ 3 := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hB₁ hB₂) (inv_mem hB₁)) (inv_mem hB₂)
    rw [SetLike.mem_coe, mem_unitarySU_iff h]
    refine ⟨?_, ?_⟩
    · have h1 : GeneralLinearGroup.det ⁅B₁, B₂⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact mul_comm _ _
      rw [← GeneralLinearGroup.val_det_apply, h1, Units.val_one]
    · have h2 := (mem_Uid_iff σ 3 _).mp hU
      rw [conjTr, hmap] at h2
      exact h2
  have hZN : X.map (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)) ≤ N := by
    have : Group.IsPerfect
        (X.map (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F))) :=
      Group.IsPerfect.map _
    rw [← Subgroup.commutator_eq_self
      (H := X.map (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)))]
    exact (Subgroup.commutator_mono hZM hZM).trans hMN
  have hdvd : Nat.card X ∣ Nat.card N := by
    rw [← Subgroup.card_map_of_injective hconj]
    exact Subgroup.card_dvd_of_le hZN
  obtain ⟨-, ⟨ι, -⟩, -⟩ := linear_graph_field_full_centralizer_rigidity h (n := 3) le_rfl σ hσbar
  have hcardN : Nat.card N = Nat.card (unitaryPSU h 3) := (Nat.card_congr ι.toEquiv).symm
  have hc := card_unitaryPSU_three_mul_gcd h
  refine dvd_two_pow_six_mul_sub_one hp hp2 (Or.inr rfl) ?_
  rw [← hc, ← hcardN]
  exact Dvd.dvd.mul_right (hpX.trans hdvd) _

private theorem linear_model {f : ℕ} (hf : 1 ≤ f) (hF : Nat.card F = 2 ^ f)
    {β : MulAut (projectiveSL 3 F)} (hβ2 : β * β = 1)
    (hβout : β ∉ (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range)
    (X : Subgroup (projectiveSL 3 F)) [Group.IsPerfect X] (hX : ∀ x ∈ X, β x = x)
    {x₄ : projectiveSL 3 F} (hx₄X : x₄ ∈ X) (hx₄ : orderOf x₄ = 4) :
    Even f ∧ ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ Nat.card X → p ∣ 2 ^ (6 * (f / 2)) - 1 := by
  classical
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; positivity)
  have : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two hf hF
  have : IsSimpleGroup (ProjectiveSpecialLinearGroup (Fin 3) F) :=
    (CFSG.LinearGroups.linear_projective_simple (by omega) (Or.inl le_rfl)).2.1
  have : IsSimpleGroup (projectiveSL 3 F) :=
    (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 F).symm.isSimpleGroup
  have hconj := conj_injective_of_orderOf_four hx₄
  obtain ⟨-, hform⟩ := automorphism_generation (K := F) (n := 3) le_rfl
  obtain ⟨A, σ, ε, hε, rfl⟩ := hform β
  have hβsq : (conjAut 3 F A * fieldAut 3 F σ * dualAut 3 F ^ ε) ^ 2 = 1 := by
    rw [sq]
    exact hβ2
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  · simp only [pow_zero, mul_one] at hβsq hβout hX
    by_cases hσ : σ = 1
    · subst hσ
      simp only [map_one, mul_one] at hβsq hβout
      exact absurd (EvenLinearSL.conjAut_mem_inner_of_sq_eq_one hf hF A hβsq) hβout
    obtain ⟨hfe, hσx, H, hβH⟩ := even_linear_field_involution_descent hf hF le_rfl A σ hσ hβsq
    have h := unitaryFieldData_of_even hf hF hfe
    have hσbar : ∀ x, σ x = h.bar x := fun x => by rw [hσx, UnitaryFieldData.bar_apply]
    have hσ2 : σ ^ 2 = 1 := RingEquiv.ext fun x => by
      rw [pow_two, RingAut.mul_apply, hσbar, hσbar, h.bar_bar]
      rfl
    refine ⟨hfe, fun p hp hp2 hpX => ?_⟩
    have hX' := map_fixed_of_eq_conj hβH hX
    have : Group.IsPerfect (X.map ((conjAut 3 F H)⁻¹ : MulAut (projectiveSL 3 F)).toMonoidHom) :=
      Group.IsPerfect.map _
    refine field_case hF hσ hσ2 hfe _ hX' hconj p hp hp2 ?_
    rwa [Subgroup.card_map_of_injective (MulEquiv.injective _)]
  · simp only [pow_one] at hβsq hβout hX
    by_cases hσ : σ = 1
    · subst hσ
      simp only [map_one, mul_one] at hβsq hβout hX
      obtain ⟨-, ⟨H₀, C, -, hβ, hC⟩, -⟩ :=
        UnitaryHigher.even_linear_pure_graph_involution_normal_forms hf hF le_rfl A hβsq
      rcases hC with ⟨h1C, -⟩ | ⟨r, hr, -, -⟩
      · rw [show C = 1 from Units.ext h1C, map_one, one_mul] at hβ
        exact (graph_case_false H₀ hβ (hX x₄ hx₄X) hx₄).elim
      · omega
    · obtain ⟨hfe, hσx, B, hβB⟩ :=
        UnitaryHigher.linear_graph_field_involution_descent Nat.prime_two hf hF le_rfl A σ hσ hβsq
      refine ⟨hfe, fun p hp hp2 hpX => ?_⟩
      have hX' := map_fixed_of_eq_conj hβB hX
      have : Group.IsPerfect
          (X.map ((conjAut 3 F B)⁻¹ : MulAut (projectiveSL 3 F)).toMonoidHom) :=
        Group.IsPerfect.map _
      refine graph_field_case hf hF hσ hσx hfe _ hX' hconj p hp hp2 ?_
      rwa [Subgroup.card_map_of_injective (MulEquiv.injective _)]

end LinearModel

section Models

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

theorem exists_orderOf_four_and_isSimpleGroup {X : Type} [Group X] {n : ℕ} (hn : 1 ≤ n)
    (hX : IsLThreeEpsAt X 2 n) : (∃ x : X, orderOf x = 4) ∧ IsSimpleGroup X := by
  rcases hX with ⟨⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩
  · have : IsSimpleGroup (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 n)) :=
      CFSG.PGLModel.isSimpleGroup_projSL_of_two_le (GaloisField 2 n) (by norm_num)
        (Or.inl (by norm_num)) (Or.inl (by norm_num))
    refine ⟨?_, φ.isSimpleGroup⟩
    set ψ := φ.trans (KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 n))
    obtain ⟨A, -, hA⟩ := CFSG.LocalAnalysis.SteinbergCD.exists_orderOf_eq_four_projectiveSL
      (k := GaloisField 2 n) (d := 3) CharTwo.two_eq_zero le_rfl
    exact ⟨ψ.symm (LinearFlag.proj 3 _ A), by rw [MulEquiv.orderOf_eq, hA]⟩
  · have hnq : (3, 2 ^ n) ≠ (3, 2) := fun h => by
      simp only [Prod.mk.injEq, true_and] at h
      omega
    have : IsSimpleGroup (CFSG.Assembly.RankThreeEven.projSU 3 2 n) :=
      CFSG.PGLModel.isSimpleGroup_projSU_of_admissible ⟨Nat.prime_two, hn, le_rfl, hnq⟩
    refine ⟨?_, φ.isSimpleGroup⟩
    have h : UnitaryFieldData 2 n (GaloisField 2 (2 * n)) :=
      ⟨Nat.prime_two, hn, GaloisField.card 2 (2 * n) (by omega)⟩
    obtain ⟨ψ₀⟩ := KFacts.nonempty_unitaryPSU_mulEquiv_projSU h
    obtain ⟨T, -, hT⟩ := CFSG.LocalAnalysis.SteinbergCD.exists_orderOf_eq_four_unitaryPSU h
      (d := 3) le_rfl
    exact ⟨φ.symm (ψ₀ (unitaryProj h 3 T)), by rw [MulEquiv.orderOf_eq, MulEquiv.orderOf_eq, hT]⟩

end Models

end KL3cProof

open KL3cProof in
theorem kl3c_holds : KL3c := by
  intro Q _ _ f n hf hn hQ Xb hXb τ hτout hτ2 hτX
  obtain ⟨⟨x₄, hx₄⟩, hsimp⟩ := exists_orderOf_four_and_isSimpleGroup hn hXb
  haveI : Group.IsPerfect Xb := isPerfect_of_orderOf_four hx₄
  have hx₄' : orderOf (x₄ : Q) = 4 := by rw [Subgroup.orderOf_coe, hx₄]
  rcases hQ with ⟨⟨φ₀⟩⟩ | ⟨hq, ⟨φ₀⟩⟩
  · refine ⟨⟨φ₀⟩, ?_⟩
    have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
    set φ : Q ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 (GaloisField 2 f) :=
      φ₀.trans (KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 f))
    set X := Xb.map φ.toMonoidHom
    have hX : ∀ x ∈ X, MulAut.congr φ τ x = x := by
      rintro _ ⟨y, hy, rfl⟩
      change φ (τ (φ.symm (φ y))) = φ y
      rw [MulEquiv.symm_apply_apply, hτX y hy]
    haveI : Group.IsPerfect X := Group.IsPerfect.map _
    obtain ⟨hfe, hp⟩ := linear_model hf hF (congr_mul_self φ hτ2) (congr_not_mem_range φ hτout)
      X hX ⟨x₄, x₄.2, rfl⟩ (by rw [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq, hx₄'])
    have hcard : Nat.card X = Nat.card Xb := Subgroup.card_map_of_injective φ.injective
    have hdvd : n ∣ f / 2 := dvd_of_isLThreeEpsAt hn hXb
      (fun p hp' hp2 hpX => hp p hp' hp2 (by rw [hcard]; exact hpX))
    obtain ⟨r, hr⟩ := hfe
    rw [show f = 2 * (f / 2) by omega]
    exact Nat.mul_dvd_mul_left 2 hdvd
  · exfalso
    have hf2 : 2 ≤ f := by
      by_contra hlt
      obtain rfl : f = 1 := by omega
      norm_num at hq
    have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f (GaloisField 2 (2 * f)) :=
      ⟨Nat.prime_two, hf, GaloisField.card 2 (2 * f) (by omega)⟩
    obtain ⟨ψ⟩ := KFacts.nonempty_unitaryPSU_mulEquiv_projSU h
    set φ := φ₀.trans ψ.symm
    refine unitary_model_false h hf2 (congr_mul_self φ hτ2) (congr_not_mem_range φ hτout)
      (x := φ x₄) ?_ (by rw [MulEquiv.orderOf_eq, hx₄'])
    change φ (τ (φ.symm (φ x₄))) = φ x₄
    rw [MulEquiv.symm_apply_apply, hτX x₄ x₄.2]

end CFSG.RankThree.PartTwo.Sec15.Wales154
