module

public import CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two

public section

namespace CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two

open CFSG.Open (IsElemAbelian)

private abbrev e9M0 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  Matrix.fromBlocks !![0, 0, 0; 0, 1, 0; 0, 0, 1] !![1, 0, 0; 0, 0, 0; 0, 0, 0]
    !![1, 0, 0; 0, 0, 0; 0, 0, 0] 1

private abbrev e9M1 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  Matrix.fromBlocks !![1, 0, 0; 0, 0, 0; 0, 0, 1] !![0, 0, 0; 0, 1, 0; 0, 0, 0]
    !![0, 0, 0; 0, 1, 0; 0, 0, 0] 1

private abbrev e9MT : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  Matrix.fromBlocks 1 !![0, 0, 0; 0, 0, 0; 0, 0, 1] 0 1

private def e9U0 : GL (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  Units.mk e9M0 (e9M0 * e9M0) (by decide) (by decide)

private def e9U1 : GL (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  Units.mk e9M1 (e9M1 * e9M1) (by decide) (by decide)

private def e9UT : GL (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  Units.mk e9MT e9MT (by decide) (by decide)

private theorem e9U0_mem : e9U0 ∈ CFSG.Open.StatedSp 3 (ZMod 2) :=
  CFSG.Open.StatedAPI.mem_statedSp_iff.2 (by decide)

private theorem e9U1_mem : e9U1 ∈ CFSG.Open.StatedSp 3 (ZMod 2) :=
  CFSG.Open.StatedAPI.mem_statedSp_iff.2 (by decide)

private theorem e9UT_mem : e9UT ∈ CFSG.Open.StatedSp 3 (ZMod 2) :=
  CFSG.Open.StatedAPI.mem_statedSp_iff.2 (by decide)

private def e9g0 : H6 := ⟨e9U0, e9U0_mem⟩

private def e9g1 : H6 := ⟨e9U1, e9U1_mem⟩

private def e9gt : H6 := ⟨e9UT, e9UT_mem⟩

private def e9rho : H6 →* Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  (Units.coeHom _).comp (CFSG.Open.StatedSp 3 (ZMod 2)).subtype

private theorem e9rho_injective : Function.Injective e9rho := by
  intro g h e
  apply Subtype.ext
  apply Units.ext
  exact e

private theorem e9rho_g0 : e9rho e9g0 = e9M0 := rfl

private theorem e9rho_g1 : e9rho e9g1 = e9M1 := rfl

private theorem e9rho_gt : e9rho e9gt = e9MT := rfl

private abbrev e9FM (p : Fin 3 × Fin 3) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  e9M0 ^ (p.1 : ℕ) * e9M1 ^ (p.2 : ℕ)

private def e9F (p : Fin 3 × Fin 3) : H6 :=
  e9g0 ^ (p.1 : ℕ) * e9g1 ^ (p.2 : ℕ)

private theorem e9rho_F (p : Fin 3 × Fin 3) : e9rho (e9F p) = e9FM p := by
  simp only [e9F, e9FM, map_mul, map_pow, e9rho_g0, e9rho_g1]

private theorem e9_mul_table : ∀ p q : Fin 3 × Fin 3, e9FM p * e9FM q = e9FM (p + q) := by
  decide

private theorem e9_inj : ∀ p q : Fin 3 × Fin 3, e9FM p = e9FM q → p = q := by
  decide

private theorem e9_pow_three : ∀ p : Fin 3 × Fin 3, e9FM p ^ 3 = 1 := by
  decide

private theorem e9_comm_t : ∀ p : Fin 3 × Fin 3, e9FM p * e9MT = e9MT * e9FM p := by
  decide

private theorem e9F_mul (p q : Fin 3 × Fin 3) : e9F p * e9F q = e9F (p + q) := by
  apply e9rho_injective
  rw [map_mul, e9rho_F, e9rho_F, e9rho_F]
  exact e9_mul_table p q

private theorem e9F_zero : e9F 0 = 1 := by
  simp [e9F]

private theorem e9F_pow_three (p : Fin 3 × Fin 3) : e9F p ^ 3 = 1 := by
  apply e9rho_injective
  rw [map_pow, e9rho_F, map_one]
  exact e9_pow_three p

private theorem e9F_comm_t (p : Fin 3 × Fin 3) : e9F p * e9gt = e9gt * e9F p := by
  apply e9rho_injective
  rw [map_mul, map_mul, e9rho_F, e9rho_gt]
  exact e9_comm_t p

private theorem e9F_inj : Function.Injective e9F := by
  intro p q h
  apply e9_inj p q
  have h' := congrArg e9rho h
  rwa [e9rho_F, e9rho_F] at h'

private def e9E : Subgroup H6 where
  carrier := Set.range e9F
  mul_mem' := by
    rintro _ _ ⟨p, rfl⟩ ⟨q, rfl⟩
    exact ⟨p + q, (e9F_mul p q).symm⟩
  one_mem' := ⟨0, e9F_zero⟩
  inv_mem' := by
    rintro _ ⟨p, rfl⟩
    refine ⟨-p, (inv_eq_of_mul_eq_one_right ?_).symm⟩
    rw [e9F_mul, add_neg_cancel, e9F_zero]

private theorem e9E_card : Nat.card e9E = 9 := by
  change Nat.card (Set.range e9F) = 9
  rw [Nat.card_range_of_injective e9F_inj]
  simp

private theorem e9E_isElemAbelian : IsElemAbelian 3 e9E := by
  unfold IsElemAbelian
  refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
  · rintro ⟨a, ha⟩ ⟨b, hb⟩
    obtain ⟨p, rfl⟩ := ha
    obtain ⟨q, rfl⟩ := hb
    apply Subtype.ext
    show e9F p * e9F q = e9F q * e9F p
    rw [e9F_mul, e9F_mul, add_comm]
  · intro x hx
    obtain ⟨p, rfl⟩ := hx
    exact e9F_pow_three p

private theorem e9E_le_normalizer :
    e9E ≤ Subgroup.normalizer (Subgroup.zpowers e9gt : Set H6) := by
  intro x hx
  obtain ⟨p, rfl⟩ := hx
  refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
  intro h hh
  have hh' : h ∈ Subgroup.zpowers e9gt := hh
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh'
  have hc : Commute e9gt (e9F p) := (e9F_comm_t p).symm
  exact hc.zpow_left k

theorem exists_e9_normalizing_two_H6 :
    ∃ E V : Subgroup H6, IsElemAbelian 3 E ∧ Nat.card E = 9 ∧ V ≠ ⊥ ∧ IsPGroup 2 V ∧
      E ≤ Subgroup.normalizer (V : Set H6) := by
  have hsq : e9gt ^ 2 = 1 := by
    apply e9rho_injective
    rw [map_pow, e9rho_gt, map_one]
    decide
  have hne : e9gt ≠ 1 := by
    intro h
    have h' := congrArg e9rho h
    rw [e9rho_gt, map_one] at h'
    revert h'
    decide
  have hord : orderOf e9gt = 2 := orderOf_eq_prime hsq hne
  refine ⟨e9E, Subgroup.zpowers e9gt, e9E_isElemAbelian, e9E_card, ?_, ?_, e9E_le_normalizer⟩
  · exact fun h => hne (Subgroup.zpowers_eq_bot.mp h)
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])

end CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two
