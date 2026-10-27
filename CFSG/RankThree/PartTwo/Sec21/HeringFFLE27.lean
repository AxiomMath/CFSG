module

public import CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two

public section

namespace CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two

open CFSG.Open (IsElemAbelian)

private abbrev e27M0 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  Matrix.fromBlocks !![0, 0, 0; 0, 1, 0; 0, 0, 1] !![1, 0, 0; 0, 0, 0; 0, 0, 0]
    !![1, 0, 0; 0, 0, 0; 0, 0, 0] 1

private abbrev e27M1 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  Matrix.fromBlocks !![1, 0, 0; 0, 0, 0; 0, 0, 1] !![0, 0, 0; 0, 1, 0; 0, 0, 0]
    !![0, 0, 0; 0, 1, 0; 0, 0, 0] 1

private abbrev e27M2 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  Matrix.fromBlocks !![1, 0, 0; 0, 1, 0; 0, 0, 0] !![0, 0, 0; 0, 0, 0; 0, 0, 1]
    !![0, 0, 0; 0, 0, 0; 0, 0, 1] 1

private def e27U0 : GL (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  Units.mk e27M0 (e27M0 * e27M0) (by decide) (by decide)

private def e27U1 : GL (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  Units.mk e27M1 (e27M1 * e27M1) (by decide) (by decide)

private def e27U2 : GL (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  Units.mk e27M2 (e27M2 * e27M2) (by decide) (by decide)

private theorem e27U0_mem : e27U0 ∈ CFSG.Open.StatedSp 3 (ZMod 2) :=
  CFSG.Open.StatedAPI.mem_statedSp_iff.2 (by decide)

private theorem e27U1_mem : e27U1 ∈ CFSG.Open.StatedSp 3 (ZMod 2) :=
  CFSG.Open.StatedAPI.mem_statedSp_iff.2 (by decide)

private theorem e27U2_mem : e27U2 ∈ CFSG.Open.StatedSp 3 (ZMod 2) :=
  CFSG.Open.StatedAPI.mem_statedSp_iff.2 (by decide)

private def e27g0 : H6 := ⟨e27U0, e27U0_mem⟩

private def e27g1 : H6 := ⟨e27U1, e27U1_mem⟩

private def e27g2 : H6 := ⟨e27U2, e27U2_mem⟩

private def e27rho : H6 →* Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  (Units.coeHom _).comp (CFSG.Open.StatedSp 3 (ZMod 2)).subtype

private theorem e27rho_injective : Function.Injective e27rho := by
  intro g h e
  apply Subtype.ext
  apply Units.ext
  exact e

private theorem e27rho_g0 : e27rho e27g0 = e27M0 := rfl

private theorem e27rho_g1 : e27rho e27g1 = e27M1 := rfl

private theorem e27rho_g2 : e27rho e27g2 = e27M2 := rfl

private theorem e27_comm01 : Commute e27g0 e27g1 := by
  show e27g0 * e27g1 = e27g1 * e27g0
  apply e27rho_injective
  rw [map_mul, map_mul, e27rho_g0, e27rho_g1]
  decide

private theorem e27_comm02 : Commute e27g0 e27g2 := by
  show e27g0 * e27g2 = e27g2 * e27g0
  apply e27rho_injective
  rw [map_mul, map_mul, e27rho_g0, e27rho_g2]
  decide

private theorem e27_comm12 : Commute e27g1 e27g2 := by
  show e27g1 * e27g2 = e27g2 * e27g1
  apply e27rho_injective
  rw [map_mul, map_mul, e27rho_g1, e27rho_g2]
  decide

private theorem e27g0_pow_three : e27g0 ^ 3 = 1 := by
  apply e27rho_injective
  rw [map_pow, e27rho_g0, map_one]
  decide

private theorem e27g1_pow_three : e27g1 ^ 3 = 1 := by
  apply e27rho_injective
  rw [map_pow, e27rho_g1, map_one]
  decide

private theorem e27g2_pow_three : e27g2 ^ 3 = 1 := by
  apply e27rho_injective
  rw [map_pow, e27rho_g2, map_one]
  decide

private theorem e27_pow_mod (g : H6) (h3 : g ^ 3 = 1) (n : ℕ) : g ^ n = g ^ (n % 3) := by
  have h := Nat.div_add_mod n 3
  calc g ^ n = g ^ (3 * (n / 3) + n % 3) := by rw [h]
    _ = (g ^ 3) ^ (n / 3) * g ^ (n % 3) := by rw [pow_add, pow_mul]
    _ = g ^ (n % 3) := by rw [h3, one_pow, one_mul]

private theorem e27_pow_add (g : H6) (h3 : g ^ 3 = 1) (x y : Fin 3) :
    g ^ (x : ℕ) * g ^ (y : ℕ) = g ^ ((x + y : Fin 3) : ℕ) := by
  rw [← pow_add, Fin.val_add, ← e27_pow_mod g h3]

private theorem e27_rearrange {x y z x' y' z' : H6} (hzx : Commute z x') (hzy : Commute z y')
    (hyx : Commute y x') : x * y * z * (x' * y' * z') = x * x' * (y * y') * (z * z') := by
  calc x * y * z * (x' * y' * z') = x * (y * (z * (x' * (y' * z')))) := by
        simp only [mul_assoc]
    _ = x * (y * (x' * (z * (y' * z')))) := by rw [hzx.left_comm]
    _ = x * (y * (x' * (y' * (z * z')))) := by rw [hzy.left_comm]
    _ = x * (x' * (y * (y' * (z * z')))) := by rw [hyx.left_comm]
    _ = x * x' * (y * y') * (z * z') := by simp only [mul_assoc]

private abbrev e27FM (p : Fin 3 × Fin 3 × Fin 3) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  e27M0 ^ (p.1 : ℕ) * e27M1 ^ (p.2.1 : ℕ) * e27M2 ^ (p.2.2 : ℕ)

private def e27F (p : Fin 3 × Fin 3 × Fin 3) : H6 :=
  e27g0 ^ (p.1 : ℕ) * e27g1 ^ (p.2.1 : ℕ) * e27g2 ^ (p.2.2 : ℕ)

private theorem e27rho_F (p : Fin 3 × Fin 3 × Fin 3) : e27rho (e27F p) = e27FM p := by
  simp only [e27F, e27FM, map_mul, map_pow, e27rho_g0, e27rho_g1, e27rho_g2]

private theorem e27F_mul (p q : Fin 3 × Fin 3 × Fin 3) : e27F p * e27F q = e27F (p + q) := by
  obtain ⟨i, j, k⟩ := p
  obtain ⟨i', j', k'⟩ := q
  simp only [e27F, Prod.mk_add_mk]
  rw [← e27_pow_add e27g0 e27g0_pow_three i i', ← e27_pow_add e27g1 e27g1_pow_three j j',
    ← e27_pow_add e27g2 e27g2_pow_three k k']
  exact e27_rearrange (e27_comm02.pow_pow i' k).symm (e27_comm12.pow_pow j' k).symm
    (e27_comm01.pow_pow i' j).symm

private theorem e27F_zero : e27F 0 = 1 := by
  simp [e27F]

private theorem e27_pow_three : ∀ p : Fin 3 × Fin 3 × Fin 3, e27FM p ^ 3 = 1 := by
  decide

private theorem e27_eq_one : ∀ p : Fin 3 × Fin 3 × Fin 3, e27FM p = 1 → p = 0 := by
  decide

private theorem e27F_pow_three (p : Fin 3 × Fin 3 × Fin 3) : e27F p ^ 3 = 1 := by
  apply e27rho_injective
  rw [map_pow, e27rho_F, map_one]
  exact e27_pow_three p

private theorem e27F_eq_one_iff (p : Fin 3 × Fin 3 × Fin 3) : e27F p = 1 → p = 0 := by
  intro h
  apply e27_eq_one p
  have h' := congrArg e27rho h
  rwa [map_one, e27rho_F] at h'

private theorem e27F_inj : Function.Injective e27F := by
  intro p q h
  have h1 : e27F (p + -q) = 1 := by
    rw [← e27F_mul, h, e27F_mul, add_neg_cancel, e27F_zero]
  exact add_neg_eq_zero.mp (e27F_eq_one_iff _ h1)

private def e27E : Subgroup H6 where
  carrier := Set.range e27F
  mul_mem' := by
    rintro _ _ ⟨p, rfl⟩ ⟨q, rfl⟩
    exact ⟨p + q, (e27F_mul p q).symm⟩
  one_mem' := ⟨0, e27F_zero⟩
  inv_mem' := by
    rintro _ ⟨p, rfl⟩
    refine ⟨-p, (inv_eq_of_mul_eq_one_right ?_).symm⟩
    rw [e27F_mul, add_neg_cancel, e27F_zero]

private theorem e27E_card : Nat.card e27E = 27 := by
  change Nat.card (Set.range e27F) = 27
  rw [Nat.card_range_of_injective e27F_inj]
  simp

private theorem e27E_isElemAbelian : IsElemAbelian 3 e27E := by
  unfold IsElemAbelian
  refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
  · rintro ⟨a, ha⟩ ⟨b, hb⟩
    obtain ⟨p, rfl⟩ := ha
    obtain ⟨q, rfl⟩ := hb
    apply Subtype.ext
    show e27F p * e27F q = e27F q * e27F p
    rw [e27F_mul, e27F_mul, add_comm]
  · intro x hx
    obtain ⟨p, rfl⟩ := hx
    exact e27F_pow_three p

theorem exists_e27_H6 : ∃ E : Subgroup H6, IsElemAbelian 3 E ∧ Nat.card E = 27 := by
  exact ⟨e27E, e27E_isElemAbelian, e27E_card⟩

end CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two
