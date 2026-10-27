module

public import CFSG.Quasithin.Recognition.RuTypeSL3
public import CFSG.LieType.SteinbergBRAutGL32
public import CFSG.LieType.SteinbergBRTwoRankBound

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Quasithin.RuType CFSG.QuasithinUnique.Setup.Family CFSG.LieType.SteinbergBR
open scoped MatrixGroups

theorem sl3_mem_stab0_of_comm : ∀ c : SL(3, ZMod 2), c ^ 21 = 1 →
    (∀ a ∈ SL3.Stab0, a ^ 3 = 1 → c * a * c⁻¹ * a⁻¹ ∈ SL3.R0) → c ∈ SL3.Stab0 ∧ c ^ 3 = 1 := by
  decide +kernel

theorem sl3_exists_inv : ∀ c ∈ SL3.Stab0, c ^ 3 = 1 →
    ∃ s ∈ SL3.Stab0, s * c * s⁻¹ * c ∈ SL3.R0 := by
  decide +kernel

theorem sl3_R0_mul_self : ∀ n ∈ SL3.R0, n * n = 1 := by
  decide +kernel

theorem congr_conj {A B : Type*} [Group A] [Group B] (e : A ≃* B) (a : A) :
    MulAut.congr e (MulAut.conj a) = MulAut.conj (e a) :=
  MulEquiv.ext fun b => by
    show e (a * e.symm b * a⁻¹) = e a * b * (e a)⁻¹
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem sl3_pow_21 {c : SL(3, ZMod 2)} {n : ℕ} (hn : Odd n) (hc : c ^ n = 1) : c ^ 21 = 1 := by
  have h1 : orderOf c ∣ n := orderOf_dvd_of_pow_eq_one hc
  have h2 : orderOf c ∣ 8 * 21 := by
    rw [show (8 * 21 : ℕ) = Nat.card SL(3, ZMod 2) by rw [SL3.card_SL3]]
    exact orderOf_dvd_natCard c
  have hodd : Odd (orderOf c) := Odd.of_dvd_nat hn h1
  have hcop : Nat.Coprime (orderOf c) 8 :=
    Nat.Coprime.pow_right 3 (Nat.coprime_two_right.mpr hodd)
  exact orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_left h2)

theorem exists_conj_of_pow_eq_one {α : MulAut SL(3, ZMod 2)} {n : ℕ} (hn : Odd n)
    (hα : α ^ n = 1) : ∃ c : SL(3, ZMod 2), α = MulAut.conj c ∧ c ^ 21 = 1 := by
  set e := slEquivGL 3 with he
  set α' := MulAut.congr e α with hα'def
  have hα' : α' ^ n = 1 := by rw [hα'def, ← map_pow, hα, map_one]
  have hmem : α' ∈ (MulAut.conj : GL32 →* MulAut GL32).range := by
    obtain ⟨m, rfl⟩ := hn
    have h := Subgroup.mul_self_mem_of_index_two AutGL32.index_inner (α' ^ (m + 1))
    rwa [← pow_add, show m + 1 + (m + 1) = 2 * m + 1 + 1 by ring, pow_succ, hα', one_mul] at h
  obtain ⟨c', hc'⟩ := hmem
  have hcn : c' ^ n = 1 := by
    apply AutGL32.conj_injective
    rw [map_pow, hc', hα', map_one]
  refine ⟨e.symm c', ?_, sl3_pow_21 hn (by rw [← map_pow, hcn, map_one])⟩
  apply (MulAut.congr e).injective
  rw [congr_conj, MulEquiv.apply_symm_apply, ← hα'def]
  exact hc'.symm

end CFSG.Quasithin.H13.L32A
