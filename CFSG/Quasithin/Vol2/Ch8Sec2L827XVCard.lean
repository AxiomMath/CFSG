module

public import CFSG.Quasithin.Vol2.Ch8Sec2L827XInputs
public import CFSG.Quasithin.Background.SmithB45Sp4Herm
public import CFSG.Quasithin.Background.HMathieuFactsBase

public section

namespace CFSG.Quasithin.H13.L827X

open CFSG.Quasithin CFSG.Quasithin.B45Sp4
open scoped IsMulCommutative

theorem card_of_binaryNineTensor {V : Type*} [CommGroup V] {H : Subgroup (MulAut V)} {a : ℕ}
    (ha : 1 ≤ a) (h : BinaryNineTensor H ⊤ ⊥ a) : Nat.card V = 2 ^ (9 * a) := by
  obtain ⟨K, _, _, _, hK, π, hπ⟩ := h
  obtain ⟨-, -, -, -, -, -, -, β, hβs, hβk, -⟩ := hπ
  have hinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have := (hβk u).1 hu
    exact Subtype.ext (Subgroup.mem_bot.1 this)
  have hbij : Function.Bijective β := ⟨hinj, hβs⟩
  have h1 : Nat.card ↥(⊤ : Subgroup V) =
      Nat.card (↥(FFModel.twistTensor a (CFSG.Open.StatedSL 3 K)).sec ⧸
        (FFModel.twistTensor a (CFSG.Open.StatedSL 3 K)).ker.subgroupOf
          (FFModel.twistTensor a (CFSG.Open.StatedSL 3 K)).sec) :=
    Nat.card_congr (Equiv.ofBijective β hbij)
  rw [Subgroup.card_top] at h1
  have h2 : Nat.card (↥(FFModel.twistTensor a (CFSG.Open.StatedSL 3 K)).sec ⧸
        (FFModel.twistTensor a (CFSG.Open.StatedSL 3 K)).ker.subgroupOf
          (FFModel.twistTensor a (CFSG.Open.StatedSL 3 K)).sec) =
      Nat.card ↥(hermSub a (Fin 3) K) := by
    show Nat.card (↥(hermSub a (Fin 3) K) ⧸ (⊥ : Subgroup _).subgroupOf (hermSub a (Fin 3) K)) = _
    rw [Subgroup.bot_subgroupOf]
    exact Nat.card_congr (QuotientGroup.quotientBot).toEquiv
  have h3 : Nat.card ↥(hermSub a (Fin 3) K) = Nat.card ↥(hermA a (Fin 3) K) :=
    Nat.card_congr
      { toFun := fun x => ⟨Multiplicative.toAdd (x : Multiplicative (Matrix (Fin 3) (Fin 3) K)),
          x.2⟩
        invFun := fun y => ⟨Multiplicative.ofAdd (y : Matrix (Fin 3) (Fin 3) K), y.2⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  have hsq : Nat.card ↥(hermA a (Fin 3) K) ^ 2 = (2 ^ (9 * a)) ^ 2 := by
    rw [card_hermA_sq (ι := Fin 3) ha hK, Fintype.card_fin, hK, ← pow_mul, ← pow_mul]
    congr 1
    ring
  have hA : Nat.card ↥(hermA a (Fin 3) K) = 2 ^ (9 * a) :=
    Nat.pow_left_injective two_ne_zero hsq
  rw [h2, h3, hA] at h1
  exact h1

theorem stmt827VCard_holds : Stmt827VCard := by
  intro G _ _ T L I _ _ hor
  rcases hor with hL | hM
  · rcases hL with ⟨-, hB⟩
    rw [card_of_binaryNineTensor (V := ↥(fsuV T I)) (le_refl 1) hB]
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  · exact (CFSG.Quasithin.H.Mathieu.code22_card hM).le

end CFSG.Quasithin.H13.L827X
