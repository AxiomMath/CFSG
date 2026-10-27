module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSADefs
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieCartanAux6

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix
open scoped IsMulCommutative

open scoped MatrixGroups

section CartanVocab

variable {G : Type} [Group G] {p N : ℕ} {Bs : Subgroup G}

theorem ggCartanRank_le (hp : p.Prime) (hp2 : p ≠ 2) (hel : IsElemAbelian p Bs) [Finite Bs]
    (ρ : Equiv.Perm (Fin N) →* MulAut ↥Bs) (hinj : Function.Injective ρ)
    (hrefl : ∀ a b : Fin N, a ≠ b → GGIsReflection p (ρ (Equiv.swap a b)))
    (hnotr : ∀ g : Equiv.Perm (Fin N), ¬ GGIsTransvection p (ρ g)) :
    p ^ (N - 1 - (if p ∣ N then 1 else 0)) ≤ Nat.card Bs := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsMulCommutative ↥Bs := hel.1
  have hexp : ∀ b : ↥Bs, b ^ p = 1 := fun b => by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hel.2 (b : G) b.2]
    rfl
  haveI : Module (ZMod p) (Additive ↥Bs) := ggNSLiePI2_moduleV hp hexp
  haveI : Fintype ↥Bs := Fintype.ofFinite _
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rcases Nat.lt_or_ge N 2 with hN | hN
  ·
    have hcard : 1 ≤ Nat.card ↥Bs := Nat.succ_le_of_lt Nat.card_pos
    interval_cases N <;> · simp only [Nat.zero_sub, Nat.sub_self, pow_zero]; exact hcard
  ·
    have hrefl' : ∀ i : Fin (N - 1),
        GGIsReflection p (ρ (ggNSLiePI2_simpleSwap N i)) := by
      intro i
      exact hrefl ⟨i.1, by omega⟩ ⟨i.1 + 1, by omega⟩ (by intro h; have := Fin.ext_iff.mp h; simp only [Fin.val_mk] at this; omega)
    choose x g hx0 hgx hnorm using fun i : Fin (N - 1) =>
      ggNSLiePI2_reflection_data hp hp2 hel (ρ (ggNSLiePI2_simpleSwap N i)) (hrefl' i)
    let xN : ℕ → Additive ↥Bs := fun k => if h : k < N - 1 then x ⟨k, h⟩ else 0
    let gN : ℕ → Module.Dual (ZMod p) (Additive ↥Bs) :=
      fun k => if h : k < N - 1 then g ⟨k, h⟩ else 0
    have hdiag : ∀ i, i < N - 1 → gN i (xN i) = 2 := by
      intro i hi
      simp only [xN, gN, dif_pos hi]
      exact hgx ⟨i, hi⟩
    have hoff : ∀ i j, i < N - 1 → j < N - 1 → j ≠ i → j ≠ i + 1 → i ≠ j + 1 →
        gN i (xN j) = 0 := by
      intro i j hi hj hji hj1 hi1
      simp only [xN, gN, dif_pos hi, dif_pos hj]
      exact ggNSLiePI2_hoff hp hp2 hel ρ hinj hnotr hrefl ⟨i, hi⟩ ⟨j, hj⟩
        (by simpa using hji.symm) (by simpa using hj1.symm) (by simpa using hi1)
        hx0 hgx hnorm
    have hadj : ∀ i, i + 1 < N - 1 →
        gN i (xN (i + 1)) * gN (i + 1) (xN i) = 1 := by
      intro i hi
      have hi' : i < N - 1 := by omega
      simp only [xN, gN, dif_pos hi', dif_pos hi, dif_pos (show i + 1 < N - 1 from hi)]
      exact ggNSLiePI2_hadj hp hp2 hel ρ hinj hnotr hrefl ⟨i, hi'⟩ hi hx0 hgx hnorm
    have hbound : N - 1 - (if (↑(N - 1) + 1 : ZMod p) = 0 then 1 else 0) ≤
        Module.finrank (ZMod p) (Additive ↥Bs) :=
      ggNSLiePI2_rank_bound (K := ZMod p) (V := Additive ↥Bs) (N - 1) xN gN hdiag hoff hadj
    have hif : (if (↑(N - 1) + 1 : ZMod p) = 0 then 1 else 0) =
        (if p ∣ N then 1 else 0) := by
      have hcast : ((N - 1 : ℕ) + 1 : ℕ) = N := Nat.sub_add_cancel (by omega : 1 ≤ N)
      have h : (↑(N - 1) + 1 : ZMod p) = 0 ↔ p ∣ N := by
        rw [show (↑(N - 1) + 1 : ZMod p) = ((N - 1 + 1 : ℕ) : ZMod p) by push_cast; ring,
          hcast, ZMod.natCast_eq_zero_iff]
      simp only [h]
    simp only [hif] at hbound
    have hcard : Nat.card ↥Bs = p ^ Module.finrank (ZMod p) (Additive ↥Bs) := by
      haveI : Fintype (ZMod p) := ZMod.fintype p
      haveI : Fintype (Additive ↥Bs) := Fintype.ofFinite (Additive ↥Bs)
      change Nat.card (Additive ↥Bs) = p ^ Module.finrank (ZMod p) (Additive ↥Bs)
      rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p) (V := Additive ↥Bs),
        ZMod.card p]
    calc p ^ (N - 1 - (if p ∣ N then 1 else 0))
        ≤ p ^ Module.finrank (ZMod p) (Additive ↥Bs) :=
          Nat.pow_le_pow_right hp.pos hbound
      _ = Nat.card ↥Bs := hcard.symm

end CartanVocab

end CFSG.StandardType

end
