module

public import CFSG.LocalAnalysis.WeakClosure81.SixFifteen
public import CFSG.CharacterTheory.Burnside

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase
open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_wClos_or_centerOf {V H T : Subgroup G} (hV : IsElemAbelian 2 V)
    (hT : IsSylowIn 2 T H) {p : ℕ} (hp : p.Prime) (hidx : T.relIndex H = p)
    (hInE : E1.InE 1 H) {i : ℕ} (hi : i + 1 < E3.sParam hV) :
    H ≤ normalizer (E3.wClos V i T : Set G) ∨
      H ≤ normalizer (centerOf (E3.wClos V (i + 1) T) : Set G) := by
  have hfac := e3_19_of_inE hV hT hInE hi
  have hTN : T ≤ normalizer (E3.wClos V i T : Set G) :=
    Subgroup.le_normalizer.trans (E3.normalizer_le_normalizer_wClos T)
  have hTH : T ≤ H := hT.1
  set K : Subgroup G := H ⊓ normalizer (E3.wClos V i T : Set G) with hK
  have hTK : T ≤ K := le_inf hTH hTN
  have hKH : K ≤ H := inf_le_left
  have hmul : T.relIndex K * K.relIndex H = p := by
    rw [Subgroup.relIndex_mul_relIndex T K H hTK hKH, hidx]
  rcases Nat.prime_mul_iff.1 (hmul ▸ hp) with ⟨-, h1⟩ | ⟨-, h1⟩
  · left
    have hHK : H ≤ K := Subgroup.relIndex_eq_one.1 h1
    exact hHK.trans inf_le_right
  · right
    have hKT : K ≤ T := Subgroup.relIndex_eq_one.1 h1
    have hTZ : T ≤ normalizer (centerOf (E3.wClos V (i + 1) T) : Set G) :=
      Subgroup.le_normalizer.trans
        ((E3.normalizer_le_normalizer_wClos T).trans (E3.normalizer_le_normalizer_centerOf _))
    have hCZ : centralizer (E3.cClos V (i + 1) T : Set G) ≤
        normalizer (centerOf (E3.wClos V (i + 1) T) : Set G) :=
      (Subgroup.centralizer_le (centerOf_wClos_le_cClos_self (i + 1) T)).trans
        (Subgroup.centralizer_le_normalizer _)
    rw [← hfac]
    exact sup_le (inf_le_right.trans hCZ) (hKT.trans hTZ)

theorem wc_of_delta_pair {V M T X₁ H : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : rankThreeIsMaxTwoLocal M) (hT2 : IsPGroup 2 T) (hW0 : E3.wClos V 0 T ≠ ⊥)
    {p k j : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hks : k + 1 < E3.sParam hV)
    (hX₁M : X₁ ≤ M) (hTH : T ≤ H) (hHM : H ≤ M) (hcard : Nat.card H = p * Nat.card T)
    (hU : InCalU M (X₁ ⊔ H)) (hkj : k + 1 ≤ j) (hjd : j < rk ↥V)
    (hX₁N : X₁ ≤ normalizer (E3.wClos V j T : Set G)) :
    ∃ i ≤ 1, normalizer (E3.wClos V i T : Set G) ≤ M ∧
      centralizer (E3.cClos V (k + i) T : Set G) ≤ M := by
  classical
  have hidx : T.relIndex H = p := by
    have h1 := Subgroup.relIndex_mul_card T H
    rw [inf_of_le_left hTH] at h1
    have h2 : T.relIndex H * Nat.card ↥T = p * Nat.card ↥T := by rw [h1, hcard]
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h2
  have hTsyl : IsSylowIn 2 T H := by
    refine ⟨hTH, hT2, ?_⟩
    rw [hidx]
    intro h2dvd
    exact hp2 (((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2dvd).symm)
  have hInE : E1.InE 1 H := by
    obtain ⟨a, ha⟩ := hT2.exists_card_eq
    have hsolv : Group.IsSolvable ↥H := by
      let : Fintype ↥H := Fintype.ofFinite _
      refine CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
        (p := p) (q := 2) (a := 1) (b := a) hp Nat.prime_two hp2 ?_
      rw [← Nat.card_eq_fintype_card, hcard, ha, pow_one]
    exact (E1.inE_subgroupOf 1 H).2 (E1.inE_one_top_of_isSolvable (Nat.card ↥H) ↥H le_rfl hsolv)
  have hd : Nat.card V = 2 ^ rk ↥V :=
    card_eq_two_pow_of_isPGroup (B2F.isPGroup_of_isElemAbelian hV)
  have hWne : ∀ i, i < rk ↥V → E3.wClos V i T ≠ ⊥ := fun i hi hbot =>
    hW0 (le_bot_iff.1 (hbot ▸ SteinbergBS.wClos_le_wClos hV hd (Nat.zero_le i) hi T))
  have hW2 : ∀ i, IsPGroup 2 (E3.wClos V i T) := fun i => hT2.to_le (E3.wClos_le i T)
  have hZne : ∀ i, i < rk ↥V → centerOf (E3.wClos V i T) ≠ ⊥ := fun i hi =>
    E3.centerOf_ne_bot_of_isPGroup (hW2 i) (hWne i hi)
  have hZ2 : ∀ i, IsPGroup 2 (centerOf (E3.wClos V i T)) := fun i => (hW2 i).to_le inf_le_left
  have hX₁i : ∀ i, i ≤ j → X₁ ≤ normalizer (E3.wClos V i T : Set G) := fun i hi =>
    hX₁N.trans (normalizer_wClos_anti hV hi hjd)
  have hX₁Z : ∀ i, i ≤ j → X₁ ≤ normalizer (centerOf (E3.wClos V i T) : Set G) := fun i hi =>
    (hX₁i i hi).trans (E3.normalizer_le_normalizer_centerOf _)
  rcases le_normalizer_wClos_or_centerOf hV hTsyl hp hidx hInE hks with hA | hB
  ·
    have hUk : InCalU M (M ⊓ normalizer (E3.wClos V k T : Set G)) :=
      InCalU.mono hM hU (le_inf (sup_le hX₁M hHM) (sup_le (hX₁i k (by omega)) hA)) inf_le_left
    obtain ⟨hN, hC⟩ := six_fifteen_three hV hM hT2 hW0 (by omega : k < rk ↥V) hUk
    refine ⟨0, by norm_num, hN 0 (by omega), ?_⟩
    simpa using hC 0 (Nat.zero_le k)
  ·
    have hNZ : normalizer (centerOf (E3.wClos V (k + 1) T) : Set G) ≤ M :=
      normalizer_le_of_inCalU hU (sup_le (hX₁Z (k + 1) hkj) hB) (hZne (k + 1) (by omega))
        (hZ2 (k + 1))
    have hCk1 : centralizer (E3.cClos V (k + 1) T : Set G) ≤ M :=
      (Subgroup.centralizer_le (centerOf_wClos_le_cClos_self (k + 1) T)).trans
        ((Subgroup.centralizer_le_normalizer _).trans hNZ)
    have hCk : centralizer (E3.cClos V k T : Set G) ≤ M :=
      (Subgroup.centralizer_le (cClos_anti hV (Nat.le_succ k) (by omega) T)).trans hCk1
    rcases le_normalizer_wClos_or_centerOf hV hTsyl hp hidx hInE (i := 0) (by omega)
      with hA0 | hB0
    · refine ⟨0, by norm_num, ?_, by simpa using hCk⟩
      exact normalizer_le_of_inCalU hU (sup_le (hX₁i 0 (Nat.zero_le j)) hA0) (hWne 0 (by omega))
        (hW2 0)
    · refine ⟨1, le_rfl, ?_, hCk1⟩
      exact (E3.normalizer_le_normalizer_centerOf _).trans
        (normalizer_le_of_inCalU hU (sup_le (hX₁Z 1 (by omega)) hB0) (hZne 1 (by omega))
          (hZ2 1))

end CFSG.LocalAnalysis.WeakClosure81
