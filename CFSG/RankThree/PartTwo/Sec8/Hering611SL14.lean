module

public import CFSG.RankThree.PartTwo.Sec8.Hering611SBasic
public import CFSG.RankThree.PartTwo.Sec8.Hering611SInner
import CFSG.RankThree.PartTwo.Sec8.Hering611K

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4

section L14


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L E T : Subgroup G} {d : G}
  {S K : Subgroup G}

theorem Frame611.inf_L_le_sec11K (F : Frame611 G A c L E T d) : A ⊓ L ≤ Sec11.sec11K L d := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro x hx
  obtain ⟨φ⟩ := F.iso_L
  obtain ⟨hdN, hQ, -⟩ := Sec6.Hering611.fieldCent_facts_two φ F.d_field F.d_pow_three
  have hxd : x ∈ L ⊓ Subgroup.centralizer ({d} : Set G) :=
    ⟨hx.2, Subgroup.mem_centralizer_singleton_iff.mpr (F.comm_of_mem hx.1 F.d_mem_A)⟩
  exact Sec11.mem_sec11K_of_pow_eq_one hdN F.d_pow_three hQ.1 hxd (k := 1)
    (by simpa using F.isElemAbelian.2 x hx.1)

theorem Cfg611.inf_L_le_K (C : Cfg611 G A c L E T d S K) : A ⊓ L ≤ K :=
  C.toFrame611.inf_L_le_sec11K.trans C.perf_le

theorem Frame611.card_inf_L (h45 : Sec4.Item4_5) (F : Frame611 G A c L E T d) :
    Nat.card ↥(A ⊓ L) = 9 :=
  card_inf_L_of F.isElemAbelian F.maximal (F.A_le_normalizer_L h45) F.center_L_bot F.inner_nine

theorem Frame611.zpowers_inf_L (F : Frame611 G A c L E T d) :
    Subgroup.zpowers d ⊓ L = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxd, hxL⟩
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxd
  have hd3 := F.d_pow_three
  have hi : d ^ i = d ^ (i % 3) := by
    have : d ^ (3 : ℤ) = 1 := by
      rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hd3]
    exact zpow_eq_zpow_emod i this
  rw [Subgroup.mem_bot]
  rcases (show i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 by omega) with h | h | h
  · rw [hi, h, zpow_zero]
  · exfalso
    rw [hi, h, zpow_one] at hxL
    exact F.d_not_mem_L hxL
  · exfalso
    rw [hi, h] at hxL
    apply F.d_not_mem_L
    have h2 : d = (d ^ (2 : ℤ)) ^ (2 : ℕ) := by
      rw [← zpow_natCast, ← zpow_mul]
      have : d ^ (4 : ℤ) = d := by
        rw [show (4 : ℤ) = ((3 : ℕ) : ℤ) + 1 by norm_num, zpow_add, zpow_natCast, hd3, one_mul,
          zpow_one]
      simpa using this.symm
    rw [h2]
    exact L.pow_mem hxL 2

end L14

end CFSG.RankThree.PartTwo.Sec8.Hering611
