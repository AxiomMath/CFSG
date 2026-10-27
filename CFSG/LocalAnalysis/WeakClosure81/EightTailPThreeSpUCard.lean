module

public import CFSG.LocalAnalysis.WeakClosure81.EightTailPShape
import CFSG.LocalAnalysis.WeakClosure81.EightFiveTwoSplitRank

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {G : Type} [Group G] [Finite G] {V H T : Subgroup G}
  {X : Type} [Group X] {φ : ↥(kGenIn V H) →* X}

theorem card_barSub_lt_card_V (d : ShapeData V H T φ) :
    Nat.card (barSub (kGenIn V H) φ V) < Nat.card V := by
  have hVK : V ≤ kGenIn V H := le_kGenIn_self V H
  have hJK : pCoreOf 2 (kGenIn V H) ≤ kGenIn V H :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 (kGenIn V H)
  have hrel := card_barSub_eq_relIndex_of_isBarMap hVK hJK d.bar
  haveI : IsMulCommutative (eSub V H T) := d.hyp83.isMulCommutative_eSub
  have hEsub : V ⊓ eSub V H T ≤ V ⊓ Subgroup.centralizer (eSub V H T : Set G) :=
    inf_le_inf_left V (Subgroup.le_centralizer (eSub V H T))
  have hCE : V ⊓ Subgroup.centralizer (eSub V H T : Set G) ≠ ⊥ := by
    intro hbot
    exact d.hyp83.inf_eSub_ne_bot (le_bot_iff.mp (hbot ▸ hEsub))
  have hle : V ⊓ Subgroup.centralizer (eSub V H T : Set G) ≤
      V ⊓ pCoreOf 2 (kGenIn V H) :=
    le_inf inf_le_left (d.hyp83.inf_centralizer_eSub_le_pCoreOf d.eq_sup)
  have hne : V ⊓ pCoreOf 2 (kGenIn V H) ≠ ⊥ := by
    intro hbot
    exact hCE (le_bot_iff.mp (hbot ▸ hle))
  have hne' : pCoreOf 2 (kGenIn V H) ⊓ V ≠ ⊥ := by rwa [inf_comm]
  rw [hrel]
  change ((pCoreOf 2 (kGenIn V H)).subgroupOf V).index < Nat.card V
  have hsub_ne : (pCoreOf 2 (kGenIn V H)).subgroupOf V ≠ ⊥ := by
    intro hbot
    apply hne'
    rw [Subgroup.eq_bot_iff_forall] at hbot ⊢
    intro x hx
    have hxV : x ∈ V := (Subgroup.mem_inf.mp hx).2
    have hxN : x ∈ pCoreOf 2 (kGenIn V H) := (Subgroup.mem_inf.mp hx).1
    exact Subtype.ext_iff.mp (hbot ⟨x, hxV⟩ hxN)
  have hNge2 : 2 ≤ Nat.card ((pCoreOf 2 (kGenIn V H)).subgroupOf V) := by
    have h1 : 1 < Nat.card ((pCoreOf 2 (kGenIn V H)).subgroupOf V) :=
      (Subgroup.one_lt_card_iff_ne_bot ((pCoreOf 2 (kGenIn V H)).subgroupOf V)).mpr hsub_ne
    omega
  have hindex := Subgroup.index_mul_card ((pCoreOf 2 (kGenIn V H)).subgroupOf V)
  have h2 : 2 * ((pCoreOf 2 (kGenIn V H)).subgroupOf V).index ≤ Nat.card V := by
    rw [mul_comm 2, ← hindex]
    exact Nat.mul_le_mul_left _ hNge2
  have h3 : ((pCoreOf 2 (kGenIn V H)).subgroupOf V).index <
      2 * ((pCoreOf 2 (kGenIn V H)).subgroupOf V).index := by
    have hpos : ((pCoreOf 2 (kGenIn V H)).subgroupOf V).index ≠ 0 :=
      Subgroup.index_ne_zero_of_finite
    omega
  exact lt_of_lt_of_le h3 h2

section Certified


theorem card_V_gt_unitary (hRU : UnitaryRootCommutatorRank) (d : ShapeData V H T φ) {m n : ℕ}
    (hm : 3 ≤ m) (hX : IsPSUGp (X ⧸ Subgroup.center X) m n)
    (hr : IsUnitaryRootGroup X m n (barSub (kGenIn V H) φ V)) : (2 ^ n) ^ 2 < Nat.card V := by
  obtain ⟨-, F, hFld, hFin, hFcard, e, he⟩ := hr
  obtain ⟨φ', hφ', hbar⟩ := exists_ambient_barMap d.hyp83 d.eq_sup d.bar
  have h711 : Hyp711 (ambV V H) (⊤ : Subgroup ↥H) (ambE V H T) :=
    AmbientH.hyp711 d.hyp83 d.eq_sup
  have hroot : ∀ k : ↥(ambK V H T), (k : ↥H) ∈ ambV V H →
      (k : ↥H) ∉ pCoreOf 2 (ambK V H T) → IsUnitaryTransvection X m n (φ' k) := by
    intro k hkV hkJ
    have hmem : φ' k ∈ barSub (kGenIn V H) φ V := by
      rw [← hbar]
      exact mem_barSub.mpr ⟨k, hkV, rfl⟩
    have hne : φ' k ≠ 1 := fun h1 => hkJ ((hφ'.ker_iff k).mp h1)
    exact ⟨F, hFld, hFin, hFcard, e, he (φ' k) hmem hne⟩
  have h13 := seven_thirteen hRU h711 hφ' hm hX hroot
  have hrk : 2 * n + 1 ≤ rk ↥V := by
    rw [← rk_subgroupOf_eq d.hyp83.le_H]
    exact h13.1
  have hcard : Nat.card V = 2 ^ rk ↥V :=
    card_eq_two_pow_of_isPGroup
      (CFSG.CGT.Timmesfeld75.isPGroup_two_of_isElemAbelian d.hyp83.elemAbelian)
  rw [hcard]
  calc (2 ^ n) ^ 2 = 2 ^ (2 * n) := by rw [← pow_mul, mul_comm]
    _ < 2 ^ (2 * n + 1) := (Nat.pow_lt_pow_iff_right (by norm_num)).2 (by omega)
    _ ≤ 2 ^ rk ↥V := Nat.pow_le_pow_right Nat.zero_lt_two hrk

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
