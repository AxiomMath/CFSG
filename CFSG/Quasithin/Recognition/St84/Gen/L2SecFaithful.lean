module

public import CFSG.GH74.QTGen4.DSGen4.Defs

import CFSG.Quasithin.Recognition.St84.Gen.L2SecDim
import CFSG.Quasithin.EmptyFaithful.S1421QA19Stage
import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P1Gen
public import CFSG.GH74.QTGen4.DSGen4.Statements

public section

namespace CFSG.Quasithin.St84

open CFSG.GH74.QTGen4.DSGen4
open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem four_le_relIndex_of_nontrivial {V Z : Subgroup G} {l : G} (hsec : IsElemSec Z V)
    (hl : l ∈ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (Z : Set G))
    (hv : ∃ v ∈ V, ⁅l, v⁆ ∉ Z) : 4 ≤ Z.relIndex V := by
  have hZV : Z ≤ V := hsec.1
  have hlV : l ∈ Subgroup.normalizer (V : Set G) := (Subgroup.mem_inf.mp hl).1
  have hlZ : l ∈ Subgroup.normalizer (Z : Set G) := (Subgroup.mem_inf.mp hl).2
  obtain ⟨v, hvV, hne⟩ := hv
  have hvZ : v ∉ Z := by
    intro h
    exact hne (Z.mul_mem ((Subgroup.mem_normalizer_iff.mp hlZ v).mp h) (Z.inv_mem h))
  have hpos : 0 < Z.relIndex V := by
    rw [Subgroup.relIndex, Subgroup.index]
    exact Nat.card_pos
  have h2dvd : 2 ∣ Z.relIndex V := by
    haveI hN : (Z.subgroupOf V).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hZV).mpr
        (Subgroup.le_normalizer_iff_commutator_le_right.mpr
          ((Subgroup.commutator_mono le_rfl hZV).trans hsec.2.1))
    let q : ↥V →* ↥V ⧸ Z.subgroupOf V := QuotientGroup.mk' (Z.subgroupOf V)
    have hq1 : q ⟨v, hvV⟩ ≠ 1 := by
      intro h
      exact hvZ (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h))
    have hq2 : q ⟨v, hvV⟩ ^ 2 = 1 := by
      rw [← map_pow]
      have hmem : (⟨v, hvV⟩ : ↥V) ^ 2 ∈ Z.subgroupOf V := by
        rw [Subgroup.mem_subgroupOf]
        simpa [Subgroup.coe_pow] using hsec.2.2 v hvV
      exact (QuotientGroup.eq_one_iff ((⟨v, hvV⟩ : ↥V) ^ 2)).mpr hmem
    have hord : orderOf (q ⟨v, hvV⟩) = 2 := by
      have hdvd : orderOf (q ⟨v, hvV⟩) ∣ 2 := orderOf_dvd_of_pow_eq_one hq2
      have hne1 : orderOf (q ⟨v, hvV⟩) ≠ 1 := fun h => hq1 (orderOf_eq_one_iff.mp h)
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact absurd h hne1
      · exact h
    have hdvd := orderOf_dvd_natCard (q ⟨v, hvV⟩)
    rw [hord] at hdvd
    rwa [Subgroup.relIndex, Subgroup.index]
  by_contra h4
  push Not at h4
  obtain ⟨k, hk⟩ := h2dvd
  have hk1 : k = 1 := by omega
  have h2 : Z.relIndex V = 2 := by omega
  exact hne (CFSG.Quasithin.S15223.commutator_mem_of_relIndex_le_two (Or.inr h2) hlZ hlV hvV)

private theorem false_of_trivial_on_quotients {V Z W L : Subgroup G} {m : ℕ}
    (hm : 2 ≤ m) (hquot : IsL2Quot m (oTwoQuot ↥L)) (hsec : IsElemSec Z V)
    (hL : L ≤ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (Z : Set G))
    (hQ : ∀ p ∈ pCoreOf 2 L, ∀ v ∈ V, ⁅p, v⁆ ∈ Z)
    (hWV : W ≤ V)
    (htrivW : ∀ l ∈ L, ∀ w ∈ W, ⁅l, w⁆ ∈ Z)
    (htrivV : ∀ l ∈ L, ∀ v ∈ V, ⁅l, v⁆ ∈ W)
    (hnt : ∃ l ∈ L, ∃ v ∈ V, ⁅l, v⁆ ∉ Z) : False := by
  classical
  let N : Subgroup ↥L :=
    { carrier := {x | ∀ v ∈ V, ⁅(x : G), v⁆ ∈ Z}
      one_mem' := by
        intro v _
        simp
      mul_mem' := by
        intro x y hx hy v hv
        have e : ⁅((x * y : ↥L) : G), v⁆ =
            (x : G) * ⁅(y : G), v⁆ * (x : G)⁻¹ * ⁅(x : G), v⁆ := by
          simp only [Subgroup.coe_mul, commutatorElement_def]
          group
        rw [e]
        exact Z.mul_mem
          ((Subgroup.mem_normalizer_iff.mp (Subgroup.mem_inf.mp (hL x.2)).2 _).mp (hy v hv))
          (hx v hv)
      inv_mem' := by
        intro x hx v hv
        have e : ⁅((x⁻¹ : ↥L) : G), v⁆ =
            (x : G)⁻¹ * ⁅(x : G), v⁆⁻¹ * (x : G) := by
          simp only [Subgroup.coe_inv, commutatorElement_def]
          group
        rw [e]
        have hxZ : (x : G)⁻¹ ∈ Subgroup.normalizer (Z : Set G) :=
          Subgroup.inv_mem _ (Subgroup.mem_inf.mp (hL x.2)).2
        simpa using (Subgroup.mem_normalizer_iff.mp hxZ _).mp (Z.inv_mem (hx v hv)) }
  have hNnormal : N.Normal := by
    refine ⟨fun n hn x => ?_⟩
    intro v hv
    have hxV : (x : G) ∈ Subgroup.normalizer (V : Set G) := (Subgroup.mem_inf.mp (hL x.2)).1
    have hxZ : (x : G) ∈ Subgroup.normalizer (Z : Set G) := (Subgroup.mem_inf.mp (hL x.2)).2
    have hconjV : (x : G)⁻¹ * v * (x : G) ∈ V := by
      simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxV) v).mp hv
    have e : ⁅((x * n * x⁻¹ : ↥L) : G), v⁆ =
        (x : G) * ⁅(n : G), (x : G)⁻¹ * v * (x : G)⁆ * (x : G)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp hxZ _).mp (hn _ hconjV)
  have hpCoreN : CFSG.pCore 2 ↥L ≤ N := by
    intro p hp v hv
    exact hQ p (Subgroup.mem_map.mpr ⟨p, hp, rfl⟩) v hv
  have hsqN : ∀ x : ↥L, x ^ 2 ∈ N := by
    intro x v hv
    have hwW : ⁅(x : G), v⁆ ∈ W := htrivV (x : G) x.2 v hv
    have hw2Z : ⁅(x : G), v⁆ ^ 2 ∈ Z := hsec.2.2 _ (hWV hwW)
    have hxwZ : ⁅(x : G), ⁅(x : G), v⁆⁆ ∈ Z := htrivW (x : G) x.2 _ hwW
    have e : ⁅((x ^ 2 : ↥L) : G), v⁆ =
        ⁅(x : G), ⁅(x : G), v⁆⁆ * ⁅(x : G), v⁆ ^ 2 := by
      simp only [Subgroup.coe_pow, Subgroup.coe_mul, commutatorElement_def, pow_two]
      group
    rw [e]
    exact Z.mul_mem hxwZ hw2Z
  let X := oTwoQuot ↥L
  let q : ↥L →* X := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  haveI hNmap : (N.map q).Normal := hNnormal.map q (QuotientGroup.mk'_surjective _)
  have hXsimple : IsSimpleGroup X :=
    CFSG.Quasithin.S1421NS.isSimpleGroup_of_isL2Quot (by omega) hquot
  rcases hXsimple.eq_bot_or_eq_top_of_normal (N.map q) with hbot | htop
  ·
    have hsqX : ∀ y : X, y ^ 2 = 1 := by
      intro y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) y
      change (q x) ^ 2 = 1
      have hx2 : q (x ^ 2) ∈ N.map q := Subgroup.mem_map.mpr ⟨x ^ 2, hsqN x, rfl⟩
      rw [hbot] at hx2
      have h1 : q (x ^ 2) = 1 := Subgroup.mem_bot.mp hx2
      rwa [map_pow] at h1
    haveI hcomm : IsMulCommutative X :=
      CFSG.BenderSuzuki.isMulCommutative_of_forall_sq_one hsqX
    have hprime : (Nat.card X).Prime := (Group.is_simple_iff_prime_card).mp hXsimple
    exact CFSG.Quasithin.QA19.not_prime_card_isL2Quot hm hquot hprime
  ·
    have hNtop : N = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hxmap : q x ∈ N.map q := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨n, hn, hnq⟩ := Subgroup.mem_map.mp hxmap
      have hmem : n⁻¹ * x ∈ CFSG.pCore 2 ↥L := by
        rw [← QuotientGroup.eq_one_iff]
        change q (n⁻¹ * x) = 1
        rw [map_mul, map_inv, hnq, inv_mul_cancel]
      have hxN : x ∈ N := by
        have h := N.mul_mem hn (hpCoreN hmem)
        simpa using h
      exact hxN
    obtain ⟨l, hl, v, hv, hne⟩ := hnt
    have hlN : (⟨l, hl⟩ : ↥L) ∈ N := by
      rw [hNtop]
      exact Subgroup.mem_top _
    exact hne (hlN v hv)

private theorem two_pow_le_relIndex_aux {V Z L : Subgroup G} {m : ℕ} (hm : 2 ≤ m)
    (hquot : IsL2Quot m (oTwoQuot ↥L)) (hsec : IsElemSec Z V)
    (hL : L ≤ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (Z : Set G))
    (hQ : ∀ p ∈ pCoreOf 2 L, ∀ v ∈ V, ⁅p, v⁆ ∈ Z)
    (hnt : ∃ l ∈ L, ∃ v ∈ V, ⁅l, v⁆ ∉ Z) :
    2 ^ (2 * m) ≤ Z.relIndex V := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ (V Z : Subgroup G), IsElemSec Z V →
    L ≤ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (Z : Set G) →
    (∀ p ∈ pCoreOf 2 L, ∀ v ∈ V, ⁅p, v⁆ ∈ Z) →
    (∃ l ∈ L, ∃ v ∈ V, ⁅l, v⁆ ∉ Z) → Z.relIndex V = n →
    2 ^ (2 * m) ≤ Z.relIndex V
  have key : ∀ n, P n := fun n =>
    Nat.strongRecOn (motive := P) n (fun n ih => by
      intro V Z hsec hL hQ hnt hrel
      by_cases hchief : ∀ W : Subgroup G, Z ≤ W → W ≤ V →
          L ≤ Subgroup.normalizer (W : Set G) → W = Z ∨ W = V
      · exact two_pow_le_relIndex_of_irreducible (by omega) hquot hsec.1 hsec hL hchief hnt
      · push Not at hchief
        obtain ⟨W, hZW, hWV, hLW, hWneZ, hWneV⟩ := hchief
        have hrelmul : Z.relIndex V = Z.relIndex W * W.relIndex V :=
          (Subgroup.relIndex_mul_relIndex Z W V hZW hWV).symm
        have hrelZW_pos : 0 < Z.relIndex W := by
          rw [Subgroup.relIndex, Subgroup.index]
          exact Nat.card_pos
        have hrelWV_pos : 0 < W.relIndex V := by
          rw [Subgroup.relIndex, Subgroup.index]
          exact Nat.card_pos
        have hrelZW_gt1 : 1 < Z.relIndex W := by
          have hne1 : Z.relIndex W ≠ 1 := fun h =>
            hWneZ (le_antisymm (Subgroup.relIndex_eq_one.mp h) hZW)
          omega
        have hrelWV_gt1 : 1 < W.relIndex V := by
          have hne1 : W.relIndex V ≠ 1 := fun h =>
            hWneV (le_antisymm hWV (Subgroup.relIndex_eq_one.mp h))
          omega
        have hsec_ZW : IsElemSec Z W :=
          ⟨hZW, (Subgroup.commutator_mono hWV hWV).trans hsec.2.1,
            fun e he => hsec.2.2 e (hWV he)⟩
        have hsec_WV : IsElemSec W V :=
          ⟨hWV, hsec.2.1.trans hZW, fun e he => hZW (hsec.2.2 e he)⟩
        have hL_ZW : L ≤ Subgroup.normalizer (W : Set G) ⊓
            Subgroup.normalizer (Z : Set G) :=
          le_inf hLW (hL.trans inf_le_right)
        have hL_VW : L ≤ Subgroup.normalizer (V : Set G) ⊓
            Subgroup.normalizer (W : Set G) :=
          le_inf (hL.trans inf_le_left) hLW
        have hQ_ZW : ∀ p ∈ pCoreOf 2 L, ∀ w ∈ W, ⁅p, w⁆ ∈ Z :=
          fun p hp w hw => hQ p hp w (hWV hw)
        have hQ_VW : ∀ p ∈ pCoreOf 2 L, ∀ v ∈ V, ⁅p, v⁆ ∈ W :=
          fun p hp v hv => hZW (hQ p hp v hv)
        by_cases hntW : ∃ l ∈ L, ∃ w ∈ W, ⁅l, w⁆ ∉ Z
        · have hlt : Z.relIndex W < n := by
            rw [← hrel, hrelmul]
            exact lt_mul_of_one_lt_right hrelZW_pos hrelWV_gt1
          have hIH : 2 ^ (2 * m) ≤ Z.relIndex W :=
            ih (Z.relIndex W) hlt W Z hsec_ZW hL_ZW hQ_ZW hntW rfl
          rw [hrelmul]
          exact hIH.trans (Nat.le_mul_of_pos_right _ hrelWV_pos)
        · push Not at hntW
          by_cases hntV : ∃ l ∈ L, ∃ v ∈ V, ⁅l, v⁆ ∉ W
          · have hlt : W.relIndex V < n := by
              rw [← hrel, hrelmul]
              exact lt_mul_of_one_lt_left hrelWV_pos hrelZW_gt1
            have hIH : 2 ^ (2 * m) ≤ W.relIndex V :=
              ih (W.relIndex V) hlt V W hsec_WV hL_VW hQ_VW hntV rfl
            rw [hrelmul]
            exact hIH.trans (Nat.le_mul_of_pos_left _ hrelZW_pos)
          · push Not at hntV
            exfalso
            exact false_of_trivial_on_quotients hm hquot hsec hL hQ hWV hntW hntV hnt)
  exact key (Z.relIndex V) V Z hsec hL hQ hnt rfl

theorem two_pow_le_relIndex_of_nontrivial {V Z L : Subgroup G} {m : ℕ} (hm : 1 ≤ m)
    (hquot : IsL2Quot m (oTwoQuot ↥L)) (hsec : IsElemSec Z V)
    (hL : L ≤ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (Z : Set G))
    (hQ : ∀ p ∈ pCoreOf 2 L, ∀ v ∈ V, ⁅p, v⁆ ∈ Z)
    (hnt : ∃ l ∈ L, ∃ v ∈ V, ⁅l, v⁆ ∉ Z) : 2 ^ (2 * m) ≤ Z.relIndex V := by
  rcases Nat.eq_or_lt_of_le hm with h | h
  · have hm1 : m = 1 := h.symm
    rw [hm1]
    obtain ⟨l, hl, v, hv, hne⟩ := hnt
    have h4 := four_le_relIndex_of_nontrivial hsec
      (Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp (hL hl)).1, (Subgroup.mem_inf.mp (hL hl)).2⟩)
      ⟨v, hv, hne⟩
    simpa using h4
  · exact two_pow_le_relIndex_aux (by omega) hquot hsec hL hQ hnt

end CFSG.Quasithin.St84
