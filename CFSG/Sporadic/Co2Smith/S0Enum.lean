module

public import CFSG.Sporadic.Co2Smith.Structure
public import Certificates.Data.CFSGNative.Co2Smith.Census

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
open scoped Matrix

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

attribute [local instance] vAction

@[expose] noncomputable def tElt (k i : ℕ) : K :=
  if i = 0 then 1
  else if _hp : (chainRec k).2.1[i]! < i then
    chainElt k (chainRec k).2.2[i]! * tElt k (chainRec k).2.1[i]!
  else 1
termination_by i

theorem tElt_zero (k : ℕ) : tElt k 0 = 1 := by
  rw [tElt, ite_eq_left rfl]

theorem tElt_of_lt
    {k i : ℕ} (hi : i ≠ 0) (hp : (chainRec k).2.1[i]! < i) :
    tElt k i = chainElt k (chainRec k).2.2[i]! * tElt k (chainRec k).2.1[i]! := by
  rw [tElt, ite_eq_right hi, dite_eq_left hp]

theorem tRowsN_zero (r : Array ℕ × Array ℕ × Array ℕ) (G : Array (Array ℕ)) :
    Native.tRowsN r G 0 = idRows 22 := by
  rw [Native.tRowsN, ite_eq_left rfl]

theorem tRowsN_of_lt {r : Array ℕ × Array ℕ × Array ℕ} {G : Array (Array ℕ)} {i : ℕ}
    (hi : i ≠ 0) (hp : r.2.1[i]! < i) :
    Native.tRowsN r G i = mulRows 22 G[r.2.2[i]!]! (Native.tRowsN r G r.2.1[i]!) := by
  rw [Native.tRowsN, ite_eq_right hi, dite_eq_left hp]

theorem tElt_spec
    {k : ℕ} (hk : k < 6) : ∀ i < Native.chainOrb[k]!,
    tElt k i ∈ chainT k ∧ tElt k i • vec Native.chainBase[k]! = vec (chainRec k).1[i]! ∧
      (tElt k i).val.val = rowsMatrix 22 (Native.tRowsN (chainRec k) (chainRows k) i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    obtain ⟨-, h0, h⟩ := chain_spec hk
    rcases (h i hi).2 with rfl | ⟨hp, hl, heq⟩
    · rw [tElt_zero, h0, tRowsN_zero, rowsMatrix_idRows]
      exact ⟨Subgroup.one_mem _, one_smul _ _, rfl⟩
    · have hi0 : i ≠ 0 := by omega
      have hl' : (chainRec k).2.2[i]! < (Native.chainGens[k]!).size := by
        rwa [← chainRows_size]
      obtain ⟨ihm, ihs, ihv⟩ := ih _ hp (hp.trans hi)
      have ht := tElt_of_lt (k := k) hi0 hp
      refine ⟨?_, ?_, ?_⟩
      · rw [ht]
        exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨_, hl', rfl⟩) ihm
      · rw [ht, mul_smul, ihs, heq, Native.vecStep, ← rowsMatrix_mulVec_vec,
          ← chainElt_val hk hl', ← smul_V_def]
      · rw [ht, val_val_mul, ihv, chainElt_val hk hl', tRowsN_of_lt hi0 hp,
          rowsMatrix_mulRows, getElem!_pos (chainRows k) _ hl]

private theorem eq_of_mul_le {a b o p : ℕ} (ha : o ≤ a) (hb : p ≤ b) (ho : 0 < o)
    (hp : 0 < p) (h : a * b ≤ o * p) : a = o ∧ b = p := by
  have h1 : a * p ≤ o * p := (Nat.mul_le_mul_left a hb).trans h
  have h2 : a ≤ o := Nat.le_of_mul_le_mul_right h1 hp
  have hao : a = o := le_antisymm h2 ha
  subst hao
  have h3 : b ≤ p := Nat.le_of_mul_le_mul_left h ho
  exact ⟨rfl, le_antisymm h3 hb⟩

theorem chainStab_index_eq :
    (∀ k < 6, (chainStab (k + 1)).relIndex (chainStab k) = Native.chainOrb[k]!) ∧
      chainStab 6 = ⊥ := by
  have e0 := chain_relIndex (k := 0) (by norm_num)
  have e1 := chain_relIndex (k := 1) (by norm_num)
  have e2 := chain_relIndex (k := 2) (by norm_num)
  have e3 := chain_relIndex (k := 3) (by norm_num)
  have e4 := chain_relIndex (k := 4) (by norm_num)
  have e5 := chain_relIndex (k := 5) (by norm_num)
  rw [show Native.chainOrb[0]! = 63 from rfl] at e0
  rw [show Native.chainOrb[1]! = 32 from rfl] at e1
  rw [show Native.chainOrb[2]! = 15 from rfl] at e2
  rw [show Native.chainOrb[3]! = 8 from rfl] at e3
  rw [show Native.chainOrb[4]! = 3 from rfl] at e4
  rw [show Native.chainOrb[5]! = 2 from rfl] at e5
  have h0 : (chainStab 0).relIndex S0 = 1 := Subgroup.relIndex_self _
  have hprod := relIndex_chainStab_six
  have hmul := Subgroup.relIndex_mul_card (chainStab 6) S0
  rw [inf_eq_left.mpr (chainStab_le_S0 6), card_S0] at hmul
  rw [relIndex_chainStab_succ, relIndex_chainStab_succ, relIndex_chainStab_succ,
    relIndex_chainStab_succ, relIndex_chainStab_succ, relIndex_chainStab_succ, h0,
    mul_one] at hmul hprod
  have hc : 0 < Nat.card (chainStab 6) := Nat.card_pos
  set a0 := (chainStab 1).relIndex (chainStab 0)
  set a1 := (chainStab 2).relIndex (chainStab 1)
  set a2 := (chainStab 3).relIndex (chainStab 2)
  set a3 := (chainStab 4).relIndex (chainStab 3)
  set a4 := (chainStab 5).relIndex (chainStab 4)
  set a5 := (chainStab 6).relIndex (chainStab 5)
  have hP : a5 * (a4 * (a3 * (a2 * (a1 * a0)))) ≤ 2 * (3 * (8 * (15 * (32 * 63)))) := by
    have : a5 * (a4 * (a3 * (a2 * (a1 * a0)))) * 1 ≤
        a5 * (a4 * (a3 * (a2 * (a1 * a0)))) * Nat.card (chainStab 6) :=
      Nat.mul_le_mul_left _ hc
    omega
  have g1 : 32 * 63 ≤ a1 * a0 := Nat.mul_le_mul e1 e0
  have g2 : 15 * (32 * 63) ≤ a2 * (a1 * a0) := Nat.mul_le_mul e2 g1
  have g3 : 8 * (15 * (32 * 63)) ≤ a3 * (a2 * (a1 * a0)) := Nat.mul_le_mul e3 g2
  have g4 : 3 * (8 * (15 * (32 * 63))) ≤ a4 * (a3 * (a2 * (a1 * a0))) := Nat.mul_le_mul e4 g3
  obtain ⟨f5, r4⟩ := eq_of_mul_le e5 g4 (by norm_num) (by norm_num) hP
  obtain ⟨f4, r3⟩ := eq_of_mul_le e4 g3 (by norm_num) (by norm_num) r4.le
  obtain ⟨f3, r2⟩ := eq_of_mul_le e3 g2 (by norm_num) (by norm_num) r3.le
  obtain ⟨f2, r1⟩ := eq_of_mul_le e2 g1 (by norm_num) (by norm_num) r2.le
  obtain ⟨f1, f0⟩ := eq_of_mul_le e1 e0 (by norm_num) (by norm_num) r1.le
  refine ⟨fun k hk => ?_, ?_⟩
  · interval_cases k
    · exact f0
    · exact f1
    · exact f2
    · exact f3
    · exact f4
    · exact f5
  · apply Subgroup.eq_bot_of_card_eq
    rw [f5, f4, f3, f2, f1, f0] at hmul
    omega

theorem exists_tElt_inv_mul
    {k : ℕ} (hk : k < 6) {g : K} (hg : g ∈ chainStab k) :
    ∃ i < Native.chainOrb[k]!, (tElt k i)⁻¹ * g ∈ chainStab (k + 1) := by
  set b := vec Native.chainBase[k]!
  have hcard : (MulAction.orbit (chainStab k) b).ncard = Native.chainOrb[k]! := by
    rw [← relIndex_inf_stabilizer]
    exact chainStab_index_eq.1 k hk
  have hsub : Set.range (fun i : Fin Native.chainOrb[k]! => vec (chainRec k).1[(i : ℕ)]!) ⊆
      MulAction.orbit (chainStab k) b := by
    rintro _ ⟨i, rfl⟩
    obtain ⟨hm, hs, -⟩ := tElt_spec hk i i.2
    exact ⟨⟨tElt k i, chainT_le hk hm⟩, hs⟩
  have hrange : (Set.range (fun i : Fin Native.chainOrb[k]! =>
      vec (chainRec k).1[(i : ℕ)]!)).ncard = Native.chainOrb[k]! := by
    rw [Set.ncard_range_of_injective (chain_injective hk), Nat.card_fin]
  have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [hcard, hrange]) (Set.toFinite _)
  have hgb : g • b ∈ MulAction.orbit (chainStab k) b := ⟨⟨g, hg⟩, rfl⟩
  rw [← heq] at hgb
  obtain ⟨i, hi⟩ := hgb
  have hi' : g • b = vec (chainRec k).1[(i : ℕ)]! := hi.symm
  obtain ⟨hm, hs, -⟩ := tElt_spec hk i i.2
  refine ⟨i, i.2, ?_⟩
  show (tElt k i)⁻¹ * g ∈ chainStab k ⊓ MulAction.stabilizer K b
  refine Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ (chainT_le hk hm)) hg, ?_⟩
  rw [MulAction.mem_stabilizer_iff, mul_smul, hi', ← hs, ← mul_smul, inv_mul_cancel, one_smul]

@[expose] noncomputable def sElt (n : ℕ) : K :=
  tElt 0 (n % 63) * (tElt 1 (n / 63 % 32) * (tElt 2 (n / 2016 % 15) *
    (tElt 3 (n / 30240 % 8) * (tElt 4 (n / 241920 % 3) * tElt 5 (n / 725760 % 2)))))

theorem tElt_mem_S0
    {k i : ℕ} (hk : k < 6) (hi : i < Native.chainOrb[k]!) : tElt k i ∈ S0 :=
  chainStab_le_S0 k (chainT_le hk (tElt_spec hk i hi).1)

theorem sElt_mem_S0
    (n : ℕ) : sElt n ∈ S0 := by
  have h0 := tElt_mem_S0 (k := 0) (i := n % 63) (by norm_num) (Nat.mod_lt _ (by norm_num))
  have h1 := tElt_mem_S0 (k := 1) (i := n / 63 % 32) (by norm_num) (Nat.mod_lt _ (by norm_num))
  have h2 := tElt_mem_S0 (k := 2) (i := n / 2016 % 15) (by norm_num) (Nat.mod_lt _ (by norm_num))
  have h3 := tElt_mem_S0 (k := 3) (i := n / 30240 % 8) (by norm_num) (Nat.mod_lt _ (by norm_num))
  have h4 := tElt_mem_S0 (k := 4) (i := n / 241920 % 3) (by norm_num) (Nat.mod_lt _ (by norm_num))
  have h5 := tElt_mem_S0 (k := 5) (i := n / 725760 % 2) (by norm_num) (Nat.mod_lt _ (by norm_num))
  exact S0.mul_mem h0 (S0.mul_mem h1 (S0.mul_mem h2 (S0.mul_mem h3 (S0.mul_mem h4 h5))))

theorem exists_sElt
    {s : K} (hs : s ∈ S0) : ∃ n < 1451520, sElt n = s := by
  obtain ⟨i0, hi0, g1⟩ := exists_tElt_inv_mul (k := 0) (by norm_num) hs
  obtain ⟨i1, hi1, g2⟩ := exists_tElt_inv_mul (k := 1) (by norm_num) g1
  obtain ⟨i2, hi2, g3⟩ := exists_tElt_inv_mul (k := 2) (by norm_num) g2
  obtain ⟨i3, hi3, g4⟩ := exists_tElt_inv_mul (k := 3) (by norm_num) g3
  obtain ⟨i4, hi4, g5⟩ := exists_tElt_inv_mul (k := 4) (by norm_num) g4
  obtain ⟨i5, hi5, g6⟩ := exists_tElt_inv_mul (k := 5) (by norm_num) g5
  rw [chainStab_index_eq.2, Subgroup.mem_bot] at g6
  rw [show Native.chainOrb[0]! = 63 from rfl] at hi0
  rw [show Native.chainOrb[1]! = 32 from rfl] at hi1
  rw [show Native.chainOrb[2]! = 15 from rfl] at hi2
  rw [show Native.chainOrb[3]! = 8 from rfl] at hi3
  rw [show Native.chainOrb[4]! = 3 from rfl] at hi4
  rw [show Native.chainOrb[5]! = 2 from rfl] at hi5
  refine ⟨i0 + 63 * i1 + 2016 * i2 + 30240 * i3 + 241920 * i4 + 725760 * i5, by omega, ?_⟩
  rw [sElt, show (i0 + 63 * i1 + 2016 * i2 + 30240 * i3 + 241920 * i4 + 725760 * i5) % 63 = i0
      by omega,
    show (i0 + 63 * i1 + 2016 * i2 + 30240 * i3 + 241920 * i4 + 725760 * i5) / 63 % 32 = i1
      by omega,
    show (i0 + 63 * i1 + 2016 * i2 + 30240 * i3 + 241920 * i4 + 725760 * i5) / 2016 % 15 = i2
      by omega,
    show (i0 + 63 * i1 + 2016 * i2 + 30240 * i3 + 241920 * i4 + 725760 * i5) / 30240 % 8 = i3
      by omega,
    show (i0 + 63 * i1 + 2016 * i2 + 30240 * i3 + 241920 * i4 + 725760 * i5) / 241920 % 3 = i4
      by omega,
    show (i0 + 63 * i1 + 2016 * i2 + 30240 * i3 + 241920 * i4 + 725760 * i5) / 725760 % 2 = i5
      by omega]
  rw [inv_mul_eq_one] at g6
  rw [g6]
  simp only [mul_inv_cancel_left]

theorem sElt_injOn
    {m n : ℕ} (hm : m < 1451520) (hn : n < 1451520) (h : sElt m = sElt n) :
    m = n := by
  let f : Fin 1451520 → S0 := fun i => ⟨sElt i, sElt_mem_S0 i⟩
  have hf : Function.Surjective f := by
    rintro ⟨s, hs⟩
    obtain ⟨n, hn, rfl⟩ := exists_sElt hs
    exact ⟨⟨n, hn⟩, rfl⟩
  have hb := hf.bijective_of_nat_card_le (by rw [Nat.card_fin, card_S0])
  have := hb.1 (a₁ := ⟨m, hm⟩) (a₂ := ⟨n, hn⟩) (Subtype.ext h)
  exact congrArg Fin.val this

theorem tArrN_get {k i : ℕ} (hk : k < 6) (hi : i < Native.chainOrb[k]!) :
    ((Native.tArrN seedRowsArr)[k]!)[i]! = Native.tRowsN (chainRec k) (chainRows k) i := by
  rw [Native.tArrN, getElem!_pos _ k (by simpa using hk), Array.getElem_map,
    List.getElem_toArray, List.getElem_range, getElem!_pos _ i (by simpa using hi),
    Array.getElem_map, List.getElem_toArray, List.getElem_range]
  rfl

theorem tElt_val
    {k i : ℕ} (hk : k < 6) (hi : i < Native.chainOrb[k]!) :
    (tElt k i).val.val = rowsMatrix 22 ((Native.tArrN seedRowsArr)[k]!)[i]! := by
  rw [tArrN_get hk hi]
  exact (tElt_spec hk i hi).2.2

theorem sElt_val
    (n : ℕ) :
    (sElt n).val.val = rowsMatrix 22 (Native.sRowsN (Native.tArrN seedRowsArr) n) := by
  rw [sElt, Native.sRowsN]
  simp only [val_val_mul, rowsMatrix_mulRows]
  rw [tElt_val (k := 0) (i := n % 63) (by norm_num) (Nat.mod_lt _ (by norm_num)),
    tElt_val (k := 1) (i := n / 63 % 32) (by norm_num) (Nat.mod_lt _ (by norm_num)),
    tElt_val (k := 2) (i := n / 2016 % 15) (by norm_num) (Nat.mod_lt _ (by norm_num)),
    tElt_val (k := 3) (i := n / 30240 % 8) (by norm_num) (Nat.mod_lt _ (by norm_num)),
    tElt_val (k := 4) (i := n / 241920 % 3) (by norm_num) (Nat.mod_lt _ (by norm_num)),
    tElt_val (k := 5) (i := n / 725760 % 2) (by norm_num) (Nat.mod_lt _ (by norm_num))]

end CFSG.Sporadic.Co2Smith
