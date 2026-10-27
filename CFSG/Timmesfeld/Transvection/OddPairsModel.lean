module

public import CFSG.Timmesfeld.Transvection.OddModelWeyl
public import CFSG.Timmesfeld.Transvection.OddModelBlock
public import CFSG.Timmesfeld.Transvection.OddModelPairs
import all CFSG.LieType.Universal.Unitary.Roots
import CFSG.Timmesfeld.Transvection.OddModelSU3
import CFSG.Timmesfeld.Transvection.PresSURankOne

public section

namespace CFSG.Timmesfeld.Transvection.Pres

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.Steinberg
open CFSG.LieType.Universal.Symplectic.SpExtras (wt)
open scoped commutatorElement

section Casts

variable (r : ℕ)

@[simp] theorem val_finCastOdd (a : Fin (2 * r / 2)) : (finCastOdd r a).val = a.val := rfl

@[simp] theorem val_finCastOdd_symm (a : Fin ((2 * r + 1) / 2)) :
    ((finCastOdd r).symm a).val = a.val := rfl

@[simp] theorem sCast_inl (a : Fin (2 * r / 2)) :
    sCast r (Sum.inl a) = Sum.inl (finCastOdd r a) := rfl

@[simp] theorem sCast_inr (a : Fin (2 * r / 2)) :
    sCast r (Sum.inr a) = Sum.inr (finCastOdd r a) := rfl

theorem rootCast_single {k : Fin (2 * r / 2)} (hk : k.val + 1 ≠ r) :
    rootCast r (Pi.single k 1) = Pi.single (finCastOdd r k) 1 := by
  funext a
  rw [rootCast, Pi.single_apply, Pi.single_apply]
  by_cases ha : a = finCastOdd r k
  · subst ha
    rw [if_pos (Equiv.symm_apply_apply (finCastOdd r) k), val_finCastOdd, if_neg hk, one_mul,
      if_pos rfl]
  · rw [if_neg ha, if_neg (fun h => ha ((Equiv.symm_apply_eq (finCastOdd r)).mp h)), mul_zero]

theorem rootCast_neg (γ : Fin (2 * r / 2) → ℤ) : rootCast r (-γ) = -rootCast r γ := by
  funext a
  simp only [rootCast, Pi.neg_apply, mul_neg]

end Casts

section Blocks

variable {F : Type} [Field F] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c)

theorem su3Emb_injective {n : ℕ} (hn : ¬Even n) (k : Fin (n / 2)) :
    Function.Injective (su3Emb σ hn k) :=
  CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.suEmbed_injective σ
    (lastIdxOdd_injective' hn k) (lastIdxOdd_rev hn)

theorem map_rankOne_oddEmb (r : ℕ) {k : Fin (2 * r / 2)} (hk : k.val + 1 ≠ r) :
    (CFSG.LieType.CurtisTits.rankOne
        (CFSG.LieType.Universal.Unitary.rootGroup σ hσ (2 * r)) k).map (oddEmb σ r) =
      CFSG.LieType.CurtisTits.rankOne
        (CFSG.LieType.Universal.Unitary.rootGroup σ hσ (2 * r + 1)) (finCastOdd r k) := by
  simp only [CFSG.LieType.CurtisTits.rankOne, Subgroup.map_sup,
    map_rootGroup_oddEmb r hσ, rootCast_neg, rootCast_single r hk]

theorem rootGroup_le_range_su3Emb {n : ℕ} (hn : ¬Even n) {a : Fin (n / 2) ⊕ Fin (n / 2)}
    {γ : Fin (n / 2) → ℤ} (hγ : toStd n γ = wt a) :
    CFSG.LieType.Universal.Unitary.rootGroup σ hσ n γ ≤ (su3Emb σ hn (idx a)).range := by
  rcases a with k | k
  · rw [← map_rootGroup_su3Emb hσ hn k hγ]
    exact Subgroup.map_le_range _ _
  · rw [← map_rootGroup_su3Emb_neg hσ hn k hγ]
    exact Subgroup.map_le_range _ _

private theorem lowIdx_notMem_lastIdxOdd {n : ℕ} (hn : ¬Even n) {i k : Fin (n / 2)}
    (hik : i.val + 2 ≤ k.val) {j : Fin (n / 2)}
    (hj : j.val ≤ i.val + 1) : lowIdx j ∉ Set.range (lastIdxOdd k hn) := by
  have hik' : i.val + 2 ≤ k.val := hik
  have hj' : j.val ≤ i.val + 1 := hj
  have hn' : n = 2 * (n / 2) + 1 := by
    rw [Nat.not_even_iff_odd] at hn
    obtain ⟨t, ht⟩ := hn
    omega
  rintro ⟨s, hs⟩
  fin_cases s
  · change lowIdx k = lowIdx j at hs
    have h := congrArg Fin.val hs
    simp only [lowIdx, Fin.val_mk] at h
    omega
  · change midIdx n hn = lowIdx j at hs
    have h := congrArg Fin.val hs
    simp only [midIdx, lowIdx, Fin.val_mk] at h
    omega
  · change Fin.rev (lowIdx k) = lowIdx j at hs
    have h := congrArg Fin.val hs
    simp only [Fin.val_rev, lowIdx, Fin.val_mk] at h
    omega

theorem rankOne_inf_rankOne_last_eq_bot {n : ℕ} (hn : ¬Even n) {i k : Fin (n / 2)}
    (hk : ¬k.val + 1 < n / 2) (hik : i.val + 2 ≤ k.val) :
    CFSG.LieType.CurtisTits.rankOne (CFSG.LieType.Universal.Unitary.rootGroup σ hσ n) i ⊓
      CFSG.LieType.CurtisTits.rankOne (CFSG.LieType.Universal.Unitary.rootGroup σ hσ n) k = ⊥ := by
  have hi : i.val + 1 < n / 2 := by omega
  refine le_antisymm ?_ bot_le
  intro x hx
  rw [Subgroup.mem_bot]
  obtain ⟨hxi, hxk⟩ := Subgroup.mem_inf.mp hx
  have hblk := isBlkOn_lastIdxOdd hn hk hxk
  have hp := lowIdx_notMem_lastIdxOdd hn hik (j := i) (by omega)
  have hq := lowIdx_notMem_lastIdxOdd hn hik (j := ⟨i.val + 1, hi⟩) (by simp)
  have hinj : Function.Injective ![lowIdx i, lowIdx ⟨i.val + 1, hi⟩] := by
    intro a b h
    fin_cases a <;> fin_cases b
    · rfl
    · change lowIdx i = lowIdx ⟨i.val + 1, hi⟩ at h
      exact absurd h (lowIdx_ne_succ hi)
    · change lowIdx ⟨i.val + 1, hi⟩ = lowIdx i at h
      exact absurd h.symm (lowIdx_ne_succ hi)
    · rfl
  have hb : toBlock (lowIdx i) (lowIdx ⟨i.val + 1, hi⟩) (mat σ n x) = 1 := by
    rw [toBlock_eq_submatrix, ← Matrix.submatrix_one (α := F) _ hinj]
    ext a b
    fin_cases a <;> fin_cases b
    all_goals
      exact hblk _ _ (Or.inl (by first | exact hp | exact hq))
  exact eq_one_of_toBlock_short hi hxi hb


private theorem commute_suElt_suHeis_last {n : ℕ} (hn : ¬Even n) {k : Fin (n / 2)}
    {a b : Fin (n / 2) ⊕ Fin (n / 2)}
    (hab : idx a ≠ idx b) (ha : idx a ≠ k) (hb : idx b ≠ k)
    {c : Fin (n / 2) ⊕ Fin (n / 2)} (hc : idx c = k) (t u v : F) :
    Commute (suElt σ hσ a b t) (suHeis σ hσ hn c u v) := by
  have hca : c ≠ Sum.swap a := by
    intro h
    apply ha
    rw [← hc, h, idx_swap]
  have hcb : c ≠ Sum.swap b := by
    intro h
    apply hb
    rw [← hc, h, idx_swap]
  exact (commutatorElement_eq_one_iff_commute.mp
    (suHeis_comm_suElt hσ hn hab hca hcb u v t)).symm

private theorem commute_rankOne_of_mem_rootGroup_wt {n : ℕ} (hn : ¬Even n)
    {i k : Fin (n / 2)} (hik : i.val + 2 ≤ k.val)
    {c : Fin (n / 2) ⊕ Fin (n / 2)} (hc : idx c = k)
    {γ : Fin (n / 2) → ℤ} (hγ : toStd n γ = wt c) {y : SU σ n}
    (hy : y ∈ CFSG.LieType.Universal.Unitary.rootGroup σ hσ n γ) :
    ∀ x ∈ CFSG.LieType.CurtisTits.rankOne
      (CFSG.LieType.Universal.Unitary.rootGroup σ hσ n) i, Commute x y := by
  have hik' : i.val + 2 ≤ k.val := hik
  have hi : i.val + 1 < n / 2 := by omega
  have hneg : toStd n (-Pi.single i 1) =
      rt (Sum.inl ⟨i.val + 1, hi⟩) (Sum.inr i) := by
    rw [toStd_neg, toStd_single_short hi, rt_inl_inr, rt_inl_inr, neg_sub]
  have hai : i ≠ k := by
    simp only [ne_eq, Fin.ext_iff]
    omega
  have hbi : (⟨i.val + 1, hi⟩ : Fin (n / 2)) ≠ k := by
    simp only [ne_eq, Fin.ext_iff]
    omega
  intro x hx
  refine rankOne_induction (k := i) (C := fun z => Commute z y) hσ hx ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨t, rfl⟩ :=
      (mem_rootGroup_iff_suElt_odd hσ (idx_short hi) (toStd_single_short hi) x).mp hx
    obtain ⟨u, v, _, rfl⟩ := (mem_rootGroup_iff_suHeis hσ hn hγ y).mp hy
    exact commute_suElt_suHeis_last hσ hn (idx_short hi) hai hbi hc t u v
  · intro x hx
    obtain ⟨t, rfl⟩ := (mem_rootGroup_iff_suElt_odd hσ (idx_short' hi) hneg x).mp hx
    obtain ⟨u, v, _, rfl⟩ := (mem_rootGroup_iff_suHeis hσ hn hγ y).mp hy
    exact commute_suElt_suHeis_last hσ hn (idx_short' hi) hbi hai hc t u v
  · exact Commute.one_left y
  · intro x₁ x₂ h₁ h₂
    exact h₁.mul_left h₂

theorem commute_of_mem_rankOne_of_mem_rankOne_last {n : ℕ} (hn : ¬Even n) {i k : Fin (n / 2)}
    (hk : ¬k.val + 1 < n / 2) (hik : i.val + 2 ≤ k.val) {x y : SU σ n}
    (hx : x ∈ CFSG.LieType.CurtisTits.rankOne
      (CFSG.LieType.Universal.Unitary.rootGroup σ hσ n) i)
    (hy : y ∈ CFSG.LieType.CurtisTits.rankOne
      (CFSG.LieType.Universal.Unitary.rootGroup σ hσ n) k) :
    Commute x y := by
  have hk_pos : toStd n (Pi.single k 1) = wt (Sum.inl k) :=
    (toStd_last_odd hk hn).trans (weight_crd (Sum.inl k))
  have hk_neg : toStd n (-Pi.single k 1) = wt (Sum.inr k) :=
    (toStd_neg_last_odd hk hn).trans (weight_crd (Sum.inr k))
  have hcomm : ∀ y ∈ CFSG.LieType.CurtisTits.rankOne
      (CFSG.LieType.Universal.Unitary.rootGroup σ hσ n) k,
      ∀ x ∈ CFSG.LieType.CurtisTits.rankOne
        (CFSG.LieType.Universal.Unitary.rootGroup σ hσ n) i, Commute x y := by
    intro y hy
    refine rankOne_induction (k := k)
      (C := fun z => ∀ x ∈ CFSG.LieType.CurtisTits.rankOne
        (CFSG.LieType.Universal.Unitary.rootGroup σ hσ n) i, Commute x z)
      hσ hy ?_ ?_ ?_ ?_
    · intro y hy
      exact commute_rankOne_of_mem_rootGroup_wt hσ hn hik rfl hk_pos hy
    · intro y hy
      exact commute_rankOne_of_mem_rootGroup_wt hσ hn hik rfl hk_neg hy
    · intro x hx
      exact Commute.one_right x
    · intro y₁ y₂ h₁ h₂ x hx
      exact (h₁ x hx).mul_right (h₂ x hx)
  exact hcomm y hy x hx

end Blocks

section Coordinates

theorem toStd_neg_single_short {m : ℕ} {i : Fin (m / 2)} (hk : i.val + 1 < m / 2) :
    toStd m (-Pi.single i 1) = rt (Sum.inl ⟨i.val + 1, hk⟩) (Sum.inr i) := by
  rw [toStd_neg, toStd_single_short hk, rt_inl_inr, rt_inl_inr, neg_sub]

theorem even_reflection_last_iff {r : ℕ} (hr : 1 ≤ r) (k : Fin ((2 * r + 1) / 2))
    (γ : Fin ((2 * r + 1) / 2) → ℤ) :
    Even (CFSG.LieType.RootSystem.reflection (cartan (2 * r + 1)) k γ (bcLastIdx r hr)) ↔
      Even (γ (bcLastIdx r hr)) := by
  by_cases h : k = bcLastIdx r hr
  · subst h
    have hL : ¬(bcLastIdx r hr).val + 1 < (2 * r + 1) / 2 := by
      simp only [bcLastIdx]
      omega
    rw [CFSG.LieType.RootSystem.reflection_apply_coroot, Pi.sub_apply, Pi.smul_apply,
      Pi.single_eq_same, smul_eq_mul, mul_one,
      coroot_cartan_of_odd (Nat.not_even_two_mul_add_one r) hL γ, Int.even_sub]
    simp [even_two_mul]
  · rw [CFSG.LieType.RootSystem.reflection_apply_of_ne _ (Ne.symm h) γ]

theorem levelPermS_inl_of_val_succ {m : ℕ} {j k : Fin (m / 2)} (hjk : j.val + 1 = k.val) :
    levelPermS j (Sum.inl k) = Sum.inl j := by
  have hj : j.val + 1 < m / 2 := by omega
  have hk : k = ⟨j.val + 1, hj⟩ := Fin.ext (by simp [hjk])
  subst hk
  rw [levelPermS, dite_eq_left hj]
  simp [Equiv.Perm.mul_apply, Equiv.swap_apply_def, Fin.ext_iff]

theorem levelPermS_inr_of_val_succ {m : ℕ} {j k : Fin (m / 2)} (hjk : j.val + 1 = k.val) :
    levelPermS j (Sum.inr k) = Sum.inr j := by
  have hj : j.val + 1 < m / 2 := by omega
  have hk : k = ⟨j.val + 1, hj⟩ := Fin.ext (by simp [hjk])
  subst hk
  rw [levelPermS, dite_eq_left hj]
  simp [Equiv.Perm.mul_apply, Equiv.swap_apply_def, Fin.ext_iff]

theorem idx_levelPermS_of_val_succ {m : ℕ} {j k : Fin (m / 2)} (hjk : j.val + 1 = k.val)
    (a : Fin (m / 2) ⊕ Fin (m / 2)) : idx (levelPermS j a) = Equiv.swap j k (idx a) := by
  have hj : j.val + 1 < m / 2 := by omega
  have hk : k = ⟨j.val + 1, hj⟩ := Fin.ext (by simp [hjk])
  subst hk
  rcases a with i | i <;>
    simp only [levelPermS, dite_eq_left hj, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
      Sum.map_inl, Sum.map_inr, idx_inl, idx_inr]
  · split_ifs <;> simp_all [idx_inl, idx_inr, Fin.ext_iff]
  · split_ifs <;> simp_all [idx_inl, idx_inr, Fin.ext_iff]

theorem levelPermS_of_not_lt_of_idx_ne {m : ℕ} {k : Fin (m / 2)} (hk : ¬k.val + 1 < m / 2)
    {a : Fin (m / 2) ⊕ Fin (m / 2)} (ha : idx a ≠ k) : levelPermS k a = a := by
  rw [levelPermS, dite_eq_right hk]
  rcases a with i | i
  · by_cases hi : i = k
    · subst hi
      exact absurd rfl ha
    · simp [Equiv.swap_apply_def, hi]
  · by_cases hi : i = k
    · subst hi
      exact absurd rfl ha
    · simp [Equiv.swap_apply_def, hi]

theorem levelPermS_of_not_lt_of_idx_eq {m : ℕ} {k : Fin (m / 2)} (hk : ¬k.val + 1 < m / 2)
    {a : Fin (m / 2) ⊕ Fin (m / 2)} (ha : idx a = k) : levelPermS k a = Sum.swap a := by
  rw [levelPermS, dite_eq_right hk]
  rcases a with i | i
  · have hi : i = k := ha
    subst hi
    simp [Equiv.swap_apply_left]
  · have hi : i = k := ha
    subst hi
    simp [Equiv.swap_apply_right]

end Coordinates

section Weyl

variable {F : Type*} [Field F] [CharP F 2] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c)

theorem levelWeyl_one_last_eq {m : ℕ} {k : Fin (m / 2)} (hk : ¬k.val + 1 < m / 2) :
    levelWeyl hσ ⟨1, one_mem_traceZero⟩ k =
      suLong σ (Sum.inl k) 1 * suLong σ (Sum.inr k) 1 * suLong σ (Sum.inl k) 1 := by
  unfold levelWeyl
  rw [dif_neg hk]
  have h := longWeyl_eq (σ := σ) (i := k) one_mem_traceZero
  simpa [inv_one, CharTwo.neg_eq] using h.symm

theorem levelWeyl_one_conj_levelWeyl_one_last {m : ℕ} {j k : Fin (m / 2)}
    (hjk : j.val + 1 = k.val) (hk : ¬k.val + 1 < m / 2) :
    levelWeyl hσ ⟨1, one_mem_traceZero⟩ j * levelWeyl hσ ⟨1, one_mem_traceZero⟩ k *
        (levelWeyl hσ ⟨1, one_mem_traceZero⟩ j)⁻¹ =
      suLong σ (Sum.inl j) 1 * suLong σ (Sum.inr j) 1 * suLong σ (Sum.inl j) 1 := by
  rw [levelWeyl_one_last_eq hσ hk]
  have h1 := levelWeyl_one_conj_suLong hσ j (Sum.inl k) 1
  have h2 := levelWeyl_one_conj_suLong hσ j (Sum.inr k) 1
  rw [levelPermS_inl_of_val_succ hjk] at h1
  rw [levelPermS_inr_of_val_succ hjk] at h2
  calc
    levelWeyl hσ ⟨1, one_mem_traceZero⟩ j *
        (suLong σ (Sum.inl k) 1 * suLong σ (Sum.inr k) 1 * suLong σ (Sum.inl k) 1) *
        (levelWeyl hσ ⟨1, one_mem_traceZero⟩ j)⁻¹ =
      (levelWeyl hσ ⟨1, one_mem_traceZero⟩ j * suLong σ (Sum.inl k) 1 *
          (levelWeyl hσ ⟨1, one_mem_traceZero⟩ j)⁻¹) *
        (levelWeyl hσ ⟨1, one_mem_traceZero⟩ j * suLong σ (Sum.inr k) 1 *
          (levelWeyl hσ ⟨1, one_mem_traceZero⟩ j)⁻¹) *
        (levelWeyl hσ ⟨1, one_mem_traceZero⟩ j * suLong σ (Sum.inl k) 1 *
          (levelWeyl hσ ⟨1, one_mem_traceZero⟩ j)⁻¹) := by group
    _ = suLong σ (Sum.inl j) 1 * suLong σ (Sum.inr j) 1 * suLong σ (Sum.inl j) 1 := by
      rw [h1, h2]

end Weyl

section BC2

theorem bcPrevIdx_ne_bcLastIdx {r : ℕ} (hr : 2 ≤ r) :
    bcPrevIdx r hr ≠ bcLastIdx r (Nat.one_le_of_lt hr) :=
  Fin.ne_of_val_ne (by simp only [bcPrevIdx, bcLastIdx]; omega)

theorem toStd_bc2_neg {r : ℕ} (hr : 2 ≤ r) :
    toStd (2 * r + 1) (-Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) =
        wt (Sum.inr (bcLastIdx r (Nat.one_le_of_lt hr))) ∧
      toStd (2 * r + 1) (-(2 • Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1)) =
        rt (Sum.inr (bcLastIdx r (Nat.one_le_of_lt hr)))
          (Sum.inr (bcLastIdx r (Nat.one_le_of_lt hr))) ∧
      toStd (2 * r + 1)
          (-(Pi.single (bcPrevIdx r hr) 1 + Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1)) =
        wt (Sum.inr (bcPrevIdx r hr)) ∧
      toStd (2 * r + 1) (-(2 • Pi.single (bcPrevIdx r hr) 1 +
          2 • Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1)) =
        rt (Sum.inr (bcPrevIdx r hr)) (Sum.inr (bcPrevIdx r hr)) := by
  have h := toStd_bc2 hr
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [toStd_neg, h.2.1]
    exact (Sp.wt_swap (Sum.inl (bcLastIdx r (Nat.one_le_of_lt hr)))).symm
  · rw [toStd_neg, h.2.2.1]
    exact (rt_swap_swap (Sum.inl (bcLastIdx r (Nat.one_le_of_lt hr)))
      (Sum.inl (bcLastIdx r (Nat.one_le_of_lt hr)))).symm
  · rw [toStd_neg, h.2.2.2.1]
    exact (Sp.wt_swap (Sum.inl (bcPrevIdx r hr))).symm
  · rw [toStd_neg, h.2.2.2.2.2]
    exact (rt_swap_swap (Sum.inl (bcPrevIdx r hr)) (Sum.inl (bcPrevIdx r hr))).symm

private theorem eq_signed_weight_of_toStd_eq_wt {r : ℕ} (hr : 2 ≤ r)
    {a : Fin ((2 * r + 1) / 2) ⊕ Fin ((2 * r + 1) / 2)}
    (ha : idx a = bcLastIdx r (Nat.one_le_of_lt hr) ∨ idx a = bcPrevIdx r hr)
    {γ : Fin ((2 * r + 1) / 2) → ℤ} (hγ : toStd (2 * r + 1) γ = wt a) :
    (a = Sum.inl (bcLastIdx r (Nat.one_le_of_lt hr)) ∧
        γ = Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) ∨
      (a = Sum.inr (bcLastIdx r (Nat.one_le_of_lt hr)) ∧
        γ = -Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) ∨
      (a = Sum.inl (bcPrevIdx r hr) ∧
        γ = Pi.single (bcPrevIdx r hr) 1 +
          Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) ∨
      (a = Sum.inr (bcPrevIdx r hr) ∧
        γ = -(Pi.single (bcPrevIdx r hr) 1 +
          Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1)) := by
  have hpos := toStd_bc2 hr
  have hneg := toStd_bc2_neg hr
  rcases a with k | k
  · have hk : k = bcLastIdx r (Nat.one_le_of_lt hr) ∨ k = bcPrevIdx r hr := by
      simpa [idx] using ha
    rcases hk with rfl | rfl
    · exact Or.inl ⟨rfl, toStd_inj' (hγ.trans hpos.2.1.symm)⟩
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, toStd_inj' (hγ.trans hpos.2.2.2.1.symm)⟩))
  · have hk : k = bcLastIdx r (Nat.one_le_of_lt hr) ∨ k = bcPrevIdx r hr := by
      simpa [idx] using ha
    rcases hk with rfl | rfl
    · exact Or.inr (Or.inl ⟨rfl, toStd_inj' (hγ.trans hneg.1.symm)⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, toStd_inj' (hγ.trans hneg.2.2.1.symm)⟩))

theorem not_even_last_of_toStd_eq_wt {r : ℕ} (hr : 2 ≤ r)
    {a : Fin ((2 * r + 1) / 2) ⊕ Fin ((2 * r + 1) / 2)}
    (ha : idx a = bcLastIdx r (Nat.one_le_of_lt hr) ∨ idx a = bcPrevIdx r hr)
    {γ : Fin ((2 * r + 1) / 2) → ℤ} (hγ : toStd (2 * r + 1) γ = wt a) :
    ¬Even (γ (bcLastIdx r (Nat.one_le_of_lt hr))) := by
  have hPL := bcPrevIdx_ne_bcLastIdx hr
  rcases eq_signed_weight_of_toStd_eq_wt hr ha hγ with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [Pi.single_eq_same]
    exact Int.not_even_one
  · rw [Pi.neg_apply, Pi.single_eq_same]
    exact fun h => Int.not_even_one (even_neg.mp h)
  · rw [Pi.add_apply, Pi.single_eq_of_ne hPL.symm, Pi.single_eq_same, zero_add]
    exact Int.not_even_one
  · rw [Pi.neg_apply, Pi.add_apply, Pi.single_eq_of_ne hPL.symm, Pi.single_eq_same, zero_add]
    exact fun h => Int.not_even_one (even_neg.mp h)

theorem prev_eq_zero_iff_of_toStd_eq_wt {r : ℕ} (hr : 2 ≤ r)
    {a : Fin ((2 * r + 1) / 2) ⊕ Fin ((2 * r + 1) / 2)}
    (ha : idx a = bcLastIdx r (Nat.one_le_of_lt hr) ∨ idx a = bcPrevIdx r hr)
    {γ : Fin ((2 * r + 1) / 2) → ℤ} (hγ : toStd (2 * r + 1) γ = wt a) :
    γ (bcPrevIdx r hr) = 0 ↔ idx a = bcLastIdx r (Nat.one_le_of_lt hr) := by
  have hPL := bcPrevIdx_ne_bcLastIdx hr
  rcases eq_signed_weight_of_toStd_eq_wt hr ha hγ with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp [Pi.single_apply, hPL]
  · simp [Pi.single_apply, hPL]
  · simp [Pi.add_apply, Pi.single_apply, hPL]
  · simp [Pi.add_apply, Pi.single_apply, hPL]

end BC2

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
  (hF : Nat.card F = (p ^ f) ^ 2)

theorem exists_toStd_eq_wt_of_mem_pairRoots_bc2 {r : ℕ} (hr : 2 ≤ r)
    {γ : Fin ((2 * r + 1) / 2) → ℤ}
    (hγ : γ ∈ pairRoots (rootDatum hF (2 * r + 1)) (bcPrevIdx r hr)
      (bcLastIdx r (Nat.one_le_of_lt hr)))
    (hodd : ¬Even (γ (bcLastIdx r (Nat.one_le_of_lt hr)))) :
    ∃ a : Fin ((2 * r + 1) / 2) ⊕ Fin ((2 * r + 1) / 2),
      (idx a = bcLastIdx r (Nat.one_le_of_lt hr) ∨ idx a = bcPrevIdx r hr) ∧
        toStd (2 * r + 1) γ = wt a := by
  have hPL := bcPrevIdx_ne_bcLastIdx hr
  have hpos := toStd_bc2 hr
  have hneg := toStd_bc2_neg hr
  obtain ⟨x, y, hxy, hγeq⟩ := (mem_pairRoots_bc2 hF hr).1 hγ
  have hy : ¬Even y := by
    have h : γ (bcLastIdx r (Nat.one_le_of_lt hr)) = y := by
      rw [hγeq]
      simp [Pi.add_apply, Pi.smul_apply, Pi.single_apply, hPL.symm]
    rwa [h] at hodd
  simp only [bc2Coeffs, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hxy
  rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩
  · exact absurd Even.zero hy
  · refine ⟨Sum.inl (bcLastIdx r (Nat.one_le_of_lt hr)), Or.inl rfl, ?_⟩
    rw [hγeq]
    simpa using hpos.2.1
  · exact absurd even_two hy
  · refine ⟨Sum.inl (bcPrevIdx r hr), Or.inr rfl, ?_⟩
    rw [hγeq]
    simpa using hpos.2.2.2.1
  · exact absurd even_two hy
  · exact absurd even_two hy
  · exact absurd Even.zero hy
  · refine ⟨Sum.inr (bcLastIdx r (Nat.one_le_of_lt hr)), Or.inl rfl, ?_⟩
    rw [hγeq]
    simpa using hneg.1
  · exact absurd (even_neg.mpr even_two) hy
  · refine ⟨Sum.inr (bcPrevIdx r hr), Or.inr rfl, ?_⟩
    rw [hγeq]
    simpa [neg_one_smul, neg_add, add_comm] using hneg.2.2.1
  · exact absurd (even_neg.mpr even_two) hy
  · exact absurd (even_neg.mpr even_two) hy

theorem eq_of_mem_pairRoots_last {r : ℕ} (hr : 2 ≤ r) {γ : Fin ((2 * r + 1) / 2) → ℤ}
    (hγ : γ ∈ pairRoots (rootDatum hF (2 * r + 1)) (bcLastIdx r (Nat.one_le_of_lt hr))
      (bcLastIdx r (Nat.one_le_of_lt hr))) :
    γ = Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1 ∨
      γ = -Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1 ∨
      γ = 2 • Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1 ∨
      γ = -(2 • Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) := by
  have hPL := bcPrevIdx_ne_bcLastIdx hr
  have hpair : γ ∈ pairRoots (rootDatum hF (2 * r + 1)) (bcPrevIdx r hr)
      (bcLastIdx r (Nat.one_le_of_lt hr)) :=
    ⟨hγ.1, fun k _ hk => hγ.2 k hk hk⟩
  obtain ⟨x, y, hxy, hγeq⟩ := (mem_pairRoots_bc2 hF hr).1 hpair
  have hx : x = 0 := by
    have h : γ (bcPrevIdx r hr) = x := by
      rw [hγeq]
      simp [Pi.add_apply, Pi.smul_apply, Pi.single_apply, hPL]
    have h0 : γ (bcPrevIdx r hr) = 0 := hγ.2 _ hPL hPL
    exact h.symm.trans h0
  simp only [bc2Coeffs, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hxy
  rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩
  · omega
  · left
    rw [hγeq]
    simp
  · right; right; left
    rw [hγeq]
    simp [two_zsmul]
  · omega
  · omega
  · omega
  · omega
  · right; left
    rw [hγeq]
    simp [neg_one_smul]
  · right; right; right
    rw [hγeq]
    simp [neg_one_smul, two_zsmul]
  · omega
  · omega
  · omega

theorem eq_single_or_mem_pairRoots_last {r : ℕ} (hr : 2 ≤ r) {i : Fin ((2 * r + 1) / 2)}
    (hi : i.val + 3 ≤ r) {γ : Fin ((2 * r + 1) / 2) → ℤ}
    (hγ : γ ∈ pairRoots (rootDatum hF (2 * r + 1)) i (bcLastIdx r (Nat.one_le_of_lt hr))) :
    (γ = Pi.single i 1 ∨ γ = -Pi.single i 1) ∨
      γ ∈ pairRoots (rootDatum hF (2 * r + 1)) (bcLastIdx r (Nat.one_le_of_lt hr))
        (bcLastIdx r (Nat.one_le_of_lt hr)) := by
  obtain ⟨x, y, hxy, hγeq⟩ := (mem_pairRoots_a1bc1 hF hr hi).1 hγ
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hxy
  rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩
  · left; left
    rw [hγeq]
    simp
  · left; right
    rw [hγeq]
    simp [neg_one_smul]
  · right
    refine ⟨hγ.1, ?_⟩
    change ∀ k : Fin ((2 * r + 1) / 2), k ≠ bcLastIdx r (Nat.one_le_of_lt hr) →
      k ≠ bcLastIdx r (Nat.one_le_of_lt hr) → γ k = 0
    intro k hk _
    rw [hγeq]
    simp [Pi.add_apply, Pi.smul_apply, Pi.single_apply, hk, smul_zero, zero_add]
  · right
    refine ⟨hγ.1, ?_⟩
    change ∀ k : Fin ((2 * r + 1) / 2), k ≠ bcLastIdx r (Nat.one_le_of_lt hr) →
      k ≠ bcLastIdx r (Nat.one_le_of_lt hr) → γ k = 0
    intro k hk _
    rw [hγeq]
    simp [Pi.add_apply, Pi.smul_apply, Pi.single_apply, hk, smul_zero, zero_add]
  · right
    refine ⟨hγ.1, ?_⟩
    change ∀ k : Fin ((2 * r + 1) / 2), k ≠ bcLastIdx r (Nat.one_le_of_lt hr) →
      k ≠ bcLastIdx r (Nat.one_le_of_lt hr) → γ k = 0
    intro k hk _
    rw [hγeq]
    simp [Pi.add_apply, Pi.smul_apply, Pi.single_apply, hk, smul_zero, zero_add]
  · right
    refine ⟨hγ.1, ?_⟩
    change ∀ k : Fin ((2 * r + 1) / 2), k ≠ bcLastIdx r (Nat.one_le_of_lt hr) →
      k ≠ bcLastIdx r (Nat.one_le_of_lt hr) → γ k = 0
    intro k hk _
    rw [hγeq]
    simp [Pi.add_apply, Pi.smul_apply, Pi.single_apply, hk, smul_zero, zero_add]

end CFSG.Timmesfeld.Transvection.Pres
