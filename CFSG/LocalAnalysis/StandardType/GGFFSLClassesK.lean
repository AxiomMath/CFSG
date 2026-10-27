module

public import CFSG.LocalAnalysis.StandardType.GGFFModelDefs
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFWreath

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.GGFF.SLClassesK

open Matrix
open scoped MatrixGroups
open CFSG.RankThree.PartTwo.Sec4.Item434Kit (WreathFacts vecElt conj_vecElt)
open CFSG.RankThree.PartTwo.Sec4.RonanK429F

@[expose] def rotV (u : Fin 3 → ZMod 3) : Fin 3 → ZMod 3 := ![u 2, u 0, u 1]

@[expose] def stepV (j : Fin 3) (u : Fin 3 → ZMod 3) : Fin 3 → ZMod 3 :=
  if u j = 2 then fun i => if j = i then -u i else u i else u

@[expose] def signV (u : Fin 3 → ZMod 3) : Fin 3 → ZMod 3 := stepV 2 (stepV 1 (stepV 0 u))

@[expose] def normV (u : Fin 3 → ZMod 3) : Fin 3 → ZMod 3 :=
  if signV u = ![0, 1, 0] ∨ signV u = ![0, 1, 1] then rotV (rotV (signV u))
  else if signV u = ![0, 0, 1] ∨ signV u = ![1, 0, 1] then rotV (signV u) else signV u

@[expose] def repV (k : ℕ) : Fin 3 → ZMod 3 :=
  if k = 1 then ![1, 0, 0] else if k = 2 then ![1, 1, 0] else ![1, 1, 1]

theorem normV_eq : ∀ v : Fin 3 → ZMod 3, v ≠ 0 → normV v = repV (wt v) := by
  decide +kernel

theorem wt_zero : wt 0 = 0 := by
  simp [wt]

theorem one_le_wt {v : Fin 3 → ZMod 3} (hv : v ≠ 0) : 1 ≤ wt v := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  unfold wt
  exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩

theorem zmod3_eq_one : ∀ e : ZMod 3, e ≠ 0 → ¬e = 2 → e = 1 := by
  decide

section Group

variable {G : Type*} [Group G]

theorem sq_pow_val {x : G} (hx : x ^ 3 = 1) (a : ZMod 3) : (x ^ 2) ^ a.val = x ^ (-a).val := by
  rw [← pow_mul, ZMod.neg_val]
  split_ifs with h
  · rw [h, ZMod.val_zero]
  · have hlt := ZMod.val_lt a
    have hne : a.val ≠ 0 := (ZMod.val_ne_zero a).mpr h
    generalize a.val = k at hlt hne ⊢
    obtain rfl | rfl : k = 1 ∨ k = 2 := by omega
    · rfl
    · change x ^ (1 + 3) = x ^ 1
      rw [pow_add, hx, mul_one]

variable {z s : Fin 3 → G} {t : G}

theorem semiconj_s_self (hss : ∀ j, s j * s j = 1)
    (hS : ∀ j k, s j * z k * s j = if j = k then z k ^ 2 else z k) (k : Fin 3) :
    s k * z k = z k ^ 2 * s k := by
  have h := hS k k
  rw [if_pos rfl] at h
  calc s k * z k = s k * z k * (s k * s k) := by rw [hss, mul_one]
    _ = s k * z k * s k * s k := by simp only [mul_assoc]
    _ = z k ^ 2 * s k := by rw [h]

theorem commute_s (hss : ∀ j, s j * s j = 1)
    (hS : ∀ j k, s j * z k * s j = if j = k then z k ^ 2 else z k) {j k : Fin 3} (hjk : j ≠ k) :
    Commute (s j) (z k) := by
  have h := hS j k
  rw [if_neg hjk] at h
  change s j * z k = z k * s j
  calc s j * z k = s j * z k * (s j * s j) := by rw [hss, mul_one]
    _ = s j * z k * s j * s j := by simp only [mul_assoc]
    _ = z k * s j := by rw [h]

theorem conj_s_vecElt (hz : ∀ i, z i ^ 3 = 1) (hss : ∀ j, s j * s j = 1)
    (hS : ∀ j k, s j * z k * s j = if j = k then z k ^ 2 else z k) (j : Fin 3)
    (v : Fin 3 → ZMod 3) :
    s j * vecElt z v * (s j)⁻¹ = vecElt z (fun i => if j = i then -v i else v i) := by
  have hinv : (s j)⁻¹ = s j := inv_eq_of_mul_eq_one_right (hss j)
  have hc : ∀ x : G, s j * x * (s j)⁻¹ = MulAut.conj (s j) x := fun x => rfl
  have hp : ∀ i, MulAut.conj (s j) (z i ^ (v i).val) =
      z i ^ (if j = i then -v i else v i).val := by
    intro i
    rw [map_pow, ← hc, hinv, hS]
    split_ifs
    · exact sq_pow_val (hz i) (v i)
    · rfl
  rw [hc, vecElt, map_mul, map_mul, hp, hp, hp]
  rfl

theorem isConj_stepV (hz : ∀ i, z i ^ 3 = 1) (hss : ∀ j, s j * s j = 1)
    (hS : ∀ j k, s j * z k * s j = if j = k then z k ^ 2 else z k) (j : Fin 3)
    (u : Fin 3 → ZMod 3) : IsConj (vecElt z u) (vecElt z (stepV j u)) := by
  unfold stepV
  split_ifs
  · exact isConj_iff.mpr ⟨s j, conj_s_vecElt hz hss hS j u⟩
  · exact IsConj.refl _

theorem isConj_rotV (hf : WreathFacts z t) (u : Fin 3 → ZMod 3) :
    IsConj (vecElt z u) (vecElt z (rotV u)) :=
  isConj_iff.mpr ⟨t, conj_vecElt hf u⟩

theorem isConj_normV (hf : WreathFacts z t) (hss : ∀ j, s j * s j = 1)
    (hS : ∀ j k, s j * z k * s j = if j = k then z k ^ 2 else z k) (u : Fin 3 → ZMod 3) :
    IsConj (vecElt z u) (vecElt z (normV u)) := by
  have hsg : IsConj (vecElt z u) (vecElt z (signV u)) :=
    ((isConj_stepV hf.pow_z hss hS 0 u).trans (isConj_stepV hf.pow_z hss hS 1 _)).trans
      (isConj_stepV hf.pow_z hss hS 2 _)
  unfold normV
  split_ifs
  · exact (hsg.trans (isConj_rotV hf _)).trans (isConj_rotV hf _)
  · exact hsg.trans (isConj_rotV hf _)
  · exact hsg

theorem vecElt_repV (k : ℕ) : vecElt z (repV k) =
    if k = 1 then z 0 else if k = 2 then z 0 * z 1 else z 0 * z 1 * z 2 := by
  unfold repV
  split_ifs
  · change z 0 ^ 1 * z 1 ^ 0 * z 2 ^ 0 = z 0
    rw [pow_one, pow_zero, pow_zero, mul_one, mul_one]
  · change z 0 ^ 1 * z 1 ^ 1 * z 2 ^ 0 = z 0 * z 1
    rw [pow_one, pow_one, pow_zero, mul_one]
  · change z 0 ^ 1 * z 1 ^ 1 * z 2 ^ 1 = z 0 * z 1 * z 2
    rw [pow_one, pow_one, pow_one]

theorem monoX_sq (hss : ∀ j, s j * s j = 1) (hcs : ∀ j k, s j * s k = s k * s j)
    (a b c : Fin 3) (ε : Fin 3 → ZMod 3) :
    (if ε 0 = 2 then s a else 1) * (if ε 1 = 2 then s b else 1) * (if ε 2 = 2 then s c else 1) *
      ((if ε 0 = 2 then s a else 1) * (if ε 1 = 2 then s b else 1) *
        (if ε 2 = 2 then s c else 1)) = 1 := by
  have hX2 : ∀ (p : Prop) [Decidable p] (j : Fin 3),
      (if p then s j else 1) ^ 2 = 1 := by
    intro p _ j
    split_ifs
    · rw [sq, hss]
    · rw [one_pow]
  have hXc : ∀ (p q : Prop) [Decidable p] [Decidable q] (j k : Fin 3),
      Commute (if p then s j else 1) (if q then s k else 1) := by
    intro p q _ _ j k
    split_ifs
    · exact hcs j k
    · exact Commute.one_right _
    · exact Commute.one_left _
    · exact Commute.one_left _
  rw [← sq, ((hXc _ _ a c).mul_left (hXc _ _ b c)).mul_pow, (hXc _ _ a b).mul_pow, hX2, hX2, hX2,
    one_mul, one_mul]

theorem mono_semiconj (hss : ∀ j, s j * s j = 1)
    (hS : ∀ j k, s j * z k * s j = if j = k then z k ^ 2 else z k) (a b c : Fin 3)
    (hinj : Function.Injective ![a, b, c]) (ε : Fin 3 → ZMod 3) (hε : ∀ i, ε i ≠ 0)
    (i : Fin 3) :
    (if ε 0 = 2 then s a else 1) * (if ε 1 = 2 then s b else 1) * (if ε 2 = 2 then s c else 1) *
        z (![a, b, c] i) =
      z (![a, b, c] i) ^ (ε i).val *
        ((if ε 0 = 2 then s a else 1) * (if ε 1 = 2 then s b else 1) *
          (if ε 2 = 2 then s c else 1)) := by
  have hcomm : ∀ (m : Fin 3) (k : Fin 3), ![a, b, c] m ≠ k →
      Commute (if ε m = 2 then s (![a, b, c] m) else 1) (z k) := by
    intro m k hmk
    split_ifs
    · exact commute_s hss hS hmk
    · exact Commute.one_left _
  have hself : ∀ m : Fin 3, SemiconjBy (if ε m = 2 then s (![a, b, c] m) else 1)
      (z (![a, b, c] m)) (z (![a, b, c] m) ^ (ε m).val) := by
    intro m
    split_ifs with h2
    · rw [h2]
      exact semiconj_s_self hss hS _
    · rw [zmod3_eq_one _ (hε m) h2]
      change 1 * z _ = z _ ^ 1 * 1
      rw [one_mul, pow_one, mul_one]
  have hne : ∀ m n : Fin 3, m ≠ n → ![a, b, c] m ≠ ![a, b, c] n :=
    fun m n hmn h => hmn (hinj h)
  change SemiconjBy _ _ _
  fin_cases i
  · exact SemiconjBy.mul_left (SemiconjBy.mul_left (hself 0) (hcomm 1 _ (hne 1 0 (by decide))))
      (hcomm 2 _ (hne 2 0 (by decide)))
  · exact SemiconjBy.mul_left
      (SemiconjBy.mul_left ((hcomm 0 _ (hne 0 1 (by decide))).pow_right _) (hself 1))
      (hcomm 2 _ (hne 2 1 (by decide)))
  · exact SemiconjBy.mul_left (SemiconjBy.mul_left ((hcomm 0 _ (hne 0 2 (by decide))).pow_right _)
      ((hcomm 1 _ (hne 1 2 (by decide))).pow_right _)) (hself 2)

end Group

@[expose] def sv6 : Fin 3 → SL(6, ZMod 2) := ![W6.s1, W6.s2, W6.s3]

theorem sv6_sq : ∀ j, sv6 j * sv6 j = 1 := by decide +kernel

theorem sv6_comm : ∀ j k, sv6 j * sv6 k = sv6 k * sv6 j := by decide +kernel

theorem sv6_conj : ∀ j k, sv6 j * W6.T k * sv6 j = if j = k then W6.T k ^ 2 else W6.T k := by
  decide +kernel

theorem conjRep6 (v : Fin 3 → ZMod 3) (hv : v ≠ 0) :
    IsConj (vecElt W6.T v) (vecElt W6.T (repV (wt v))) := by
  have h := isConj_normV W6.wreathFacts sv6_sq sv6_conj v
  rwa [normV_eq v hv] at h

@[expose] def actK6 (f : Fin 3 → Fin 3) (j : Fin 6) : Fin 6 :=
  Fin.ofNat 6 (2 * (f (Fin.ofNat 3 (j.val / 2))).val + j.val % 2)

@[expose] def pK6 (f : Fin 3 → Fin 3) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  Matrix.of fun i j => if i = actK6 f j then 1 else 0

theorem pK6_mul_T : ∀ a b c : Fin 3, Function.Injective ![a, b, c] → ∀ i : Fin 3,
    pK6 ![a, b, c] * ![W6.t1M, W6.t2M, W6.t3M] i =
      ![W6.t1M, W6.t2M, W6.t3M] (![a, b, c] i) * pK6 ![a, b, c] := by
  decide +kernel

theorem pK6_mul_transpose : ∀ a b c : Fin 3, Function.Injective ![a, b, c] →
    pK6 ![a, b, c] * (pK6 ![a, b, c])ᵀ = 1 := by
  decide +kernel

@[expose] def sv7 : Fin 3 → SL(7, ZMod 2) := ![W7.s1, W7.s2, W7.s3]

theorem sv7_sq : ∀ j, sv7 j * sv7 j = 1 := by decide +kernel

theorem sv7_comm : ∀ j k, sv7 j * sv7 k = sv7 k * sv7 j := by decide +kernel

theorem sv7_conj : ∀ j k, sv7 j * W7.T k * sv7 j = if j = k then W7.T k ^ 2 else W7.T k := by
  decide +kernel

theorem conjRep7 (v : Fin 3 → ZMod 3) (hv : v ≠ 0) :
    IsConj (vecElt W7.T v) (vecElt W7.T (repV (wt v))) := by
  have h := isConj_normV W7.wreathFacts sv7_sq sv7_conj v
  rwa [normV_eq v hv] at h

@[expose] def actK7 (f : Fin 3 → Fin 3) (j : Fin 7) : Fin 7 :=
  if j.val = 6 then 6
  else Fin.ofNat 7 (2 * (f (Fin.ofNat 3 (j.val / 2))).val + j.val % 2)

@[expose] def pK7 (f : Fin 3 → Fin 3) : Matrix (Fin 7) (Fin 7) (ZMod 2) :=
  Matrix.of fun i j => if i = actK7 f j then 1 else 0

theorem pK7_mul_T : ∀ a b c : Fin 3, Function.Injective ![a, b, c] → ∀ i : Fin 3,
    pK7 ![a, b, c] * ![W7.t1M, W7.t2M, W7.t3M] i =
      ![W7.t1M, W7.t2M, W7.t3M] (![a, b, c] i) * pK7 ![a, b, c] := by
  decide +kernel

theorem pK7_mul_transpose : ∀ a b c : Fin 3, Function.Injective ![a, b, c] →
    pK7 ![a, b, c] * (pK7 ![a, b, c])ᵀ = 1 := by
  decide +kernel

end CFSG.StandardType.GGFF.SLClassesK

end
