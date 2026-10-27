module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.AutBigKit
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.RankThree.PartTwo.Sec21.Item21LateProofOrders

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSpor)

private def k330cM23Gen₁ : Equiv.Perm (Fin 23) :=
  List.formPerm [0, 1] * List.formPerm [2, 3] * List.formPerm [6, 7] * List.formPerm [8, 9] *
  List.formPerm [12, 13] * List.formPerm [14, 15] * List.formPerm [18, 19] *
  List.formPerm [20, 21]

private def k330cM23Gen₂ : Equiv.Perm (Fin 23) :=
  List.formPerm [0, 15, 10, 2] * List.formPerm [1, 8, 20, 11] * List.formPerm [3, 4, 7, 22] *
  List.formPerm [5, 21, 13, 17] * List.formPerm [12, 19] * List.formPerm [14, 16]

private def k330cM23Letter (l : ℤ) : Equiv.Perm (Fin 23) :=
  if l = 1 then k330cM23Gen₁ else if l = 2 then k330cM23Gen₂
  else if l = -1 then k330cM23Gen₁⁻¹ else k330cM23Gen₂⁻¹

private def k330cM23Word (w : List ℤ) : Equiv.Perm (Fin 23) :=
  w.foldr (fun l acc => acc * k330cM23Letter l) 1

private theorem k330cMemClosurePair {M : Type*} [Group M] {a b : M} (ha : a ^ 3 = 1)
    (hb : b ^ 3 = 1) (hab : a * b = b * a) (x : M) :
    x ∈ Subgroup.closure ({a, b} : Set M) ↔ ∃ i j, i < 3 ∧ j < 3 ∧ x = a ^ i * b ^ j := by
  have hc : Commute a b := hab
  have hmod : ∀ (c : M), c ^ 3 = 1 → ∀ n : ℕ, c ^ n = c ^ (n % 3) := by
    intro c hc3 n
    conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, hc3, one_pow, one_mul]
  constructor
  · intro hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact ⟨1, 0, by norm_num, by norm_num, by simp⟩
      · exact ⟨0, 1, by norm_num, by norm_num, by simp⟩
    | one => exact ⟨0, 0, by norm_num, by norm_num, by simp⟩
    | mul x y _ _ hx hy =>
      obtain ⟨i, j, hi, hj, rfl⟩ := hx
      obtain ⟨i', j', hi', hj', rfl⟩ := hy
      refine ⟨(i + i') % 3, (j + j') % 3, Nat.mod_lt _ (by norm_num),
        Nat.mod_lt _ (by norm_num), ?_⟩
      rw [← hmod a ha, ← hmod b hb, pow_add, pow_add]
      have h1 : b ^ j * a ^ i' = a ^ i' * b ^ j := (hc.pow_pow i' j).symm.eq
      calc a ^ i * b ^ j * (a ^ i' * b ^ j') = a ^ i * (b ^ j * a ^ i') * b ^ j' := by group
        _ = a ^ i * (a ^ i' * b ^ j) * b ^ j' := by rw [h1]
        _ = a ^ i * a ^ i' * (b ^ j * b ^ j') := by group
    | inv x _ hx =>
      obtain ⟨i, j, hi, hj, rfl⟩ := hx
      refine ⟨(3 - i) % 3, (3 - j) % 3, Nat.mod_lt _ (by norm_num),
        Nat.mod_lt _ (by norm_num), ?_⟩
      rw [← hmod a ha, ← hmod b hb]
      have hai : (a ^ i)⁻¹ = a ^ (3 - i) := by
        rw [inv_eq_iff_mul_eq_one, ← pow_add, Nat.add_sub_cancel' hi.le, ha]
      have hbj : (b ^ j)⁻¹ = b ^ (3 - j) := by
        rw [inv_eq_iff_mul_eq_one, ← pow_add, Nat.add_sub_cancel' hj.le, hb]
      rw [mul_inv_rev, hai, hbj]
      exact (hc.pow_pow (3 - i) (3 - j)).symm.eq
  · rintro ⟨i, j, -, -, rfl⟩
    exact mul_mem (pow_mem (subset_closure (by simp)) i)
      (pow_mem (subset_closure (by simp)) j)

private theorem k330cM23Gen₁_mem :
    k330cM23Gen₁ ∈ CFSG.Blueprint.NativeSporadic.M23 := by
  rw [CFSG.Blueprint.NativeSporadic.M23]
  exact Subgroup.subset_closure (by simp [k330cM23Gen₁])

private theorem k330cM23Gen₂_mem :
    k330cM23Gen₂ ∈ CFSG.Blueprint.NativeSporadic.M23 := by
  rw [CFSG.Blueprint.NativeSporadic.M23]
  exact Subgroup.subset_closure (by simp [k330cM23Gen₂])

private theorem k330cM23Letter_mem (l : ℤ) :
    k330cM23Letter l ∈ CFSG.Blueprint.NativeSporadic.M23 := by
  unfold k330cM23Letter
  split_ifs
  · exact k330cM23Gen₁_mem
  · exact k330cM23Gen₂_mem
  · exact Subgroup.inv_mem _ k330cM23Gen₁_mem
  · exact Subgroup.inv_mem _ k330cM23Gen₂_mem

private theorem k330cM23Word_mem (w : List ℤ) :
    k330cM23Word w ∈ CFSG.Blueprint.NativeSporadic.M23 := by
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons l ls ih =>
    have ih' : List.foldr (fun l acc => acc * k330cM23Letter l) 1 ls ∈
        CFSG.Blueprint.NativeSporadic.M23 := ih
    rw [k330cM23Word, List.foldr_cons]
    exact Subgroup.mul_mem _ ih' (k330cM23Letter_mem l)

private def k330cM23Ag : ↥CFSG.Blueprint.NativeSporadic.M23 :=
  ⟨k330cM23Word [2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 2, 1, -2],
    k330cM23Word_mem [2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 2, 1, -2]⟩

private def k330cM23Bg : ↥CFSG.Blueprint.NativeSporadic.M23 :=
  ⟨k330cM23Word [1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2],
    k330cM23Word_mem [1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2]⟩

private def k330cM23Ng : ↥CFSG.Blueprint.NativeSporadic.M23 :=
  ⟨k330cM23Word [-2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, -2, 1, -2, 1, 2, 2, 1, 2],
    k330cM23Word_mem [-2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, -2, 1, -2, 1, 2, 2, 1, 2]⟩

private def k330cM23X : Subgroup ↥CFSG.Blueprint.NativeSporadic.M23 :=
  Subgroup.closure ({k330cM23Ag, k330cM23Bg} : Set ↥CFSG.Blueprint.NativeSporadic.M23)

private theorem k330cFactorThree : (2 ^ 7 * 79695).factorization 3 = 2 := by
  have hn : 2 ^ 7 * 79695 ≠ 0 := by norm_num
  have hp : Nat.Prime 3 := by norm_num
  have hle : 2 ≤ (2 ^ 7 * 79695).factorization 3 :=
    (hp.pow_dvd_iff_le_factorization hn).mp (by norm_num)
  have hlt : (2 ^ 7 * 79695).factorization 3 < 3 := by
    rw [← not_le, ← hp.pow_dvd_iff_le_factorization hn]
    norm_num
  omega

private lemma k330cM23Ag_cube : k330cM23Ag ^ 3 = 1 := by
  decide +kernel

private lemma k330cM23Bg_cube : k330cM23Bg ^ 3 = 1 := by
  decide +kernel

private lemma k330cM23_comm :
    k330cM23Ag * k330cM23Bg = k330cM23Bg * k330cM23Ag := by
  decide +kernel

private lemma k330cM23_conj_Ag :
    k330cM23Ng * k330cM23Ag * k330cM23Ng⁻¹ = k330cM23Bg ^ 2 := by
  decide +kernel

private lemma k330cM23_conj_Bg :
    k330cM23Ng * k330cM23Bg * k330cM23Ng⁻¹ = k330cM23Ag ^ 2 * k330cM23Bg := by
  decide +kernel

private lemma k330cM23_injective :
    Function.Injective (fun p : Fin 3 × Fin 3 =>
      k330cM23Ag ^ (p.1 : ℕ) * k330cM23Bg ^ (p.2 : ℕ)) := by
  decide +kernel

private lemma k330cM23Ng_moves_01 :
    k330cM23Ng * (k330cM23Ag ^ 0 * k330cM23Bg ^ 1) * k330cM23Ng⁻¹ ≠
      k330cM23Ag ^ 0 * k330cM23Bg ^ 1 ∧
    k330cM23Ng * (k330cM23Ag ^ 0 * k330cM23Bg ^ 1) * k330cM23Ng⁻¹ ≠
      (k330cM23Ag ^ 0 * k330cM23Bg ^ 1)⁻¹ := by
  decide +kernel

private lemma k330cM23Ng_moves_02 :
    k330cM23Ng * (k330cM23Ag ^ 0 * k330cM23Bg ^ 2) * k330cM23Ng⁻¹ ≠
      k330cM23Ag ^ 0 * k330cM23Bg ^ 2 ∧
    k330cM23Ng * (k330cM23Ag ^ 0 * k330cM23Bg ^ 2) * k330cM23Ng⁻¹ ≠
      (k330cM23Ag ^ 0 * k330cM23Bg ^ 2)⁻¹ := by
  decide +kernel

private lemma k330cM23Ng_moves_10 :
    k330cM23Ng * (k330cM23Ag ^ 1 * k330cM23Bg ^ 0) * k330cM23Ng⁻¹ ≠
      k330cM23Ag ^ 1 * k330cM23Bg ^ 0 ∧
    k330cM23Ng * (k330cM23Ag ^ 1 * k330cM23Bg ^ 0) * k330cM23Ng⁻¹ ≠
      (k330cM23Ag ^ 1 * k330cM23Bg ^ 0)⁻¹ := by
  decide +kernel

private lemma k330cM23Ng_moves_11 :
    k330cM23Ng * (k330cM23Ag ^ 1 * k330cM23Bg ^ 1) * k330cM23Ng⁻¹ ≠
      k330cM23Ag ^ 1 * k330cM23Bg ^ 1 ∧
    k330cM23Ng * (k330cM23Ag ^ 1 * k330cM23Bg ^ 1) * k330cM23Ng⁻¹ ≠
      (k330cM23Ag ^ 1 * k330cM23Bg ^ 1)⁻¹ := by
  decide +kernel

private lemma k330cM23Ng_moves_12 :
    k330cM23Ng * (k330cM23Ag ^ 1 * k330cM23Bg ^ 2) * k330cM23Ng⁻¹ ≠
      k330cM23Ag ^ 1 * k330cM23Bg ^ 2 ∧
    k330cM23Ng * (k330cM23Ag ^ 1 * k330cM23Bg ^ 2) * k330cM23Ng⁻¹ ≠
      (k330cM23Ag ^ 1 * k330cM23Bg ^ 2)⁻¹ := by
  decide +kernel

private lemma k330cM23Ng_moves_20 :
    k330cM23Ng * (k330cM23Ag ^ 2 * k330cM23Bg ^ 0) * k330cM23Ng⁻¹ ≠
      k330cM23Ag ^ 2 * k330cM23Bg ^ 0 ∧
    k330cM23Ng * (k330cM23Ag ^ 2 * k330cM23Bg ^ 0) * k330cM23Ng⁻¹ ≠
      (k330cM23Ag ^ 2 * k330cM23Bg ^ 0)⁻¹ := by
  decide +kernel

private lemma k330cM23Ng_moves_21 :
    k330cM23Ng * (k330cM23Ag ^ 2 * k330cM23Bg ^ 1) * k330cM23Ng⁻¹ ≠
      k330cM23Ag ^ 2 * k330cM23Bg ^ 1 ∧
    k330cM23Ng * (k330cM23Ag ^ 2 * k330cM23Bg ^ 1) * k330cM23Ng⁻¹ ≠
      (k330cM23Ag ^ 2 * k330cM23Bg ^ 1)⁻¹ := by
  decide +kernel

private lemma k330cM23Ng_moves_22 :
    k330cM23Ng * (k330cM23Ag ^ 2 * k330cM23Bg ^ 2) * k330cM23Ng⁻¹ ≠
      k330cM23Ag ^ 2 * k330cM23Bg ^ 2 ∧
    k330cM23Ng * (k330cM23Ag ^ 2 * k330cM23Bg ^ 2) * k330cM23Ng⁻¹ ≠
      (k330cM23Ag ^ 2 * k330cM23Bg ^ 2)⁻¹ := by
  decide +kernel

private lemma k330cM23Ng2_moves_01 :
    k330cM23Ng ^ 2 * (k330cM23Ag ^ 0 * k330cM23Bg ^ 1) * (k330cM23Ng ^ 2)⁻¹ ≠
      k330cM23Ag ^ 0 * k330cM23Bg ^ 1 ∧
    k330cM23Ng ^ 2 * (k330cM23Ag ^ 0 * k330cM23Bg ^ 1) * (k330cM23Ng ^ 2)⁻¹ ≠
      (k330cM23Ag ^ 0 * k330cM23Bg ^ 1)⁻¹ := by
  decide +kernel

private lemma k330cM23Ng2_moves_02 :
    k330cM23Ng ^ 2 * (k330cM23Ag ^ 0 * k330cM23Bg ^ 2) * (k330cM23Ng ^ 2)⁻¹ ≠
      k330cM23Ag ^ 0 * k330cM23Bg ^ 2 ∧
    k330cM23Ng ^ 2 * (k330cM23Ag ^ 0 * k330cM23Bg ^ 2) * (k330cM23Ng ^ 2)⁻¹ ≠
      (k330cM23Ag ^ 0 * k330cM23Bg ^ 2)⁻¹ := by
  decide +kernel

private lemma k330cM23Ng2_moves_10 :
    k330cM23Ng ^ 2 * (k330cM23Ag ^ 1 * k330cM23Bg ^ 0) * (k330cM23Ng ^ 2)⁻¹ ≠
      k330cM23Ag ^ 1 * k330cM23Bg ^ 0 ∧
    k330cM23Ng ^ 2 * (k330cM23Ag ^ 1 * k330cM23Bg ^ 0) * (k330cM23Ng ^ 2)⁻¹ ≠
      (k330cM23Ag ^ 1 * k330cM23Bg ^ 0)⁻¹ := by
  decide +kernel

private lemma k330cM23Ng2_moves_11 :
    k330cM23Ng ^ 2 * (k330cM23Ag ^ 1 * k330cM23Bg ^ 1) * (k330cM23Ng ^ 2)⁻¹ ≠
      k330cM23Ag ^ 1 * k330cM23Bg ^ 1 ∧
    k330cM23Ng ^ 2 * (k330cM23Ag ^ 1 * k330cM23Bg ^ 1) * (k330cM23Ng ^ 2)⁻¹ ≠
      (k330cM23Ag ^ 1 * k330cM23Bg ^ 1)⁻¹ := by
  decide +kernel

private lemma k330cM23Ng2_moves_12 :
    k330cM23Ng ^ 2 * (k330cM23Ag ^ 1 * k330cM23Bg ^ 2) * (k330cM23Ng ^ 2)⁻¹ ≠
      k330cM23Ag ^ 1 * k330cM23Bg ^ 2 ∧
    k330cM23Ng ^ 2 * (k330cM23Ag ^ 1 * k330cM23Bg ^ 2) * (k330cM23Ng ^ 2)⁻¹ ≠
      (k330cM23Ag ^ 1 * k330cM23Bg ^ 2)⁻¹ := by
  decide +kernel

private lemma k330cM23Ng2_moves_20 :
    k330cM23Ng ^ 2 * (k330cM23Ag ^ 2 * k330cM23Bg ^ 0) * (k330cM23Ng ^ 2)⁻¹ ≠
      k330cM23Ag ^ 2 * k330cM23Bg ^ 0 ∧
    k330cM23Ng ^ 2 * (k330cM23Ag ^ 2 * k330cM23Bg ^ 0) * (k330cM23Ng ^ 2)⁻¹ ≠
      (k330cM23Ag ^ 2 * k330cM23Bg ^ 0)⁻¹ := by
  decide +kernel

private lemma k330cM23Ng2_moves_21 :
    k330cM23Ng ^ 2 * (k330cM23Ag ^ 2 * k330cM23Bg ^ 1) * (k330cM23Ng ^ 2)⁻¹ ≠
      k330cM23Ag ^ 2 * k330cM23Bg ^ 1 ∧
    k330cM23Ng ^ 2 * (k330cM23Ag ^ 2 * k330cM23Bg ^ 1) * (k330cM23Ng ^ 2)⁻¹ ≠
      (k330cM23Ag ^ 2 * k330cM23Bg ^ 1)⁻¹ := by
  decide +kernel

private lemma k330cM23Ng2_moves_22 :
    k330cM23Ng ^ 2 * (k330cM23Ag ^ 2 * k330cM23Bg ^ 2) * (k330cM23Ng ^ 2)⁻¹ ≠
      k330cM23Ag ^ 2 * k330cM23Bg ^ 2 ∧
    k330cM23Ng ^ 2 * (k330cM23Ag ^ 2 * k330cM23Bg ^ 2) * (k330cM23Ng ^ 2)⁻¹ ≠
      (k330cM23Ag ^ 2 * k330cM23Bg ^ 2)⁻¹ := by
  decide +kernel

theorem automizerBig_M23 {J : Type} [Group J] [Finite J]
    (e : IsSpor J .M23) : AutomizerBig J := by
  obtain ⟨e⟩ := e
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .M23) := by
    dsimp [CFSG.Blueprint.NativeSporadic.Carrier]
    infer_instance
  refine automizerBig_of_mulEquiv e ?_
  change AutomizerBig ↥CFSG.Blueprint.NativeSporadic.M23
  have hA3 : k330cM23Ag ^ 3 = 1 := k330cM23Ag_cube
  have hB3 : k330cM23Bg ^ 3 = 1 := k330cM23Bg_cube
  have hAB : k330cM23Ag * k330cM23Bg = k330cM23Bg * k330cM23Ag := k330cM23_comm
  have h9 : Nat.card k330cM23X = 9 := by
    have hinj := k330cM23_injective
    let f : Fin 3 × Fin 3 → ↥k330cM23X := fun p =>
      ⟨k330cM23Ag ^ (p.1 : ℕ) * k330cM23Bg ^ (p.2 : ℕ),
        Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
          (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)⟩
    have hf_inj : Function.Injective f := by
      intro p q hpq
      have h : k330cM23Ag ^ (p.1 : ℕ) * k330cM23Bg ^ (p.2 : ℕ) =
               k330cM23Ag ^ (q.1 : ℕ) * k330cM23Bg ^ (q.2 : ℕ) :=
        Subtype.ext_iff.mp hpq
      exact hinj h
    have hf_surj : Function.Surjective f := by
      intro z
      obtain ⟨i, j, hi, hj, hz⟩ := (k330cMemClosurePair hA3 hB3 hAB z.val).mp z.2
      refine ⟨(⟨i, hi⟩, ⟨j, hj⟩), ?_⟩
      apply Subtype.ext
      show k330cM23Ag ^ i * k330cM23Bg ^ j = z.val
      exact hz.symm
    have e9 : (Fin 3 × Fin 3) ≃ ↥k330cM23X := Equiv.ofBijective f ⟨hf_inj, hf_surj⟩
    have hcard : Nat.card ↥k330cM23X = Nat.card (Fin 3 × Fin 3) := Nat.card_congr e9.symm
    rw [hcard]
    simp [Nat.card_prod]
  have hE : IsElemAbelian 3 k330cM23X := by
    refine ⟨?_, ?_⟩
    · refine Subgroup.isMulCommutative_closure
        (k := ({k330cM23Ag, k330cM23Bg} : Set ↥CFSG.Blueprint.NativeSporadic.M23)) ?_
      rintro x hx y hy hxy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact Commute.refl _
      · exact hAB
      · exact hAB.symm
      · exact Commute.refl _
    · intro x hx
      obtain ⟨i, j, hi, hj, hxeq⟩ := (k330cMemClosurePair hA3 hB3 hAB x).mp hx
      rw [hxeq]
      have hc : Commute (k330cM23Ag ^ i) (k330cM23Bg ^ j) :=
        (show Commute k330cM23Ag k330cM23Bg from hAB).pow_pow i j
      rw [hc.mul_pow]
      have hAi : (k330cM23Ag ^ i) ^ 3 = 1 := by
        rw [← pow_mul, Nat.mul_comm i 3, pow_mul, hA3, one_pow]
      have hBj : (k330cM23Bg ^ j) ^ 3 = 1 := by
        rw [← pow_mul, Nat.mul_comm j 3, pow_mul, hB3, one_pow]
      rw [hAi, hBj, one_mul]
  have hS : IsSylowOf 3 k330cM23X ⊤ := by
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    refine CFSG.ABGLocalTools.isSylowOf_of_card le_top ?_
    rw [h9, Subgroup.card_top, CFSG.RankThree.PartTwo.Sec21.Item21LateProof.card_M23_eq,
      k330cFactorThree]
    norm_num
  have hn : k330cM23Ng ∈ normalizer (k330cM23X : Set ↥CFSG.Blueprint.NativeSporadic.M23) := by
    have hmap_le : k330cM23X.map (MulAut.conj k330cM23Ng).toMonoidHom ≤ k330cM23X := by
      rw [show k330cM23X = Subgroup.closure ({k330cM23Ag, k330cM23Bg} :
            Set ↥CFSG.Blueprint.NativeSporadic.M23) from rfl, MonoidHom.map_closure]
      rw [Subgroup.closure_le]
      rintro _ ⟨y, hy, rfl⟩
      rcases hy with rfl | rfl
      · change k330cM23Ng * k330cM23Ag * k330cM23Ng⁻¹ ∈ k330cM23X
        rw [k330cM23_conj_Ag]
        exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) 2
      · change k330cM23Ng * k330cM23Bg * k330cM23Ng⁻¹ ∈ k330cM23X
        rw [k330cM23_conj_Bg]
        exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) 2)
          (Subgroup.subset_closure (by simp))
    have hcard : Nat.card (k330cM23X.map (MulAut.conj k330cM23Ng).toMonoidHom) =
        Nat.card k330cM23X :=
      Nat.card_congr (Subgroup.equivMapOfInjective k330cM23X
        (MulAut.conj k330cM23Ng).toMonoidHom (MulAut.conj k330cM23Ng).injective).toEquiv.symm
    refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
    exact Subgroup.eq_of_le_of_card_ge hmap_le (le_of_eq hcard.symm)
  have h1 : MovesLines k330cM23X k330cM23Ng := by
    intro x hx hx1
    obtain ⟨i, j, hi, hj, hxeq⟩ := (k330cMemClosurePair hA3 hB3 hAB x).mp hx
    subst hxeq
    interval_cases i <;> interval_cases j
    · exact absurd rfl hx1
    · exact k330cM23Ng_moves_01
    · exact k330cM23Ng_moves_02
    · exact k330cM23Ng_moves_10
    · exact k330cM23Ng_moves_11
    · exact k330cM23Ng_moves_12
    · exact k330cM23Ng_moves_20
    · exact k330cM23Ng_moves_21
    · exact k330cM23Ng_moves_22
  have h2 : MovesLines k330cM23X (k330cM23Ng ^ 2) := by
    intro x hx hx1
    obtain ⟨i, j, hi, hj, hxeq⟩ := (k330cMemClosurePair hA3 hB3 hAB x).mp hx
    subst hxeq
    interval_cases i <;> interval_cases j
    · exact absurd rfl hx1
    · exact k330cM23Ng2_moves_01
    · exact k330cM23Ng2_moves_02
    · exact k330cM23Ng2_moves_10
    · exact k330cM23Ng2_moves_11
    · exact k330cM23Ng2_moves_12
    · exact k330cM23Ng2_moves_20
    · exact k330cM23Ng2_moves_21
    · exact k330cM23Ng2_moves_22
  exact automizerBig_of_one k330cM23X hS hE h9 k330cM23Ng hn h1 h2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg
