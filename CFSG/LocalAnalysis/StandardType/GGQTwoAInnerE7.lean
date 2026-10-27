module

public import CFSG.LocalAnalysis.StandardType.GGQTwoInnerDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoQuandleE
public import CFSG.LocalAnalysis.StandardType.GGQTwoTransport

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


private def ggQ2xE7_z : Fin 7 → GGBCV 8 :=
  ![![1,2,0,0,0,0,0,0],
    ![0,0,1,2,0,0,0,0],
    ![2,0,0,0,1,0,0,0],
    ![0,0,0,1,2,0,0,0],
    ![2,2,1,1,2,1,1,2],
    ![0,0,0,0,0,1,0,2],
    ![0,0,0,0,0,2,1,0]]

private def ggQ2xE7_words : List (List (Fin 7)) :=
  [
    [0],
    [1],
    [2],
    [3],
    [4],
    [5],
    [6],
    [0, 0],
    [0, 2],
    [1, 1],
    [1, 3],
    [2, 2],
    [2, 3],
    [3, 3],
    [3, 4],
    [4, 4],
    [4, 5],
    [5, 5],
    [5, 6],
    [6, 6],
    [0, 0, 2],
    [0, 2, 3],
    [1, 1, 3],
    [1, 3, 2],
    [1, 3, 4],
    [2, 2, 3],
    [2, 3, 4],
    [3, 3, 4],
    [3, 4, 5],
    [4, 4, 5],
    [4, 5, 6],
    [5, 5, 6],
    [0, 0, 2, 3],
    [0, 2, 3, 1],
    [0, 2, 3, 4],
    [1, 1, 3, 2],
    [1, 1, 3, 4],
    [1, 3, 2, 4],
    [1, 3, 4, 5],
    [2, 2, 3, 4],
    [2, 3, 4, 5],
    [3, 3, 4, 5],
    [3, 4, 5, 6],
    [4, 4, 5, 6],
    [0, 0, 2, 3, 1],
    [0, 0, 2, 3, 4],
    [0, 2, 3, 1, 4],
    [0, 2, 3, 4, 5],
    [1, 1, 3, 2, 4],
    [1, 1, 3, 4, 5],
    [1, 3, 2, 4, 3],
    [1, 3, 2, 4, 5],
    [1, 3, 4, 5, 6],
    [2, 2, 3, 4, 5],
    [2, 3, 4, 5, 6],
    [3, 3, 4, 5, 6],
    [0, 0, 2, 3, 1, 4],
    [0, 0, 2, 3, 4, 5],
    [0, 2, 3, 1, 4, 3],
    [0, 2, 3, 1, 4, 5],
    [0, 2, 3, 4, 5, 6],
    [1, 1, 3, 2, 4, 3],
    [1, 1, 3, 2, 4, 5],
    [1, 1, 3, 4, 5, 6],
    [1, 3, 2, 4, 3, 5],
    [1, 3, 2, 4, 5, 6],
    [2, 2, 3, 4, 5, 6],
    [0, 0, 2, 3, 1, 4, 3],
    [0, 0, 2, 3, 1, 4, 5],
    [0, 0, 2, 3, 4, 5, 6],
    [0, 2, 3, 1, 4, 3, 2],
    [0, 2, 3, 1, 4, 3, 5],
    [0, 2, 3, 1, 4, 5, 6],
    [1, 1, 3, 2, 4, 3, 5],
    [1, 1, 3, 2, 4, 5, 6],
    [1, 3, 2, 4, 3, 5, 4],
    [1, 3, 2, 4, 3, 5, 6],
    [0, 0, 2, 3, 1, 4, 3, 2],
    [0, 0, 2, 3, 1, 4, 3, 5],
    [0, 0, 2, 3, 1, 4, 5, 6],
    [0, 2, 3, 1, 4, 3, 2, 5],
    [0, 2, 3, 1, 4, 3, 5, 4],
    [0, 2, 3, 1, 4, 3, 5, 6],
    [1, 1, 3, 2, 4, 3, 5, 4],
    [1, 1, 3, 2, 4, 3, 5, 6],
    [1, 3, 2, 4, 3, 5, 4, 6],
    [0, 0, 2, 3, 1, 4, 3, 2, 5],
    [0, 0, 2, 3, 1, 4, 3, 5, 4],
    [0, 0, 2, 3, 1, 4, 3, 5, 6],
    [0, 2, 3, 1, 4, 3, 2, 5, 4],
    [0, 2, 3, 1, 4, 3, 2, 5, 6],
    [0, 2, 3, 1, 4, 3, 5, 4, 6],
    [1, 1, 3, 2, 4, 3, 5, 4, 6],
    [1, 3, 2, 4, 3, 5, 4, 6, 5],
    [0, 0, 2, 3, 1, 4, 3, 2, 5, 4],
    [0, 0, 2, 3, 1, 4, 3, 2, 5, 6],
    [0, 0, 2, 3, 1, 4, 3, 5, 4, 6],
    [0, 2, 3, 1, 4, 3, 2, 5, 4, 3],
    [0, 2, 3, 1, 4, 3, 2, 5, 4, 6],
    [0, 2, 3, 1, 4, 3, 5, 4, 6, 5],
    [1, 1, 3, 2, 4, 3, 5, 4, 6, 5],
    [0, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3],
    [0, 0, 2, 3, 1, 4, 3, 2, 5, 4, 6],
    [0, 0, 2, 3, 1, 4, 3, 5, 4, 6, 5],
    [0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1],
    [0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 6],
    [0, 2, 3, 1, 4, 3, 2, 5, 4, 6, 5],
    [0, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1],
    [0, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 6],
    [0, 0, 2, 3, 1, 4, 3, 2, 5, 4, 6, 5],
    [0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6],
    [0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 6, 5],
    [0, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6],
    [0, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 6, 5],
    [0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5],
    [0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 6, 5, 4],
    [0, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5],
    [0, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 6, 5, 4],
    [0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4],
    [0, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4],
    [0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3],
    [0, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3],
    [0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3, 2],
    [0, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3, 2],
    [0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3, 2, 0],
    [0, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3, 2, 0]
  ]

private def ggQ2xE7_act (j : Fin 7) (v : GGBCV 8) : GGBCV 8 :=
  v - (ggQ2xE7_z j ⬝ᵥ v) • ggQ2xE7_z j

private def ggQ2xE7_evalWord (w : List (Fin 7)) : GGBCV 8 :=
  match w with
  | [] => 0
  | k :: js => js.foldl (fun v j => ggQ2xE7_act j v) (ggQ2xE7_z k)

private def ggQ2xE7_wordList : List (GGBCV 8) := ggQ2xE7_words.map ggQ2xE7_evalWord

private def ggQ2xE7_T : Set (GGBCV 8) := ggARoots 8 ∪ {z | ggAType4 z}

private lemma ggQ2xE7_isT_iff (v : GGBCV 8) :
    ((ggBCWt v = 2 ∧ ∑ i, v i = 0) ∨
      ((∀ i, v i ≠ 0) ∧ (Finset.univ.filter fun i => v i = 1).card = 4 ∧
        (Finset.univ.filter fun i => v i = -1).card = 4)) ↔ v ∈ ggQ2xE7_T :=
  Iff.rfl

private lemma ggQ2xE7_Wt_eq_two {n : ℕ} {v : GGBCV n} (h : ggBCWt v = 2) :
    ∃ a b : Fin n, a ≠ b ∧ ∃ c d : ZMod 3, c ≠ 0 ∧ d ≠ 0 ∧
      v = c • Pi.single a 1 + d • Pi.single b 1 := by
  unfold ggBCWt at h
  obtain ⟨a, b, hab, ha⟩ : ∃ a b : Fin n, a ≠ b ∧
      Finset.univ.filter (fun i => v i ≠ 0) = {a, b} := Finset.card_eq_two.mp h
  have hma : a ∈ Finset.univ.filter (fun i => v i ≠ 0) := by rw [ha]; simp
  have hmb : b ∈ Finset.univ.filter (fun i => v i ≠ 0) := by rw [ha]; simp
  have hva : v a ≠ 0 := by simpa using hma
  have hvb : v b ≠ 0 := by simpa using hmb
  refine ⟨a, b, hab, v a, v b, hva, hvb, ?_⟩
  funext i
  by_cases hia : i = a
  · subst hia
    simp [Pi.single_eq_of_ne (Ne.symm hab), hab]
  · by_cases hib : i = b
    · subst hib
      simp [Pi.single_eq_of_ne hab, hab]
    · have hm : i ∉ Finset.univ.filter (fun i => v i ≠ 0) := by rw [ha]; simp [hia, hib]
      have hvi : v i = 0 := by simpa using hm
      simp [Pi.single_eq_of_ne hia, Pi.single_eq_of_ne hib, hvi]

private lemma ggQ2xE7_eq_one_or_neg_one : ∀ x : ZMod 3, x ≠ 0 → x = 1 ∨ x = -1 := by
  decide

private lemma ggQ2xE7_sum_smul_single {n : ℕ} (i : Fin n) (x : ZMod 3) :
    ∑ k, (x • (Pi.single i (1 : ZMod 3) : GGBCV n)) k = x := by
  rw [Finset.sum_eq_single i]
  · simp [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul]
  · intro j _ hj
    simp [Pi.smul_apply, Pi.single_eq_of_ne hj, smul_eq_mul]
  · intro hi; exact absurd (Finset.mem_univ i) hi

private lemma ggQ2xE7_wordList_nodup : ggQ2xE7_wordList.Nodup := by decide +kernel

private lemma ggQ2xE7_wordList_isT :
    ggQ2xE7_wordList.Forall (fun v : GGBCV 8 =>
      (ggBCWt v = 2 ∧ ∑ i, v i = 0) ∨
        ((∀ i, v i ≠ 0) ∧ (Finset.univ.filter fun i => v i = 1).card = 4 ∧
          (Finset.univ.filter fun i => v i = -1).card = 4)) := by decide +kernel

private lemma ggQ2xE7_wordList_subset_T : ↑ggQ2xE7_wordList.toFinset ⊆ ggQ2xE7_T := by
  intro v hv
  rw [Finset.mem_coe, List.mem_toFinset] at hv
  rw [← ggQ2xE7_isT_iff]
  exact (List.forall_iff_forall_mem.mp ggQ2xE7_wordList_isT) v hv

private lemma ggQ2xE7_sub_mem : ∀ a b : Fin 8, a ≠ b →
    ((Pi.single a (1 : ZMod 3) : GGBCV 8) - Pi.single b 1) ∈ ggQ2xE7_wordList := by
  decide +kernel

private lemma ggQ2xE7_type4_mem : ∀ S : Finset (Fin 8), S.card = 4 →
    (fun i => if i ∈ S then (1 : ZMod 3) else -1) ∈ ggQ2xE7_wordList := by
  decide +kernel

private lemma ggQ2xE7_sc1 : ∀ c A B : ZMod 3, c * A + -c * B = c * (A - B) := by decide
private lemma ggQ2xE7_sc2 : ∀ A B : ZMod 3, (-1 : ZMod 3) * (A - B) = B - A := by decide

private lemma ggQ2xE7_T_subset_wordList : ggQ2xE7_T ⊆ ↑ggQ2xE7_wordList.toFinset := by
  intro v hv
  rw [ggQ2xE7_T, Set.mem_union] at hv
  rw [Finset.mem_coe, List.mem_toFinset]
  rcases hv with hvA | hv4
  · rw [ggARoots, Set.mem_setOf_eq] at hvA
    obtain ⟨hwt, hsum⟩ := hvA
    obtain ⟨a, b, hab, c, d, hc, hd, rfl⟩ := ggQ2xE7_Wt_eq_two hwt
    have hsum' : c + d = 0 := by
      have h := hsum
      simp only [Pi.add_apply] at h
      rw [Finset.sum_add_distrib, ggQ2xE7_sum_smul_single a c,
        ggQ2xE7_sum_smul_single b d] at h
      exact h
    have hd_eq : d = -c := eq_neg_of_add_eq_zero_right hsum'
    rw [hd_eq]
    have hfac : c • (Pi.single a (1 : ZMod 3) : GGBCV 8) + (-c) • Pi.single b 1 =
        c • ((Pi.single a (1 : ZMod 3) : GGBCV 8) - Pi.single b 1) := by
      ext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      exact ggQ2xE7_sc1 c _ _
    rw [hfac]
    rcases ggQ2xE7_eq_one_or_neg_one c hc with hc1 | hc1
    · rw [hc1, one_smul]
      exact ggQ2xE7_sub_mem a b hab
    · rw [hc1]
      have hneg : (-1 : ZMod 3) • ((Pi.single a (1 : ZMod 3) : GGBCV 8) - Pi.single b 1) =
          (Pi.single b (1 : ZMod 3) : GGBCV 8) - Pi.single a 1 := by
        ext i
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        exact ggQ2xE7_sc2 _ _
      rw [hneg]
      exact ggQ2xE7_sub_mem b a (Ne.symm hab)
  · simp only [ggAType4, Set.mem_setOf_eq] at hv4
    obtain ⟨hnz, hc1, _⟩ := hv4
    have hv_eq : v = fun i => if v i = 1 then (1 : ZMod 3) else -1 := by
      funext i
      by_cases hi : v i = 1
      · simp [hi]
      · rcases ggQ2xE7_eq_one_or_neg_one (v i) (hnz i) with h | h
        · exact absurd h hi
        · simp [hi, h]
    have hvS : (fun i => if v i = 1 then (1 : ZMod 3) else -1) =
        (fun i => if i ∈ (Finset.univ.filter fun i => v i = 1) then (1 : ZMod 3) else -1) := by
      funext i
      by_cases hi : v i = 1 <;> simp [hi]
    rw [hv_eq, hvS]
    exact ggQ2xE7_type4_mem (Finset.univ.filter fun i => v i = 1) hc1

private lemma ggQ2xE7_T_eq_wordList : ggQ2xE7_T = ↑ggQ2xE7_wordList.toFinset :=
  Set.Subset.antisymm ggQ2xE7_T_subset_wordList ggQ2xE7_wordList_subset_T

private lemma ggQ2xE7_T_closed : ∀ j : Fin 7,
    ggQ2xE7_wordList.Forall (fun v => ggQ2xE7_act j v ∈ ggQ2xE7_wordList) := by
  decide +kernel

private lemma ggQ2xE7_z_mem_wordList : ∀ i : Fin 7, ggQ2xE7_z i ∈ ggQ2xE7_wordList := by
  decide +kernel

private lemma ggQ2xE7_gram : ∀ i j : Fin 7,
    (ggQ2xE7_z i ⬝ᵥ ggQ2xE7_z j : ZMod 3) = (CartanMatrix.E 7 i j : ZMod 3) := by
  decide

private lemma ggQ2xE7_z_sum : ∀ i : Fin 7, ∑ k, ggQ2xE7_z i k = 0 := by
  decide

private lemma ggQ2xE7_z_mem_T : ∀ i : Fin 7, ggQ2xE7_z i ∈ ggQ2xE7_T := by
  intro i
  rw [ggQ2xE7_T_eq_wordList, Finset.mem_coe, List.mem_toFinset]
  exact ggQ2xE7_z_mem_wordList i


private noncomputable def ggQ2xE7_sumLin : GGBCV 8 →ₗ[ZMod 3] ZMod 3 where
  toFun v := ∑ i, v i
  map_add' v w := by simp [Finset.sum_add_distrib]
  map_smul' a v := by simp [Finset.mul_sum]

private noncomputable def ggQ2xE7_H : Submodule (ZMod 3) (GGBCV 8) :=
  LinearMap.ker ggQ2xE7_sumLin

private noncomputable def ggQ2xE7_c : GGBCV 8 →ₗ[ZMod 3] ZMod 3 :=
  (2 : ZMod 3) • ggQ2xE7_sumLin

private lemma ggQ2xE7_sumLin_apply (v : GGBCV 8) : ggQ2xE7_sumLin v = ∑ i, v i := rfl

private lemma ggQ2xE7_sumLin_one : ggQ2xE7_sumLin (1 : GGBCV 8) = 2 := by decide

private lemma ggQ2xE7_c_apply (v : GGBCV 8) : ggQ2xE7_c v = 2 * ∑ i, v i := rfl

private lemma ggQ2xE7_sc3 : ∀ S : ZMod 3, S - (2 * S) * 2 = 0 := by decide

private lemma ggQ2xE7_proj_mem (v : GGBCV 8) :
    v - ggQ2xE7_c v • (1 : GGBCV 8) ∈ ggQ2xE7_H := by
  rw [ggQ2xE7_H, LinearMap.mem_ker, map_sub, map_smul, ggQ2xE7_sumLin_apply,
    ggQ2xE7_sumLin_one, ggQ2xE7_c_apply, smul_eq_mul]
  exact ggQ2xE7_sc3 _

private noncomputable def ggQ2xE7_proj (v : GGBCV 8) : ggQ2xE7_H :=
  ⟨v - ggQ2xE7_c v • (1 : GGBCV 8), ggQ2xE7_proj_mem v⟩

private lemma ggQ2xE7_proj_spec (v : GGBCV 8) :
    (ggQ2xE7_proj v : GGBCV 8) + ggQ2xE7_c v • (1 : GGBCV 8) = v := by
  simp [ggQ2xE7_proj]

private lemma ggQ2xE7_c_one : ggQ2xE7_c (1 : GGBCV 8) = 1 := by decide

private lemma ggQ2xE7_proj_one : ggQ2xE7_proj (1 : GGBCV 8) = 0 := by
  ext
  simp [ggQ2xE7_proj, ggQ2xE7_c_one]

private lemma ggQ2xE7_ggBCDot_apply (c v : GGBCV 8) : ggBCDot c v = c ⬝ᵥ v := by
  simp only [ggBCDot, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
    smul_eq_mul]
  rfl

private def ggQ2xE7_sig (x : Fin 7 → ZMod 3) : GGBCV 8 :=
  Fin.cases (-∑ i, x i) x

private lemma ggQ2xE7_sig_sum (x : Fin 7 → ZMod 3) : ∑ k, ggQ2xE7_sig x k = 0 := by
  rw [Fin.sum_univ_succ]
  simp only [ggQ2xE7_sig, Fin.cases_zero, Fin.cases_succ]
  abel

private noncomputable def ggQ2xE7_tauLin :
    ggQ2xE7_H →ₗ[ZMod 3] (Fin 7 → ZMod 3) where
  toFun v := fun i => v.val (Fin.succ i)
  map_add' v w := by ext i; rfl
  map_smul' a v := by ext i; rfl

private lemma ggQ2xE7_tauLin_injective : Function.Injective ggQ2xE7_tauLin := by
  intro v w h
  apply Subtype.ext
  funext k
  cases k using Fin.cases with
  | zero =>
    have hv : ∑ i, v.val i = 0 := v.2
    have hw : ∑ i, w.val i = 0 := w.2
    have hvs : ∀ i, v.val (Fin.succ i) = w.val (Fin.succ i) := fun i => congrFun h i
    rw [Fin.sum_univ_succ] at hv hw
    have hs : ∑ i, v.val (Fin.succ i) = ∑ i, w.val (Fin.succ i) :=
      Finset.sum_congr rfl (fun i _ => hvs i)
    rw [hs] at hv
    exact add_right_cancel (by rw [hv, hw])
  | succ i => exact congrFun h i

private lemma ggQ2xE7_tauLin_surjective : Function.Surjective ggQ2xE7_tauLin := by
  intro x
  refine ⟨⟨ggQ2xE7_sig x, ?_⟩, ?_⟩
  · rw [ggQ2xE7_H, LinearMap.mem_ker, ggQ2xE7_sumLin_apply]
    exact ggQ2xE7_sig_sum x
  · ext i; rfl

private noncomputable def ggQ2xE7_tau :
    ggQ2xE7_H ≃ₗ[ZMod 3] (Fin 7 → ZMod 3) :=
  LinearEquiv.ofBijective ggQ2xE7_tauLin
    ⟨ggQ2xE7_tauLin_injective, ggQ2xE7_tauLin_surjective⟩

private lemma ggQ2xE7_finrank_H : Module.finrank (ZMod 3) ggQ2xE7_H = 7 := by
  rw [ggQ2xE7_tau.finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

private noncomputable def ggQ2xE7_D : GGQ2Lin 3 where
  ι := Fin 7
  coxeter := CoxeterMatrix.E₇
  cartan := CartanMatrix.E 7
  V := ggQ2xE7_H
  instAddCommGroup := Submodule.addCommGroup ggQ2xE7_H
  instModule := Submodule.module ggQ2xE7_H
  coroot i := ⟨ggQ2xE7_z i, by
    rw [ggQ2xE7_H, LinearMap.mem_ker, ggQ2xE7_sumLin_apply]
    exact ggQ2xE7_z_sum i⟩
  root i := (ggBCDot (ggQ2xE7_z i)).comp ggQ2xE7_H.subtype
  a := 0
  b := 1
  a_ne_b := by decide
  a_leaf := by
    refine ⟨2, by decide, ?_⟩
    intro y hy
    fin_cases y <;> (first | exact rfl | (exfalso; exact hy.1 rfl) |
      (exfalso; exact hy.2 (by decide)))
  isWeyl := Or.inr (Or.inr (Or.inl ⟨Equiv.refl _, rfl⟩))
  isCartan := by
    refine ⟨fun i => by fin_cases i <;> decide, fun i j hij => ?_⟩
    fin_cases i <;> fin_cases j <;>
      first | (exfalso; exact hij rfl) | decide +kernel
  pairing i j := by
    change ggBCDot (ggQ2xE7_z i) (ggQ2xE7_z j) = (CartanMatrix.E 7 i j : ZMod 3)
    rw [ggQ2xE7_ggBCDot_apply, ggQ2xE7_gram]

private def ggQ2xE7_Cinv : Matrix (Fin 7) (Fin 7) (ZMod 3) :=
  !![2, 2, 0, 1, 0, 2, 1;
     2, 2, 1, 0, 0, 0, 0;
     0, 1, 0, 2, 0, 1, 2;
     1, 0, 2, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 2, 1;
     2, 0, 1, 0, 2, 1, 2;
     1, 0, 2, 0, 1, 2, 0]

private lemma ggQ2xE7_det_ne_zero :
    (Matrix.of (fun i j : Fin 7 => (CartanMatrix.E 7 i j : ZMod 3))).det ≠ 0 := by
  intro h
  have hmul : (Matrix.of (fun i j : Fin 7 => (CartanMatrix.E 7 i j : ZMod 3))) *
      ggQ2xE7_Cinv = 1 := by decide
  have hdet := congrArg Matrix.det hmul
  rw [Matrix.det_mul, Matrix.det_one, h, zero_mul] at hdet
  exact one_ne_zero hdet.symm

private lemma ggQ2xE7_D_coroot_li : LinearIndependent (ZMod 3) ggQ2xE7_D.coroot := by
  refine linearIndependent_of_det_ne_zero ggQ2xE7_D.coroot ggQ2xE7_D.root ?_
  have h : (Matrix.of fun i j => ggQ2xE7_D.root i (ggQ2xE7_D.coroot j)) =
      (Matrix.of fun i j => (CartanMatrix.E 7 i j : ZMod 3)) := by
    ext i j; exact ggQ2xE7_D.pairing i j
  rw [h]; exact ggQ2xE7_det_ne_zero

private lemma ggQ2xE7_D_basis : ggQ2xE7_D.Basis := by
  refine ⟨ggQ2xE7_D_coroot_li, ?_⟩
  change Fintype.card (Fin 7) = Module.finrank (ZMod 3) ggQ2xE7_H
  rw [ggQ2xE7_finrank_H]
  simp

private lemma ggQ2xE7_D_isE :
    (∃ e : Fin 6 ≃ ggQ2xE7_D.ι, ggQ2xE7_D.coxeter = CoxeterMatrix.E₆.reindex e) ∨
      (∃ e : Fin 7 ≃ ggQ2xE7_D.ι, ggQ2xE7_D.coxeter = CoxeterMatrix.E₇.reindex e) ∨
      (∃ e : Fin 8 ≃ ggQ2xE7_D.ι, ggQ2xE7_D.coxeter = CoxeterMatrix.E₈.reindex e) :=
  Or.inr (Or.inl ⟨Equiv.refl _, rfl⟩)

private lemma ggQ2xE7_D_isConjRefl_finite : (ggQ2xQ_isConjRefl ggQ2xE7_D).Finite := by
  haveI : Finite (ggQ2xE7_H ≃ₗ[ZMod 3] ggQ2xE7_H) :=
    Finite.of_injective (fun e => (e : ggQ2xE7_H → ggQ2xE7_H))
      (fun e f h => LinearEquiv.ext (congrFun h))
  exact (Set.finite_univ (α := ggQ2xE7_H ≃ₗ[ZMod 3] ggQ2xE7_H)).subset (Set.subset_univ _)

private theorem ggQ2xE7_D_inner :
    GGQ2QuandleInner (ggQ2xQ_isConjRefl ggQ2xE7_D) (ggQ2xE7_D.weyl : Set _) := by
  intro π hπT hinj hπ
  have hmaps : Set.MapsTo π (ggQ2xQ_isConjRefl ggQ2xE7_D) (ggQ2xQ_isConjRefl ggQ2xE7_D) := hπT
  have hsurj : Set.SurjOn π (ggQ2xQ_isConjRefl ggQ2xE7_D) (ggQ2xQ_isConjRefl ggQ2xE7_D) :=
    (Set.Finite.surjOn_iff_bijOn_of_mapsTo ggQ2xE7_D_isConjRefl_finite hmaps).mpr
      ((Set.Finite.injOn_iff_bijOn_of_mapsTo ggQ2xE7_D_isConjRefl_finite hmaps).mp hinj)
  exact ggQ2_quandle_aut_E ggQ2xE7_D ggQ2xE7_D_basis ggQ2xE7_D_isE π hπT hinj hsurj hπ


private noncomputable def ggQ2xE7_K : Subgroup (GGBCV 8 ≃ₗ[ZMod 3] GGBCV 8) where
  carrier := {g | ggQ2xE7_H.map g.toLinearMap = ggQ2xE7_H ∧ g 1 = 1}
  one_mem' := by
    refine ⟨?_, rfl⟩
    change ggQ2xE7_H.map (↑(1 : GGBCV 8 ≃ₗ[ZMod 3] GGBCV 8) :
      GGBCV 8 →ₗ[ZMod 3] GGBCV 8) = ggQ2xE7_H
    rw [show (↑(1 : GGBCV 8 ≃ₗ[ZMod 3] GGBCV 8) : GGBCV 8 →ₗ[ZMod 3] GGBCV 8) =
      LinearMap.id from rfl, Submodule.map_id]
  mul_mem' := fun {g h} hg hh => by
    refine ⟨?_, ?_⟩
    · change ggQ2xE7_H.map (↑(g * h) : GGBCV 8 →ₗ[ZMod 3] GGBCV 8) = ggQ2xE7_H
      rw [show (↑(g * h) : GGBCV 8 →ₗ[ZMod 3] GGBCV 8) =
          (↑g : GGBCV 8 →ₗ[ZMod 3] GGBCV 8).comp (↑h : GGBCV 8 →ₗ[ZMod 3] GGBCV 8) from rfl,
        Submodule.map_comp, hh.1, hg.1]
    · rw [LinearEquiv.mul_apply, hh.2, hg.2]
  inv_mem' := fun {g} hg => by
    refine ⟨?_, ?_⟩
    · change ggQ2xE7_H.map (↑(g⁻¹) : GGBCV 8 →ₗ[ZMod 3] GGBCV 8) = ggQ2xE7_H
      have h := congrArg (Submodule.map (↑(g⁻¹) : GGBCV 8 →ₗ[ZMod 3] GGBCV 8)) hg.1
      rw [← Submodule.map_comp] at h
      have h2 : (↑(g⁻¹) : GGBCV 8 →ₗ[ZMod 3] GGBCV 8).comp
          (↑g : GGBCV 8 →ₗ[ZMod 3] GGBCV 8) = LinearMap.id := by
        ext v; simp
      rw [h2, Submodule.map_id] at h
      exact h.symm
    · conv_lhs => rw [← hg.2]
      exact LinearEquiv.symm_apply_apply g 1

private noncomputable def ggQ2xE7_resHom :
    ggQ2xE7_K →* (ggQ2xE7_H ≃ₗ[ZMod 3] ggQ2xE7_H) where
  toFun g := LinearEquiv.ofSubmodules g.1 ggQ2xE7_H ggQ2xE7_H g.2.1
  map_one' := by ext; rfl
  map_mul' g h := by ext; rfl

private lemma ggQ2xE7_resHom_apply (g : ggQ2xE7_K) (x : ggQ2xE7_H) :
    (ggQ2xE7_resHom g x : GGBCV 8) = g.1 x := rfl

private lemma ggQ2xE7_resHom_injective : Function.Injective ggQ2xE7_resHom := by
  intro g h hgh
  apply Subtype.ext
  refine LinearEquiv.ext (fun v => ?_)
  have hproj : g.1 (ggQ2xE7_proj v : GGBCV 8) = h.1 (ggQ2xE7_proj v : GGBCV 8) := by
    have := congrArg (fun e : ggQ2xE7_H ≃ₗ[ZMod 3] ggQ2xE7_H =>
      (e (ggQ2xE7_proj v) : GGBCV 8)) hgh
    simpa [ggQ2xE7_resHom] using this
  have h1 : g.1 (1 : GGBCV 8) = 1 := g.2.2
  have h2 : h.1 (1 : GGBCV 8) = 1 := h.2.2
  calc g.1 v = g.1 ((ggQ2xE7_proj v : GGBCV 8) + ggQ2xE7_c v • (1 : GGBCV 8)) := by
        rw [ggQ2xE7_proj_spec]
    _ = g.1 (ggQ2xE7_proj v : GGBCV 8) + ggQ2xE7_c v • g.1 1 := by rw [map_add, map_smul]
    _ = h.1 (ggQ2xE7_proj v : GGBCV 8) + ggQ2xE7_c v • h.1 1 := by rw [hproj, h1, h2]
    _ = h.1 ((ggQ2xE7_proj v : GGBCV 8) + ggQ2xE7_c v • (1 : GGBCV 8)) := by
        rw [map_add, map_smul]
    _ = h.1 v := by rw [ggQ2xE7_proj_spec]

private lemma ggQ2xE7_ggBCRefl_apply (c : GGBCV 8) (hc : c ⬝ᵥ c ≠ 0) (v : GGBCV 8) :
    ggBCRefl c hc v = v - (2 / (c ⬝ᵥ c) * (c ⬝ᵥ v)) • c := by
  erw [ggBCRefl, Module.reflection_apply]
  erw [LinearMap.smul_apply, ggQ2xE7_ggBCDot_apply, smul_eq_mul]
  rfl

private lemma ggQ2xE7_wordList_sum : ggQ2xE7_wordList.Forall (fun v => ∑ i, v i = 0) := by
  decide +kernel

private lemma ggQ2xE7_T_subset_H : ggQ2xE7_T ⊆ ggQ2xE7_H := by
  intro v hv
  have hv' := hv
  rw [ggQ2xE7_T_eq_wordList, Finset.mem_coe, List.mem_toFinset] at hv'
  have hs := (List.forall_iff_forall_mem.mp ggQ2xE7_wordList_sum) v hv'
  show ggQ2xE7_sumLin v = 0
  rw [ggQ2xE7_sumLin_apply]
  exact hs

private lemma ggQ2xE7_dot_one (v : GGBCV 8) : v ⬝ᵥ (1 : GGBCV 8) = ∑ i, v i := by
  simp [dotProduct]

private lemma ggQ2xE7_refl_involutive (v : GGBCV 8) (hc : v ⬝ᵥ v ≠ 0) :
    Function.Involutive (ggBCRefl v hc) := by
  intro x
  rw [ggBCRefl]
  exact Module.involutive_reflection _ x

private lemma ggQ2xE7_refl_mem_K (v : GGBCV 8) (hv : v ∈ ggQ2xE7_T) (hc : v ⬝ᵥ v ≠ 0) :
    ggBCRefl v hc ∈ ggQ2xE7_K := by
  have hvH : v ∈ ggQ2xE7_H := ggQ2xE7_T_subset_H hv
  have hsum : ∑ i, v i = 0 := by
    have h := hvH; rwa [ggQ2xE7_H, LinearMap.mem_ker, ggQ2xE7_sumLin_apply] at h
  have hmem : ∀ x ∈ ggQ2xE7_H, ggBCRefl v hc x ∈ ggQ2xE7_H := by
    intro x hx
    rw [ggQ2xE7_ggBCRefl_apply]
    exact ggQ2xE7_H.sub_mem hx (ggQ2xE7_H.smul_mem _ hvH)
  refine ⟨?_, ?_⟩
  · change ggQ2xE7_H.map (ggBCRefl v hc).toLinearMap = ggQ2xE7_H
    refine le_antisymm ?_ ?_
    · rw [Submodule.map_le_iff_le_comap]
      exact hmem
    · intro y hy
      exact ⟨ggBCRefl v hc y, hmem y hy, ggQ2xE7_refl_involutive v hc y⟩
  · rw [ggQ2xE7_ggBCRefl_apply, ggQ2xE7_dot_one v, hsum, mul_zero, zero_smul]
    simp

private lemma ggQ2xE7_simpleRefl_eq_act (k : Fin 7) (v : ggQ2xE7_H) :
    (ggQ2xE7_D.simpleRefl k v).val = ggQ2xE7_act k v.val := by
  let v' : ggQ2xE7_D.V := v
  change (ggQ2xE7_D.simpleRefl k v').val = ggQ2xE7_act k v.val
  have h : ggQ2xE7_D.simpleRefl k v' =
      v' - (ggQ2xE7_D.root k v') • ggQ2xE7_D.coroot k :=
    Module.reflection_apply (h := ggQ2xE7_D.root_coroot_self k) v'
  rw [h]
  rfl

private lemma ggQ2xE7_resHom_refl (k : Fin 7) (hc : ggQ2xE7_z k ⬝ᵥ ggQ2xE7_z k ≠ 0) :
    ggQ2xE7_resHom ⟨ggBCRefl (ggQ2xE7_z k) hc,
      ggQ2xE7_refl_mem_K _ (ggQ2xE7_z_mem_T k) hc⟩ = ggQ2xE7_D.simpleRefl k := by
  refine LinearEquiv.ext (fun x => ?_)
  apply Subtype.ext
  rw [ggQ2xE7_resHom_apply]
  change ggBCRefl (ggQ2xE7_z k) hc x.val = (ggQ2xE7_D.simpleRefl k x).val
  rw [ggQ2xE7_simpleRefl_eq_act, ggQ2xE7_act, ggQ2xE7_ggBCRefl_apply]
  have hkk : ggQ2xE7_z k ⬝ᵥ ggQ2xE7_z k = 2 := by
    rw [ggQ2xE7_gram]; fin_cases k <;> decide
  rw [hkk]
  rw [show (2 : ZMod 3) / 2 = 1 by decide +kernel, one_mul]

private lemma ggQ2xE7_two_div_eq_neg (x : ZMod 3) (hx : x ≠ 0) : (2 : ZMod 3) / x = -x := by
  revert hx; revert x; decide +kernel

private lemma ggQ2xE7_scalar_refl (vi ci A B : ZMod 3) :
    vi - (-A * B) * ci = vi + (A * B) * ci := by
  revert vi ci A B; decide +kernel

private lemma ggQ2xE7_refl_apply (c : GGBCV 8) (hc : c ⬝ᵥ c ≠ 0) (v : GGBCV 8) :
    ggBCRefl c hc v = v + ((c ⬝ᵥ c) * (c ⬝ᵥ v)) • c := by
  rw [ggQ2xE7_ggBCRefl_apply, ggQ2xE7_two_div_eq_neg (c ⬝ᵥ c) hc]
  ext i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  exact ggQ2xE7_scalar_refl (v i) (c i) (c ⬝ᵥ c) (c ⬝ᵥ v)

private lemma ggQ2xE7_iso_scalar : ∀ r d p q : ZMod 3, d * d = 1 →
    r + d * p * q + d * q * (p + d * p * d) = r := by decide

private lemma ggQ2xE7_refl_isometry (c : GGBCV 8) (hc : c ⬝ᵥ c ≠ 0) (x y : GGBCV 8) :
    (ggBCRefl c hc x) ⬝ᵥ (ggBCRefl c hc y) = x ⬝ᵥ y := by
  have hcast : ∀ z : ZMod 3, z ≠ 0 → z * z = 1 := by decide
  have hdd : (c ⬝ᵥ c) * (c ⬝ᵥ c) = 1 := hcast _ hc
  rw [ggQ2xE7_refl_apply, ggQ2xE7_refl_apply]
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [dotProduct_comm (c : GGBCV 8) x, dotProduct_comm (c : GGBCV 8) y]
  rw [ggQ2xE7_iso_scalar (x ⬝ᵥ y) (c ⬝ᵥ c) (x ⬝ᵥ c) (y ⬝ᵥ c) hdd]

private lemma ggQ2xE7_conj_refl (b : GGBCV 8 ≃ₗ[ZMod 3] GGBCV 8)
    (hb : ∀ x y, (b x) ⬝ᵥ (b y) = x ⬝ᵥ y)
    (c : GGBCV 8) (hc : c ⬝ᵥ c ≠ 0) :
    b * ggBCRefl c hc * b.symm = ggBCRefl (b c) (by rw [hb]; exact hc) := by
  have hbc : (b c) ⬝ᵥ (b c) = c ⬝ᵥ c := hb c c
  ext v
  have hbv : (b c) ⬝ᵥ v = c ⬝ᵥ (b.symm v) := by
    conv_lhs => rw [← LinearEquiv.apply_symm_apply b v]
    rw [hb c (b.symm v)]
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ggQ2xE7_refl_apply, ggQ2xE7_refl_apply,
    map_add, map_smul, LinearEquiv.apply_symm_apply]
  rw [hbc, hbv]

private lemma ggQ2xE7_reflGp_isometry :
    ∀ b ∈ ggBCReflGp ggQ2xE7_T, ∀ x y : GGBCV 8, (b x) ⬝ᵥ (b y) = x ⬝ᵥ y := by
  intro b hb
  refine Subgroup.closure_induction (p := fun b _ => ∀ x y, (b x) ⬝ᵥ (b y) = x ⬝ᵥ y) ?_ ?_ ?_ ?_ hb
  · rintro u ⟨c, hc, hcc, rfl⟩
    exact ggQ2xE7_refl_isometry c hcc
  · intro x y; rfl
  · intro a b _ _ iha ihb x y
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, iha, ihb]
  · intro a _ iha x y
    have h := iha (a⁻¹ x) (a⁻¹ y)
    rw [show a (a⁻¹ x) = x from by simp [LinearEquiv.coe_inv],
      show a (a⁻¹ y) = y from by simp [LinearEquiv.coe_inv]] at h
    exact h.symm




private noncomputable def ggQ2xE7_idx : Fin 7 → ggQ2xE7_D.ι := fun j => j

private noncomputable def ggQ2xE7_vec : ggQ2xE7_H → ggQ2xE7_D.V := fun v => v

private noncomputable def ggQ2xE7_vecInv : ggQ2xE7_D.V → ggQ2xE7_H := fun v => v

private lemma ggQ2xE7_vec_vecInv (v : ggQ2xE7_D.V) : ggQ2xE7_vec (ggQ2xE7_vecInv v) = v := rfl

private lemma ggQ2xE7_vecInv_vec (v : ggQ2xE7_H) : ggQ2xE7_vecInv (ggQ2xE7_vec v) = v := rfl

example (v : ggQ2xE7_H) : ggQ2xE7_vecInv (ggQ2xE7_vec v) = v := rfl
example (v : ggQ2xE7_D.V) : ggQ2xE7_vec (ggQ2xE7_vecInv v) = v := rfl
example (j : Fin 7) : ggQ2xE7_idx j = (j : ggQ2xE7_D.ι) := rfl


private noncomputable def ggQ2xE7_val (v : ggQ2xE7_D.V) : GGBCV 8 :=
  (ggQ2xE7_vecInv v).val

private def ggQ2xE7_TH : Set ggQ2xE7_D.V := {v | ggQ2xE7_val v ∈ ggQ2xE7_T}

private def ggQ2xE7_orbit : Set ggQ2xE7_D.V :=
  {v | ∃ w ∈ ggQ2xE7_D.weyl, ∃ k : ggQ2xE7_D.ι, w (ggQ2xE7_D.coroot k) = v}

private noncomputable def ggQ2xE7_wordProd :
    List (Fin 7) → (ggQ2xE7_D.V ≃ₗ[ZMod 3] ggQ2xE7_D.V)
  | [] => 1
  | j :: js => ggQ2xE7_wordProd js * ggQ2xE7_D.simpleRefl (ggQ2xE7_idx j)

private lemma ggQ2xE7_wordProd_mem_weyl (js : List (Fin 7)) :
    ggQ2xE7_wordProd js ∈ ggQ2xE7_D.weyl := by
  induction js with
  | nil => exact Subgroup.one_mem _
  | cons j js ih =>
    exact Subgroup.mul_mem _ ih (ggQ2xQ_simpleRefl_mem_weyl ggQ2xE7_D (ggQ2xE7_idx j))

private lemma ggQ2xE7_foldl_eq_wordProd (js : List (Fin 7)) (v : ggQ2xE7_D.V) :
    js.foldl (fun v j => ggQ2xE7_D.simpleRefl (ggQ2xE7_idx j) v) v =
      ggQ2xE7_wordProd js v := by
  induction js generalizing v with
  | nil => rfl
  | cons j js ih =>
    show js.foldl (fun v j => ggQ2xE7_D.simpleRefl (ggQ2xE7_idx j) v)
        (ggQ2xE7_D.simpleRefl (ggQ2xE7_idx j) v) =
      (ggQ2xE7_wordProd js * ggQ2xE7_D.simpleRefl (ggQ2xE7_idx j)) v
    rw [ih, LinearEquiv.mul_apply]

private noncomputable def ggQ2xE7_evalH : List (Fin 7) → ggQ2xE7_D.V
  | [] => 0
  | k :: js => js.foldl (fun v j => ggQ2xE7_D.simpleRefl (ggQ2xE7_idx j) v)
      (ggQ2xE7_D.coroot (ggQ2xE7_idx k))

private lemma ggQ2xE7_evalH_mem_orbit (k : Fin 7) (js : List (Fin 7)) :
    ggQ2xE7_evalH (k :: js) ∈ ggQ2xE7_orbit := by
  refine ⟨ggQ2xE7_wordProd js, ggQ2xE7_wordProd_mem_weyl js, ggQ2xE7_idx k, ?_⟩
  show ggQ2xE7_wordProd js (ggQ2xE7_D.coroot (ggQ2xE7_idx k)) = ggQ2xE7_evalH (k :: js)
  rw [← ggQ2xE7_foldl_eq_wordProd]
  rfl

private lemma ggQ2xE7_z_mem_TH (k : Fin 7) : ggQ2xE7_D.coroot (ggQ2xE7_idx k) ∈ ggQ2xE7_TH := by
  show ggQ2xE7_val (ggQ2xE7_D.coroot (ggQ2xE7_idx k)) ∈ ggQ2xE7_T
  have : ggQ2xE7_val (ggQ2xE7_D.coroot (ggQ2xE7_idx k)) = ggQ2xE7_z k := rfl
  rw [this]
  exact ggQ2xE7_z_mem_T k


private noncomputable def ggQ2xE7_idx_inv : ggQ2xE7_D.ι → Fin 7 := fun k => k

private lemma ggQ2xE7_idx_inv_idx (j : Fin 7) : ggQ2xE7_idx_inv (ggQ2xE7_idx j) = j := rfl

private lemma ggQ2xE7_val_simpleRefl (j : Fin 7) (v : ggQ2xE7_D.V) :
    ggQ2xE7_val (ggQ2xE7_D.simpleRefl (ggQ2xE7_idx j) v) =
      ggQ2xE7_act j (ggQ2xE7_val v) := by
  change (ggQ2xE7_vecInv (ggQ2xE7_D.simpleRefl (ggQ2xE7_idx j) v)).val = _
  rw [show ggQ2xE7_vecInv (ggQ2xE7_D.simpleRefl (ggQ2xE7_idx j) v) =
      ggQ2xE7_D.simpleRefl j (ggQ2xE7_vecInv v) from rfl]
  rw [ggQ2xE7_simpleRefl_eq_act]
  rfl

private lemma ggQ2xE7_simpleRefl_mem_TH (k : Fin 7) {v : ggQ2xE7_D.V}
    (hv : v ∈ ggQ2xE7_TH) : ggQ2xE7_D.simpleRefl (ggQ2xE7_idx k) v ∈ ggQ2xE7_TH := by
  have hv' : ggQ2xE7_val v ∈ ggQ2xE7_T := hv
  show ggQ2xE7_val (ggQ2xE7_D.simpleRefl (ggQ2xE7_idx k) v) ∈ ggQ2xE7_T
  rw [ggQ2xE7_val_simpleRefl]
  rw [ggQ2xE7_T_eq_wordList] at hv' ⊢
  rw [Finset.mem_coe, List.mem_toFinset] at hv' ⊢
  exact (List.forall_iff_forall_mem.mp (ggQ2xE7_T_closed k)) (ggQ2xE7_val v) hv'

private lemma ggQ2xE7_simpleRefl_image_TH (k : Fin 7) :
    ggQ2xE7_D.simpleRefl (ggQ2xE7_idx k) '' ggQ2xE7_TH = ggQ2xE7_TH := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨v, hv, rfl⟩
    exact ggQ2xE7_simpleRefl_mem_TH k hv
  · intro v hv
    exact ⟨ggQ2xE7_D.simpleRefl (ggQ2xE7_idx k) v, ggQ2xE7_simpleRefl_mem_TH k hv,
      Module.involutive_reflection (ggQ2xE7_D.root_coroot_self (ggQ2xE7_idx k)) v⟩

private lemma ggQ2xE7_weyl_image_TH (w : ggQ2xE7_D.V ≃ₗ[ZMod 3] ggQ2xE7_D.V)
    (hw : w ∈ ggQ2xE7_D.weyl) : w '' ggQ2xE7_TH = ggQ2xE7_TH := by
  have hw' : w ∈ Subgroup.closure (Set.range ggQ2xE7_D.simpleRefl) :=
    (ggQ2xQ_mem_weyl_iff ggQ2xE7_D).1 hw
  refine Subgroup.closure_induction (G := ggQ2xE7_D.V ≃ₗ[ZMod 3] ggQ2xE7_D.V)
    (p := fun w _ => w '' ggQ2xE7_TH = ggQ2xE7_TH) ?_ ?_ ?_ ?_ hw'
  · rintro u ⟨k, rfl⟩
    have h := ggQ2xE7_simpleRefl_image_TH (ggQ2xE7_idx_inv k)
    rwa [show ggQ2xE7_idx (ggQ2xE7_idx_inv k) = k from rfl] at h
  · exact Set.image_id _
  · intro a b _ _ iha ihb
    rw [show (a * b) '' ggQ2xE7_TH = a '' (b '' ggQ2xE7_TH) by
      ext x; constructor
      · rintro ⟨u, hu, rfl⟩; exact ⟨b u, ⟨u, hu, rfl⟩, rfl⟩
      · rintro ⟨u, ⟨z, hz, rfl⟩, rfl⟩; exact ⟨z, hz, by simp [LinearEquiv.mul_apply]⟩]
    rw [ihb, iha]
  · intro a _ iha
    refine le_antisymm ?_ ?_
    · rintro _ ⟨v, hv, rfl⟩
      have hmem : v ∈ a '' ggQ2xE7_TH := by rw [iha]; exact hv
      rcases hmem with ⟨u, hu, hua⟩
      rw [show a⁻¹ v = u from by rw [← hua]; simp]
      exact hu
    · intro v hv
      refine ⟨a v, ?_, ?_⟩
      · rw [← iha]; exact ⟨v, hv, rfl⟩
      · simp

private lemma ggQ2xE7_orbit_subset_TH : ggQ2xE7_orbit ⊆ ggQ2xE7_TH := by
  rintro v ⟨w, hw, k, rfl⟩
  have hw' := ggQ2xE7_weyl_image_TH w hw
  have hmem : w (ggQ2xE7_D.coroot k) ∈ w '' ggQ2xE7_TH :=
    ⟨ggQ2xE7_D.coroot k, ggQ2xE7_z_mem_TH (ggQ2xE7_idx_inv k), rfl⟩
  rwa [hw'] at hmem

private lemma ggQ2xE7_foldl_val (js : List (Fin 7)) (v : ggQ2xE7_D.V) :
    ggQ2xE7_val (js.foldl (fun v j => ggQ2xE7_D.simpleRefl (ggQ2xE7_idx j) v) v) =
      js.foldl (fun w j => ggQ2xE7_act j w) (ggQ2xE7_val v) := by
  induction js generalizing v with
  | nil => rfl
  | cons j js ih =>
    show ggQ2xE7_val (js.foldl (fun v j => ggQ2xE7_D.simpleRefl (ggQ2xE7_idx j) v)
        (ggQ2xE7_D.simpleRefl (ggQ2xE7_idx j) v)) =
      js.foldl (fun w j => ggQ2xE7_act j w) (ggQ2xE7_act j (ggQ2xE7_val v))
    rw [ih (ggQ2xE7_D.simpleRefl (ggQ2xE7_idx j) v), ggQ2xE7_val_simpleRefl]

private lemma ggQ2xE7_evalH_val (w : List (Fin 7)) :
    ggQ2xE7_val (ggQ2xE7_evalH w) = ggQ2xE7_evalWord w := by
  cases w with
  | nil => rfl
  | cons k js =>
    exact ggQ2xE7_foldl_val js (ggQ2xE7_D.coroot (ggQ2xE7_idx k))

private lemma ggQ2xE7_words_ne_nil : ggQ2xE7_words.Forall (fun w => w ≠ []) := by
  decide +kernel

private lemma ggQ2xE7_TH_subset_orbit : ggQ2xE7_TH ⊆ ggQ2xE7_orbit := by
  intro v hv
  have hv' : ggQ2xE7_val v ∈ ggQ2xE7_wordList := by
    have h : ggQ2xE7_val v ∈ ggQ2xE7_T := hv
    simp only [ggQ2xE7_T_eq_wordList, Finset.mem_coe, List.mem_toFinset] at h
    exact h
  rw [ggQ2xE7_wordList, List.mem_map] at hv'
  obtain ⟨w, hw, hwe⟩ := hv'
  have hwne : w ≠ [] := (List.forall_iff_forall_mem.mp ggQ2xE7_words_ne_nil) w hw
  obtain ⟨k, js, rfl⟩ := List.exists_cons_of_ne_nil hwne
  have hveq : v = ggQ2xE7_evalH (k :: js) := by
    have h1 : ggQ2xE7_vecInv v = ggQ2xE7_vecInv (ggQ2xE7_evalH (k :: js)) := by
      apply Subtype.ext
      change ggQ2xE7_val v = ggQ2xE7_val (ggQ2xE7_evalH (k :: js))
      rw [ggQ2xE7_evalH_val]
      exact hwe.symm
    calc v = ggQ2xE7_vec (ggQ2xE7_vecInv v) := (ggQ2xE7_vec_vecInv v).symm
      _ = ggQ2xE7_vec (ggQ2xE7_vecInv (ggQ2xE7_evalH (k :: js))) := by rw [h1]
      _ = ggQ2xE7_evalH (k :: js) := ggQ2xE7_vec_vecInv _
  rw [hveq]
  exact ggQ2xE7_evalH_mem_orbit k js

private lemma ggQ2xE7_orbit_eq_TH : ggQ2xE7_orbit = ggQ2xE7_TH :=
  le_antisymm ggQ2xE7_orbit_subset_TH ggQ2xE7_TH_subset_orbit


private lemma ggQ2xE7_z_hc_eq (k : Fin 7) : ggQ2xE7_z k ⬝ᵥ ggQ2xE7_z k = 2 := by
  rw [ggQ2xE7_gram]; fin_cases k <;> decide

private lemma ggQ2xE7_z_hc (k : Fin 7) : ggQ2xE7_z k ⬝ᵥ ggQ2xE7_z k ≠ 0 := by
  rw [ggQ2xE7_z_hc_eq]; decide



private noncomputable def ggQ2xE7_tauD : ggQ2xE7_H ≃ₗ[ZMod 3] ggQ2xE7_D.V where
  toFun := ggQ2xE7_vec
  invFun := ggQ2xE7_vecInv
  left_inv := ggQ2xE7_vecInv_vec
  right_inv := ggQ2xE7_vec_vecInv
  map_add' v w := rfl
  map_smul' a v := rfl

private noncomputable def ggQ2xE7_resHomD :
    ggQ2xE7_K →* (ggQ2xE7_D.V ≃ₗ[ZMod 3] ggQ2xE7_D.V) :=
  (ggLinConj ggQ2xE7_tauD).toMonoidHom.comp ggQ2xE7_resHom

private lemma ggQ2xE7_resHomD_apply (g : ggQ2xE7_K) (x : ggQ2xE7_H) :
    ggQ2xE7_resHomD g (ggQ2xE7_vec x) = ggQ2xE7_vec (ggQ2xE7_resHom g x) := by
  change ggLinConj ggQ2xE7_tauD (ggQ2xE7_resHom g) (ggQ2xE7_vec x) =
    ggQ2xE7_vec (ggQ2xE7_resHom g x)
  rw [ggLinConj_apply, show ggQ2xE7_vec x = ggQ2xE7_tauD x from rfl,
    LinearEquiv.symm_apply_apply]
  rfl



private lemma ggQ2xE7_act_eq_refl (j : Fin 7) (v : GGBCV 8) :
    ggQ2xE7_act j v = ggBCRefl (ggQ2xE7_z j) (ggQ2xE7_z_hc j) v := by
  rw [ggQ2xE7_act, ggQ2xE7_ggBCRefl_apply]
  have h : ggQ2xE7_z j ⬝ᵥ ggQ2xE7_z j = 2 := by rw [ggQ2xE7_gram]; fin_cases j <;> decide
  rw [h, show (2 : ZMod 3) / 2 = 1 by decide +kernel, one_mul]

private lemma ggQ2xE7_val_coroot (k : ggQ2xE7_D.ι) :
    ggQ2xE7_val (ggQ2xE7_D.coroot k) = ggQ2xE7_z (ggQ2xE7_idx_inv k) := rfl

private lemma ggQ2xE7_val_simpleRefl_act (k : ggQ2xE7_D.ι) (v : ggQ2xE7_D.V) :
    ggQ2xE7_val (ggQ2xE7_D.simpleRefl k v) =
      ggQ2xE7_act (ggQ2xE7_idx_inv k) (ggQ2xE7_val v) := by
  have h := ggQ2xE7_val_simpleRefl (ggQ2xE7_idx_inv k) v
  rwa [show ggQ2xE7_idx (ggQ2xE7_idx_inv k) = k from rfl] at h

private lemma ggQ2xE7_weyl_isometry :
    ∀ w ∈ ggQ2xE7_D.weyl, ∀ x y : ggQ2xE7_D.V,
      ggQ2xE7_val (w x) ⬝ᵥ ggQ2xE7_val (w y) = ggQ2xE7_val x ⬝ᵥ ggQ2xE7_val y := by
  have hgen : ∀ u ∈ Set.range ggQ2xE7_D.simpleRefl, ∀ x y : ggQ2xE7_D.V,
      ggQ2xE7_val (u x) ⬝ᵥ ggQ2xE7_val (u y) = ggQ2xE7_val x ⬝ᵥ ggQ2xE7_val y := by
    rintro u ⟨k, rfl⟩ x y
    rw [ggQ2xE7_val_simpleRefl_act, ggQ2xE7_val_simpleRefl_act,
      ggQ2xE7_act_eq_refl, ggQ2xE7_act_eq_refl]
    exact ggQ2xE7_refl_isometry _ _ _ _
  intro w hw
  have hw' : w ∈ Subgroup.closure (Set.range ggQ2xE7_D.simpleRefl) :=
    (ggQ2xQ_mem_weyl_iff ggQ2xE7_D).1 hw
  exact Subgroup.closure_induction (G := ggQ2xE7_D.V ≃ₗ[ZMod 3] ggQ2xE7_D.V)
    (p := fun u _ => ∀ x y : ggQ2xE7_D.V,
      ggQ2xE7_val (u x) ⬝ᵥ ggQ2xE7_val (u y) = ggQ2xE7_val x ⬝ᵥ ggQ2xE7_val y)
    hgen (fun x y => rfl)
    (fun a b _ _ iha ihb => by
      intro x y
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, iha, ihb])
    (fun a _ iha => by
      intro x y
      have h := iha (a⁻¹ x) (a⁻¹ y)
      rw [show a (a⁻¹ x) = x from by simp [LinearEquiv.coe_inv],
        show a (a⁻¹ y) = y from by simp [LinearEquiv.coe_inv]] at h
      exact h.symm) hw'


private lemma ggQ2xE7_orbit_mem_T (w : ggQ2xE7_D.V ≃ₗ[ZMod 3] ggQ2xE7_D.V)
    (hw : w ∈ ggQ2xE7_D.weyl) (k : ggQ2xE7_D.ι) :
    ggQ2xE7_val (w (ggQ2xE7_D.coroot k)) ∈ ggQ2xE7_T :=
  ggQ2xE7_orbit_subset_TH ⟨w, hw, k, rfl⟩

private lemma ggQ2xE7_val_sub (y z : ggQ2xE7_D.V) :
    ggQ2xE7_val (y - z) = ggQ2xE7_val y - ggQ2xE7_val z := by
  show (ggQ2xE7_vecInv (y - z)).val = _
  rw [show ggQ2xE7_vecInv (y - z) = ggQ2xE7_vecInv y - ggQ2xE7_vecInv z from rfl,
    Submodule.coe_sub]
  rfl

private lemma ggQ2xE7_val_smul (a : ZMod 3) (y : ggQ2xE7_D.V) :
    ggQ2xE7_val (a • y) = a • ggQ2xE7_val y := by
  show (ggQ2xE7_vecInv (a • y)).val = _
  rw [show ggQ2xE7_vecInv (a • y) = a • ggQ2xE7_vecInv y from rfl, Submodule.coe_smul]
  rfl

private lemma ggQ2xE7_val_vec (y : ggQ2xE7_D.V) :
    ggQ2xE7_val (ggQ2xE7_vec y) = ggQ2xE7_val y := rfl

private lemma ggQ2xE7_val_vecInv (y : ggQ2xE7_H) :
    ggQ2xE7_val (ggQ2xE7_vec y) = (y : GGBCV 8) := rfl

private lemma ggQ2xE7_root_eq (k : ggQ2xE7_D.ι) (y : ggQ2xE7_D.V) :
    ggQ2xE7_D.root k y = ggQ2xE7_z (ggQ2xE7_idx_inv k) ⬝ᵥ ggQ2xE7_val y := by
  show ggBCDot (ggQ2xE7_z (ggQ2xE7_idx_inv k)) (ggQ2xE7_val y) = _
  rw [ggQ2xE7_ggBCDot_apply]

private lemma ggQ2xE7_val_refl_apply (v : GGBCV 8) (hc : v ⬝ᵥ v ≠ 0) (y : GGBCV 8) :
    ggBCRefl v hc y = y - (2 / (v ⬝ᵥ v) * (v ⬝ᵥ y)) • v :=
  ggQ2xE7_ggBCRefl_apply v hc y

private lemma ggQ2xE7_resHomD_refl_apply (v : GGBCV 8) (hv : v ∈ ggQ2xE7_T)
    (hc : v ⬝ᵥ v ≠ 0) (x : ggQ2xE7_D.V) :
    ggQ2xE7_val (ggQ2xE7_resHomD ⟨ggBCRefl v hc, ggQ2xE7_refl_mem_K v hv hc⟩ x) =
      ggBCRefl v hc (ggQ2xE7_val x) := by
  have hx : x = ggQ2xE7_vec (ggQ2xE7_vecInv x) := (ggQ2xE7_vec_vecInv x).symm
  rw [hx, ggQ2xE7_resHomD_apply]
  show ggBCRefl v hc (ggQ2xE7_vecInv x : GGBCV 8) = ggBCRefl v hc (ggQ2xE7_val x)
  rfl

private lemma ggQ2xE7_conj_simpleRefl_D (k : ggQ2xE7_D.ι)
    {w : ggQ2xE7_D.V ≃ₗ[ZMod 3] ggQ2xE7_D.V} (hw : w ∈ ggQ2xE7_D.weyl)
    (hc : ggQ2xE7_val (w (ggQ2xE7_D.coroot k)) ⬝ᵥ ggQ2xE7_val (w (ggQ2xE7_D.coroot k)) ≠ 0) :
    w * ggQ2xE7_D.simpleRefl k * w⁻¹ =
      ggQ2xE7_resHomD ⟨ggBCRefl (ggQ2xE7_val (w (ggQ2xE7_D.coroot k))) hc,
        ggQ2xE7_refl_mem_K _ (ggQ2xE7_orbit_mem_T w hw k) hc⟩ := by
  have hvv : ggQ2xE7_val (w (ggQ2xE7_D.coroot k)) ⬝ᵥ ggQ2xE7_val (w (ggQ2xE7_D.coroot k)) = 2 := by
    rw [ggQ2xE7_weyl_isometry w hw (ggQ2xE7_D.coroot k) (ggQ2xE7_D.coroot k), ggQ2xE7_val_coroot]
    exact ggQ2xE7_z_hc_eq (ggQ2xE7_idx_inv k)
  refine LinearEquiv.ext (fun x => ?_)
  apply Subtype.ext
  change ggQ2xE7_val (w (ggQ2xE7_D.simpleRefl k (w⁻¹ x))) =
    ggQ2xE7_val (ggQ2xE7_resHomD ⟨ggBCRefl (ggQ2xE7_val (w (ggQ2xE7_D.coroot k))) hc, _⟩ x)
  rw [ggQ2xE7_resHomD_refl_apply (ggQ2xE7_val (w (ggQ2xE7_D.coroot k)))
    (ggQ2xE7_orbit_mem_T w hw k) hc, ggQ2xE7_ggBCRefl_apply]
  have hsimple : ggQ2xE7_D.simpleRefl k (w⁻¹ x) =
      (w⁻¹ x) - (ggQ2xE7_D.root k (w⁻¹ x)) • ggQ2xE7_D.coroot k :=
    Module.reflection_apply (h := ggQ2xE7_D.root_coroot_self k) (w⁻¹ x)
  rw [hsimple, map_sub, map_smul]
  rw [show w (w⁻¹ x) = x from by simp [LinearEquiv.coe_inv]]
  have hroot : ggQ2xE7_D.root k (w⁻¹ x) =
      ggQ2xE7_val (w (ggQ2xE7_D.coroot k)) ⬝ᵥ ggQ2xE7_val x := by
    rw [ggQ2xE7_root_eq]
    have h := ggQ2xE7_weyl_isometry w hw (ggQ2xE7_D.coroot k) (w⁻¹ x)
    rw [show w (w⁻¹ x) = x from by simp [LinearEquiv.coe_inv]] at h
    rw [ggQ2xE7_val_coroot] at h
    exact h.symm
  rw [hroot, hvv, show (2 : ZMod 3) / 2 = 1 by decide +kernel, one_mul]
  rw [ggQ2xE7_val_sub, ggQ2xE7_val_smul]


private def ggQ2xE7_TK : Set ggQ2xE7_K := {t | t.val ∈ ggBCReflSet ggQ2xE7_T}

private noncomputable def ggQ2xE7_ΓK : Subgroup ggQ2xE7_K :=
  (ggBCReflGp ggQ2xE7_T).comap ggQ2xE7_K.subtype

private lemma ggQ2xE7_resHomD_refl' (k : ggQ2xE7_D.ι) :
    ggQ2xE7_resHomD ⟨ggBCRefl (ggQ2xE7_z (ggQ2xE7_idx_inv k)) (ggQ2xE7_z_hc _),
      ggQ2xE7_refl_mem_K _ (ggQ2xE7_z_mem_T _) _⟩ = ggQ2xE7_D.simpleRefl k := by
  refine LinearEquiv.ext (fun x => ?_)
  conv_lhs => rw [show x = ggQ2xE7_vec (ggQ2xE7_vecInv x) from (ggQ2xE7_vec_vecInv x).symm]
  rw [ggQ2xE7_resHomD_apply, ggQ2xE7_resHom_refl (ggQ2xE7_idx_inv k) (ggQ2xE7_z_hc _)]
  rfl

private lemma ggQ2xE7_resHomD_weyl_subset :
    ggQ2xE7_D.weyl ≤ ggQ2xE7_ΓK.map ggQ2xE7_resHomD := by
  have h : ggQ2xE7_D.weyl = Subgroup.closure (Set.range ggQ2xE7_D.simpleRefl) := by
    ext w; exact ggQ2xQ_mem_weyl_iff ggQ2xE7_D
  rw [h, Subgroup.closure_le]
  rintro _ ⟨k, rfl⟩
  refine ⟨⟨ggBCRefl (ggQ2xE7_z (ggQ2xE7_idx_inv k)) (ggQ2xE7_z_hc _),
    ggQ2xE7_refl_mem_K _ (ggQ2xE7_z_mem_T _) _⟩, ?_, ggQ2xE7_resHomD_refl' k⟩
  exact Subgroup.subset_closure
    ⟨ggQ2xE7_z (ggQ2xE7_idx_inv k), ggQ2xE7_z_mem_T _, ggQ2xE7_z_hc _, rfl⟩



private lemma ggQ2xE7_ggBCRefl_hc (v : GGBCV 8) (h1 h2 : v ⬝ᵥ v ≠ 0) :
    ggBCRefl v h1 = ggBCRefl v h2 := by
  refine LinearEquiv.ext (fun y => ?_)
  rw [ggQ2xE7_ggBCRefl_apply v h1 y]




private lemma ggQ2xE7_val_mk (v : GGBCV 8) (h : v ∈ ggQ2xE7_H) :
    ggQ2xE7_val (⟨v, h⟩ : ggQ2xE7_D.V) = v := rfl




private lemma ggQ2xE7_conj_simpleRefl_D_symm (k : ggQ2xE7_D.ι)
    {w : ggQ2xE7_D.V ≃ₗ[ZMod 3] ggQ2xE7_D.V} (hw : w ∈ ggQ2xE7_D.weyl)
    (hc : ggQ2xE7_val (w (ggQ2xE7_D.coroot k)) ⬝ᵥ ggQ2xE7_val (w (ggQ2xE7_D.coroot k)) ≠ 0) :
    w * ggQ2xE7_D.simpleRefl k * w.symm =
      ggQ2xE7_resHomD ⟨ggBCRefl (ggQ2xE7_val (w (ggQ2xE7_D.coroot k))) hc,
        ggQ2xE7_refl_mem_K _ (ggQ2xE7_orbit_mem_T w hw k) hc⟩ := by
  rw [show w.symm = w⁻¹ from rfl]
  exact ggQ2xE7_conj_simpleRefl_D k hw hc

private lemma ggQ2xE7_refl_mem_T (c : GGBCV 8) (hcT : c ∈ ggQ2xE7_T)
    (hc : c ⬝ᵥ c ≠ 0) (v : GGBCV 8) (hv : v ∈ ggQ2xE7_T) : ggBCRefl c hc v ∈ ggQ2xE7_T := by
  have hcTH : (⟨c, ggQ2xE7_T_subset_H hcT⟩ : ggQ2xE7_D.V) ∈ ggQ2xE7_TH := hcT
  rw [← ggQ2xE7_orbit_eq_TH] at hcTH
  obtain ⟨w, hw, k, hwk⟩ := hcTH
  have hcv : c = ggQ2xE7_val (w (ggQ2xE7_D.coroot k)) := by
    have h := congrArg (fun e : ggQ2xE7_D.V => ggQ2xE7_val e) hwk
    rw [ggQ2xE7_val_mk] at h
    exact h.symm
  have hc' : ggQ2xE7_val (w (ggQ2xE7_D.coroot k)) ⬝ᵥ ggQ2xE7_val (w (ggQ2xE7_D.coroot k)) ≠ 0 := by
    rw [ggQ2xE7_weyl_isometry w hw (ggQ2xE7_D.coroot k) (ggQ2xE7_D.coroot k), ggQ2xE7_val_coroot,
      ggQ2xE7_z_hc_eq]
    decide
  have hconj := ggQ2xE7_conj_simpleRefl_D_symm k hw hc'
  set x : ggQ2xE7_D.V := ⟨v, ggQ2xE7_T_subset_H hv⟩ with hx
  have hxv : ggQ2xE7_val x = v := by rw [hx]; rfl
  have hxT : x ∈ ggQ2xE7_TH := hv
  have hwx : w x ∈ ggQ2xE7_TH := by
    have hw' := ggQ2xE7_weyl_image_TH w hw
    have hmem : w x ∈ w '' ggQ2xE7_TH := ⟨x, hxT, rfl⟩
    rwa [hw'] at hmem
  have hw1 : w.symm '' ggQ2xE7_TH = ggQ2xE7_TH :=
    ggQ2xE7_weyl_image_TH w.symm (Subgroup.inv_mem ggQ2xE7_D.weyl hw)
  have h1 : w.symm x ∈ ggQ2xE7_TH := by
    rw [← hw1]
    exact ⟨x, hxT, rfl⟩
  have h1T : ggQ2xE7_val (w.symm x) ∈ ggQ2xE7_T := h1
  have h2 : ggQ2xE7_D.simpleRefl k (w.symm x) ∈ ggQ2xE7_TH := by
    show ggQ2xE7_val (ggQ2xE7_D.simpleRefl k (w.symm x)) ∈ ggQ2xE7_T
    rw [ggQ2xE7_val_simpleRefl_act]
    rw [ggQ2xE7_T_eq_wordList] at h1T ⊢
    rw [Finset.mem_coe, List.mem_toFinset] at h1T ⊢
    exact (List.forall_iff_forall_mem.mp (ggQ2xE7_T_closed (ggQ2xE7_idx_inv k))) _ h1T
  have h3 : w (ggQ2xE7_D.simpleRefl k (w.symm x)) ∈ ggQ2xE7_TH := by
    have hw' := ggQ2xE7_weyl_image_TH w hw
    have hmem : w (ggQ2xE7_D.simpleRefl k (w.symm x)) ∈ w '' ggQ2xE7_TH :=
      ⟨ggQ2xE7_D.simpleRefl k (w.symm x), h2, rfl⟩
    rwa [hw'] at hmem
  have hval : ggQ2xE7_val (w (ggQ2xE7_D.simpleRefl k (w.symm x))) = ggBCRefl c hc v := by
    have e1 : w (ggQ2xE7_D.simpleRefl k (w.symm x)) = (w * ggQ2xE7_D.simpleRefl k * w.symm) x := by
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    rw [e1, hconj, ggQ2xE7_resHomD_refl_apply (ggQ2xE7_val (w (ggQ2xE7_D.coroot k)))
      (ggQ2xE7_orbit_mem_T w hw k) hc']
    rw [hxv]
    subst hcv
    rw [ggQ2xE7_ggBCRefl_hc _ hc' hc]
  rw [← hval]
  exact h3



private lemma ggQ2xE7_reflGp_image_T :
    ∀ b ∈ ggBCReflGp ggQ2xE7_T, b '' ggQ2xE7_T = ggQ2xE7_T := by
  intro b hb
  refine Subgroup.closure_induction (G := GGBCV 8 ≃ₗ[ZMod 3] GGBCV 8)
    (p := fun b _ => b '' ggQ2xE7_T = ggQ2xE7_T) ?_ ?_ ?_ ?_ hb
  · rintro u ⟨c, hcT, hcc, rfl⟩
    refine le_antisymm ?_ ?_
    · rintro _ ⟨v, hv, rfl⟩
      exact ggQ2xE7_refl_mem_T c hcT hcc v hv
    · intro v hv
      exact ⟨ggBCRefl c hcc v, ggQ2xE7_refl_mem_T c hcT hcc v hv,
        ggQ2xE7_refl_involutive c hcc v⟩
  · exact Set.image_id _
  · intro a b _ _ iha ihb
    rw [show (a * b) '' ggQ2xE7_T = a '' (b '' ggQ2xE7_T) from by
      rw [show (⇑(a * b) : GGBCV 8 → GGBCV 8) = (⇑a) ∘ (⇑b) from by
        funext x; simp [LinearEquiv.mul_apply]]
      exact Set.image_comp (⇑a) (⇑b) ggQ2xE7_T]
    rw [ihb, iha]
  · intro a _ iha
    conv_lhs => rw [← iha]
    rw [← Set.image_comp]
    rw [show (⇑a⁻¹) ∘ (⇑a) = (id : GGBCV 8 → GGBCV 8) from by
      funext x; simp [LinearEquiv.coe_inv]]
    exact Set.image_id _

private lemma ggQ2xE7_reflGp_mem_T :
    ∀ b ∈ ggBCReflGp ggQ2xE7_T, ∀ v ∈ ggQ2xE7_T, b v ∈ ggQ2xE7_T := by
  intro b hb v hv
  have h := ggQ2xE7_reflGp_image_T b hb
  have hmem : b v ∈ b '' ggQ2xE7_T := ⟨v, hv, rfl⟩
  rwa [h] at hmem



private lemma ggQ2xE7_conj_simpleRefl_D_inv (k : ggQ2xE7_D.ι)
    {w : ggQ2xE7_D.V ≃ₗ[ZMod 3] ggQ2xE7_D.V} (hw : w ∈ ggQ2xE7_D.weyl)
    (hc : ggQ2xE7_val (w (ggQ2xE7_D.coroot k)) ⬝ᵥ ggQ2xE7_val (w (ggQ2xE7_D.coroot k)) ≠ 0) :
    w * ggQ2xE7_D.simpleRefl k * w⁻¹ =
      ggQ2xE7_resHomD ⟨ggBCRefl (ggQ2xE7_val (w (ggQ2xE7_D.coroot k))) hc,
        ggQ2xE7_refl_mem_K _ (ggQ2xE7_orbit_mem_T w hw k) hc⟩ :=
  ggQ2xE7_conj_simpleRefl_D_symm k hw hc

private lemma ggQ2xE7_resHomD_TK :
    ggQ2xE7_resHomD '' ggQ2xE7_TK = ggQ2xQ_isConjRefl ggQ2xE7_D := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨u, hu, rfl⟩
    obtain ⟨v, hv, hc, hval⟩ := hu
    have hu' : u = ⟨ggBCRefl v hc, ggQ2xE7_refl_mem_K v hv hc⟩ := Subtype.ext hval
    rw [hu']
    have hvTH : (⟨v, ggQ2xE7_T_subset_H hv⟩ : ggQ2xE7_D.V) ∈ ggQ2xE7_TH := hv
    rw [← ggQ2xE7_orbit_eq_TH] at hvTH
    obtain ⟨w, hw, k, hwk⟩ := hvTH
    have hcv : v = ggQ2xE7_val (w (ggQ2xE7_D.coroot k)) := by
      have h := congrArg (fun e : ggQ2xE7_D.V => ggQ2xE7_val e) hwk
      rw [ggQ2xE7_val_mk] at h
      exact h.symm
    have hc' : ggQ2xE7_val (w (ggQ2xE7_D.coroot k)) ⬝ᵥ
        ggQ2xE7_val (w (ggQ2xE7_D.coroot k)) ≠ 0 := by
      rw [ggQ2xE7_weyl_isometry w hw (ggQ2xE7_D.coroot k) (ggQ2xE7_D.coroot k), ggQ2xE7_val_coroot,
        ggQ2xE7_z_hc_eq]
      decide
    refine ⟨k, w, hw, ?_⟩
    have hEq : (⟨ggBCRefl v hc, ggQ2xE7_refl_mem_K v hv hc⟩ : ggQ2xE7_K) =
        ⟨ggBCRefl (ggQ2xE7_val (w (ggQ2xE7_D.coroot k))) hc',
          ggQ2xE7_refl_mem_K _ (ggQ2xE7_orbit_mem_T w hw k) hc'⟩ := by
      apply Subtype.ext
      show ggBCRefl v hc = ggBCRefl (ggQ2xE7_val (w (ggQ2xE7_D.coroot k))) hc'
      subst hcv
      exact (ggQ2xE7_ggBCRefl_hc _ hc' hc).symm
    rw [hEq]
    exact (ggQ2xE7_conj_simpleRefl_D_inv k hw hc').symm
  · rintro t ⟨k, w, hw, rfl⟩
    obtain ⟨W, hW, hWres⟩ := ggQ2xE7_resHomD_weyl_subset hw
    refine ⟨W * ⟨ggBCRefl (ggQ2xE7_z (ggQ2xE7_idx_inv k)) (ggQ2xE7_z_hc _),
      ggQ2xE7_refl_mem_K _ (ggQ2xE7_z_mem_T _) _⟩ * W⁻¹, ?_, ?_⟩
    · have hiso : ∀ x y, (W.val x) ⬝ᵥ (W.val y) = x ⬝ᵥ y :=
        ggQ2xE7_reflGp_isometry W.val hW
      have hcW : W.val (ggQ2xE7_z (ggQ2xE7_idx_inv k)) ⬝ᵥ
          W.val (ggQ2xE7_z (ggQ2xE7_idx_inv k)) ≠ 0 := by
        rw [hiso]; exact ggQ2xE7_z_hc _
      have hcW' : W.val (ggQ2xE7_z (ggQ2xE7_idx_inv k)) ⬝ᵥ
          W.val (ggQ2xE7_z (ggQ2xE7_idx_inv k)) ≠ 0 := by
        rw [hiso]; exact ggQ2xE7_z_hc _
      change (W * ⟨ggBCRefl (ggQ2xE7_z (ggQ2xE7_idx_inv k)) (ggQ2xE7_z_hc _),
        ggQ2xE7_refl_mem_K _ (ggQ2xE7_z_mem_T _) _⟩ * W⁻¹).val ∈ ggBCReflSet ggQ2xE7_T
      rw [show (W * ⟨ggBCRefl (ggQ2xE7_z (ggQ2xE7_idx_inv k)) (ggQ2xE7_z_hc _),
          ggQ2xE7_refl_mem_K _ (ggQ2xE7_z_mem_T _) _⟩ * W⁻¹).val =
          ggBCRefl (W.val (ggQ2xE7_z (ggQ2xE7_idx_inv k))) hcW from by
        show (W.val : GGBCV 8 ≃ₗ[ZMod 3] GGBCV 8) *
          ggBCRefl (ggQ2xE7_z (ggQ2xE7_idx_inv k)) (ggQ2xE7_z_hc _) *
          (W.val : GGBCV 8 ≃ₗ[ZMod 3] GGBCV 8)⁻¹ =
          ggBCRefl (W.val (ggQ2xE7_z (ggQ2xE7_idx_inv k))) hcW
        rw [ggQ2xE7_ggBCRefl_hc (W.val (ggQ2xE7_z (ggQ2xE7_idx_inv k))) hcW' hcW]
        exact ggQ2xE7_conj_refl W.val hiso (ggQ2xE7_z (ggQ2xE7_idx_inv k)) (ggQ2xE7_z_hc _)]
      exact ⟨W.val (ggQ2xE7_z (ggQ2xE7_idx_inv k)),
        ggQ2xE7_reflGp_mem_T W.val hW _ (ggQ2xE7_z_mem_T _), hcW, rfl⟩
    · rw [map_mul, map_mul, map_inv, hWres, ggQ2xE7_resHomD_refl' k]


private lemma ggQ2xE7_wordList_dot : ggQ2xE7_wordList.Forall (fun c => c ⬝ᵥ c = 2) := by
  decide +kernel

private lemma ggQ2xE7_dot_self_of_mem_T (c : GGBCV 8) (hc : c ∈ ggQ2xE7_T) : c ⬝ᵥ c = 2 := by
  have hcW : c ∈ ggQ2xE7_wordList := by
    rwa [ggQ2xE7_T_eq_wordList, Finset.mem_coe, List.mem_toFinset] at hc
  exact (List.forall_iff_forall_mem.mp ggQ2xE7_wordList_dot) c hcW

private lemma ggQ2xE7_resHomD_injective : Function.Injective ggQ2xE7_resHomD := by
  intro g h hgh
  apply ggQ2xE7_resHom_injective
  have := congrArg (fun e : ggQ2xE7_D.V ≃ₗ[ZMod 3] ggQ2xE7_D.V =>
    (ggLinConj ggQ2xE7_tauD).symm e) hgh
  simpa [ggQ2xE7_resHomD] using this

private lemma ggQ2xE7_reflSet_subset_K : ∀ t ∈ ggBCReflSet ggQ2xE7_T, t ∈ ggQ2xE7_K := by
  rintro t ⟨c, hcT, hc, rfl⟩
  exact ggQ2xE7_refl_mem_K c hcT hc

private lemma ggQ2xE7_reflGp_subset_K : ∀ t ∈ ggBCReflGp ggQ2xE7_T, t ∈ ggQ2xE7_K := by
  intro t ht
  exact Subgroup.closure_induction (p := fun t _ => t ∈ ggQ2xE7_K)
    (fun u hu => ggQ2xE7_reflSet_subset_K u hu) (Subgroup.one_mem _)
    (fun a b _ _ iha ihb => Subgroup.mul_mem _ iha ihb)
    (fun a _ iha => Subgroup.inv_mem _ iha) ht


private lemma ggQ2xE7_TK_hTc : ∀ s ∈ ggQ2xE7_TK, ∀ t ∈ ggQ2xE7_TK,
    s * t * s⁻¹ ∈ ggQ2xE7_TK := by
  intro s hs t ht
  obtain ⟨c, hcT, hc, hsval⟩ := hs
  obtain ⟨d, hdT, hd, htval⟩ := ht
  have hs' : s = ⟨ggBCRefl c hc, ggQ2xE7_refl_mem_K c hcT hc⟩ := Subtype.ext hsval
  have ht' : t = ⟨ggBCRefl d hd, ggQ2xE7_refl_mem_K d hdT hd⟩ := Subtype.ext htval
  change (s * t * s⁻¹).val ∈ ggBCReflSet ggQ2xE7_T
  rw [hs', ht']
  have hconj := ggQ2xE7_conj_refl (ggBCRefl c hc) (ggQ2xE7_refl_isometry c hc) d hd
  have hmem : ggBCRefl c hc d ∈ ggQ2xE7_T := ggQ2xE7_refl_mem_T c hcT hc d hdT
  refine ⟨ggBCRefl c hc d, hmem, ?_, ?_⟩
  · rw [ggQ2xE7_refl_isometry c hc d d, ggQ2xE7_dot_self_of_mem_T d hdT]; decide
  · show ((⟨ggBCRefl c hc, ggQ2xE7_refl_mem_K c hcT hc⟩ : ggQ2xE7_K) *
      (⟨ggBCRefl d hd, ggQ2xE7_refl_mem_K d hdT hd⟩ : ggQ2xE7_K) *
      (⟨ggBCRefl c hc, ggQ2xE7_refl_mem_K c hcT hc⟩ : ggQ2xE7_K)⁻¹).val =
      ggBCRefl (ggBCRefl c hc d) _
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hconj

private lemma ggQ2xE7_subtype_TK : ggQ2xE7_K.subtype '' ggQ2xE7_TK = ggBCReflSet ggQ2xE7_T := by
  ext t; constructor
  · rintro ⟨u, hu, rfl⟩; exact hu
  · intro ht; exact ⟨⟨t, ggQ2xE7_reflSet_subset_K t ht⟩, ht, rfl⟩

private lemma ggQ2xE7_subtype_ΓK : ggQ2xE7_K.subtype '' ggQ2xE7_ΓK = ggBCReflGp ggQ2xE7_T := by
  ext t; constructor
  · rintro ⟨u, hu, rfl⟩; exact hu
  · intro ht; exact ⟨⟨t, ggQ2xE7_reflGp_subset_K t ht⟩, ht, rfl⟩

theorem ggQ2_A_inner_E7 :
    GGQ2QuandleInner (ggBCReflSet (ggARoots 8 ∪ {z | ggAType4 z}))
      (ggBCReflGp (ggARoots 8 ∪ {z | ggAType4 z})) := by
  have hinner : GGQ2QuandleInner (ggQ2xE7_resHomD '' ggQ2xE7_TK)
      (ggQ2xE7_D.weyl : Set _) := by
    rw [ggQ2xE7_resHomD_TK]
    exact ggQ2xE7_D_inner
  have hΓ : (ggQ2xE7_D.weyl : Set _) ⊆ ggQ2xE7_resHomD '' ggQ2xE7_ΓK :=
    ggQ2xE7_resHomD_weyl_subset
  have hK := ggQ2_inner_of_hom ggQ2xE7_resHomD ggQ2xE7_resHomD_injective
    ggQ2xE7_TK_hTc hinner hΓ
  have hK' := ggQ2_inner_image ggQ2xE7_K.subtype (fun a b h => Subtype.ext h)
    ggQ2xE7_TK_hTc hK
  rwa [ggQ2xE7_subtype_TK, ggQ2xE7_subtype_ΓK] at hK'

end CFSG.StandardType

end
