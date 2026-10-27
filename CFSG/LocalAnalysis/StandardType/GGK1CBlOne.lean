module

public import CFSG.LocalAnalysis.StandardType.GGK1CCoDefs
public import CFSG.LocalAnalysis.StandardType.GGK1CBlDefs
public import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.Classical (spEnd IsReciprocalTransversal SpPrimaryBlocks spSupported
  symplectic_cross_prime_primary_centralizer_blocks)
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)

private theorem ggK1On_sum_eq_headD_add_sum_tail (m : List ℕ) :
    m.sum = m.headD 0 + m.tail.sum := by
  cases m <;> rfl

private theorem ggK1On_getD_eq_zero_of_sum_eq_zero (l : List ℕ) (h : l.sum = 0) :
    ∀ k, l.getD k 0 = 0 := by
  induction l with
  | nil => intro k; rfl
  | cons a t ih =>
      simp only [List.sum_cons] at h
      have ha : a = 0 := by omega
      have ht : t.sum = 0 := by omega
      intro k
      cases k with
      | zero => simpa using ha
      | succ k => rw [List.getD_cons_succ]; exact ih ht k

private theorem ggK1On_getD_succ_eq_tail_getD (m : List ℕ) (k : ℕ) :
    m.getD (k + 1) 0 = m.tail.getD k 0 := by
  cases m <;> rfl

theorem ggK1CBl_preblocks_one {p nf d r : ℕ} {K : Type} [Field K] [Finite K]
    (hnf : 1 ≤ nf) (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1) (hK : Nat.card K = 2 ^ nf)
    {x : ↥(StatedSp r K)} {m : List ℕ} (hm : GGK1CMultOf p nf d r K x m)
    (hx : x ^ p = 1) (hx1 : x = 1) :
    Nonempty (ggK1CBl_PreBlocks p nf d r K x m) := by
  classical
  have hsp : spEnd x = (1 : Module.End K (Fin r ⊕ Fin r → K)) := by
    rw [hx1]
    simp [spEnd, CFSG.RankThree.Classical.spLin]
  have hpc : primaryComponent (spEnd x) (X - 1) = ⊤ := by
    rw [hsp]
    simp [primaryComponent]
  have hfinV : Module.finrank K (Fin r ⊕ Fin r → K) = 2 * r := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega
  have hm0r : m.headD 0 = r := by
    rw [hm.head_eq, hpc, finrank_top, hfinV]
    omega
  have hsum_tail : m.tail.sum = 0 := by
    have h := ggK1On_sum_eq_headD_add_sum_tail m
    rw [hm.sum_eq, hm0r] at h
    omega
  have hget : ∀ j, 1 ≤ j → m.getD j 0 = 0 := by
    intro j hj
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    rw [ggK1On_getD_succ_eq_tail_getD]
    exact ggK1On_getD_eq_zero_of_sum_eq_zero m.tail hsum_tail k
  have htail : (List.range ((p - 1) / 2 + 1)).filter
      (fun j => decide (1 ≤ j ∧ 1 ≤ m.getD j 0)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro j hj
    by_cases hj1 : 1 ≤ j
    · have hz := hget j hj1
      rw [decide_eq_true_eq]
      omega
    · simp [hj1]
  have hExp : ggK1CCo_expectedKinds p nf d m =
      (if m.headD 0 = 0 then 0 else {ggK1CCo_Kind.sp (m.headD 0)}) := by
    rw [ggK1CCo_expectedKinds, ggK1CCo_expectedKindList, htail]
    split_ifs <;> simp
  let ι := Subtype (fun _ : Unit => m.headD 0 ≠ 0)
  have hB : (Finset.univ : Finset ι).val.map
        (fun _ : ι => ggK1CCo_Kind.sp (m.headD 0)) =
      (if m.headD 0 = 0 then 0 else {ggK1CCo_Kind.sp (m.headD 0)}) := by
    by_cases h0 : m.headD 0 = 0
    · rw [if_pos h0]
      haveI : IsEmpty ι := ⟨fun z => z.2 h0⟩
      rw [Finset.univ_eq_empty]
      simp
    · rw [if_neg h0]
      have hsub : (Finset.univ : Finset ι) = {⟨(), h0⟩} := by
        rw [Finset.eq_singleton_iff_unique_mem]
        exact ⟨Finset.mem_univ _, fun z _ => Subtype.ext (Subsingleton.elim _ _)⟩
      rw [hsub]
      simp
  have hwit : ∀ _ : ι, ggK1CBl_KindWitness nf K (ggK1CCo_Kind.sp (m.headD 0))
      (⊤ : Subgroup (StatedSp r K)) := by
    intro i
    have hpos : 1 ≤ m.headD 0 := Nat.pos_of_ne_zero i.2
    unfold ggK1CBl_KindWitness
    refine ⟨hpos, Fin r ⊕ Fin r → K, inferInstance, inferInstance, inferInstance,
      CFSG.RankThree.Classical.spForm r K, CFSG.RankThree.Classical.spForm_isAlt,
      CFSG.RankThree.Classical.spForm_nondegenerate, ?_, ?_⟩
    · rw [hfinV, hm0r]
    · exact ⟨(Subgroup.topEquiv).trans
        ((MonoidHom.ofInjective CFSG.RankThree.Classical.spLin_injective).trans
          (MulEquiv.subgroupCongr CFSG.RankThree.Classical.range_spLin))⟩
  refine ⟨⟨ι, (fun _ => ⊤), (fun _ => ggK1CCo_Kind.sp (m.headD 0)), ?_, ?_, ?_, ?_, ?_⟩⟩
  ·
    intro i j hij
    exact absurd (Subsingleton.elim i j) hij
  ·
    have hcent : Subgroup.centralizer ({1} : Set ↥(StatedSp r K)) = ⊤ := by
      rw [Subgroup.centralizer_eq_top_iff_subset, Set.singleton_subset_iff]
      exact Subgroup.mem_center_iff.mpr (fun g => by simp)
    rw [hx1, hcent]
    by_cases h0 : m.headD 0 = 0
    · haveI : IsEmpty ι := ⟨fun z => z.2 h0⟩
      have hr0 : r = 0 := by omega
      haveI : Subsingleton ↥(StatedSp r K) := by rw [hr0]; exact inferInstance
      have hempty : (⨆ _ : ι, (⊤ : Subgroup (StatedSp r K))) = ⊥ := by
        apply le_antisymm _ bot_le
        apply iSup_le
        intro i
        exact (IsEmpty.false i).elim
      rw [hempty]
      apply le_antisymm bot_le
      intro y _
      rw [Subgroup.mem_bot]
      exact Subsingleton.elim y 1
    · haveI : Nonempty ι := ⟨⟨(), h0⟩⟩
      exact iSup_const
  ·
    intro i
    have h : (⨆ j : ι, ⨆ (_ : j ≠ i), (⊤ : Subgroup (StatedSp r K))) = ⊥ := by
      apply le_antisymm _ bot_le
      apply iSup_le; intro j
      apply iSup_le; intro hji
      exact (hji (Subsingleton.elim j i)).elim
    rw [h]
    exact disjoint_bot_right
  ·
    rw [hB, hExp]
  · exact hwit

end CFSG.StandardType

end
