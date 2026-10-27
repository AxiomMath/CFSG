module

public import CFSG.OddTranspositions.PartThree.Ten.WreathEndgame
public import CFSG.Timmesfeld.Bridge.Asc72Basic
import CFSG.OddTranspositions.PartThree.EightEight.WreathNatural
import CFSG.OddTranspositions.PartThree.Ten.SwapKlein
import CFSG.Timmesfeld.Bridge.OddLocalCommonBasic
import CFSG.OddTranspositions.SymSixQHyp
import CFSG.Timmesfeld.Bridge.Asc72Lift
import CFSG.Timmesfeld.Transvection.Statement

public section

namespace CFSG.OddTranspositions.PartThree.EightEight

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.BenderSuzuki
open Equiv SemidirectProduct
open CFSG.OddTranspositions.PartThree.WreathEndgame
open CFSG.OddTranspositions.PartThree.SwapKlein
open CFSG.Timmesfeld.Bridge (commSet)

private theorem commute_inr_swp_iff_w4w {f m : ℕ} {g : PSL2Model f} {i j : Fin m}
    (hij : i ≠ j) :
    Commute (inr (swap i j) : L2Wreath f m) (swp g i j) ↔ g * g = 1 := by
  rw [← swp_one_eq_inr]
  rw [Commute.symm_iff, commute_swp_swp_iff g 1 hij]
  simp

private theorem commute_swp_swp_iff_commute_w4w {f m : ℕ} {c c' : PSL2Model f}
    (hc : c * c = 1) (hc' : c' * c' = 1) {i j : Fin m} (hij : i ≠ j) :
    Commute (swp c i j) (swp c' i j) ↔ Commute c c' := by
  rw [Commute.symm_iff, commute_swp_swp_iff c' c hij]
  have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc
  have hc'i : c'⁻¹ = c' := inv_eq_of_mul_eq_one_right hc'
  constructor
  · intro h
    rw [hci] at h
    have h' : (c' * c)⁻¹ = c' * c := inv_eq_of_mul_eq_one_right h
    rw [mul_inv_rev, hci, hc'i] at h'
    exact h'
  · intro h
    rw [hci]
    calc c' * c * (c' * c) = c * c' * (c' * c) := by rw [h.eq]
      _ = c * (c' * c') * c := by group
      _ = c * 1 * c := by rw [hc']
      _ = 1 := by simp [hc]

private theorem conj_mem_swapSet_iff_w4w {f m : ℕ} (g : L2Wreath f m) {x : L2Wreath f m} :
    g * x * g⁻¹ ∈ swapSet f m ↔ x ∈ swapSet f m := by
  constructor
  · intro h
    have := conj_mem_swapSet g⁻¹ h
    simpa [mul_assoc] using this
  · exact conj_mem_swapSet g

private theorem mem_commSet_commSet_iff_w4w {f k : ℕ} {a b x : L2Wreath f k} :
    x ∈ commSet (commSet (swapSet f k) a) b ↔
      x ∈ {c | c ∈ swapSet f k ∧ Commute a c ∧ Commute b c ∧ c ≠ a ∧ c ≠ b} := by
  simp only [commSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨hxS, hxa, hxane⟩, hxb, hxbne⟩
    exact ⟨hxS, hxa.symm, hxb.symm, hxane, hxbne⟩
  · rintro ⟨hxS, hax, hbx, hxane, hxbne⟩
    exact ⟨⟨hxS, hax.symm, hxane⟩, hbx.symm, hxbne⟩

private theorem conj_mem_commSet_commSet_iff_w4w {f k : ℕ} (c : L2Wreath f k)
    (a b x : L2Wreath f k) :
    c * x * c⁻¹ ∈ commSet (commSet (swapSet f k) a) b ↔
      x ∈ commSet (commSet (swapSet f k) (c⁻¹ * a * c)) (c⁻¹ * b * c) := by
  simp only [commSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨hxS, hxa, hxane⟩, hxb, hxbne⟩
    refine ⟨⟨(conj_mem_swapSet_iff_w4w c).1 hxS, ?_, ?_⟩, ?_, ?_⟩
    · exact (Commute.conj_iff c).1 (by simpa [mul_assoc] using hxa)
    · intro h
      apply hxane
      calc c * x * c⁻¹ = c * (c⁻¹ * a * c) * c⁻¹ := by rw [h]
        _ = a := by group
    · exact (Commute.conj_iff c).1 (by simpa [mul_assoc] using hxb)
    · intro h
      apply hxbne
      calc c * x * c⁻¹ = c * (c⁻¹ * b * c) * c⁻¹ := by rw [h]
        _ = b := by group
  · rintro ⟨⟨hxS, hxa, hxane⟩, hxb, hxbne⟩
    refine ⟨⟨conj_mem_swapSet c hxS, ?_, ?_⟩, ?_, ?_⟩
    · have := (Commute.conj_iff c).2 hxa
      simpa [mul_assoc] using this
    · intro h
      apply hxane
      calc x = c⁻¹ * (c * x * c⁻¹) * c := by group
        _ = c⁻¹ * a * c := by rw [h]
    · have := (Commute.conj_iff c).2 hxb
      simpa [mul_assoc] using this
    · intro h
      apply hxbne
      calc x = c⁻¹ * (c * x * c⁻¹) * c := by group
        _ = c⁻¹ * b * c := by rw [h]


private theorem not_four_distinct_fin_three_w4w {u v i j : Fin 3} (huv : u ≠ v) (hij : i ≠ j)
    (h1 : u ≠ i) (h2 : u ≠ j) (h3 : v ≠ i) (h4 : v ≠ j) : False := by
  fin_cases u <;> fin_cases v <;> fin_cases i <;> fin_cases j <;> simp_all

private theorem not_disjoint_fin_three_w4w {u v i j : Fin 3} (huv : u ≠ v) (hij : i ≠ j) :
    ¬ (swap u v).Disjoint (swap i j) := by
  intro h
  obtain ⟨h1, h2, h3, h4⟩ := (swapDisjoint_iff huv hij).1 h
  exact not_four_distinct_fin_three_w4w huv hij h1 h2 h3 h4

private theorem eq_compl_pair_four_w4w {i j u v : Fin 4} (hij : i ≠ j) (huv : u ≠ v)
    (h1 : u ≠ i) (h2 : u ≠ j) (h3 : v ≠ i) (h4 : v ≠ j) :
    ({u, v} : Finset (Fin 4)) = {i, j}ᶜ := by
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · simp [h1, h2]
    · simp [h3, h4]
  · rw [Finset.card_compl, Finset.card_pair hij, Finset.card_pair huv]
    norm_num

private theorem eq_of_disjoint_fin_four_w4w {i j u v u' v' : Fin 4} (hij : i ≠ j)
    (huv : u ≠ v) (hu'v' : u' ≠ v') (h1 : (swap u v).Disjoint (swap i j))
    (h2 : (swap u' v').Disjoint (swap i j)) : swap u v = swap u' v' := by
  obtain ⟨h1a, h1b, h1c, h1d⟩ := (swapDisjoint_iff huv hij).1 h1
  obtain ⟨h2a, h2b, h2c, h2d⟩ := (swapDisjoint_iff hu'v' hij).1 h2
  have hcomp1 := eq_compl_pair_four_w4w hij huv h1a h1b h1c h1d
  have hcomp2 := eq_compl_pair_four_w4w hij hu'v' h2a h2b h2c h2d
  have hset : ({u, v} : Finset (Fin 4)) = {u', v'} := by rw [hcomp1, hcomp2]
  have hu' : u' ∈ ({u, v} : Finset (Fin 4)) := by rw [hset]; simp
  have hv' : v' ∈ ({u, v} : Finset (Fin 4)) := by rw [hset]; simp
  exact (CFSG.OddTranspositions.swap_eq_swap_of_mem_pair hu' hv' hu'v').symm

private theorem right_eq_or_disjoint_of_commute_tau_w4w {f k : ℕ} {i j : Fin k} (hij : i ≠ j)
    {b : L2Wreath f k} (hb : b ∈ swapSet f k) (hcomm : Commute b (inr (swap i j))) :
    b.right = swap i j ∨ b.right.Disjoint (swap i j) := by
  obtain ⟨u, v, huv, hbr, -⟩ := hb
  have hc : Commute (swap i j) b.right := hcomm.symm.map SemidirectProduct.rightHom
  rw [hbr] at hc
  rcases swap_commute_cases hij huv hc with h | h
  · exact Or.inl (hbr.trans h.symm)
  · exact Or.inr (hbr ▸ h.symm)


private theorem false_of_same_swp_w4w {f k : ℕ} (hf : 2 ≤ f) {i j : Fin k} (hij : i ≠ j)
    {c c' : PSL2Model f} (hc : c * c = 1) (hc' : c' * c' = 1) (hc1 : c ≠ 1) (hc'1 : c' ≠ 1)
    (hnc : ¬ Commute c c')
    (hsub : commSet (commSet (swapSet f k) (inr (swap i j))) (swp c i j) ⊆
      commSet (commSet (swapSet f k) (inr (swap i j))) (swp c' i j)) : False := by
  obtain ⟨a, ha1, hacomm⟩ := exists_conj_ne_commute_of_involution hf hc hc1
  let d := a * c * a⁻¹
  have hd : d * d = 1 := by
    dsimp [d]
    calc (a * c * a⁻¹) * (a * c * a⁻¹) = a * (c * c) * a⁻¹ := by group
      _ = 1 := by rw [hc]; group
  have hd1 : d ≠ 1 := by
    intro h
    apply hc1
    have := congrArg (fun y => a⁻¹ * y * a) h
    simpa [d, mul_assoc] using this
  have hdne : d ≠ c := by simpa [d] using ha1
  have hcd : Commute c d := hacomm.symm
  have hmem : swp d i j ∈ commSet (commSet (swapSet f k) (inr (swap i j))) (swp c i j) :=
    ⟨⟨swp_mem hij, (commute_inr_swp_iff_w4w hij).2 hd |>.symm, by
        intro h
        apply hd1
        rw [← swp_one_eq_inr] at h
        exact swp_injective d 1 hij h⟩,
      (commute_swp_swp_iff_commute_w4w hc hd hij).2 hcd |>.symm,
      by
        intro h
        exact hdne (swp_injective d c hij h)⟩
  have hcomm' : Commute (swp d i j) (swp c' i j) := (hsub hmem).2.1
  have hc'd : Commute c' d := (commute_swp_swp_iff_commute_w4w hc' hd hij).1 hcomm'.symm
  have hK : IsBenderGroup (PSL2Model f) := IsBenderGroup.isPSL2 f hf (MulEquiv.refl _)
  have hc_ord : orderOf c = 2 := orderOf_eq_prime (by rwa [pow_two]) hc1
  have hc'_ord : orderOf c' = 2 := orderOf_eq_prime (by rwa [pow_two]) hc'1
  have hd_ord : orderOf d = 2 := orderOf_eq_prime (by rwa [pow_two]) hd1
  exact hnc (CFSG.Timmesfeld.Bridge.OddLocal.IsBenderGroup.commute_trans hK hc_ord hd_ord
    hc'_ord hcd hc'd.symm)

private theorem inverts_of_mem_commSet_w4w {f k : ℕ} {i j p q : Fin k}
    (hij : i ≠ j) (hpq : p ≠ q) (hdisj : (swap i j).Disjoint (swap p q))
    (hne : swap i j ≠ swap p q) {g g' : PSL2Model f}
    (hsub : commSet (commSet (swapSet f k) (inr (swap i j))) (swp g p q) ⊆
      commSet (commSet (swapSet f k) (inr (swap i j))) (swp g' p q)) :
    ∀ t : PSL2Model f, t * t = 1 → t ≠ 1 →
      t * (g' * g⁻¹) * t = (g' * g⁻¹)⁻¹ := by
    intro t ht ht1
    have hmem : swp (t * g) p q ∈
        commSet (commSet (swapSet f k) (inr (swap i j))) (swp g p q) :=
      ⟨⟨swp_mem hpq, (commute_of_disjoint_right (inr_swap_mem_swapSet hij) (swp_mem hpq)
            (by simpa using hdisj)).symm, by
          intro heq
          have hr := congrArg SemidirectProduct.right heq
          simp only [swp_right, right_inr] at hr
          exact hne hr.symm⟩,
        by
          refine ((commute_swp_swp_iff (a := g) (b := t * g) hpq).2 ?_).symm
          have htg : g * (t * g)⁻¹ = t := by
            rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ht]
            group
          rw [htg, ht],
        by
          intro heq
          apply ht1
          have htg : t * g = g := swp_injective (t * g) g hpq heq
          calc t = t * g * g⁻¹ := by group
            _ = g * g⁻¹ := by rw [htg]
            _ = 1 := mul_inv_cancel g⟩
    have hcomm := (hsub hmem).2.1
    have hsq : (g' * (t * g)⁻¹) * (g' * (t * g)⁻¹) = 1 :=
      (commute_swp_swp_iff (a := g') (b := t * g) hpq).1 hcomm.symm
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    have hht : ((g' * g⁻¹) * t) * ((g' * g⁻¹) * t) = 1 := by
      calc ((g' * g⁻¹) * t) * ((g' * g⁻¹) * t)
          = (g' * (t * g)⁻¹) * (g' * (t * g)⁻¹) := by
            simp [mul_inv_rev, htinv, mul_assoc]
        _ = 1 := hsq
    calc t * (g' * g⁻¹) * t
        = (g' * g⁻¹)⁻¹ * (((g' * g⁻¹) * t) * ((g' * g⁻¹) * t)) := by group
      _ = (g' * g⁻¹)⁻¹ := by rw [hht, mul_one]

private theorem false_of_disjoint_swp_w4w {f k : ℕ} (hf : 2 ≤ f) {i j p q : Fin k}
    (hij : i ≠ j) (hpq : p ≠ q) (hdisj : (swap i j).Disjoint (swap p q))
    (hne : swap i j ≠ swap p q) {g g' : PSL2Model f}
    (hgg' : ¬ Commute (swp g p q) (swp g' p q))
    (hsub : commSet (commSet (swapSet f k) (inr (swap i j))) (swp g p q) ⊆
      commSet (commSet (swapSet f k) (inr (swap i j))) (swp g' p q)) : False := by
  let h := g' * g⁻¹
  have hh : h * h ≠ 1 := by
    intro hh1
    apply hgg'
    exact ((commute_swp_swp_iff (a := g') (b := g) hpq).2 (by simpa [h] using hh1)).symm
  have hinv : ∀ t : PSL2Model f, t * t = 1 → t ≠ 1 → t * h * t = h⁻¹ := by
    intro t ht ht1
    exact inverts_of_mem_commSet_w4w hij hpq hdisj hne hsub t ht ht1
  obtain ⟨t, s, ht, hs, hts, ht1, hs1, htsne⟩ := exists_klein_psl2 hf
  obtain ⟨-, -, -, hu, -, -⟩ := klein_relations ht hs hts
  have hu1 : t * s ≠ 1 := by
    intro hts1
    have hst : s = t := by
      have := eq_inv_of_mul_eq_one_right hts1
      rwa [inv_eq_of_mul_eq_one_right ht] at this
    exact htsne hst.symm
  have hti := hinv t ht ht1
  have hsi := hinv s hs hs1
  have hui := hinv (t * s) hu hu1
  have hinv3 : (t * h * t)⁻¹ = t * h⁻¹ * t := by
    rw [mul_inv_rev, mul_inv_rev, inv_eq_of_mul_eq_one_right ht]
    group
  have hucen : (t * s) * h * (t * s) = h := by
    calc (t * s) * h * (t * s) = t * s * h * (s * t) := by rw [hts]
      _ = t * (s * h * s) * t := by group
      _ = t * h⁻¹ * t := by rw [hsi]
      _ = (t * h * t)⁻¹ := by rw [hinv3]
      _ = (h⁻¹)⁻¹ := by rw [hti]
      _ = h := inv_inv h
  have heq : h = h⁻¹ := by
    rw [hucen] at hui
    exact hui
  have hsq : h * h = 1 := by
    calc h * h = h⁻¹ * h := by nth_rw 1 [heq]
      _ = 1 := inv_mul_cancel h
  exact hh hsq


private theorem false_of_both_right_eq_tau_w4w {f k : ℕ} (hf : 2 ≤ f) {i j : Fin k}
    (hij : i ≠ j) {b b' : L2Wreath f k} (hb : b ∈ swapSet f k) (hb' : b' ∈ swapSet f k)
    (hbr : b.right = swap i j) (hb'r : b'.right = swap i j)
    (hτb : Commute b (inr (swap i j))) (hτb' : Commute b' (inr (swap i j)))
    (hbτ : b ≠ inr (swap i j)) (hb'τ : b' ≠ inr (swap i j)) (hnc : ¬ Commute b b')
    (hsub : commSet (commSet (swapSet f k) (inr (swap i j))) b ⊆
      commSet (commSet (swapSet f k) (inr (swap i j))) b') : False := by
  obtain ⟨c, hbc⟩ : ∃ c, b = swp c i j := ⟨b.left i, eq_swp_of_right_eq hb hij hbr⟩
  obtain ⟨c', hb'c'⟩ : ∃ c', b' = swp c' i j := ⟨b'.left i, eq_swp_of_right_eq hb' hij hb'r⟩
  have hc : c * c = 1 := (commute_inr_swp_iff_w4w hij).1 (by rw [← hbc]; exact hτb.symm)
  have hc' : c' * c' = 1 := (commute_inr_swp_iff_w4w hij).1 (by rw [← hb'c']; exact hτb'.symm)
  have hc1 : c ≠ 1 := by
    intro h
    apply hbτ
    rw [hbc, h, swp_one_eq_inr]
  have hc'1 : c' ≠ 1 := by
    intro h
    apply hb'τ
    rw [hb'c', h, swp_one_eq_inr]
  have hnc' : ¬ Commute c c' := by
    intro h
    apply hnc
    rw [hbc, hb'c']
    exact (commute_swp_swp_iff_commute_w4w hc hc' hij).2 h
  exact false_of_same_swp_w4w hf hij hc hc' hc1 hc'1 hnc' (by simpa [hbc, hb'c'] using hsub)

private theorem core_three_w4w {f : ℕ} (hf : 2 ≤ f) {i j : Fin 3} (hij : i ≠ j)
    {b b' : L2Wreath f 3} (hb : b ∈ swapSet f 3) (hb' : b' ∈ swapSet f 3)
    (hτb : Commute b (inr (swap i j))) (hτb' : Commute b' (inr (swap i j)))
    (hbτ : b ≠ inr (swap i j)) (hb'τ : b' ≠ inr (swap i j)) (hnc : ¬ Commute b b')
    (hsub : commSet (commSet (swapSet f 3) (inr (swap i j))) b ⊆
      commSet (commSet (swapSet f 3) (inr (swap i j))) b') : False := by
  rcases right_eq_or_disjoint_of_commute_tau_w4w hij hb hτb with hbr | hbd
  · rcases right_eq_or_disjoint_of_commute_tau_w4w hij hb' hτb' with hb'r | hb'd
    · exact false_of_both_right_eq_tau_w4w hf hij hb hb' hbr hb'r hτb hτb' hbτ hb'τ hnc hsub
    · obtain ⟨u', v', hu'v', hb'r, -⟩ := hb'
      rw [hb'r] at hb'd
      exact absurd hb'd (not_disjoint_fin_three_w4w hu'v' hij)
  · obtain ⟨u, v, huv, hbr, -⟩ := hb
    rw [hbr] at hbd
    exact absurd hbd (not_disjoint_fin_three_w4w huv hij)

private theorem core_four_w4w {f : ℕ} (hf : 2 ≤ f) {i j : Fin 4} (hij : i ≠ j)
    {b b' : L2Wreath f 4} (hb : b ∈ swapSet f 4) (hb' : b' ∈ swapSet f 4)
    (hτb : Commute b (inr (swap i j))) (hτb' : Commute b' (inr (swap i j)))
    (hbτ : b ≠ inr (swap i j)) (hb'τ : b' ≠ inr (swap i j)) (hnc : ¬ Commute b b')
    (hsub : commSet (commSet (swapSet f 4) (inr (swap i j))) b ⊆
      commSet (commSet (swapSet f 4) (inr (swap i j))) b') : False := by
  rcases right_eq_or_disjoint_of_commute_tau_w4w hij hb hτb with hbr | hbd
  · rcases right_eq_or_disjoint_of_commute_tau_w4w hij hb' hτb' with hb'r | hb'd
    · exact false_of_both_right_eq_tau_w4w hf hij hb hb' hbr hb'r hτb hτb' hbτ hb'τ hnc hsub
    · have hb'0 : b' ∈ swapSet f 4 := hb'
      obtain ⟨u', v', hu'v', hb'r, -⟩ := hb'0
      rw [hb'r] at hb'd
      have hcomm : Commute b b' := by
        refine commute_of_disjoint_right hb hb' ?_
        rw [hbr, hb'r]
        exact hb'd.symm
      exact hnc hcomm
  · have hb0 : b ∈ swapSet f 4 := hb
    obtain ⟨u, v, huv, hbr, -⟩ := hb0
    rw [hbr] at hbd
    rcases right_eq_or_disjoint_of_commute_tau_w4w hij hb' hτb' with hb'r | hb'd
    · obtain ⟨c', hb'c'⟩ : ∃ c', b' = swp c' i j := ⟨b'.left i, eq_swp_of_right_eq hb' hij hb'r⟩
      have hcomm : Commute b b' := by
        refine commute_of_disjoint_right hb hb' ?_
        rw [hbr, hb'c']
        exact hbd
      exact hnc hcomm
    · have hb'0 : b' ∈ swapSet f 4 := hb'
      obtain ⟨u', v', hu'v', hb'r, -⟩ := hb'0
      rw [hb'r] at hb'd
      have heq : swap u v = swap u' v' := eq_of_disjoint_fin_four_w4w hij huv hu'v' hbd hb'd
      obtain ⟨g, hbg⟩ : ∃ g, b = swp g u v := ⟨b.left u, eq_swp_of_right_eq hb huv hbr⟩
      obtain ⟨g', hb'g'⟩ : ∃ g', b' = swp g' u v :=
        ⟨b'.left u, eq_swp_of_right_eq hb' huv (hb'r.trans heq.symm)⟩
      have hgg' : ¬ Commute (swp g u v) (swp g' u v) := by
        rw [← hbg, ← hb'g']
        exact hnc
      have hne : swap i j ≠ swap u v := by
        intro h
        rw [h] at hbd
        exact huv (swap_eq_one_iff.1 (Perm.disjoint_refl_iff.1 hbd))
      exact false_of_disjoint_swp_w4w hf hij huv hbd.symm hne hgg'
        (by simpa [hbg, hb'g'] using hsub)


private theorem eq_or_false_of_commSet_eq_w4w {f k : ℕ} {a b b' : L2Wreath f k}
    (hb : b ∈ swapSet f k) (hb' : b' ∈ swapSet f k) (hab : Commute a b)
    (hab' : Commute a b')
    (h : commSet (commSet (swapSet f k) a) b = commSet (commSet (swapSet f k) a) b')
    (hcore : b ≠ a → b' ≠ a → ¬ Commute b b' →
      commSet (commSet (swapSet f k) a) b ⊆
        commSet (commSet (swapSet f k) a) b' → False) : b = b' := by
  by_cases hba : b = a
  · by_cases hb'a : b' = a
    · rw [hba, hb'a]
    · exfalso
      have hmem : b' ∈ commSet (commSet (swapSet f k) a) b :=
        ⟨⟨hb', hab'.symm, hb'a⟩, by rw [hba]; exact hab'.symm, by
          intro hEq
          exact hb'a (by rw [← hba]; exact hEq)⟩
      have := h ▸ hmem
      exact this.2.2 rfl
  · by_cases hb'a : b' = a
    · exfalso
      have hmem : b ∈ commSet (commSet (swapSet f k) a) b' :=
        ⟨⟨hb, hab.symm, hba⟩, by rw [hb'a]; exact hab.symm, by
          intro hEq
          exact hba (by rw [hb'a] at hEq; exact hEq)⟩
      have := h.symm ▸ hmem
      exact this.2.2 rfl
    · by_cases hbb' : b = b'
      · exact hbb'
      · by_cases hcomm : Commute b b'
        · exfalso
          have hmem : b' ∈ commSet (commSet (swapSet f k) a) b :=
            ⟨⟨hb', hab'.symm, hb'a⟩, hcomm.symm, fun hEq => hbb' hEq.symm⟩
          have := h ▸ hmem
          exact this.2.2 rfl
        · exact (hcore hba hb'a hcomm h.le).elim

private theorem commSet_conj_subset_w4w {f k : ℕ} (c : L2Wreath f k) {a b b' : L2Wreath f k}
    (hle : commSet (commSet (swapSet f k) a) b ⊆
      commSet (commSet (swapSet f k) a) b') :
    commSet (commSet (swapSet f k) (c⁻¹ * a * c)) (c⁻¹ * b * c) ⊆
      commSet (commSet (swapSet f k) (c⁻¹ * a * c)) (c⁻¹ * b' * c) := by
  intro x hx
  have hy : c * x * c⁻¹ ∈ commSet (commSet (swapSet f k) a) b :=
    (conj_mem_commSet_commSet_iff_w4w c a b x).2 hx
  exact (conj_mem_commSet_commSet_iff_w4w c a b' x).1 (hle hy)

private theorem false_of_core_w4w {f k : ℕ} (hf : 2 ≤ f) (hk : k = 3 ∨ k = 4)
    {a b b' : L2Wreath f k} (ha : a ∈ swapSet f k) (hb : b ∈ swapSet f k)
    (hb' : b' ∈ swapSet f k) (hab : Commute a b) (hab' : Commute a b')
    (hba : b ≠ a) (hb'a : b' ≠ a) (hnc : ¬ Commute b b')
    (hle : commSet (commSet (swapSet f k) a) b ⊆
      commSet (commSet (swapSet f k) a) b') : False := by
  have hk2 : 2 ≤ k := by omega
  let i : Fin k := ⟨0, by omega⟩
  let j : Fin k := ⟨1, by omega⟩
  have hij : i ≠ j := by simp [i, j, Fin.ext_iff]
  obtain ⟨c, hc⟩ := isConj_iff.1 (isConj_of_mem_swapSet hij ha)
  let B := c⁻¹ * b * c
  let B' := c⁻¹ * b' * c
  have hcB : c * B * c⁻¹ = b := by dsimp [B]; group
  have hcB' : c * B' * c⁻¹ = b' := by dsimp [B']; group
  have htau : c⁻¹ * a * c = inr (swap i j) := by rw [← hc]; group
  have hB : B ∈ swapSet f k := by simpa [B] using conj_mem_swapSet c⁻¹ hb
  have hB' : B' ∈ swapSet f k := by simpa [B'] using conj_mem_swapSet c⁻¹ hb'
  have hτB : Commute B (inr (swap i j)) :=
    (Commute.conj_iff c).1 (by
      rw [hcB, hc]
      exact hab.symm)
  have hτB' : Commute B' (inr (swap i j)) :=
    (Commute.conj_iff c).1 (by
      rw [hcB', hc]
      exact hab'.symm)
  have hBτ : B ≠ inr (swap i j) := by
    intro h
    apply hba
    rw [← hcB, h, hc]
  have hB'τ : B' ≠ inr (swap i j) := by
    intro h
    apply hb'a
    rw [← hcB', h, hc]
  have hncB : ¬ Commute B B' := by
    intro h
    apply hnc
    have h' := (Commute.conj_iff c).2 h
    rwa [hcB, hcB'] at h'
  have hsubB : commSet (commSet (swapSet f k) (inr (swap i j))) B ⊆
      commSet (commSet (swapSet f k) (inr (swap i j))) B' := by
    intro x hx
    have hx' : x ∈ commSet (commSet (swapSet f k) (c⁻¹ * a * c)) (c⁻¹ * b * c) := by
      simpa [htau, B] using hx
    simpa [htau, B'] using commSet_conj_subset_w4w c hle hx'
  rcases hk with rfl | rfl
  · exact core_three_w4w hf hij hB hB' hτB hτB' hBτ hB'τ hncB hsubB
  · exact core_four_w4w hf hij hB hB' hτB hτB' hBτ hB'τ hncB hsubB


private theorem map_mem_commSet_iff_w4w {X : Type*} [Group X] {E : Set X} {f k : ℕ}
    (e : X ≃* L2Wreath f k) (hE : E = e ⁻¹' swapSet f k) {a b x : X} :
    e x ∈ {c | c ∈ swapSet f k ∧ Commute (e a) c ∧ Commute (e b) c ∧
        c ≠ e a ∧ c ≠ e b} ↔
      x ∈ {c | c ∈ E ∧ Commute a c ∧ Commute b c ∧ c ≠ a ∧ c ≠ b} := by
  constructor
  · rintro ⟨hxS, hxa, hxb, hxae, hxbe⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hE]
      simpa using hxS
    · simpa using hxa.map e.symm.toMonoidHom
    · simpa using hxb.map e.symm.toMonoidHom
    · intro h
      apply hxae
      rw [h]
    · intro h
      apply hxbe
      rw [h]
  · rintro ⟨hxE, hxa, hxb, hxane, hxbne⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hE] at hxE
      simpa using hxE
    · simpa using hxa.map e.toMonoidHom
    · simpa using hxb.map e.toMonoidHom
    · intro h
      apply hxane
      exact e.injective h
    · intro h
      apply hxbne
      exact e.injective h

theorem eq_of_setOf_commute_eq_swapSet {f k : ℕ} (hf : 2 ≤ f) (hk : k = 3 ∨ k = 4)
    {a b b' : L2Wreath f k} (ha : a ∈ WreathEndgame.swapSet f k)
    (hb : b ∈ WreathEndgame.swapSet f k) (hb' : b' ∈ WreathEndgame.swapSet f k)
    (hab : Commute a b) (hab' : Commute a b')
    (h : {c | c ∈ WreathEndgame.swapSet f k ∧ Commute a c ∧ Commute b c ∧ c ≠ a ∧ c ≠ b} =
      {c | c ∈ WreathEndgame.swapSet f k ∧ Commute a c ∧ Commute b' c ∧ c ≠ a ∧ c ≠ b'}) :
    b = b' := by
  have hcomm : commSet (commSet (WreathEndgame.swapSet f k) a) b =
      commSet (commSet (WreathEndgame.swapSet f k) a) b' := by
    ext x
    rw [mem_commSet_commSet_iff_w4w, mem_commSet_commSet_iff_w4w, h]
  exact eq_or_false_of_commSet_eq_w4w hb hb' hab hab' hcomm
    (fun hba hb'a hnc hle => false_of_core_w4w hf hk ha hb hb' hab hab' hba hb'a hnc hle)

theorem eq_of_setOf_commute_eq_of_mulEquiv {X : Type*} [Group X] {E : Set X} (hS : Setup X E)
    {f k : ℕ} (hf : 2 ≤ f) (hk : k = 3 ∨ k = 4) (e : X ≃* L2Wreath f k) {a b b' : X}
    (ha : a ∈ E) (hb : b ∈ E) (hb' : b' ∈ E) (hab : Commute a b) (hab' : Commute a b')
    (h : {c | c ∈ E ∧ Commute a c ∧ Commute b c ∧ c ≠ a ∧ c ≠ b} =
      {c | c ∈ E ∧ Commute a c ∧ Commute b' c ∧ c ≠ a ∧ c ≠ b'}) :
    b = b' := by
  have hE : E = e ⁻¹' WreathEndgame.swapSet f k :=
    eq_preimage_swapSet_of_mulEquiv hS hf hk e
  have hsa : e a ∈ WreathEndgame.swapSet f k := by
    have h := hE ▸ ha
    simpa using h
  have hsb : e b ∈ WreathEndgame.swapSet f k := by
    have h := hE ▸ hb
    simpa using h
  have hsb' : e b' ∈ WreathEndgame.swapSet f k := by
    have h := hE ▸ hb'
    simpa using h
  refine e.injective (eq_of_setOf_commute_eq_swapSet hf hk hsa hsb hsb' ?_ ?_ ?_)
  · exact hab.map e.toMonoidHom
  · exact hab'.map e.toMonoidHom
  · ext c
    constructor
    · intro hc
      have hx : e (e.symm c) ∈ {d | d ∈ WreathEndgame.swapSet f k ∧ Commute (e a) d ∧
          Commute (e b) d ∧ d ≠ e a ∧ d ≠ e b} := by simpa using hc
      have hx' := (map_mem_commSet_iff_w4w e hE (a := a) (b := b) (x := e.symm c)).1 hx
      have hy' := h ▸ hx'
      have hy := (map_mem_commSet_iff_w4w e hE (a := a) (b := b') (x := e.symm c)).2 hy'
      simpa using hy
    · intro hc
      have hx : e (e.symm c) ∈ {d | d ∈ WreathEndgame.swapSet f k ∧ Commute (e a) d ∧
          Commute (e b') d ∧ d ≠ e a ∧ d ≠ e b'} := by simpa using hc
      have hx' := (map_mem_commSet_iff_w4w e hE (a := a) (b := b') (x := e.symm c)).1 hx
      have hy' := h.symm ▸ hx'
      have hy := (map_mem_commSet_iff_w4w e hE (a := a) (b := b) (x := e.symm c)).2 hy'
      simpa using hy

end CFSG.OddTranspositions.PartThree.EightEight

end
