module

public import CFSG.LocalAnalysis.StandardType.GGExcLeviRankBase
public import CFSG.LocalAnalysis.StandardType.GGExcLeviRankA
public import CFSG.LocalAnalysis.StandardType.GGExcLeviRankD
public import CFSG.LocalAnalysis.StandardType.GGExcLeviRankE
public import CFSG.LocalAnalysis.StandardType.GGExcLeviRankProp
public import CFSG.LocalAnalysis.StandardType.GGExcKGBorelTitsLevi

public section

namespace CFSG.StandardType.E8LeviG3

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.Assembly CFSG.ComponentClassification.CatLeafProof
open CFSG.StandardType.F4Rest
open scoped MatrixGroups


theorem card_le_pow_three_subsystemGroup_e8delete0 {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h3 : 3 ≤ CFSG.StandardType.OrdPNS.ordQ K p)
    {E : Subgroup (ModGL Tag.E8 K)}
    (hE : E ≤ subsystemGroup Tag.E8 K {j : Fin Tag.E8.rank | j ≠ 0})
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 3 := by
  have hsub : ({j : Fin Tag.E8.rank | j ≠ 0} : Set _) ⊆ Set.range e8D7Node := by
    intro j hj
    exact (mem_range_e8D7Node j).2 hj
  exact card_le_pow_three_subsystemGroup_e8D7 hp hp2 h3
    (hE.trans (subsystemGroup_mono hsub)) hEel

theorem card_le_pow_three_subsystemGroup_e8delete1 {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h3 : 3 ≤ CFSG.StandardType.OrdPNS.ordQ K p)
    {E : Subgroup (ModGL Tag.E8 K)}
    (hE : E ≤ subsystemGroup Tag.E8 K {j : Fin Tag.E8.rank | j ≠ 1})
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 3 := by
  have hsub : ({j : Fin Tag.E8.rank | j ≠ 1} : Set _) ⊆ Set.range e8A7Node := by
    intro j hj
    exact (mem_range_e8A7Node j).2 hj
  calc Nat.card E ≤ p ^ 2 :=
        card_le_pow_two_subsystemGroup_e8A7 hp hp2 h3
          (hE.trans (subsystemGroup_mono hsub)) hEel
    _ ≤ p ^ 3 := Nat.pow_le_pow_right hp.pos (by norm_num)

theorem card_le_pow_three_subsystemGroup_e8delete2 {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h3 : 3 ≤ CFSG.StandardType.OrdPNS.ordQ K p)
    {E : Subgroup (ModGL Tag.E8 K)}
    (hE : E ≤ subsystemGroup Tag.E8 K {j : Fin Tag.E8.rank | j ≠ 2})
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 3 := by
  have hpq : ¬ p ∣ Nat.card K - 1 := not_dvd_card_sub_one_of_three_le_ordQ hp h3
  have hsub : ({j : Fin Tag.E8.rank | j ≠ 2} : Set _) ⊆
      ({0} : Set (Fin Tag.E8.rank)) ∪ Set.range e8A6Node := by
    intro j hj
    fin_cases j <;> first | exact absurd rfl hj | decide
  have hE' : E ≤ subsystemGroup Tag.E8 K (({0} : Set (Fin Tag.E8.rank)) ∪ Set.range e8A6Node) :=
    hE.trans (subsystemGroup_mono hsub)
  rw [subsystemGroup_union] at hE'
  have hcomm := commute_subsystemGroup_of_cartan_zero (K := K)
    (A := ({0} : Set (Fin Tag.E8.rank))) (B := Set.range e8A6Node) (by
      intro a ha b hb
      have ha0 : a = 0 := by simpa using ha
      subst ha0
      have hb' : b = 1 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 ∨ b = 7 := by
        have h1 := (mem_range_e8A6Node b).1 hb
        fin_cases b <;> first | exact absurd rfl h1.1 | exact absurd rfl h1.2 | decide
      rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have hboundA : ∀ F : Subgroup (subsystemGroup Tag.E8 K ({0} : Set (Fin Tag.E8.rank))),
      IsElemAbelian p F → Nat.card F ≤ p ^ 0 :=
    bound_subgroup_of_ambient (fun F hF hFel =>
      card_le_pow_zero_subsystemGroup_e8node hp hp2 h3 0 hF hFel)
  have hboundB : ∀ F : Subgroup (subsystemGroup Tag.E8 K (Set.range e8A6Node)),
      IsElemAbelian p F → Nat.card F ≤ p ^ 2 :=
    bound_subgroup_of_ambient (fun F hF hFel =>
      card_le_pow_two_subsystemGroup_e8A6 hp hp2 h3 hF hFel)
  have h := CFSG.LocalAnalysis.GLTheoremA.card_le_pow_add_of_le_sup_of_not_dvd_inf (p := p) hp hcomm
    (not_dvd_card_inf_subsystemGroup_e8 hp hpq hcomm) hboundA hboundB hE' hEel
  exact h.trans (Nat.pow_le_pow_right hp.pos (by norm_num))

theorem card_le_pow_three_subsystemGroup_e8delete3 {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h3 : 3 ≤ CFSG.StandardType.OrdPNS.ordQ K p)
    {E : Subgroup (ModGL Tag.E8 K)}
    (hE : E ≤ subsystemGroup Tag.E8 K {j : Fin Tag.E8.rank | j ≠ 3})
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 3 := by
  have hpq : ¬ p ∣ Nat.card K - 1 := not_dvd_card_sub_one_of_three_le_ordQ hp h3
  have hsub : ({j : Fin Tag.E8.rank | j ≠ 3} : Set _) ⊆
      ({1} : Set (Fin Tag.E8.rank)) ∪ (({0, 2} : Set (Fin Tag.E8.rank)) ∪ Set.range e8A4Node) := by
    intro j hj
    fin_cases j <;> first | exact absurd rfl hj | decide
  have hE' : E ≤ subsystemGroup Tag.E8 K
      (({1} : Set (Fin Tag.E8.rank)) ∪ (({0, 2} : Set (Fin Tag.E8.rank)) ∪ Set.range e8A4Node)) :=
    hE.trans (subsystemGroup_mono hsub)
  rw [subsystemGroup_union] at hE'
  have hcomm₁ := commute_subsystemGroup_of_cartan_zero (K := K)
    (A := ({1} : Set (Fin Tag.E8.rank)))
    (B := (({0, 2} : Set (Fin Tag.E8.rank)) ∪ Set.range e8A4Node)) (by
      intro a ha b hb
      have ha1 : a = 1 := by simpa using ha
      subst ha1
      rcases hb with hb | hb
      · rcases (by simpa using hb : b = 0 ∨ b = 2) with rfl | rfl <;> decide
      · have hb' := (mem_range_e8A4Node b).1 hb
        rcases hb' with rfl | rfl | rfl | rfl <;> decide)
  have hcomm₂ := commute_subsystemGroup_of_cartan_zero (K := K)
    (A := ({0, 2} : Set (Fin Tag.E8.rank))) (B := Set.range e8A4Node) (by
      intro a ha b hb
      have ha' : a = 0 ∨ a = 2 := by simpa using ha
      have hb' := (mem_range_e8A4Node b).1 hb
      rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl | rfl | rfl <;> decide)
  have hboundA : ∀ F : Subgroup (subsystemGroup Tag.E8 K ({1} : Set (Fin Tag.E8.rank))),
      IsElemAbelian p F → Nat.card F ≤ p ^ 0 :=
    bound_subgroup_of_ambient (fun F hF hFel =>
      card_le_pow_zero_subsystemGroup_e8node hp hp2 h3 1 hF hFel)
  have hboundB : ∀ F : Subgroup (subsystemGroup Tag.E8 K
      (({0, 2} : Set (Fin Tag.E8.rank)) ∪ Set.range e8A4Node)),
      IsElemAbelian p F → Nat.card F ≤ p ^ (1 + 1) :=
    bound_subgroup_of_ambient (fun E hE hEel => by
      have hE' : E ≤ subsystemGroup Tag.E8 K ({0, 2} : Set (Fin Tag.E8.rank)) ⊔
          subsystemGroup Tag.E8 K (Set.range e8A4Node) := by
        rw [← subsystemGroup_union]
        exact hE
      exact CFSG.LocalAnalysis.GLTheoremA.card_le_pow_add_of_le_sup_of_not_dvd_inf (p := p) hp hcomm₂
        (not_dvd_card_inf_subsystemGroup_e8 hp hpq hcomm₂)
        (bound_subgroup_of_ambient (fun G hG hGel =>
          card_le_pow_one_subsystemGroup_e8A2 (i := 0) (j := 2) hp hp2 h3
            (by decide) (by decide) (by decide) ⟨3, by decide⟩ hG hGel))
        (bound_subgroup_of_ambient (fun G hG hGel =>
          card_le_pow_one_subsystemGroup_e8A4 hp hp2 h3 hG hGel)) hE' hEel)
  have h := CFSG.LocalAnalysis.GLTheoremA.card_le_pow_add_of_le_sup_of_not_dvd_inf (p := p) hp hcomm₁
    (not_dvd_card_inf_subsystemGroup_e8 hp hpq hcomm₁) hboundA hboundB hE' hEel
  exact h.trans (Nat.pow_le_pow_right hp.pos (by norm_num))

theorem card_le_pow_three_subsystemGroup_e8delete4 {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h3 : 3 ≤ CFSG.StandardType.OrdPNS.ordQ K p)
    {E : Subgroup (ModGL Tag.E8 K)}
    (hE : E ≤ subsystemGroup Tag.E8 K {j : Fin Tag.E8.rank | j ≠ 4})
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 3 := by
  have hpq : ¬ p ∣ Nat.card K - 1 := not_dvd_card_sub_one_of_three_le_ordQ hp h3
  have hsub : ({j : Fin Tag.E8.rank | j ≠ 4} : Set _) ⊆
      Set.range e8A4Node' ∪ Set.range e8A3Node := by
    intro j hj
    fin_cases j <;> first | exact absurd rfl hj | decide
  have hE' : E ≤ subsystemGroup Tag.E8 K (Set.range e8A4Node' ∪ Set.range e8A3Node) :=
    hE.trans (subsystemGroup_mono hsub)
  rw [subsystemGroup_union] at hE'
  have hcomm := commute_subsystemGroup_of_cartan_zero (K := K)
    (A := Set.range e8A4Node') (B := Set.range e8A3Node) (by
      intro a ha b hb
      have ha' := (mem_range_e8A4Node' a).1 ha
      have hb' := (mem_range_e8A3Node b).1 hb
      rcases ha' with rfl | rfl | rfl | rfl <;>
        rcases hb' with rfl | rfl | rfl <;> decide)
  have hboundA : ∀ F : Subgroup (subsystemGroup Tag.E8 K (Set.range e8A4Node')),
      IsElemAbelian p F → Nat.card F ≤ p ^ 1 :=
    bound_subgroup_of_ambient (fun F hF hFel =>
      card_le_pow_one_subsystemGroup_e8A4' hp hp2 h3 hF hFel)
  have hboundB : ∀ F : Subgroup (subsystemGroup Tag.E8 K (Set.range e8A3Node)),
      IsElemAbelian p F → Nat.card F ≤ p ^ 1 :=
    bound_subgroup_of_ambient (fun F hF hFel =>
      card_le_pow_one_subsystemGroup_e8A3 hp hp2 h3 hF hFel)
  have h := CFSG.LocalAnalysis.GLTheoremA.card_le_pow_add_of_le_sup_of_not_dvd_inf (p := p) hp hcomm
    (not_dvd_card_inf_subsystemGroup_e8 hp hpq hcomm) hboundA hboundB hE' hEel
  exact h.trans (Nat.pow_le_pow_right hp.pos (by norm_num))

theorem card_le_pow_three_subsystemGroup_e8delete5 {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h3 : 3 ≤ CFSG.StandardType.OrdPNS.ordQ K p)
    {E : Subgroup (ModGL Tag.E8 K)}
    (hE : E ≤ subsystemGroup Tag.E8 K {j : Fin Tag.E8.rank | j ≠ 5})
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 3 := by
  have hpq : ¬ p ∣ Nat.card K - 1 := not_dvd_card_sub_one_of_three_le_ordQ hp h3
  have hsub : ({j : Fin Tag.E8.rank | j ≠ 5} : Set _) ⊆
      Set.range e8D5Node ∪ Set.range e8A2Node := by
    intro j hj
    fin_cases j <;> first | exact absurd rfl hj | decide
  have hE' : E ≤ subsystemGroup Tag.E8 K (Set.range e8D5Node ∪ Set.range e8A2Node) :=
    hE.trans (subsystemGroup_mono hsub)
  rw [subsystemGroup_union] at hE'
  have hcomm := commute_subsystemGroup_of_cartan_zero (K := K)
    (A := Set.range e8D5Node) (B := Set.range e8A2Node) (by
      intro a ha b hb
      have ha' := (mem_range_e8D5Node a).1 ha
      have hb' := (mem_range_e8A2Node b).1 hb
      rcases ha' with rfl | rfl | rfl | rfl | rfl <;>
        rcases hb' with rfl | rfl <;> decide)
  have hboundA : ∀ F : Subgroup (subsystemGroup Tag.E8 K (Set.range e8D5Node)),
      IsElemAbelian p F → Nat.card F ≤ p ^ 2 :=
    bound_subgroup_of_ambient (fun F hF hFel =>
      card_le_pow_two_subsystemGroup_e8D5 hp hp2 h3 hF hFel)
  have hboundB : ∀ F : Subgroup (subsystemGroup Tag.E8 K (Set.range e8A2Node)),
      IsElemAbelian p F → Nat.card F ≤ p ^ 1 :=
    bound_subgroup_of_ambient (fun E hE hEel => by
      have hE' : E ≤ subsystemGroup Tag.E8 K ({6, 7} : Set (Fin Tag.E8.rank)) := by
        rw [← e8A2Node_range]
        exact hE
      exact card_le_pow_one_subsystemGroup_e8A2 (i := 6) (j := 7) hp hp2 h3
        (by decide) (by decide) (by decide) ⟨5, by decide⟩ hE' hEel)
  have h := CFSG.LocalAnalysis.GLTheoremA.card_le_pow_add_of_le_sup_of_not_dvd_inf (p := p) hp hcomm
    (not_dvd_card_inf_subsystemGroup_e8 hp hpq hcomm) hboundA hboundB hE' hEel
  exact h.trans (Nat.pow_le_pow_right hp.pos (by norm_num))

theorem card_le_pow_three_subsystemGroup_e8delete6 {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h3 : 3 ≤ CFSG.StandardType.OrdPNS.ordQ K p)
    {E : Subgroup (ModGL Tag.E8 K)}
    (hE : E ≤ subsystemGroup Tag.E8 K {j : Fin Tag.E8.rank | j ≠ 6})
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 3 := by
  have hpq : ¬ p ∣ Nat.card K - 1 := not_dvd_card_sub_one_of_three_le_ordQ hp h3
  have hsub : ({j : Fin Tag.E8.rank | j ≠ 6} : Set _) ⊆
      Set.range e8E6Node ∪ ({7} : Set (Fin Tag.E8.rank)) := by
    intro j hj
    fin_cases j <;> first | exact absurd rfl hj | decide
  have hE' : E ≤ subsystemGroup Tag.E8 K (Set.range e8E6Node ∪ ({7} : Set (Fin Tag.E8.rank))) :=
    hE.trans (subsystemGroup_mono hsub)
  rw [subsystemGroup_union] at hE'
  have hcomm := commute_subsystemGroup_of_cartan_zero (K := K)
    (A := Set.range e8E6Node) (B := ({7} : Set (Fin Tag.E8.rank))) (by
      intro a ha b hb
      have ha' := (mem_range_e8E6Node a).1 ha
      have hb7 : b = 7 := by simpa using hb
      subst hb7
      rcases ha' with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have hboundA : ∀ F : Subgroup (subsystemGroup Tag.E8 K (Set.range e8E6Node)),
      IsElemAbelian p F → Nat.card F ≤ p ^ 3 :=
    bound_subgroup_of_ambient (fun F hF hFel =>
      card_le_pow_three_subsystemGroup_e8E6 hp hp2 h3 hF hFel)
  have hboundB : ∀ F : Subgroup (subsystemGroup Tag.E8 K ({7} : Set (Fin Tag.E8.rank))),
      IsElemAbelian p F → Nat.card F ≤ p ^ 0 :=
    bound_subgroup_of_ambient (fun F hF hFel =>
      card_le_pow_zero_subsystemGroup_e8node hp hp2 h3 7 hF hFel)
  have h := CFSG.LocalAnalysis.GLTheoremA.card_le_pow_add_of_le_sup_of_not_dvd_inf (p := p) hp hcomm
    (not_dvd_card_inf_subsystemGroup_e8 hp hpq hcomm) hboundA hboundB hE' hEel
  exact h.trans (Nat.pow_le_pow_right hp.pos (by norm_num))

theorem card_le_pow_three_subsystemGroup_e8delete7 {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h3 : 3 ≤ CFSG.StandardType.OrdPNS.ordQ K p)
    {E : Subgroup (ModGL Tag.E8 K)}
    (hE : E ≤ subsystemGroup Tag.E8 K {j : Fin Tag.E8.rank | j ≠ 7})
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 3 := by
  have hsub : ({j : Fin Tag.E8.rank | j ≠ 7} : Set _) ⊆ e8LeviE7 := by
    intro j hj
    exact (mem_range_e8E7Node j).2 hj
  exact card_le_pow_three_subsystemGroup_e8E7 hp hp2 h3
    (hE.trans (subsystemGroup_mono hsub)) hEel

theorem levi_card_le_three_explicit {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (h3 : 3 ≤ CFSG.StandardType.OrdPNS.ordQ K p)
    {J : Set (Fin Tag.E8.rank)} (hJ : J ≠ Set.univ)
    {E : Subgroup (ModGL Tag.E8 K)} (hE : E ≤ subsystemGroup Tag.E8 K J)
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 3 := by
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨i, hi⟩ : ∃ i, i ∉ J := by
    by_contra hall
    push Not at hall
    exact hJ (Set.eq_univ_of_forall hall)
  have hJle : J ⊆ {j : Fin Tag.E8.rank | j ≠ i} := by
    intro j hj hji
    exact hi (hji ▸ hj)
  have hE' : E ≤ subsystemGroup Tag.E8 K {j : Fin Tag.E8.rank | j ≠ i} :=
    hE.trans (subsystemGroup_mono hJle)
  fin_cases i
  · exact card_le_pow_three_subsystemGroup_e8delete0 hp hp2 h3 hE' hEel
  · exact card_le_pow_three_subsystemGroup_e8delete1 hp hp2 h3 hE' hEel
  · exact card_le_pow_three_subsystemGroup_e8delete2 hp hp2 h3 hE' hEel
  · exact card_le_pow_three_subsystemGroup_e8delete3 hp hp2 h3 hE' hEel
  · exact card_le_pow_three_subsystemGroup_e8delete4 hp hp2 h3 hE' hEel
  · exact card_le_pow_three_subsystemGroup_e8delete5 hp hp2 h3 hE' hEel
  · exact card_le_pow_three_subsystemGroup_e8delete6 hp hp2 h3 hE' hEel
  · exact card_le_pow_three_subsystemGroup_e8delete7 hp hp2 h3 hE' hEel

theorem _root_.CFSG.StandardType.e8LeviRankLE3_holds : CFSG.StandardType.E8LeviRankLE3 := by
  unfold CFSG.StandardType.E8LeviRankLE3
  intro K _ _ _ p hp hp2 hord J hJ E hE hEel
  have h3 : 3 ≤ CFSG.StandardType.OrdPNS.ordQ K p := by
    rw [CFSG.StandardType.OrdPNS.ordQ]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hord
    rcases hord with h | h | h <;> omega
  exact levi_card_le_three_explicit hp hp2 h3 hJ hE hEel

theorem _root_.CFSG.StandardType.ggExcKGBorelTits_holds : CFSG.StandardType.GGExcKGBorelTits :=
  fun n f G _ _ ψ hset p hp hp2 hord E hEn hE hcard hdiag T hTn hT2 hET =>
    CFSG.StandardType.ggExcKGBorelTits_of_leviRank CFSG.StandardType.e8LeviRankLE3_holds n f G ψ
      hset p hp hp2 hord E hEn hE hcard hdiag T hTn hT2 hET

end CFSG.StandardType.E8LeviG3
