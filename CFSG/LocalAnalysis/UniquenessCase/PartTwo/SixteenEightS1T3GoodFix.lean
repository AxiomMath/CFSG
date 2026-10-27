module

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC163Lift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightRowCtx

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

theorem s16g_fix_good_vector_witness (hset : Setting16 D V₀ V L) (hV₀ : V₀ = ⊥)
    {w : Vtil V₀ V hV} (hw : w ≠ 1)
    (hwT : ∀ t : ↥(barSub V₀ V hV D.T), (t : MulAut (Vtil V₀ V hV)) w = w)
    {E : Subgroup (MulAut (Vtil V₀ V hV))} (hEM : E ≤ Mbar D.M V₀ V hV)
    (hEw : ∀ e ∈ E, e w = w) :
    ∃ x : IntMod V hV, mkTil V₀ V hV x = w ∧ x.val ∉ V₀ ∧
      (∀ t ∈ D.T, t * x.val = x.val * t) ∧
      E ≤ ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV x) := by
  classical
  have hMst : D.M ≤ stabTil V₀ V := s16g_le_stabTil hset
  have hDT : D.T ≤ D.M := D.sylowM.le
  obtain ⟨x, hx⟩ := mkTil_surjective V₀ V hV w
  have hx0 : x.val ∉ V₀ := by
    intro hmem
    rw [hV₀] at hmem
    have hx1 : x = (1 : IntMod V hV) := Subtype.ext (Subgroup.mem_bot.1 hmem)
    exact hw (by rw [← hx, hx1, map_one])
  have hcomm : ∀ t ∈ D.T, t * x.val = x.val * t := by
    intro t ht
    have hst : t ∈ stabTil V₀ V := hMst (hDT ht)
    have hmem : actTil V₀ V hV ⟨t, hst⟩ ∈ barSub V₀ V hV D.T :=
      actTil_mem_barSub V₀ V hV ht hst
    have hfix' : actTil V₀ V hV ⟨t, hst⟩ (mkTil V₀ V hV x) = mkTil V₀ V hV x := by
      rw [hx]
      exact hwT ⟨actTil V₀ V hV ⟨t, hst⟩, hmem⟩
    rw [actTil_mk, mkTil_eq_iff, actStab_apply_val] at hfix'
    have h3' : t * x.val * t⁻¹ = x.val := by
      have hmem0 : (t * x.val * t⁻¹) * x.val⁻¹ ∈ (⊥ : Subgroup G) := by
        simpa using (le_of_eq hV₀) hfix'
      exact mul_inv_eq_one.mp (Subgroup.mem_bot.1 hmem0)
    calc t * x.val = (t * x.val * t⁻¹) * t := by group
      _ = x.val * t := by rw [h3']
  have hE : E ≤ ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV x) := by
    intro e he
    refine Subgroup.mem_inf.2 ⟨hEM he, ?_⟩
    rw [MulAction.mem_stabilizer_iff]
    change e (mkTil V₀ V hV x) = mkTil V₀ V hV x
    rw [hx]
    exact hEw e he
  exact ⟨x, hx, hx0, hcomm, hE⟩

theorem Setting16.good_vector_of_fix (hset : Setting16 D V₀ V L) (h61 : UC6.R6_1 D)
    (h3 : 3 ∈ D.sig) (hV₀ : V₀ = ⊥) {w : Vtil V₀ V hV} (hw : w ≠ 1)
    (hwT : ∀ t : ↥(barSub V₀ V hV D.T), (t : MulAut (Vtil V₀ V hV)) w = w)
    {E : Subgroup (MulAut (Vtil V₀ V hV))} (hEM : E ≤ Mbar D.M V₀ V hV) (hEp : IsPGroup 3 ↥E)
    (hEc : ¬ IsCyclic ↥E) (hEw : ∀ e ∈ E, e w = w) :
    ∃ v ∈ V, v ≠ 1 ∧ (∀ t ∈ D.T, t * v = v * t) ∧
      Subgroup.centralizer ({v} : Set G) ≤ D.M := by
  obtain ⟨x, hxw, hx0, hcomm, hE⟩ := s16g_fix_good_vector_witness hset hV₀ hw hwT hEM hEw
  refine ⟨x.val, x.val_mem, ?_, hcomm, ?_⟩
  · intro h1
    exact hx0 (by rw [hV₀]; exact Subgroup.mem_bot.2 h1)
  · refine centralizer_le_of_noncyclic_bar D h61 Nat.prime_three (by norm_num) h3 hV
      hset.hyp16.hyp125.pairFacts (Or.inl hV₀) ?_ x hx0 hE hEp hEc
    rw [hV₀, Subgroup.card_bot]
    norm_num

theorem Setting16.good_vector_of_fix_of_stronglyEmbedded (hset : Setting16 D V₀ V L)
    (h61 : UC6.R6_1 D) (h63 : UC6.R6_3 D)
    (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M) (hV₀ : V₀ = ⊥)
    {w : Vtil V₀ V hV} (hw : w ≠ 1)
    (hwT : ∀ t : ↥(barSub V₀ V hV D.T), (t : MulAut (Vtil V₀ V hV)) w = w)
    {E : Subgroup (MulAut (Vtil V₀ V hV))} (hEM : E ≤ Mbar D.M V₀ V hV) (hEp : IsPGroup 3 ↥E)
    (hEc : ¬ IsCyclic ↥E) (hEw : ∀ e ∈ E, e w = w) :
    ∃ v ∈ V, v ≠ 1 ∧ (∀ t ∈ D.T, t * v = v * t) ∧
      Subgroup.centralizer ({v} : Set G) ≤ D.M := by
  obtain ⟨x, hxw, hx0, hcomm, -⟩ := s16g_fix_good_vector_witness hset hV₀ hw hwT hEM hEw
  have hV₀card : Nat.card V₀ < 3 := by
    rw [hV₀, Subgroup.card_bot]
    norm_num
  have hxmk : IntMod.mk hV ⟨x.val, x.val_mem⟩ = x := rfl
  have hEw' : ∀ e ∈ E, e (mkTil V₀ V hV (IntMod.mk hV ⟨x.val, x.val_mem⟩)) =
      mkTil V₀ V hV (IntMod.mk hV ⟨x.val, x.val_mem⟩) := by
    intro e he
    rw [hxmk, hxw]
    exact hEw e he
  obtain ⟨P, hPX, hPp, hPc⟩ :=
    C163.exists_noncyclic_le_centralizer hV Nat.prime_three hV₀card x.val_mem hEM hEp hEc hEw'
  have hu : UniqueMax D.M (D.M ⊓ centralizer ({x.val} : Set G)) :=
    uc22p22u_uniqueMax_mono D hPX inf_le_left
      (uc22p22u_uniqueMax_of_noncyclic D h61 h63 Nat.prime_three (by norm_num)
        (hPX.trans inf_le_left) hPp hPc
        (Or.inl (ElevenNine.gamma_le_of_stronglyEmbedded D Nat.prime_three hsp
          (hPX.trans inf_le_left) hPp)))
  have hx1 : x.val ≠ 1 := fun h => hx0 (by rw [hV₀]; exact Subgroup.mem_bot.2 h)
  have hx2 : ∃ n : ℕ, x.val ^ (2 ^ n) = 1 := ⟨1, by simpa using hV.2 x.val x.val_mem⟩
  exact ⟨x.val, x.val_mem, hx1, hcomm,
    (centralizer_le_of_uniqueMax D.maxLocal hx1 hx2 hu).1⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
