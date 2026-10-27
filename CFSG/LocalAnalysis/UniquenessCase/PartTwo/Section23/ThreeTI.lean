module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeBasics

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Ctx23

private theorem rMV_indexSet_eq_singleton {D : Data G} {Ch : Choice2011 G} (c : Ctx23 D Ch) :
    {V : Subgroup G | V ≤ D.U ∧ ¬ centralizer (V : Set G) ≤ D.M} = {⊥} := by
  ext V
  constructor
  · rintro ⟨hVU, hVM⟩
    by_contra hVne
    obtain ⟨v, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hVne
    have hv1' : (v : G) ≠ 1 := fun h => hv1 (Subtype.ext h)
    refine hVM ((Subgroup.centralizer_le ?_).trans
      (Ctx23.centralizer_le_M c (hVU v.2) hv1'))
    exact Set.singleton_subset_iff.mpr v.2
  · rintro rfl
    refine ⟨bot_le, ?_⟩
    intro hC
    have htop : (⊤ : Subgroup G) ≤ D.M := by
      intro g _
      exact hC (by
        change g ∈ Subgroup.centralizer ((⊥ : Subgroup G) : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        simp at hy
        subst hy
        simp)
    exact uc22br4_M_ne_top D (top_le_iff.mp htop)

theorem rMV_eq_rk_of_TI {D : Data G} {Ch : Choice2011 G} (c : Ctx23 D Ch) :
    rMV D.M D.U = (rk ↥D.U : ℕ∞) := by
  have hUel : IsElemAbelian 2 D.U := (uc22p22e_inCalV_U D).2.2.2
  have hset := rMV_indexSet_eq_singleton c
  rw [rMV]
  refine le_antisymm ?_ ?_
  · refine (iInf₂_le (⊥ : Subgroup G) (show ⊥ ∈
      {V : Subgroup G | V ≤ D.U ∧ ¬ centralizer (V : Set G) ≤ D.M} from ⟨bot_le, by
        intro hC
        have htop : (⊤ : Subgroup G) ≤ D.M := by
          intro g _
          exact hC (by
            change g ∈ Subgroup.centralizer ((⊥ : Subgroup G) : Set G)
            rw [Subgroup.mem_centralizer_iff]
            intro y hy
            simp at hy
            subst hy
            simp)
        exact uc22br4_M_ne_top D (top_le_iff.mp htop)⟩)).trans ?_
    rw [E6.mQuot_bot_eq_rk hUel]
    change (rk ↥D.U : ℕ∞) ≤ (rk ↥D.U : ℕ∞)
    exact le_rfl
  · refine le_iInf₂ fun V hV => ?_
    have hVbot : V = ⊥ := by
      have := (Set.ext_iff.mp hset V).mp hV
      simpa using this
    subst hVbot
    rw [E6.mQuot_bot_eq_rk hUel]
    change (rk ↥D.U : ℕ∞) ≤ (rk ↥D.U : ℕ∞)
    exact le_rfl

private theorem commElt_ne_bot_of_not_centralizes {D : Data G} {t : G}
    (hMU : D.M ≤ Subgroup.normalizer (D.U : Set G)) (ht : t ∈ D.M)
    (htU : ¬ D.U ≤ Subgroup.centralizer ({t} : Set G)) : commElt D.U t ≠ ⊥ := by
  obtain ⟨u, huU, htu⟩ := Set.not_subset.mp htU
  have hcomm1 : u⁻¹ * t⁻¹ * u * t ≠ 1 := by
    intro h1
    apply htu
    change u ∈ Subgroup.centralizer ({t} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h2 : t⁻¹ * u * t = u := by
      have := congrArg (fun x => u * x) h1
      simpa [mul_assoc] using this
    have h2' : t * u = u * t := by
      calc t * u = t * (t⁻¹ * u * t) := by rw [h2]
        _ = u * t := by group
    exact h2'.symm
  intro hbot
  exact hcomm1 (by
    have hmem : u⁻¹ * t⁻¹ * u * t ∈ commElt D.U t :=
      Subgroup.subset_closure ⟨u, huU, rfl⟩
    rw [hbot] at hmem
    exact Subgroup.mem_bot.mp hmem)

private theorem calBn_zero_eq_empty {D : Data G} {Ch : Choice2011 G} (c : Ctx23 D Ch) :
    calBn 0 D.M D.U = ∅ := by
  have hMU : D.M ≤ Subgroup.normalizer (D.U : Set G) := (uc22p22e_inCalV_U D).2.2.1
  ext V
  refine iff_false_intro ?_
  rintro ⟨-, t, ht, htord, W, hWU, hmW, -, htW, hPB⟩
  obtain rfl : W = D.U :=
    (E3.mQuot_eq_zero_iff (Data.U_isPGroup D) hWU).mp (Nat.le_zero.mp hmW)
  have hct_ne : commElt D.U t ≠ ⊥ :=
    commElt_ne_bot_of_not_centralizes hMU ht.1 htW
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hct_ne
  have hx1' : (x : G) ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hctU : commElt D.U t ≤ D.U := by
    refine (Subgroup.closure_le (K := D.U)).2 ?_
    rintro y ⟨w, hw, rfl⟩
    have htw : t⁻¹ * w * t ∈ D.U :=
      (Subgroup.mem_normalizer_iff''.1 (hMU ht.1) w).1 hw
    rw [show w⁻¹ * t⁻¹ * w * t = w⁻¹ * (t⁻¹ * w * t) from by group]
    exact D.U.mul_mem (D.U.inv_mem hw) htw
  refine hPB ((Subgroup.centralizer_le ?_).trans
    (Ctx23.centralizer_le_M c (hctU x.2) hx1'))
  exact Set.singleton_subset_iff.mpr x.2

theorem betaN_eq_top_of_TI {D : Data G} {Ch : Choice2011 G} (c : Ctx23 D Ch) :
    betaN 0 D.M D.U = ⊤ := by
  have hempty := calBn_zero_eq_empty c
  simp [betaN, hempty]

end Ctx23

end CFSG.LocalAnalysis.UniquenessCase.UC22
