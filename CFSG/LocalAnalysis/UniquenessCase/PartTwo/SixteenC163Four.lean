module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.Quasithin.Background.F918V3S1
import CFSG.LocalAnalysis.RankThreeTheoremC.LayerNormal
import CFSG.Adapters.LieModelSimple
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatOdd

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

namespace C163

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem exists_four_factors {Γ : Type} [Group Γ] [Finite Γ] {A K : Subgroup Γ}
    (hK : IsComponentOf K A) (hK8 : UC22.IsL2 ↥K 3) {g φ : Γ} (hg : g ∈ A) (hφ : φ ∈ A)
    (hKg : K ≠ K.map (MulAut.conj g).toMonoidHom)
    (hcomm : ⁅K ⊔ K.map (MulAut.conj g).toMonoidHom,
      (K ⊔ K.map (MulAut.conj g).toMonoidHom).map (MulAut.conj φ).toMonoidHom⁆ = ⊥) :
    ∃ N : Fin 4 → Subgroup Γ, (∀ j, N j ≤ A) ∧ (∀ j, IsSimpleGroup ↥(N j)) ∧
      (∀ j, Subgroup.center ↥(N j) = ⊥) ∧ (∀ j, 3 ∣ Nat.card ↥(N j)) ∧
      (∀ j, 7 ∣ Nat.card ↥(N j)) ∧
      (∀ j l, j ≠ l → ∀ x ∈ N j, ∀ y ∈ N l, x * y = y * x) := by
  classical
  let cg : Γ →* Γ := (MulAut.conj g).toMonoidHom
  let cφ : Γ →* Γ := (MulAut.conj φ).toMonoidHom
  let N : Fin 4 → Subgroup Γ := ![K, K.map cg, K.map cφ, (K.map cg).map cφ]
  have hinjg : Function.Injective cg := (MulAut.conj g).injective
  have hinjφ : Function.Injective cφ := (MulAut.conj φ).injective
  have hKg' : K ≠ K.map cg := by simpa only [cg] using hKg
  have hcommN : ⁅K ⊔ K.map cg, (K ⊔ K.map cg).map cφ⁆ = ⊥ := by
    simpa only [cg, cφ] using hcomm
  have hKs : IsSimpleGroup ↥K :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hK8
  have hKcard : Nat.card ↥K = 504 :=
    CFSG.SeitzReduction.F4Pilot.card_of_lieModel_PSL_two_two_three hK8
  have e1 : ↥K ≃* ↥(K.map cg) := K.equivMapOfInjective cg hinjg
  have e2 : ↥K ≃* ↥(K.map cφ) := K.equivMapOfInjective cφ hinjφ
  have e3 : ↥K ≃* ↥((K.map cg).map cφ) :=
    e1.trans ((K.map cg).equivMapOfInjective cφ hinjφ)
  have hc : ∀ j, IsComponentOf (N j) A := by
    intro j
    fin_cases j
    · change IsComponentOf K A
      exact hK
    · change IsComponentOf (K.map cg) A
      exact CFSG.LocalAnalysis.RankThreeTheoremC.IsComponentOf.map_conj hK hg
    · change IsComponentOf (K.map cφ) A
      exact CFSG.LocalAnalysis.RankThreeTheoremC.IsComponentOf.map_conj hK hφ
    · change IsComponentOf ((K.map cg).map cφ) A
      exact CFSG.LocalAnalysis.RankThreeTheoremC.IsComponentOf.map_conj
        (CFSG.LocalAnalysis.RankThreeTheoremC.IsComponentOf.map_conj hK hg) hφ
  have hsimp : ∀ j, IsSimpleGroup ↥(N j) := by
    intro j
    fin_cases j
    · change IsSimpleGroup ↥K
      exact hKs
    · change IsSimpleGroup ↥(K.map cg)
      exact e1.isSimpleGroup_congr.mp hKs
    · change IsSimpleGroup ↥(K.map cφ)
      exact e2.isSimpleGroup_congr.mp hKs
    · change IsSimpleGroup ↥((K.map cg).map cφ)
      exact e3.isSimpleGroup_congr.mp hKs
  have hcard : ∀ j, Nat.card ↥(N j) = 504 := by
    intro j
    fin_cases j
    · simpa [N] using hKcard
    · simpa [N] using (Nat.card_congr e1.toEquiv).symm.trans hKcard
    · simpa [N] using (Nat.card_congr e2.toEquiv).symm.trans hKcard
    · simpa [N] using (Nat.card_congr e3.toEquiv).symm.trans hKcard
  have hcenter : ∀ j, Subgroup.center ↥(N j) = ⊥ := by
    intro j
    haveI := hsimp j
    haveI : Group.IsPerfect ↥(N j) := (Group.isPerfect_def).mpr (hc j).2.2.1
    exact TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative
      (Group.IsPerfect.not_isMulCommutative ↥(N j))
  have hdiv3 : ∀ j, 3 ∣ Nat.card ↥(N j) := fun j => by rw [hcard j]; norm_num
  have hdiv7 : ∀ j, 7 ∣ Nat.card ↥(N j) := fun j => by rw [hcard j]; norm_num
  have hsup0 : N 0 ≤ K ⊔ K.map cg := by
    simpa [N] using (le_sup_left : K ≤ K ⊔ K.map cg)
  have hsup1 : N 1 ≤ K ⊔ K.map cg := by
    simpa [N] using (le_sup_right : K.map cg ≤ K ⊔ K.map cg)
  have hsupφ2 : N 2 ≤ (K ⊔ K.map cg).map cφ := by
    simpa [N] using (Subgroup.map_mono (le_sup_left : K ≤ K ⊔ K.map cg) :
      (K.map cφ) ≤ (K ⊔ K.map cg).map cφ)
  have hsupφ3 : N 3 ≤ (K ⊔ K.map cg).map cφ := by
    simpa [N] using (Subgroup.map_mono (le_sup_right : K.map cg ≤ K ⊔ K.map cg) :
      ((K.map cg).map cφ) ≤ (K ⊔ K.map cg).map cφ)
  have hperf : ∀ j, ⁅N j, N j⁆ = N j := fun j =>
    (Subgroup.isPerfect_iff).mp ((Group.isPerfect_def).mpr (hc j).2.2.1)
  have hcross : ∀ j l : Fin 4, N j ≤ K ⊔ K.map cg →
      N l ≤ (K ⊔ K.map cg).map cφ → N j ≠ N l := by
    intro j l hj hl h_eq
    have hle : N j ≤ (K ⊔ K.map cg).map cφ := by rw [h_eq]; exact hl
    have hle' : ⁅N j, N j⁆ ≤ ⁅K ⊔ K.map cg, (K ⊔ K.map cg).map cφ⁆ :=
      Subgroup.commutator_mono hj hle
    rw [hcommN] at hle'
    have hbot : N j = ⊥ := (hperf j).symm.trans (le_bot_iff.mp hle')
    exact ((Subgroup.isSimpleGroup_iff).mp (hsimp j)).1 hbot
  have h01 : N 0 ≠ N 1 := by simpa [N] using hKg'
  have h23 : N 2 ≠ N 3 := by
    intro h
    have h' : K = K.map cg :=
      Subgroup.map_injective (f := cφ) hinjφ (by simpa [N] using h)
    exact hKg' h'
  have h02 : N 0 ≠ N 2 := hcross 0 2 hsup0 hsupφ2
  have h03 : N 0 ≠ N 3 := hcross 0 3 hsup0 hsupφ3
  have h12 : N 1 ≠ N 2 := hcross 1 2 hsup1 hsupφ2
  have h13 : N 1 ≠ N 3 := hcross 1 3 hsup1 hsupφ3
  have hNne : ∀ j l : Fin 4, j ≠ l → N j ≠ N l := by
    intro j l hjl h_eq
    fin_cases j <;> fin_cases l
    all_goals
      first
      | exact hjl rfl
      | exact h01 h_eq
      | exact h01 h_eq.symm
      | exact h23 h_eq
      | exact h23 h_eq.symm
      | exact h02 h_eq
      | exact h02 h_eq.symm
      | exact h03 h_eq
      | exact h03 h_eq.symm
      | exact h12 h_eq
      | exact h12 h_eq.symm
      | exact h13 h_eq
      | exact h13 h_eq.symm
  refine ⟨N, fun j => (hc j).1, hsimp, hcenter, hdiv3, hdiv7, ?_⟩
  intro j l hjl
  exact CFSG.Quasithin.F918V3S1.comp_commute (hc j) (hc l) (hNne j l hjl)

end C163

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
