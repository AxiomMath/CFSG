module

public import CFSG.Timmesfeld.ARS.Sec13Commuting

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace Sec13

variable {A A₀ : Subgroup G} (hS : Sec13 R A A₀)
include hS

theorem commutator_le_gen_deltaSet {B X Y : Subgroup G} (hX : X ∈ deltaSet R A A₀ B)
    (hY : Y ∈ leviSet R A A₀) (hYB : Commuting Y B) : ⁅X, Y⁆ ≤ gen (deltaSet R A A₀ B) := by
  have hR := hS.hyp.root
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have hXy : conjSub X y ∈ deltaSet R A A₀ B := by
    rw [← conjSet_deltaSet_eq_of_commuting hR hY hYB hy]
    exact conjSub_mem_conjSet hX y
  rw [commutatorElement_def, show x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) by group]
  exact Subgroup.mul_mem _ (le_gen hX hx) (le_gen hXy (conj_mem_conjSub y (X.inv_mem hx)))

theorem exists_mem_deltaSet_not_commuting {C D : Subgroup G} (hC : C ∈ lambdaStar R A A₀)
    (hD : D ∈ lambdaStar R A A₀) (hCD : C ∈ lambdaSet R D) :
    ∃ X ∈ deltaSet R A A₀ D, ¬ Commuting C X := by
  have := hS.hyp.finite
  have hR := hS.hyp.root
  have hiso := hS.hyp.noIsolated
  have hDR : D ∈ R := hD.1.1.1
  obtain ⟨X, hX, hCXD⟩ :=
    exists_commutator_eq_of_mem_lambdaStar hS.hyp hS.mem hS.sec8.2 hS.opp hC hD hCD
  have hs : Special R C X :=
    special_of_commutator_mem_of_mem_leviSet hS.hyp hS.mem hC hX (hCXD ▸ hDR)
  have hXD : X ∈ lambdaSet R D := by
    have := (mem_lambdaSet_commutator hR hiso hC.1.1.1 hX.1.1 hs).2
    rwa [hCXD] at this
  exact ⟨X, ⟨hX, hXD⟩, hs.not_commuting hR⟩

theorem eq_of_forall_commuting (hcl : LeviClosed R A A₀) {B C : Subgroup G}
    (hB : B ∈ lambdaStar R A A₀) (hC : C ∈ lambdaStar R A A₀)
    (hCB : ∀ X ∈ deltaSet R A A₀ C, Commuting X B) : C = B := by
  have := hS.hyp.finite
  have hR := hS.hyp.root
  have hiso := hS.hyp.noIsolated
  have hA := hS.mem
  have hBR : B ∈ R := hB.1.1.1
  have hCR : C ∈ R := hC.1.1.1
  by_contra hne
  by_cases h1 : ∃ E ∈ deltaSet R A A₀ B, ¬ Commuting E C
  ·
    obtain ⟨E, hE, hEC⟩ := h1
    have hER : E ∈ R := hE.1.1.1
    have hsCE : Special R C E :=
      special_of_not_commuting_of_mem_leviSet hS.hyp hA hC hE.1 fun h' => hEC h'.symm
    obtain ⟨e, he, he1⟩ := hR.exists_ne_one hER
    have heV : e ∈ levi R A A₀ := le_gen hE.1 he
    have hCe : conjSub C e ∈ lambdaStar R A A₀ := conjSub_mem_lambdaStar_of_mem_levi hR hC heV
    have hCene : conjSub C e ≠ C := Sec3.conjSub_ne_of_special hR hiso hER hCR hsCE.symm he he1
    obtain ⟨-, hKC, -⟩ := commutator_mem_lambdaStar hS.hyp hA hS.sec8.2 hS.opp hC hE.1 hsCE
    have hCeC : conjSub C e ∈ lambdaSet R C :=
      (mem_lambdaSet_of_le_sup hR hiso hCR hKC hCR le_sup_left hCe.1.1.1
        ((conjSub_le_commutator_sup (A := C) he).trans (sup_comm _ _).le) hCene.symm).1
    have hsub : ∀ L ∈ deltaSet R A A₀ (conjSub C e), Commuting L C := by
      intro L hL
      rw [← conjSet_deltaSet hR heV] at hL
      obtain ⟨F, hF, rfl⟩ := hL
      dsimp only
      have hFC : Commuting F C := hF.2.1.2.2.symm
      by_cases hFE : Commuting F E
      · rwa [conjSub_of_forall_commute fun f hf => (hFE f hf e he).symm]
      · have hFB := hCB F hF
        have hsFE : Special R F E := by
          have hne' : F ≠ E := fun e' => hFE (e' ▸ hR.commuting_self hF.1.1.1)
          rcases hR.rel _ hF.1.1.1 _ hER hne' with h2 | h2 | h2
          · exact absurd h2 hFE
          · exact absurd hFB (not_commuting_of_opposite_of_mem_lambdaSet hR hF.1.1.1 h2
              (mem_lambdaSet_comm hBR hE.2))
          · exact h2
        have hKΔ := Levi.commutator_mem_leviSet hR hA hS.opp hF.1 hE.1 hsFE
        have hKF : ⁅F, E⁆ ∈ lambdaSet R F :=
          mem_lambdaSet_comm hsFE.1 (mem_lambdaSet_commutator hR hiso hF.1.1.1 hER hsFE).1
        have hKCc := commuting_of_mem_deltaSet_of_mem_lambdaSet hS.hyp hA hS.opp hC hF hKΔ hKF
        exact (Commuting.sup_left hKCc hFC).mono (conjSub_le_commutator_sup he) le_rfl
    obtain ⟨X, hX, hCX⟩ := hS.exists_mem_deltaSet_not_commuting hC hCe
      (mem_lambdaSet_comm hCR hCeC)
    exact hCX (hsub X hX).symm
  ·
    push Not at h1
    have h2 : ∃ X ∈ deltaSet R A A₀ B, ∃ Y ∈ deltaSet R A A₀ C, ¬ Commuting X Y := by
      by_contra! h3
      apply hne
      refine hS.eq_of_deltaSet_eq hC hB (Set.Subset.antisymm ?_ ?_)
      · rw [← hS.setOf_forall_commuting_eq hB]
        exact fun Y hY => ⟨hY.1, fun X hX => (h3 X hX Y hY).symm⟩
      · rw [← hS.setOf_forall_commuting_eq hC]
        exact fun X hX => ⟨hX.1, fun Y hY => h3 X hX Y hY⟩
    obtain ⟨X, hX, Y, hY, hXY⟩ := h2
    have hsXY : Special R X Y := by
      have hne' : X ≠ Y := fun e' => hXY (e' ▸ hR.commuting_self hX.1.1.1)
      rcases hR.rel _ hX.1.1.1 _ hY.1.1.1 hne' with h3 | h3 | h3
      · exact absurd h3 hXY
      · exact absurd (hCB Y hY) (not_commuting_of_opposite_of_mem_lambdaSet hR hY.1.1.1 h3.symm
          (mem_lambdaSet_comm hBR hX.2))
      · exact h3
    have hKΔ := Levi.commutator_mem_leviSet hR hA hS.opp hX.1 hY.1 hsXY
    have hKB : ⁅X, Y⁆ ∈ deltaSet R A A₀ B := by
      rw [← hS.setOf_le_gen_deltaSet_eq hB]
      exact ⟨hKΔ, hS.commutator_le_gen_deltaSet hX hY.1 (hCB Y hY)⟩
    have hKC : ⁅X, Y⁆ ∈ deltaSet R A A₀ C := by
      rw [← hS.setOf_le_gen_deltaSet_eq hC, Subgroup.commutator_comm]
      exact ⟨Subgroup.commutator_comm X Y ▸ hKΔ,
        hS.commutator_le_gen_deltaSet hY hX.1 (h1 X hX)⟩
    have hBC : B ∉ lambdaSet R C := by
      intro hBC
      obtain ⟨Z, hZ, hBZ⟩ := hS.exists_mem_deltaSet_not_commuting hB hC hBC
      exact hBZ (hCB Z hZ).symm
    have hBCc : Commuting B C := by
      rcases commuting_or_commutator_eq_of_mem_lambdaSet hS.hyp hA hB.1 hC.1
        (fun e' => hne e'.symm) with h3 | h3
      · exact h3
      · exfalso
        have hle : A ≤ ⁅X, Y⁆ := by
          rw [← h3.2, ← (Q_eq_M hS.hyp hKB.1.1.1).2.2.1]
          exact Subgroup.commutator_mono (QD.le_M (mem_lambdaSet_comm hBR hKB.2))
            (QD.le_M (mem_lambdaSet_comm hCR hKC.2))
        exact hKΔ.1.2.1 (QD.eq_of_le_of_mem hR hiso hA hKΔ.1.1 hle).symm
    obtain ⟨D, ⟨hD, hDB⟩, hDC⟩ := hS.lambdaStar_inter_nonempty hcl hB hC hBCc
    obtain ⟨X', hX', hX'B⟩ :=
      exists_commutator_eq_of_mem_lambdaStar hS.hyp hA hS.sec8.2 hS.opp hD hB hDB
    have hsDX' : Special R D X' :=
      special_of_commutator_mem_of_mem_leviSet hS.hyp hA hD hX' (hX'B ▸ hBR)
    have hX'Bl : X' ∈ lambdaSet R B := by
      have := (mem_lambdaSet_commutator hR hiso hD.1.1.1 hX'.1.1 hsDX').2
      rwa [hX'B] at this
    have hX'C := h1 X' ⟨hX', hX'Bl⟩
    have hle : B ≤ M R C := by
      rw [← hX'B]
      exact commutator_le_of_le_normalizer (QD.le_M hDC)
        (QD.le_normalizer_M hR hCR ⟨hX'.1.1, hX'C.symm⟩)
    exact hBC (mem_lambdaSet_of_le_M_of_hyp hS.hyp hCR hBR hle fun e' => hne e'.symm)

theorem eq_of_le_normalizer (hcl : LeviClosed R A A₀) {B C : Subgroup G}
    (hB : B ∈ lambdaStar R A A₀) (hC : C ∈ lambdaStar R A A₀)
    (hCB : ∀ X ∈ deltaSet R A A₀ C, ∀ x ∈ X,
      conjSet (deltaSet R A A₀ B) x = deltaSet R A A₀ B) : C = B :=
  hS.eq_of_forall_commuting hcl hB hC fun X hX =>
    hS.commuting_of_forall_conjSet_eq hB hX.1 (hCB X hX)

end Sec13

end CFSG.Timmesfeld.ARS
