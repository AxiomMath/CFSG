module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec5.Thm53AuxA7
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec5.Thm53AuxA9

public section

open CFSG.Open
open scoped Pointwise

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

namespace Thm53A

variable {G : Type u} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {θ : G → Subgroup G}

omit [Finite G] in
theorem admits_centralizer_of_le {A B : Subgroup G} (hA : IsMulCommutative A) (hBA : B ≤ A) :
    Admits A (Subgroup.centralizer (B : Set G)) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  simp only [Subgroup.mem_centralizer_iff]
  constructor
  · intro hx b hb
    exact ((commute_conj_iff (commute_of_mem hA hg (hBA hb))).mpr (hx b hb).symm).symm
  · intro hx b hb
    exact ((commute_conj_iff (commute_of_mem hA hg (hBA hb))).mp (hx b hb).symm).symm

theorem cenIn_le_normalizer_sol
    (h : Counterexample p A θ) {W : Subgroup G}
    (hW : Setting p A θ W) (hI : ∀ Y ∈ dset p A θ, thetaMG p A θ Y ∈ assoc p A θ)
    (hin : CompInput p W) {S : Subgroup G} (hSm : S ∈ mhat p A θ)
    (hSsol : Group.IsSolvable ↥S) (hsolS : sol W ≤ S) {B : Subgroup G}
    (hB : B ∈ signalizerFunctorEk p 2 A) :
    cenIn S (B : Set G) ≤ Subgroup.normalizer (sol W : Set G) := by
  have hθ := h.hyp.nearFunctor
  intro c hc
  have hcS : c ∈ S := hc.1
  have hcH : c ∈ thetaOf θ B := inf_centralizer_le_thetaOf hSm.1 hB.1 hc
  have hcZ : c ∈ Subgroup.normalizer (WB W B : Set G) :=
    thetaOf_le_normalizer_WB h hW hI hin hB.1 hcH
  have hZm : WB W B ∈ mhat p A θ := WB_mem_mhat hθ hW.mem_mtil hB.1
  have hgr := hW.isGreatest (WB W B) hZm S hSm (WB_mul_sol hθ hW.mem_mtil hin hB) hSsol hsolS
  have hadm : Admits (WB W B) (sol W) :=
    ((WB_le_kOf W B).trans (kOf_le W)).trans (Thm41Aux.le_normalizer_sol W)
  have hSnorm : c ∈ Subgroup.normalizer (S : Set G) := Subgroup.le_normalizer hcS
  obtain ⟨hMle, hMadm⟩ := Thm41Aux.map_conj_mem_of_admits hcZ hSnorm ⟨hsolS, hadm⟩
  have hle := hgr.2 ⟨hMle, hMadm⟩
  have hcard : Nat.card (sol W) ≤
      Nat.card ((sol W).map ((MulAut.conj c : G ≃* G) : G →* G)) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj c : G ≃* G).injective]
  exact Thm41Aux.mem_normalizer_of_map_conj_eq (Subgroup.eq_of_le_of_card_ge hle hcard)

theorem kOf_ne_bot
    (h : Counterexample p A θ) {W : Subgroup G} (hW : Setting p A θ W)
    (hI : ∀ Y ∈ dset p A θ, thetaMG p A θ Y ∈ assoc p A θ) (hin : CompInput p W) :
    kOf W ≠ ⊥ := by
  intro hb
  have hperf := perfRes_le_kOf h hW hI hin
  rw [hb] at hperf
  exact hW.not_isSolvable ((perfRes_eq_bot_iff W).mp (le_bot_iff.mp hperf))

theorem sol_ne_bot
    (h : Counterexample p A θ) {W : Subgroup G} (hW : Setting p A θ W)
    (hI : ∀ Y ∈ dset p A θ, thetaMG p A θ Y ∈ assoc p A θ) (hin : CompInput p W) :
    sol W ≠ ⊥ := by
  intro hbot
  have hθ := h.hyp.nearFunctor
  have hKassoc : kOf W ∈ assoc p A θ :=
    mem_assoc_of_le hθ.prime hW.mem_mtil.1 (kOf_le W)
      (hW.mem_mtil.1.1.trans (Thm52Aux.normalizer_le_normalizer_kOf W))
  obtain ⟨Θ, hΘ, -, hΘmax⟩ := h.isLocallyComplete (kOf W) hKassoc (kOf_ne_bot h hW hI hin)
  obtain ⟨B, hB, hnot⟩ := h.exists_not_kOf_le_thetaOf hΘ
  refine hnot ?_
  have hBne : B ≠ ⊥ := by
    rintro rfl
    have h2 := hB.2
    rw [Subgroup.card_bot] at h2
    exact (Nat.one_lt_pow (by norm_num) hθ.prime.one_lt).ne h2
  have hnorm : thetaOf θ B ≤ Subgroup.normalizer (kOf W : Set G) := by
    have h1 := thetaOf_le_normalizer_WB h hW hI hin hB.1
    have hsup := WB_sup_sol hθ hW.mem_mtil hin hB
    rw [hbot, sup_bot_eq] at hsup
    rwa [hsup] at h1
  exact (kOf_le _).trans (hΘmax _ (thetaOf_mem_assoc hθ hB.1 hBne) hnorm)

theorem ssol_le
    (h : Counterexample p A θ) {W : Subgroup G} (hW : Setting p A θ W)
    (hI : ∀ Y ∈ dset p A θ, thetaMG p A θ Y ∈ assoc p A θ) (hin : CompInput p W)
    {S : Subgroup G} (hSm : S ∈ mhat p A θ) (hSsol : Group.IsSolvable ↥S) (hsolS : sol W ≤ S) :
    S ≤ W := by
  have hθ := h.hyp.nearFunctor
  have hsolm : sol W ∈ mhat p A θ := sol_mem_mhat hθ hW.mem_mtil
  obtain ⟨Y, hY, -, hYmax⟩ := h.isLocallyComplete (sol W) hsolm.1 (sol_ne_bot h hW hI hin)
  have hWY : W ≤ Y := hYmax W hW.mem_mtil.1 (Thm41Aux.le_normalizer_sol W)
  have hDY : dsub A θ ≤ Y :=
    hYmax _ (dsub_mem_assoc hθ) (hW.mem_mtil.2.trans (Thm41Aux.le_normalizer_sol W))
  have hYm : Y ∈ mhat p A θ := ⟨hY, admits_dsub_of_le hDY⟩
  have hYW : Y ≤ W := hW.le_of_kOf_le Y hYm ((kOf_le W).trans hWY)
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation p 2
    hθ.prime A S hθ.elemAbelian (by rw [h.hyp.card]) hSm.1.1 hSm.1.2.1
  rw [← hgen]
  refine iSup₂_le fun B hB => ?_
  have hadm : Admits A (cenIn S (B : Set G)) :=
    Admits.inf hSm.1.1 (admits_centralizer_of_le hθ.elemAbelian.1 hB.1)
  have hcB : cenIn S (B : Set G) ∈ assoc p A θ :=
    mem_assoc_of_le hθ.prime hSm.1 inf_le_left hadm
  exact (hYmax _ hcB (cenIn_le_normalizer_sol h hW hI hin hSm hSsol hsolS hB)).trans hYW

end Thm53A

end CFSG.SignalizerFunctorTheorem.McBride.Near
