module

public import CFSG.Timmesfeld.ARS.Sec12Plane
public import CFSG.Timmesfeld.ARS.Sec13Star

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace Sec12

variable {A A₀ : Subgroup G} (hS : Sec12 R A A₀)
include hS

theorem deltaSet_inter_nonempty_of_mem_lambdaSet {B C : Subgroup G}
    (hB : B ∈ lambdaStar R A A₀) (hC : C ∈ lambdaStar R A A₀) (hCB : C ∈ lambdaSet R B) :
    (deltaSet R A A₀ B ∩ deltaSet R A A₀ C).Nonempty := by
  have := hS.hyp.finite
  have hR := hS.hyp.root
  have hiso := hS.hyp.noIsolated
  have hA := hS.mem
  have hBR : B ∈ R := hB.1.1.1
  have hCR : C ∈ R := hC.1.1.1
  rw [Set.nonempty_iff_ne_empty]
  intro hemp
  have hΛ := insert_insert_inter_eq hS.hyp hA hS.sec8 hS.max hS.opp hB hC hCB hemp
  have hpts : ∀ P ∈ lambdaStar R A A₀, P ∈ lambdaSet R B → P ≤ B ⊔ C := by
    intro P hP hPB
    by_cases hPC : P = C
    · rw [hPC]
      exact le_sup_right
    have hmem : P ∈ insert B (insert A (lambdaSet R B ∩ lambdaSet R A)) :=
      Or.inr (Or.inr ⟨hPB, hP.1⟩)
    rw [← hΛ] at hmem
    rcases hmem with h1 | h1 | ⟨-, hPCl⟩
    · exact absurd h1 hPB.1.2.1
    · exact absurd h1 hPC
    · exact hS.le_sup_of_mem_lambdaSet hB hC hP hCB hPB hPCl
  have hnorm : ∀ X ∈ leviSet R A A₀, ∀ x ∈ X, conjSub (B ⊔ C) x ≤ B ⊔ C := by
    intro X hX x hx
    have hxV : x ∈ levi R A A₀ := le_gen hX hx
    rcases hS.mem_deltaSet_or_special hB hX with hXB | hs
    ·
      have hxB : conjSub B x = B := conjSub_of_forall_commute fun b hb =>
        (hXB.2.1.2.2 b hb x hx).symm
      have hCx : conjSub C x ∈ lambdaStar R A A₀ := conjSub_mem_lambdaStar_of_mem_levi hR hC hxV
      have hCxB : conjSub C x ∈ lambdaSet R B := by
        have := conjSub_mem_lambdaSet hR hCB x
        rwa [hxB] at this
      rw [conjSub, Subgroup.map_sup, ← conjSub, ← conjSub, hxB]
      exact sup_le le_sup_left (hpts _ hCx hCxB)
    ·
      obtain ⟨hW, hWB, hWX⟩ := commutator_mem_lambdaStar hS.hyp hA hS.sec8.2 hS.opp hB hX hs
      have hWle : ⁅B, X⁆ ≤ B ⊔ C := hpts _ hW hWB
      have hsup : B ⊔ ⁅B, X⁆ = B ⊔ C :=
        (mem_lambdaSet_of_le_sup hR hiso hBR hCB hBR le_sup_left hW.1.1.1 hWle
          hWB.1.2.1.symm).2
      have hxW : conjSub ⁅B, X⁆ x = ⁅B, X⁆ := conjSub_of_forall_commute fun w hw =>
        (hWX.1.2.2 x hx w hw)
      rw [← hsup, conjSub, Subgroup.map_sup, ← conjSub, ← conjSub, hxW]
      refine sup_le ?_ le_sup_right
      exact (conjSub_le_commutator_sup (A := B) hx).trans (sup_comm _ _).le
  have hVN : levi R A A₀ ≤ Subgroup.normalizer ((B ⊔ C : Subgroup G) : Set G) :=
    iSup₂_le fun X hX => le_normalizer_of_conjSub_le fun x hx => hnorm X hX x hx
  have hMle : M R A ≤ B ⊔ C := by
    rw [M_eq_gen_lambdaStar hS.hyp hA hS.opp]
    refine gen_le fun P hP => ?_
    obtain ⟨v, hv, rfl⟩ :=
      exists_mem_levi_conjSub_eq_of_isSigmaMaximal hS.hyp hA hS.sec8.2 hS.max hS.opp hB hP
    calc conjSub B v ≤ conjSub (B ⊔ C) v := Subgroup.map_mono le_sup_left
      _ = B ⊔ C := conjSub_eq_self_iff.2 (hVN hv)
  have hab : Commuting (B ⊔ C) (B ⊔ C) :=
    Commuting.sup_right (Commuting.sup_right (hR.commuting_self hBR) hCB.1.2.2).symm
      (Commuting.sup_right hCB.1.2.2.symm (hR.commuting_self hCR)).symm
  apply hR.ne_bot A hA
  rw [← (Q_eq_M hS.hyp hA).2.2.1]
  exact commuting_iff_commutator_eq_bot.1 (hab.mono hMle hMle)

end Sec12

end CFSG.Timmesfeld.ARS
