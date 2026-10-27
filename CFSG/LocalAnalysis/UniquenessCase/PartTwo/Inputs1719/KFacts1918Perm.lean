module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFacts1918Quot
import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2Sp4Two
import CFSG.Quasithin.EmptyFaithful.SzF53BasFin

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem oUpperTwo_top_perm (k : ℕ) :
    S17.oUpperTwo (⊤ : Subgroup (Equiv.Perm (Fin k))) = alternatingGroup (Fin k) := by
  rw [S17.oUpperTwo_eq_closure]
  simpa using CFSG.SeitzReduction.F4Pilot.closure_odd_eq_alternatingGroup

theorem opp_top_perm (k : ℕ) : Opp 2 (⊤ : Subgroup (Equiv.Perm (Fin k))) = ⊤ := by
  apply le_antisymm le_top
  have hle : Subgroup.closure {σ : Equiv.Perm (Fin k) | σ.IsSwap} ≤
      Opp 2 (⊤ : Subgroup (Equiv.Perm (Fin k))) := by
    unfold Opp CFSG.RankThree.PartOne.pElementSubgroup
    apply Subgroup.closure_mono
    intro σ hσ
    exact ⟨Subgroup.mem_top σ, ⟨1, by simp [hσ.orderOf]⟩⟩
  rwa [Equiv.Perm.closure_isSwap] at hle

theorem alternatingGroup_le_of_normal_perm {k : ℕ} (hk : k = 3 ∨ 5 ≤ k)
    {N : Subgroup (Equiv.Perm (Fin k))} (hN : N.Normal) (hne : N ≠ ⊥) :
    alternatingGroup (Fin k) ≤ N := by
  rcases hk with rfl | hk5
  · haveI : N.Normal := hN
    exact CFSG.Quasithin.F53.normal_ge_alt3 N hne
  · haveI : N.Normal := hN
    haveI : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).2 hne
    exact Equiv.Perm.alternatingGroup_le_of_normal (by simpa using hk5) inferInstance

theorem kFacts1918_of_perm {X : Type} [Group X] [Finite X] (Y : Subgroup X) {k : ℕ}
    (hk : k = 3 ∨ 5 ≤ k) (φ : ↥Y →* Equiv.Perm (Fin k)) (hφ : Function.Surjective φ)
    (hker : φ.ker = CFSG.pCore 2 ↥Y) :
    (∀ Nn : Subgroup X, Nn ≤ Opp 2 Y → (Nn.subgroupOf (Opp 2 Y)).Normal →
      ¬ Nn ≤ pCoreOf 2 (Opp 2 Y) → S17.oUpperTwo (Opp 2 Y) ≤ Nn ⊔ pCoreOf 2 (Opp 2 Y)) ∧
    Nat.card (Bar2 (S17.oUpperTwo (Opp 2 Y))) = k.factorial / 2 := by
  have hY : Opp 2 Y = Y :=
    opp_eq_self_of_quot Y φ hφ (by rw [hker]; exact CFSG.pCore_isPGroup)
      (opp_top_perm k)
  rw [hY]
  have hmin : ∀ N : Subgroup (Equiv.Perm (Fin k)), N.Normal → N ≠ ⊥ →
      S17.oUpperTwo (⊤ : Subgroup (Equiv.Perm (Fin k))) ≤ N := by
    intro N hN hne
    rw [oUpperTwo_top_perm k]
    exact alternatingGroup_le_of_normal_perm hk hN hne
  refine ⟨?_, ?_⟩
  · intro Nn hNnY hNn hNnQ
    exact oUpperTwo_le_sup_pCoreOf_of_quot Y φ hφ (le_of_eq hker) hmin Nn hNnY hNn hNnQ
  · haveI : Nontrivial (Fin k) :=
      Fintype.one_lt_card_iff_nontrivial.mp (by
        rw [Fintype.card_fin]
        rcases hk with h3 | h5 <;> omega)
    calc
      Nat.card (Bar2 (S17.oUpperTwo Y))
          = Nat.card (S17.oUpperTwo (⊤ : Subgroup (Equiv.Perm (Fin k)))) :=
            card_bar2_oUpperTwo_of_quot Y φ hφ hker
      _ = Nat.card (alternatingGroup (Fin k)) := by rw [oUpperTwo_top_perm k]
      _ = k.factorial / 2 := by
            rw [nat_card_alternatingGroup]
            simp

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
