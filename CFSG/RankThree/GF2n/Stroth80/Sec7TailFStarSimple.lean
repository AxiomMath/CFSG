module

public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.Assembly.Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup CFSG

theorem fstar_eq_of_simple {Y : Type} [Group Y] [Finite Y] {S : Subgroup Y} [S.Normal]
    (hS : IsSimpleGroup S) (hnab : ∃ a ∈ S, ∃ b ∈ S, a * b ≠ b * a)
    (hC : ∀ c : Y, (∀ s ∈ S, c * s = s * c) → c = 1)
    (hO2 : ∀ P : Subgroup Y, P.Normal → IsPGroup 2 P → P = ⊥)
    (hO : ∀ P : Subgroup Y, P.Normal → Odd (Nat.card P) → P = ⊥) :
    generalizedFitting Y = S := by
  have hcore : ∀ p : ℕ, p.Prime → CFSG.pCore p Y = ⊥ := by
    intro p hp
    haveI : Fact p.Prime := ⟨hp⟩
    by_cases h2 : p = 2
    · subst h2
      exact hO2 _ CFSG.pCore_normal CFSG.pCore_isPGroup
    · refine hO _ CFSG.pCore_normal ?_
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp (CFSG.pCore_isPGroup (p := p) (G := Y))
      rw [hn]
      exact (hp.odd_of_ne_two h2).pow
  have hF : CFSG.fittingSubgroup Y = ⊥ := by
    rw [CFSG.fitting_eq_sup_pCore Y, eq_bot_iff]
    refine iSup_le fun p => ?_
    exact (hcore _ (Nat.prime_of_mem_primeFactors p.1.2)).le
  have hnab' : ∃ x y : S, x * y ≠ y * x := by
    obtain ⟨a, ha, b, hb, hab⟩ := hnab
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩
  haveI : IsSimpleGroup S := hS
  have hSq : CFSG.IsQuasisimple S := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab').1
  have hSc : CFSG.IsComponent S := ⟨hSq, Subgroup.Normal.isSubnormal inferInstance⟩
  have hL : CFSG.layer Y = S := by
    rw [CFSG.layer.eq_sSup Y]
    refine le_antisymm (sSup_le fun K hK => ?_) (le_sSup hSc)
    rcases CFSG.LocalCores.component_normal_subgroup (N := S) hK inferInstance with h | h
    · exact h
    · exfalso
      have hKc : K ≤ Subgroup.centralizer (S : Set Y) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
      have hKbot : K = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have hx1 : x = 1 :=
          hC x fun s hs => (Subgroup.mem_centralizer_iff.mp (hKc hx) s hs).symm
        rw [hx1]
        exact one_mem _
      exact (Subgroup.nontrivial_iff_ne_bot K).mp
        (CFSG.LocalCores.isQuasisimple_nontrivial hK.1) hKbot
  rw [CFSG.generalizedFitting.eq_sup Y, hF, bot_sup_eq, hL]

end CFSG.RankThree.GF2n.Stroth80
