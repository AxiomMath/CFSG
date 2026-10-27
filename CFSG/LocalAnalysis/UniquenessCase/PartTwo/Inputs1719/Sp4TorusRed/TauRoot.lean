module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TorusRed.TauTorus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TorusRed

open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.Assembly.LowTwoRank
open CFSG.QuasithinUnique.Lin2.Five (tauSp tauMat tauPair)

variable {K : Type} [Field K] [CharP K 2]

theorem tauSp_pairRootElt_of_short {a b : Fin 2 ⊕ Fin 2} (hab : a ≠ b) (hb : b ≠ a.swap) :
    ∃ c : Fin 2 ⊕ Fin 2, ∀ t : K,
      tauSp (pairRootElt hab t) = pairRootElt (swap_ne_self c).symm (t ^ 2) := by
  have key : ∀ c : Fin 2 ⊕ Fin 2, (∀ t : K, tauMat (pairRootMat K a b t) =
      pairRootMat K c c.swap (t ^ 2)) → ∃ c : Fin 2 ⊕ Fin 2, ∀ t : K,
        tauSp (pairRootElt hab t) = pairRootElt (swap_ne_self c).symm (t ^ 2) :=
    fun c h => ⟨c, fun t => statedSp_ext (h t)⟩
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    simp only [ne_eq, Sum.inl.injEq, Sum.inr.injEq, Sum.swap_inl, Sum.swap_inr, reduceCtorEq,
      not_false_eq_true, not_true_eq_false, Fin.isValue, Fin.zero_eta, Fin.mk_one] at hab hb ⊢
  on_goal 1 => refine key (Sum.inl 1) fun t => ?_
  on_goal 2 => refine key (Sum.inr 1) fun t => ?_
  on_goal 3 => refine key (Sum.inl 0) fun t => ?_
  on_goal 4 => refine key (Sum.inl 0) fun t => ?_
  on_goal 5 => refine key (Sum.inr 0) fun t => ?_
  on_goal 6 => refine key (Sum.inr 0) fun t => ?_
  on_goal 7 => refine key (Sum.inr 1) fun t => ?_
  on_goal 8 => refine key (Sum.inl 1) fun t => ?_
  all_goals
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [CFSG.QuasithinUnique.Lin2.Five.tauMat_apply, tauPair, pairRootMat, rootNil,
        lineSign, CharTwo.neg_eq, CharTwo.sub_eq_add, sq]

theorem exists_long_root_le_map_tauSp [Finite K] {H : Subgroup (StatedSp 2 K)}
    {a b : Fin 2 ⊕ Fin 2} (hab : a ≠ b) (hb : b ≠ a.swap)
    (hH : ∀ s : K, pairRootElt hab s ∈ H) :
    ∃ c : Fin 2 ⊕ Fin 2, ∀ s : K, pairRootElt (swap_ne_self c).symm s ∈ H.map tauSp := by
  obtain ⟨c, hc⟩ := tauSp_pairRootElt_of_short (K := K) hab hb
  refine ⟨c, fun s => ?_⟩
  obtain ⟨u, rfl⟩ := isSquare_of_charTwo' (R := K) s
  rw [← sq u, ← hc u]
  exact Subgroup.mem_map_of_mem _ (hH u)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TorusRed

end
