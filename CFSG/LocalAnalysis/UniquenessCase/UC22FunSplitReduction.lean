module

public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitModels
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitRankOne
public import CFSG.GroupTheory.PermutingInnerSplit

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F14 (FunSet)
open scoped Pointwise


theorem funSplit_of_le_sup_centralizer {X : Type} [Group X] [Finite X]
    {q : ℕ} {B K T : Subgroup X}
    (hK : K ∈ FunSet (fundPred q) X T)
    (hBc : IsMulCommutative B) (hBo : Odd (Nat.card B)) (hB3 : ¬ 3 ∣ Nat.card B)
    (hT : IsPGroup 2 T)
    (hperm : (B : Set X) * (T : Set X) = (T : Set X) * (B : Set X))
    (hBK : B ≤ K ⊔ centralizer (K : Set X)) :
    B = (B ⊓ K) ⊔ (B ⊓ centralizer (K : Set X)) := by
  obtain ⟨p, e₀, e, hp, hp2, he₀, -, he, ⟨eK⟩⟩ :=
    exists_psl2_quotient_of_isFundamentalOver hK.1
  letI : Fact p.Prime := hp
  have he1 : 1 ≤ e := by rcases he with rfl | rfl <;> omega
  obtain ⟨s, hs, hinv⟩ := exists_inv_mod_centralizer_of_psl2_quotient
    hBK hBc hBo hB3 hT hperm hK.2 hp2 he1 eK
  exact CFSG.GroupTheory.eq_sup_inf_centralizer_of_permuting_inner hBc hBo hT hperm hBK
    (fun z hzK hzC => sq_eq_one_of_mem_fundamental_centralizer hK.1 hzK hzC)
    hs.1 hs.2 hinv

end CFSG.LocalAnalysis.UniquenessCase.UC22
