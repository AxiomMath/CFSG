module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69S7M
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69S7MPairs
import CFSG.Mathlib.GroupTheory.SylowPairJoins
import CFSG.RankThree.Native.HSMcLFiveCentralizers
public import CFSG.Sporadic.Schreier.PairMcLCertBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

private theorem mcl275P_eq_of_dvd
    {V : Subgroup (Equiv.Perm (Fin 275))} (hVG : V ≤ CFSG.RankThree.Native.mcl275P)
    (hV : 3 ^ 4 * 5 ^ 3 ∣ Nat.card V) : V = CFSG.RankThree.Native.mcl275P := by
  obtain ⟨R, B, hRG, hR, hNR, hB, hjoin, hpair⟩ := exists_mcl_five_pair_joins
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact CFSG.eq_of_sylow_pair_joins (p := 5) (m := 3 ^ 4) hRG
    (by rw [hR, CFSG.RankThree.Native.factorization_card_mcl275P_five]; norm_num)
    hjoin hpair (by rw [hR, hNR]; decide) (fun k => by rw [hB k, hNR]; decide) hVG
    (by rw [hR]; exact dvd_trans (by decide) hV) (dvd_trans (dvd_mul_right _ _) hV)

theorem mclThreeFiveMax_holds :
    McLThreeFiveMax := by
  intro U hU
  have e : CFSG.Blueprint.NativeSporadic.McL ≃* ↥CFSG.Sporadic.Schreier.mclP :=
    CFSG.Sporadic.Schreier.mclPermEquiv
  let f : CFSG.Blueprint.NativeSporadic.McL →* ↥CFSG.Sporadic.Schreier.mclP := e
  have hf : Function.Injective f := e.injective
  set V : Subgroup (Equiv.Perm (Fin 275)) :=
    (U.map f).map CFSG.Sporadic.Schreier.mclP.subtype with hV
  have hcard : Nat.card V = Nat.card U := by
    rw [hV, Subgroup.card_map_of_injective (f := CFSG.Sporadic.Schreier.mclP.subtype)
      Subtype.val_injective, Subgroup.card_map_of_injective hf]
  have hVeq : V = CFSG.RankThree.Native.mcl275P :=
    mcl275P_eq_of_dvd (Subgroup.map_subtype_le _) (hcard ▸ hU)
  rw [Subgroup.eq_top_iff']
  intro x
  have hx : ((f x : CFSG.Sporadic.Schreier.mclP) : Equiv.Perm (Fin 275)) ∈ V := by
    rw [hVeq]
    exact (f x).2
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hy
  rwa [hf (Subtype.ext hyx)] at hu

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
