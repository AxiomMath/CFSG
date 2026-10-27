module

public import CFSG.LocalAnalysis.StandardType.GGQTwoTBCGraphDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoTBCF4Core
import CFSG.LocalAnalysis.StandardType.GGQTwoTBCGraphD
import CFSG.LocalAnalysis.StandardType.GGQTwoTBCLift
import CFSG.LocalAnalysis.StandardType.GGQTwoTBCTransfer
import CFSG.LocalAnalysis.StandardType.GGQTwoGammaXGraphLin
import CFSG.LocalAnalysis.StandardType.GGE6DepFrameCentral
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyDichotomy
import CFSG.LocalAnalysis.StandardType.GGTableBF4Basic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley

section F4


theorem ggQ2TBCGraphF4Input_holds : GGQ2TBCGraphF4Input := by
  intro G _ _ p B Bs x L D J hS hp _ _ _ labL hmk htag M hLW hshape φ hφ hr hfix
  subst hp
  obtain ⟨hQ2, hlab, hmark⟩ := hmk
  obtain ⟨-, lab', hlab', hraw⟩ := hmark
  have heq : lab' = labL := GGDichotomy.rawDatum_elim_const
    (largeEvenRawDatum_mono (fun R _ I F hq => by
      obtain ⟨-, -, -, h⟩ := hq
      exact h) hraw)
  subst heq
  obtain ⟨hcfg, -, -, -, -⟩ := hS.1
  have hx1 : x ≠ 1 := hcfg.1.2.2.2.2.2.2.1.2.2.1
  have hfull : M.ShapeFull := ggQ2_shapeFull_of_graph M hLW hlab (Or.inr htag) hx1 hshape
  have hZ : ¬ 3 ∣ Nat.card ↥(Subgroup.center ↥L) := ggE6Dep_hZ hcfg hfull.1
  obtain ⟨tag, rank, n⟩ := lab'
  obtain rfl : tag = .F4 := htag
  have hn1 : 1 ≤ n := hlab'.1
  have hn2 : n < 2 := hQ2
  obtain rfl : n = 1 := by omega
  have hΛ : Fintype.card M.Λ = 4 := by
    obtain ⟨e, -⟩ := hLW
    exact (Fintype.card_congr e).symm.trans (Fintype.card_fin 4)
  dsimp only [LargeEvenRawDatum, CFSG.Assembly.LargeEvenRawDatumLegacy] at hraw
  obtain ⟨K, hKf, hKfin, hK, -, -, θ, -⟩ := hraw
  have hK2 : Nat.card K = 2 := by rw [hK]; norm_num
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := 1)
    (by rw [← Nat.card_eq_fintype_card, hK2]; norm_num)
  have : Finite ↥(adjointGroup .F4 K) := by
    have : Finite (Module.End K (RootModule .F4 K)) := Module.finite_of_finite K
    infer_instance
  let e : ↥L ⧸ Subgroup.center ↥L ≃* ↥(adjointGroup .F4 K) := θ.trans (TableBF4.recipeEquiv K)
  let f : ↥L →* ↥(adjointGroup .F4 K) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : f.ker = Subgroup.center ↥L := by
    ext l
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk l) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hcore : GGTBCReflCoreIn 4 L :=
    (ggTBCReflCoreIn_iff L).mpr (ggTBCReflCore_of_surjective f hf hker.le
      (by rw [hker]; exact hZ) (TBCF4.ggTBCReflCore_F4Two hK2))
  exact ggQ2_tbc_of_coreIn hS M hfull (by rw [hΛ]; exact hcore) hφ hr hfix

theorem ggQ2TBCGraphInput_holds : GGQ2TBCGraphInput :=
  ggQ2TBCGraphInput_of_F4 ggQ2TBCGraphF4Input_holds

end F4

end CFSG.StandardType

end
