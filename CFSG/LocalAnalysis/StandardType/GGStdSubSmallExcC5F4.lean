module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestThreeLift
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5F4Orb
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5F4Torus

public section

namespace CFSG.StandardType.SmallExc.F4Two

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem ggStdSubTwoTorusEltNormSmall_of_weak {p r : ℕ} {R : Type} [Group R]
    (h : EltNormWeak p r R) : GGStdSubTwoTorusEltNormSmall p r R :=
  fun A hA hr h3 hα a ha ha1 D hDC hDn hDq _ _ => h A hA hr h3 hα a ha ha1 D ⟨hDC, hDn, hDq⟩

section Certs


theorem eltNormWeak_adjointF4Two {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) (h3C : GGF4TwoThreeCSolv K) :
    EltNormWeak 3 3 (adjointGroup .F4 K) := by
  intro A hA _ h27 hα a ha ha1 D hD
  obtain ⟨β, hβ⟩ := exists_mulEquiv_le_range_torus3 hK hA h27 hα
  refine eltConcl_of_map β (eltConcl_mono ?_
    (eltConcl_range_torus3 hK h3C (hβ a ha) ?_ (eltHyp_map β hD)))
  · rintro _ ⟨s, hs, rfl⟩
    exact hβ s hs
  · exact fun h1 => ha1 (β.injective (h1.trans (map_one β).symm))

theorem ggF4TwoNormSmallInput_of_threeC (h : GGF4TwoThreeCSolvInput) : GGF4TwoNormSmallInput := by
  intro K _ _ hK
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK])
  exact ggStdSubTwoTorusNormSmall_of_elt Nat.prime_three (ggIE_outdiagPrime_F4Two (K := K))
    (TableBF4.center_recipeGroup_eq_bot K)
    (ExcSplitL.ggCenterPrime_recipe_F4 Nat.prime_three (by norm_num))
    (ggStdSubTwoTorusEltNormSmall_of_weak (eltNormWeak_of_mulEquiv (TableBF4.recipeEquiv K)
      (eltNormWeak_adjointF4Two hK (h K hK))))

end Certs

end CFSG.StandardType.SmallExc.F4Two

end
