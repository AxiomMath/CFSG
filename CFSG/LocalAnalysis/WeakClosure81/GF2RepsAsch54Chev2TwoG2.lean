module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Chev2TwoFrame
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Chev2TwoFamEx
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Chev2G2

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Chev2Orbit

open CFSG.Quasithin CFSG.Open CFSG.ComponentClassification.CatLeaf Subgroup CFSG.QuasithinUnique
  CFSG.AGLEmbeddingD2.Tits.GN516.SimpleBQ

theorem lGen_eq_top_of_lieModel_g2
    {Q : Type} [Group Q] [Finite Q] {L T : Subgroup Q} [hLn : L.Normal]
    (hLs : IsSimpleGroup ↥L) (hnab : ∃ a b : ↥L, a * b ≠ b * a) (hq : Group.IsSolvable (Q ⧸ L))
    (hT : IsSylowIn 2 T ⊤) (hL0 : ∀ (X : Type) [Group X], IsCalL0 X → ∃ a b : X, a * b ≠ b * a)
    (hO : LieOrderFormulasInput) {n : ℕ} (hm : CFSG.Models.LieModel ↥L .G2 n 2 2) :
    lGen IsCalL0 ⊤ T = ⊤ := by
  obtain ⟨K, hK, hKfin, D, w, H, π, e, hbq, hsmall, hrank⟩ := exists_bqSmall_g2 hO hm
  have hT2 : IsSylowTwoOf T ⊤ := ⟨hT.1, hT.2.1, hT.2.2⟩
  have hS : IsSylowTwoOf (T ⊓ L) L :=
    CFSG.Quasithin.A4.isSylowTwoOf_inf_normal hT2 le_top
      (@Subgroup.le_normalizer_of_normal Q _ L ⊤ hLn)
  obtain ⟨π', hbq', hunip⟩ := exists_borelQuotient_conj hS hbq
  by_cases htr : NodeTransitive L T D H π'
  · obtain ⟨t, ht, P, hPL, hPmax, hPN, hPne⟩ :=
      exists_swap_of_nodeTransitive hbq' hunip htr hrank
    exact (false_of_swap_g2 hLn hm hT ht hPL hPmax hPN hPne).elim
  · exact lGen_eq_top_of_bqSmall hLs hnab hq hT hL0 hbq' hunip hsmall htr

end CFSG.LocalAnalysis.WeakClosure81.Chev2Orbit
