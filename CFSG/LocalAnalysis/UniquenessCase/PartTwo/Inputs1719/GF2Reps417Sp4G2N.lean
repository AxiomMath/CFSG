module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2Reps417Sp4G2NPair
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2Reps417Sp4G2NG2Par
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsNoO2Normal
import CFSG.Quasithin.H13.NQCatL2LieParabolic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

theorem bParam_le_two_mul_of_isSp4_of_noSwap
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y L T : Subgroup (MulAut W)} {n : ℕ} (hLT : L ⊔ T = Y) (hcomp : IsComponentOf L Y)
    (hsyl : IsSylowIn 2 T Y) (hO2 : O2Trivial Y) (hfix : fixV T ≠ fixV Y)
    (hTN : T ≤ Subgroup.normalizer (L : Set (MulAut W))) (hn : 2 ≤ n) (hSp : IsSp4 ↥L n)
    (hsw : ¬ S17.SwapsParabolics (T ⊓ Subgroup.normalizer (L : Set (MulAut W))) L) :
    bParam L Y ≤ 2 * n := by
  obtain ⟨P, -, hmax, hP, hgen⟩ := CFSG.Quasithin.H13.NQCat.factL2LieParabolic_holds ↥L n hn
    (Or.inr hSp) _ (isSylowTwoOf_subgroupOf_inf hcomp hsyl)
  have hTinf : T ⊓ Subgroup.normalizer (L : Set (MulAut W)) = T := inf_eq_left.mpr hTN
  have hinvP : ∀ j, ∀ t ∈ T, t ∈ Subgroup.normalizer (L : Set (MulAut W)) →
      ((P j).map L.subtype).map (MulAut.conj t).toMonoidHom = (P j).map L.subtype := by
    intro j t ht htN
    by_contra hne
    apply hsw
    refine ⟨t, ⟨ht, htN⟩, (P j).map L.subtype, ?_, hne⟩
    have h1 := isMaxParabolicOver_map_subtype_of_isCoatom L
      (covBy_top_iff.mp ((hmax (P j) (hP j).1.le).2 ⟨j, rfl⟩)) (hP j).1.le
    rw [hTinf]
    rwa [Subgroup.subgroupOf_map_subtype, inf_assoc, inf_idem] at h1
  have hinvY : ∀ j, ∀ t ∈ T, t ∈ Subgroup.normalizer (L : Set (MulAut W)) →
      ((perfectCore (P j)).map L.subtype).map (MulAut.conj t).toMonoidHom =
        (perfectCore (P j)).map L.subtype := by
    intro j t ht htN
    rw [CFSG.Quasithin.map_perfectCore L.subtype, CFSG.Quasithin.map_perfectCore,
      hinvP j t ht htN]
  refine bParam_le_of_pair_of_conj_inv hW hLT hcomp hsyl hO2 hfix (Y₁ := perfectCore (P 0))
    (Y₂ := perfectCore (P 1)) ?_ (CFSG.Quasithin.perfectCore_perfect _)
    (CFSG.Quasithin.perfectCore_perfect _)
    (Or.inl (CFSG.Quasithin.RonanF918.lieModel_of_isPSL (hP 0).2.2))
    (Or.inl (CFSG.Quasithin.RonanF918.lieModel_of_isPSL (hP 1).2.2))
    (hinvY 0) (hinvY 1) (by omega)
  rw [hgen, top_sup_eq]

theorem bParam_le_two_mul_of_isG2
    (hG : K_G2ParabolicGen)
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y L T : Subgroup (MulAut W)} {n : ℕ} (hLT : L ⊔ T = Y) (hcomp : IsComponentOf L Y)
    (hsyl : IsSylowIn 2 T Y) (hO2 : O2Trivial Y) (hfix : fixV T ≠ fixV Y)
    (hn : 2 ≤ n) (hG2 : UC22.IsG2 ↥L n) : bParam L Y ≤ 2 * n := by
  obtain ⟨Y₁, Y₂, hperf₁, hperf₂, hL2₁, hL2₂, hgen, hinv⟩ :=
    hG ↥L n hn hG2 _ (isSylowTwoOf_subgroupOf_inf hcomp hsyl)
  exact bParam_le_of_pair_of_aut_inv hW hLT hcomp hsyl hO2 hfix hgen hperf₁ hperf₂
    (Or.inl hL2₁) (Or.inl hL2₂) hinv (by omega)

theorem w4Lem4_17Sp4G2N_holds :
    W4Lem4_17Sp4G2N := by
  intro W _ _ hW Y L T n hLY hTY hLT hcomp hsyl hfix hodd hTN hn hSG
  refine bParam_le_of_noO2_of_normal (P := fun X _ => IsSp4 X n ∨ IsG2 X n)
    (hP := fun {X X'} _ _ e hh => hh.imp (fun h => h.of_mulEquiv e) (fun h => h.of_mulEquiv e))
    (B := 2 * n) ?_ hW hLY hTY hLT hcomp hsyl hfix hodd hTN hSG
  intro U _ _ hu Y' L' T' hLT' hcomp' hsyl' hO2' hfix' hTN' hPL
  rcases hPL with hSp | hG2
  · by_cases hsw : S17.SwapsParabolics (T' ⊓ Subgroup.normalizer (L' : Set (MulAut U))) L'
    · have h1 := bParam_le_of_w4Lem4_17_one
        CFSG.LocalAnalysis.WeakClosure81.FourFiveLayer.w3Lem45_2Chief_holds hu hLT' hcomp'
        hsyl' hO2' hfix' (Or.inr (Or.inr (Or.inr ⟨Or.inr (Or.inr hSp), hsw⟩)))
      omega
    · exact bParam_le_two_mul_of_isSp4_of_noSwap hu hLT' hcomp' hsyl' hO2' hfix' hTN'
        (by omega) hSp hsw
  · exact bParam_le_two_mul_of_isG2 k_G2ParabolicGen_holds hu hLT' hcomp' hsyl' hO2' hfix'
      (by omega) hG2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
