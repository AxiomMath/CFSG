module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeFourteenFiveInst
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ThreeLStarClosure
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeOneABoundShape

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem ncard_conjSet_barSub_K_le_two {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    {A K : Subgroup G} (hA : IsElemAbelian 2 A)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G)) (hK : K ∈ calC c.L)
    (hconf : K = c.L ∨ ∃ t ∈ D.T, c.L = K ⊔ K.map (MulAut.conj t).toMonoidHom) :
    (conjSet (barSub (⊥ : Subgroup G) A hA K) (barSub (⊥ : Subgroup G) A hA D.T)).ncard ≤ 2 := by
  classical
  have hNstab : c.N ≤ stabTil (⊥ : Subgroup G) A := N_le_stabTil_of_le_normalizer c hAN
  have hKstab : K ≤ stabTil (⊥ : Subgroup G) A :=
    ((CFSG.Quasithin.A3.subnormal_le hK.1).trans (Ctx23L.L_le_N c)).trans hNstab
  have hTstab : D.T ≤ stabTil (⊥ : Subgroup G) A := (Ctx23L.T_le_N c).trans hNstab
  have hTL : D.T ≤ Subgroup.normalizer (c.L : Set G) := c.hL.1.1
  have hconj : ∀ X ∈ conjSet (barSub (⊥ : Subgroup G) A hA K)
      (barSub (⊥ : Subgroup G) A hA D.T),
      ∃ g ∈ D.T, X = barSub (⊥ : Subgroup G) A hA (K.map (MulAut.conj g).toMonoidHom) := by
    rintro X ⟨s, hs, rfl⟩
    obtain ⟨g, hgT, hgs⟩ := (mem_barSub (⊥ : Subgroup G) A hA D.T s).1 hs
    refine ⟨g, hgT, ?_⟩
    rw [TwelveTwentyThree.barSub_map_conj hA hKstab (hTstab hgT)]
    rw [show actTil (⊥ : Subgroup G) A hA ⟨g, hTstab hgT⟩ = s from hgs]
  rcases hconf with hsingle | ⟨t, htT, hsup⟩
  · have hsub : conjSet (barSub (⊥ : Subgroup G) A hA K) (barSub (⊥ : Subgroup G) A hA D.T) ⊆
        {barSub (⊥ : Subgroup G) A hA K} := by
      intro X hX
      obtain ⟨g, hgT, rfl⟩ := hconj X hX
      have hKg : K.map (MulAut.conj g).toMonoidHom = K := by
        rw [hsingle]
        exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTL hgT)
      rw [hKg]
      rfl
    calc _ ≤ ({barSub (⊥ : Subgroup G) A hA K} : Set _).ncard :=
          Set.ncard_le_ncard hsub (Set.finite_singleton _)
      _ ≤ 2 := by rw [Set.ncard_singleton]; omega
  · have hKt : K.map (MulAut.conj t).toMonoidHom ∈ calC c.L :=
      calC_map_conj_of_mem_normalizer hK (hTL htT)
    have hsub : conjSet (barSub (⊥ : Subgroup G) A hA K) (barSub (⊥ : Subgroup G) A hA D.T) ⊆
        {barSub (⊥ : Subgroup G) A hA K,
          barSub (⊥ : Subgroup G) A hA (K.map (MulAut.conj t).toMonoidHom)} := by
      intro X hX
      obtain ⟨g, hgT, rfl⟩ := hconj X hX
      rcases eq_or_eq_of_mem_calC_of_sup_eq hK hKt hsup
          (calC_map_conj_of_mem_normalizer hK (hTL hgT)) with h | h
      · exact Or.inl (by rw [h])
      · exact Or.inr (by rw [h]; rfl)
    calc _ ≤ ({barSub (⊥ : Subgroup G) A hA K,
            barSub (⊥ : Subgroup G) A hA (K.map (MulAut.conj t).toMonoidHom)} : Set _).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ 2 := (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])

end CFSG.LocalAnalysis.UniquenessCase.UC22
