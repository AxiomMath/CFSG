module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveF4Contracts
public import CFSG.LocalAnalysis.StandardType.GGF4B3CoreDefs
import CFSG.LocalAnalysis.StandardType.GGF4B3Pair
import CFSG.LocalAnalysis.StandardType.GGSecFiveRootRefl
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoRowE
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelTypeAAssembly
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
import TauCeti.GroupTheory.Coxeter.Geometric

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem automizerJoin_le_ggInduced_F4 {G : Type} [Group G] {Bs : Subgroup G}
    (L : Subgroup G) (𝒦 : Finset (Subgroup G)) :
    ggAutomizerJoin L Bs 𝒦 ≤ ggInduced ⊤ Bs := by
  intro φ hφ
  rw [ggAutomizerJoin] at hφ
  exact mem_ggInduced_top_of_mem_ggAutomizer
    (sup_le (ggAutomizer_mono Bs le_top)
      (iSup₂_le fun K _ => ggAutomizer_mono Bs le_top) hφ)

private theorem automizer_sup_le_automizerJoin_F4 {G : Type} [Group G] {Bs L : Subgroup G}
    {𝒦 : Finset (Subgroup G)} {K : Subgroup G} (hK : K ∈ 𝒦) :
    ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦 := by
  rw [ggAutomizerJoin]
  exact sup_le le_sup_left (le_sup_of_le_right (le_iSup₂_of_le K hK le_rfl))

theorem ggSecFiveF4OriginalBCPairInput_of_core
    (hCore : GGF4B3Core) : GGSecFiveF4OriginalBCPairInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR hT1 ι M e hP hF hB3
  classical
  obtain ⟨e', rfl⟩ := hF
  obtain ⟨hp, hp2, -⟩ := (hR.1.1.1.2.2.2.2.2.1 : p ∈ CFSG.Assembly.LargeEvenBeta 4 G)
  have hEl : CFSG.Assembly.IsElemAbelian p Bs := hR.1.1.2.1.2.1
  have hNT : GGNoTransvection p Bs := hR.1.2.2.2.1
  have hAind : ggAutomizerJoin L Bs 𝒦 ≤ ggInduced ⊤ Bs := automizerJoin_le_ggInduced_F4 L 𝒦
  have hG2 : ¬ ∃ e'' : Fin 2 ≃ ι, CoxeterMatrix.F₄.reindex e' = CoxeterMatrix.G₂.reindex e'' := by
    rintro ⟨e'', -⟩
    have h := Fintype.card_congr (e''.trans e'.symm)
    simp at h
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦),
      ∀ j : ι, Θ (CoxeterMatrix.F₄.simple (e'.symm j)) =
        e ((CoxeterMatrix.F₄.reindex e').simple j) :=
    ⟨((CoxeterMatrix.F₄.reindexGroupEquiv e').symm).trans e, fun j => by
      simp [CoxeterMatrix.reindexGroupEquiv_symm_apply_simple]⟩
  let cs : CoxeterSystem CoxeterMatrix.F₄ ↥(ggAutomizerJoin L Bs 𝒦) :=
    CoxeterMatrix.F₄.toCoxeterSystem.map Θ
  have hconv : ∀ (φ : MulAut ↥Bs) (hφ : φ ∈ ggAutomizerJoin L Bs 𝒦), GGIsReflection p φ →
      cs.IsReflection ⟨φ, hφ⟩ := by
    intro φ hφ hr
    obtain ⟨j, g, hg⟩ := SecFiveRootRefl.ggSecFiveRootReflInput_holds G p Bs hp hp2 hEl hNT
      (ggAutomizerJoin L Bs 𝒦) hAind ι (CoxeterMatrix.F₄.reindex e') hP.1 hG2 e hP.2
      ⟨φ, hφ⟩ hr
    refine ⟨e g, e'.symm j, ?_⟩
    have hs : cs.simple (e'.symm j) = e ((CoxeterMatrix.F₄.reindex e').simple j) := hΘ j
    rw [hs, hg, map_mul, map_mul, map_inv]
  obtain ⟨eB, hEB⟩ := hB3
  have hALA : ggAutomizer L Bs ≤ ggAutomizerJoin L Bs 𝒦 := le_sup_left
  obtain ⟨a, ha_def⟩ : ∃ a : Fin 3 → ↥(ggAutomizerJoin L Bs 𝒦), ∀ i,
      a i = Subgroup.inclusion hALA (eB ((CoxeterMatrix.B 3).simple i)) :=
    ⟨fun i => Subgroup.inclusion hALA (eB ((CoxeterMatrix.B 3).simple i)), fun i => rfl⟩
  have ha : ∀ i, cs.IsReflection (a i) := by
    intro i
    rw [ha_def i]
    exact hconv (eB ((CoxeterMatrix.B 3).simple i) : MulAut ↥Bs)
      (hALA (eB ((CoxeterMatrix.B 3).simple i)).2) (hEB i)
  have hord : ∀ i j : Fin 3, orderOf (a i * a j) = (CoxeterMatrix.B 3).M i j := by
    intro i j
    have h1 : a i * a j = Subgroup.inclusion hALA
        (eB ((CoxeterMatrix.B 3).simple i * (CoxeterMatrix.B 3).simple j)) := by
      rw [ha_def i, ha_def j, map_mul, map_mul]
    rw [h1, orderOf_injective (Subgroup.inclusion hALA) (Subgroup.inclusion_injective hALA),
      MulEquiv.orderOf_eq eB]
    simpa using (CoxeterMatrix.B 3).toCoxeterSystem.orderOf_simple_mul_simple i j
  have o01 : orderOf (a 0 * a 1) = 3 := by
    rw [hord 0 1]; first | decide | rfl | simp [CoxeterMatrix.B]
  have o12 : orderOf (a 1 * a 2) = 4 := by
    rw [hord 1 2]; first | decide | rfl | simp [CoxeterMatrix.B]
  have o02 : orderOf (a 0 * a 2) = 2 := by
    rw [hord 0 2]; first | decide | rfl | simp [CoxeterMatrix.B]
  have haAL : ∀ i, ((a i : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ∈ ggAutomizer L Bs := by
    intro i
    rw [ha_def i]
    exact (eB ((CoxeterMatrix.B 3).simple i)).2
  have hAL : ggAutomizer L Bs ≤ Subgroup.closure
      (Set.range fun i : Fin 3 => ((a i : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)) := by
    have h := closure_range_simple_of_equiv eB
    have hfun : (fun i : Fin 3 => ((a i : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)) =
        fun i => ((eB ((CoxeterMatrix.B 3).simple i) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) := by
      funext i
      rw [ha_def i]
      rfl
    rw [hfun]
    exact h.symm.le
  have hAK : ∀ K ∈ 𝒦, ggAutomizer K Bs ≤ Subgroup.closure
      {x : MulAut ↥Bs | ∃ t : ↥(ggAutomizerJoin L Bs 𝒦), cs.IsReflection t ∧
        (t : MulAut ↥Bs) = x ∧ x ∈ ggAutomizer K Bs} := by
    intro K hK
    obtain ⟨y, hN⟩ := hR.2.2.2.1.2 K hK
    have hKA : ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦 := by
      rw [ggAutomizerJoin]
      exact le_sup_of_le_right (le_iSup₂_of_le K hK le_rfl)
    have hrefl : GGReflGenerated p (ggAutomizer K Bs) := hR.2.1 y K hN
    refine hrefl.le.trans (Subgroup.closure_mono ?_)
    intro φ hφ
    exact ⟨⟨φ, hKA hφ.1⟩, hconv φ (hKA hφ.1) hφ.2, rfl, hφ.1⟩
  have hA : ggAutomizerJoin L Bs 𝒦 ≤ ggAutomizer L Bs ⊔ ⨆ K ∈ 𝒦, ggAutomizer K Bs := by
    unfold ggAutomizerJoin
    exact le_rfl
  obtain ⟨K, hK, hKle⟩ := ggF4B3_exists_pair_of_core hCore cs a ha o01 o12 o02
    (AL := ggAutomizer L Bs) haAL hAL (𝒦 := 𝒦) (AK := fun K => ggAutomizer K Bs) hAK hA
  obtain ⟨y, hN⟩ := hR.2.2.2.1.2 K hK
  exact ggSecFiveWeylAt_of_join_eq hN
    (le_antisymm (automizer_sup_le_automizerJoin_F4 hK) hKle) e hP

end CFSG.StandardType

end
