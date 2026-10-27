module

public import CFSG.Quasithin.Background.RonanE68Inn
public import CFSG.Quasithin.Background.RonanE68Mat
public import CFSG.Quasithin.Background.RonanE611Sp4

public section

namespace CFSG.Quasithin.RonanE68

open CFSG.Open CFSG.Quasithin CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.Quasithin.SteinbergBS CFSG.RankThree.PartOne.KCRootAxis CFSG.Quasithin.RonanE611

section Marking

variable {G : Type} [Group G] {L V W : Subgroup G}

theorem conj_injective_of_center_eq_bot {X : Type*} [Group X] (hZ : Subgroup.center X = ⊥) :
    Function.Injective (MulAut.conj : X →* MulAut X) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hc : g ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro x
    have := congrArg (fun α : MulAut X => α x) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    exact (mul_inv_eq_iff_eq_mul.1 this).symm
  rw [hZ] at hc
  exact hc

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem isMarkedSp4Root_of_root {n : ℕ} (hK : Nat.card K = 2 ^ n) (hZ : Subgroup.center ↥L = ⊥)
    (φ : ↥L ≃* antiSp K) (i : Axis) (hW : W = (rootU K i).map (Sp4G.emb φ))
    (hVN : V ≤ Subgroup.normalizer (L : Set G)) (hWV : W ≤ V)
    (hdec : ∀ v ∈ V, ∃ w ∈ W, ∀ x ∈ L, v * x * v⁻¹ = w * x * w⁻¹) :
    E6.IsMarkedSp4Root n (autSubInduced L (L ⊔ V)) (autSubInduced L V) := by
  classical
  have hWL : W ≤ L := by
    rw [hW]
    rintro _ ⟨x, -, rfl⟩
    exact Sp4G.emb_mem φ x
  have hY := autSubInduced_sup_eq_range hVN hWV hWL hdec
  have hR := autSubInduced_eq_map_conj hVN hWV hWL hdec
  have hinj := conj_injective_of_center_eq_bot hZ
  refine ⟨fun α ⟨g, hg, h⟩ => ⟨g, ⟨Subgroup.mem_sup_right hg.1, hg.2⟩, h⟩, K, inferInstance,
    inferInstance, inferInstance, hK, ?_⟩
  let e1 : ↥(autSubInduced L (L ⊔ V)) ≃* ↥(MulAut.conj : ↥L →* MulAut ↥L).range :=
    MulEquiv.subgroupCongr hY
  let e2 : ↥L ≃* ↥(MulAut.conj : ↥L →* MulAut ↥L).range := MonoidHom.ofInjective hinj
  let Ψ : ↥L ≃* ↥(StatedSp 2 K) := φ.trans (antiSpEquiv K)
  let marking : ↥(autSubInduced L (L ⊔ V)) ≃* ↥(StatedSp 2 K) :=
    (e1.trans e2.symm).trans Ψ
  have hmem : ∀ g : ↥(StatedSp 2 K),
      g ∈ ((autSubInduced L V).subgroupOf (autSubInduced L (L ⊔ V))).map marking.toMonoidHom ↔
        (antiSpEquiv K).symm g ∈ rootU K i := by
    intro g
    rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf]
    have h1 : ((marking.symm g : ↥(autSubInduced L (L ⊔ V))) : MulAut ↥L) =
        MulAut.conj (Ψ.symm g) := by
      show ((e1.symm (e2 (Ψ.symm g)) : ↥(autSubInduced L (L ⊔ V))) : MulAut ↥L) = _
      rfl
    rw [h1, hR, Subgroup.mem_map_iff_mem hinj, Subgroup.mem_subgroupOf]
    have h2 : ((Ψ.symm g : ↥L) : G) = Sp4G.emb φ ((antiSpEquiv K).symm g) := by
      show ((φ.symm ((antiSpEquiv K).symm g) : ↥L) : G) = _
      rfl
    rw [h2, hW]
    exact Subgroup.mem_map_iff_mem (Sp4G.emb_injective φ)
  have hmap : ((autSubInduced L V).subgroupOf (autSubInduced L (L ⊔ V))).map marking.toMonoidHom =
      (rootU K i).map (antiSpEquiv K).toMonoidHom := by
    ext g
    rw [hmem g, Subgroup.mem_map_equiv]
  refine ⟨marking, ?_⟩
  cases i
  ·
    refine ⟨antiSpEquiv K (CFSG.Quasithin.E6.E68Proof.Sp4.pElt2 : antiSp K), Or.inr ?_⟩
    rw [hmap, Sp4G.rootU_one, map_rootShort_antiSpEquiv]
  ·
    refine ⟨1, Or.inl ?_⟩
    rw [hmap, Sp4G.rootU_two, map_rootLong_antiSpEquiv]
    ext g
    simp

end Marking

end CFSG.Quasithin.RonanE68
