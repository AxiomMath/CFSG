module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDFrame
public import CFSG.LocalAnalysis.StandardType.GGQTwoJoinDefs
import CFSG.LocalAnalysis.StandardType.GGQTwoDCox
public import CFSG.LocalAnalysis.StandardType.GGQTwoDSevenPatterns

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn.QTwo

section Contain

variable {G : Type} [Group G]

theorem ggRankTwoIn_le (X Bs : Subgroup G) (r r' : MulAut ↥Bs) : ggRankTwoIn X Bs r r' ≤ X := by
  rw [ggRankTwoIn, ggOTwoPrime]
  exact (Subgroup.closure_le X).mpr fun y hy => (Subgroup.mem_inf.mp hy.1).1

theorem le_of_map_conj_le_of_mem {S H : Subgroup G} {g : G} (hg : g ∈ H)
    (h : S.map (MulAut.conj g).toMonoidHom ≤ H) : S ≤ H := by
  intro s hs
  have h1 : g * s * g⁻¹ ∈ H := h (Subgroup.mem_map.mpr ⟨s, hs, rfl⟩)
  have h2 := H.mul_mem (H.mul_mem (H.inv_mem hg) h1) hg
  have h3 : g⁻¹ * (g * s * g⁻¹) * g = s := by group
  rwa [h3] at h2

end Contain

section Cfg

variable {G : Type} [Group G] [Finite G] {Bs X : Subgroup G} {L : Subgroup G}
  {𝒦 : Finset (Subgroup G)} {ι : Type} {M : CoxeterMatrix ι}
  {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} {m : ℕ} {e' : Fin m ≃ ι}

theorem qtwo_transport_mem (hfacts : QTwoMemberFacts Bs X M (ggAutomizerJoin L Bs 𝒦) e)
    {T : Finset (Fin m)} {w : M.Group}
    (hw : ∀ t ∈ T, qtwoConjRefl e e' w t ∈ ggAutomizer X Bs) :
    ∃ g ∈ L ⊔ ⨆ K ∈ 𝒦, K, (∀ t ∈ T, (qtwoNode Bs (qtwoRefl e e') t).map
        (MulAut.conj g).toMonoidHom = ggRankOneIn X Bs (qtwoConjRefl e e' w t)) ∧
      ∀ s t : Fin m, (ggRankTwo Bs (qtwoRefl e e' s) (qtwoRefl e e' t)).map
          (MulAut.conj g).toMonoidHom =
        ggRankTwo Bs (qtwoConjRefl e e' w s) (qtwoConjRefl e e' w t) := by
  obtain ⟨g, hgY, -, hg⟩ := exists_lift_of_mem_ggAutomizerJoin (𝒦 := 𝒦) (e w).2
  have hconj : ∀ t : Fin m, ((e w : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) *
      qtwoRefl e e' t * ((e w : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)⁻¹ =
        qtwoConjRefl e e' w t := fun t => coe_conj_simple e w (e' t)
  refine ⟨g, hgY, fun t ht => ?_, fun s t => ?_⟩
  · have h1 : (qtwoNode Bs (qtwoRefl e e') t).map (MulAut.conj g).toMonoidHom =
        ggRankOne Bs (qtwoConjRefl e e' w t) := by
      rw [← hconj t]
      exact ggRankOne_map_conj hg _
    rw [h1]
    exact hfacts.1 _ (hw t ht) (conjRefl_mem_ggCoxRefl e e' w t)
  · rw [ggRankTwo_map_conj hg, hconj s, hconj t]

theorem qtwoW_le_of_frame {H : Subgroup G} (hH : L ⊔ ⨆ K ∈ 𝒦, K ≤ H) (hX : X ≤ H)
    (hfacts : QTwoMemberFacts Bs X M (ggAutomizerJoin L Bs 𝒦) e)
    (hm : 5 ≤ m) (hM : M = (ggCoxeterMatrixD m).reindex e')
    (hF : QTwoFrameAt Bs X M (ggAutomizerJoin L Bs 𝒦) e e') {i j : Fin m} (hij : i ≠ j) :
    qtwoW Bs (qtwoRefl e e') i j ≤ H := by
  have : Finite ι := Finite.of_equiv (Fin m) e'
  obtain ⟨w, hw⟩ := orbAt_of_frame_of_conj e hM hF (T := {i, j})
    (qtwo_exists_conj_into_parab_pairA3 hm (Or.inl ⟨i, j, hij, rfl⟩))
  have hwi : qtwoConjRefl e e' w i ∈ ggAutomizer X Bs := hw i (by simp)
  have hwj : qtwoConjRefl e e' w j ∈ ggAutomizer X Bs := hw j (by simp)
  obtain ⟨g, hgY, hg1, hg2⟩ := qtwo_transport_mem hfacts (T := {i, j}) hw
  refine le_of_map_conj_le_of_mem (hH hgY) ?_
  rcases ggCoxeterMatrixD_two_or_three i j hij with h2 | h3
  · rw [qtwoW_of_nonedge _ h2, Subgroup.map_sup, hg1 i (by simp), hg1 j (by simp)]
    exact sup_le ((ggRankOneIn_le _ _ _).trans hX) ((ggRankOneIn_le _ _ _).trans hX)
  · have hE := hfacts.2.1 _ hwi (conjRefl_mem_ggCoxRefl e e' w i) _ hwj
      (conjRefl_mem_ggCoxRefl e e' w j) (conjRefl_noncomm e e' hM w h3)
    rw [qtwoW_of_edge _ h3, hg2, hE]
    exact (ggRankTwoIn_le _ _ _ _).trans hX

end Cfg

section Inputs


@[expose] def GGQTwoRMInputOn (R : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)) (ι : Type) (M : CoxeterMatrix ι)
    (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)), GGQTwoDCfg p B Bs x L D J 𝒦 M e →
      ∀ (m : ℕ) (e' : Fin m ≃ ι), R m → M = (ggCoxeterMatrixD m).reindex e' →
        ∀ (y : G) (K' : Subgroup G), GGNbr p B x D J y K' →
          ggAutomizer K' Bs ≤ ggAutomizerJoin L Bs 𝒦

@[expose] def GGQTwoRMInput : Prop :=
  GGQTwoRMInputOn fun m => 7 ≤ m

@[expose] def GGQTwoGNInputOn (R : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)) (ι : Type) (M : CoxeterMatrix ι)
    (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)), GGQTwoDCfg p B Bs x L D J 𝒦 M e →
      ∀ (m : ℕ) (e' : Fin m ≃ ι), R m → M = (ggCoxeterMatrixD m).reindex e' →
        ∀ (y : G) (K' : Subgroup G), GGNbr p B x D J y K' →
          ggAutomizer K' Bs ≤ ggAutomizerJoin L Bs 𝒦 →
            K' ≤ ⨆ (n : G) (_ : n ∈ K') (_ : ∃ φ : MulAut ↥Bs,
                n ∈ Subgroup.normalizer (Bs : Set G) ∧
                  ∀ b : ↥Bs, ((φ b : ↥Bs) : G) = n * b * n⁻¹),
              J.map (MulAut.conj n).toMonoidHom

@[expose] def GGQTwoGNInput : Prop :=
  GGQTwoGNInputOn fun m => 7 ≤ m

@[expose] def GGQTwoEdgeLeInputOn (R : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)) (ι : Type) (M : CoxeterMatrix ι)
    (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)), GGQTwoDCfg p B Bs x L D J 𝒦 M e →
      ∀ (m : ℕ) (e' : Fin m ≃ ι), R m → M = (ggCoxeterMatrixD m).reindex e' →
        ∀ i j : Fin m, i ≠ j → qtwoW Bs (qtwoRefl e e') i j ≤ ggG0 p B x L D J

theorem ggQTwoEdgeLeInput_of_cells {R : ℕ → Prop} (hR : ∀ m, R m → 5 ≤ m)
    (hOrth : GGQTwoCellInputOn R qtwoOrthL) (hUnit : GGQTwoCellInputOn R qtwoOrthL.compl) :
    GGQTwoEdgeLeInputOn R := by
  classical
  intro G _ _ p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM i j hij
  have hJoin : L ⊔ ⨆ K ∈ 𝒦, K ≤ ggG0 p B x L D J :=
    ggJoin_le_ggG0 (Bs := Bs) hcfg.1.2.2.2.1
  by_cases hc : qtwoOrthL G L 𝒦
  · obtain ⟨X, hfacts, hframe, hX⟩ := hOrth G p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM hc
    exact qtwoW_le_of_frame hJoin hX hfacts (hR m hm) hM hframe hij
  · obtain ⟨X, hfacts, hframe, hX⟩ := hUnit G p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM hc
    exact qtwoW_le_of_frame hJoin hX hfacts (hR m hm) hM hframe hij

end Inputs

end CFSG.StandardType.QTwo

end
