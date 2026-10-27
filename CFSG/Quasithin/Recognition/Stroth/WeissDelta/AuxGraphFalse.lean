module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.AuxGraphLocal4
public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.VertexFacts
public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.Lemma5Kernel2
public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.Lemma5Transitive
public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.AuxGraphLocal3

public section

open scoped Pointwise

namespace CFSG.Quasithin.Stroth.WeissDelta

variable {V : Type} {Γ : SimpleGraph V} {H : Type} [Group H] [MulAction H V] [GraphAction H Γ]

attribute [local instance] auxAction

private theorem finite_auxS [Finite V] (W : ClosedGoodPath H Γ) : Finite ↥W.auxS := by
  haveI : Finite ↥(auxComp Γ (W.kernelAt 0) (W.x 0)) := Subtype.finite
  haveI : Finite (Equiv.Perm ↥(auxComp Γ (W.kernelAt 0) (W.x 0))) := inferInstance
  exact Finite.of_injective
    (fun x : ↥W.auxS => (x : Equiv.Perm ↥(auxComp Γ (W.kernelAt 0) (W.x 0))))
    Subtype.val_injective

private theorem exists_auxI_sixPath [Finite V] [Finite H] {W : ClosedGoodPath H Γ}
    (hQ : W.QuarterHyp) : ∃ p : GPath W.auxI 6, p.NoBack := by
  obtain ⟨hne, -, -, -, -⟩ := hQ.aux_local
  obtain ⟨p, -, -⟩ := exists_auxI_path hQ
    ⟨W.x 0, SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩
  obtain ⟨q, hq, -⟩ := exists_backward_noBack hne (p.adj 0 (by norm_num)) 6
  exact ⟨q, hq⟩

private theorem false_of_secondKernel_ne_bot [Finite V] [Finite H] {W : ClosedGoodPath H Γ}
    (hQ : W.QuarterHyp)
    (hM : MoufangCondition ↥W.auxS W.auxI 4) (hW : WeissFree ↥W.auxS W.auxI 4)
    (hL : ∀ u : ↥(auxComp Γ (W.kernelAt 0) (W.x 0)), LocalFacts ↥W.auxS W.auxI u)
    (hR : ∀ u : ↥(auxComp Γ (W.kernelAt 0) (W.x 0)), RootFacts ↥W.auxS W.auxI 4 u)
    (hC : ∀ u : ↥(auxComp Γ (W.kernelAt 0) (W.x 0)), CenterFacts ↥W.auxS W.auxI u 1)
    (hP : ∀ u : ↥(auxComp Γ (W.kernelAt 0) (W.x 0)),
      IsPGroup 2 ↥(fixingSubgroup ↥W.auxS (W.auxI.neighborSet u)))
    {z : ↥(auxComp Γ (W.kernelAt 0) (W.x 0))}
    (hz : secondKernel ↥W.auxS W.auxI z ≠ ⊥) : False := by
  classical
  haveI : Finite ↥W.auxS := finite_auxS W
  obtain ⟨hne, h3, hval, hloc, -⟩ := hQ.aux_local
  obtain ⟨p, hp0, hp⟩ := exists_auxI_path hQ z
  let r : GPath W.auxI 2 := p.take 2 (by norm_num)
  have hr0 : r 0 = z := by simpa [r] using hp0
  have hr : r.NoBack := hp.take 2 (by norm_num)
  have h2 : secondKernel ↥W.auxS W.auxI (r 0) ≠ ⊥ := by rwa [hr0]
  exact (not_isPGroup_of_secondKernel_ne_bot (H := ↥W.auxS) (Γ := W.auxI)
    hM hW hne h3 hval hloc hL hR hC hr h2) (hP (r 2))

theorem ClosedGoodPath.QuarterHyp.false_of_sz [Finite V]
    [Finite H] {W : ClosedGoodPath H Γ} (hQ : W.QuarterHyp) {a : ℕ} (ha : 1 ≤ a)
    (hT0 : IsLocalSz H Γ (W.x 0) a) : False := by
  classical
  haveI : Finite ↥W.auxS := finite_auxS W
  have hM : MoufangCondition ↥W.auxS W.auxI 4 := hQ.moufangCondition_aux
  have hW : WeissFree ↥W.auxS W.auxI 4 := hQ.weissFree_aux
  obtain ⟨hne, -, hval, -, hK⟩ := hQ.aux_local
  have hSz : ∀ u : ↥(auxComp Γ (W.kernelAt 0) (W.x 0)),
      IsLocalSz ↥W.auxS W.auxI u a := fun u => hQ.isLocalSz_aux_of_one_le ha hT0 u
  have hL : ∀ u : ↥(auxComp Γ (W.kernelAt 0) (W.x 0)),
      LocalFacts ↥W.auxS W.auxI u := fun u =>
    (vertexFacts_of_isLocalSz (H := ↥W.auxS) (Γ := W.auxI) ha (hK u) (hSz u)).1
  have hC : ∀ u : ↥(auxComp Γ (W.kernelAt 0) (W.x 0)),
      CenterFacts ↥W.auxS W.auxI u 1 := fun u =>
    (vertexFacts_of_isLocalSz (H := ↥W.auxS) (Γ := W.auxI) ha (hK u) (hSz u)).2.2
  have hR : ∀ u : ↥(auxComp Γ (W.kernelAt 0) (W.x 0)),
      RootFacts ↥W.auxS W.auxI 4 u := fun u =>
    rootFacts_of_isLocalSz (H := ↥W.auxS) (Γ := W.auxI) (n := 4) (by norm_num)
      hM hW hne hval hK ha (hSz u)
  obtain ⟨p, hp⟩ := exists_auxI_sixPath hQ
  have hnc : ∃ x ∈ pathRootGroup ↥W.auxS W.auxI (p.drop 2 (by norm_num)),
      ∃ y ∈ pathRootGroup ↥W.auxS W.auxI (p.drop 2 (by norm_num)), x * y ≠ y * x :=
    exists_not_comm_pathRootGroup_of_isLocalSz (H := ↥W.auxS) (Γ := W.auxI) (n := 4)
      (by norm_num) hM hW hne hval hK ha (hp.drop 2 (by norm_num))
      (hSz ((p.drop 2 (by norm_num)) 4))
  have hz : secondKernel ↥W.auxS W.auxI (p 4) ≠ ⊥ :=
    secondKernel_ne_bot_of_not_comm (H := ↥W.auxS) (Γ := W.auxI) hM hW hp hnc
  exact false_of_secondKernel_ne_bot hQ hM hW hL hR hC
    hQ.isPGroup_fixingSubgroup_aux hz

theorem ClosedGoodPath.QuarterHyp.false_of_l2 [Finite V] [Finite H]
    {W : ClosedGoodPath H Γ} (hQ : W.QuarterHyp) {m : ℕ} (hm : 2 ≤ m)
    (hT0 : IsLocalL2 H Γ (W.x 0) m) : False := by
  classical
  haveI : Finite ↥W.auxS := finite_auxS W
  have hM : MoufangCondition ↥W.auxS W.auxI 4 := hQ.moufangCondition_aux
  have hW : WeissFree ↥W.auxS W.auxI 4 := hQ.weissFree_aux
  obtain ⟨hne, h3, hval, hloc, hK⟩ := hQ.aux_local
  have hL2 : ∀ u : ↥(auxComp Γ (W.kernelAt 0) (W.x 0)),
      IsLocalL2 ↥W.auxS W.auxI u m := fun u => hQ.isLocalL2_aux hT0 u
  have hL : ∀ u : ↥(auxComp Γ (W.kernelAt 0) (W.x 0)),
      LocalFacts ↥W.auxS W.auxI u := fun u =>
    (vertexFacts_of_isLocalL2 (H := ↥W.auxS) (Γ := W.auxI) hm (hK u) (hL2 u)).1
  have hC : ∀ u : ↥(auxComp Γ (W.kernelAt 0) (W.x 0)),
      CenterFacts ↥W.auxS W.auxI u 1 := fun u =>
    (vertexFacts_of_isLocalL2 (H := ↥W.auxS) (Γ := W.auxI) hm (hK u) (hL2 u)).2.2.1
  have hT : ∀ u : ↥(auxComp Γ (W.kernelAt 0) (W.x 0)),
      TransitiveFacts ↥W.auxS W.auxI u := fun u =>
    (vertexFacts_of_isLocalL2 (H := ↥W.auxS) (Γ := W.auxI) hm (hK u) (hL2 u)).2.2.2
  have hR : ∀ u : ↥(auxComp Γ (W.kernelAt 0) (W.x 0)),
      RootFacts ↥W.auxS W.auxI 4 u := fun u =>
    rootFacts_of_isLocalL2 (H := ↥W.auxS) (Γ := W.auxI) (n := 4) (by norm_num)
      hM hW hne hval hK hm (hL2 u)
  obtain ⟨p, -, -⟩ := exists_auxI_path hQ
    ⟨W.x 0, SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩
  have hedge : W.auxI.Adj (p 0) (p 1) := p.adj 0 (by norm_num)
  obtain ⟨z, hz⟩ := exists_secondKernel_ne_bot_of_transitive (H := ↥W.auxS) (Γ := W.auxI)
    hM hW hne h3 hval hloc hL hT hedge
  exact false_of_secondKernel_ne_bot hQ hM hW hL hR hC
    hQ.isPGroup_fixingSubgroup_aux hz

end CFSG.Quasithin.Stroth.WeissDelta

end
