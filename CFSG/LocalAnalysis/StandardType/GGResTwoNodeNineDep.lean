module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeIndepDefs
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallRankDefs
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeNineDepL
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeNineDepK
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepLarge
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepMove

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l6n3_rowAt_mono {G : Type} [Group G] {p : ℕ} {J X : Subgroup G}
    {R R' : ℕ → LargeEvenLabel → LargeEvenLabel → Prop}
    (hRR : ∀ labJ labX, R p labJ labX → R' p labJ labX) (h : GGResRowAt R p J X) :
    GGResRowAt R' p J X := by
  obtain ⟨labJ, labX, hJΛ, hXΛ, hJl, hXl, hr⟩ := h
  exact ⟨labJ, labX, hJΛ, hXΛ, hJl, hXl, hRR _ _ hr⟩

private theorem l6n3_xdatum_of_A {G : Type} [Group G] [Finite G] {p n : ℕ} [Fact p.Prime]
    {Bs X : Subgroup G} (h : GGResXDatumA p Bs X n) : GGResXDatum p Bs X := by
  obtain ⟨Λ, i1, i2, M, C, V, i3, i4, ι, φ, h, α, e, hM, hW, hC, hlin, hrefl, hpair, hf, hcl⟩ := h
  exact ⟨Λ, i1, i2, M, C, V, i3, i4, ι, φ, h, α, hW, hC, hlin, hrefl, hpair, hf, hcl⟩

private theorem l6n3_A_of_Ax {G : Type} [Group G] [Finite G] {p n : ℕ} [Fact p.Prime]
    {Bs X : Subgroup G} {z : G} (h : GGResXDatumAx p Bs X z n) : GGResXDatumA p Bs X n := by
  obtain ⟨Λ, i1, i2, M, C, V, i3, i4, ι, φ, h, α, e, hM, hW, hC, hlin, hrefl, hpair, hf, hcl, -⟩ := h
  exact ⟨Λ, i1, i2, M, C, V, i3, i4, ι, φ, h, α, e, hM, hW, hC, hlin, hrefl, hpair, hf, hcl⟩

private lemma l6n3_row_facts {p : ℕ} {J X : LargeEvenLabel} (h : ggRowTwoNode p J X)
    (h9 : 8 ≤ X.rank) : (X.tag = .A ∨ X.tag = .twA) ∧ p ∣ X.rank + 1 := by
  rcases h with ⟨-, hp1, hp2, hX⟩ | ⟨-, hp1, hp2, hX⟩ | ⟨-, -, -, hX⟩ | ⟨-, -, -, hX⟩
  · subst hX
    refine ⟨Or.inl rfl, ?_⟩
    have he : (J.rank + 2) + 1 = J.rank + 3 := by omega
    rw [he]; exact hp2
  · subst hX
    refine ⟨Or.inr rfl, ?_⟩
    have he : (J.rank + 2) + 1 = J.rank + 3 := by omega
    rw [he]; exact hp2
  · subst hX
    have h0 : (⟨.E6, 0, J.n⟩ : LargeEvenLabel).rank = 0 := rfl
    rw [h0] at h9; omega
  · subst hX
    have h0 : (⟨.twE6, 0, J.n⟩ : LargeEvenLabel).rank = 0 := rfl
    rw [h0] at h9; omega

theorem ggResTwoNodeNineDepInput_of_inputs (hNine : LR6NineDepPos)
    (hTwo : GGResTwoNodeNineDepTwoInput) (hLE3 : GGResTwoNodeIndepLE3RestInput)
    (hOrb : GGResCentBoundInput) (hOrbK : GGResCentBoundNbrInput) (hFix : GGTBFixInput)
    (hFixK : GGTBFixNbrInput) (hD : GGTwoNodeIndepDatum) (hJ : GGTBJInputR)
    (hJ2 : GGTBJTwoNodeInput)
    (hX : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
      (L D J : Subgroup G) (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K →
      ∀ [Fact p.Prime], (GGResXDatum p Bs L ∨ GGResRowAt ggRowSeven p J L) ∧
        (GGResXDatum p Bs K ∨ GGResRowAt ggRowSeven p J K))
    (h6c : GGResMaxRankInput) (h6d : GGResTrialityInput) (h6e : GGResTriD4TwE6Input)
    (h6f : GGResSevenInput) (h6g : GGResTwA2Input) : GGResTwoNodeNineDepInput := by
  intro G _ _ p B Bs x L D J y K hH _ hF hS hE hP
  rcases hP with ⟨hrowL, hxL, hnc⟩ | ⟨hrowK, hyK, hnc⟩
  ·
    have hrowL' := hrowL
    obtain ⟨labJ, labX, hJΛ, hXΛ, hJlab, hXlab, hRowNine⟩ := hrowL'
    obtain ⟨hRowN, hp3, hrank⟩ := hRowNine
    have hx : x ∈ Bs := hH.1.tableB_facts.2.2.1
    have hrow2 : GGResRowAt ggRowTwoNode p J L := l6n3_rowAt_mono (fun _ _ h => h.1) hrowL
    rcases hD G p B Bs x L D J y K hH L x (Or.inl ⟨rfl, rfl⟩) labJ labX hJΛ hXΛ hJlab hXlab
      hRowN hxL with ⟨-, hA⟩ | ⟨hE', -⟩
    · have hXd : GGResXDatumA p Bs L 8 := by
        rcases hA with hAx | ⟨-, hXA⟩
        · simpa [hrank] using (l6n3_A_of_Ax hAx)
        · simpa [hrank] using hXA
      have hXs : GGResTwoNodeSideDatum p Bs L J :=
        (hJ2 G p B Bs x L D J y K hH).1 (l6n3_xdatum_of_A hXd) hrow2
      rcases ggTwoNode_shape_K_R hJ hJ2 hX h6c h6d h6e h6f h6g hH hF hS hE with
        hK1 | hK3 | hK2 | hW
      · exact ggTwoNodeNineDepL_closer hNine hOrb hFix hFixK hp3 hH hx hXd hnc hXs hK1
      · exact hLE3 G p B Bs x L D J y K hH hF hS hE
          (Or.inr (Or.inr (Or.inl ⟨hrowL, hxL, hnc, hK3⟩)))
      · exact hTwo G p B Bs x L D J y K hH hF hS hE (Or.inl ⟨hrowL, hxL, hnc, hK2⟩)
      · exact hW
    · exfalso
      obtain ⟨htag, -⟩ := l6n3_row_facts hRowN (by omega)
      rcases hE' with h | h <;> rcases htag with h' | h' <;>
        exact absurd (h.symm.trans h') (by decide)
  ·
    have hrowK' := hrowK
    obtain ⟨labJ, labX, hJΛ, hXΛ, hJlab, hXlab, hRowNine⟩ := hrowK'
    obtain ⟨hRowN, hp3, hrank⟩ := hRowNine
    have hyD : y ∈ D := by
      rw [hH.2.2.2.2.1.2.1]
      exact Subgroup.subset_closure (by simp)
    have hy : y ∈ Bs := hH.1.2.1.1 (hH.1.2.2.1.1 hyD)
    have hrow2 : GGResRowAt ggRowTwoNode p J K := l6n3_rowAt_mono (fun _ _ h => h.1) hrowK
    rcases hD G p B Bs x L D J y K hH K y (Or.inr ⟨rfl, rfl⟩) labJ labX hJΛ hXΛ hJlab hXlab
      hRowN hyK with ⟨-, hA⟩ | ⟨hE', -⟩
    · have hXd : GGResXDatumA p Bs K 8 := by
        rcases hA with hAx | ⟨-, hXA⟩
        · simpa [hrank] using (l6n3_A_of_Ax hAx)
        · simpa [hrank] using hXA
      have hXs : GGResTwoNodeSideDatum p Bs K J :=
        (hJ2 G p B Bs x L D J y K hH).2 (l6n3_xdatum_of_A hXd) hrow2
      rcases ggTwoNode_shape_L_R hJ hJ2 hX h6c h6d h6e h6f h6g hH hF hS hE with
        hL1 | hL3 | hL2 | hW
      · rw [sup_comm]
        exact ggTwoNodeNineDepK_closer hNine hOrbK hFix hp3 hH hy hXd hnc hXs hL1
      · exact hLE3 G p B Bs x L D J y K hH hF hS hE
          (Or.inr (Or.inr (Or.inr ⟨hrowK, hyK, hnc, hL3⟩)))
      · exact hTwo G p B Bs x L D J y K hH hF hS hE (Or.inr ⟨hrowK, hyK, hnc, hL2⟩)
      · exact hW
    · exfalso
      obtain ⟨htag, -⟩ := l6n3_row_facts hRowN (by omega)
      rcases hE' with h | h <;> rcases htag with h' | h' <;>
        exact absurd (h.symm.trans h') (by decide)

end CFSG.StandardType

end
