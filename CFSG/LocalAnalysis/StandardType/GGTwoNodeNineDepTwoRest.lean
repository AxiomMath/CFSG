module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeNineDepTwoRestDefs
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeNineConsumer
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeNineConsumerK

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem nt9_A_of_Ax {G : Type} [Group G] [Finite G] {p n : ℕ} [Fact p.Prime]
    {Bs X : Subgroup G} {z : G} (h : GGResXDatumAx p Bs X z n) : GGResXDatumA p Bs X n := by
  obtain ⟨Λ, i1, i2, M, C, V, i3, i4, ι, φ, h, α, e, hM, hW, hC, hlin, hrefl, hpair, hf, hcl, -⟩ := h
  exact ⟨Λ, i1, i2, M, C, V, i3, i4, ι, φ, h, α, e, hM, hW, hC, hlin, hrefl, hpair, hf, hcl⟩

private lemma nt9_row_tag {p : ℕ} {J X : LargeEvenLabel} (h : ggRowTwoNode p J X) (h9 : 8 ≤ X.rank) :
    X.tag = .A ∨ X.tag = .twA := by
  rcases h with ⟨-, -, -, hX⟩ | ⟨-, -, -, hX⟩ | ⟨-, -, -, hX⟩ | ⟨-, -, -, hX⟩
  · subst hX
    exact Or.inl rfl
  · subst hX
    exact Or.inr rfl
  · subst hX
    have h0 : (⟨.E6, 0, J.n⟩ : LargeEvenLabel).rank = 0 := rfl
    rw [h0] at h9; omega
  · subst hX
    have h0 : (⟨.twE6, 0, J.n⟩ : LargeEvenLabel).rank = 0 := rfl
    rw [h0] at h9; omega

theorem ggResTwoNodeNineDepTwo_of_rest (hAll : LR6NineAll) (hOrb : GGResCentBoundInput)
    (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput) (hD : GGTwoNodeIndepDatum)
    (hRest : GGResTwoNodeNineDepTwoRestInput) : GGResTwoNodeNineDepTwoInput := by
  intro G _ _ p B Bs x L D J y K hH _ hF hS hE hP
  rcases hP with ⟨hrowL, hxL, hnc, hKs⟩ | ⟨hrowK, hyK, hnc, hLs⟩
  ·
    obtain ⟨labJ, labX, hJΛ, hXΛ, hJlab, hXlab, hRowNine⟩ := hrowL
    obtain ⟨hRowN, hp3, hrank⟩ := hRowNine
    have hx : x ∈ Bs := hH.1.tableB_facts.2.2.1
    rcases hD G p B Bs x L D J y K hH L x (Or.inl ⟨rfl, rfl⟩) labJ labX hJΛ hXΛ hJlab hXlab
      hRowN hxL with ⟨-, hA⟩ | ⟨hE', -⟩
    · have hXd : GGResXDatumA p Bs L 8 := by
        rcases hA with hAx | ⟨-, hXA⟩
        · simpa [hrank] using (nt9_A_of_Ax hAx)
        · simpa [hrank] using hXA
      exact ggTwoNodeNineDepL_two hAll hOrb hFix hFixK hp3 hH hx hXd hnc hKs
    · exfalso
      rcases hE' with h | h <;> rcases nt9_row_tag hRowN (by omega) with h' | h' <;>
        exact absurd (h.symm.trans h') (by decide)
  · exact hRest G p B Bs x L D J y K hH hF hS hE ⟨hrowK, hyK, hnc, hLs⟩

theorem ggResTwoNodeNineDepTwoRest_of_W1 (hAll : LR6NineAll) (hOrbK : GGResCentBoundNbrInput)
    (hFix : GGTBFixInput) (hD : GGTwoNodeIndepDatum) (hW1 : GGNineDepKFixLine) :
    GGResTwoNodeNineDepTwoRestInput := by
  intro G _ _ p B Bs x L D J y K hH _ hF hS hE hP
  obtain ⟨hrowK, hyK, hnc, hLs⟩ := hP
  have hrowK' := hrowK
  obtain ⟨labJ, labX, hJΛ, hXΛ, hJlab, hXlab, hRowNine⟩ := hrowK
  obtain ⟨hRowN, hp3, hrank⟩ := hRowNine
  have hyD : y ∈ D := by
    rw [hH.2.2.2.2.1.2.1]
    exact Subgroup.subset_closure (by simp)
  have hy : y ∈ Bs := hH.1.2.1.1 (hH.1.2.2.1.1 hyD)
  rcases hD G p B Bs x L D J y K hH K y (Or.inr ⟨rfl, rfl⟩) labJ labX hJΛ hXΛ hJlab hXlab hRowN
    hyK with ⟨-, hA⟩ | ⟨hE', -⟩
  · have hXd : GGResXDatumA p Bs K 8 := by
      rcases hA with hAx | ⟨-, hXA⟩
      · simpa [hrank] using (nt9_A_of_Ax hAx)
      · simpa [hrank] using hXA
    have hstrong : ∀ b : ↥Bs, (∀ ψ ∈ ggAutomizer K Bs, ψ b = b) → (b : G) ∈ Subgroup.zpowers y :=
      fun b hb => hW1 G p B Bs x L D J y K hH hF hS hE hrowK' hnc hLs hXd b hb
    exact ggTwoNodeNineDepK_two_of_orbK hAll hOrbK hFix hp3 hH hy hstrong hXd hnc hLs
  · exfalso
    rcases hE' with h | h <;> rcases nt9_row_tag hRowN (by omega) with h' | h' <;>
      exact absurd (h.symm.trans h') (by decide)

theorem ggResTwoNodeNineDepTwo_of_W1 (hAll : LR6NineAll) (hOrb : GGResCentBoundInput)
    (hOrbK : GGResCentBoundNbrInput) (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput)
    (hD : GGTwoNodeIndepDatum) (hW1 : GGNineDepKFixLine) : GGResTwoNodeNineDepTwoInput :=
  ggResTwoNodeNineDepTwo_of_rest hAll hOrb hFix hFixK hD
    (ggResTwoNodeNineDepTwoRest_of_W1 hAll hOrbK hFix hD hW1)

end CFSG.StandardType

end
