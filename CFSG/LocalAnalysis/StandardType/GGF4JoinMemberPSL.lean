module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveFieldTwoPSL
public import CFSG.LocalAnalysis.StandardType.GGSecFiveCompatJoinF4

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.StandardType.ClassicalPosition

section TypeDet

theorem guarded_lieModel_PSL {X : Type} [Group X] {lab : LargeEvenLabel}
    (hg : GuardedLargeEvenLabel lab) (hM : MarkedModel lab X) {r f : ℕ}
    (h : LieModel X .PSL r 2 f) : f = 1 ∧ lab.tag = .A ∧ r = lab.rank + 1 := by
  obtain ⟨tg, rk, nn⟩ := lab
  have hdet : markChar ⟨tg, rk, nn⟩ = 2 → StatedLieTag.PSL = markTag ⟨tg, rk, nn⟩ ∧
      r = markRank ⟨tg, rk, nn⟩ ∧ f = markDeg ⟨tg, rk, nn⟩ :=
    fun h2 => cls_typeDet h2 hM (Or.inl rfl) h
  unfold GuardedLargeEvenLabel at hg
  dsimp only at hg ⊢
  rcases hg with ⟨rfl | rfl, -⟩ | ⟨rfl | rfl, hrk⟩ | (rfl | rfl | rfl | rfl | rfl) | ⟨rfl, -, rfl⟩
  · have := (hdet rfl).1
    simp [markTag] at this
  · have := (hdet rfl).1
    simp [markTag] at this
  · have := (hdet rfl).1
    simp [markTag, show rk ≠ 3 by omega] at this
  · have := (hdet rfl).1
    simp [markTag, show rk ≠ 2 by omega, show rk ≠ 3 by omega] at this
  · have := (hdet rfl).1
    simp [markTag] at this
  · have := (hdet rfl).1
    simp [markTag] at this
  · have := (hdet rfl).1
    simp [markTag] at this
  · have := (hdet rfl).1
    simp [markTag] at this
  · have := (hdet rfl).1
    simp [markTag] at this
  · obtain ⟨-, hr, hf⟩ := hdet rfl
    exact ⟨hf, rfl, hr⟩

end TypeDet

section Cert

theorem exists_selected_PSL_of_component
    {G : Type} [Group G] [Finite G] {p : ℕ} {X : Subgroup G} {x : G}
    {n f : ℕ} (ψ : (ggU .PSL n f).K →* G)
    (hadm : StatedLieAdmissible .PSL n 2 f)
    (hψker : ψ.ker ≤ Subgroup.center (ggU .PSL n f).K)
    (hx : x ∈ ψ.range) (hp : Odd p) (hxp : x ^ p = 1)
    (hX : IsComponentOf X (ψ.range ⊓ Subgroup.centralizer {x}))
    (hmark : LargeEvenMarking ↥X (fun lab _ _ _ _ _ => GuardedLargeEvenLabel lab)) :
    ∃ S : Subgroup G, MemberSelectedSL2At X S ∧ PresentedSelectedSL2At ψ S := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hadm.2.2.1; omega⟩
  have hf : 1 ≤ f := hadm.2.1
  let ψ₀ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f) →* G := ψ
  have hψ : ψ₀.ker ≤ Subgroup.center _ := hψker
  have hxR : x ∈ ψ₀.range := by
    change x ∈ ψ.range
    exact hx
  have hdiag : GGPsiInnerDiag (SpecialLinear.rootDatum m (GaloisField 2 f)) ψ₀ x :=
    ggPsiInnerDiag_of_mem_range _ hxR
  have hxN : x ∈ Subgroup.normalizer (ψ₀.range : Set G) := Subgroup.le_normalizer hxR
  obtain ⟨s, X', hL'X, hL', hodd⟩ :=
    FieldTwoPSL.exists_lift_component m f hf ψ₀ hψ hxN hdiag hp hxp hX
  obtain ⟨-, lab, -, hraw⟩ := largeEvenMarking_markedModel hmark
  obtain ⟨R, _, I, F, -, -, θ, hg, hMR⟩ := largeEvenRawDatum_exists hraw
  have hM : MarkedModel lab (↥X ⧸ Subgroup.center ↥X) := MarkedModel.of_mulEquiv θ.symm hMR
  obtain ⟨hf1, k, r', eidx, P, Pinv, hPP, hPinvP, hk2, hιr⟩ :=
    FieldTwoPSL.block_of_component m f hf ψ₀ hψ (fun h => (guarded_lieModel_PSL hg hM h).1)
      s X' hL'X hL' hodd
  subst hf1
  have hm2 : 2 ≤ m := by
    have h := Fintype.card_congr eidx
    simp only [Fintype.card_sum, Fintype.card_fin] at h
    omega
  set ιb := bmPSL_embedHom eidx P Pinv hPP hPinvP with hιdef
  have hrangeL : (ψ₀.comp ιb).range = X := by rw [MonoidHom.range_comp, hιr, hL'X]
  have hψkerL : (ψ₀.comp ιb).ker ≤ Subgroup.center (ggU .PSL (k + 1) 1).K := by
    intro y hy
    exact Subgroup.comap_center_le_center (f := ιb) bmPSL_embedHom_injective (hψ hy)
  obtain ⟨γ, model₀, hm₀⟩ :=
    FieldTwoPSL.exists_selectedModel_PSL_chart (F := GaloisField 2 1) (m := m) (by omega)
  obtain ⟨δ, model₁, hm₁⟩ :=
    FieldTwoPSL.exists_selectedModel_PSL_chart (F := GaloisField 2 1) (m := k) (by omega)
  obtain ⟨u₀, hu₀⟩ :=
    FieldTwoPSL.exists_conj_embM_eq_embedMat hm2 (by omega : 2 ≤ k + 1) eidx P Pinv hPP hPinvP
  have hpt : ∀ A : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1),
      (MulAut.conj u₀) (model₀.phi A) = ιb (model₁.phi A) := by
    intro A
    rw [MulAut.conj_apply]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hm₀]
    change _ = bmPSL_embedMat eidx P Pinv
      ((model₁.phi A : Matrix.SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 1)) :
        Matrix (Fin (k + 1)) (Fin (k + 1)) (GaloisField 2 1))
    rw [hm₁]
    exact hu₀ _
  refine ⟨((ψ₀.comp ιb).comp model₁.phi).range,
    ⟨.PSL, k + 1, 1, ψ₀.comp ιb, ?_, ?_, hψkerL, hrangeL, GaloisField 2 1, inferInstance,
      inferInstance, inferInstance, δ, model₁, rfl⟩,
    GaloisField 2 1, inferInstance, inferInstance, inferInstance, γ, model₀, u₀, ?_⟩
  · exact ⟨Nat.prime_two, le_rfl, by omega, fun h => by have := (Prod.mk.inj h).1; omega,
      fun h => by have := (Prod.mk.inj h).1; omega⟩
  · show 2 ≤ k
    exact hk2
  · congr 1
    ext A
    exact congrArg ψ₀ (hpt A)

theorem ggActualMember_PSL_selected
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs L D J X : Subgroup G} {x : G}
    (hcfg : GGConfig p B Bs x L D J) {n f : ℕ}
    (ψ : (ggU .PSL n f).K →* G)
    (hpres : GGPresentsG0 (ggG0 p B x L D J) (ggU .PSL n f).D .PSL n f ψ)
    (horigin : (X = L ∧ x ∈ ggG0 p B x L D J) ∨
      ∃ y : G, GGNbr p B x D J y X ∧ y ∈ ggG0 p B x L D J)
    (hmark : LargeEvenMarking ↥X (fun lab _ _ _ _ _ => GuardedLargeEvenLabel lab)) :
    ∃ S : Subgroup G, MemberSelectedSL2At X S ∧ PresentedSelectedSL2At ψ S := by
  have hq : CFSG.Assembly.IsQuasisimple ↥X := isQuasisimple_of_largeEvenMarking hmark
  obtain ⟨z, -, hz, hzp, hX⟩ := ggActualMember_internal_component hcfg horigin hq
  obtain ⟨hp, hp2, -⟩ := (hcfg.1.2.2.2.2.2.1 : p ∈ CFSG.Assembly.LargeEvenBeta 4 G)
  have hzR : z ∈ ψ.range := by
    rw [hpres.2.1.1]
    exact hz
  have hXR : IsComponentOf X (ψ.range ⊓ Subgroup.centralizer {z}) := by
    rw [hpres.2.1.1]
    exact hX
  exact exists_selected_PSL_of_component ψ hpres.1.1 hpres.2.1.2 hzR
    (hp.odd_of_ne_two hp2) hzp hXR hmark

end Cert

end CFSG.StandardType

end
