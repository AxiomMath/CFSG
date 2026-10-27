module

public import CFSG.LocalAnalysis.StandardType.GGNTPlaneInput
public import CFSG.RankThree.Chevalley.SteinbergBID4Restrict
public import CFSG.RankThree.PartOne.KE.D4TranspositionInterface
public import CFSG.HardMathSupport.Lang.D4Three.NormalForm
public import CFSG.LocalAnalysis.StandardType.GGCentD4HomExt
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagTwisted
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiag

public section

namespace CFSG.StandardType.NTPlane

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Lang.D4Three
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Chevalley


theorem ntpD4_theta_torus
    
    
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] (v : WeylGroup Tag.E6)
    (Y : Subgroup (ModGL Tag.E6 L))
    (hY : Y = rootSpan Tag.E6 L ((fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6)))
    (Θ : ↥Y ≃* ↥(adjointGroup Tag.D4 L))
    (hΘ : ∀ (y : ↥Y) (k : Fin Tag.D4.rank) (c : L),
      ((y : ModGL Tag.E6 L) = canonicalRep (coxeterSystem Tag.E6) L v *
          xUnit Tag.E6 L (d4Idx k) c * (canonicalRep (coxeterSystem Tag.E6) L v)⁻¹ →
        (Θ y : ModGL Tag.D4 L) = xUnit Tag.D4 L k c) ∧
      ((y : ModGL Tag.E6 L) = canonicalRep (coxeterSystem Tag.E6) L v *
          yUnit Tag.E6 L (d4Idx k) c * (canonicalRep (coxeterSystem Tag.E6) L v)⁻¹ →
        (Θ y : ModGL Tag.D4 L) = yUnit Tag.D4 L k c))
    (τ : ModGL Tag.E6 L) (hτ : τ ∈ torusGroup Tag.E6 L)
    (y : ModGL Tag.E6 L) (hy : y ∈ Y) (hy' : τ * y * τ⁻¹ ∈ Y) :
    ∃ τ' : ↥(adjointGroup Tag.D4 L), Θ ⟨τ * y * τ⁻¹, hy'⟩ = τ' * Θ ⟨y, hy⟩ * τ'⁻¹ := by
  have h2L : (2 : L) = 0 := CharP.cast_eq_zero L 2
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hτ
  set nv : ModGL Tag.E6 L := canonicalRep (coxeterSystem Tag.E6) L v with hnv
  let a : Fin Tag.D4.rank → Lˣ :=
    fun k => rootChar l (v • (Pi.single (d4Idx k) 1 : Fin Tag.E6.rank → ℤ))
  let τ' : ↥(adjointGroup Tag.D4 L) :=
    ⟨rootDiagUnit Tag.D4 a,
      CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_mem_adjointGroup_of_isAlgClosed a⟩
  have hstab : Y.map (MulAut.conj (rootDiagUnit Tag.E6 l)).toMonoidHom = Y := by
    rw [hY]
    refine map_rootSpan_of_forall (fun α hα => ?_)
    obtain ⟨β, hβ, rfl⟩ := hα
    exact map_conj_rootDiagUnit_rootSubgroup l (IsRoot.smul hβ.1 v)
  have hstab' : Y.map (↑(MulAut.conj (rootDiagUnit Tag.E6 l))) = Y := hstab
  let cf : MulAut ↥Y :=
    ((MulAut.conj (rootDiagUnit Tag.E6 l)).subgroupMap Y).trans (MulEquiv.subgroupCongr hstab')
  have hcf : ∀ x : ↥Y,
      ((cf x : ↥Y) : ModGL Tag.E6 L) =
        rootDiagUnit Tag.E6 l * (x : ModGL Tag.E6 L) * (rootDiagUnit Tag.E6 l)⁻¹ := by
    intro x
    simp only [cf, MulEquiv.trans_apply]
    rw [MulEquiv.subgroupCongr_apply, MulEquiv.coe_subgroupMap_apply, MulAut.conj_apply]
  let φ : ↥Y →* ↥(adjointGroup Tag.D4 L) := Θ.toMonoidHom.comp cf.toMonoidHom
  let ψ : ↥Y →* ↥(adjointGroup Tag.D4 L) := (MulAut.conj τ').toMonoidHom.comp Θ.toMonoidHom
  have hx : ∀ (y : ↥Y) (k : Fin Tag.D4.rank) (c : L),
      (y : ModGL Tag.E6 L) = nv * xUnit Tag.E6 L (d4Idx k) c * nv⁻¹ → φ y = ψ y := by
    intro y k c hyk
    let A : Fin Tag.E6.rank → ℤ := v • (Pi.single (d4Idx k) 1)
    have hA : IsRoot Tag.E6 A := IsRoot.smul (isRoot_single Tag.E6 (d4Idx k)) v
    have h1 : nv * xUnit Tag.E6 L (d4Idx k) c * nv⁻¹ = pinnedX Tag.E6 L A c := by
      rw [← pinnedX_single]
      exact canonicalRep_mul_pinnedX_mul_inv_of_two h2L v (isRoot_single Tag.E6 (d4Idx k)) c
    have h3 : nv * xUnit Tag.E6 L (d4Idx k) ((rootChar l A : L) * c) * nv⁻¹ =
        pinnedX Tag.E6 L A ((rootChar l A : L) * c) := by
      rw [← pinnedX_single]
      exact canonicalRep_mul_pinnedX_mul_inv_of_two h2L v (isRoot_single Tag.E6 (d4Idx k)) _
    have hconj : (cf y : ModGL Tag.E6 L) =
        nv * xUnit Tag.E6 L (d4Idx k) ((rootChar l A : L) * c) * nv⁻¹ := by
      rw [hcf y, hyk, h1, rootDiagUnit_conj_pinnedX l hA c, ← h3]
    have hφ : φ y = adjX Tag.D4 L k ((rootChar l A : L) * c) := by
      show Θ (cf y) = adjX Tag.D4 L k ((rootChar l A : L) * c)
      exact Subtype.ext ((hΘ (cf y) k ((rootChar l A : L) * c)).1 hconj)
    have hΘy : (Θ y : ModGL Tag.D4 L) = xUnit Tag.D4 L k c := (hΘ y k c).1 hyk
    have hψ : ψ y = adjX Tag.D4 L k ((rootChar l A : L) * c) := by
      show MulAut.conj τ' (Θ y) = adjX Tag.D4 L k ((rootChar l A : L) * c)
      rw [show Θ y = adjX Tag.D4 L k c from Subtype.ext hΘy]
      refine Subtype.ext ?_
      change rootDiagUnit Tag.D4 a * xUnit Tag.D4 L k c * (rootDiagUnit Tag.D4 a)⁻¹ =
        xUnit Tag.D4 L k ((rootChar l A : L) * c)
      simpa [a, A] using (root_diagonal_conjugation Tag.D4 L a).1 k c
    rw [hφ, hψ]
  have hyy : ∀ (y : ↥Y) (k : Fin Tag.D4.rank) (c : L),
      (y : ModGL Tag.E6 L) = nv * yUnit Tag.E6 L (d4Idx k) c * nv⁻¹ → φ y = ψ y := by
    intro y k c hyk
    let A : Fin Tag.E6.rank → ℤ := v • (-(Pi.single (d4Idx k) 1))
    have hA : IsRoot Tag.E6 A :=
      IsRoot.smul (IsRoot.neg (isRoot_single Tag.E6 (d4Idx k))) v
    have hneg : rootChar l A = (a k)⁻¹ := by
      have hA0 : A = -(v • (Pi.single (d4Idx k) 1 : Fin Tag.E6.rank → ℤ)) := by
        simp [A, smul_neg]
      rw [hA0, show (-(v • (Pi.single (d4Idx k) 1 : Fin Tag.E6.rank → ℤ))) =
          0 - (v • (Pi.single (d4Idx k) 1 : Fin Tag.E6.rank → ℤ)) from (zero_sub _).symm,
        rootChar_sub, rootChar_zero, one_mul]
    have h1 : nv * yUnit Tag.E6 L (d4Idx k) c * nv⁻¹ = pinnedX Tag.E6 L A c := by
      rw [← pinnedX_neg_single]
      exact canonicalRep_mul_pinnedX_mul_inv_of_two h2L v
        (IsRoot.neg (isRoot_single Tag.E6 (d4Idx k))) c
    have h3 : nv * yUnit Tag.E6 L (d4Idx k) ((((a k)⁻¹ : Lˣ) : L) * c) * nv⁻¹ =
        pinnedX Tag.E6 L A ((((a k)⁻¹ : Lˣ) : L) * c) := by
      rw [← pinnedX_neg_single]
      exact canonicalRep_mul_pinnedX_mul_inv_of_two h2L v
        (IsRoot.neg (isRoot_single Tag.E6 (d4Idx k))) _
    have hnegL : (rootChar l A : L) = (((a k)⁻¹ : Lˣ) : L) := by rw [hneg]
    have hconj : (cf y : ModGL Tag.E6 L) =
        nv * yUnit Tag.E6 L (d4Idx k) ((((a k)⁻¹ : Lˣ) : L) * c) * nv⁻¹ := by
      rw [hcf y, hyk, h1, rootDiagUnit_conj_pinnedX l hA c, hnegL, ← h3]
    have hφ : φ y = adjY Tag.D4 L k ((((a k)⁻¹ : Lˣ) : L) * c) := by
      show Θ (cf y) = adjY Tag.D4 L k ((((a k)⁻¹ : Lˣ) : L) * c)
      exact Subtype.ext ((hΘ (cf y) k ((((a k)⁻¹ : Lˣ) : L) * c)).2 hconj)
    have hΘy : (Θ y : ModGL Tag.D4 L) = yUnit Tag.D4 L k c := (hΘ y k c).2 hyk
    have hψ : ψ y = adjY Tag.D4 L k ((((a k)⁻¹ : Lˣ) : L) * c) := by
      show MulAut.conj τ' (Θ y) = adjY Tag.D4 L k ((((a k)⁻¹ : Lˣ) : L) * c)
      rw [show Θ y = adjY Tag.D4 L k c from Subtype.ext hΘy]
      refine Subtype.ext ?_
      change rootDiagUnit Tag.D4 a * yUnit Tag.D4 L k c * (rootDiagUnit Tag.D4 a)⁻¹ =
        yUnit Tag.D4 L k ((((a k)⁻¹ : Lˣ) : L) * c)
      simpa [a, A] using (root_diagonal_conjugation Tag.D4 L a).2.1 k c
    rw [hφ, hψ]
  have hφψ : φ = ψ := ntpD4_hom_ext v Y hY Θ hΘ hx hyy
  have hmem : cf ⟨y, hy⟩ =
      ⟨rootDiagUnit Tag.E6 l * y * (rootDiagUnit Tag.E6 l)⁻¹, hy'⟩ :=
    Subtype.ext (hcf ⟨y, hy⟩)
  have hfinal := DFunLike.congr_fun hφψ ⟨y, hy⟩
  change Θ (cf ⟨y, hy⟩) = MulAut.conj τ' (Θ ⟨y, hy⟩) at hfinal
  rw [hmem, MulAut.conj_apply] at hfinal
  exact ⟨τ', hfinal⟩

end CFSG.StandardType.NTPlane

end
