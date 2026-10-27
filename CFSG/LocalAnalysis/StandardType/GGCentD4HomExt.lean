module

public import CFSG.LocalAnalysis.StandardType.GGNTPlaneInput
public import CFSG.RankThree.Chevalley.SteinbergBID4Restrict
public import CFSG.RankThree.PartOne.KE.D4TranspositionInterface
public import CFSG.LieType.Chevalley.GraphFixedCoordinateDetection

public section

namespace CFSG.StandardType.NTPlane

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE

theorem ntpD4_conj_mem
    {L : Type} [Field L] (v : WeylGroup Tag.E6) (k : Fin Tag.D4.rank) (c : L) :
    canonicalRep (coxeterSystem Tag.E6) L v * xUnit Tag.E6 L (d4Idx k) c *
        (canonicalRep (coxeterSystem Tag.E6) L v)⁻¹ ∈
      rootSpan Tag.E6 L ((fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ∧
      canonicalRep (coxeterSystem Tag.E6) L v * yUnit Tag.E6 L (d4Idx k) c *
        (canonicalRep (coxeterSystem Tag.E6) L v)⁻¹ ∈
      rootSpan Tag.E6 L ((fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6)) := by
  obtain ⟨εx, -, hεx⟩ :=
    exists_canonicalRep_mul_pinnedX_mul_inv L v (isRoot_single Tag.E6 (d4Idx k))
  obtain ⟨εy, -, hεy⟩ :=
    exists_canonicalRep_mul_pinnedX_mul_inv L v (isRoot_neg_single Tag.E6 (d4Idx k))
  have hk : k.val < 4 := k.2
  have hmem : d4Idx k ∈ d4Nodes Tag.E6 := by
    change 1 ≤ (d4Idx k).val ∧ (d4Idx k).val ≤ 4
    simp only [d4Idx]
    omega
  have hne : ∀ i : Fin Tag.E6.rank, i ∉ d4Nodes Tag.E6 → i ≠ d4Idx k := by
    intro i hi h
    exact hi (by rw [h]; exact hmem)
  have hx : (Pi.single (d4Idx k) 1 : Fin Tag.E6.rank → ℤ) ∈
      parabolicRoots Tag.E6 (d4Nodes Tag.E6) :=
    ⟨isRoot_single Tag.E6 (d4Idx k), fun i hi => by
      simp [Pi.single_eq_of_ne (hne i hi)]⟩
  have hy : (-Pi.single (d4Idx k) 1 : Fin Tag.E6.rank → ℤ) ∈
      parabolicRoots Tag.E6 (d4Nodes Tag.E6) :=
    ⟨isRoot_neg_single Tag.E6 (d4Idx k), fun i hi => by
      simp [Pi.single_eq_of_ne (hne i hi)]⟩
  constructor
  · rw [← pinnedX_single Tag.E6 L (d4Idx k) c, hεx c]
    exact pinnedX_mem_rootSpan
      (S := (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6))
      ⟨Pi.single (d4Idx k) 1, hx, rfl⟩ (εx * c)
  · rw [← pinnedX_neg_single Tag.E6 L (d4Idx k) c, hεy c]
    exact pinnedX_mem_rootSpan
      (S := (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6))
      ⟨-Pi.single (d4Idx k) 1, hy, rfl⟩ (εy * c)

theorem ntpD4_hom_ext
    {L : Type} [Field L] (v : WeylGroup Tag.E6) (Y : Subgroup (ModGL Tag.E6 L))
    (hY : Y = rootSpan Tag.E6 L ((fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6)))
    (Θ : ↥Y ≃* ↥(adjointGroup Tag.D4 L))
    (hΘ : ∀ (y : ↥Y) (k : Fin Tag.D4.rank) (c : L),
      ((y : ModGL Tag.E6 L) = canonicalRep (coxeterSystem Tag.E6) L v *
          xUnit Tag.E6 L (d4Idx k) c * (canonicalRep (coxeterSystem Tag.E6) L v)⁻¹ →
        (Θ y : ModGL Tag.D4 L) = xUnit Tag.D4 L k c) ∧
      ((y : ModGL Tag.E6 L) = canonicalRep (coxeterSystem Tag.E6) L v *
          yUnit Tag.E6 L (d4Idx k) c * (canonicalRep (coxeterSystem Tag.E6) L v)⁻¹ →
        (Θ y : ModGL Tag.D4 L) = yUnit Tag.D4 L k c))
    {G : Type*} [Group G] {φ ψ : ↥Y →* G}
    (hx : ∀ (y : ↥Y) (k : Fin Tag.D4.rank) (c : L), (y : ModGL Tag.E6 L) =
      canonicalRep (coxeterSystem Tag.E6) L v * xUnit Tag.E6 L (d4Idx k) c *
        (canonicalRep (coxeterSystem Tag.E6) L v)⁻¹ → φ y = ψ y)
    (hy : ∀ (y : ↥Y) (k : Fin Tag.D4.rank) (c : L), (y : ModGL Tag.E6 L) =
      canonicalRep (coxeterSystem Tag.E6) L v * yUnit Tag.E6 L (d4Idx k) c *
        (canonicalRep (coxeterSystem Tag.E6) L v)⁻¹ → φ y = ψ y) :
    φ = ψ := by
  let x : Fin Tag.D4.rank → L → ↥Y := fun k c =>
    ⟨canonicalRep (coxeterSystem Tag.E6) L v * xUnit Tag.E6 L (d4Idx k) c *
        (canonicalRep (coxeterSystem Tag.E6) L v)⁻¹,
      by rw [hY]; exact (ntpD4_conj_mem (L := L) v k c).1⟩
  let y : Fin Tag.D4.rank → L → ↥Y := fun k c =>
    ⟨canonicalRep (coxeterSystem Tag.E6) L v * yUnit Tag.E6 L (d4Idx k) c *
        (canonicalRep (coxeterSystem Tag.E6) L v)⁻¹,
      by rw [hY]; exact (ntpD4_conj_mem (L := L) v k c).2⟩
  have hxΘ : ∀ k c, Θ.symm (adjX Tag.D4 L k c) = x k c := by
    intro k c
    rw [← show Θ (x k c) = adjX Tag.D4 L k c from
      Subtype.ext ((hΘ (x k c) k c).1 rfl), Θ.symm_apply_apply]
  have hyΘ : ∀ k c, Θ.symm (adjY Tag.D4 L k c) = y k c := by
    intro k c
    rw [← show Θ (y k c) = adjY Tag.D4 L k c from
      Subtype.ext ((hΘ (y k c) k c).2 rfl), Θ.symm_apply_apply]
  have hcomp : φ.comp Θ.symm.toMonoidHom = ψ.comp Θ.symm.toMonoidHom := by
    refine MonoidHom.eq_of_eqOn_dense (Subgroup.closure_closure_coe_preimage
      (k := {g : ModGL Tag.D4 L | ∃ (i : Fin Tag.D4.rank) (c : L),
        (g : Module.End L (RootModule Tag.D4 L)) = xOp Tag.D4 L i c ∨
          (g : Module.End L (RootModule Tag.D4 L)) = yOp Tag.D4 L i c})) ?_
    rintro g ⟨i, c, hc | hc⟩
    · have e : g = adjX Tag.D4 L i c :=
        Subtype.ext (Units.ext (hc.trans (coe_xUnit i c).symm))
      change φ (Θ.symm g) = ψ (Θ.symm g)
      rw [e, hxΘ i c]
      exact hx (x i c) i c rfl
    · have e : g = adjY Tag.D4 L i c :=
        Subtype.ext (Units.ext (hc.trans (coe_yUnit i c).symm))
      change φ (Θ.symm g) = ψ (Θ.symm g)
      rw [e, hyΘ i c]
      exact hy (y i c) i c rfl
  ext g
  have h := DFunLike.congr_fun hcomp (Θ g)
  simpa [MonoidHom.comp_apply, MulEquiv.symm_apply_apply] using h

end CFSG.StandardType.NTPlane
