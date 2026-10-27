module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeTriD4PinnedFrame
public import CFSG.RankThree.PartOne.KD4L.TriNu

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.GGFinModel
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KD4L CFSG.RankThree.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.Adjoint


section Lattice

variable (τ : Tag) [E6Sub τ]

@[expose] def d4ResLat : (Fin τ.rank → ℤ) →+ (Fin Tag.D4.rank → ℤ) where
  toFun β k := β (d4Id k)
  map_zero' := rfl
  map_add' _ _ := rfl

variable {τ}

theorem d4ResLat_apply (β : Fin τ.rank → ℤ) (k : Fin Tag.D4.rank) :
    d4ResLat τ β k = β (d4Id k) :=
  rfl

private theorem exists_d4Lat_of_mem_parabolicRoots
    {β : Fin τ.rank → ℤ} (hβ : β ∈ parabolicRoots τ (d4Set τ)) :
    ∃ α : Fin Tag.D4.rank → ℤ, IsRoot Tag.D4 α ∧ β = e6Lat τ (d4Lat α) := by
  obtain ⟨γ', hγ', heq⟩ := mem_parabolicRoots_d4Set_iff.1 hβ
  obtain ⟨α, hα, hαγ'⟩ := mem_parabolicRoots_d4Support_iff.1 hγ'
  exact ⟨α, hα, heq.symm.trans (by rw [← hαγ'])⟩

private theorem d4ResLat_e6Lat_d4Lat (α : Fin Tag.D4.rank → ℤ) :
    d4ResLat τ (e6Lat τ (d4Lat α)) = α := by
  funext k
  rw [d4ResLat_apply, d4Id, e6Lat_apply_e6Idx, d4Lat_apply_d4Idx]

theorem bijOn_d4ResLat :
    Set.BijOn (d4ResLat τ) (parabolicRoots τ (d4Set τ)) {δ | IsRoot Tag.D4 δ} := by
  refine ⟨?_, ?_, ?_⟩
  · rintro β hβ
    obtain ⟨α, hα, rfl⟩ := exists_d4Lat_of_mem_parabolicRoots hβ
    rwa [d4ResLat_e6Lat_d4Lat]
  · rintro β hβ δ hδ h
    obtain ⟨α, -, rfl⟩ := exists_d4Lat_of_mem_parabolicRoots hβ
    obtain ⟨α', -, rfl⟩ := exists_d4Lat_of_mem_parabolicRoots hδ
    rw [d4ResLat_e6Lat_d4Lat, d4ResLat_e6Lat_d4Lat] at h
    rw [h]
  · rintro α hα
    exact ⟨e6Lat τ (d4Lat α),
      mem_parabolicRoots_d4Set_iff.2 ⟨d4Lat α, d4Lat_mem_parabolicRoots hα, rfl⟩,
      d4ResLat_e6Lat_d4Lat α⟩

theorem iform_d4ResLat
    (hsym : ∀ k l : Fin Tag.D4.rank,
      τ.symmetrizedCartan (d4Id k) (d4Id l) = Tag.D4.symmetrizedCartan k l)
    {β δ : Fin τ.rank → ℤ} (hβ : β ∈ parabolicRoots τ (d4Set τ))
    (hδ : δ ∈ parabolicRoots τ (d4Set τ)) :
    iform (d4ResLat τ β) (d4ResLat τ δ) = iform β δ := by
  classical
  have hsub : ∀ (x : Fin τ.rank → ℤ), (∀ i ∉ d4Set τ, x i = 0) →
      ∀ i : Fin τ.rank,
        i ∉ (d4Id '' (Finset.univ : Finset (Fin Tag.D4.rank)) : Set (Fin τ.rank)) → x i = 0 := by
    intro x hx i hi
    exact hx i fun hmem => hi (by
      obtain ⟨k, rfl⟩ := exists_d4Id_eq hmem
      exact Set.mem_image_of_mem d4Id (by simp))
  simp only [iform, d4ResLat_apply]
  refine Finset.sum_of_injOn (s := Finset.univ) (t := Finset.univ) (e := d4Id (τ := τ))
    (f := fun i : Fin Tag.D4.rank => ∑ j : Fin Tag.D4.rank,
      β (d4Id i) * Tag.D4.symmetrizedCartan i j * δ (d4Id j))
    (g := fun i : Fin τ.rank => ∑ j : Fin τ.rank,
      β i * τ.symmetrizedCartan i j * δ j)
    (fun _ _ _ _ h => d4Id_injective h) (fun _ _ => Finset.mem_univ _)
    (fun i _ hi => by rw [hsub β hβ.2 i hi]; simp) fun i _ => by
      refine Finset.sum_of_injOn (s := Finset.univ) (t := Finset.univ) (e := d4Id (τ := τ))
        (f := fun j : Fin Tag.D4.rank =>
          β (d4Id i) * Tag.D4.symmetrizedCartan i j * δ (d4Id j))
        (g := fun j : Fin τ.rank =>
          β (d4Id i) * τ.symmetrizedCartan (d4Id i) j * δ j)
        (fun _ _ _ _ h => d4Id_injective h) (fun _ _ => Finset.mem_univ _)
        (fun j _ hj => by rw [hsub δ hδ.2 j hj]; simp) fun j _ => by
          rw [hsym i j]

end Lattice

section AuxTorus

variable {τ : Tag}

private theorem torusRootChar_conj_of_mapsRootLines
    {τ : Tag} {K : Type} [Field K] {n h : ModGL τ K}
    {w : WeylGroup τ} (hn : MapsRootLines n w) (hh : h ∈ diagonalGroup)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    torusRootChar (n * h * n⁻¹) α = torusRootChar h (w⁻¹ • α) := by
  obtain ⟨c, hc⟩ := hn.inv α hα
  have hα' : IsRoot τ (w⁻¹ • α) := IsRoot.smul hα w⁻¹
  refine torusRootChar_eq_of_apply hα ?_
  have e2 : (n : Module.End K (RootModule τ K)) ((c : K) • rootVec τ K (w⁻¹ • α)) =
      rootVec τ K α := by
    rw [← hc]
    change ((n * n⁻¹ : ModGL τ K) : Module.End K (RootModule τ K)) (rootVec τ K α) = _
    rw [mul_inv_cancel]
    rfl
  rw [Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply, hc, map_smul,
    apply_rootVec_of_mem_diagonalGroup hh hα', smul_comm, map_smul, e2]

private theorem torusRootChar_rootDiagUnit'
    {τ : Tag} {K : Type} [Field K] (a : Fin τ.rank → Kˣ)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    torusRootChar (rootDiagUnit τ a) α = ((rootChar a α : Kˣ) : K) :=
  torusRootChar_eq_of_apply hα (rootDiag_rootVec a hα)

private theorem rckTorusCoord_rootDiagUnit
    {τ : Tag} (a : Fin τ.rank → GGLˣ) :
    rckTorusCoord (rootDiagUnit τ a) = a := by
  refine rootDiagUnit_injective (K := GGL) ?_
  exact Function.invFun_eq (f := rootDiagUnitHom τ GGL) ⟨a, rfl⟩

private theorem coe_rckRootVal_of_isRoot
    {τ : Tag} {x : ModGL τ GGL}
    (hx : x ∈ torusGroup τ GGL) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    (rckRootVal x β : GGL) = torusRootChar x β := by
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hx
  rw [rckRootVal, rckTorusCoord_rootDiagUnit a, torusRootChar_rootDiagUnit' a hβ]
  rfl


end AuxTorus

section Weyl


variable {τ : Tag}

theorem rootSpan_smul_d4Set (v : WeylGroup τ) :
    rootSpan τ GGL ((fun α => v • α) '' parabolicRoots τ (d4Set τ)) =
      (subsystemGroup τ GGL (d4Set τ)).map
        (MulAut.conj (canonicalRep (coxeterSystem τ) GGL v)).toMonoidHom := by
  rw [subsystemGroup_eq_rootSpan]
  exact ((canonical_weyl_root_transport τ GGL).1 v (parabolicRoots τ (d4Set τ))
    (fun α hα => hα.1)).symm

theorem rckRootVal_conj_canonicalRep {b : ModGL τ GGL} (hb : b ∈ torusGroup τ GGL)
    (v : WeylGroup τ) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    rckRootVal ((canonicalRep (coxeterSystem τ) GGL v)⁻¹ * b *
        canonicalRep (coxeterSystem τ) GGL v) β = rckRootVal b (v • β) := by
  have hb' : (canonicalRep (coxeterSystem τ) GGL v)⁻¹ * b *
      canonicalRep (coxeterSystem τ) GGL v ∈ torusGroup τ GGL := by
    have hn : (canonicalRep (coxeterSystem τ) GGL v)⁻¹ ∈
        Subgroup.normalizer (torusGroup τ GGL : Set (ModGL τ GGL)) :=
      inv_mem ((canonical_weyl_root_transport τ GGL).2.2 v)
    simpa using (Subgroup.mem_normalizer_iff.1 hn b).1 hb
  refine Units.ext ?_
  rw [coe_rckRootVal_of_isRoot hb' hβ, coe_rckRootVal_of_isRoot hb (IsRoot.smul hβ v)]
  simpa using torusRootChar_conj_of_mapsRootLines (mapsRootLines_canonicalRep v).inv
    (torusGroup_le_diagonalGroup hb) hβ

end Weyl

section Diagram


private theorem d4DiagramMap_pow_conj_xUnit {Ω : Type} [Field Ω] (e : ℕ)
    (k : Fin Tag.D4.rank) (c : Ω) :
    d4DiagramMap Ω ^ e * xUnit Tag.D4 Ω k c * (d4DiagramMap Ω ^ e)⁻¹ =
      xUnit Tag.D4 Ω ((d4Rho^[e]) k) c := by
  induction e with
  | zero => simp [Function.iterate_zero]
  | succ e ih =>
    calc d4DiagramMap Ω ^ (e + 1) * xUnit Tag.D4 Ω k c *
          (d4DiagramMap Ω ^ (e + 1))⁻¹
        = d4DiagramMap Ω * (d4DiagramMap Ω ^ e * xUnit Tag.D4 Ω k c *
            (d4DiagramMap Ω ^ e)⁻¹) * (d4DiagramMap Ω)⁻¹ := by
          rw [pow_succ]
          group
      _ = d4DiagramMap Ω * xUnit Tag.D4 Ω ((d4Rho^[e]) k) c * (d4DiagramMap Ω)⁻¹ := by
          rw [ih]
      _ = xUnit Tag.D4 Ω ((d4Rho^[e + 1]) k) c := by
          rw [Function.iterate_succ_apply', d4DiagramMap_conj_xUnit]

private theorem d4DiagramMap_pow_conj_yUnit {Ω : Type} [Field Ω] (e : ℕ)
    (k : Fin Tag.D4.rank) (c : Ω) :
    d4DiagramMap Ω ^ e * yUnit Tag.D4 Ω k c * (d4DiagramMap Ω ^ e)⁻¹ =
      yUnit Tag.D4 Ω ((d4Rho^[e]) k) c := by
  induction e with
  | zero => simp [Function.iterate_zero]
  | succ e ih =>
    calc d4DiagramMap Ω ^ (e + 1) * yUnit Tag.D4 Ω k c *
          (d4DiagramMap Ω ^ (e + 1))⁻¹
        = d4DiagramMap Ω * (d4DiagramMap Ω ^ e * yUnit Tag.D4 Ω k c *
            (d4DiagramMap Ω ^ e)⁻¹) * (d4DiagramMap Ω)⁻¹ := by
          rw [pow_succ]
          group
      _ = d4DiagramMap Ω * yUnit Tag.D4 Ω ((d4Rho^[e]) k) c * (d4DiagramMap Ω)⁻¹ := by
          rw [ih]
      _ = yUnit Tag.D4 Ω ((d4Rho^[e + 1]) k) c := by
          rw [Function.iterate_succ_apply', d4DiagramMap_conj_yUnit]

end Diagram

section Aux

variable {τ : Tag}

private theorem rootDiagUnit_rckTorusCoord
    {τ : Tag} {x : ModGL τ GGL}
    (hx : x ∈ torusGroup τ GGL) : rootDiagUnit τ (rckTorusCoord x) = x := by
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hx
  exact Function.invFun_eq (f := rootDiagUnitHom τ GGL) ⟨a, rfl⟩

private theorem rootChar_single_apply {τ : Tag} {K : Type} [Field K]
    (a : Fin τ.rank → Kˣ) (j : Fin τ.rank) :
    rootChar a (Pi.single j 1) = a j := by
  classical
  rw [rootChar, Finset.prod_eq_single j]
  · simp
  · intro i _ hij
    simp [Pi.single_eq_of_ne hij]
  · intro h
    exact absurd (Finset.mem_univ j) h

private theorem rootChar_neg_apply {τ : Tag} {K : Type} [Field K]
    (a : Fin τ.rank → Kˣ) (v : Fin τ.rank → ℤ) :
    rootChar a (-v) = (rootChar a v)⁻¹ := by
  simp [rootChar, zpow_neg, Finset.prod_inv_distrib]

private theorem rootChar_e6Lat_d4Lat {τ : Tag} [E6Sub τ]
    (c : Fin τ.rank → GGLˣ) (α : Fin Tag.D4.rank → ℤ) :
    rootChar c (e6Lat τ (d4Lat α)) = ∏ k : Fin Tag.D4.rank, c (d4Id k) ^ α k := by
  have hz : ∀ i : Fin τ.rank, i ∉ d4Set τ → e6Lat τ (d4Lat α) i = 0 := by
    intro i hi
    by_cases h : i.val < Tag.E6.rank
    · obtain ⟨k, rfl⟩ := exists_e6Idx_eq (τ := τ) h
      rw [e6Lat_apply_e6Idx]
      have hk : k ∉ d4Support := fun hk => hi ((e6Idx_mem_d4Set_iff k).2 hk)
      rw [mem_d4Support, not_and_or, not_not, not_not] at hk
      rcases hk with rfl | rfl
      · rfl
      · rfl
    · exact e6Lat_apply_of_le (not_lt.1 h)
  rw [rootChar]
  refine (Finset.prod_of_injOn (s := Finset.univ) (t := Finset.univ) (e := d4Id (τ := τ))
    (f := fun k : Fin Tag.D4.rank => c (d4Id k) ^ α k)
    (g := fun i : Fin τ.rank => c i ^ e6Lat τ (d4Lat α) i)
    (fun _ _ _ _ h => d4Id_injective h) (fun _ _ => Finset.mem_univ _) ?_ ?_).symm
  · intro i _ hi
    have hmem : i ∉ d4Set τ := fun h => hi (by
      obtain ⟨k, rfl⟩ := exists_d4Id_eq h
      exact Set.mem_image_of_mem d4Id (by simp))
    rw [hz i hmem, zpow_zero]
  · intro k _
    rw [d4Id, e6Lat_apply_e6Idx, d4Lat_apply_d4Idx]


end Aux

section Native


variable {τ : Tag} [E6Sub τ]
  (ε : ↥(adjointGroup Tag.D4 GGL) ≃* ↥(subsystemGroup τ GGL (d4Set τ)))
  (hεx : ∀ (k : Fin Tag.D4.rank) (c : GGL),
    (ε ⟨xUnit Tag.D4 GGL k c, xUnit_mem_adjointGroup k c⟩ : ModGL τ GGL) =
      xUnit τ GGL (d4Id k) c)
  (hεy : ∀ (k : Fin Tag.D4.rank) (c : GGL),
    (ε ⟨yUnit Tag.D4 GGL k c, yUnit_mem_adjointGroup k c⟩ : ModGL τ GGL) =
      yUnit τ GGL (d4Id k) c)

include hεx hεy

omit
  hεy in
theorem native_symm_xUnit (k : Fin Tag.D4.rank) (c : GGL) :
    (ε.symm ⟨xUnit τ GGL (d4Id k) c, xUnit_mem_subsystemGroup (d4Id_mem k) c⟩ :
      ModGL Tag.D4 GGL) = xUnit Tag.D4 GGL k c := by
  have h : ε.symm ⟨xUnit τ GGL (d4Id k) c, xUnit_mem_subsystemGroup (d4Id_mem k) c⟩ =
      (⟨xUnit Tag.D4 GGL k c, xUnit_mem_adjointGroup k c⟩ : ↥(adjointGroup Tag.D4 GGL)) := by
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext (hεx k c).symm
  exact congrArg Subtype.val h

omit
  hεx in
theorem native_symm_yUnit (k : Fin Tag.D4.rank) (c : GGL) :
    (ε.symm ⟨yUnit τ GGL (d4Id k) c, yUnit_mem_subsystemGroup (d4Id_mem k) c⟩ :
      ModGL Tag.D4 GGL) = yUnit Tag.D4 GGL k c := by
  have h : ε.symm ⟨yUnit τ GGL (d4Id k) c, yUnit_mem_subsystemGroup (d4Id_mem k) c⟩ =
      (⟨yUnit Tag.D4 GGL k c, yUnit_mem_adjointGroup k c⟩ : ↥(adjointGroup Tag.D4 GGL)) := by
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext (hεy k c).symm
  exact congrArg Subtype.val h

theorem native_weylElt (k : Fin Tag.D4.rank) (s : GGLˣ) :
    (ε ⟨weylElt Tag.D4 GGL k s, weylElt_mem_adjointGroup k s⟩ : ModGL τ GGL) =
      weylElt τ GGL (d4Id k) s := by
  have h : (⟨weylElt Tag.D4 GGL k s, weylElt_mem_adjointGroup k s⟩ :
      ↥(adjointGroup Tag.D4 GGL)) =
      ⟨xUnit Tag.D4 GGL k (s : GGL), xUnit_mem_adjointGroup k _⟩ *
        ⟨yUnit Tag.D4 GGL k (-((s⁻¹ : GGLˣ) : GGL)), yUnit_mem_adjointGroup k _⟩ *
          ⟨xUnit Tag.D4 GGL k (s : GGL), xUnit_mem_adjointGroup k _⟩ :=
    Subtype.ext (CFSG.LieType.Chevalley.weylElt_eq_xUnit_mul k s)
  rw [h, map_mul, map_mul]
  simp only [Subgroup.coe_mul]
  rw [hεx, hεy, ← CFSG.LieType.Chevalley.weylElt_eq_xUnit_mul]

theorem native_torusElt (k : Fin Tag.D4.rank) (s : GGLˣ) :
    (ε ⟨torusElt Tag.D4 GGL k s, torusElt_mem_adjointGroup k s⟩ : ModGL τ GGL) =
      torusElt τ GGL (d4Id k) s := by
  rw [show (⟨torusElt Tag.D4 GGL k s, torusElt_mem_adjointGroup k s⟩ :
      ↥(adjointGroup Tag.D4 GGL)) =
      ⟨weylElt Tag.D4 GGL k s, weylElt_mem_adjointGroup k s⟩ *
        ⟨weylElt Tag.D4 GGL k (-1), weylElt_mem_adjointGroup k (-1)⟩ from rfl]
  rw [map_mul]
  simp only [Subgroup.coe_mul]
  rw [native_weylElt ε hεx hεy, native_weylElt ε hεx hεy]
  simp only [torusElt]

theorem native_symm_eq_d4Res_nuE (g : ↥(subsystemGroup τ GGL (d4Set τ))) :
    (ε.symm g : ModGL Tag.D4 GGL) = d4Res GGL (nuE τ GGL g) := by
  have h : ((adjointGroup Tag.D4 GGL).subtype.comp
        (ε.symm : ↥(subsystemGroup τ GGL (d4Set τ)) ≃*
          ↥(adjointGroup Tag.D4 GGL)).toMonoidHom) =
      (d4Res GGL).comp (nuE τ GGL) := by
    refine hom_ext_Q (fun k c => ?_) (fun k c => ?_)
    · change (ε.symm ⟨xUnit τ GGL (d4Id k) c, xUnit_mem_subsystemGroup (d4Id_mem k) c⟩ :
          ModGL Tag.D4 GGL) =
        d4Res GGL (nuE τ GGL ⟨xUnit τ GGL (d4Id k) c,
          xUnit_mem_subsystemGroup (d4Id_mem k) c⟩)
      rw [native_symm_xUnit ε hεx, nuE_xUnit, d4Res_xUnit]
    · change (ε.symm ⟨yUnit τ GGL (d4Id k) c, yUnit_mem_subsystemGroup (d4Id_mem k) c⟩ :
          ModGL Tag.D4 GGL) =
        d4Res GGL (nuE τ GGL ⟨yUnit τ GGL (d4Id k) c,
          yUnit_mem_subsystemGroup (d4Id_mem k) c⟩)
      rw [native_symm_yUnit ε hεy, nuE_yUnit, d4Res_yUnit]
  simpa using DFunLike.congr_fun h g

theorem native_mem_rootSubgroup_iff {β : Fin τ.rank → ℤ} (hβ : β ∈ parabolicRoots τ (d4Set τ))
    (g : ↥(subsystemGroup τ GGL (d4Set τ))) :
    (g : ModGL τ GGL) ∈ rootSubgroup τ GGL β ↔
      (ε.symm g : ModGL Tag.D4 GGL) ∈ rootSubgroup Tag.D4 GGL (d4ResLat τ β) := by
  obtain ⟨α, hα, hβeq⟩ := exists_d4Lat_of_mem_parabolicRoots hβ
  rw [hβeq, d4ResLat_e6Lat_d4Lat]
  have hβ' : d4Lat α ∈ parabolicRoots Tag.E6 d4Support := d4Lat_mem_parabolicRoots hα
  constructor
  · rintro hg
    obtain ⟨c, hc⟩ := mem_rootSubgroup.1 hg
    obtain ⟨ε₀, -, hεeq⟩ := exists_sign_e6Res_pinnedX (τ := τ) hβ'
    let u : ↥(subsystemGroup τ GGL (d4Set τ)) :=
      ⟨pinnedX τ GGL (e6Lat τ (d4Lat α)) c, pinnedX_e6Lat_mem_subsystemGroup hβ' c⟩
    have hgu : g = u := Subtype.ext (hc.symm.trans rfl)
    have hnu : (nuE τ GGL u : ModGL Tag.E6 GGL) =
        pinnedX Tag.E6 GGL (d4Lat α) ((ε₀ : GGL) * c) := by
      rw [coe_nuE]
      exact hεeq GGL c
    have hmem : (nuE τ GGL u : ModGL Tag.E6 GGL) ∈
        rootSubgroup Tag.E6 GGL (d4Lat α) := mem_rootSubgroup.2 ⟨_, hnu.symm⟩
    rw [hgu, native_symm_eq_d4Res_nuE ε hεx hεy u, ← map_d4Res_rootSubgroup hα]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hmem)
  · rintro hg
    have hmem : d4Res GGL (nuE τ GGL g) ∈ rootSubgroup Tag.D4 GGL α := by
      rwa [← native_symm_eq_d4Res_nuE ε hεx hεy g]
    rw [← map_d4Res_rootSubgroup hα] at hmem
    obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.1 hmem
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨c', hc'⟩ := mem_rootSubgroup.1 hx
    obtain ⟨ε₀, hε₀, hεeq⟩ := exists_sign_e6Res_pinnedX (τ := τ) hβ'
    let g' : ↥(subsystemGroup τ GGL (d4Set τ)) :=
      ⟨pinnedX τ GGL (e6Lat τ (d4Lat α)) ((ε₀ : GGL) * c'),
        pinnedX_e6Lat_mem_subsystemGroup hβ' _⟩
    have hsign : (ε₀ : GGL) * ((ε₀ : GGL) * c') = c' := by
      rcases hε₀ with h | h <;> rw [h] <;> ring
    have hnu : (nuE τ GGL g' : ModGL Tag.E6 GGL) = pinnedX Tag.E6 GGL (d4Lat α) c' := by
      rw [coe_nuE]
      exact (hεeq GGL ((ε₀ : GGL) * c')).trans (by rw [hsign])
    have hxg : nuE τ GGL g' = x := Subtype.ext (hnu.trans hc')
    have hgg' : g' = g := by
      refine ε.symm.injective (Subtype.ext ?_)
      rw [native_symm_eq_d4Res_nuE ε hεx hεy g', native_symm_eq_d4Res_nuE ε hεx hεy g,
        hxg, hxeq]
    rw [← hgg']
    exact mem_rootSubgroup.2 ⟨_, rfl⟩

theorem native_symm_frobTwist {h e : ℕ} {N : ModGL τ GGL}
    (hN : N ∈ Subgroup.normalizer (subsystemGroup τ GGL (d4Set τ) : Set (ModGL τ GGL)))
    (hNx : ∀ (k : Fin Tag.D4.rank) (c : GGL),
      N * xUnit τ GGL (d4Id k) c * N⁻¹ = xUnit τ GGL (d4Id (d4Rho^[e] k)) c)
    (hNy : ∀ (k : Fin Tag.D4.rank) (c : GGL),
      N * yUnit τ GGL (d4Id k) c * N⁻¹ = yUnit τ GGL (d4Id (d4Rho^[e] k)) c)
    (g : ↥(subsystemGroup τ GGL (d4Set τ))) :
    (ε.symm (supportedFrobTwistAut 2 h hN g) : ModGL Tag.D4 GGL) =
      triPsi h e (ε.symm g : ModGL Tag.D4 GGL) := by
  have hchar : CharP GGL 2 := inferInstance
  have hfact : Fact (Nat.Prime 2) := inferInstance
  let P : ModGL Tag.D4 GGL := diagramMap TwistTag.D4 GGL
  have htriPsi : triPsi h e = (MulAut.conj (P ^ e)).toMonoidHom.comp
      (Units.map (entrywiseHom (iterateFrobenius GGL 2 h))) := by
    rw [triPsi]
    rfl
  have h : (((adjointGroup Tag.D4 GGL).subtype.comp
        (ε.symm : ↥(subsystemGroup τ GGL (d4Set τ)) ≃*
          ↥(adjointGroup Tag.D4 GGL)).toMonoidHom).comp
        (supportedFrobTwistAut 2 h hN).toMonoidHom) =
      (triPsi h e).comp ((adjointGroup Tag.D4 GGL).subtype.comp
        (ε.symm : ↥(subsystemGroup τ GGL (d4Set τ)) ≃*
          ↥(adjointGroup Tag.D4 GGL)).toMonoidHom) := by
    refine hom_ext_Q (fun k c => ?_) (fun k c => ?_)
    · change (ε.symm (supportedFrobTwistAut 2 h hN
          ⟨xUnit τ GGL (d4Id k) c, xUnit_mem_subsystemGroup (d4Id_mem k) c⟩) :
          ModGL Tag.D4 GGL) =
        triPsi h e (ε.symm ⟨xUnit τ GGL (d4Id k) c,
          xUnit_mem_subsystemGroup (d4Id_mem k) c⟩ : ModGL Tag.D4 GGL)
      have hs : supportedFrobTwistAut 2 h hN
          ⟨xUnit τ GGL (d4Id k) c, xUnit_mem_subsystemGroup (d4Id_mem k) c⟩ =
          ⟨xUnit τ GGL (d4Id ((d4Rho^[e]) k)) (c ^ 2 ^ h),
            xUnit_mem_subsystemGroup (d4Id_mem _) _⟩ := by
        apply Subtype.ext
        rw [coe_supportedFrobTwistAut, frobTwistGL_apply]
        change N * Units.map (entrywiseHom (iterateFrobenius GGL 2 h))
          (xUnit τ GGL (d4Id k) c) * N⁻¹ = _
        rw [entrywise_xUnit, hNx]
      have hx1 : (ε.symm ⟨xUnit τ GGL (d4Id ((d4Rho^[e]) k)) (c ^ 2 ^ h),
            xUnit_mem_subsystemGroup (d4Id_mem _) _⟩ : ModGL Tag.D4 GGL) =
          xUnit Tag.D4 GGL ((d4Rho^[e]) k) (c ^ 2 ^ h) :=
        native_symm_xUnit ε hεx _ _
      have hx0 : (ε.symm ⟨xUnit τ GGL (d4Id k) c,
            xUnit_mem_subsystemGroup (d4Id_mem k) c⟩ : ModGL Tag.D4 GGL) =
          xUnit Tag.D4 GGL k c := native_symm_xUnit ε hεx _ _
      rw [hs, hx1, hx0]
      rw [htriPsi]
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [entrywise_xUnit]
      exact (d4DiagramMap_pow_conj_xUnit e k (c ^ 2 ^ h)).symm
    · change (ε.symm (supportedFrobTwistAut 2 h hN
          ⟨yUnit τ GGL (d4Id k) c, yUnit_mem_subsystemGroup (d4Id_mem k) c⟩) :
          ModGL Tag.D4 GGL) =
        triPsi h e (ε.symm ⟨yUnit τ GGL (d4Id k) c,
          yUnit_mem_subsystemGroup (d4Id_mem k) c⟩ : ModGL Tag.D4 GGL)
      have hs : supportedFrobTwistAut 2 h hN
          ⟨yUnit τ GGL (d4Id k) c, yUnit_mem_subsystemGroup (d4Id_mem k) c⟩ =
          ⟨yUnit τ GGL (d4Id ((d4Rho^[e]) k)) (c ^ 2 ^ h),
            yUnit_mem_subsystemGroup (d4Id_mem _) _⟩ := by
        apply Subtype.ext
        rw [coe_supportedFrobTwistAut, frobTwistGL_apply]
        change N * Units.map (entrywiseHom (iterateFrobenius GGL 2 h))
          (yUnit τ GGL (d4Id k) c) * N⁻¹ = _
        rw [entrywise_yUnit, hNy]
      have hy1 : (ε.symm ⟨yUnit τ GGL (d4Id ((d4Rho^[e]) k)) (c ^ 2 ^ h),
            yUnit_mem_subsystemGroup (d4Id_mem _) _⟩ : ModGL Tag.D4 GGL) =
          yUnit Tag.D4 GGL ((d4Rho^[e]) k) (c ^ 2 ^ h) :=
        native_symm_yUnit ε hεy _ _
      have hy0 : (ε.symm ⟨yUnit τ GGL (d4Id k) c,
            yUnit_mem_subsystemGroup (d4Id_mem k) c⟩ : ModGL Tag.D4 GGL) =
          yUnit Tag.D4 GGL k c := native_symm_yUnit ε hεy _ _
      rw [hs, hy1, hy0]
      rw [htriPsi]
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [entrywise_yUnit]
      exact (d4DiagramMap_pow_conj_yUnit e k (c ^ 2 ^ h)).symm
  simpa using DFunLike.congr_fun h g

private theorem native_symm_weylElt (k : Fin Tag.D4.rank) (s : GGLˣ) :
    (ε.symm ⟨weylElt τ GGL (d4Id k) s,
      weylElt_mem_subsystemGroup (d4Id_mem k) s⟩ : ModGL Tag.D4 GGL) =
      weylElt Tag.D4 GGL k s := by
  have h : ε.symm ⟨weylElt τ GGL (d4Id k) s,
      weylElt_mem_subsystemGroup (d4Id_mem k) s⟩ =
      (⟨weylElt Tag.D4 GGL k s, weylElt_mem_adjointGroup k s⟩ :
        ↥(adjointGroup Tag.D4 GGL)) := by
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext (native_weylElt ε hεx hεy k s).symm
  exact congrArg Subtype.val h

private theorem native_symm_torusElt (k : Fin Tag.D4.rank) (s : GGLˣ) :
    (ε.symm ⟨torusElt τ GGL (d4Id k) s,
      subsystemTorus_le_subsystemGroup (torusElt_mem_subsystemTorus (d4Id_mem k) s)⟩ :
      ModGL Tag.D4 GGL) = torusElt Tag.D4 GGL k s := by
  have h : ε.symm ⟨torusElt τ GGL (d4Id k) s,
      subsystemTorus_le_subsystemGroup (torusElt_mem_subsystemTorus (d4Id_mem k) s)⟩ =
      (⟨torusElt Tag.D4 GGL k s, torusElt_mem_adjointGroup k s⟩ :
        ↥(adjointGroup Tag.D4 GGL)) := by
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext (native_torusElt ε hεx hεy k s).symm
  exact congrArg Subtype.val h

private theorem eps_symm_list_weylElt_mem (l : List (Fin τ.rank))
    (hl : ∀ i ∈ l, i ∈ d4Set τ)
    {h : (l.map fun i => weylElt τ GGL i 1).prod ∈ subsystemGroup τ GGL (d4Set τ)} :
    (ε.symm ⟨(l.map fun i => weylElt τ GGL i 1).prod, h⟩ : ModGL Tag.D4 GGL) ∈
      monomialSubgroup Tag.D4 GGL := by
  induction l with
  | nil =>
    have hone : (⟨(([] : List (Fin τ.rank)).map fun i => weylElt τ GGL i 1).prod, h⟩ :
        ↥(subsystemGroup τ GGL (d4Set τ))) = 1 := Subtype.ext rfl
    rw [hone, map_one]
    exact one_mem _
  | cons i l ih =>
    have hi : i ∈ d4Set τ := hl i (List.mem_cons_self ..)
    have hl' : ∀ j ∈ l, j ∈ d4Set τ := fun j hj => hl j (List.mem_cons_of_mem _ hj)
    have hhead : weylElt τ GGL i 1 ∈ subsystemGroup τ GGL (d4Set τ) :=
      weylElt_mem_subsystemGroup hi 1
    have htail : (l.map fun j => weylElt τ GGL j 1).prod ∈
        subsystemGroup τ GGL (d4Set τ) :=
      Subgroup.list_prod_mem _ fun x hx => by
        obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
        exact weylElt_mem_subsystemGroup (hl' j hj) 1
    have hsub : (⟨(List.map (fun i => weylElt τ GGL i 1) (i :: l)).prod, h⟩ :
        ↥(subsystemGroup τ GGL (d4Set τ))) =
        ⟨weylElt τ GGL i 1, hhead⟩ *
          ⟨(l.map fun j => weylElt τ GGL j 1).prod, htail⟩ := by
      apply Subtype.ext
      simp only [List.map_cons, List.prod_cons, Subgroup.coe_mul]
    rw [hsub, map_mul]
    simp only [Subgroup.coe_mul]
    refine mul_mem ?_ (ih hl')
    obtain ⟨k, rfl⟩ := exists_d4Id_eq hi
    rw [native_symm_weylElt ε hεx hεy]
    exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨k, rfl⟩)

private theorem eps_symm_d4TorusWord_mem (t : Fin Tag.D4.rank → GGLˣ)
    {h : (d4TorusWord t : ModGL τ GGL) ∈ subsystemGroup τ GGL (d4Set τ)} :
    (ε.symm ⟨(d4TorusWord t : ModGL τ GGL), h⟩ : ModGL Tag.D4 GGL) ∈
      monomialSubgroup Tag.D4 GGL := by
  have h0 : torusElt τ GGL (d4Id 0) (t 0) ∈ subsystemGroup τ GGL (d4Set τ) :=
    subsystemTorus_le_subsystemGroup (torusElt_mem_subsystemTorus (d4Id_mem 0) (t 0))
  have h1 : torusElt τ GGL (d4Id 1) (t 1) ∈ subsystemGroup τ GGL (d4Set τ) :=
    subsystemTorus_le_subsystemGroup (torusElt_mem_subsystemTorus (d4Id_mem 1) (t 1))
  have h2 : torusElt τ GGL (d4Id 2) (t 2) ∈ subsystemGroup τ GGL (d4Set τ) :=
    subsystemTorus_le_subsystemGroup (torusElt_mem_subsystemTorus (d4Id_mem 2) (t 2))
  have h3 : torusElt τ GGL (d4Id 3) (t 3) ∈ subsystemGroup τ GGL (d4Set τ) :=
    subsystemTorus_le_subsystemGroup (torusElt_mem_subsystemTorus (d4Id_mem 3) (t 3))
  have hsub : (⟨(d4TorusWord t : ModGL τ GGL), h⟩ :
      ↥(subsystemGroup τ GGL (d4Set τ))) =
      ⟨torusElt τ GGL (d4Id 0) (t 0), h0⟩ * ⟨torusElt τ GGL (d4Id 1) (t 1), h1⟩ *
        ⟨torusElt τ GGL (d4Id 2) (t 2), h2⟩ *
          ⟨torusElt τ GGL (d4Id 3) (t 3), h3⟩ := by
    apply Subtype.ext
    simp only [d4TorusWord, Subgroup.coe_mul]
  rw [hsub, map_mul, map_mul, map_mul]
  simp only [Subgroup.coe_mul]
  rw [native_symm_torusElt ε hεx hεy, native_symm_torusElt ε hεx hεy,
    native_symm_torusElt ε hεx hεy, native_symm_torusElt ε hεx hεy]
  exact mul_mem (mul_mem (mul_mem
    (Subgroup.mem_sup_left (torusElt_mem_torusGroup _ _))
    (Subgroup.mem_sup_left (torusElt_mem_torusGroup _ _)))
    (Subgroup.mem_sup_left (torusElt_mem_torusGroup _ _)))
    (Subgroup.mem_sup_left (torusElt_mem_torusGroup _ _))

theorem native_symm_mem_monomialSubgroup {u : WeylGroup τ}
    (hu : u ∈ parabolicWeylGroup τ (d4Set τ)) (t : Fin Tag.D4.rank → GGLˣ) {q : ModGL τ GGL}
    (hq : q = canonicalRep (coxeterSystem τ) GGL u *
      (torusElt τ GGL (d4Id 0) (t 0) * torusElt τ GGL (d4Id 1) (t 1) *
        torusElt τ GGL (d4Id 2) (t 2) * torusElt τ GGL (d4Id 3) (t 3))⁻¹)
    (hqQ : q ∈ subsystemGroup τ GGL (d4Set τ)) :
    (ε.symm ⟨q, hqQ⟩ : ModGL Tag.D4 GGL) ∈ monomialSubgroup Tag.D4 GGL := by
  have hTQ : (d4TorusWord t : ModGL τ GGL) ∈ subsystemGroup τ GGL (d4Set τ) :=
    d4TorusWord_mem_subsystemGroup t
  have hnQ : canonicalRep (coxeterSystem τ) GGL u ∈
      subsystemGroup τ GGL (d4Set τ) := canonicalRep_mem_subsystemGroup hu
  have hq' : (⟨q, hqQ⟩ : ↥(subsystemGroup τ GGL (d4Set τ))) =
      ⟨canonicalRep (coxeterSystem τ) GGL u, hnQ⟩ * ⟨(d4TorusWord t : ModGL τ GGL), hTQ⟩⁻¹ :=
    Subtype.ext hq
  have hnM : (ε.symm ⟨canonicalRep (coxeterSystem τ) GGL u, hnQ⟩ :
      ModGL Tag.D4 GGL) ∈ monomialSubgroup Tag.D4 GGL := by
    obtain ⟨ω, hω, hwu, hletters⟩ :=
      (parabolic_Weyl_coordinate_stabilizer τ (d4Set τ)).2.1 u hu
    subst hwu
    have hprod : (ω.map fun i => weylElt τ GGL i 1).prod ∈
        subsystemGroup τ GGL (d4Set τ) :=
      Subgroup.list_prod_mem _ fun x hx => by
        obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
        exact weylElt_mem_subsystemGroup (hletters i hi) 1
    have hcan : (⟨canonicalRep (coxeterSystem τ) GGL ((coxeterSystem τ).wordProd ω), hnQ⟩ :
        ↥(subsystemGroup τ GGL (d4Set τ))) =
        ⟨(ω.map fun i => weylElt τ GGL i 1).prod, hprod⟩ :=
      Subtype.ext (canonicalRep_wordProd hω)
    rw [hcan]
    exact eps_symm_list_weylElt_mem ε hεx hεy ω hletters
  have hTM : (ε.symm ⟨(d4TorusWord t : ModGL τ GGL), hTQ⟩ :
      ModGL Tag.D4 GGL) ∈ monomialSubgroup Tag.D4 GGL :=
    eps_symm_d4TorusWord_mem ε hεx hεy t
  rw [hq', map_mul, map_inv]
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using mul_mem hnM (inv_mem hTM)

theorem exists_native_torus {b : ModGL τ GGL} (hb : b ∈ torusGroup τ GGL) :
    ∃ t ∈ torusGroup Tag.D4 GGL,
      (∀ (g : ↥(subsystemGroup τ GGL (d4Set τ)))
          (hbg : b * (g : ModGL τ GGL) * b⁻¹ ∈ subsystemGroup τ GGL (d4Set τ)),
        (ε.symm ⟨b * g * b⁻¹, hbg⟩ : ModGL Tag.D4 GGL) =
          t * (ε.symm g : ModGL Tag.D4 GGL) * t⁻¹) ∧
      ∀ β ∈ parabolicRoots τ (d4Set τ), rckRootVal t (d4ResLat τ β) = rckRootVal b β := by
  classical
  set s : Fin Tag.D4.rank → GGLˣ := fun k => rckRootVal b (Pi.single (d4Id k) 1) with hs
  obtain ⟨t₀, hkey⟩ := exists_d4Params s
  let t : ModGL Tag.D4 GGL :=
    torusElt Tag.D4 GGL 0 (t₀ 0) * torusElt Tag.D4 GGL 1 (t₀ 1) *
      torusElt Tag.D4 GGL 2 (t₀ 2) * torusElt Tag.D4 GGL 3 (t₀ 3)
  have ht_torus : t ∈ torusGroup Tag.D4 GGL :=
    mul_mem (mul_mem (mul_mem (torusElt_mem_torusGroup 0 (t₀ 0))
      (torusElt_mem_torusGroup 1 (t₀ 1))) (torusElt_mem_torusGroup 2 (t₀ 2)))
      (torusElt_mem_torusGroup 3 (t₀ 3))
  have ht_adj : t ∈ adjointGroup Tag.D4 GGL :=
    mul_mem (mul_mem (mul_mem (torusElt_mem_adjointGroup 0 (t₀ 0))
      (torusElt_mem_adjointGroup 1 (t₀ 1))) (torusElt_mem_adjointGroup 2 (t₀ 2)))
      (torusElt_mem_adjointGroup 3 (t₀ 3))
  have hTQ : (d4TorusWord (τ := τ) t₀ : ModGL τ GGL) ∈ subsystemGroup τ GGL (d4Set τ) :=
    d4TorusWord_mem_subsystemGroup t₀
  have hT_torus : (d4TorusWord (τ := τ) t₀ : ModGL τ GGL) ∈ torusGroup τ GGL :=
    d4TorusWord_mem_torusGroup t₀
  have ht_char : ∀ k : Fin Tag.D4.rank,
      torusRootChar t (Pi.single k 1) = (s k : GGL) := by
    intro k
    have hd : ∀ i : Fin Tag.D4.rank, torusElt Tag.D4 GGL i (t₀ i) ∈ diagonalGroup :=
      fun i => torusGroup_le_diagonalGroup (torusElt_mem_torusGroup i (t₀ i))
    rw [show t = torusElt Tag.D4 GGL 0 (t₀ 0) * torusElt Tag.D4 GGL 1 (t₀ 1) *
        torusElt Tag.D4 GGL 2 (t₀ 2) * torusElt Tag.D4 GGL 3 (t₀ 3) from rfl,
      torusRootChar_mul (mul_mem (mul_mem (hd 0) (hd 1)) (hd 2)) (hd 3),
      torusRootChar_mul (mul_mem (hd 0) (hd 1)) (hd 2), torusRootChar_mul (hd 0) (hd 1)]
    rw [torusRootChar_torusElt 0 (t₀ 0) (isRoot_single Tag.D4 k),
      torusRootChar_torusElt 1 (t₀ 1) (isRoot_single Tag.D4 k),
      torusRootChar_torusElt 2 (t₀ 2) (isRoot_single Tag.D4 k),
      torusRootChar_torusElt 3 (t₀ 3) (isRoot_single Tag.D4 k)]
    have hsum : ∀ i : Fin Tag.D4.rank,
        (∑ j, Tag.D4.cartan i j * (Pi.single k 1 : Fin Tag.D4.rank → ℤ) j) =
          Tag.D4.cartan i k := fun i => by simp [Pi.single_apply]
    simp only [hsum]
    exact hkey k
  have hcoord_t : ∀ k : Fin Tag.D4.rank, rckTorusCoord t k = s k := by
    intro k
    refine Units.ext ?_
    have h1 : torusRootChar t (Pi.single k 1) = (↑(rckTorusCoord t k) : GGL) := by
      rw [← rootDiagUnit_rckTorusCoord ht_torus,
        torusRootChar_rootDiagUnit' _ (isRoot_single Tag.D4 k), rootChar_single_apply,
        rckTorusCoord_rootDiagUnit]
    rw [← h1, ht_char k]
  have hcoord_b : ∀ k : Fin Tag.D4.rank, rckTorusCoord b (d4Id k) = s k := by
    intro k
    have h1 : s k = rootChar (rckTorusCoord b) (Pi.single (d4Id k) 1) := rfl
    rw [h1, rootChar_single_apply]
  have hbchar : ∀ k : Fin Tag.D4.rank,
      torusRootChar b (Pi.single (d4Id k) 1) = (s k : GGL) := by
    intro k
    rw [← rootDiagUnit_rckTorusCoord hb,
      torusRootChar_rootDiagUnit' _ (isRoot_single τ (d4Id k)), rootChar_single_apply,
      hcoord_b k]
  have hbchar_neg : ∀ k : Fin Tag.D4.rank,
      torusRootChar b (-Pi.single (d4Id k) 1) = ↑((s k)⁻¹) := by
    intro k
    rw [← rootDiagUnit_rckTorusCoord hb,
      torusRootChar_rootDiagUnit' _ (IsRoot.neg (isRoot_single τ (d4Id k))),
      rootChar_neg_apply, rootChar_single_apply, hcoord_b k]
  have hTchar : ∀ k : Fin Tag.D4.rank,
      torusRootChar (d4TorusWord (τ := τ) t₀) (Pi.single (d4Id k) 1) = (s k : GGL) := by
    intro k
    rw [torusRootChar_d4TorusWord (τ := τ) t₀ (isRoot_single τ (d4Id k))]
    simp only [pair_single_eq, cartan_d4Id]
    exact hkey k
  have hTchar_neg : ∀ k : Fin Tag.D4.rank,
      torusRootChar (d4TorusWord (τ := τ) t₀) (-Pi.single (d4Id k) 1) = ↑((s k)⁻¹) := by
    intro k
    rw [torusRootChar_d4TorusWord (τ := τ) t₀ (IsRoot.neg (isRoot_single τ (d4Id k)))]
    have hn : ∀ a : Fin τ.rank,
        (∑ j, τ.cartan a j * (-Pi.single (d4Id k) 1 : Fin τ.rank → ℤ) j) =
          -τ.cartan a (d4Id k) := fun a => by
      simp [Pi.single_apply, Finset.sum_neg_distrib]
    simp only [hn, cartan_d4Id]
    have hinv : (t₀ 0 ^ (-Tag.D4.cartan 0 k) * t₀ 1 ^ (-Tag.D4.cartan 1 k) *
        t₀ 2 ^ (-Tag.D4.cartan 2 k) * t₀ 3 ^ (-Tag.D4.cartan 3 k) : GGLˣ) = (s k)⁻¹ := by
      rw [← Units.ext (hkey k)]
      simp only [zpow_neg, mul_inv]
    exact congrArg Units.val hinv
  have hεt : (ε ⟨t, ht_adj⟩ : ModGL τ GGL) = (d4TorusWord (τ := τ) t₀ : ModGL τ GGL) := by
    have hsub : (⟨t, ht_adj⟩ : ↥(adjointGroup Tag.D4 GGL)) =
        ⟨torusElt Tag.D4 GGL 0 (t₀ 0), torusElt_mem_adjointGroup 0 (t₀ 0)⟩ *
        ⟨torusElt Tag.D4 GGL 1 (t₀ 1), torusElt_mem_adjointGroup 1 (t₀ 1)⟩ *
        ⟨torusElt Tag.D4 GGL 2 (t₀ 2), torusElt_mem_adjointGroup 2 (t₀ 2)⟩ *
        ⟨torusElt Tag.D4 GGL 3 (t₀ 3), torusElt_mem_adjointGroup 3 (t₀ 3)⟩ :=
      Subtype.ext rfl
    rw [hsub, map_mul, map_mul, map_mul]
    simp only [Subgroup.coe_mul]
    rw [native_torusElt ε hεx hεy, native_torusElt ε hεx hεy,
      native_torusElt ε hεx hεy, native_torusElt ε hεx hεy]
    rfl
  have hconj : ((MulAut.conj b).toMonoidHom.comp
        (subsystemGroup τ GGL (d4Set τ)).subtype) =
      ((MulAut.conj (d4TorusWord (τ := τ) t₀)).toMonoidHom.comp
        (subsystemGroup τ GGL (d4Set τ)).subtype) := by
    refine hom_ext_Q (fun k c => ?_) (fun k c => ?_)
    · change b * xUnit τ GGL (d4Id k) c * b⁻¹ =
        d4TorusWord (τ := τ) t₀ * xUnit τ GGL (d4Id k) c * (d4TorusWord (τ := τ) t₀)⁻¹
      rw [← pinnedX_single, conj_pinnedX_of_mem_torusGroup hb (isRoot_single τ (d4Id k)) c,
        hbchar k, conj_pinnedX_of_mem_torusGroup hT_torus (isRoot_single τ (d4Id k)) c, hTchar k]
    · change b * yUnit τ GGL (d4Id k) c * b⁻¹ =
        d4TorusWord (τ := τ) t₀ * yUnit τ GGL (d4Id k) c * (d4TorusWord (τ := τ) t₀)⁻¹
      rw [← pinnedX_neg_single,
        conj_pinnedX_of_mem_torusGroup hb (IsRoot.neg (isRoot_single τ (d4Id k))) c,
        hbchar_neg k,
        conj_pinnedX_of_mem_torusGroup hT_torus (IsRoot.neg (isRoot_single τ (d4Id k))) c,
        hTchar_neg k]
  have hchar : ∀ β ∈ parabolicRoots τ (d4Set τ), rckRootVal t (d4ResLat τ β) = rckRootVal b β := by
    intro β hβ
    obtain ⟨α, hα, hβeq⟩ := exists_d4Lat_of_mem_parabolicRoots hβ
    have hres : d4ResLat τ β = α := by rw [hβeq, d4ResLat_e6Lat_d4Lat]
    rw [hres]
    refine Units.ext ?_
    rw [coe_rckRootVal_of_isRoot ht_torus hα, coe_rckRootVal_of_isRoot hb hβ.1]
    have hL : torusRootChar t α = ((∏ k : Fin Tag.D4.rank, (s k) ^ (α k) : GGLˣ) : GGL) := by
      rw [← rootDiagUnit_rckTorusCoord ht_torus, torusRootChar_rootDiagUnit' _ hα, rootChar]
      exact congrArg Units.val (Finset.prod_congr rfl fun k _ => by rw [hcoord_t k])
    have hR : torusRootChar b β = ((∏ k : Fin Tag.D4.rank, (s k) ^ (α k) : GGLˣ) : GGL) := by
      rw [← rootDiagUnit_rckTorusCoord hb, torusRootChar_rootDiagUnit' _ hβ.1]
      rw [hβeq, rootChar_e6Lat_d4Lat]
      exact congrArg Units.val (Finset.prod_congr rfl fun k _ => by rw [hcoord_b k])
    rw [hL, hR]
  refine ⟨t, ht_torus, ?_, hchar⟩
  intro g hbg
  have hgg : b * (subsystemGroup τ GGL (d4Set τ)).subtype g * b⁻¹ =
      d4TorusWord (τ := τ) t₀ * (subsystemGroup τ GGL (d4Set τ)).subtype g *
        (d4TorusWord (τ := τ) t₀)⁻¹ := by
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      using DFunLike.congr_fun hconj g
  have hbg' : d4TorusWord (τ := τ) t₀ * (subsystemGroup τ GGL (d4Set τ)).subtype g *
      (d4TorusWord (τ := τ) t₀)⁻¹ ∈ subsystemGroup τ GGL (d4Set τ) := by
    rw [← hgg]
    exact hbg
  have h1 : (⟨b * (g : ModGL τ GGL) * b⁻¹, hbg⟩ :
      ↥(subsystemGroup τ GGL (d4Set τ))) =
      ⟨d4TorusWord (τ := τ) t₀ * (g : ModGL τ GGL) * (d4TorusWord (τ := τ) t₀)⁻¹, hbg'⟩ :=
    Subtype.ext hgg
  rw [h1]
  have harg : (⟨d4TorusWord (τ := τ) t₀ * (g : ModGL τ GGL) * (d4TorusWord (τ := τ) t₀)⁻¹, hbg'⟩ :
      ↥(subsystemGroup τ GGL (d4Set τ))) = ε ⟨t, ht_adj⟩ * g * (ε ⟨t, ht_adj⟩)⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hεt]
  rw [harg]
  have hm : (ε.symm (ε ⟨t, ht_adj⟩ * g * (ε ⟨t, ht_adj⟩)⁻¹) :
      ↥(adjointGroup Tag.D4 GGL)) = ⟨t, ht_adj⟩ * ε.symm g * ⟨t, ht_adj⟩⁻¹ := by
    rw [map_mul, map_mul, map_inv]
    simp
  rw [show (ε.symm (ε ⟨t, ht_adj⟩ * g * (ε ⟨t, ht_adj⟩)⁻¹) : ModGL Tag.D4 GGL) =
      ((⟨t, ht_adj⟩ * ε.symm g * ⟨t, ht_adj⟩⁻¹ : ↥(adjointGroup Tag.D4 GGL)) :
        ModGL Tag.D4 GGL) from congrArg Subtype.val hm]
  rfl

end Native

end CFSG.StandardType.RCKRP

end


