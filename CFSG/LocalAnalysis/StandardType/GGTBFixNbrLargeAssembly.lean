module

public import CFSG.LocalAnalysis.StandardType.GGLargeFixDefs
public import CFSG.LocalAnalysis.StandardType.GGTBFixNbrDefs
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeKFixLineProducer
public import CFSG.LocalAnalysis.StandardType.GGTBFixNbrXInnerWeyl
public import CFSG.LocalAnalysis.StandardType.GGLargeRowKDatum
public import CFSG.LocalAnalysis.StandardType.GGLargeRowCard
public import CFSG.LocalAnalysis.StandardType.GGLargeRowShared
public import CFSG.LocalAnalysis.StandardType.GGLargeRowFrame
public import CFSG.LocalAnalysis.StandardType.GGLargeDepFixLineKG
public import CFSG.LocalAnalysis.StandardType.GGResKnownGroup
public import CFSG.LocalAnalysis.StandardType.GGResHdRoNarrowDefs
public import CFSG.LocalAnalysis.StandardType.GGResXDichotomyDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleDefs
public import CFSG.LocalAnalysis.StandardType.GGRowKFrame
public import CFSG.LocalAnalysis.StandardType.GGHLAutomizer

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggLargeFixLine_indep (hI : GGIndepFixLineLin) {p N : ℕ} [Fact p.Prime] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {h : Fin (N - 1) → V}
    {α : Fin (N - 1) → Module.Dual (ZMod p) V} {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {T : Type}
    {s : T → (V ≃ₗ[ZMod p] V)} {x : V} (F : GGLargeLinHyp p N h α r s x)
    (hind : LinearIndependent (ZMod p) h) :
    Module.finrank (ZMod p) ↥(ggLinFix (Set.range r)) ≤ 1 := by
  have := F.finT
  have hN := F.N_ge
  exact (hI p N F.p_ne_two (by omega) F.p_dvd V F.dim_le h α r hind F.pair F.refl_form T s
    F.s_refl F.conn x F.x_ne F.fix_s F.x_not_fix F.no_transv).le

theorem ggLargeFixLineLin_of_branches (hI : GGIndepFixLineLin) (hD : GGLargeDepFixLineLin) :
    GGLargeFixLineLin := by
  intro p N _ V _ _ h α r T s x F hcard
  by_cases hind : LinearIndependent (ZMod p) h
  · exact ggLargeFixLine_indep hI F hind
  · exact hD p N V h α r T s x F hind (hcard hind)


theorem ggTBFixNbrLargeInput_of_frame (hFrame : GGLargeRowFrameInput) (hLin : GGLargeFixLineLin) :
    GGTBFixNbrLargeInput := by
  intro G _ _ p _ B Bs x L D J y K hH hrow b hb
  classical
  obtain ⟨labJ, labK, hJΛ, hKΛ, hJl, hKl, hr2, hr10⟩ := hrow
  have hrowN : GGResRowAt (ggRowLargeN (labK.rank + 1)) p J K :=
    ⟨labJ, labK, hJΛ, hKΛ, hJl, hKl, hr2, hr10, rfl⟩
  have hx : x ∈ Bs := hH.1.tableB_facts.2.2.1
  have hyD : y ∈ D := by
    rw [hH.2.2.2.2.1.2.1]
    exact Subgroup.subset_closure (by simp)
  have hy : y ∈ Bs := hH.1.2.1.1 (hH.1.2.2.1.1 hyD)
  have hy1 : y ≠ 1 := ggRC_y_ne_one hH
  have hKy : K ≤ Subgroup.centralizer ({y} : Set G) := hH.2.2.2.2.1.1.2.2.2.1
  have hfixy : ∀ φ ∈ ggAutomizer K Bs, φ (⟨y, hy⟩ : ↥Bs) = ⟨y, hy⟩ :=
    ggHLA_fixes_x hKy hy
  obtain ⟨V, iVadd, iVmod, ι, h, α, r, T, s, F, hclos, hcard⟩ :=
    hFrame G p B Bs x L D J y K (labK.rank + 1) hH hrowN hx
  let := iVadd
  let := iVmod
  have : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have : Module.Finite (ZMod p) V := Module.Finite.of_finite
  let Fx : Submodule (ZMod p) V := ggLinFix (Set.range r)
  let xV : V := ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs))
  let vy : V := ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs))
  have hFfin : Module.finrank (ZMod p) Fx ≤ 1 := hLin p (labK.rank + 1) V h α r T s xV F hcard
  have hvy_mem : vy ∈ Fx := by
    intro a ha
    rcases ha with ⟨i, rfl⟩
    have hri : r i ∈ Subgroup.closure (Set.range r) := Subgroup.subset_closure ⟨i, rfl⟩
    rw [hclos] at hri
    rcases Subgroup.mem_map.mp hri with ⟨φ, hφA, hφi⟩
    calc (r i) vy = ggLin (p := p) ι φ vy := by rw [hφi]
      _ = ggLin (p := p) ι φ (ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs))) := rfl
      _ = ι (Additive.ofMul (φ (⟨y, hy⟩ : ↥Bs))) := by rw [ggLin_apply_ofMul]
      _ = ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs)) := by rw [hfixy φ hφA]
      _ = vy := rfl
  have hvy0 : vy ≠ 0 := by
    intro h0
    have h1 : Additive.ofMul (⟨y, hy⟩ : ↥Bs) = 0 := by
      apply ι.injective
      simpa [vy] using h0
    have h2 : (⟨y, hy⟩ : ↥Bs) = 1 := by
      have := congrArg Additive.toMul h1
      simpa using this
    exact hy1 (by simpa using congrArg Subtype.val h2)
  have hspan_le : Submodule.span (ZMod p) ({vy} : Set V) ≤ Fx := by
    rw [Submodule.span_le]
    intro v hv
    rw [Set.mem_singleton_iff] at hv
    rw [hv]
    exact hvy_mem
  have hFeq : Fx = Submodule.span (ZMod p) ({vy} : Set V) :=
    (Submodule.eq_of_le_of_finrank_le hspan_le
      (by rw [finrank_span_singleton hvy0]; exact hFfin)).symm
  have hbF : ι (Additive.ofMul b) ∈ Fx := by
    intro a ha
    rcases ha with ⟨i, rfl⟩
    have hri : r i ∈ Subgroup.closure (Set.range r) := Subgroup.subset_closure ⟨i, rfl⟩
    rw [hclos] at hri
    rcases Subgroup.mem_map.mp hri with ⟨φ, hφA, hφi⟩
    calc (r i) (ι (Additive.ofMul b))
        = ggLin (p := p) ι φ (ι (Additive.ofMul b)) := by rw [hφi]
      _ = ι (Additive.ofMul (φ b)) := by rw [ggLin_apply_ofMul]
      _ = ι (Additive.ofMul b) := by rw [hb φ hφA]
  rw [hFeq] at hbF
  rcases Submodule.mem_span_singleton.mp hbF with ⟨c, hc⟩
  have hc' : (c.val : ℤ) • vy = ι (Additive.ofMul b) := by
    rw [← Int.cast_smul_eq_zsmul (R := ZMod p)]
    simp only [Int.cast_natCast, ZMod.natCast_zmod_val]
    exact hc
  have hpow : Additive.ofMul ((⟨y, hy⟩ : ↥Bs) ^ (c.val : ℤ)) = Additive.ofMul b := by
    apply ι.injective
    calc ι (Additive.ofMul ((⟨y, hy⟩ : ↥Bs) ^ (c.val : ℤ)))
        = ι ((c.val : ℤ) • Additive.ofMul (⟨y, hy⟩ : ↥Bs)) := by rw [ofMul_zpow]
      _ = (c.val : ℤ) • ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs)) := by rw [map_zsmul]
      _ = (c.val : ℤ) • vy := rfl
      _ = ι (Additive.ofMul b) := hc'
  refine Subgroup.mem_zpowers_iff.mpr ⟨(c.val : ℤ), ?_⟩
  have hc2 := congrArg (fun z : ↥Bs => (z : G)) (congrArg Additive.toMul hpow)
  simpa using hc2

theorem ggTBFixNbrInput_holds
    (hWI : GGNbrInnerWeylInput) (hUse : ZS.UseInput) (hKG : GGReflClassLargeInput')
    (hT : GGTBTorANarrow) (hLift : GGTBTorLiftADepRows) (hRig : GGLabelRigidInput)
    (hX : GGResXDichotomyInput) (hFix : GGTBFixInput) (hOrb : GGResCentBoundInput)
    (hTCJ : GGTCJKnown) (hDim : GGTwoNodeRowDimKnown) : GGTBFixNbrInput := by
  have hWA : GGTBFixNbrXInput := ggTBFixNbrXInput_of_innerWeyl hWI
  have hNoSeven : GGLargeRowNoSevenAtL := ggLargeRowNoSevenAtL_of_tcj hTCJ hRig
  exact ⟨hWA, ggTBFixNbrLargeInput_of_frame
    (ggLargeRowFrame_of_pieces (ggLargeRowKDatum_of_inputs hT hLift hRig) hX hFix hNoSeven
      (ggLargeRowCard_of_inputs hOrb hX hNoSeven (ggLargeRowDimKnown_of_twoNode hDim)) hDim hWA)
    (ggLargeFixLineLin_of_branches (ggIndepFixLineLin_of_zs hUse)
      (ggLargeDepFixLineLin_of_kg hKG))⟩

end CFSG.StandardType

end
