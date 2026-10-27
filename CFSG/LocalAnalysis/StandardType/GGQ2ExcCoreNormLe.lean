module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreAmbientCent
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreOccursDict
import CFSG.LieType.Chevalley.SignKernelComponentBruhat
import CFSG.LocalAnalysis.StandardType.GGLinImageSubspace

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.QTwoCav CFSG.StandardType.TableCRes


namespace ExcCoordDatum

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} {S : LangSetup τ L p}
  {T₀ : Subgroup (ModGL τ L)} {m : Fin 6} (d : ExcCoordDatum S T₀ m)
include d

theorem exists_le_ggLinImage_eq (U : Submodule (ZMod 3) (ExcRaw.V m)) :
    ∃ A : Subgroup (ModGL τ L), A ≤ T₀ ∧ ggLinImage (p := 3) d.coord A = U :=
  exists_le_ggLinImage_eq_of_addEquiv d.coord U

theorem exists_famCharHom_componentRoots_eq {c : Finset (ExcRaw.Root m)}
    (hc : ∃ U, ExcRaw.occurs m U c) :
    ∃ (A : Subgroup (ModGL τ L)) (a : ↥A → Fin τ.rank → Lˣ)
      (j : KernelComponent (famCharHom a)), componentRoots (famCharHom a) j = codeRoots d.γ c := by
  classical
  obtain ⟨U, hU⟩ := hc
  obtain ⟨A, hA, hAU⟩ := d.exists_le_ggLinImage_eq U
  obtain ⟨a, ha, -, -⟩ := exists_excFamily d hA
  obtain ⟨j, hj⟩ := exists_kernelComponent_of_occurs d hA ha (hAU.symm ▸ hU)
  exact ⟨A, a, j, hj⟩

theorem exists_weylTuple_mem_weyl {c : Finset (ExcRaw.Root m)} {w : WeylGroup τ}
    (hw : w ∈ componentWeylGroup (codeRoots d.γ c)) :
    ∃ M ∈ ExcRaw.weyl m c, ∀ (b : Fin τ.rank → Lˣ) (hb : rootDiagUnit τ b ∈ T₀),
      ∃ h : rootDiagUnit τ (weylTuple w b) ∈ T₀,
        d.coord (Additive.ofMul ⟨_, h⟩) = M (d.coord (Additive.ofMul ⟨_, hb⟩)) := by
  classical
  have hgen : ∀ β ∈ simpleRoots (codeRoots d.γ c),
      ∃ M ∈ ExcRaw.weyl m c, ∀ (b : Fin τ.rank → Lˣ) (hb : rootDiagUnit τ b ∈ T₀),
        ∃ h : rootDiagUnit τ (weylTuple (rootReflection β) b) ∈ T₀,
          d.coord (Additive.ofMul ⟨_, h⟩) =
            M (d.coord (Additive.ofMul ⟨_, hb⟩)) := by
    intro β hβ
    obtain ⟨i, hi, hβi⟩ := simpleRoots_subset hβ
    refine ⟨ExcRaw.reflection m i, Subgroup.subset_closure ⟨i, hi, rfl⟩, fun b hb => ?_⟩
    rcases hβi with rfl | hβi
    · exact d.weylTuple_reflection_mem i hb
    · rw [hβi, rootReflection_neg (d.isRoot i)]
      exact d.weylTuple_reflection_mem i hb
  induction hw using Subgroup.closure_induction'' with
  | mem x hx =>
      obtain ⟨β, hβ, rfl⟩ := hx
      exact hgen β hβ
  | inv_mem x hx =>
      obtain ⟨β, hβ, rfl⟩ := hx
      rw [rootReflection_inv (simpleRoots_isRoot hβ)]
      exact hgen β hβ
  | one =>
      refine ⟨1, (ExcRaw.weyl m c).one_mem, fun b hb => ?_⟩
      rw [weylTuple_one]
      exact ⟨hb, by simp⟩
  | mul w w' hw hw' ihw ihw' =>
      obtain ⟨M, hM, hMprop⟩ := ihw
      obtain ⟨M', hM', hM'prop⟩ := ihw'
      refine ⟨M * M', (ExcRaw.weyl m c).mul_mem hM hM', fun b hb => ?_⟩
      obtain ⟨h', hcoord'⟩ := hM'prop b hb
      obtain ⟨h'', hcoord''⟩ := hMprop (weylTuple w' b) h'
      rw [← weylTuple_weylTuple]
      exact ⟨h'', hcoord''.trans (by rw [hcoord', LinearEquiv.mul_apply])⟩

section Bruhat


theorem exists_mem_componentWeylGroup_of_mem_rootSpan (hsep : ExcRaw.RootSep m)
    {c : Finset (ExcRaw.Root m)} (hc : ∃ U, ExcRaw.occurs m U c) {g : ModGL τ L}
    (hg : g ∈ rootSpan τ L (codeRoots d.γ c))
    (hgN : g ∈ Subgroup.normalizer (T₀ : Set (ModGL τ L))) :
    ∃ w ∈ componentWeylGroup (codeRoots d.γ c),
      ∀ b, g * rootDiagUnit τ b * g⁻¹ = rootDiagUnit τ (weylTuple w b) := by
  classical
  obtain ⟨A, a, j, hcomp⟩ := d.exists_famCharHom_componentRoots_eq hc
  obtain ⟨v, j', hvj⟩ := exists_componentWeylChoice (famCharHom a) j
  have hgspan : g ∈ componentRootSpan L (famCharHom a) j := by
    change g ∈ rootSpan τ L (componentRoots (famCharHom a) j)
    rw [hcomp]
    exact hg
  have hmemU : g ∈ ⋃ w ∈ componentWeylGroup (componentRoots (famCharHom a) j),
      componentCell L (famCharHom a) j v j' w := by
    rw [← coe_componentRootSpan_eq_iUnion (K := L) (χ := famCharHom a) (i := j) hvj]
    exact hgspan
  simp only [Set.mem_iUnion, exists_prop] at hmemU
  obtain ⟨w', hw'W, hgw'⟩ := hmemU
  have hgB' : g ∈ bruhatCell τ L w' :=
    componentCell_subset_bruhatCell (χ := famCharHom a) (i := j) (v := v) (j := j') w' hgw'
  have hgadj : g ∈ adjointGroup τ L := rootSpan_le_adjointGroup L (codeRoots d.γ c) hg
  obtain ⟨h, hh, w, rfl⟩ :=
    CFSG.RankThree.Chevalley.exists_eq_mul_canonicalRep_of_mem_normalizer
      (V := (T₀ : Set (ModGL τ L))) d.le_torusGroup
      (d.adjointGroup_inf_centralizer hsep) ⟨hgadj, hgN⟩
  have hconj : ∀ b, (h * canonicalRep (coxeterSystem τ) L w) * rootDiagUnit τ b *
      (h * canonicalRep (coxeterSystem τ) L w)⁻¹ = rootDiagUnit τ (weylTuple w b) := by
    intro b
    rw [show h * canonicalRep (coxeterSystem τ) L w * rootDiagUnit τ b *
          (h * canonicalRep (coxeterSystem τ) L w)⁻¹ =
        h * (canonicalRep (coxeterSystem τ) L w * rootDiagUnit τ b *
          (canonicalRep (coxeterSystem τ) L w)⁻¹) * h⁻¹ by group,
      canonicalRep_conj_rootDiagUnit,
      CFSG.LieType.Chevalley.RootTorus.torusGroup_mul_comm hh
        (rootDiagUnit_mem_torusGroup (τ := τ) (K := L) (weylTuple w b)),
      mul_inv_cancel_right]
  have hgB : (h * canonicalRep (coxeterSystem τ) L w) ∈ bruhatCell τ L w :=
    mem_bruhatCell.2 ⟨h, torusGroup_le_borelGroup hh, 1, one_mem _, by simp⟩
  have hww' : w = w' := by
    by_contra hne
    exact Set.disjoint_left.mp (disjoint_bruhatCell (K := L) hne) hgB hgB'
  refine ⟨w, ?_, hconj⟩
  rw [hww']
  exact hcomp ▸ hw'W

theorem map_ggAutomizer_codeComponent_le_weyl (hsep : ExcRaw.RootSep m)
    {c : Finset (ExcRaw.Root m)} (hc : ∃ U, ExcRaw.occurs m U c) :
    (ggAutomizer (codeComponent S d.γ c) T₀).map (ggLin (p := 3) d.coord) ≤
      ExcRaw.weyl m c := by
  rw [ggAutomizer, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨φ, ⟨g, hgH, hgN, hgφ⟩, rfl⟩
  have hgspan : g ∈ rootSpan τ L (codeRoots d.γ c) :=
    (Subgroup.commutator_le_self
      (rootSpan τ L (codeRoots d.γ c) ⊓ S.Γ)).trans inf_le_left hgH
  obtain ⟨w, hwW, hwconj⟩ :=
    d.exists_mem_componentWeylGroup_of_mem_rootSpan hsep hc hgspan hgN
  obtain ⟨M, hM, hMw⟩ := d.exists_weylTuple_mem_weyl hwW
  suffices ggLin (p := 3) d.coord φ = M from this ▸ hM
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨t, rfl⟩ := d.coord.surjective v
  rw [← ofMul_toMul t, ggLin_apply_ofMul]
  obtain ⟨b, hb⟩ := d.exists_rootDiagUnit (Additive.toMul t)
  have hbT : rootDiagUnit τ b ∈ T₀ := hb ▸ (Additive.toMul t).2
  obtain ⟨hmem, hcoord⟩ := hMw b hbT
  have h1 : φ (Additive.toMul t) = ⟨_, hmem⟩ := Subtype.ext (by rw [hgφ, hb, hwconj])
  have h2 : Additive.toMul t = ⟨_, hbT⟩ := Subtype.ext hb
  rw [h1, hcoord, ← h2]

end Bruhat

end ExcCoordDatum

end CFSG.StandardType.GGQ2Frame.ExcPlacement

end
