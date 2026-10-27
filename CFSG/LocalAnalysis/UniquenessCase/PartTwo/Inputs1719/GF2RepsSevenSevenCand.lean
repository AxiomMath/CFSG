module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FstarBridge
public import CFSG.LieType.CurtisTits.Recognition
public import CFSG.GroupTheory.MulAutCongr

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

theorem quotCenterAut_apply_mk {H : Type} [Group H] (a : MulAut H) (x : H) :
    quotCenterAut H a (QuotientGroup.mk x) = QuotientGroup.mk (a x) :=
  QuotientGroup.congr_mk (Subgroup.center H) (Subgroup.center H) a
    (Subgroup.map_center_eq a) x

theorem quotCenterAut_conj {H : Type} [Group H] (a : H) :
    quotCenterAut H (MulAut.conj a) = MulAut.conj (QuotientGroup.mk a) := by
  ext q
  refine QuotientGroup.induction_on q ?_
  intro b
  rw [quotCenterAut_apply_mk, MulAut.conj_apply]
  simp [map_mul, map_inv]

theorem nonempty_aCandidate_of_surjective {K : Type} [Group K] [Finite K]
    (hKq : IsQuasisimple K) {U : Type} [CommGroup U] [Finite U] (hU : ∀ u : U, u ^ 2 = 1)
    (Y' : Subgroup (MulAut U)) (hLn : (fstarSubOf Y').Normal)
    (hLq : IsQuasisimple ↥(fstarSubOf Y')) (f : K →* ↥(fstarSubOf Y'))
    (hf : Function.Surjective f) : Nonempty (ACandidate K (E3.aParam Y')) := by
  classical
  let A := ↥(fstarTop K)
  let B := ↥(fstarSubOf Y')
  have hKqOpen : CFSG.Open.IsQuasisimple K :=
    CFSG.Quasithin.A3.isQuasisimple_iff_open.mp hKq
  have hKtop : CFSG.Open.IsQuasisimple ↥(⊤ : Subgroup K) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv Subgroup.topEquiv hKqOpen
  have hftop : fstarTop K = ⊤ := fstar_eq_self_of_isQuasisimple hKtop
  let eTop : A ≃* K :=
    (MulEquiv.subgroupCongr hftop).trans
      (Subgroup.topEquiv : ↥(⊤ : Subgroup K) ≃* K)
  have hAq : CFSG.IsQuasisimple A := CFSG.IsQuasisimple.of_mulEquiv eTop hKq
  have hLnK : (fstarTop K).Normal := by
    rw [hftop]
    infer_instance
  have hsub : Function.Surjective (fstarTop K).subtype := by
    intro x
    exact ⟨⟨x, by rw [hftop]; exact Subgroup.mem_top x⟩, rfl⟩
  let π : A →* B := f.comp (fstarTop K).subtype
  have hπsurj : Function.Surjective π := hf.comp hsub
  have : Nontrivial B := CFSG.LocalCores.isQuasisimple_nontrivial hLq
  have hnt : ∃ a : A, π a ≠ 1 := by
    obtain ⟨b, hb⟩ := exists_ne (1 : B)
    obtain ⟨a, rfl⟩ := hπsurj b
    exact ⟨a, hb⟩
  have hπker : π.ker ≤ Subgroup.center A :=
    CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hAq hnt
  let Z₀ : Subgroup A := π.ker
  have hZ₀ : Z₀.Normal := inferInstance
  let ψ : A →* B ⧸ Subgroup.center B :=
    (QuotientGroup.mk' (Subgroup.center B)).comp π
  have hψsurj : Function.Surjective ψ :=
    (QuotientGroup.mk'_surjective (Subgroup.center B)).comp hπsurj
  have hψker : ψ.ker = Subgroup.center A := by
    change ((QuotientGroup.mk' (Subgroup.center B)).comp π).ker = Subgroup.center A
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk',
      CFSG.LieType.CurtisTits.center_eq_map_center_of_isQuasisimple hAq hπsurj hπker,
      Subgroup.comap_map_eq_self hπker]
  let φ : A ⧸ Subgroup.center A ≃* B ⧸ Subgroup.center B :=
    (QuotientGroup.quotientMulEquivOfEq hψker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψsurj)
  have hφmk : ∀ a : A, φ (QuotientGroup.mk a) = QuotientGroup.mk (π a) := by
    intro a
    dsimp only [φ]
    rw [MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  have hcf : ∃ (Z : Subgroup A) (hZ : Z.Normal),
      Z ≤ Subgroup.center A ∧ Nonempty (B ≃* quotBy Z hZ) := by
    refine ⟨Z₀, hZ₀, hπker, ?_⟩
    exact ⟨(QuotientGroup.quotientKerEquivOfSurjective π hπsurj).symm⟩
  let gA : K →* MulAut (A ⧸ Subgroup.center A) :=
    (quotCenterAut A).comp (@MulAut.conjNormal K _ (fstarTop K) hLnK)
  let gB : ↥Y' →* MulAut (B ⧸ Subgroup.center B) :=
    (quotCenterAut B).comp (@MulAut.conjNormal ↥Y' _ (fstarSubOf Y') hLn)
  let j : K →* ↥Y' := (fstarSubOf Y').subtype.comp f
  have hcomp : (MulAut.congr φ).toMonoidHom.comp gA = gB.comp j := by
    apply MonoidHom.ext
    intro x
    let ax : A := ⟨x, by rw [hftop]; exact Subgroup.mem_top x⟩
    let bx : B := f x
    have hx : @MulAut.conjNormal K _ (fstarTop K) hLnK x = MulAut.conj ax := by
      ext y
      simp [ax, MulAut.conjNormal_apply, MulAut.conj_apply]
    have hx' : @MulAut.conjNormal ↥Y' _ (fstarSubOf Y') hLn (j x) = MulAut.conj bx := by
      ext y
      simp [j, bx, MulAut.conjNormal_apply, MulAut.conj_apply]
    have hgAx : gA x = MulAut.conj (QuotientGroup.mk (ax : A)) := by
      dsimp only [gA]
      rw [MonoidHom.comp_apply, hx, quotCenterAut_conj]
    have hgBx : gB (j x) = MulAut.conj (QuotientGroup.mk (bx : B)) := by
      dsimp only [gB]
      rw [MonoidHom.comp_apply, hx', quotCenterAut_conj]
    change (MulAut.congr φ) (gA x) = gB (j x)
    rw [hgAx, hgBx, CFSG.mulAut_congr_conj, hφmk ax]
    rfl
  have himg : (conjImgTop K hLnK).map (MulAut.congr φ).toMonoidHom ≤ conjImgSub Y' hLn := by
    calc (conjImgTop K hLnK).map (MulAut.congr φ).toMonoidHom
        = ((MulAut.congr φ).toMonoidHom.comp gA).range := by
          change (gA.range).map (MulAut.congr φ).toMonoidHom =
            ((MulAut.congr φ).toMonoidHom.comp gA).range
          rw [MonoidHom.map_range]
      _ = (gB.comp j).range := by rw [hcomp]
      _ = j.range.map gB := MonoidHom.range_comp gB j
      _ ≤ gB.range := (Subgroup.map_mono (le_top : j.range ≤ ⊤)).trans_eq
        (Subgroup.map_top gB)
      _ = conjImgSub Y' hLn := rfl
  exact ⟨U, hU, Y', hLnK, hLn, hAq, hLq, hcf, φ, himg, rfl⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
