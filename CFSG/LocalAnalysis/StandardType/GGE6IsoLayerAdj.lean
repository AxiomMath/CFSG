module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeLayerFrame
public import CFSG.LieType.Universal.SpecialLinear
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
public import CFSG.ClassicalInvolution.WeakCT.StandardPair
public import CFSG.ClassicalInvolution.WeakCT.TorusAgree
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAut
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.Classical2.TwistedE6Phi3A2Case
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartOne.KE.ThreeA1Group
public import CFSG.RankThree.PartOne.KLCE.Sector
public import CFSG.RankThree.PartOne.KLR.SL2Gen

public section

namespace CFSG.StandardType.KGL

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
  (e6LineChar e6LineFactor e6Line_kernel rootSpan_eq_iSup_e6LineFactor e6LineFactor_normalizer
    exists_lineFrames)

theorem kgAdjNonIso
    {K : Type} [Field K] {ζ : Kˣ} (hζ : ζ ^ 3 = 1) (h1 : ζ ≠ 1)
    (i : Fin 3) :
    IsComponentOf (e6LineFactor K i) (toralCentralizer Tag.E6 K (e6LineChar ζ)) := by
  obtain ⟨hMC, hMn, -, -, -⟩ :=
    Chevalley_toral_centralizer_root_generated_quotient Tag.E6 K (e6LineChar ζ)
  have hroot : e6LineFactor K i ≤ rootSpan Tag.E6 K (rootCharKernel (e6LineChar ζ)) := by
    rw [e6Line_kernel hζ h1, rootSpan_eq_iSup_e6LineFactor]
    exact le_iSup (fun j => e6LineFactor K j) i
  have hUM : e6LineFactor K i ≤ toralRootGroup Tag.E6 K (e6LineChar ζ) := by
    rw [toralRootGroup]
    exact hroot.trans le_sup_right
  have hUn : ((e6LineFactor K i).subgroupOf (toralRootGroup Tag.E6 K (e6LineChar ζ))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUM).2 (e6LineFactor_normalizer hζ h1 i)
  refine ⟨hUM.trans hMC, IsSubnormal.step hUM hUn
    (IsSubnormal.step hMC hMn (IsSubnormal.refl _)), ?_⟩
  obtain ⟨ρ, hinj, hrange, -⟩ := exists_lineFrames K
  let e : Matrix.SpecialLinearGroup (Fin 3) K ≃* ↥(e6LineFactor K i) :=
    (MonoidHom.ofInjective (f := ρ i) (hinj i)).trans (MulEquiv.subgroupCongr (hrange i))
  exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2
    ((CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr e).1
      (CFSG.LieType.Universal.SpecialLinear.isQuasisimple 2 K le_rfl))

theorem isComponentOf_e6LineFactor_inf
    {Ω : Type} [Field Ω] {ζ : Ωˣ} (hζ : ζ ^ 3 = 1)
    (h1 : ζ ≠ 1) (i : Fin 3) (Γ : Subgroup (ModGL .E6 Ω))
    (hΓ : Γ ≤ adjointGroup .E6 Ω)
    (hQ : CFSG.Assembly.IsQuasisimple ↥(e6LineFactor Ω i ⊓ Γ)) :
    CFSG.Assembly.IsComponentOf (e6LineFactor Ω i ⊓ Γ)
      (Γ ⊓ Subgroup.centralizer {rootDiagUnit .E6 (e6LineChar ζ)}) := by
  have hgeom := kgAdjNonIso hζ h1 i
  have hC : toralCentralizer Tag.E6 Ω (e6LineChar ζ) ⊓ Γ =
      Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 (e6LineChar ζ)} := by
    rw [toralCentralizer, inf_assoc, inf_comm (Subgroup.centralizer _) Γ,
      ← inf_assoc, inf_eq_right.2 hΓ]
  refine ⟨?_, ?_, hQ⟩
  · rw [← hC]
    exact inf_le_inf hgeom.1 le_rfl
  · rw [← hC]
    exact hgeom.2.1.inf Γ

theorem e6LineFactor_inf_coord_ne_one
    {Ω : Type} [Field Ω] {H : Type} [Group H] [Finite H]
    {ι : H →* ModGL Tag.E6 Ω} (hι : Function.Injective ι) {J K : Subgroup H} {e : H}
    {a b : Ωˣ} (hJq : CFSG.Assembly.IsQuasisimple ↥J)
    (hK : CFSG.Assembly.IsComponentOf K (Subgroup.centralizer ({e} : Set H)))
    (hJK : J ≤ K) (hKJ : K ≠ J)
    (hJmap : J.map ι = e6LineFactor Ω 0 ⊓ ι.range)
    (hΓ : ι.range ≤ adjointGroup Tag.E6 Ω)
    (he : ι e = rootDiagUnit Tag.E6 ![1, a, 1, b, 1, 1])
    (hb3 : b ^ 3 = 1) (he1 : e ≠ 1) :
    a ≠ 1 := by
  rintro rfl
  have hb1 : b ≠ 1 := by
    rintro rfl
    refine he1 (hι ?_)
    have hvec : (![1, 1, 1, 1, 1, 1] : Fin Tag.E6.rank → Ωˣ) = 1 := by
      funext i
      fin_cases i <;> rfl
    have hroot : rootDiagUnit Tag.E6
        (![1, 1, 1, 1, 1, 1] : Fin Tag.E6.rank → Ωˣ) = 1 := by
      rw [hvec]
      exact rootDiagUnit_one (K := Ω)
    rw [hroot] at he
    simpa only [map_one] using he
  have hline : ι e = rootDiagUnit Tag.E6 (e6LineChar b) := by
    simpa only [e6LineChar] using he
  have hJmq : CFSG.Assembly.IsQuasisimple ↥(J.map ι) :=
    CFSG.Assembly.IsQuasisimple.of_mulEquiv (J.equivMapOfInjective ι hι).symm hJq
  have hQ : CFSG.Assembly.IsQuasisimple ↥(e6LineFactor Ω 0 ⊓ ι.range) := by
    rw [← hJmap]
    exact hJmq
  have hgeom : CFSG.Assembly.IsComponentOf (J.map ι)
      (ι.range ⊓ Subgroup.centralizer ({ι e} : Set (ModGL Tag.E6 Ω))) := by
    rw [hJmap, hline]
    exact isComponentOf_e6LineFactor_inf hb3 hb1 (0 : Fin 3) ι.range hΓ hQ
  have hCpre :
      (ι.range ⊓ Subgroup.centralizer ({ι e} : Set (ModGL Tag.E6 Ω))).comap ι =
        Subgroup.centralizer ({e} : Set H) := by
    ext u
    change (ι u ∈ ι.range ∧
        ι u ∈ Subgroup.centralizer ({ι e} : Set (ModGL Tag.E6 Ω))) ↔
      u ∈ Subgroup.centralizer ({e} : Set H)
    rw [Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨_, hu⟩
      apply hι
      simpa only [map_mul] using hu
    · intro hu
      exact ⟨⟨u, rfl⟩, by simpa only [map_mul] using congrArg ι hu⟩
  have hJpre : (J.map ι).comap ι = J :=
    Subgroup.comap_map_eq_self_of_injective hι J
  have hle : (J.map ι).comap ι ≤
      (ι.range ⊓ Subgroup.centralizer ({ι e} : Set (ModGL Tag.E6 Ω))).comap ι :=
    Subgroup.comap_mono hgeom.1
  have hsub := CFSG.Assembly.IsSubnormal.comap ι hgeom.2.1
  have hJcomp : CFSG.Assembly.IsComponentOf J
      (Subgroup.centralizer ({e} : Set H)) := by
    refine ⟨?_, ?_, hJq⟩
    · simpa only [hJpre, hCpre] using hle
    · simpa only [hJpre, hCpre] using hsub
  exact hKJ
    (CFSG.LocalAnalysis.ComponentInitial.eq_of_isComponentOf_le hJcomp hK hJK).symm

end CFSG.StandardType.KGL

end
