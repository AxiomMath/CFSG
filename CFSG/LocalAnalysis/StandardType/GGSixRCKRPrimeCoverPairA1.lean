module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeShapeLeaves
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCarrierA1
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCarrierA1Cover
import CFSG.Timmesfeld.ARS.CaseOALevi
import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimple
import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleSplit
import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleRankOne
import CFSG.HardMathSupport.Timmesfeld.LangTorus.GoodRankOne
import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcCtx
import CFSG.Blueprint.ChevalleyRootGroups
import CFSG.LieType.Chevalley.BruhatCellFactorization
import CFSG.LieType.Chevalley.CoordinateFieldFixedSubgroup
import CFSG.LieType.Chevalley.LangRootRankOne
import CFSG.LieType.Chevalley.RankOneGaussian
import CFSG.LieType.Chevalley.GraphFixedRankOneImage
import CFSG.LieType.HighestRoot.CentChevalley
import CFSG.LieType.AlgebraicGroups.ToralTwistSemilinearDatum
import CFSG.RankThree.Chevalley.SteinbergBIRootSL2Tools
import CFSG.RankThree.Chevalley.EvenPinnedRootSL2
import CFSG.LinearAlgebra.LinearGroups.Perfect
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwapLiftSplit
import CFSG.RankThree.PartOne.S13K.Row1At
import CFSG.CGT.PushingUpLit.BHS6.ThreeEightSL2
import CFSG.CGT.PushingUpLit.BHS.ThreeEight
import CFSG.CGT.PushingUpLit.BHS6.ThreeEightBT
import CFSG.RankThree.PartOne.KF.R10Final
import CFSG.RankThree.PartOne.KFOUT3.Cocycle
import CFSG.RankThree.PartOne.S12.Sec138Loc

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.LieCore
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Open (StatedLieTag)

private theorem rootGroup_SL2_closure_uSL (F : Type) [Field F] :
    (SpecialLinear.rootDatum 1 F).rootGroup (Pi.single (0 : Fin 1) (1 : ℤ)) =
      Subgroup.closure (Set.range (uSL : F → SL2 F)) := by
  rw [CFSG.Timmesfeld.ARS.CaseOA.rootGroup_SL2_single]
  unfold CFSG.Timmesfeld.upperUnipotent
  congr 1
  ext g
  exact ⟨fun ⟨t, ht⟩ => ⟨t, Subtype.ext (by rw [coe_uSL]; exact ht.symm)⟩,
    fun ⟨t, ht⟩ => ⟨t, by rw [← ht, coe_uSL]⟩⟩

private theorem rootGroup_SL2_closure_vSL (F : Type) [Field F] :
    (SpecialLinear.rootDatum 1 F).rootGroup (-Pi.single (0 : Fin 1) (1 : ℤ)) =
      Subgroup.closure (Set.range (vSL : F → SL2 F)) := by
  rw [CFSG.Timmesfeld.ARS.CaseOA.rootGroup_SL2_neg_single]
  unfold CFSG.Timmesfeld.lowerUnipotent
  congr 1
  ext g
  exact ⟨fun ⟨t, ht⟩ => ⟨t, Subtype.ext (by rw [coe_vSL]; exact ht.symm)⟩,
    fun ⟨t, ht⟩ => ⟨t, by rw [← ht, coe_vSL]⟩⟩

private theorem center_SL2_eq_bot {F : Type*} [Field F] [CharP F 2] :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro A hA
  rw [Subgroup.mem_bot]
  obtain ⟨r, hr2, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  have hr2' : r ^ 2 = 1 := by simpa using hr2
  have hr1 : r = 1 := by
    have hsq : (r - 1) ^ 2 = 0 := by
      have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
      calc (r - 1) ^ 2 = r ^ 2 - 2 * r + 1 := by ring
        _ = 1 - 2 * r + 1 := by rw [hr2']
        _ = 0 := by linear_combination (1 - r) * h2
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)
  apply Subtype.ext
  rw [← hrA, hr1]
  simp

private theorem sl2_map_injective {F L : Type*} [Field F] [Field L] {ι : F →+* L}
    (hι : Function.Injective ι) :
    Function.Injective (Matrix.SpecialLinearGroup.map ι :
      Matrix.SpecialLinearGroup (Fin 2) F → Matrix.SpecialLinearGroup (Fin 2) L) := by
  intro A B hAB
  apply Subtype.ext
  ext i j
  have h := congrArg (fun X : Matrix.SpecialLinearGroup (Fin 2) L =>
    (X : Matrix (Fin 2) (Fin 2) L) i j) hAB
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, Matrix.map_apply] at h
  exact hι h

private theorem step_conj_pinnedX
    {τ : Tag} {p₀ : ℕ} {S : LangSetup τ GGL p₀} {a : Fin τ.rank → GGLˣ}
    {i : KernelComponent (rootCharHom a)} {s : ℕ} {σ : GGL ≃+* GGL} {z : ModGL τ GGL}
    (hs1 : s = 1)
    (hz : ∀ g ∈ rootSpan τ GGL (componentRoots (rootCharHom a) i),
      iterHom S.D.step s (z * g * z⁻¹) = z * frobGL σ g * z⁻¹)
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ componentRoots (rootCharHom a) i) (c : GGL) :
    S.D.step (MulAut.conj z (pinnedX τ GGL γ c)) = MulAut.conj z (pinnedX τ GGL γ (σ c)) := by
  have hg : pinnedX τ GGL γ c ∈ rootSpan τ GGL (componentRoots (rootCharHom a) i) :=
    pinnedX_mem_rootSpan hγ c
  have h := hz _ hg
  rw [hs1, iterHom_succ, iterHom_zero, frobGL_pinnedX] at h
  exact h

private theorem map_conj_map_step
    {τ : Tag} {p₀ : ℕ}
    (S : LangSetup τ GGL p₀) {σ : GGL ≃+* GGL} {z : ModGL τ GGL} {γ : Fin τ.rank → ℤ}
    (hσ : Function.Surjective σ)
    (hstep : ∀ c : GGL, S.D.step (MulAut.conj z (pinnedX τ GGL γ c)) =
      MulAut.conj z (pinnedX τ GGL γ (σ c))) :
    ((rootSubgroup τ GGL γ).map (MulAut.conj z).toMonoidHom).map S.D.step =
      (rootSubgroup τ GGL γ).map (MulAut.conj z).toMonoidHom := by
  have h1 : (rootSubgroup τ GGL γ).map (MulAut.conj z).toMonoidHom =
      Subgroup.closure (Set.range fun c => MulAut.conj z (pinnedX τ GGL γ c)) := by
    rw [rootSubgroup, MonoidHom.map_closure, ← Set.range_comp]
    rfl
  have h2 : ((rootSubgroup τ GGL γ).map (MulAut.conj z).toMonoidHom).map S.D.step =
      Subgroup.closure (Set.range fun c => S.D.step (MulAut.conj z (pinnedX τ GGL γ c))) := by
    rw [h1, MonoidHom.map_closure, ← Set.range_comp]
    rfl
  have hEq : Set.range (fun c => MulAut.conj z (pinnedX τ GGL γ c)) =
      Set.range (fun c => S.D.step (MulAut.conj z (pinnedX τ GGL γ c))) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨c, rfl⟩ := hσ x
      exact ⟨c, hstep c⟩
    · rintro ⟨x, rfl⟩
      exact ⟨σ x, (hstep x).symm⟩
  rw [h2, h1, hEq]

private theorem image_rootGroup_eq {τ : Tag}
    {p₀ : ℕ}
    (S : LangSetup τ GGL p₀) {σ : GGL ≃+* GGL} {γ : Fin τ.rank → ℤ} {z : ModGL τ GGL}
    {F : Type} [Field F] (κ : F ≃+* ↥(fixSubfield σ))
    (δ : Fin 1 → ℤ) {e : F → SL2 F} {Φ : SL2 F →* ModGL τ GGL}
    (hgen : (SpecialLinear.rootDatum 1 F).rootGroup δ = Subgroup.closure (Set.range e))
    (hpin : ∀ c : F, Φ (e c) =
      MulAut.conj z (pinnedX τ GGL γ ((fixSubfield σ).subtype (κ c))))
    (hstep : ∀ c : GGL, S.D.step (MulAut.conj z (pinnedX τ GGL γ c)) =
      MulAut.conj z (pinnedX τ GGL γ (σ c))) :
    ((SpecialLinear.rootDatum 1 F).rootGroup δ).map Φ =
      (rootSubgroup τ GGL γ).map (MulAut.conj z).toMonoidHom ⊓
        S.D.step.eqLocus (MonoidHom.id _) := by
  have himg : Φ '' Set.range e =
      Set.range (fun c : F => MulAut.conj z (pinnedX τ GGL γ ((fixSubfield σ).subtype (κ c)))) := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext hpin)
  rw [hgen, MonoidHom.map_closure, himg]
  refine le_antisymm ?_ ?_
  · rw [Subgroup.closure_le]
    rintro y ⟨c, rfl⟩
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_map_of_mem _
      (Subgroup.subset_closure ⟨_, rfl⟩), ?_⟩
    change S.D.step (MulAut.conj z (pinnedX τ GGL γ ((fixSubfield σ).subtype (κ c)))) =
      MulAut.conj z (pinnedX τ GGL γ ((fixSubfield σ).subtype (κ c)))
    rw [hstep]
    rw [show σ ((fixSubfield σ).subtype (κ c)) = (fixSubfield σ).subtype (κ c) from
      (mem_fixSubfield σ).1 (κ c).2]
  · intro y hy
    obtain ⟨hyU, hyfix⟩ := Subgroup.mem_inf.1 hy
    obtain ⟨w, hw, hwy⟩ := Subgroup.mem_map.1 hyU
    obtain ⟨c, rfl⟩ := (mem_rootSubgroup).1 hw
    have hc : σ c = c := by
      have h1 : S.D.step (MulAut.conj z (pinnedX τ GGL γ c)) =
          MulAut.conj z (pinnedX τ GGL γ c) := hwy ▸ hyfix
      rw [hstep] at h1
      exact pinnedX_injective τ GGL γ ((MulAut.conj z).injective h1)
    refine Subgroup.subset_closure ⟨κ.symm ⟨c, (mem_fixSubfield σ).2 hc⟩, ?_⟩
    change MulAut.conj z (pinnedX τ GGL γ ((fixSubfield σ).subtype
      (κ (κ.symm ⟨c, (mem_fixSubfield σ).2 hc⟩)))) = y
    have hsub : (fixSubfield σ).subtype (κ (κ.symm ⟨c, (mem_fixSubfield σ).2 hc⟩)) = c := by
      simp
    rw [hsub]
    exact hwy

private theorem map_mem_rationalSpan
    {τ : Tag} {p₀ : ℕ} {S : LangSetup τ GGL p₀} {a : Fin τ.rank → GGLˣ}
    {i : KernelComponent (rootCharHom a)} {s : ℕ} {β : Fin τ.rank → ℤ}
    {σ : GGL ≃+* GGL} {z : ModGL τ GGL}
    (hβ : IsRoot τ β) (hΨ : componentRoots (rootCharHom a) i = {β, -β})
    (hs1 : s = 1)
    (hzZ : z ∈ torusGroup τ GGL ⊔ rootSpan τ GGL (kernelRoots (rootCharHom a)))
    (hnorm : ∀ j : KernelComponent (rootCharHom a), ∀ g : ModGL τ GGL,
      g ∈ rootSpan τ GGL (componentRoots (rootCharHom a) j) ↔
        z * g * z⁻¹ ∈ rootSpan τ GGL (componentRoots (rootCharHom a) j))
    (hz : ∀ g ∈ rootSpan τ GGL (componentRoots (rootCharHom a) i),
      iterHom S.D.step s (z * g * z⁻¹) = z * frobGL σ g * z⁻¹)
    {F : Type} [Field F] (ι : F →+* GGL) (hιfix : ∀ c : F, σ (ι c) = ι c)
    (hσmap : ∀ A : Matrix.SpecialLinearGroup (Fin 2) F,
      Matrix.SpecialLinearGroup.map σ.toRingHom (Matrix.SpecialLinearGroup.map ι A) =
        Matrix.SpecialLinearGroup.map ι A)
    (hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F))
    (B : Matrix.SpecialLinearGroup (Fin 2) F) :
    ((MulAut.conj z).toMonoidHom.comp ((rootSL2 τ GGL β).comp
        (Matrix.SpecialLinearGroup.map ι))) B ∈
      rationalSpan S.ρ S.Γ (rootCharHom a) i := by
  set Φ : Matrix.SpecialLinearGroup (Fin 2) F →* ModGL τ GGL :=
    (MulAut.conj z).toMonoidHom.comp ((rootSL2 τ GGL β).comp
      (Matrix.SpecialLinearGroup.map ι))
  have hg : ∀ B : Matrix.SpecialLinearGroup (Fin 2) F,
      rootSL2 τ GGL β (Matrix.SpecialLinearGroup.map ι B) ∈
        rootSpan τ GGL (componentRoots (rootCharHom a) i) := by
    intro B
    rw [hΨ, CFSG.LieType.HighestRoot.rootSpan_pair_eq,
      ← CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot hβ]
    exact ⟨Matrix.SpecialLinearGroup.map ι B, rfl⟩
  have hleadj : (rootSL2 τ GGL β).range ≤ adjointGroup τ GGL := by
    rw [CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot hβ]
    exact sup_le (rootSubgroup_le_adjointGroup _) (rootSubgroup_le_adjointGroup _)
  have hmodel : ∀ B : Matrix.SpecialLinearGroup (Fin 2) F,
      Φ B ∈ S.D.model := by
    intro B
    rw [LangDatum.mem_model]
    refine ⟨?_, ?_⟩
    · have hzadj : z ∈ adjointGroup τ GGL :=
        torus_sup_rootSpan_le_adjointGroup (kernelRoots (rootCharHom a)) hzZ
      exact (adjointGroup τ GGL).mul_mem ((adjointGroup τ GGL).mul_mem hzadj
        (hleadj ⟨Matrix.SpecialLinearGroup.map ι B, rfl⟩)) ((adjointGroup τ GGL).inv_mem hzadj)
    · have h1 := hz _ (hg B)
      rw [hs1, iterHom_succ, iterHom_zero, frobGL_rootSL2 σ hβ, hσmap B] at h1
      exact h1
  change Φ B ∈ rootSpan τ GGL (rationalRoots S.ρ (rootCharHom a) i) ⊓ S.Γ
  refine ⟨?_, ?_⟩
  · refine rootSpan_mono (S := componentRoots (rootCharHom a) i)
      (T := rationalRoots S.ρ (rootCharHom a) i)
      (fun γ hγ => ⟨0, γ, hγ, rfl⟩) ?_
    have hΦval : Φ B = z * rootSL2 τ GGL β (Matrix.SpecialLinearGroup.map ι B) * z⁻¹ := by
      dsimp only [Φ]
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hΦval]
    exact (hnorm i _).1 (hg B)
  · exact map_mem_commutator_of_perfect hperf Φ S.D.model hmodel B

private theorem range_le_rationalComponent
    {τ : Tag} {p₀ : ℕ} {S : LangSetup τ GGL p₀} {a : Fin τ.rank → GGLˣ}
    {i : KernelComponent (rootCharHom a)} {s : ℕ} {β : Fin τ.rank → ℤ}
    {σ : GGL ≃+* GGL} {z : ModGL τ GGL}
    (hβ : IsRoot τ β) (hΨ : componentRoots (rootCharHom a) i = {β, -β})
    (hs1 : s = 1)
    (hzZ : z ∈ torusGroup τ GGL ⊔ rootSpan τ GGL (kernelRoots (rootCharHom a)))
    (hnorm : ∀ j : KernelComponent (rootCharHom a), ∀ g : ModGL τ GGL,
      g ∈ rootSpan τ GGL (componentRoots (rootCharHom a) j) ↔
        z * g * z⁻¹ ∈ rootSpan τ GGL (componentRoots (rootCharHom a) j))
    (hz : ∀ g ∈ rootSpan τ GGL (componentRoots (rootCharHom a) i),
      iterHom S.D.step s (z * g * z⁻¹) = z * frobGL σ g * z⁻¹)
    {F : Type} [Field F] (ι : F →+* GGL) (hιfix : ∀ c : F, σ (ι c) = ι c)
    (hσmap : ∀ A : Matrix.SpecialLinearGroup (Fin 2) F,
      Matrix.SpecialLinearGroup.map σ.toRingHom (Matrix.SpecialLinearGroup.map ι A) =
        Matrix.SpecialLinearGroup.map ι A)
    (hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F)) :
    ((MulAut.conj z).toMonoidHom.comp ((rootSL2 τ GGL β).comp
        (Matrix.SpecialLinearGroup.map ι))).range ≤
      rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  rintro x ⟨A, rfl⟩
  exact map_mem_commutator_of_perfect hperf _ _
    (fun B => map_mem_rationalSpan hβ hΨ hs1 hzZ hnorm hz ι hιfix hσmap hperf B) A

section CoverPairA1

private theorem rckADEModel_PSL_two
    (g : ℕ) (hg : 2 ≤ g) :
    RCKADEModel (ggU .PSL 2 g) g := by
  exact Or.inl ⟨.PSL, 2, Or.inl rfl,
    CFSG.RankThree.PartOne.S13K.admissible_psl_two hg, rfl⟩

private theorem nonempty_ringEquiv_fixSubfield
    {τ : Tag} {p₀ : ℕ} {S : LangSetup τ GGL p₀} {s : ℕ}
    {σ : GGL ≃+* GGL} {h : ℕ}
    (hs0 : 0 < s) (hhs : 2 ≤ h * s)
    (hσ : ∀ c, σ c = c ^ (S.D.q ^ s)) (hq : S.D.q = 2 ^ h) :
    Nonempty (GaloisField 2 (h * s) ≃+* ↥(fixSubfield σ)) := by
  classical
  obtain ⟨hKfin, hKcard⟩ := exists_fixSubfield_fintype S hs0 hσ
  haveI : Finite ↥(fixSubfield σ) := hKfin
  haveI : Fintype ↥(fixSubfield σ) := Fintype.ofFinite _
  haveI : Fintype (GaloisField 2 (h * s)) := Fintype.ofFinite _
  have hGcard : Fintype.card (GaloisField 2 (h * s)) = 2 ^ (h * s) := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 (h * s) (by omega)]
  have hFcard : Fintype.card ↥(fixSubfield σ) = 2 ^ (h * s) := by
    rw [← Nat.card_eq_fintype_card, hKcard, hq, ← pow_mul]
  exact ⟨FiniteField.ringEquivOfCardEq (by rw [hGcard, hFcard])⟩

private theorem range_eq_of_card
    {τ : Tag} {p₀ : ℕ} {S : LangSetup τ GGL p₀} {a : Fin τ.rank → GGLˣ}
    {i : KernelComponent (rootCharHom a)} {s : ℕ} {h : ℕ}
    {Φ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (h * s)) →* ModGL τ GGL}
    {φ₀ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (h * s)) →* ModGL τ GGL}
    (hle : Φ.range ≤ rationalComponent S.ρ S.Γ (rootCharHom a) i)
    (hinj : Function.Injective Φ)
    (hφr : φ₀.range = rationalComponent S.ρ S.Γ (rootCharHom a) i)
    (hφk : φ₀.ker ≤ Subgroup.center
      (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (h * s)))) :
    Φ.range = rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  have hRle : rationalComponent S.ρ S.Γ (rootCharHom a) i ≤ S.D.model :=
    (Subgroup.commutator_le_self _).trans
      (inf_le_right.trans (Subgroup.commutator_le_self _))
  haveI : Finite ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
    haveI : Finite ↥S.D.model := S.finite
    exact Finite.of_injective (Subgroup.inclusion hRle) (Subgroup.inclusion_injective hRle)
  have hinj₀ : Function.Injective φ₀ := by
    rw [← MonoidHom.ker_eq_bot_iff φ₀]
    exact le_bot_iff.1 (hφk.trans (le_of_eq (center_SL2_eq_bot (F := GaloisField 2 (h * s)))))
  have hcardR : Nat.card ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) =
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (h * s))) := by
    rw [← hφr]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj₀).toEquiv).symm
  have hcardΦ : Nat.card ↥Φ.range =
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (h * s))) :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcardR, hcardΦ])

private theorem coverData_one
    {τ : Tag} {p₀ : ℕ} {S : LangSetup τ GGL p₀} {a : Fin τ.rank → GGLˣ}
    {i : KernelComponent (rootCharHom a)} {s : ℕ} {β : Fin τ.rank → ℤ}
    {σ : GGL ≃+* GGL} {z : ModGL τ GGL} {h : ℕ}
    (hβ : IsRoot τ β) (hΨ : componentRoots (rootCharHom a) i = {β, -β})
    (hs1 : s = 1) (hs0 : 0 < s)
    (hσ : ∀ c, σ c = c ^ (S.D.q ^ s)) (hq : S.D.q = 2 ^ h)
    (hhs : 2 ≤ h * s)
    (hzZ : z ∈ torusGroup τ GGL ⊔ rootSpan τ GGL (kernelRoots (rootCharHom a)))
    (hnorm : ∀ j : KernelComponent (rootCharHom a), ∀ g : ModGL τ GGL,
      g ∈ rootSpan τ GGL (componentRoots (rootCharHom a) j) ↔
        z * g * z⁻¹ ∈ rootSpan τ GGL (componentRoots (rootCharHom a) j))
    (hz : ∀ g ∈ rootSpan τ GGL (componentRoots (rootCharHom a) i),
      iterHom S.D.step s (z * g * z⁻¹) = z * frobGL σ g * z⁻¹)
    (hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (h * s))))
    {φ₀ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (h * s)) →* ModGL τ GGL}
    (hφr : φ₀.range = rationalComponent S.ρ S.Γ (rootCharHom a) i)
    (hφk : φ₀.ker ≤ Subgroup.center
      (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (h * s)))) :
    ∃ (κ : GaloisField 2 (h * s) ≃+* ↥(fixSubfield σ))
      (Φ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (h * s)) →* ModGL τ GGL),
      Φ = (MulAut.conj z).toMonoidHom.comp ((rootSL2 τ GGL β).comp
            (Matrix.SpecialLinearGroup.map ((fixSubfield σ).subtype.comp κ.toRingHom))) ∧
      Φ.range = rationalComponent S.ρ S.Γ (rootCharHom a) i ∧
      Φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (h * s))) ∧
      Function.Injective Φ := by
  classical
  obtain ⟨κ⟩ := nonempty_ringEquiv_fixSubfield (s := s) (h := h) hs0 hhs hσ hq
  let ι : GaloisField 2 (h * s) →+* GGL := (fixSubfield σ).subtype.comp κ.toRingHom
  let Φ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (h * s)) →* ModGL τ GGL :=
    (MulAut.conj z).toMonoidHom.comp ((rootSL2 τ GGL β).comp
      (Matrix.SpecialLinearGroup.map ι))
  have hιfix : ∀ c : GaloisField 2 (h * s), σ (ι c) = ι c :=
    fun c => (mem_fixSubfield σ).1 (κ c).2
  have hσmap : ∀ A : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (h * s)),
      Matrix.SpecialLinearGroup.map σ.toRingHom (Matrix.SpecialLinearGroup.map ι A) =
        Matrix.SpecialLinearGroup.map ι A := by
    intro A
    apply Subtype.ext
    ext i j
    simpa using hιfix ((A : Matrix (Fin 2) (Fin 2) (GaloisField 2 (h * s))) i j)
  have hinj : Function.Injective Φ :=
    (MulAut.conj z).injective.comp ((CFSG.RankThree.Chevalley.rootSL2_injective_of_field β).comp
      (sl2_map_injective ((fixSubfield σ).subtype_injective.comp κ.injective)))
  have hΦk : Φ.ker ≤ Subgroup.center
      (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (h * s))) := by
    rw [(MonoidHom.ker_eq_bot_iff Φ).2 hinj]
    exact bot_le
  have hle : Φ.range ≤ rationalComponent S.ρ S.Γ (rootCharHom a) i :=
    range_le_rationalComponent hβ hΨ hs1 hzZ hnorm hz ι hιfix hσmap hperf
  have hΦr : Φ.range = rationalComponent S.ρ S.Γ (rootCharHom a) i :=
    range_eq_of_card hle hinj hφr hφk
  exact ⟨κ, Φ, rfl, hΦr, hΦk, hinj⟩

private theorem stable_beta
    {τ : Tag} {p₀ : ℕ} (S : LangSetup τ GGL p₀) {σ : GGL ≃+* GGL} {z : ModGL τ GGL}
    {β : Fin τ.rank → ℤ}
    (hσ : Function.Surjective σ)
    (hst : ∀ c : GGL, S.D.step (MulAut.conj z (pinnedX τ GGL β c)) =
      MulAut.conj z (pinnedX τ GGL β (σ c))) :
    ((rootSubgroup τ GGL β).map (MulAut.conj z).toMonoidHom).map S.D.step =
      (rootSubgroup τ GGL β).map (MulAut.conj z).toMonoidHom :=
  map_conj_map_step S hσ hst

private theorem stable_neg_beta
    {τ : Tag} {p₀ : ℕ} (S : LangSetup τ GGL p₀) {σ : GGL ≃+* GGL} {z : ModGL τ GGL}
    {β : Fin τ.rank → ℤ}
    (hσ : Function.Surjective σ)
    (hst : ∀ c : GGL, S.D.step (MulAut.conj z (pinnedX τ GGL (-β) c)) =
      MulAut.conj z (pinnedX τ GGL (-β) (σ c))) :
    ((rootSubgroup τ GGL (-β)).map (MulAut.conj z).toMonoidHom).map S.D.step =
      (rootSubgroup τ GGL (-β)).map (MulAut.conj z).toMonoidHom :=
  map_conj_map_step S hσ hst

private theorem imagePSL_pos
    {τ : Tag} {p₀ : ℕ} {S : LangSetup τ GGL p₀} {s : ℕ} {β : Fin τ.rank → ℤ}
    {σ : GGL ≃+* GGL} {z : ModGL τ GGL} {h : ℕ}
    (κ : GaloisField 2 (h * s) ≃+* ↥(fixSubfield σ))
    (Φ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (h * s)) →* ModGL τ GGL)
    (hpin : ∀ c : GaloisField 2 (h * s),
      Φ (uSL c) = MulAut.conj z (pinnedX τ GGL β ((fixSubfield σ).subtype (κ c))))
    (hst : ∀ c : GGL, S.D.step (MulAut.conj z (pinnedX τ GGL β c)) =
      MulAut.conj z (pinnedX τ GGL β (σ c))) :
    ((SpecialLinear.rootDatum 1 (GaloisField 2 (h * s))).rootGroup
        (Pi.single (0 : Fin 1) (1 : ℤ))).map Φ =
      (rootSubgroup τ GGL β).map (MulAut.conj z).toMonoidHom ⊓
        S.D.step.eqLocus (MonoidHom.id _) := by
  exact image_rootGroup_eq S κ (Pi.single (0 : Fin 1) (1 : ℤ))
    (e := (uSL : GaloisField 2 (h * s) → SL2 (GaloisField 2 (h * s)))) (Φ := Φ)
    (rootGroup_SL2_closure_uSL _) hpin hst

private theorem imagePSL_neg
    {τ : Tag} {p₀ : ℕ} {S : LangSetup τ GGL p₀} {s : ℕ} {β : Fin τ.rank → ℤ}
    {σ : GGL ≃+* GGL} {z : ModGL τ GGL} {h : ℕ}
    (κ : GaloisField 2 (h * s) ≃+* ↥(fixSubfield σ))
    (Φ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (h * s)) →* ModGL τ GGL)
    (hpin : ∀ c : GaloisField 2 (h * s),
      Φ (vSL c) = MulAut.conj z (pinnedX τ GGL (-β) ((fixSubfield σ).subtype (κ c))))
    (hst : ∀ c : GGL, S.D.step (MulAut.conj z (pinnedX τ GGL (-β) c)) =
      MulAut.conj z (pinnedX τ GGL (-β) (σ c))) :
    ((SpecialLinear.rootDatum 1 (GaloisField 2 (h * s))).rootGroup
        (-Pi.single (0 : Fin 1) (1 : ℤ))).map Φ =
      (rootSubgroup τ GGL (-β)).map (MulAut.conj z).toMonoidHom ⊓
        S.D.step.eqLocus (MonoidHom.id _) := by
  let δ : Fin 1 → ℤ := -Pi.single (0 : Fin 1) (1 : ℤ)
  have hgen : (SpecialLinear.rootDatum 1 (GaloisField 2 (h * s))).rootGroup δ =
      Subgroup.closure (Set.range (vSL : GaloisField 2 (h * s) → SL2 (GaloisField 2 (h * s)))) :=
    rootGroup_SL2_closure_vSL _
  exact image_rootGroup_eq S κ δ
    (e := (vSL : GaloisField 2 (h * s) → SL2 (GaloisField 2 (h * s)))) (Φ := Φ) hgen hpin hst

private theorem pairClause_beta
    {τ : Tag} {p₀ : ℕ} {S : LangSetup τ GGL p₀} {a : Fin τ.rank → GGLˣ}
    {i : KernelComponent (rootCharHom a)} {s : ℕ} {β : Fin τ.rank → ℤ}
    {σ : GGL ≃+* GGL} {z : ModGL τ GGL} {h : ℕ}
    (hβmem : β ∈ componentRoots (rootCharHom a) i)
    (hnegβmem : -β ∈ componentRoots (rootCharHom a) i)
    (hzZ : z ∈ torusGroup τ GGL ⊔ rootSpan τ GGL (kernelRoots (rootCharHom a)))
    (κ : GaloisField 2 (h * s) ≃+* ↥(fixSubfield σ))
    (Φ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (h * s)) →* ModGL τ GGL)
    (hstβ : ∀ c : GGL, S.D.step (MulAut.conj z (pinnedX τ GGL β c)) =
      MulAut.conj z (pinnedX τ GGL β (σ c)))
    (hstnβ : ∀ c : GGL, S.D.step (MulAut.conj z (pinnedX τ GGL (-β) c)) =
      MulAut.conj z (pinnedX τ GGL (-β) (σ c)))
    (hpinβ : ∀ c : GaloisField 2 (h * s),
      Φ (uSL c) = MulAut.conj z (pinnedX τ GGL β ((fixSubfield σ).subtype (κ c))))
    (hpinnβ : ∀ c : GaloisField 2 (h * s),
      Φ (vSL c) = MulAut.conj z (pinnedX τ GGL (-β) ((fixSubfield σ).subtype (κ c)))) :
    ∃ γ ∈ componentRoots (rootCharHom a) i,
      ∃ z' ∈ torusGroup τ GGL ⊔ rootSpan τ GGL (kernelRoots (rootCharHom a)),
      ((rootSubgroup τ GGL γ).map (MulAut.conj z').toMonoidHom).map S.D.step =
          (rootSubgroup τ GGL γ).map (MulAut.conj z').toMonoidHom ∧
        ((rootSubgroup τ GGL (-γ)).map (MulAut.conj z').toMonoidHom).map S.D.step =
          (rootSubgroup τ GGL (-γ)).map (MulAut.conj z').toMonoidHom ∧
        ((SpecialLinear.rootDatum 1 (GaloisField 2 (h * s))).rootGroup
            (Pi.single (0 : Fin 1) (1 : ℤ))).map Φ =
          (rootSubgroup τ GGL γ).map (MulAut.conj z').toMonoidHom ⊓
            S.D.step.eqLocus (MonoidHom.id _) ∧
        ((SpecialLinear.rootDatum 1 (GaloisField 2 (h * s))).rootGroup
            (-Pi.single (0 : Fin 1) (1 : ℤ))).map Φ =
          (rootSubgroup τ GGL (-γ)).map (MulAut.conj z').toMonoidHom ⊓
            S.D.step.eqLocus (MonoidHom.id _) := by
  exact ⟨β, hβmem, z, hzZ,
    stable_beta S σ.surjective hstβ, stable_neg_beta S σ.surjective hstnβ,
    imagePSL_pos (h := h) κ Φ hpinβ hstβ, imagePSL_neg (h := h) κ Φ hpinnβ hstnβ⟩

private theorem pairClause_neg_beta
    {τ : Tag} {p₀ : ℕ} {S : LangSetup τ GGL p₀} {a : Fin τ.rank → GGLˣ}
    {i : KernelComponent (rootCharHom a)} {s : ℕ} {β : Fin τ.rank → ℤ}
    {σ : GGL ≃+* GGL} {z : ModGL τ GGL} {h : ℕ}
    (hβmem : β ∈ componentRoots (rootCharHom a) i)
    (hnegβmem : -β ∈ componentRoots (rootCharHom a) i)
    (hzZ : z ∈ torusGroup τ GGL ⊔ rootSpan τ GGL (kernelRoots (rootCharHom a)))
    (κ : GaloisField 2 (h * s) ≃+* ↥(fixSubfield σ))
    (Φ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (h * s)) →* ModGL τ GGL)
    (hstβ : ∀ c : GGL, S.D.step (MulAut.conj z (pinnedX τ GGL β c)) =
      MulAut.conj z (pinnedX τ GGL β (σ c)))
    (hstnβ : ∀ c : GGL, S.D.step (MulAut.conj z (pinnedX τ GGL (-β) c)) =
      MulAut.conj z (pinnedX τ GGL (-β) (σ c)))
    (hpinβ : ∀ c : GaloisField 2 (h * s),
      Φ (uSL c) = MulAut.conj z (pinnedX τ GGL β ((fixSubfield σ).subtype (κ c))))
    (hpinnβ : ∀ c : GaloisField 2 (h * s),
      Φ (vSL c) = MulAut.conj z (pinnedX τ GGL (-β) ((fixSubfield σ).subtype (κ c)))) :
    ∃ γ ∈ componentRoots (rootCharHom a) i,
      ∃ z' ∈ torusGroup τ GGL ⊔ rootSpan τ GGL (kernelRoots (rootCharHom a)),
      ((rootSubgroup τ GGL γ).map (MulAut.conj z').toMonoidHom).map S.D.step =
          (rootSubgroup τ GGL γ).map (MulAut.conj z').toMonoidHom ∧
        ((rootSubgroup τ GGL (-γ)).map (MulAut.conj z').toMonoidHom).map S.D.step =
          (rootSubgroup τ GGL (-γ)).map (MulAut.conj z').toMonoidHom ∧
        ((SpecialLinear.rootDatum 1 (GaloisField 2 (h * s))).rootGroup
            (-Pi.single (0 : Fin 1) (1 : ℤ))).map Φ =
          (rootSubgroup τ GGL γ).map (MulAut.conj z').toMonoidHom ⊓
            S.D.step.eqLocus (MonoidHom.id _) ∧
        ((SpecialLinear.rootDatum 1 (GaloisField 2 (h * s))).rootGroup
            ((- -Pi.single (0 : Fin 1) (1 : ℤ) : Fin 1 → ℤ))).map Φ =
          (rootSubgroup τ GGL (-γ)).map (MulAut.conj z').toMonoidHom ⊓
            S.D.step.eqLocus (MonoidHom.id _) := by
  refine ⟨-β, hnegβmem, z, hzZ, ?_, ?_, ?_, ?_⟩
  · exact stable_neg_beta S σ.surjective hstnβ
  · rw [neg_neg]
    exact stable_beta S σ.surjective hstβ
  · exact imagePSL_neg κ Φ hpinnβ hstnβ
  · rw [show (- -Pi.single (0 : Fin 1) (1 : ℤ) : Fin 1 → ℤ) =
      Pi.single (0 : Fin 1) (1 : ℤ) by simp]
    rw [show - -β = β by simp]
    exact imagePSL_pos κ Φ hpinβ hstβ

private theorem pairClause_one
    {τ : Tag} {p₀ : ℕ} {S : LangSetup τ GGL p₀} {a : Fin τ.rank → GGLˣ}
    {i : KernelComponent (rootCharHom a)} {s : ℕ} {β : Fin τ.rank → ℤ}
    {σ : GGL ≃+* GGL} {z : ModGL τ GGL} {h : ℕ}
    (hβ : IsRoot τ β)
    (hβmem : β ∈ componentRoots (rootCharHom a) i)
    (hnegβmem : -β ∈ componentRoots (rootCharHom a) i)
    (hs1 : s = 1)
    (hzZ : z ∈ torusGroup τ GGL ⊔ rootSpan τ GGL (kernelRoots (rootCharHom a)))
    (hz : ∀ g ∈ rootSpan τ GGL (componentRoots (rootCharHom a) i),
      iterHom S.D.step s (z * g * z⁻¹) = z * frobGL σ g * z⁻¹)
    (κ : GaloisField 2 (h * s) ≃+* ↥(fixSubfield σ))
    (Φ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (h * s)) →* ModGL τ GGL)
    (hΦ : Φ = (MulAut.conj z).toMonoidHom.comp ((rootSL2 τ GGL β).comp
            (Matrix.SpecialLinearGroup.map ((fixSubfield σ).subtype.comp κ.toRingHom)))) :
    ∀ β' ∈ (ggU .PSL 2 (h * s)).D.roots, GGLongRoot (ggU .PSL 2 (h * s)).D β' →
      ∃ γ ∈ componentRoots (rootCharHom a) i,
      ∃ z' ∈ torusGroup τ GGL ⊔ rootSpan τ GGL (kernelRoots (rootCharHom a)),
        ((rootSubgroup τ GGL γ).map (MulAut.conj z').toMonoidHom).map S.D.step =
            (rootSubgroup τ GGL γ).map (MulAut.conj z').toMonoidHom ∧
          ((rootSubgroup τ GGL (-γ)).map (MulAut.conj z').toMonoidHom).map S.D.step =
            (rootSubgroup τ GGL (-γ)).map (MulAut.conj z').toMonoidHom ∧
          ((ggU .PSL 2 (h * s)).D.rootGroup β').map Φ =
            (rootSubgroup τ GGL γ).map (MulAut.conj z').toMonoidHom ⊓
              S.D.step.eqLocus (MonoidHom.id _) ∧
          ((ggU .PSL 2 (h * s)).D.rootGroup (-β')).map Φ =
            (rootSubgroup τ GGL (-γ)).map (MulAut.conj z').toMonoidHom ⊓
              S.D.step.eqLocus (MonoidHom.id _) := by
  intro β' hβ' _hlong
  have hβ'' : β' ∈ (SpecialLinear.rootDatum 1 (GaloisField 2 (h * s))).roots := hβ'
  have hstβ : ∀ c : GGL, S.D.step (MulAut.conj z (pinnedX τ GGL β c)) =
      MulAut.conj z (pinnedX τ GGL β (σ c)) :=
    fun c => step_conj_pinnedX hs1 hz hβmem c
  have hstnβ : ∀ c : GGL, S.D.step (MulAut.conj z (pinnedX τ GGL (-β) c)) =
      MulAut.conj z (pinnedX τ GGL (-β) (σ c)) :=
    fun c => step_conj_pinnedX hs1 hz hnegβmem c
  have hpinβ : ∀ c : GaloisField 2 (h * s),
      Φ (uSL c) = MulAut.conj z (pinnedX τ GGL β ((fixSubfield σ).subtype (κ c))) := by
    intro c
    rw [hΦ]
    simp only [MonoidHom.comp_apply]
    rw [map_uSL, CFSG.RankThree.Chevalley.rootSL2_uSL_of_charTwo hβ]
    rfl
  have hpinnβ : ∀ c : GaloisField 2 (h * s),
      Φ (vSL c) = MulAut.conj z (pinnedX τ GGL (-β) ((fixSubfield σ).subtype (κ c))) := by
    intro c
    rw [hΦ]
    simp only [MonoidHom.comp_apply]
    rw [map_vSL, CFSG.RankThree.Chevalley.rootSL2_vSL_of_charTwo hβ]
    rfl
  rcases CFSG.Timmesfeld.ARS.CaseOA.eq_or_eq_neg_of_mem_roots_SL2
    (GaloisField 2 (h * s)) hβ'' with h | h
  · rw [h]
    exact pairClause_beta hβmem hnegβmem hzZ κ Φ hstβ hstnβ hpinβ hpinnβ
  · rw [h]
    exact pairClause_neg_beta hβmem hnegβmem hzZ κ Φ hstβ hstnβ hpinβ hpinnβ

private theorem frameCoverPair_ne_one
    {τ : Tag} {p₀ : ℕ} {S : LangSetup τ GGL p₀} {a : Fin τ.rank → GGLˣ}
    {i : KernelComponent (rootCharHom a)} {s : ℕ} {h : ℕ}
    (hhs : 2 ≤ h * s)
    (hs : s = componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
    (hne : s ≠ 1)
    (hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (h * s))))
    {φ₀ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (h * s)) →* ModGL τ GGL}
    (hφr : φ₀.range = rationalComponent S.ρ S.Γ (rootCharHom a) i)
    (hφk : φ₀.ker ≤ Subgroup.center
      (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (h * s)))) :
    RCKFrameCoverPair S a i h (fun M g => M = ggU .PSL 2 g) := by
  let T := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)
  have hsT : s = T := hs
  subst hsT
  refine ⟨ggU .PSL 2 (h * T), φ₀, rfl, rckADEModel_PSL_two (h * T) hhs, hφr, hφk,
    ?_, hperf, ?_, ?_⟩
  · show Finite (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (h * T)))
    infer_instance
  · exact CFSG.SeitzReduction.LinearPilot.oddCentralSplit_specialLinearGroup (m := 1)
      (F := GaloisField 2 (h * T))
  · intro hs1'
    exact absurd hs1' hne

end CoverPairA1

theorem rckPairA1_holds :
    RCKPairA1 := by
  intro τ p₀ S a hT p hp hp2 hap i h hq h1 hqs
  classical
  obtain ⟨β, hβ, hΨ⟩ := rckA1_componentRoots_eq_pair i h1
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  haveI : NeZero s := ⟨hs0.ne'⟩
  have hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[s]) := by
    have hs' := hs
    rw [hΨ] at hs' ⊢
    exact rckA1_twistInner_pair hβ hs' (rho_iterate_neg S s β)
  obtain ⟨σ, z, hσ, hzZ, hnorm, hz⟩ :=
    CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.exists_untwistT_Z S hT i hs0 hinner
  obtain ⟨hhs, φ₀, hφr₀, hφk₀⟩ := rckA1_exists_cover S hT i hΨ hs hmin σ hσ hnorm hz hq hqs
  have hperfSL : Group.IsPerfect
      (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (h * s))) :=
    CFSG.CGT.PushingUpLit.BHS6.isPerfect_sl2_galoisField hhs
  have hβmem : β ∈ componentRoots (rootCharHom a) i := by
    rw [hΨ]
    exact Set.mem_insert β ({-β} : Set (Fin τ.rank → ℤ))
  have hnegβmem : -β ∈ componentRoots (rootCharHom a) i := by
    rw [hΨ]
    exact Set.mem_insert_of_mem β (Set.mem_singleton_iff.2 rfl)
  by_cases hs1 : s = 1
  · obtain ⟨κ, Φ, hΦdef, hΦr, hΦk, -⟩ :=
      coverData_one hβ hΨ hs1 hs0 hσ hq hhs hzZ hnorm hz hperfSL hφr₀ hφk₀
    refine ⟨ggU .PSL 2 (h * s), Φ, rfl, rckADEModel_PSL_two (h * s) hhs, hΦr, hΦk,
      ?_, hperfSL, ?_, ?_⟩
    · show Finite (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (h * s)))
      infer_instance
    · exact CFSG.SeitzReduction.LinearPilot.oddCentralSplit_specialLinearGroup (m := 1)
        (F := GaloisField 2 (h * s))
    · intro _
      exact pairClause_one hβ hβmem hnegβmem hs1 hzZ hz κ Φ hΦdef
  · exact frameCoverPair_ne_one hhs hsdef hs1 hperfSL hφr₀ hφk₀

end CFSG.StandardType.RCKRP
