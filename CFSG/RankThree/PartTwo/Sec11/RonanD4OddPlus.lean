module

public import CFSG.RankThree.PartTwo.Sec11.RonanD4OddKill
public import CFSG.RankThree.PartTwo.Sec11.RonanD4OddHeis
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriA2Split
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriA2RecStruct

public section

namespace CFSG.RankThree.PartTwo.Sec11.RonanD4Odd

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open scoped MatrixGroups

set_option linter.unusedSectionVars false


theorem not_hasType424_fixSub_a2Plus {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hq : (p ^ f) % 3 = 1) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3)
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (p ^ f)) {d : Kˣ}
    (hd : Units.map σ.toRingHom.toMonoidHom d = d) (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1)
    {s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hs : (s : ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag ![1, 1, d, 1]) :
    ¬ KS11Lie2Proof.HasType424
      ↥(CFSG.RankThree.PartTwo.Sec4.autFix
        (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ)) := by
  classical
  haveI : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hA : A2Std σ d (p ^ f) := a2Std_of_class hp hp2 hf hq hK hσ hd hd3 hd1
  have hφ := a2_hφ_of_class (σ := σ) (d := d) hs
  obtain ⟨ρ, hρ, hcard, -⟩ := TriA2.exists_hom_fixSub hA.toCore
    (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ) hφ
  obtain ⟨hker, hN, hsolv⟩ := sl3_hom_structure ρ hρ hcard
  haveI := hN
  haveI : Fintype (CFSG.LieType.Steinberg.TwistedD4.fixedField σ.toRingHom) :=
    Fintype.ofFinite _
  have hquasi' : CFSG.IsQuasisimple
      SL(3, CFSG.LieType.Steinberg.TwistedD4.fixedField σ.toRingHom) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple 3 _
      (by norm_num) (Or.inl (by norm_num)) (Or.inl (by norm_num))
  have hkR : ρ.rangeRestrict.ker ≤
      Subgroup.center SL(3, CFSG.LieType.Steinberg.TwistedD4.fixedField σ.toRingHom) := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hker
  have hqs : CFSG.IsQuasisimple ↥ρ.range :=
    CFSG.LocalCores.isQuasisimple_of_surjective hquasi' ρ.rangeRestrict
      ρ.rangeRestrict_surjective hkR
  have hdK : σ.toRingHom (d : K) = d := congrArg Units.val hd
  let ω : CFSG.LieType.Steinberg.TwistedD4.fixedField σ.toRingHom := ⟨(d : K), hdK⟩
  have hω3 : ω ^ 3 = 1 := by
    apply Subtype.ext
    have h := congrArg Units.val hd3
    rw [Units.val_pow_eq_pow_val, Units.val_one] at h
    exact h
  have hω1 : ω ≠ 1 := by
    intro h
    apply hd1
    apply Units.ext
    have := congrArg Subtype.val h
    simpa [ω] using this
  obtain ⟨hx1, hx3, hy3, hcx, hcy, hyx⟩ := heis_of_hom ω hω3 hω1 ρ hker
  have hmem : ∀ z, ρ z ∈ ρ.range := fun z => ⟨z, rfl⟩
  have hfix : ¬ KS11Lie2Proof.HasType424
      ↥(CFSG.GH74.GLS.Stage2.Signalizer.Odd87.fixSub
        (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ)) :=
    not_hasType424_of_quasisimple ρ.range hqs hsolv (hmem _) (hmem _) hx1 hx3 hy3 hcx hcy hyx
  intro h
  exact hfix (h.of_mulEquiv (MulEquiv.subgroupCongr (Subgroup.ext fun _ => Iff.rfl)))

end CFSG.RankThree.PartTwo.Sec11.RonanD4Odd
