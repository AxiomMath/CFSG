module

public import CFSG.LocalAnalysis.StandardType.GGA6GlueToral
public import CFSG.LocalAnalysis.StandardType.GGLieCoreE6NonToralHolds
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeConfigID
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIpIso
public import CFSG.LocalAnalysis.StandardType.ChevTwoMarking
public import CFSG.LocalAnalysis.StandardType.GGLinearSemisimple
public import CFSG.LocalAnalysis.ComponentInitial.FixedComponentCorrespondence
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
public import CFSG.LocalAnalysis.StandardType.AlternatingEightNormalizerAction
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIField

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.RCKRP CFSG.StandardType.LieCore CFSG.StandardType.A6Red
open CFSG.Open (StatedLieTag)
open CFSG.StandardType.ExcFramesHalf (IsToralSubgroup)
open scoped commutatorElement

theorem rckIIpAt_excFive_toral_bridge
    {X : Type} [Group X] [Finite X] {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* X} {p : ℕ} {G₀ A B₁ D J L K : Subgroup X} {e : X}
    (ht : GGExcFive t) (hrow : GGSixRCKJRow .IIp J)
    (hcfg : RCKCompConfig t n f ψ p G₀ A B₁ D J L K e) :
    ∃ (θ : ↥G₀ →* ModGL (langTag t) GGL) (E : Subgroup (ModGL (langTag t) GGL)),
      θ.ker = Subgroup.center ↥G₀ ∧ θ.range = ⁅ggFixGp t f, ggFixGp t f⁆ ∧
      E ≤ ggFixGp t f ∧ IsElemAbelian p E ∧ Nat.card E = Nat.card D ∧
      (∀ d ∈ D, ∃ a ∈ E, ∀ x : ↥G₀, ∀ h : d * (x : X) * d⁻¹ ∈ G₀,
        θ ⟨d * (x : X) * d⁻¹, h⟩ = a * θ x * a⁻¹) ∧
      (∀ a ∈ E, ∃ d ∈ D, ∀ x : ↥G₀, ∀ h : d * (x : X) * d⁻¹ ∈ G₀,
        θ ⟨d * (x : X) * d⁻¹, h⟩ = a * θ x * a⁻¹) ∧
      (IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set X)) →
        IsComponentOf ((J.subgroupOf G₀).map θ)
          (⁅ggFixGp t f, ggFixGp t f⁆ ⊓
            Subgroup.centralizer (E : Set (ModGL (langTag t) GGL)))) ∧
      IsComponentOf ((J.subgroupOf G₀).map θ)
        (⁅ggFixGp t f, ggFixGp t f⁆ ⊓
          Subgroup.centralizer (E : Set (ModGL (langTag t) GGL))) ∧
      IsToralSubgroup (langTag t) GGL E ∧
      Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃*
        (↥((J.subgroupOf G₀).map θ) ⧸
          Subgroup.center ↥((J.subgroupOf G₀).map θ))) := by
  classical
  have hcfg' := hcfg
  obtain ⟨hGG, hodd, hp, hp2, hAel, hB1A, hDB1, hDc, hAnorm, hMark, hB1J, hB1inf,
    hp4, hA2, hrankA, hbot, hB1L, hMarkL, hJcomp, hoddJ, hLG0, hx, hnotD, hJcompL,
    hA6, heD, hene, hKcomp, hJK, hoddK⟩ := hcfg
  have hLie : LieModel (↥G₀ ⧸ Subgroup.center ↥G₀) t n 2 f := hGG.2.2.2
  have hf : 1 ≤ f := (LieModel.admissible hLie).2.1
  have hD_le_A : D ≤ A := hDB1.trans hB1A
  have hDn : D ≤ Subgroup.normalizer (G₀ : Set X) := hD_le_A.trans hAnorm
  have hDdiag : ∀ d ∈ D, GGPsiInnerDiag (ggU t n f).D ψ d := by
    intro d hd
    exact rckRPConfigInnerDiag_holds X t n f ψ p G₀ A B₁ D J L K e hcfg' d (hD_le_A hd)
  have hDel : IsElemAbelian p D := hAel.mono hD_le_A
  have hDC : D ⊓ Subgroup.centralizer (G₀ : Set X) = ⊥ := by
    refine le_bot_iff.mp ?_
    calc D ⊓ Subgroup.centralizer (G₀ : Set X)
        ≤ A ⊓ Subgroup.centralizer (G₀ : Set X) :=
          le_inf (inf_le_left.trans hD_le_A) inf_le_right
      _ = ⊥ := hbot
  have hbundle : GGLieBridgeHyp t n f p ψ G₀ D :=
    ⟨hGG.2.1.1, hGG.2.1.2, hLie, hDn, hDdiag, hDel, hDC⟩
  obtain ⟨θ, E, hθker, hθrange, hEfix, hEel, hEcard, hE1, hE2, hcomp⟩ :=
    ggLieBridge_holds p t n f ψ G₀ D J hp hp2 ht hf hbundle
  let Jalg : Subgroup (ModGL (langTag t) GGL) := (J.subgroupOf G₀).map θ
  have hJ' : IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set X)) := by
    rw [inf_comm]
    exact hJcomp
  have hJalgComp : IsComponentOf ((J.subgroupOf G₀).map θ)
      (⁅ggFixGp t f, ggFixGp t f⁆ ⊓
        Subgroup.centralizer (E : Set (ModGL (langTag t) GGL))) := hcomp hJ'
  have hJG : J ≤ G₀ := hJ'.1.trans inf_le_left
  let ψθ : ↥J →* ModGL (langTag t) GGL := θ.comp (Subgroup.inclusion hJG)
  have hψθ_apply : ∀ x : ↥J, ψθ x = θ ⟨(x : X), hJG x.2⟩ := by
    intro x
    change θ (Subgroup.inclusion hJG x) = θ ⟨(x : X), hJG x.2⟩
    simpa using congrArg θ
      (show Subgroup.inclusion hJG x = (⟨(x : X), hJG x.2⟩ : ↥G₀) from
        Subtype.ext (Subgroup.coe_inclusion hJG x))
  have hψθ_mem : ∀ x : ↥J, ψθ x ∈ (J.subgroupOf G₀).map θ := by
    intro x
    rw [hψθ_apply x]
    exact Subgroup.mem_map.mpr
      ⟨⟨(x : X), hJG x.2⟩, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩
  let φ : ↥J →* ↥Jalg := ψθ.codRestrict Jalg hψθ_mem
  have hφ_surj : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    have hy' : y ∈ (J.subgroupOf G₀).map θ := hy
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy'
    let zJ : ↥J := ⟨(z : X), Subgroup.mem_subgroupOf.mp hz⟩
    refine ⟨zJ, ?_⟩
    apply Subtype.ext
    change ψθ zJ = y
    rw [hψθ_apply zJ]
    change θ ⟨(z : X), hJG zJ.2⟩ = y
    have hz_eq : (⟨(z : X), hJG zJ.2⟩ : ↥G₀) = z := Subtype.ext rfl
    rw [hz_eq]
    exact hzy
  have hφ_ker : φ.ker ≤ Subgroup.center ↥J := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hx1 : θ ⟨(x : X), hJG x.2⟩ = 1 := by
      have h := Subtype.ext_iff.mp hx
      change ψθ x = 1 at h
      rw [hψθ_apply x] at h
      exact h
    have hxG : (⟨(x : X), hJG x.2⟩ : ↥G₀) ∈ Subgroup.center ↥G₀ := by
      rw [← hθker, MonoidHom.mem_ker]
      exact hx1
    have hcomm := Subgroup.mem_center_iff.mp hxG ⟨(y : X), hJG y.2⟩
    exact congrArg (fun z : ↥G₀ => (z : X)) hcomm
  have hJqs : CFSG.IsQuasisimple ↥J :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥J).mp
      hJcomp.2.2
  obtain ⟨eQuot⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.center_quotient_equiv_of_surjective
      hJqs φ hφ_surj hφ_ker
  obtain ⟨eA8⟩ := CFSG.StandardType.RCKK1IIp.rckIIp_iso hrow
  have hLieJalg : LieModel (↥Jalg ⧸ Subgroup.center ↥Jalg) .PSL 4 2 1 :=
    CFSG.StandardType.ChevTwo.lieModel_psl_four_two_of_alternating_eight
      (eQuot.symm.trans eA8)
  have hT : IsToralSubgroup (langTag t) GGL E := by
    by_cases hT : IsToralSubgroup (langTag t) GGL E
    · exact hT
    · exfalso
      have hEcardle : Nat.card E ≤ p ^ 2 := le_of_eq (hEcard.trans hDc)
      rcases a6glue_toral_or_nontoral ht hf hp hp2 hEfix hEel hEcardle with hT' | ⟨hτ, hp3, hE9⟩
      · exact hT hT'
      · have htE : t = .E6 ∨ t = .twistedE6 := by
          rcases ht with h | h | h | h | h
          · rw [h] at hτ ⊢
            exact absurd hτ (by simp [langTag])
          · exact Or.inl h
          · rw [h] at hτ ⊢
            exact absurd hτ (by simp [langTag])
          · rw [h] at hτ ⊢
            exact absurd hτ (by simp [langTag])
          · exact Or.inr h
        rcases htE with rfl | rfl
        · have hnt : ¬ IsToralSubgroup Tag.E6 GGL E := by simpa [langTag] using hT
          have hEadj : E ≤ adjointGroup Tag.E6 GGL := by
            simpa [langTag] using hEfix.trans inf_le_left
          have hJadj : Jalg ≤ adjointGroup Tag.E6 GGL := by
            change (J.subgroupOf G₀).map θ ≤ adjointGroup Tag.E6 GGL
            simpa [langTag] using
              hJalgComp.1.trans (inf_le_left.trans
                ((Subgroup.commutator_le_self (ggFixGp .E6 f)).trans inf_le_left))
          let E' : Subgroup (ModGL Tag.E6 GGL) := E
          have hnt' : ¬ IsToralSubgroup Tag.E6 GGL E' := hnt
          have hEadj' : E' ≤ adjointGroup Tag.E6 GGL := hEadj
          have hEel3 : IsElemAbelian 3 E := by simpa [hp3] using hEel
          have hEel3' : IsElemAbelian 3 E' := hEel3
          have hE9' : Nat.card E' = 3 ^ 2 := hE9
          have hJcent : Jalg ≤ Subgroup.centralizer (E' : Set (ModGL Tag.E6 GGL)) := by
            change (J.subgroupOf G₀).map θ ≤
              Subgroup.centralizer (E : Set (ModGL (langTag .E6) GGL))
            simpa using hJalgComp.1.trans inf_le_right
          have hJperf : ⁅Jalg, Jalg⁆ = Jalg :=
            CFSG.StandardType.LinSemisimple.commutator_eq_self_of_isQuasisimple hJalgComp.2.2
          exact (ggLieE6NonToralNoA8_holds GGL
            (CFSG.HardMathSupport.Timmesfeld.CrossChar.isAlgebraic_zmod_algebraicClosure_of_finite
              (ZMod 2) 2)
            E' hEadj' hEel3' hE9' hnt' Jalg hJadj hJcent hJperf) hLieJalg
        · have hnt : ¬ IsToralSubgroup Tag.E6 GGL E := by simpa [langTag] using hT
          have hEadj : E ≤ adjointGroup Tag.E6 GGL := by
            simpa [langTag] using hEfix.trans inf_le_left
          have hJadj : Jalg ≤ adjointGroup Tag.E6 GGL := by
            change (J.subgroupOf G₀).map θ ≤ adjointGroup Tag.E6 GGL
            simpa [langTag] using
              hJalgComp.1.trans (inf_le_left.trans
                ((Subgroup.commutator_le_self (ggFixGp .twistedE6 f)).trans inf_le_left))
          let E' : Subgroup (ModGL Tag.E6 GGL) := E
          have hnt' : ¬ IsToralSubgroup Tag.E6 GGL E' := hnt
          have hEadj' : E' ≤ adjointGroup Tag.E6 GGL := hEadj
          have hEel3 : IsElemAbelian 3 E := by simpa [hp3] using hEel
          have hEel3' : IsElemAbelian 3 E' := hEel3
          have hE9' : Nat.card E' = 3 ^ 2 := hE9
          have hJcent : Jalg ≤ Subgroup.centralizer (E' : Set (ModGL Tag.E6 GGL)) := by
            change (J.subgroupOf G₀).map θ ≤
              Subgroup.centralizer (E : Set (ModGL (langTag .twistedE6) GGL))
            simpa using hJalgComp.1.trans inf_le_right
          have hJperf : ⁅Jalg, Jalg⁆ = Jalg :=
            CFSG.StandardType.LinSemisimple.commutator_eq_self_of_isQuasisimple hJalgComp.2.2
          exact (ggLieE6NonToralNoA8_holds GGL
            (CFSG.HardMathSupport.Timmesfeld.CrossChar.isAlgebraic_zmod_algebraicClosure_of_finite
              (ZMod 2) 2)
            E' hEadj' hEel3' hE9' hnt' Jalg hJadj hJcent hJperf) hLieJalg
  refine ⟨θ, E, hθker, hθrange, hEfix, hEel, hEcard, hE1, hE2, hcomp, hJalgComp, hT, ?_⟩
  exact ⟨eQuot⟩

end CFSG.StandardType.RCKC1
