module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SmallGL2
public import CFSG.RankThree.SubgroupLists.SymplecticReducible

import CFSG.LocalAnalysis.UniquenessCase.UC22P20a
import CFSG.LocalAnalysis.WeakClosure81.W18ASNineCF
import CFSG.Quasithin.Vol2.Ch8Sec2L829LN1
public import CFSG.GH74.GLS.IVK.Proofs2.Stmt41
import CFSG.CGT.Timmesfeld75.L2Pair
import CFSG.CGT.Timmesfeld75.ListWCBasic
import CFSG.Certificates.Kernel.LocalCompTits.Span
import CFSG.CharacterTheory.TwoRankLowerBound.NormalComplementCharacterSpace
import CFSG.ClassicalGroups
import CFSG.LocalAnalysis.ComponentClassification.GSFMMaximal
import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSteps
import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
import CFSG.LocalAnalysis.ComponentClassification.Sol78Family
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7Iso
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122AProved
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57Sp4
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftSaturate
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
import CFSG.LocalAnalysis.SignalizerFunctor
import CFSG.Quasithin.Background.A3Structure318Red
import CFSG.Quasithin.Background.A3Structure36A
import CFSG.Quasithin.Background.A3Structure36BBase
import CFSG.Quasithin.Background.A3Structure36Base
import CFSG.Quasithin.Background.B216Quotient
import CFSG.Quasithin.Background.B3Facts
import CFSG.Quasithin.Background.B3FourConj
import CFSG.Quasithin.Background.B69Core
import CFSG.Quasithin.Background.C4Statement
import CFSG.Quasithin.Background.D2
import CFSG.Quasithin.Background.D2Dihedral
import CFSG.Quasithin.Background.E2Statements
import CFSG.Quasithin.Background.E2TwoLieQuotLift
import CFSG.Quasithin.Background.E3
import CFSG.Quasithin.Background.E3Uniq
import CFSG.Quasithin.Background.E4Solv
import CFSG.Quasithin.Background.F9FiveStruct
import CFSG.Quasithin.Background.F9G2
import CFSG.Quasithin.Background.F9Sixteen
import CFSG.Quasithin.Background.FFC7G
import CFSG.Quasithin.Background.H16TwoM22
import CFSG.Quasithin.Background.HMathieuO2Data
import CFSG.Quasithin.Background.HSecQuot
import CFSG.Quasithin.Background.HTriSolv
import CFSG.Quasithin.Background.HTriU3
import CFSG.Quasithin.Background.InternalSecAutOn
import CFSG.Quasithin.Background.InternalSecB4
import CFSG.Quasithin.Background.SmithB42L2L32
import CFSG.Quasithin.Background.SmithB42L2Nat
import CFSG.Quasithin.Background.SmithB42SL3Key
import CFSG.Quasithin.Background.SmithB45SL3Label
import CFSG.Quasithin.Background.SmithB45SL3Outer
import CFSG.Quasithin.Background.SmithB51LnRealB
import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
import CFSG.Quasithin.EmptyFaithful.S14110
import CFSG.Quasithin.EmptyFaithful.S14117
import CFSG.Quasithin.EmptyFaithful.S142Statements
import CFSG.Quasithin.EmptyFaithful.T1515Der
import CFSG.Quasithin.H13.A5S1326
import CFSG.Quasithin.H13.A5Top
import CFSG.Quasithin.Vol2.Ch10SecA1011B
import CFSG.Quasithin.Vol2.Ch10SecANat3
import CFSG.Quasithin.Vol2.Ch10StatementsE
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS
import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS2
import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS3
import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS4
import CFSG.Quasithin.Vol2.Ch12Sec2Statements
import CFSG.Quasithin.Vol2.Ch7NotFFS7
import CFSG.Quasithin.Vol2.Ch8Sec2L825O
import CFSG.Quasithin.Vol2.Ch8Sec2L829LM1
import CFSG.Quasithin.Vol2.Ch8Sec2L829LN0
import CFSG.RankThree.Asc83Table.PermTables
import CFSG.Sporadic.Schreier.J4SCommGenBase1
import CFSG.Sporadic.Schreier.J4SProfileNode
import Certificates.Kernel.J4Count.Cent11Base
import Certificates.Kernel.J4Count.Fix5
import Certificates.Kernel.J4Count.FixCE
import Certificates.Kernel.J4Count.FixCPairBase1
import Certificates.Kernel.J4Count.KFactsBase

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix CFSG.RankThree.SubgroupLists

private theorem sectionalTwoRankLE_of_isCompositionFactor_quotient_ker {F : Type} [Field F]
    [Finite F] (hodd : Odd (Nat.card F)) {X : Type} [Group X] (ρ : X →* GL (Fin 2) F)
    {L : Type} [Group L] (hL : CFSG.Quasithin.E1.IsCompositionFactor (X ⧸ ρ.ker) L)
    (hnab : ∃ a b : L, a * b ≠ b * a) : CFSG.GH74.SectionalTwoRankLE L 2 := by
  by_contra hrk
  have h : CFSG.Quasithin.E1.IsCompositionFactor
      ((X ⧸ ρ.ker) ⧸ (⊥ : Subgroup (X ⧸ ρ.ker))) L :=
    (CFSG.Quasithin.H13.L829N.isCompositionFactor_congr QuotientGroup.quotientBot).2 hL
  exact not_isCompositionFactor_quotient_of_injective_GL2
    (P := fun L _ => (∃ a b : L, a * b ≠ b * a) ∧ ¬ CFSG.GH74.SectionalTwoRankLE L 2)
    (fun _ _ _ hL => hL) hodd (QuotientGroup.kerLift ρ) (QuotientGroup.kerLift_injective ρ) ⊥ L h
    ⟨hnab, hrk⟩

theorem sectionalTwoRankLE_of_isCompositionFactor_of_gl2 {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) {X : Type} [Group X] [Finite X] (ρ : X →* GL (Fin 2) F)
    (hker : Group.IsSolvable ρ.ker) {L : Type} [Group L]
    (hL : CFSG.Quasithin.E1.IsCompositionFactor X L) (hnab : ∃ a b : L, a * b ≠ b * a) :
    CFSG.GH74.SectionalTwoRankLE L 2 := by
  rcases isCompositionFactor_of_normal ρ.ker hL with h | h
  · obtain ⟨a, b, hab⟩ := hnab
    exact absurd (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20a_abelian_of_compositionFactor
      hker h a b) hab
  · exact sectionalTwoRankLE_of_isCompositionFactor_quotient_ker hodd ρ h hnab

theorem sectionalTwoRankLE_of_isCompositionFactor_of_not_irreducible {r : ℕ} [Fact r.Prime]
    (hr2 : r ≠ 2) {G : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod r))}
    (hGS : G ≤ CFSG.Open.StatedSp 2 (ZMod r)) (hred : ¬ IsIrreducibleOn G)
    {L : Type} [Group L] (hL : CFSG.Quasithin.E1.IsCompositionFactor G L)
    (hnab : ∃ a b : L, a * b ≠ b * a) : CFSG.GH74.SectionalTwoRankLE L 2 := by
  classical
  have hodd : Odd (Nat.card (ZMod r)) := by
    rw [Nat.card_zmod]
    exact (Fact.out : r.Prime).odd_of_ne_two hr2
  have hV : Module.finrank (ZMod r) (Fin 2 ⊕ Fin 2 → ZMod r) = 4 := by simp
  have key : ∀ ρ : G →* GL (Fin 2) (ZMod r), Group.IsSolvable ρ.ker →
      CFSG.GH74.SectionalTwoRankLE L 2 :=
    fun ρ hρ => sectionalTwoRankLE_of_isCompositionFactor_of_gl2 hodd ρ hρ hL hnab
  have caseA : ∀ W, CFSG.RankThree.SubgroupLists.IsInvariant G W → Module.finrank (ZMod r) W = 2 → W ⊓ orth W = ⊥ →
      CFSG.GH74.SectionalTwoRankLE L 2 := by
    intro W hW h2 hd
    have hW' : CFSG.RankThree.SubgroupLists.IsInvariant G (orth W) := isInvariant_orth hGS hW
    have h2' : Module.finrank (ZMod r) (orth W) = 2 := by rw [finrank_orth, h2]
    have hsup : W ⊔ orth W = ⊤ := sup_orth_eq_top hd
    let b₁ := Module.finBasisOfFinrankEq (ZMod r) _ ((finrank_section_bot W).trans h2)
    let b₂ := Module.finBasisOfFinrankEq (ZMod r) _ ((finrank_section_bot (orth W)).trans h2')
    have hρ₁ := sectionRep_bot_eq_one_iff G hW b₁
    have hρ₂ := sectionRep_bot_eq_one_iff G hW' b₂
    have hjoint : ∀ g : G, sectionRep G (isInvariant_bot G) hW b₁ g = 1 →
        sectionRep G (isInvariant_bot G) hW' b₂ g = 1 → g = 1 := by
      intro g h1 h2
      apply Subtype.ext
      apply Units.ext
      rw [Matrix.ext_iff_mulVec]
      intro v
      have hv : v ∈ W ⊔ orth W := hsup ▸ Submodule.mem_top
      obtain ⟨w, hw, w', hw', rfl⟩ := Submodule.mem_sup.mp hv
      rw [Matrix.mulVec_add, (hρ₁ g).mp h1 w hw, (hρ₂ g).mp h2 w' hw', OneMemClass.coe_one,
        Units.val_one, Matrix.one_mulVec]
    rcases isCompositionFactor_of_normal (sectionRep G (isInvariant_bot G) hW b₁).ker hL with h | h
    ·
      refine sectionalTwoRankLE_of_isCompositionFactor_of_gl2 hodd
        ((sectionRep G (isInvariant_bot G) hW' b₂).comp
          (sectionRep G (isInvariant_bot G) hW b₁).ker.subtype) ?_ h hnab
      have : Subsingleton
          ((sectionRep G (isInvariant_bot G) hW' b₂).comp
            (sectionRep G (isInvariant_bot G) hW b₁).ker.subtype).ker :=
        ⟨fun x y => by
          have hx : (x.1 : G) = 1 := hjoint _ x.1.2 x.2
          have hy : (y.1 : G) = 1 := hjoint _ y.1.2 y.2
          exact Subtype.ext (Subtype.ext (hx.trans hy.symm))⟩
      infer_instance
    · exact sectionalTwoRankLE_of_isCompositionFactor_quotient_ker hodd _ h hnab
  have caseB : ∀ T, CFSG.RankThree.SubgroupLists.IsInvariant G T → T ≠ ⊥ → T ≤ orth T → CFSG.GH74.SectionalTwoRankLE L 2 := by
    intro T hT hT0 hTT
    have hfT := finrank_orth T
    have hle := Submodule.finrank_mono hTT
    have hpos : Module.finrank (ZMod r) T ≠ 0 := fun h => hT0 (Submodule.finrank_eq_zero.mp h)
    rcases (by omega : Module.finrank (ZMod r) T = 1 ∨ Module.finrank (ZMod r) T = 2) with
      h1 | h2
    ·
      let b₁ := Module.finBasisOfFinrankEq (ZMod r) _ ((finrank_section_bot T).trans h1)
      have hS : CFSG.RankThree.SubgroupLists.IsInvariant G (orth T) := isInvariant_orth hGS hT
      have hsec : Module.finrank (ZMod r) (orth T ⧸ T.comap (orth T).subtype) = 2 := by
        have h := Submodule.finrank_quotient_add_finrank (T.comap (orth T).subtype)
        rw [LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hTT), h1, hfT, h1] at h
        omega
      let b₂ := Module.finBasisOfFinrankEq (ZMod r) _ hsec
      have hker : ∀ g : G, sectionRep G hT hS b₂ g = 1 →
          sectionRep G (isInvariant_bot G) hT b₁ g = 1 → g ^ (r ^ 2) = 1 := by
        intro g hg hχ
        have hfix := (sectionRep_bot_eq_one_iff G hT b₁ g).mp hχ
        have hk := (sectionRep_eq_one_iff G hT hS b₂ g).mp hg
        apply pow_eq_one_of_unipotent_sub
        set gm : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod r) :=
          ((g : GL (Fin 2 ⊕ Fin 2) (ZMod r)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod r))
          with hgm
        set M := gm - 1 with hM
        have hMv : ∀ v, M *ᵥ v = gm *ᵥ v - v :=
          fun v => by rw [hM, Matrix.sub_mulVec, Matrix.one_mulVec]
        have h3 : M ^ 3 = 0 := by
          rw [Matrix.ext_iff_mulVec]
          intro v
          rw [mulVec_cube, Matrix.zero_mulVec]
          have hv1 : M *ᵥ v ∈ orth T := by rw [hMv]; exact sub_mem_orth_of_fix hGS hfix v
          have hv2 : M *ᵥ (M *ᵥ v) ∈ T := by rw [hMv]; exact hk _ hv1
          rw [hMv, hfix _ hv2, sub_self]
        rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, h3, zero_mul]
      refine key (sectionRep G hT hS b₂) ?_
      let ψ : (sectionRep G hT hS b₂).ker →* GL (Fin 1) (ZMod r) :=
        (sectionRep G (isInvariant_bot G) hT b₁).comp (sectionRep G hT hS b₂).ker.subtype
      have hψ : Group.IsSolvable ψ.ker := by
        have hp : IsPGroup r ψ.ker := fun x =>
          ⟨2, Subtype.ext (Subtype.ext (hker x.1.1 x.1.2 x.2))⟩
        have := hp.isNilpotent
        infer_instance
      have hcomm : Group.IsSolvable (GL (Fin 1) (ZMod r)) :=
        Group.isSolvable_of_comm gl_fin_one_comm
      exact Group.isSolvable_of_ker_le_range ψ.ker.subtype ψ (by simp)
    ·
      have hTeq : orth T = T :=
        (Submodule.eq_of_le_of_finrank_le hTT (by rw [hfT, h2])).symm
      let b := Module.finBasisOfFinrankEq (ZMod r) _ ((finrank_section_bot T).trans h2)
      have hker : ∀ g : G, sectionRep G (isInvariant_bot G) hT b g = 1 → g ^ (r ^ 2) = 1 := by
        intro g hg
        have hk := (sectionRep_bot_eq_one_iff G hT b g).mp hg
        apply pow_eq_one_of_unipotent_sub
        set gm : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod r) :=
          ((g : GL (Fin 2 ⊕ Fin 2) (ZMod r)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod r))
          with hgm
        set M := gm - 1 with hM
        have hMv : ∀ v, M *ᵥ v = gm *ᵥ v - v :=
          fun v => by rw [hM, Matrix.sub_mulVec, Matrix.one_mulVec]
        have h2' : M ^ 2 = 0 := by
          rw [Matrix.ext_iff_mulVec]
          intro v
          rw [mulVec_sq, Matrix.zero_mulVec]
          have hv1 : M *ᵥ v ∈ T := by
            rw [hMv, ← hTeq]
            exact sub_mem_orth_of_fix hGS hk v
          rw [hMv, hk _ hv1, sub_self]
        rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, h2', zero_mul]
      refine key (sectionRep G (isInvariant_bot G) hT b) ?_
      have hp : IsPGroup r (sectionRep G (isInvariant_bot G) hT b).ker := fun g =>
        ⟨2, Subtype.ext (hker g g.2)⟩
      have := hp.isNilpotent
      infer_instance
  obtain ⟨U, hU, hU0, hUt⟩ : ∃ U : Submodule (ZMod r) (Fin 2 ⊕ Fin 2 → ZMod r),
      CFSG.RankThree.SubgroupLists.IsInvariant G U ∧ U ≠ ⊥ ∧ U ≠ ⊤ := by
    by_contra hcon
    refine hred fun W hW => ?_
    by_contra hW'
    exact hcon ⟨W, hW, fun h => hW' (Or.inl h), fun h => hW' (Or.inr h)⟩
  by_cases hR : U ⊓ orth U = ⊥
  · have hpos : Module.finrank (ZMod r) U ≠ 0 := fun h => hU0 (Submodule.finrank_eq_zero.mp h)
    have hlt : Module.finrank (ZMod r) U < 4 := hV ▸ Submodule.finrank_lt hUt
    rcases (by omega : Module.finrank (ZMod r) U = 1 ∨ Module.finrank (ZMod r) U = 2 ∨
        Module.finrank (ZMod r) U = 3) with h1 | h2 | h3
    · exfalso
      exact hU0 (by rw [← inf_eq_left.mpr (le_orth_of_finrank_eq_one h1)]; exact hR)
    · exact caseA U hU h2 hR
    · exfalso
      have hW1 : Module.finrank (ZMod r) (orth U) = 1 := by rw [finrank_orth, h3]
      have hWle := le_orth_of_finrank_eq_one hW1
      rw [orth_orth] at hWle
      have hbot : orth U = ⊥ := by
        rw [← hR]
        exact le_antisymm (le_inf hWle le_rfl) inf_le_right
      rw [hbot, finrank_bot] at hW1
      exact zero_ne_one hW1
  · refine caseB (U ⊓ orth U)
      (CFSG.RankThree.SubgroupLists.isInvariant_inf hU (isInvariant_orth hGS hU)) hR
      fun x hx => ?_
    rw [mem_orth]
    intro y hy
    exact (mem_orth.mp hx.2) y hy.1

end CFSG.LocalAnalysis.WeakClosure81

end
