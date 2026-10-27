module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndSignalizer

import CFSG.LocalAnalysis.UniquenessCase.UC1K327Core
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma123a
import CFSG.LocalAnalysis.GH72.PGammaL2Permutable
import CFSG.Adapters.WholeGroupLayer
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Core
import CFSG.GH74.GLS.AssemblyComponents
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure
import CFSG.SignalizerFunctorTheorem.McBride.Functor.SrSubgroup
public import CFSG.Fischer.Classification.Unitary.Coords
public import CFSG.LargeExtraspecial.AS35QThModel
import CFSG.Adapters.GeneralizedFitting
import CFSG.GH74.GLS.Defs
import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionFitting
import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionMoved
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5Containment
import CFSG.LocalAnalysis.ComponentClassification.FittingNilpotence
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma136
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
  (coprime_card_relPPrimeCore)

@[expose] def KFactE27SignalizerComp : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (P A : Subgroup X), CFSG.Open.IsKGroup X →
    UC22.InS3.UC327.Hyp327 X P A → Nonempty (↥P ≃* UC22.InS3.UC326.ZWr 1) →
    CFSG.pPrimeCore 3 X = ⊥ →
    (∀ a ∈ A, a ≠ 1 → ∀ W : Subgroup X, W ≤ Subgroup.centralizer ({a} : Set X) →
      A ≤ Subgroup.normalizer (W : Set X) → Nat.Coprime (Nat.card W) 3 →
      W ≤ CFSG.Open.relPPrimeCore 3 (Subgroup.centralizer ({a} : Set X))) →
    ∀ L : Subgroup X, CFSG.IsComponent L →
      IsCyclic ↥(A ⊓ Subgroup.centralizer (L : Set X)) →
    ∀ W : Subgroup X, A ≤ Subgroup.normalizer (W : Set X) → Nat.Coprime (Nat.card W) 3 →
      W ≤ Subgroup.centralizer (L : Set X)

namespace A10Gen

theorem eq_bot_of_le_centralizer_generalizedFitting {H : Type} [Group H] [Finite H]
    {p : ℕ} [Fact p.Prime] {W : Subgroup H} (hcop : Nat.Coprime p (Nat.card W))
    (hO : CFSG.pPrimeCore p H = ⊥)
    (hW : W ≤ Subgroup.centralizer (CFSG.generalizedFitting H : Set H)) : W = ⊥ := by
  have hle : W ≤ CFSG.pCore p H := by
    refine hW.trans ((CFSG.Adapters.centralizer_generalizedFitting_le_fittingSubgroup H).trans ?_)
    rw [CFSG.Fitting_eq_pcore H p hO]
  have hdisj : CFSG.pCore p H ⊓ W = ⊥ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC327.inf_eq_bot_of_isPGroup_of_coprime
      (p := p) (CFSG.pCore_isPGroup (p := p) (G := H)) hcop
  exact le_bot_iff.mp (le_inf hle le_rfl |>.trans (le_of_eq hdisj))

end A10Gen

private lemma inf_centralizer_le_centralizer_of_isComponent {X : Type} [Group X] [Finite X]
    {A : Subgroup X} (hA : CFSG.Open.IsElemAbelian 3 A)
    (hbal : ∀ a ∈ A, a ≠ 1 → ∀ U : Subgroup X, U ≤ Subgroup.centralizer ({a} : Set X) →
      A ≤ Subgroup.normalizer (U : Set X) → Nat.Coprime (Nat.card U) 3 →
      U ≤ CFSG.Open.relPPrimeCore 3 (Subgroup.centralizer ({a} : Set X)))
    (h3' : CFSG.pPrimeCore 3 X = ⊥) {W : Subgroup X}
    (hW : A ≤ Subgroup.normalizer (W : Set X)) (hcop : Nat.Coprime (Nat.card W) 3)
    {L : Subgroup X} (hL : CFSG.IsComponent L) {b : X} (hbA : b ∈ A)
    (hbL : b ∈ Subgroup.centralizer (L : Set X)) (hb1 : b ≠ 1) :
    W ⊓ Subgroup.centralizer ({b} : Set X) ≤ Subgroup.centralizer (L : Set X) := by
  classical
  let C : Subgroup X := Subgroup.centralizer ({b} : Set X)
  let N : Subgroup X := CFSG.Open.relPPrimeCore 3 C
  let R : Subgroup X := W ⊓ C
  have hLC : L ≤ C := by
    intro l hl
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hbL l hl
  have hAC : A ≤ C := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hx⟩ ⟨b, hbA⟩)
  have hRle : R ≤ N := by
    refine hbal b hbA hb1 R inf_le_right ?_ ?_
    · exact (le_inf hW (hAC.trans Subgroup.le_normalizer)).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    · exact (Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le (inf_le_left : R ≤ W))
        hcop.symm).symm
  have hNle : N ≤ C :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le C
  have hNnorm : (N.subgroupOf C).Normal :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_normal
      Nat.prime_three C
  have hcomp : CFSG.IsComponent (L.subgroupOf C) := CFSG.LocalCores.component_overgroup hL hLC
  rcases CFSG.LocalCores.component_normal_subgroup hcomp hNnorm with hLN | hcomm
  · exfalso
    have hLN' : L ≤ N := CFSG.LocalCores.le_of_subgroupOf_le hLC hLN
    have hLcop : Nat.Coprime 3 (Nat.card L) :=
      Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le hLN')
        (coprime_card_relPPrimeCore
          Nat.prime_three C)
    have hLbot : L = ⊥ := by
      have h := CFSG.GH74.GLS.le_pPrimeCore_of_subnormal 3 hL.2 hLcop
      rw [h3'] at h
      exact le_bot_iff.mp h
    exact (Subgroup.nontrivial_iff_ne_bot L).mp
      (CFSG.LocalCores.isQuasisimple_nontrivial hL.1) hLbot
  · have hcommL : ⁅L, N ⊓ C⁆ = ⊥ :=
      CFSG.LocalCores.commutator_inf_eq_bot_of_subgroupOf hLC hcomm
    rw [inf_eq_left.mpr hNle, Subgroup.commutator_comm] at hcommL
    have hNcent : N ≤ Subgroup.centralizer (L : Set X) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hcommL
    exact hRle.trans hNcent

private lemma centralizer_relPPrimeCore {X : Type} [Group X] [Finite X] {a : X} :
    CFSG.pCore 3 X ⊓ Subgroup.centralizer ({a} : Set X) ≤
      Subgroup.centralizer (CFSG.Open.relPPrimeCore 3
        (Subgroup.centralizer ({a} : Set X)) : Set X) := by
  classical
  let C : Subgroup X := Subgroup.centralizer ({a} : Set X)
  let N : Subgroup X := CFSG.Open.relPPrimeCore 3 C
  let M : Subgroup X := CFSG.pCore 3 X ⊓ C
  have hMC : M ≤ C := inf_le_right
  have hNle : N ≤ C :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le C
  have hNnorm : (N.subgroupOf C).Normal :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_normal
      Nat.prime_three C
  have hCN : C ≤ Subgroup.normalizer (N : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNle).mp hNnorm
  have hCM : C ≤ Subgroup.normalizer (M : Set X) := by
    have hCP : C ≤ Subgroup.normalizer (CFSG.pCore 3 X : Set X) := by
      rw [Subgroup.normalizer_eq_top (CFSG.pCore 3 X)]
      exact le_top
    exact (le_inf hCP Subgroup.le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hNMleN : ⁅N, M⁆ ≤ N :=
    (Subgroup.le_normalizer_iff_commutator_le_left (H := M) (K := N)).mp (hMC.trans hCN)
  have hNMleM : ⁅N, M⁆ ≤ M := by
    rw [Subgroup.commutator_comm N M]
    exact (Subgroup.le_normalizer_iff_commutator_le_left (H := N) (K := M)).mp (hNle.trans hCM)
  have hPNbot : CFSG.pCore 3 X ⊓ N = ⊥ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC327.inf_eq_bot_of_isPGroup_of_coprime
      (p := 3) (CFSG.pCore_isPGroup (p := 3) (G := X))
      (coprime_card_relPPrimeCore
        Nat.prime_three C)
  have hNMbot : ⁅N, M⁆ = ⊥ := by
    rw [eq_bot_iff]
    refine (le_inf hNMleN hNMleM).trans ?_
    exact (inf_le_inf_left N (inf_le_left : M ≤ CFSG.pCore 3 X)).trans
      (le_of_eq (by rw [inf_comm, hPNbot]))
  rw [Subgroup.commutator_comm N M] at hNMbot
  exact (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hNMbot

private lemma pCore_le_centralizer_inf_centralizer_singleton {X : Type} [Group X] [Finite X]
    {A : Subgroup X} (hA : CFSG.Open.IsElemAbelian 3 A)
    (hbal : ∀ a ∈ A, a ≠ 1 → ∀ U : Subgroup X, U ≤ Subgroup.centralizer ({a} : Set X) →
      A ≤ Subgroup.normalizer (U : Set X) → Nat.Coprime (Nat.card U) 3 →
      U ≤ CFSG.Open.relPPrimeCore 3 (Subgroup.centralizer ({a} : Set X)))
    {W : Subgroup X} (hW : A ≤ Subgroup.normalizer (W : Set X))
    (hcop : Nat.Coprime (Nat.card W) 3) {a : X} (haA : a ∈ A) (ha1 : a ≠ 1) :
    CFSG.pCore 3 X ≤ Subgroup.centralizer
      ((W ⊓ Subgroup.centralizer ({a} : Set X)) : Set X) := by
  classical
  let C : Subgroup X := Subgroup.centralizer ({a} : Set X)
  let R : Subgroup X := W ⊓ C
  let P : Subgroup X := CFSG.pCore 3 X
  let N : Subgroup X := CFSG.Open.relPPrimeCore 3 C
  let M : Subgroup X := P ⊓ C
  have hRC : R ≤ C := inf_le_right
  have hAC : A ≤ C := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hx⟩ ⟨a, haA⟩)
  have hAR : A ≤ Subgroup.normalizer (R : Set X) :=
    (le_inf hW (hAC.trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hRcop : Nat.Coprime (Nat.card R) 3 :=
    (Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le (inf_le_left : R ≤ W)) hcop.symm).symm
  have hRN : R ≤ N := hbal a haA ha1 R hRC hAR hRcop
  have hfix : P ⊓ Subgroup.centralizer (Subgroup.zpowers a : Set X) ≤
      Subgroup.centralizer (R : Set X) := by
    have hzp : Subgroup.centralizer (Subgroup.zpowers a : Set X) = C := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    rw [hzp]
    exact (centralizer_relPPrimeCore (a := a)).trans (Subgroup.centralizer_le hRN)
  have hB3 : IsPGroup 3 (Subgroup.zpowers a) :=
    hA.isPGroup.to_le (Subgroup.zpowers_le.mpr haA)
  have hRB : ⁅R, Subgroup.zpowers a⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.zpowers_eq_closure,
      Subgroup.centralizer_closure]
    exact hRC
  have hnormP : R ≤ Subgroup.normalizer (P : Set X) := by
    rw [Subgroup.normalizer_eq_top P]
    exact le_top
  have hnormP' : Subgroup.zpowers a ≤ Subgroup.normalizer (P : Set X) := by
    rw [Subgroup.normalizer_eq_top P]
    exact le_top
  exact CFSG.GH72.le_centralizer_of_thompson_AxB (p := 3) (P := P) (R := R)
    (B := Subgroup.zpowers a) (CFSG.pCore_isPGroup (p := 3) (G := X)) hRcop hB3
    hnormP hnormP' hRB hfix

private lemma le_centralizer_layer_of_comp (h : KFactE27SignalizerComp)
    {X : Type} [Group X] [Finite X] {P A : Subgroup X} (hK : CFSG.Open.IsKGroup X)
    (hX : UC22.InS3.UC327.Hyp327 X P A) (hP : Nonempty (↥P ≃* UC22.InS3.UC326.ZWr 1))
    (h3' : CFSG.pPrimeCore 3 X = ⊥)
    (hbal : ∀ a ∈ A, a ≠ 1 → ∀ U : Subgroup X, U ≤ Subgroup.centralizer ({a} : Set X) →
      A ≤ Subgroup.normalizer (U : Set X) → Nat.Coprime (Nat.card U) 3 →
      U ≤ CFSG.Open.relPPrimeCore 3 (Subgroup.centralizer ({a} : Set X)))
    {W : Subgroup X} (hW : A ≤ Subgroup.normalizer (W : Set X))
    (hcop : Nat.Coprime (Nat.card W) 3) :
    W ≤ Subgroup.centralizer (CFSG.layer X : Set X) := by
  classical
  rw [CFSG.layer.eq_sSup, Subgroup.le_centralizer_iff]
  refine sSup_le fun L hL => ?_
  rw [Subgroup.le_centralizer_iff]
  let B : Subgroup X := A ⊓ Subgroup.centralizer (L : Set X)
  by_cases hcyc : IsCyclic ↥B
  · exact h X P A hK hX hP h3' hbal L hL hcyc W hW hcop
  · have hBA : B ≤ A := inf_le_left
    have hBelem : CFSG.Open.IsElemAbelian 3 B := hX.elem.mono hBA
    have hBcard : 3 ^ 2 ≤ Nat.card B :=
      CFSG.SignalizerFunctorTheorem.McBride.two_le_rank_of_not_isCyclic
        (p := 3) Nat.prime_three hX.elem hBA hcyc
    have hdiv : ¬ 3 ∣ Nat.card W :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop.symm
    have hgen := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma123.le_iSup_inf_centralizer
      (p := 3) hBelem hBcard hdiv (hBA.trans hW)
    refine hgen.trans ?_
    refine iSup_le fun b => iSup_le fun hbB => iSup_le fun hb1 => ?_
    exact inf_centralizer_le_centralizer_of_isComponent hX.elem hbal h3' hW hcop hL
      (Subgroup.mem_inf.mp hbB).1 (Subgroup.mem_inf.mp hbB).2 hb1

private lemma le_centralizer_fittingSubgroup {X : Type} [Group X] [Finite X] {W : Subgroup X}
    (h3' : CFSG.pPrimeCore 3 X = ⊥)
    (hcore : W ≤ Subgroup.centralizer (CFSG.pCore 3 X : Set X)) :
    W ≤ Subgroup.centralizer (CFSG.fittingSubgroup X : Set X) := by
  rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore]
  refine CFSG.subgroup_le_centralizer_iSup_of_le_centralizer
    (fun q : (Nat.card X).primeFactors => CFSG.pCore (q : ℕ) X) ?_
  intro q
  by_cases hq3 : (q : ℕ) = 3
  · rw [hq3]
    exact hcore
  · have hqprime : (q : ℕ).Prime := Nat.prime_of_mem_primeFactors q.2
    have hqcop : Nat.Coprime 3 (Nat.card (CFSG.pCore (q : ℕ) X)) := by
      haveI : Fact (Nat.Prime (q : ℕ)) := ⟨hqprime⟩
      obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := (q : ℕ)) (G := X)).exists_card_eq
      rw [hn]
      exact ((Nat.coprime_primes Nat.prime_three hqprime).2 (fun h => hq3 h.symm)).pow_right n
    have hbot : CFSG.pCore (q : ℕ) X = ⊥ :=
      (CFSG.pPrimeCore_eq_bot_iff (p := 3) (G := X)).mp h3' (CFSG.pCore (q : ℕ) X)
        CFSG.pCore_normal hqcop
    rw [hbot]
    exact (Subgroup.le_centralizer_iff).mpr bot_le

theorem kFactE27SignalizerLayer_of_comp (h : KFactE27SignalizerComp) :
    KFactE27SignalizerLayer := by
  intro X _ _ P A hK hX hP h3' hlayer hbal W hW hcop
  have hdiv : ¬ 3 ∣ Nat.card W :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop.symm
  have hgen := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma123.le_iSup_inf_centralizer
    (p := 3) hX.elem (by rw [hX.card]; norm_num) hdiv hW
  have hcore : W ≤ Subgroup.centralizer (CFSG.pCore 3 X : Set X) := by
    refine hgen.trans ?_
    refine iSup_le fun a => iSup_le fun ha => iSup_le fun ha1 => ?_
    exact (Subgroup.le_centralizer_iff).mpr
      (pCore_le_centralizer_inf_centralizer_singleton hX.elem hbal hW hcop ha ha1)
  have hlayerCent : W ≤ Subgroup.centralizer (CFSG.layer X : Set X) :=
    le_centralizer_layer_of_comp h hK hX hP h3' hbal hW hcop
  have hfit : W ≤ Subgroup.centralizer (CFSG.fittingSubgroup X : Set X) :=
    le_centralizer_fittingSubgroup h3' hcore
  have hFstar : W ≤ Subgroup.centralizer (CFSG.generalizedFitting X : Set X) := by
    rw [CFSG.generalizedFitting.eq_sup]
    exact CFSG.GorensteinWalter.le_centralizer_sup_of_le_centralizers hfit hlayerCent
  exact A10Gen.eq_bot_of_le_centralizer_generalizedFitting hcop.symm h3' hFstar

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
