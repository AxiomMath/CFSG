module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148HL37
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.PointSigReduction
public import CFSG.RankThree.PartTwo.Sec14.Ronan148HYd
import CFSG.RankThree.PartTwo.Sec14.Item148StepPoint
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKType
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec6.Item68
import CFSG.RankThree.PartTwo.Sec6.Item612Local
import CFSG.RankThree.PartTwo.Sec6.Item612Core
import CFSG.RankThree.PartTwo.Sec15.Item1423ProofTools
import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
import CFSG.RankThree.PartTwo.Sec14.Concl143Std
import CFSG.RankThree.PartTwo.Sec4.LThreePiAct
import CFSG.RankThree.PartTwo.Sec21.Item223PrintProofOne
public import CFSG.Milestones.CL_LIT_Gorenstein_Walter_L_balance
public import CFSG.RankThree.PartTwo.Sec14.Item148HJRes2ProofInner
public import CFSG.RankThree.PartTwo.Sec14.Item148HJRes2ProofYd
import CFSG.RankThree.PartOne.S9.Sylow.GlobalRelative
import CFSG.RankThree.PartTwo.Sec11.Theorem1134
import CFSG.RankThree.PartTwo.Sec13.Item135
import CFSG.RankThree.PartTwo.Sec13.Item135Simple
import CFSG.RankThree.PartTwo.Sec13.Item135SimpleReduce
import CFSG.RankThree.PartTwo.Sec21.Commute33
import CFSG.RankThree.PartTwo.Sec21.Item223PrintProofFour
import CFSG.RankThree.PartTwo.Sec21.Item233
import CFSG.RankThree.PartTwo.Sec21.Item233OneProof
import CFSG.RankThree.PartTwo.Sec21.Item233OneProofHull
import CFSG.RankThree.PartTwo.Sec21.Item233OneProofStatements

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148H

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.PointSig (Data bar
  rho rho_mk_of_mem pi_mem_normalizer_bar card_bar_dvd bar_commutator bar_mono not_bar_le_core
  isHyperplane_bar center_le_bar sig_bar isE27_bar mem_bar exists_component_of_image coreSup
  TwoLines thL)
open scoped commutatorElement

@[expose] def KList46 (X : Type) [Group X] : Prop :=
  ∀ J : Subgroup X, Group.IsPerfect J → IsQuasisimple (↥J ⧸ aschbacherSolvableCore 3 ↥J) →
    Sec4.IsList46 (↥J ⧸ aschbacherSolvableCore 3 ↥J)

@[expose] def KF148OneLineK : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Group.IsPerfect X →
    Sec4.IsTripleCover X CFSG.Blueprint.NativeSporadic.ON → KList46 X →
    ∀ (P Y : Subgroup X), Late.IsE27 P → P ≤ Subgroup.normalizer (Y : Set X) →
      (∀ H : Subgroup X, IsHyperplane P H → ∀ V : Subgroup X,
        V ≤ Y ⊓ Subgroup.centralizer (H : Set X) → V ∈ invariantPiSubgroups ⊤ P (piCompl 3) →
        V = ⁅V, P⁆ → V ≤ pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer (H : Set X))) →
      ¬ TwoLines P Y → coreSup P Y ≤ pPrimeCoreOf 3 Y

@[expose] def KF148CoreComponentK : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Group.IsPerfect X →
    Sec4.IsTripleCover X CFSG.Blueprint.NativeSporadic.ON → KList46 X →
    ∀ (P Y : Subgroup X), Late.IsE27 P → P ≤ Subgroup.normalizer (Y : Set X) →
      (∀ H : Subgroup X, IsHyperplane P H → ∀ V : Subgroup X,
        V ≤ Y ⊓ Subgroup.centralizer (H : Set X) → V ∈ invariantPiSubgroups ⊤ P (piCompl 3) →
        V = ⁅V, P⁆ → V ≤ pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer (H : Set X))) →
      ¬ coreSup P Y ≤ pPrimeCoreOf 3 Y →
      coreSup P Y ∈ thetaComponentsIn Y ∧ 3 ∣ Nat.card (coreSup P Y)

@[expose] def KF148PointX27K : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Group.IsPerfect X →
    Sec4.IsTripleCover X CFSG.Blueprint.NativeSporadic.ON → KList46 X →
    ∀ (P W Q B : Subgroup X), Late.IsE27 P → P ≤ Subgroup.normalizer (W : Set X) →
      IsHyperplane P B → Subgroup.center X ≤ B →
      Q ≤ W ⊓ Subgroup.centralizer (B : Set X) → Q ∈ invariantPiSubgroups ⊤ P (piCompl 3) →
      Q = ⁅Q, P⁆ → Q ≠ ⊥ →
      (∀ H : Subgroup X, IsHyperplane P H → ∀ V : Subgroup X,
        V ≤ W ⊓ Subgroup.centralizer (H : Set X) → V ∈ invariantPiSubgroups ⊤ P (piCompl 3) →
        V = ⁅V, P⁆ → V ≤ pPrimeCoreOf 3 (W ⊓ Subgroup.centralizer (H : Set X))) →
      ¬ Q ≤ pPrimeCoreOf 3 W →
      ∃ T ∈ thetaComponentsIn W, P ≤ Subgroup.normalizer (T : Set X) ∧ 3 ∣ Nat.card T ∧
        T ≤ ⨆ (p : X) (_ : p ∈ P) (_ : p ∉ Subgroup.center X),
          pPrimeCoreOf 3 (T ⊓ Subgroup.centralizer ({p} : Set X))

@[expose] def KF148PointSigONMaxK : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (A L R W Q B : Subgroup Γ) (b : Γ),
    Late.IsE27 A → b ∈ A → b ≠ 1 → L ≤ Subgroup.centralizer ({b} : Set Γ) →
    A ≤ Subgroup.normalizer (L : Set Γ) →
    Sec4.IsTripleCover (↥L ⧸ aschbacherSolvableCore 3 ↥L) CFSG.Blueprint.NativeSporadic.ON →
    IsQuasisimple (↥L ⧸ aschbacherSolvableCore 3 ↥L) →
    (∀ x : Γ, x ^ 3 = 1 → (∀ a ∈ A, a * x = x * a) → x ∈ A) →
    (∀ J : Subgroup Γ, J ≤ L → Group.IsPerfect J →
      IsQuasisimple (↥J ⧸ aschbacherSolvableCore 3 ↥J) →
      Sec4.IsList46 (↥J ⧸ aschbacherSolvableCore 3 ↥J)) →
    Nat.Coprime 3 (Nat.card R) → L ≤ Subgroup.normalizer (R : Set Γ) →
    R ≤ Subgroup.normalizer (L : Set Γ) → A ≤ Subgroup.normalizer (R : Set Γ) →
    W ≤ L ⊔ R → A ≤ Subgroup.normalizer (W : Set Γ) →
    IsHyperplane A B → b ∈ B → Q ≤ W ⊓ Subgroup.centralizer (B : Set Γ) →
    Q ∈ invariantPiSubgroups ⊤ A (piCompl 3) → Q = ⁅Q, A⁆ →
    (∀ H : Subgroup Γ, IsHyperplane A H → ∀ V : Subgroup Γ,
      V ≤ W ⊓ Subgroup.centralizer (H : Set Γ) → V ∈ invariantPiSubgroups ⊤ A (piCompl 3) →
      V = ⁅V, A⁆ → V ≤ pPrimeCoreOf 3 (W ⊓ Subgroup.centralizer (H : Set Γ))) →
    ¬ Q ≤ pPrimeCoreOf 3 W →
    ∃ K ∈ thetaComponentsIn W, K ≤ L ∧
      K ≤ sSup {V : Subgroup Γ | V ≤ K ∧ V ∈ invariantPiSubgroups ⊤ A (piCompl 3) ∧ V = ⁅V, A⁆}

section Lift

variable {X Y : Type} [Group X] [Group Y] [Finite X]

theorem exists_perfect_map_eq_of_surjective (π : X →* Y) (hπ : Function.Surjective π)
    (J : Subgroup Y) (hJ : Group.IsPerfect J) :
    ∃ P : Subgroup X, Group.IsPerfect P ∧ P.map π = J := by
  obtain ⟨P, hP, hmin⟩ := Set.exists_min_image {P : Subgroup X | P.map π = J}
    (fun P => Nat.card P) (Set.toFinite _)
    ⟨J.comap π, Subgroup.map_comap_eq_self_of_surjective hπ J⟩
  have hP' : P.map π = J := hP
  have hc : (⁅P, P⁆ : Subgroup X).map π = J := by
    rw [Subgroup.map_commutator, hP']
    exact Subgroup.isPerfect_iff.mp hJ
  have hle : ⁅P, P⁆ ≤ P := Subgroup.commutator_le.mpr fun g₁ h₁ g₂ h₂ => by
    rw [commutatorElement_def]
    exact P.mul_mem (P.mul_mem (P.mul_mem h₁ h₂) (P.inv_mem h₁)) (P.inv_mem h₂)
  have heq : ⁅P, P⁆ = P := Subgroup.eq_of_le_of_card_ge hle (hmin _ hc)
  exact ⟨P, Subgroup.isPerfect_iff.mpr heq, hP'⟩

end Lift

theorem kList46_thetaQuot {Γ : Type} [Group Γ] [Finite Γ] {L : Subgroup Γ}
    (hK : ∀ J : Subgroup Γ, J ≤ L → Group.IsPerfect J →
      IsQuasisimple (↥J ⧸ aschbacherSolvableCore 3 ↥J) →
      Sec4.IsList46 (↥J ⧸ aschbacherSolvableCore 3 ↥J)) :
    KList46 (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
  intro J hJp hJq
  obtain ⟨-, hθc, -, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  haveI : (aschbacherSolvableCore 3 ↥L).Normal := by haveI := hθc; infer_instance
  set N := aschbacherSolvableCore 3 ↥L with hN
  set π : ↥L →* ↥L ⧸ N := QuotientGroup.mk' N with hπ
  obtain ⟨P, hPp, hPJ⟩ :=
    exists_perfect_map_eq_of_surjective π (QuotientGroup.mk'_surjective N) J hJp
  have hmem : ∀ p : ↥P, π (P.subtype p) ∈ J := fun p => hPJ ▸ ⟨p, p.2, rfl⟩
  set f : ↥P →* ↥J := (π.comp P.subtype).codRestrict J hmem with hf
  have hfs : Function.Surjective f := by
    rintro ⟨y, hy⟩
    rw [← hPJ] at hy
    obtain ⟨p, hp, rfl⟩ := hy
    exact ⟨⟨p, hp⟩, rfl⟩
  have hker : f.ker ≤ aschbacherSolvableCore 3 ↥P := by
    refine le_trans ?_ (comap_theta_le P.subtype P.subtype_injective)
    intro p hp
    rw [MonoidHom.mem_ker] at hp
    rw [Subgroup.mem_comap]
    have h1 : π (P.subtype p) = 1 := congrArg Subtype.val hp
    exact (QuotientGroup.eq_one_iff _).mp h1
  obtain ⟨e⟩ := nonempty_thetaQuot_equiv_of_ker_le f hfs hker
  set J₀ : Subgroup Γ := P.map L.subtype with hJ₀
  have eP : ↥P ≃* ↥J₀ := P.equivMapOfInjective L.subtype L.subtype_injective
  have hJ₀p : Group.IsPerfect J₀ := isPerfect_of_mulEquiv eP hPp
  have eθ : ↥J₀ ⧸ aschbacherSolvableCore 3 ↥J₀ ≃* ↥J ⧸ aschbacherSolvableCore 3 ↥J :=
    (thetaQuotEquiv eP).symm.trans e
  have hJ₀q : IsQuasisimple (↥J₀ ⧸ aschbacherSolvableCore 3 ↥J₀) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eθ.symm hJq
  exact Sec21.Item223PrintProof.isList46_of_mulEquiv eθ
    (hK J₀ (Subgroup.map_subtype_le P) hJ₀p hJ₀q)

section Model

set_option linter.unusedSectionVars false


theorem kf148CoreComponentK_of_oneLineK (h1 : KF148OneLineK) : KF148CoreComponentK := by
  intro X _ _ hperf hT hKX P Y hP hPY hsig hnot
  by_cases htwo : TwoLines P Y
  · obtain ⟨hm, hc⟩ := PointSig.coreSup_mem_of_twoLines hperf hT hP hPY
      Sec4.Ronan148H.l37OvergroupTransfer_holds htwo
    exact ⟨hm, by rw [hc]; norm_num⟩
  · exact (hnot (h1 X hperf hT hKX P Y hP hPY hsig htwo)).elim

end Model

theorem kf148PointX27K_of_coreComponentK (h : KF148CoreComponentK) : KF148PointX27K := by
  intro X _ _ hperf htriple hKX P W Q B hP hPW hB hZB hQW hQinv hQc hQ0 hsig hQnot
  have hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hP.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hQcore := hsig B hB Q hQW hQinv hQc
  have hQT : Q ≤ coreSup P W := PointSig.le_coreSup_of_le_core hP hB htriple.1 hZB hQcore
  have hnot : ¬ coreSup P W ≤ pPrimeCoreOf 3 W := fun hle => hQnot (hQT.trans hle)
  obtain ⟨hmem, h3⟩ := h X hperf htriple hKX P W hP hPW hsig hnot
  exact ⟨coreSup P W, hmem, PointSig.le_normalizer_coreSup hcomm hPW, h3,
    PointSig.coreSup_le_iSup_core P W⟩

theorem kf148PointSigONMaxK_of_x27K
    (h : KF148PointX27K) : KF148PointSigONMaxK := by
  intro Γ _ _ A L R W Q B b hA hbA hb1 hLb hAL hT hq hmax hKL hR3 hLR hRL hAR hWLR hAW hB hbB
    hQW hQ hQA hsig hQW'
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAL' : A ≤ L := ONLoc.le_of_forall_mem hA hbA hb1 hLb hAL hq hT hmax
  have hAθ : A ⊓ thL L = ⊥ := ONLoc.inf_theta_eq_bot hA.isPGroup
  let d : Data A L R b :=
    ⟨hA, hbA, hb1, hLb, hAL, hT, hq, hAL', hAθ, hR3, hLR, hRL, hAR⟩
  have hsolL : Group.IsSolvable ↥(L ⊓ Subgroup.centralizer (A : Set Γ)) :=
    ThreeGroup.isSolvable_inf_centralizer hA hbA hb1 hLb hAL hq hT hmax
  have hQLR : Q ≤ L ⊔ R := (hQW.trans inf_le_left).trans hWLR
  have hQW0 : Q ≤ W := hQW.trans inf_le_left
  have hPE := isE27_bar d
  have hPW : bar d A ≤ Subgroup.normalizer (↑(bar d W) : Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)) := by
    intro x hx
    obtain ⟨a, haLR, haA, rfl⟩ := (mem_bar d).mp hx
    rw [rho_mk_of_mem d haLR (hAL' haA)]
    exact pi_mem_normalizer_bar d (hAL' haA) (hAW haA)
  have hQinv : bar d Q ∈ invariantPiSubgroups ⊤ (bar d A) (piCompl 3) := by
    refine ⟨le_top, ?_, ?_⟩
    · intro q hq3
      have hQ3 : ¬ 3 ∣ Nat.card Q := fun h3 => (hQ.2.1 ⟨3, Nat.prime_three⟩ h3) rfl
      have := card_bar_dvd d hQLR
      show (q : ℕ) ≠ 3
      intro hq3'
      exact hQ3 ((hq3' ▸ hq3).trans this)
    · intro x hx
      obtain ⟨a, haLR, haA, rfl⟩ := (mem_bar d).mp hx
      rw [rho_mk_of_mem d haLR (hAL' haA)]
      exact pi_mem_normalizer_bar d (hAL' haA) (hQ.2.2 haA)
  have hQcomm : bar d Q = ⁅bar d Q, bar d A⁆ := by
    rw [← bar_commutator d hQLR d.le_sup, ← hQA]
  have hQC : bar d Q ≤ bar d W ⊓
      Subgroup.centralizer (↑(bar d B) : Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)) := by
    refine le_inf (bar_mono d hQW0) ?_
    intro x hx
    obtain ⟨q, hqLR, hqQ, rfl⟩ := (mem_bar d).mp hx
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    obtain ⟨β, hβLR, hβB, rfl⟩ := (mem_bar d).mp hy
    have hcomm : β * q = q * β := Subgroup.mem_centralizer_iff.mp (hQW hqQ).2 β hβB
    change rho d ⟨β, hβLR⟩ * rho d ⟨q, hqLR⟩ = rho d ⟨q, hqLR⟩ * rho d ⟨β, hβLR⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hcomm
  have hnotcore := not_bar_le_core d hWLR hQW0 hQW'
  obtain ⟨T', hT'mem, hPT, h3, hgen⟩ := h (↥L ⧸ aschbacherSolvableCore 3 ↥L) hq.1 hT
    (kList46_thetaQuot hKL) (bar d A) (bar d W) (bar d Q) (bar d B) hPE hPW
    (isHyperplane_bar d hB) (center_le_bar d hB.1 hbB) hQC hQinv hQcomm
    (fun hbot => hnotcore (hbot ▸ bot_le)) (sig_bar d hWLR hAW hsig) hnotcore
  have hTperf : Group.IsPerfect ↥T' := isPerfect_of_mem_thetaComponentsIn hT'mem
  have hsolT : Group.IsSolvable ↥(T' ⊓
      Subgroup.centralizer (↑(bar d A) : Set (↥L ⧸ aschbacherSolvableCore 3 ↥L))) := by
    have hp := IsPGroup.to_le (ThreeGroup.isPGroup_centralizer hq.1 hT hPE) (inf_le_right :
      T' ⊓ Subgroup.centralizer (↑(bar d A) : Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)) ≤ _)
    have := hp.isNilpotent
    infer_instance
  have hΔ := PointSig.le_sSup_signalizers (A := bar d A) (K := T')
    (S := {p | p ∈ bar d A ∧ p ∉ Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L)}) hPE
    (fun p hp => hp.1) hPT hTperf
    (hgen.trans (iSup_le fun p => iSup_le fun h1 => iSup_le fun h2 =>
      le_iSup₂_of_le p ⟨h1, h2⟩ le_rfl)) hsolT
  exact exists_component_of_image d hWLR hAW hT'mem hPT h3 hΔ hsolL

variable {G : Type} [Group G] [Finite G]

theorem isList46_of_perfect_le_centralizer (h46 : Sec4.Item4_6) (hG : TheoremFourHyp G)
    {b : G} (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1) {J : Subgroup G}
    (hJb : J ≤ Subgroup.centralizer ({b} : Set G)) (hJp : Group.IsPerfect J)
    (hJq : IsQuasisimple (↥J ⧸ aschbacherSolvableCore 3 ↥J)) :
    Sec4.IsList46 (↥J ⧸ aschbacherSolvableCore 3 ↥J) := by
  set C := Subgroup.centralizer ({b} : Set G) with hC
  have hbC : b ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  set H := J ⊔ Subgroup.zpowers b with hH
  have hHC : H ≤ C := sup_le hJb (Subgroup.zpowers_le.mpr hbC)
  have hH4 : SectionFourHyp ↥H := hG.sectionFourHyp (fun h => by
    have : (⊤ : Subgroup G) ≤ C := h ▸ hHC
    exact Sec6.centralizer_ne_top_of_ne_one hG hb1 (top_le_iff.mp this))
  set b' : H := ⟨b, Subgroup.mem_sup_right (Subgroup.mem_zpowers b)⟩ with hb'
  have hb'Z : b' ∈ Subgroup.center H := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hHC g.2))
  have hb'o : orderOf b' = 3 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime hb3 hb1
  have h3 : 3 ∣ Nat.card (Subgroup.center H) := by
    rw [← hb'o, show orderOf b' = orderOf (⟨b', hb'Z⟩ : Subgroup.center H) from
      (Subgroup.orderOf_mk b' hb'Z).symm]
    exact orderOf_dvd_natCard _
  have hbJ : b ∈ Subgroup.centralizer (J : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    exact Subgroup.mem_centralizer_singleton_iff.mp (hJb hj)
  have hJn : H ≤ Subgroup.normalizer (J : Set G) :=
    sup_le Subgroup.le_normalizer
      ((Subgroup.zpowers_le).mpr (Subgroup.centralizer_le_normalizer _ hbJ))
  have hJH : J ∈ thetaComponentsIn H :=
    Sec6.mem_thetaComponentsIn_of le_sup_left hJp
      (Subgroup.Normal.isSubnormal ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        hJn)) hJq
  obtain ⟨hJH', hmem⟩ := mem_thetaComponentsIn_iff.mp hJH
  exact Sec21.Item223PrintProof.isList46_of_mulEquiv
    (thetaQuotEquiv (Subgroup.subgroupOfEquivOfLe hJH'))
    (h46 H hH4 h3 (J.subgroupOf H) hmem)

namespace ONLocK

theorem exists_of_kfMaxK (h46 : Sec4.Item4_6) (hKF : KF148PointSigONMaxK) {A L : Subgroup G}
    {c : G} (h : Sec14Std G A c L)
    (h143 : Concl143 A (lB A)) {Y : Subgroup G} (hY : Y ∈ scriptY A)
    (hYB : ∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') {B : Subgroup G}
    (hB : IsHyperplane A B) {Q : Subgroup G} (hQ : Q ∈ scriptQZero A (lB A))
    (hQY : Q ≤ Y ⊓ Subgroup.centralizer (B : Set G)) {b : G} (hb : b ∈ B) (hb1 : b ≠ 1)
    (hbΩ : Subgroup.zpowers b ∉ omegaA A)
    (hQb : ¬ Q ≤ pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ({b} : Set G))) {X : Subgroup G}
    (hΔ : delta A (lB A) (Subgroup.centralizer ({b} : Set G)) =
      pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔
        pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊔ X)
    (hCX : Subgroup.centralizer ({b} : Set G) ≤
      Subgroup.normalizer
        ((pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔ X : Subgroup G) : Set G))
    (hX : X ∈ thetaComponentsAt 3 b)
    (hT : Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X) CFSG.Blueprint.NativeSporadic.ON)
    (hQX : Q ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔ X) :
    ∃ K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({b} : Set G)), K ≤ X ∧
      K ≤ sSup {V : Subgroup G | V ≤ K ∧ V ∈ invariantPiSubgroups ⊤ A (piCompl 3) ∧
        V = ⁅V, A⁆} := by
  have hbA : b ∈ A := hB.1 hb
  set C := Subgroup.centralizer ({b} : Set G) with hCdef
  set R := pPrimeCoreOf 3 C with hRdef
  have hRC : R ≤ C := pPrimeCoreOf_le 3 C
  have hCR : C ≤ Subgroup.normalizer (R : Set G) := le_normalizer_pPrimeCoreOf 3 C
  have hR3 : Nat.Coprime 3 (Nat.card R) := coprime_card_pPrimeCoreOf 3 C
  have hXC : X ≤ C := le_centralizer_of_mem_thetaComponentsAt hX
  have hAb : A ≤ C := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (h.toSec13Data.commute ha hbA)
  have h3X : 3 ∣ Nat.card X := by
    obtain ⟨hZ, ⟨-⟩⟩ := hT
    have h1 : Nat.card (Subgroup.center (↥X ⧸ aschbacherSolvableCore 3 ↥X)) ∣
        Nat.card (↥X ⧸ aschbacherSolvableCore 3 ↥X) := Subgroup.card_subgroup_dvd_card _
    rw [hZ] at h1
    exact h1.trans (Subgroup.card_quotient_dvd_card _)
  have hCXn : C ≤ Subgroup.normalizer (X : Set G) := fun g hg =>
    Res7ONPoint.le_normalizer_of_le_sup148 hX h3X hRC hCR hR3 hg (hCX hg)
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := hAb.trans hCXn
  have hRX : R ≤ Subgroup.normalizer (X : Set G) := hRC.trans hCXn
  set W := (Y ⊓ C) ⊓ (X ⊔ R) with hWdef
  have hWXR : W ≤ X ⊔ R := inf_le_right
  have hWC : W ≤ Y ⊓ C := inf_le_left
  have hXRn : C ≤ Subgroup.normalizer ((X ⊔ R : Subgroup G) : Set G) := fun g hg =>
    le_normalizer_sup (A := C) hCXn hCR hg
  have hAW : A ≤ Subgroup.normalizer (W : Set G) := fun a ha =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.inf_normalizer_le_normalizer_inf ⟨hY.2 ha, Subgroup.le_normalizer (hAb ha)⟩,
        hXRn (hAb ha)⟩
  have hCW : Y ⊓ C ≤ Subgroup.normalizer (W : Set G) := fun y hy =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hy, hXRn hy.2⟩
  have hQW : Q ≤ W ⊓ Subgroup.centralizer (B : Set G) := by
    have hQb' : Q ≤ C :=
      (hQY.trans inf_le_right).trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hb))
    exact le_inf (le_inf (le_inf (hQY.trans inf_le_left) hQb') (hQX.trans (sup_comm R X).le))
      (hQY.trans inf_le_right)
  have hXRΔ : X ⊔ R ≤ delta A (lB A) C := by
    rw [hΔ]
    exact sup_le le_sup_right (le_sup_left.trans le_sup_left)
  have hsig : ∀ H' : Subgroup G, IsHyperplane A H' → ∀ V : Subgroup G,
      V ≤ W ⊓ Subgroup.centralizer (H' : Set G) → V ∈ invariantPiSubgroups ⊤ A (piCompl 3) →
      V = ⁅V, A⁆ → V ≤ pPrimeCoreOf 3 (W ⊓ Subgroup.centralizer (H' : Set G)) := by
    intro H' hH' V hVWH hV hVA
    have hVΔ : V ≤ delta A (lB A) C := (hVWH.trans inf_le_left).trans (hWXR.trans hXRΔ)
    obtain ⟨Qs, hQs, hVQs⟩ := exists_le_mem_maxInvariantPiSubgroups
      (⟨hVΔ, hV.2.1, hV.2.2⟩ : V ∈ invariantPiSubgroups (delta A (lB A) C) A (piCompl 3))
    have hVq : V ∈ scriptQ A (lB A) :=
      mem_scriptQ_of_le (h143 b hbA hb1 hbΩ Qs hQs).1 hVQs hV.2.2
    have hVYH : V ≤ Y ⊓ Subgroup.centralizer (H' : Set G) :=
      le_inf (((hVWH.trans inf_le_left).trans hWC).trans inf_le_left) (hVWH.trans inf_le_right)
    have hVO : V ≤ pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer (H' : Set G)) :=
      (le_deltaZero ⟨hVq, hVA⟩ hVYH).trans (hYB H' hH')
    have hWHY : W ⊓ Subgroup.centralizer (H' : Set G) ≤ Y ⊓ Subgroup.centralizer (H' : Set G) :=
      inf_le_inf_right _ (hWC.trans inf_le_left)
    refine (le_inf hVO hVWH).trans (le_pPrimeCoreOf inf_le_right (fun g hg => ?_) ?_)
    · exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨le_normalizer_pPrimeCoreOf 3 _ (hWHY hg), Subgroup.le_normalizer hg⟩
    · exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
        (coprime_card_pPrimeCoreOf 3 _)
  have hQW' : ¬ Q ≤ pPrimeCoreOf 3 W := by
    intro hQO
    refine hQb (hQO.trans (le_pPrimeCoreOf ((pPrimeCoreOf_le 3 W).trans hWC)
      (fun g hg => normalizer_le_normalizer_pPrimeCoreOf 3 W (hCW hg))
      (coprime_card_pPrimeCoreOf 3 W)))
  have hKX : ∀ J : Subgroup G, J ≤ X → Group.IsPerfect J →
      IsQuasisimple (↥J ⧸ aschbacherSolvableCore 3 ↥J) →
      Sec4.IsList46 (↥J ⧸ aschbacherSolvableCore 3 ↥J) := fun J hJX hJp hJq =>
    isList46_of_perfect_le_centralizer h46 h.toTheoremFourHyp (h.isE27'.1.2 b hbA) hb1
      (hJX.trans hXC) hJp hJq
  obtain ⟨K, hK, hKX, hKgen⟩ := hKF G A X R W Q B b h.isE27' hbA hb1 hXC hAX hT
    (Sec6.isQuasisimple_of_mem_thetaComponentsAt hX)
    (fun x hx3 hxA => Sec4.mem_of_maximal_of_commute h.maximal_isElemAbelian hx3 hxA) hKX hR3
    (hXC.trans hCR) hRX (hAb.trans hCR) hWXR hAW hB hb hQW hQ.1.1 hQ.2 hsig hQW'
  have hsub : (W.subgroupOf (Y ⊓ C)).IsSubnormal :=
    Subgroup.Normal.isSubnormal ((Subgroup.normal_subgroupOf_iff_le_normalizer hWC).mpr hCW)
  exact ⟨K, Sec15.Proof1423.mem_thetaComponentsIn_of_isSubnormal hK hWC hsub, hKX, hKgen⟩

end ONLocK

theorem step148PointHJdONGenD_of_sigMaxK (h143 : Concl143S14) (h46 : Sec4.Item4_6)
    (hKF : KF148PointSigONMaxK) : Step148PointHJdONGenD := by
  intro G _ _ A c L h Y hY hs hYB B hB Q hQ hQY hall b hb hb1 hbΩ hQb b' d Lb hb'Ω hLb hJ2 hdA
    hd1 hdc hbbd hbd X hΔ hCX hX hT hQX
  exact Or.inl (ONLocK.exists_of_kfMaxK h46 hKF h (h143 G A c L h) hY hYB hB hQ hQY hb hb1 hbΩ
    hQb hΔ hCX hX hT hQX)

section Chain

set_option linter.unusedSectionVars false


theorem kf148PointSigONMaxK_of_oneLineK (h1 : KF148OneLineK) : KF148PointSigONMaxK :=
  kf148PointSigONMaxK_of_x27K (kf148PointX27K_of_coreComponentK
    (kf148CoreComponentK_of_oneLineK h1))

theorem step148PointHJdONGenD_of_oneLineK (h143 : Concl143S14) (h46 : Sec4.Item4_6)
    (h1 : KF148OneLineK) : Step148PointHJdONGenD :=
  step148PointHJdONGenD_of_sigMaxK h143 h46 (kf148PointSigONMaxK_of_oneLineK h1)

end Chain

end CFSG.RankThree.PartTwo.Sec14.Ronan148H
