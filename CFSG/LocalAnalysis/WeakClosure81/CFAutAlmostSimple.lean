module

public import CFSG.LocalAnalysis.WeakClosure81.FourFiveHyp
public import CFSG.GroupTheory.Fitting.MulEquiv
public import CFSG.Quasithin.Vol2.Ch11SecBNPAut
import CFSG.GroupTheory.PCentralElement
import CFSG.GroupTheory.PGL2Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Shape
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem inFGroup_of_isPGL2_seven (h410 : W4Lem4_10) (Q : Type) [Group Q] [Finite Q]
    (hPGL : CFSG.Quasithin.F6.IsPGL2 7 Q) : InFGroup 1 Q := by
  classical
  obtain ⟨F, hF, hFfin, hFcard, ⟨eQ⟩⟩ := hPGL
  have hcs : Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) F) =
      CFSG.Open.StatedScalars (Fin 2) F := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    rfl
  let e : Q ≃* CFSG.GorensteinWalter.PGL2 F :=
    eQ.trans (QuotientGroup.quotientMulEquivOfEq hcs).symm
  have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F) := by
    rw [hFcard]
    exact ⟨7, 1, by norm_num, ⟨3, by norm_num⟩, by norm_num, by norm_num⟩
  have hcard : 3 < Nat.card F := by rw [hFcard]; norm_num
  let L' : Subgroup Q := commutator Q
  have hL'normal : L'.Normal := inferInstance
  obtain ⟨eL⟩ :=
    CFSG.GorensteinWalter.commutator_mulEquiv_psl2_of_mulEquiv_pgl2_card_gt_three
      F hodd hcard e
  have hsimple : IsSimpleGroup (CFSG.GorensteinWalter.PSL2 F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [hFcard]; norm_num)
  have hsimpleL : IsSimpleGroup ↥L' := (MulEquiv.isSimpleGroup_congr eL).mpr hsimple
  have hnabL : ∃ a b : ↥L', a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := CFSG.ABGLocalTools.psl2_exists_not_commute (K := F)
    exact ⟨eL.symm a, eL.symm b, fun h => hab (by simpa using congrArg eL h)⟩
  have hquasi : CFSG.IsQuasisimple ↥L' :=
    (@CFSG.LocalCores.isQuasisimple_of_isSimpleGroup ↥L' _ hsimpleL hnabL).1
  have hcomp : CFSG.IsComponent L' := ⟨hquasi, hL'normal.isSubnormal⟩
  have hL'map : L'.map e.toMonoidHom =
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
    have h1 : L'.map e.toMonoidHom = commutator (CFSG.GorensteinWalter.PGL2 F) := by
      rw [show L' = commutator Q from rfl,
        show commutator Q = ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ from rfl,
        Subgroup.map_commutator, Subgroup.map_top,
        MonoidHom.range_eq_top.mpr e.surjective]
      rfl
    rw [h1, CFSG.GorensteinWalter.pgl2_commutator_eq_psl2_range_of_card_gt_three
      F hodd hcard]
  have hcentL' : Subgroup.centralizer (L' : Set Q) = ⊥ := by
    have hle := CFSG.GorensteinWalter.centralizer_map_le_of_mulEquiv e L'
      (Subgroup.centralizer (L' : Set Q)) le_rfl
    rw [hL'map, CFSG.GorensteinWalter.pgl2_psl2Range_centralizer_eq_bot F hodd] at hle
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp (le_bot_iff.mp hle)
  have hFstar : Fstar (⊤ : Subgroup Q) = L' := by
    have hgen := CFSG.Quasithin.Vol2.Ch11.SecB.generalizedFitting_eq_of_component
      (G := Q) L' hcomp hcentL'
    unfold Fstar
    rw [CFSG.Adapters.genFittingFStar_eq_foundations, ← hgen]
    exact CFSG.WholeGroup.generalizedFitting_map_mulEquiv (Subgroup.topEquiv (G := Q))
  obtain ⟨T⟩ := Sylow.nonempty (p := 2) (G := Q)
  have hL'card : Nat.card ↥L' = 168 := by
    rw [Nat.card_congr eL.toEquiv, CFSG.GorensteinWalter.psl2_card_formula F hodd, hFcard]
    norm_num
  have hQcard : Nat.card Q = 336 := by
    rw [Nat.card_congr e.toEquiv, CFSG.GorensteinWalter.pgl2_card_formula F, hFcard]
    norm_num
  have hquot2 : IsPGroup 2 (Q ⧸ L') := by
    have hindex : L'.index = 2 := by
      have hmul := L'.index_mul_card
      rw [hQcard, hL'card] at hmul
      omega
    have hcardq : Nat.card (Q ⧸ L') = 2 := by
      rw [← Subgroup.index_eq_card]
      exact hindex
    exact IsPGroup.of_card (n := 1) (by rw [hcardq]; norm_num)
  have hLT : L' ⊔ (T : Subgroup Q) = ⊤ :=
    CFSG.OrderReductions.PrimeQuotientFrattini.kernel_sup_sylow_eq_top 2 L' hquot2 T
  have hF6L' : F6.IsL2 7 1 ↥L' := by
    refine ⟨⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩,
      F, hF, hFfin, ?_, ?_⟩
    · rw [hFcard]; norm_num
    · exact ⟨eL.trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F)⟩
  have hTsylIn : CFSG.Quasithin.IsSylowIn 2 (T : Subgroup Q) ⊤ :=
    CFSG.Quasithin.isSylowIn_top T
  have hFconcl := h410 Q L' (T : Subgroup Q) 7 hL'normal hFstar
    ⟨7, 1, by norm_num, by norm_num, by norm_num, hF6L'⟩ (by norm_num) (by norm_num)
    hTsylIn hLT
  rcases hFconcl with hF | hAlt | ⟨hsmall, -⟩
  · exact hF
  · exact absurd hAlt
      (CFSG.LocalAnalysis.WeakClosure81.not_isAlt_five_of_isL2_odd
        (p := 7) (e := 1) (by norm_num) (by norm_num) (by norm_num) hF6L')
  · rcases hsmall with hL27 | hL29 | hSym
    · exfalso
      have h2 := CFSG.LocalAnalysis.WeakClosure81.two_mul_card_isL2_odd
        (p := 7) (e := 1) (by norm_num) (by norm_num) hL27
      omega
    · exfalso
      have h2 := CFSG.LocalAnalysis.WeakClosure81.two_mul_card_isL2_odd
        (p := 3) (e := 2) (by norm_num) (by norm_num) hL29
      omega
    · exfalso
      obtain ⟨eSym⟩ := hSym
      have h720 : Nat.card Q = 720 := by
        rw [Nat.card_congr eSym.toEquiv, Nat.card_perm, Nat.card_fin]
        norm_num
      omega

@[expose] def CFAutInFGroupPGL2 (Q : Type) [Group Q] [Finite Q] (S : Subgroup Q) : Prop :=
  ∀ X : Subgroup Q, X.Normal → X ≠ ⊥ →
    (∀ N : Subgroup Q, N.Normal → N ≤ X → N = ⊥ ∨ N = X) → ¬ IsMulCommutative X →
    ∀ L : Subgroup Q, CFSG.Open.IsComponentOf L X →
      ∃ h : ((CFSG.LocalAnalysis.UniquenessCase.UC22.F12.autC S L).subgroupOf
          (CFSG.LocalAnalysis.UniquenessCase.UC22.F12.autNL S L)).Normal,
        haveI := h
        CFSG.Quasithin.F6.IsPGL2 7
          (↥(CFSG.LocalAnalysis.UniquenessCase.UC22.F12.autNL S L) ⧸
            (CFSG.LocalAnalysis.UniquenessCase.UC22.F12.autC S L).subgroupOf
              (CFSG.LocalAnalysis.UniquenessCase.UC22.F12.autNL S L))

theorem CFAutInFGroupPGL2.map_mulEquiv {Q Q' : Type} [Group Q] [Finite Q]
    [Group Q'] [Finite Q'] (e : Q ≃* Q') {S : Subgroup Q} (h : CFAutInFGroupPGL2 Q S) :
    CFAutInFGroupPGL2 Q' (S.map e.toMonoidHom) := by
  intro X' hXn hXne hXmin hXnc L' hL'
  set X : Subgroup Q := X'.map e.symm.toMonoidHom with hXdef
  set L : Subgroup Q := L'.map e.symm.toMonoidHom with hLdef
  have hXmap : X.map e.toMonoidHom = X' := by
    rw [hXdef, Subgroup.map_map]
    have hcomp : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id Q' := by
      ext x
      simp
    rw [hcomp, Subgroup.map_id]
  have hLmap : L.map e.toMonoidHom = L' := by
    rw [hLdef, Subgroup.map_map]
    have hcomp : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id Q' := by
      ext x
      simp
    rw [hcomp, Subgroup.map_id]
  have hXnorm : X.Normal :=
    (MulEquiv.normal_map_iff (f := e.symm) (H := X')).mpr hXn
  have hXbot : X ≠ ⊥ := by
    intro hbot
    apply hXne
    rw [← hXmap, hbot, Subgroup.map_bot]
  have hXmin' : ∀ N : Subgroup Q, N.Normal → N ≤ X → N = ⊥ ∨ N = X := by
    intro N hNn hNle
    have hmaple : N.map e.toMonoidHom ≤ X' := by
      rw [← hXmap]
      exact Subgroup.map_mono hNle
    have hmapn : (N.map e.toMonoidHom).Normal := hNn.map e.toMonoidHom e.surjective
    rcases hXmin (N.map e.toMonoidHom) hmapn hmaple with hN | hN
    · left
      rwa [Subgroup.map_eq_bot_iff_of_injective (H := N) (f := e.toMonoidHom) e.injective] at hN
    · right
      have h' : N.map e.toMonoidHom = X.map e.toMonoidHom := by rw [hN, hXmap]
      exact (Subgroup.map_injective (f := e.toMonoidHom) e.injective).eq_iff.mp h'
  have hXnc' : ¬ IsMulCommutative ↥X := by
    intro hc
    apply hXnc
    exact (MulEquiv.subgroupMap e.symm X').symm.surjective.isMulCommutative hc
  have hLc : CFSG.Open.IsComponentOf L X := by
    rw [hLdef, hXdef]
    refine ⟨Subgroup.map_mono hL'.1, ?_, ?_⟩
    · exact CFSG.Open.IsSubnormal.map e.symm.toMonoidHom hL'.2.1
    · exact CFSG.Open.IsQuasisimple.of_mulEquiv
        (Subgroup.equivMapOfInjective L' e.symm.toMonoidHom e.symm.injective).symm hL'.2.2
  obtain ⟨hnorm, hPGL⟩ := h X hXnorm hXbot hXmin' hXnc' L hLc
  refine ⟨fourFive_normal_autC (S.map e.toMonoidHom) L', ?_⟩
  classical
  let φ := Classical.choice (fourFive_autQuot_equiv e S L)
  have hPGL' := CFSG.GroupTheory.isPGL2_of_mulEquiv φ.symm hPGL
  rwa [hLmap] at hPGL'

theorem cfAutInFGroup_of_isPGroup {p : ℕ} (hp : p.Prime) {Q : Type} [Group Q] [Finite Q]
    (hQ : IsPGroup p Q) (j : ℕ) (S : Subgroup Q) : CFAutInFGroup j Q S := by
  intro X hXn hXne hXmin hXnc L hL
  have : Fact p.Prime := ⟨hp⟩
  exact absurd (CFSG.isElementaryAbelian_of_minimalNormal hXn (hQ.to_subgroup X) hXne
    hXmin).toIsMulCommutative hXnc

theorem CFAutInFGroupPGL2.map_mulEquiv_eq {Q Q' : Type} [Group Q] [Finite Q]
    [Group Q'] [Finite Q'] (e : Q ≃* Q') {S : Subgroup Q} {S' : Subgroup Q'}
    (hS : Subgroup.map e.toMonoidHom S = S') (h : CFAutInFGroupPGL2 Q S) :
    CFAutInFGroupPGL2 Q' S' := by
  rw [← hS]
  exact h.map_mulEquiv e

end CFSG.LocalAnalysis.WeakClosure81
