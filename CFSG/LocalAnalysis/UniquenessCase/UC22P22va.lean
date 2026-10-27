module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront05
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rc
import CFSG.LocalAnalysis.UniquenessCase.UC22P22uh
import CFSG.GroupTheory.LocalCores.FittingNormal
import CFSG.LocalAnalysis.SectionRank.TwoGenerators
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

private theorem uc22p22va_exists_noncyclic_sylow {F : Type*} [Group F] [Finite F] [Group.IsNilpotent F]
    (hnc : ¬ IsCyclic F) : ∃ q : ℕ, q.Prime ∧ ∃ S : Sylow q F, ¬ IsCyclic ↥(S : Subgroup F) := by
  by_contra h
  haveI : IsZGroup F := ⟨fun q hq S => by_contra fun hS => h ⟨q, hq, S, hS⟩⟩
  exact hnc inferInstance

private theorem uc22p22va_exists_normal_noncyclic {H : Type} [Group H] [Finite H]
    (hF : ¬ IsCyclic ↥(CFSG.fittingSubgroup ↥(_root_.commutator H))) :
    ∃ (q : ℕ) (R : Subgroup H), q.Prime ∧ R.Normal ∧ IsPGroup q ↥R ∧ ¬ IsCyclic ↥R ∧
      R ≤ _root_.commutator H := by
  classical
  set N : Subgroup H := _root_.commutator H
  set F : Subgroup H := N ⊓ CFSG.fittingSubgroup H
  have hFcyc : ¬ IsCyclic ↥F := by
    intro hc
    have h := CFSG.LocalCores.fitting_normal_intersection N
    let e : ↥(CFSG.fittingSubgroup ↥N) ≃* ↥F :=
      ((CFSG.fittingSubgroup ↥N).equivMapOfInjective N.subtype N.subtype_injective).trans
        (MulEquiv.subgroupCongr h)
    exact hF (isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective)
  haveI hFn : F.Normal := inferInstance
  haveI hFnil : Group.IsNilpotent ↥F := by
    haveI : Group.IsNilpotent ↥(CFSG.fittingSubgroup H) := inferInstance
    exact Group.nilpotent_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (inf_le_right : F ≤ CFSG.fittingSubgroup H))
  obtain ⟨q, hq, S, hS⟩ := uc22p22va_exists_noncyclic_sylow hFcyc
  haveI : Fact q.Prime := ⟨hq⟩
  have hle : (S : Subgroup ↥F).map F.subtype ≤ CFSG.pCore q H := Sylow.map_le_pCore hFn hFnil q S
  refine ⟨q, CFSG.pCore q H ⊓ N, hq, inferInstance, (CFSG.pCore_isPGroup).to_le inf_le_left, ?_,
    inf_le_right⟩
  intro hRc
  have hSR : (S : Subgroup ↥F).map F.subtype ≤ CFSG.pCore q H ⊓ N :=
    le_inf hle ((Subgroup.map_subtype_le _).trans inf_le_left)
  haveI := hRc
  haveI : IsCyclic ↥((S : Subgroup ↥F).map F.subtype) := Subgroup.isCyclic_of_le hSR
  exact hS (isCyclic_of_surjective
    ((S : Subgroup ↥F).equivMapOfInjective F.subtype F.subtype_injective).symm.toMonoidHom
    (MulEquiv.surjective _))

theorem uc22p22va_exists_minimal_calQ {Hh : Type} [Group Hh] [Finite Hh]
    (hO2 : CFSG.pCore 2 Hh = ⊥)
    (hF : ¬ IsCyclic ↥(CFSG.fittingSubgroup ↥(_root_.commutator Hh))) :
    ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ∈ F05.alphaSet Hh ∧ ∃ P ∈ F05.calQ (G := Hh) q,
      ∀ Q : Subgroup Hh, Q ≤ P → Q.Normal → 1 < CFSG.Open.pRank q Q → Q = P := by
  classical
  obtain ⟨q, R, hq, hRn, hRq, hRnc, hRN⟩ := uc22p22va_exists_normal_noncyclic hF
  have hq2 : q ≠ 2 := by
    rintro rfl
    have hRbot : R ≤ ⊥ := hO2 ▸ le_sSup ⟨hRn, hRq⟩
    exact hRnc (Subgroup.isCyclic_of_le hRbot)
  haveI := hRn
  obtain ⟨P₀, hP₀R, hP₀n, hP₀exp, hP₀cl, hP₀nc, -⟩ := uc22p22r_exists_omega_two hq hq2 R hRq hRnc
  have hRN' : R ≤ ⁅(⊤ : Subgroup Hh), (⊤ : Subgroup Hh)⁆ := by
    rw [← _root_.commutator_def]; exact hRN
  have hP₀Q : P₀ ∈ F05.calQ (G := Hh) q :=
    ⟨hP₀n, hP₀nc, hRq.to_le hP₀R, hP₀exp, hP₀cl, hP₀R.trans hRN'⟩
  have hqα : q ∈ F05.alphaSet Hh := by
    refine ⟨hq, ?_⟩
    have h2 : 2 ≤ CFSG.Open.pRank q R := uc22p22u_two_le_pRank hq hq2 hRq hRnc
    have hsub : R.subgroupOf ⁅(⊤ : Subgroup Hh), (⊤ : Subgroup Hh)⁆ ≤
        CFSG.pCore q ↥⁅(⊤ : Subgroup Hh), (⊤ : Subgroup Hh)⁆ := by
      refine le_sSup ⟨Subgroup.normal_subgroupOf, ?_⟩
      exact hRq.of_injective (Subgroup.subgroupOfEquivOfLe hRN').toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hRN').injective
    have hle : R ≤ pCoreOf q ⁅(⊤ : Subgroup Hh), (⊤ : Subgroup Hh)⁆ :=
      calc R = (R.subgroupOf ⁅(⊤ : Subgroup Hh), (⊤ : Subgroup Hh)⁆).map
            (⁅(⊤ : Subgroup Hh), (⊤ : Subgroup Hh)⁆).subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hRN').symm
        _ ≤ pCoreOf q ⁅(⊤ : Subgroup Hh), (⊤ : Subgroup Hh)⁆ := Subgroup.map_mono hsub
    exact lt_of_lt_of_le (by norm_num) (h2.trans (CFSG.SectionRank.pRank_mono hq.one_lt hle))
  have hne : ∃ n : ℕ, ∃ P ∈ F05.calQ (G := Hh) q, Nat.card ↥P = n := ⟨_, P₀, hP₀Q, rfl⟩
  obtain ⟨P, hP, hPn⟩ := Nat.find_spec hne
  refine ⟨q, hq, hq2, hqα, P, hP, fun Q hQP hQn hQr => ?_⟩
  have hQmem : Q ∈ F05.calQ (G := Hh) q := by
    obtain ⟨-, -, hPq, hPexp, hPcl, hPN⟩ := hP
    refine ⟨hQn, fun hc => absurd (CFSG.SectionRank.pRank_le_one_of_isCyclic hq hc) (not_le.2 hQr),
      hPq.to_le hQP, fun x hx => hPexp x (hQP hx), ?_, hQP.trans hPN⟩
    rw [eq_bot_iff, ← hPcl]
    exact Subgroup.commutator_mono (Subgroup.commutator_mono hQP hQP) hQP
  have hcard : Nat.card ↥P ≤ Nat.card ↥Q := hPn ▸ Nat.find_min' hne ⟨Q, hQmem, rfl⟩
  exact Subgroup.eq_of_le_of_card_ge hQP hcard

end CFSG.LocalAnalysis.UniquenessCase.UC22
