module

public import CFSG.LocalAnalysis.StandardType.GGTCJDivDefs
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnSymp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GNegBCSymp
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympInnerExport
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSL
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSU
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GCenterQuot
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinCore
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.StandardType.TCJ

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.Y10F
  CFSG.LocalAnalysis.GLTheoremA.Y10GField
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LieType.SemisimpleCentralizers.Held (heldSU)
open CFSG.LocalAnalysis.GLTheoremA.Y10GInnSympMark
open CFSG.LocalAnalysis.GLTheoremA.Y10GInnSympRed
open CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin
open CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni
open CFSG.LocalAnalysis.GLTheoremA.Y10GSympLabel
open CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot

theorem tcjSymp_quotCenter_cases_of_component_conj {m n p : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n) (hm : 1 ≤ m) (hp : p.Prime) (hp2 : p ≠ 2)
    (x : StatedSp m K) (hx : x ^ p = 1) {J : Subgroup (StatedProj (StatedSp m K))}
    (hJ : CFSG.Open.IsComponentOf J (fixSubgroup (MulAut.conj (proj m K x)))) :
    (∃ (a k : ℕ) (E : Type) (_ : Field E) (_ : Finite E), 2 ≤ a ∧ Nat.card E = 2 ^ k ∧
        n ∣ k ∧ Nonempty (↥J ⧸ Subgroup.center ↥J ≃* StatedProj (StatedSL a E))) ∨
      (∃ (a k : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (τ : E ≃+* E)
          (hτ : ∀ y, τ (τ y) = y), 2 ≤ a ∧ (∀ y, τ y = y ^ (2 ^ k)) ∧
          Nat.card E = (2 ^ k) ^ 2 ∧ n ∣ k ∧
          Nonempty (↥J ⧸ Subgroup.center ↥J ≃*
            ↥(heldSU a E τ hτ) ⧸ Subgroup.center ↥(heldSU a E τ hτ))) ∨
      (∃ s : ℕ, 2 ≤ s ∧ ¬(s = 2 ∧ Nat.card K = 2) ∧
        Nonempty (↥J ⧸ Subgroup.center ↥J ≃* StatedProj (StatedSp s K))) ∨
      Nat.card K = 2 := by
  rcases CFSG.LocalAnalysis.GLTheoremA.Y10GNegBC.quotCenter_cases_symp_of_component
      hK hn hm hp hp2 x hx hJ with hlin | huni | hsp | ⟨hK2, -⟩
  · exact Or.inl hlin
  · exact Or.inr (Or.inl huni)
  · exact Or.inr (Or.inr (Or.inl hsp))
  · exact Or.inr (Or.inr (Or.inr hK2))

theorem tcjSymp_isComponentOf_map {S R : Type} [Group S] [Group R] (e : S ≃* R) (α : MulAut S)
    {J : Subgroup S} (hJ : CFSG.Assembly.IsComponentOf J (fixSubgroup α)) :
    CFSG.Assembly.IsComponentOf (J.map e.toMonoidHom) (fixSubgroup (MulAut.congr e α)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← CFSG.LocalAnalysis.GLTheoremA.Y10F.fixSubgroup_map_congr e α]
    exact Subgroup.map_mono hJ.1
  · rw [← CFSG.LocalAnalysis.GLTheoremA.Y10F.fixSubgroup_map_congr e α]
    exact CFSG.Assembly.IsSubnormal.map e.toMonoidHom hJ.2.1
  · exact CFSG.Assembly.IsQuasisimple.of_mulEquiv
      (Subgroup.equivMapOfInjective J e.toMonoidHom e.injective).symm hJ.2.2

theorem tcjSymp_innDiagAllSymp_of_ggLabelRigidInput (hRig : GGLabelRigidInput) :
    InnDiagAllOn FamSymp := by
  intro S _ _ p α J labK labJ hFam hp hp2 hcen hin hα hlabJ hJ
  rcases innDiagKind_symp_data hcen hFam hin with h1 |
    ⟨K, hK, hKf, m, hm, hcard, e, A, hαA⟩
  · rw [h1]
    exact one_dvd _
  have hn : 1 ≤ (canonLabel labK).n := by
    rcases Nat.eq_zero_or_pos (canonLabel labK).n with h0 | h0
    · exfalso
      rw [h0, pow_zero] at hcard
      have : 1 < Nat.card K := Finite.one_lt_card
      omega
    · exact h0
  have h2 : (2 : K) = 0 := by
    haveI := Fintype.ofFinite K
    obtain ⟨q, hq, k, hqp, hqcard⟩ := FiniteField.card' K
    have hc := hcard
    rw [Nat.card_eq_fintype_card, hqcard] at hc
    have hdvd : q ∣ 2 ^ (canonLabel labK).n := by
      rw [← hc]
      exact dvd_pow_self q (PNat.ne_zero k)
    have hq2 : q = 2 :=
      (Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).mp (hqp.dvd_of_dvd_pow hdvd)
    subst hq2
    exact_mod_cast CharP.cast_eq_zero K 2
  obtain ⟨x, hx⟩ := exists_conjAut_eq_conj h2 A
  have hMEq : MulAut.congr e α = MulAut.conj (proj m K x) := by
    rw [← hx]
    ext r
    have h1 := hαA (e.symm r)
    rw [MulEquiv.apply_symm_apply] at h1
    exact h1
  have hZ : Subgroup.center (StatedProj (StatedSp m K)) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : e.symm z ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro g
      apply e.injective
      simp only [map_mul, MulEquiv.apply_symm_apply]
      exact hz (e g)
    rw [hcen, Subgroup.mem_bot] at hz'
    rw [Subgroup.mem_bot]
    simpa using congrArg e hz'
  have hpow : MulAut.conj (proj m K x) ^ p = 1 := by
    rw [← hMEq, ← map_pow, hα, map_one]
  have hxp : x ^ p = 1 := pow_eq_one_of_conj_pow_eq_one h2 hZ hpow
  have hJ' : CFSG.Assembly.IsComponentOf (J.map e.toMonoidHom)
      (fixSubgroup (MulAut.conj (proj m K x))) := by
    rw [← hMEq]
    exact tcjSymp_isComponentOf_map e α hJ
  have hlabJ' := hasLabel_transport e hlabJ
  rcases tcjSymp_quotCenter_cases_of_component_conj hcard hn (by omega) hp hp2 x hxp
      (CFSG.Assembly.isComponentOf_iff_open.1 hJ') with
    ⟨a, k, E, _, _, ha, hE, hnk, hφ⟩ | ⟨a, k, E, _, _, τ, hτ, ha, hτk, hE, hnk, hφ⟩ |
      ⟨s, hs, hne, ⟨φ⟩⟩ | hK2
  ·
    rw [linLabelDict_of_ggLabelRigidInput hRig _ labJ a k E ha hE hlabJ' hφ]
    exact hnk
  ·
    rw [uniLabelDict_of_ggLabelRigidInput hRig _ labJ a k E τ hτ ha hτk hE hlabJ' hφ]
    exact hnk
  ·
    rw [canonLabel_eq_of_quot_statedSp hRig hs hcard hne hlabJ' φ]
  ·
    have h1 : (canonLabel labK).n = 1 := by
      have h : 2 ^ (canonLabel labK).n = 2 ^ 1 := by rw [← hcard, hK2, pow_one]
      exact Nat.pow_right_injective le_rfl h
    rw [h1]
    exact one_dvd _

theorem innDiagAllSymp :
    InnDiagAllOn FamSymp :=
  tcjSymp_innDiagAllSymp_of_ggLabelRigidInput ggLabelRigidInput_holds

end CFSG.StandardType.TCJ

end
