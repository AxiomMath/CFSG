module

public import CFSG.RankThree.PartTwo.Sec12.Hering129D4HInner
public import CFSG.RankThree.PartTwo.Sec12.Hering129KModels

public section

namespace CFSG.RankThree.PartTwo.Sec12

namespace Hering129D4H

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.Blueprint
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


section Theta

variable {Y : Type} [Group Y] [Finite Y]

theorem theta_eq_bot_of_isG2D4 {r : TauCeti.PrimePower} {δ : ℕ} (h : IsG2D4 Y r δ) :
    aschbacherSolvableCore 3 Y = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI hS : IsSimpleGroup Y := Hering129KModels.isSimpleGroup_of_isG2D4 h
  haveI hP : Group.IsPerfect Y := Hering129KModels.isPerfect_of_isG2D4 h
  obtain ⟨hθsol, -, -, -, -, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := Y) Nat.prime_three
  rcases hS.eq_bot_or_eq_top_of_normal (aschbacherSolvableCore 3 Y) with h0 | h1
  · exact h0
  · exfalso
    haveI : Group.IsSolvable (aschbacherSolvableCore 3 Y) := hθsol
    haveI : Group.IsSolvable Y := by
      refine solvable_of_surjective (f := (aschbacherSolvableCore 3 Y).subtype) ?_
      intro y
      exact ⟨⟨y, by rw [h1]; trivial⟩, rfl⟩
    haveI : Nontrivial Y := hS.toNontrivial
    exact Group.IsPerfect.not_isSolvable Y ‹_›

end Theta

section Inner

variable {P : Type} [Group P] [Finite P] {Yh Bh : Subgroup P} {xh bh ch : P}

theorem not_inducesOuterTheta_of_d4 [Yh.Normal] (hD : HessData Yh Bh xh bh ch)
    {r : TauCeti.PrimePower} {hr : (TauCeti.LieTypeIndex.trialityD4 r).Valid} (hp : r.p = 2)
    (e : ↥Yh ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 r, hr⟩).Group) {β : P} (hβ : β ∈ Bh) :
    ¬ Sec4.InducesOuterTheta β Yh := by
  intro hout
  have hG : IsG2D4 ↥Yh r 3 := Or.inr ⟨rfl, hr, ⟨e⟩⟩
  have hθ := theta_eq_bot_of_isG2D4 hG
  let f : ↥Yh ⧸ aschbacherSolvableCore 3 ↥Yh ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 r, hr⟩).Group :=
    ((QuotientGroup.quotientMulEquivOfEq hθ).trans QuotientGroup.quotientBot).trans e
  obtain ⟨K, hK1, hK2, σ, hK, hσ, ⟨eK⟩⟩ := Hering129KModels.exists_d4_model f
  have hrc : r.card = 2 ^ r.exponent := by rw [TauCeti.PrimePower.card_def, hp]
  have hK' : Nat.card K = (2 ^ r.exponent) ^ 3 := by rw [hK, hrc]
  have hσ' : ∀ c, σ c = c ^ 2 ^ r.exponent := fun c => by rw [hσ c, hrc]
  have hf1 : 1 ≤ r.exponent := r.exponent_pos
  have he3 : β ^ 3 = 1 := hD.elem.2 β hβ
  exact (hD.inner β hβ).2 (KFacts.InducesStdKind.triality r.exponent hf1 K hK' σ hσ'
    (KFacts.inducesKindTriality_graphField hf1 hK' hσ' Yh he3 hout eK))

theorem le_innerSub_of_d4 [Yh.Normal] (hD : HessData Yh Bh xh bh ch)
    {r : TauCeti.PrimePower} {hr : (TauCeti.LieTypeIndex.trialityD4 r).Valid} (hp : r.p = 2)
    (e : ↥Yh ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 r, hr⟩).Group) : Bh ≤ innerSub Yh := by
  intro β hβ
  have hnot := not_inducesOuterTheta_of_d4 hD hp e hβ
  have hG : IsG2D4 ↥Yh r 3 := Or.inr ⟨rfl, hr, ⟨e⟩⟩
  have hθ := theta_eq_bot_of_isG2D4 hG
  have hx : β ∈ Subgroup.normalizer (Yh : Set P) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr ‹Yh.Normal›]
    exact Subgroup.mem_top _
  unfold Sec4.InducesOuterTheta at hnot
  push Not at hnot
  obtain ⟨q, hq⟩ := hnot hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨y, fun u => ?_⟩
  have h1 : MulAut.conj (y : ↥Yh ⧸ aschbacherSolvableCore 3 ↥Yh) (u : ↥Yh ⧸ _) =
      Sec4.thetaQuotMulAut ↥Yh (Sec4.compAction Yh ⟨β, hx⟩) (u : ↥Yh ⧸ _) := by rw [hq]
  rw [Sec4.thetaQuotMulAut_mk, MulAut.conj_apply] at h1
  have h2 : ((y * u * y⁻¹ : ↥Yh) : ↥Yh ⧸ aschbacherSolvableCore 3 ↥Yh) =
      ((Sec4.compAction Yh ⟨β, hx⟩ u : ↥Yh) : ↥Yh ⧸ aschbacherSolvableCore 3 ↥Yh) := by
    rw [← h1]
    simp
  have h3 := QuotientGroup.eq.mp h2
  rw [hθ, Subgroup.mem_bot, inv_mul_eq_one] at h3
  have h4 : ((Sec4.compAction Yh ⟨β, hx⟩ u : ↥Yh) : P) = β * (u : P) * β⁻¹ :=
    Sec4.normalizerMonoidHom_apply_coe hx u
  rw [← h4, ← h3]

theorem exists_act_of_d4 [Yh.Normal] (hD : HessData Yh Bh xh bh ch)
    {r : TauCeti.PrimePower} {hr : (TauCeti.LieTypeIndex.trialityD4 r).Valid} (hp : r.p = 2)
    (e : ↥Yh ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 r, hr⟩).Group) :
    Subgroup.center ↥Yh = ⊥ ∧ Nonempty (Act Yh Bh) := by
  have hG : IsG2D4 ↥Yh r 3 := Or.inr ⟨rfl, hr, ⟨e⟩⟩
  have hZ : Subgroup.center ↥Yh = ⊥ := Hering129KModels.center_eq_bot_of_isG2D4 hG
  obtain ⟨ψ, hψ⟩ := exists_innerAct hZ (le_innerSub_of_d4 hD hp e)
  exact ⟨hZ, ⟨⟨ψ, hψ⟩⟩⟩

theorem pairData_of_hess (hD : HessData Yh Bh xh bh ch) (hZ : Subgroup.center ↥Yh = ⊥)
    (a : Act Yh Bh) :
    PairData (⟨ch, hD.cY⟩ : ↥Yh) (a.ψ ⟨bh, bh_mem_sup hD⟩) := by
  obtain ⟨hc3, hy3, hyc, hc1, hy1⟩ := pair_facts hD hZ a
  refine ⟨hc3, hy3, hc1, hy1, hyc, ?_⟩
  obtain ⟨Xh, hXY, hXC, hperf, hsub, hcX, p, m, hp, h4, φ, hφ⟩ := hD.comp
  set y : ↥Yh := a.ψ ⟨bh, bh_mem_sup hD⟩ with hy
  have hcomm : ∀ u : ↥Yh, bh * (u : P) = (u : P) * bh ↔ y * u = u * y := by
    intro u
    have h1 : bh * (u : P) * bh⁻¹ = ((y * u * y⁻¹ : ↥Yh) : P) := a.conj ⟨bh, bh_mem_sup hD⟩ u
    constructor
    · intro h
      have h2 : bh * (u : P) * bh⁻¹ = (u : P) := by rw [h]; group
      rw [h2] at h1
      have h3 : y * u * y⁻¹ = u := Subtype.ext h1.symm
      calc y * u = (y * u * y⁻¹) * y := by group
        _ = u * y := by rw [h3]
    · intro h
      have h3 : y * u * y⁻¹ = u := by rw [h]; group
      rw [h3] at h1
      calc bh * (u : P) = (bh * (u : P) * bh⁻¹) * bh := by group
        _ = (u : P) * bh := by rw [h1]
  refine ⟨Xh.subgroupOf Yh, ?_, ?_, ?_, hcX, p, m, hp, h4, ?_⟩
  · intro u hu
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((hcomm u).mp (Subgroup.mem_centralizer_singleton_iff.mp (hXC hu)).symm).symm
  · haveI := hperf
    exact Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hXY).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hXY).symm.surjective
  ·
    let g : ↥(Subgroup.centralizer ({y} : Set ↥Yh)) →*
        ↥(Yh ⊓ Subgroup.centralizer ({bh} : Set P)) :=
      { toFun := fun u => ⟨((u : ↥Yh) : P), (u : ↥Yh).2,
          Subgroup.mem_centralizer_singleton_iff.mpr
            ((hcomm u).mpr (Subgroup.mem_centralizer_singleton_iff.mp u.2).symm).symm⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have heq : (Xh.subgroupOf Yh).subgroupOf (Subgroup.centralizer ({y} : Set ↥Yh)) =
        (Xh.subgroupOf (Yh ⊓ Subgroup.centralizer ({bh} : Set P))).comap g := by
      ext u
      rfl
    rw [heq]
    exact hsub.comap g
  · exact ⟨φ.comp (Subgroup.subgroupOfEquivOfLe hXY).toMonoidHom,
      hφ.comp (Subgroup.subgroupOfEquivOfLe hXY).surjective⟩

end Inner

end Hering129D4H

end CFSG.RankThree.PartTwo.Sec12
