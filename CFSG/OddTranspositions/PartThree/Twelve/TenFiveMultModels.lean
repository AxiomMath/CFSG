module

public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveMultBridge
public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveMultReflPair
public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveMultSimilar
public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveMultTransport
public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveMultTransportProj

public section

namespace CFSG.OddTranspositions.PartThree

open Matrix CFSG.Open

@[expose] def FiveSimilarTo (k : ℕ) (ε : Bool) {ι : Type} [Fintype ι] [DecidableEq ι]
    (Q₀ : (ι → ZMod 5) → ZMod 5) : Prop :=
  ∃ (S : (Fin (k + 1) → ZMod 5) ≃ₗ[ZMod 5] (ι → ZMod 5)) (ν : ZMod 5), ν ≠ 0 ∧
    ∀ v, Q₀ (S v) = ν * fiveForm k ε v v

theorem fiveSimilar_odd {k : ℕ} (hk : 4 ≤ k) (ε : Bool) {n : ℕ} (hn : k = 2 * n) :
    FiveSimilarTo k ε (StatedQuadOdd n (ZMod 5)) := by
  subst hn
  set ν : ZMod 5 := if ε then 4 else 2 with hνdef
  have hνne : ν ≠ 0 := by rw [hνdef]; cases ε <;> decide
  have hνα : ν * (if ε then 1 else 2) = -1 := by rw [hνdef]; cases ε <;> decide
  refine ⟨LinearEquiv.ofBijective (fiveOddMap n ν) ?_, ν, hνne, ?_⟩
  · exact (Fintype.bijective_iff_injective_and_card (fiveOddMap n ν)).mpr
      ⟨fiveOddMap_injective n hνne, card_odd n⟩
  · intro v
    simpa only [StatedQuadOdd, LinearEquiv.ofBijective_apply] using
      statedQuadOdd_fiveOddMap n ε ν hνα v

theorem fiveSimilar_plus {k : ℕ} (hk : 4 ≤ k) {n : ℕ} (hn : k + 1 = 2 * n) :
    FiveSimilarTo k true (StatedQuadPlus n (ZMod 5)) := by
  refine ⟨fivePlusEquiv hn, 1, one_ne_zero, ?_⟩
  intro v
  rw [one_mul]
  simpa only [StatedQuadPlus, fivePlusEquiv, LinearEquiv.ofBijective_apply,
    LinearMap.comp_apply] using statedQuadPlus_fivePlusMap hn v

theorem fiveSimilar_minus {k : ℕ} (hk : 4 ≤ k) {n : ℕ} (hn : k + 1 = 2 * n) :
    ∃ b c : ZMod 5, (∀ s : ZMod 5, s ^ 2 + b * s + c ≠ 0) ∧
      FiveSimilarTo k false (StatedQuadMinus n (ZMod 5) b c) := by
  refine ⟨0, 3, ?_, ?_⟩
  · decide
  · refine ⟨fiveMinusEquiv hn, 1, one_ne_zero, ?_⟩
    intro v
    rw [one_mul]
    simpa only [StatedQuadMinus, CFSG.MatrixModel.minusQuadCore, fiveMinusEquiv,
      LinearEquiv.ofBijective_apply, zero_mul, mul_zero, zero_add, add_zero] using
      statedQuadMinus_fiveMinusMap hn v

theorem fiveOmega_mulEquiv_of_similar (k : ℕ) (ε : Bool) {ι : Type} [Fintype ι] [DecidableEq ι]
    {Q₀ : (ι → ZMod 5) → ZMod 5} (S : (Fin (k + 1) → ZMod 5) ≃ₗ[ZMod 5] (ι → ZMod 5))
    {ν : ZMod 5} (hν : ν ≠ 0) (hS : ∀ v, Q₀ (S v) = ν * fiveForm k ε v v) :
    ∃ Θ : ↥(fiveOmega k ε) ≃* ↥(StatedOmega Q₀),
      (∀ (g : ↥(fiveOmega k ε)) (v : Fin (k + 1) → ZMod 5),
        ((Θ g : GL ι (ZMod 5)) : Matrix ι ι (ZMod 5)) *ᵥ S v =
          S (((g : GL (Fin (k + 1)) (ZMod 5)) :
            Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ v)) ∧
      ∀ g : ↥(fiveOmega k ε),
        (g : GL (Fin (k + 1)) (ZMod 5)) ∈ Subgroup.center (GL (Fin (k + 1)) (ZMod 5)) ↔
          (Θ g : GL ι (ZMod 5)) ∈ StatedScalars ι (ZMod 5) := by
  have hmap : Subgroup.map (glConj S) (fiveOmega k ε) = StatedOmega Q₀ := by
    unfold fiveOmega StatedOmega
    rw [Subgroup.map_commutator, fiveOrthogonal_glConj_map ε S hν hS]
    rfl
  let Θ : ↥(fiveOmega k ε) ≃* ↥(StatedOmega Q₀) :=
    (MulEquiv.subgroupMap (glConj S) (fiveOmega k ε)).trans (MulEquiv.subgroupCongr hmap)
  have hΘ : ∀ g : ↥(fiveOmega k ε),
      (Θ g : GL ι (ZMod 5)) = (glConj S) (g : GL (Fin (k + 1)) (ZMod 5)) := by
    intro g
    simp [Θ]
  refine ⟨Θ, ?_, ?_⟩
  · intro g v
    rw [hΘ g]
    exact glConj_mulVec S (g : GL (Fin (k + 1)) (ZMod 5)) v
  · intro g
    rw [hΘ g, StatedScalars, ← Matrix.GeneralLinearGroup.center_eq_range_scalar,
      ← Subgroup.map_center_eq (glConj S)]
    constructor
    · intro hg
      exact Subgroup.mem_map.mpr ⟨g, hg, rfl⟩
    · intro hg
      obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.mp hg
      rw [(glConj S).injective hxg] at hx
      exact hx

@[expose] def CentralKernelTwoGroup (X : Type) [Group X] : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (φ : Γ →* X), Function.Surjective φ →
    φ.ker ≤ Subgroup.center Γ → φ.ker ≤ commutator Γ → IsPGroup 2 φ.ker

theorem commutator_fiveProjective_mulEquiv_of_similar {k : ℕ} (hk : 4 ≤ k) (ε π : Bool)
    {ι : Type} [Fintype ι] [DecidableEq ι] {Q₀ : (ι → ZMod 5) → ZMod 5}
    (S : (Fin (k + 1) → ZMod 5) ≃ₗ[ZMod 5] (ι → ZMod 5)) {ν : ZMod 5} (hν : ν ≠ 0)
    (hS : ∀ v, Q₀ (S v) = ν * fiveForm k ε v v) :
    ∃ Ψ : ↥(commutator (fiveProjective k ε π)) ≃* StatedProj (StatedOmega Q₀),
      ∀ (g : fiveReflectionGroup k ε π)
        (hg : (QuotientGroup.mk g : fiveProjective k ε π) ∈ commutator (fiveProjective k ε π))
        (g₀ : ↥(StatedOmega Q₀)),
        (∀ v, ((g₀ : GL ι (ZMod 5)) : Matrix ι ι (ZMod 5)) *ᵥ S v =
          S (((g : GL (Fin (k + 1)) (ZMod 5)) : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ v)) →
        Ψ ⟨QuotientGroup.mk g, hg⟩ = (QuotientGroup.mk g₀ : StatedProj (StatedOmega Q₀)) := by
  obtain ⟨Θ, hΘ_mul, hΘ_scalar⟩ := fiveOmega_mulEquiv_of_similar k ε S hν hS
  refine ⟨psiProj hk ε π Θ hΘ_scalar, ?_⟩
  intro g hg g₀ hg₀
  obtain ⟨ω, z, hz, hg_eq⟩ := exists_eq_mul_center_of_mem_commutator hk ε π g hg
  have hq : (⟨QuotientGroup.mk g, hg⟩ : ↥(commutator (fiveProjective k ε π))) = qProj hk ε π ω := by
    apply Subtype.ext
    rw [coe_qProj]
    change (QuotientGroup.mk' (Subgroup.center (fiveReflectionGroup k ε π))) g =
      (QuotientGroup.mk' (Subgroup.center (fiveReflectionGroup k ε π))) (omegaIncl hk ε π ω)
    rw [hg_eq, map_mul,
      show (QuotientGroup.mk' (Subgroup.center (fiveReflectionGroup k ε π))) z = 1 from
        (QuotientGroup.eq_one_iff z).mpr hz, mul_one]
  rw [hq, psiProj_qProj]
  exact mk_theta_eq_mk_of_intertwine hk ε π S Θ hΘ_mul hz hg_eq hg₀

@[expose] def FiveInvolutionLiftCover (k : ℕ) (ε π : Bool) : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (ρ : Γ →* fiveProjective k ε π),
    ρ.range = commutator (fiveProjective k ε π) → commutator Γ = ⊤ →
    ρ.ker ≤ Subgroup.center Γ → Nat.card ρ.ker = 2 →
    ∀ {ra rb : fiveReflectionGroup k ε π},
      (ra : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflections k ε π →
      (rb : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflections k ε π → Commute ra rb → ra ≠ rb →
      (∃ x : Γ, ρ x = (QuotientGroup.mk (ra * rb) : fiveProjective k ε π) ∧ x * x = 1) →
      ∃ ψ : Γ ≃* ↥(commutator (fiveReflectionGroup k ε π)),
        ∀ g : Γ, ρ g =
          (QuotientGroup.mk (ψ g : fiveReflectionGroup k ε π) : fiveProjective k ε π)

@[expose] def modelReflect {ι : Type} (Q₀ : (ι → ZMod 5) → ZMod 5) (a v : ι → ZMod 5) :
    ι → ZMod 5 :=
  v - ((Q₀ (v + a) - Q₀ v - Q₀ a) * (Q₀ a)⁻¹) • a

@[expose] def IsModelReflectionPair {ι : Type} [Fintype ι] [DecidableEq ι]
    (Q₀ : (ι → ZMod 5) → ZMod 5) (g : GL ι (ZMod 5)) : Prop :=
  ∃ a b : ι → ZMod 5, Q₀ a ≠ 0 ∧ Q₀ b ≠ 0 ∧ IsSquare (Q₀ a * Q₀ b) ∧
    Q₀ (a + b) = Q₀ a + Q₀ b ∧
    ∀ v, (g : Matrix ι ι (ZMod 5)) *ᵥ v = modelReflect Q₀ a (modelReflect Q₀ b v)

@[expose] def ModelInvolutionCover {ι : Type} [Fintype ι] [DecidableEq ι]
    (Q₀ : (ι → ZMod 5) → ZMod 5) : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (ρ : Γ →* StatedProj (StatedOmega Q₀)),
    Function.Surjective ρ → commutator Γ = ⊤ → ρ.ker ≤ Subgroup.center Γ →
    Nat.card ρ.ker = 2 →
    ∀ g₀ : ↥(StatedOmega Q₀), IsModelReflectionPair Q₀ (g₀ : GL ι (ZMod 5)) →
      (∃ x : Γ, ρ x = (QuotientGroup.mk g₀ : StatedProj (StatedOmega Q₀)) ∧ x * x = 1) →
      ∃ ψ : Γ ≃* ↥(StatedOmega Q₀),
        ∀ g : Γ, ρ g = (QuotientGroup.mk (ψ g) : StatedProj (StatedOmega Q₀))

theorem fiveInvolutionLiftCover_of_similar {k : ℕ} (hk : 4 ≤ k) (ε π : Bool) {ι : Type}
    [Fintype ι] [DecidableEq ι] {Q₀ : (ι → ZMod 5) → ZMod 5} (hsim : FiveSimilarTo k ε Q₀)
    (hmodel : ModelInvolutionCover Q₀) : FiveInvolutionLiftCover k ε π := by
  obtain ⟨S, ν, hν, hS⟩ := hsim
  obtain ⟨Θ, hΘ1, -⟩ := fiveOmega_mulEquiv_of_similar k ε S hν hS
  obtain ⟨Ψ, hΨ⟩ := commutator_fiveProjective_mulEquiv_of_similar hk ε π S hν hS
  intro Γ _ _ ρ hρ hperf hker hcard ra rb ha hb hab hne hlift
  have hmem : ((ra * rb : fiveReflectionGroup k ε π) : GL (Fin (k + 1)) (ZMod 5)) ∈
      fiveOmega k ε :=
    mul_mem_fiveOmega_of_mem_fiveReflections hk ha hb
  let g0 : ↥(StatedOmega Q₀) :=
    Θ ⟨((ra * rb : fiveReflectionGroup k ε π) : GL (Fin (k + 1)) (ZMod 5)), hmem⟩
  have hg0S : ∀ v : Fin (k + 1) → ZMod 5,
      ((g0 : GL ι (ZMod 5)) : Matrix ι ι (ZMod 5)) *ᵥ S v =
        S (((ra * rb : fiveReflectionGroup k ε π) : GL (Fin (k + 1)) (ZMod 5)) *ᵥ v) := by
    intro v
    have h := hΘ1 ⟨((ra * rb : fiveReflectionGroup k ε π) : GL (Fin (k + 1)) (ZMod 5)),
      hmem⟩ v
    simpa [g0] using h
  obtain ⟨a, haQ, haπ, haeq⟩ := exists_eq_fiveReflOf ha
  obtain ⟨b, hbQ, hbπ, hbeq⟩ := exists_eq_fiveReflOf hb
  have hcomm : fiveReflOf k ε a * fiveReflOf k ε b =
      fiveReflOf k ε b * fiveReflOf k ε a := by
    rw [← haeq, ← hbeq]
    simpa only [Subgroup.coe_mul] using
      congrArg (fun x : fiveReflectionGroup k ε π => (x : GL (Fin (k + 1)) (ZMod 5))) hab
  have hne' : fiveReflOf k ε a ≠ fiveReflOf k ε b := by
    intro h
    exact hne (Subtype.ext (by rw [haeq, hbeq, h]))
  have horth : fiveForm k ε a b = 0 :=
    fiveForm_eq_zero_of_commute_fiveReflOf haQ hbQ hcomm hne'
  have hpair : IsModelReflectionPair Q₀ (g0 : GL ι (ZMod 5)) := by
    refine ⟨S a, S b, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hS]; exact mul_ne_zero hν haQ
    · rw [hS]; exact mul_ne_zero hν hbQ
    · rw [hS, hS]
      have hiff : IsSquare (fiveForm k ε a a) ↔ IsSquare (fiveForm k ε b b) :=
        haπ.trans hbπ.symm
      have hsq := isSquare_mul_of_isSquare_iff hiff
      have hν2 : IsSquare (ν * ν) := ⟨ν, by ring⟩
      have hmain := hν2.mul hsq
      rw [show ν * fiveForm k ε a a * (ν * fiveForm k ε b b) =
        (ν * ν) * (fiveForm k ε a a * fiveForm k ε b b) by ring]
      exact hmain
    · rw [← map_add, hS (a + b), hS a, hS b, fiveForm_add_add, horth]
      ring
    · intro v
      have hv := hg0S (S.symm v)
      rw [LinearEquiv.apply_symm_apply] at hv
      rw [hv, Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec, haeq, hbeq]
      have hinner : S (((fiveReflOf k ε b : GL (Fin (k + 1)) (ZMod 5))) *ᵥ S.symm v) =
          modelReflect Q₀ (S b) v := by
        rw [map_fiveReflOf_mulVec S hν hS hbQ, LinearEquiv.apply_symm_apply]
        rfl
      rw [map_fiveReflOf_mulVec S hν hS haQ, hinner]
      rfl
  let ρc : Γ →* ↥(commutator (fiveProjective k ε π)) :=
    ρ.codRestrict (commutator (fiveProjective k ε π)) (fun g => by
      rw [← hρ]; exact ⟨g, rfl⟩)
  let ρ' : Γ →* StatedProj (StatedOmega Q₀) := Ψ.toMonoidHom.comp ρc
  have hρ'ker_eq : ρ'.ker = ρ.ker := by simp [ρ', ρc]
  have hρ'surj : Function.Surjective ρ' := by
    intro y
    have hz : ((Ψ.symm y : ↥(commutator (fiveProjective k ε π))) : fiveProjective k ε π) ∈
        ρ.range := by
      rw [hρ]; exact (Ψ.symm y).2
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp hz
    refine ⟨g, ?_⟩
    have hρc : ρc g = Ψ.symm y := Subtype.ext hg
    show Ψ (ρc g) = y
    rw [hρc, MulEquiv.apply_symm_apply]
  have hlift' : ∃ x : Γ, ρ' x = (QuotientGroup.mk g0 : StatedProj (StatedOmega Q₀)) ∧
      x * x = 1 := by
    obtain ⟨x, hx, hx2⟩ := hlift
    have hg_mem : (QuotientGroup.mk (ra * rb) : fiveProjective k ε π) ∈
        commutator (fiveProjective k ε π) := by
      rw [← hρ, ← hx]; exact ⟨x, rfl⟩
    refine ⟨x, ?_, hx2⟩
    have hρcx : ρc x = ⟨(QuotientGroup.mk (ra * rb) : fiveProjective k ε π), hg_mem⟩ :=
      Subtype.ext hx
    show Ψ (ρc x) = (QuotientGroup.mk g0 : StatedProj (StatedOmega Q₀))
    rw [hρcx]
    exact hΨ (ra * rb) hg_mem g0 hg0S
  obtain ⟨ψ', hψ'⟩ := hmodel Γ ρ' hρ'surj hperf (by rw [hρ'ker_eq]; exact hker)
    (by rw [hρ'ker_eq]; exact hcard) g0 hpair hlift'
  have hmap : (commutator ↥(fiveReflectionGroup k ε π)).map
      (fiveReflectionGroup k ε π).subtype = fiveOmega k ε := by
    rw [← commutator_fiveReflectionGroup_eq_fiveOmega hk ε π]
    exact Subgroup.map_subtype_commutator _
  let eΩ : ↥(fiveOmega k ε) ≃* ↥(commutator ↥(fiveReflectionGroup k ε π)) :=
    ((Subgroup.equivMapOfInjective (commutator ↥(fiveReflectionGroup k ε π))
        (fiveReflectionGroup k ε π).subtype (fiveReflectionGroup k ε π).subtype_injective).trans
      (MulEquiv.subgroupCongr hmap)).symm
  let ψ : Γ ≃* ↥(commutator (fiveReflectionGroup k ε π)) := (ψ'.trans Θ.symm).trans eΩ
  have heΩ : ∀ x : ↥(commutator ↥(fiveReflectionGroup k ε π)),
      ((eΩ.symm x : ↥(fiveOmega k ε)) : GL (Fin (k + 1)) (ZMod 5)) =
        ((x : fiveReflectionGroup k ε π) : GL (Fin (k + 1)) (ZMod 5)) := by
    intro x
    simp only [eΩ, MulEquiv.symm_symm, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
      Subgroup.coe_equivMapOfInjective_apply, Subgroup.coe_subtype]
  have hψ'g : ∀ g : Γ, ψ' g = Θ (eΩ.symm (ψ g)) := by
    intro g
    simp only [ψ, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply]
  refine ⟨ψ, fun g => ?_⟩
  have hmapQ : (commutator ↥(fiveReflectionGroup k ε π)).map
      (QuotientGroup.mk' (Subgroup.center (fiveReflectionGroup k ε π))) =
      commutator (fiveProjective k ε π) := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
    rfl
  have hg_mem2 : (QuotientGroup.mk ((ψ g : ↥(commutator (fiveReflectionGroup k ε π))) :
      fiveReflectionGroup k ε π) : fiveProjective k ε π) ∈
      commutator (fiveProjective k ε π) := by
    rw [← hmapQ]; exact ⟨ψ g, (ψ g).2, rfl⟩
  have hcompat : ∀ v, ((Θ (eΩ.symm (ψ g)) : GL ι (ZMod 5)) :
      Matrix ι ι (ZMod 5)) *ᵥ S v =
        S ((((ψ g : ↥(commutator (fiveReflectionGroup k ε π))) :
          fiveReflectionGroup k ε π) : GL (Fin (k + 1)) (ZMod 5)) *ᵥ v) := by
    intro v
    have h := hΘ1 (eΩ.symm (ψ g)) v
    simpa only [heΩ (ψ g)] using h
  have hΨapply : Ψ ⟨(QuotientGroup.mk ((ψ g : ↥(commutator (fiveReflectionGroup k ε π))) :
      fiveReflectionGroup k ε π) : fiveProjective k ε π), hg_mem2⟩ =
      (QuotientGroup.mk (Θ (eΩ.symm (ψ g))) : StatedProj (StatedOmega Q₀)) :=
    hΨ ((ψ g : ↥(commutator (fiveReflectionGroup k ε π))) : fiveReflectionGroup k ε π)
      hg_mem2 (Θ (eΩ.symm (ψ g))) hcompat
  have hΨρc : Ψ (ρc g) = (QuotientGroup.mk (Θ (eΩ.symm (ψ g))) :
      StatedProj (StatedOmega Q₀)) := by
    have h := hψ' g
    rw [hψ'g g] at h
    exact h
  have hthis : (⟨(QuotientGroup.mk ((ψ g : ↥(commutator (fiveReflectionGroup k ε π))) :
      fiveReflectionGroup k ε π) : fiveProjective k ε π), hg_mem2⟩ :
      ↥(commutator (fiveProjective k ε π))) = ρc g := by
    apply Ψ.injective
    rw [hΨapply, hΨρc]
  exact (Subtype.ext_iff.mp hthis).symm

end CFSG.OddTranspositions.PartThree
