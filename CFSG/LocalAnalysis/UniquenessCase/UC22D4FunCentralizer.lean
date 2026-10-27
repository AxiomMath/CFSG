module

public import CFSG.LocalAnalysis.UniquenessCase.FundamentalLie
public import CFSG.LocalAnalysis.UniquenessCase.FundamentalLieFunFamily
import CFSG.ClassicalInvolution.AschTight.S19GC2
import CFSG.ClassicalInvolution.AschTight.S19GD4Inv
public import CFSG.ClassicalInvolution.ModelFacts.G2D4TD4Chart
import CFSG.ClassicalInvolution.SmallCases.UpgradeCover
import CFSG.LocalAnalysis.UniquenessCase.FundamentalLieFunLowerBound
import CFSG.LocalAnalysis.UniquenessCase.UC22FunCountCommute
import CFSG.LocalAnalysis.UniquenessCase.UC22FunCountTwo
import CFSG.LieType.Steinberg.CentralExt.TrialityCoprime

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.ClassicalInvolution.Generic
open CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.G2D4Models
open CFSG.ClassicalInvolution.Disconnected.AschTight.S19F
open scoped MatrixGroups



theorem d4_funSet_eq_pair {X : Type} [Group X] [Finite X] [IsSimpleGroup X] {n p f : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .trialityD4 n p f)
    (hX : CFSG.Blueprint.LieModel X .trialityD4 n p f) (P : Sylow 2 X) :
    ∃ (hσ : ∀ c, iterateFrobenius (GaloisField p (3 * f)) p f
          (iterateFrobenius (GaloisField p (3 * f)) p f
            (iterateFrobenius (GaloisField p (3 * f)) p f c)) = c)
      (ψ : twistedGroup (iterateFrobenius (GaloisField p (3 * f)) p f) ≃* X),
      F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X) =
        {(slLong _ hσ).range.map ψ.toMonoidHom, (slB _ hσ).range.map ψ.toMonoidHom} := by
  have hp : p.Prime := Fact.out
  have hf : 1 ≤ f := hadm.2.1
  obtain ⟨hσ, -, -, -, -, -⟩ :=
    CFSG.ClassicalInvolution.Disconnected.AschTight.S19G.d4_model_data hp2 hf
  set σ := iterateFrobenius (GaloisField p (3 * f)) p f with hσdef
  obtain ⟨ψ, hψ, hker⟩ := CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover
    .trialityD4 n p f hp hp2 (by trivial) hadm X hX
  let A : Bool → Subgroup (modelUniv .trialityD4 n p f hp).K :=
    fun b => cond b (slLong σ hσ).range (slB σ hσ).range
  have hA : ∀ b, A b ∈ fundamentalSubgroups .trialityD4 (modelUniv .trialityD4 n p f hp).D := by
    have hrank : ∀ i, rankOne (modelUniv .trialityD4 n p f hp).D.rootGroup i ∈
        fundamentalSubgroups .trialityD4 (modelUniv .trialityD4 n p f hp).D := fun i =>
      ⟨1, Pi.single i 1, Or.inr (Or.inr ⟨rfl,
        CFSG.ClassicalInvolution.Balance.single_mem_roots _ i⟩), (conjSub_one _).symm⟩
    intro b
    cases b
    · have hS := hrank (ng 1)
      rw [show rankOne (modelUniv .trialityD4 n p f hp).D.rootGroup (ng 1) = (slShort σ hσ).range
        from CFSG.ClassicalInvolution.ModelFacts.rankOne_short_eq_range hσ] at hS
      have hB := CFSG.ClassicalInvolution.RouteD.conjSub_mem_fundamentalSubgroups hS (nB σ)
      have heq : conjSub (nB σ) (slShort σ hσ).range = (slB σ hσ).range := by
        rw [conjSub, MonoidHom.map_range]
        rfl
      convert hB using 1
      exact heq.symm
    · have hL := hrank (ng 0)
      rwa [show rankOne (modelUniv .trialityD4 n p f hp).D.rootGroup (ng 0) = (slLong σ hσ).range
        from CFSG.ClassicalInvolution.ModelFacts.rankOne_long_eq_range hσ] at hL
  have hAc : ∀ i j, i ≠ j → Commutes (A i) (A j) := by
    intro i j hij a ha b hb
    cases i <;> cases j
    · exact absurd rfl hij
    · obtain ⟨B, rfl⟩ := ha
      obtain ⟨C, rfl⟩ := hb
      exact (slLong_comm_slB hσ C B).symm
    · obtain ⟨C, rfl⟩ := ha
      obtain ⟨B, rfl⟩ := hb
      exact slLong_comm_slB hσ C B
    · exact absurd rfl hij
  have hAfund : ∀ k, IsFundamentalOver (p ^ f) ((A k).map ψ) := fun k =>
    ⟨.trialityD4, n, p, f, hp, hp2, rfl, by trivial, hadm, ψ, hψ, hker, A k, hA k, rfl⟩
  have hnorm : ∀ i j, (A j).map ψ ≤ Subgroup.normalizer ((A i).map ψ : Set X) := by
    intro i j
    by_cases hij : i = j
    · subst j
      exact Subgroup.le_normalizer
    · have hcent : (A j).map ψ ≤ centralizer ((A i).map ψ : Set X) := fun a ha =>
        Subgroup.mem_centralizer_iff.mpr fun b hb =>
          CFSG.ClassicalInvolution.RouteD.commutes_map ψ (hAc i j hij) b hb a ha
      exact hcent.trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨c, hc⟩ := F14.exists_conj_family_mem_funSet (𝔉 := fundPred (p ^ f))
    (fun g _ h => isFundamentalOver_map_mulEquiv (MulAut.conj g) h)
    (fun k => (A k).map ψ) hAfund hnorm P
  let ψc : (modelUniv .trialityD4 n p f hp).K →* X := (MulAut.conj c).toMonoidHom.comp ψ
  have hψc : Function.Surjective ψc := (MulAut.conj c).surjective.comp hψ
  have hkerC : ψc.ker ≤ Subgroup.center (modelUniv .trialityD4 n p f hp).K := by
    intro a ha
    apply hker
    rw [MonoidHom.mem_ker] at ha ⊢
    exact (MulAut.conj c).injective (by simpa [ψc] using ha)
  have hc' : ∀ k, (A k).map ψc ∈ F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X) :=
    fun k => by simpa only [ψc, Subgroup.map_map] using hc k
  have hLS : (A true).map ψc ≠ (A false).map ψc := by
    intro heq
    obtain ⟨a, ha, b, hb, hab⟩ := F14.exists_noncommuting_map_of_equiv_sl2 ψc hkerC
      (MonoidHom.ofInjective (slLong_injective hσ)).symm
    have hb' : ψc b ∈ (A false).map ψc := by
      rw [← heq]
      exact Subgroup.mem_map_of_mem ψc hb
    obtain ⟨s, hs, hsb⟩ := Subgroup.mem_map.mp hb'
    apply hab
    rw [← hsb, ← map_mul, ← map_mul, hAc true false (by decide) a ha s hs]
  have hcard := ncard_funSet_eq_two_of_funTwoType hp hp2 hadm hX trivial P
  have hFun : F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X) =
      {(A true).map ψc, (A false).map ψc} := by
    refine (Set.eq_of_subset_of_ncard_le ?_ ?_
      (Set.finite_of_ncard_ne_zero (by rw [hcard]; norm_num))).symm
    · intro K hK
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hK
      rcases hK with rfl | rfl
      · exact hc' true
      · exact hc' false
    · rw [hcard, Set.ncard_pair hLS]
  have hK3 : Nat.card (GaloisField p (3 * f)) = (p ^ f) ^ 3 := by
    rw [GaloisField.card p (3 * f) (by omega), pow_mul']
  have hZ : Subgroup.center (modelUniv .trialityD4 n p f hp).K = ⊥ :=
    CFSG.LieType.Steinberg.CentralExt.TrialityClosed.twistedGroup_center_eq_bot_of_card
      (le_trans hp.two_le (Nat.le_self_pow (by omega) p)) hK3
      (fun c => iterateFrobenius_def p f c)
  have hinj : Function.Injective ψc :=
    (MonoidHom.ker_eq_bot_iff ψc).mp (le_bot_iff.mp (hZ ▸ hkerC))
  refine ⟨hσ, MulEquiv.ofBijective ψc ⟨hinj, hψc⟩, ?_⟩
  rw [hFun]
  rfl

theorem d4_funSet_equiv_sl2 {X : Type} [Group X] [Finite X] [IsSimpleGroup X] {n p f : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .trialityD4 n p f)
    (hX : CFSG.Blueprint.LieModel X .trialityD4 n p f) (P : Sylow 2 X)
    {K₁ K₂ : Subgroup X} (h₁ : K₁ ∈ F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X))
    (h₂ : K₂ ∈ F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X)) (hne : K₁ ≠ K₂) :
    (Nonempty (K₁ ≃* SL(2, GaloisField p f)) ∧ Nonempty (K₂ ≃* SL(2, GaloisField p (3 * f)))) ∨
      (Nonempty (K₂ ≃* SL(2, GaloisField p f)) ∧
        Nonempty (K₁ ≃* SL(2, GaloisField p (3 * f)))) := by
  have hf : 1 ≤ f := hadm.2.1
  obtain ⟨hσ, ψ, hFun⟩ := d4_funSet_eq_pair hp2 hadm hX P
  have hL : Nonempty ((slLong _ hσ).range.map ψ.toMonoidHom ≃* SL(2, GaloisField p f)) := by
    obtain ⟨eF⟩ := CFSG.ClassicalInvolution.ModelFacts.nonempty_ringEquiv_of_natCard_eq
      (F := CFSG.ClassicalInvolution.Models.TwistedPairs.fixedField
        (iterateFrobenius (GaloisField p (3 * f)) p f)) (F' := GaloisField p f) (by
        rw [CFSG.ClassicalInvolution.ModelFacts.card_fixedField_iterateFrobenius hf,
          GaloisField.card p f (by omega)])
    exact ⟨(Subgroup.equivMapOfInjective _ ψ.toMonoidHom ψ.injective).symm.trans
      ((MonoidHom.ofInjective (slLong_injective hσ)).symm.trans
        (CFSG.ClassicalInvolution.ModelFacts.slMapEquiv eF))⟩
  have hS : Nonempty ((slB _ hσ).range.map ψ.toMonoidHom ≃* SL(2, GaloisField p (3 * f))) :=
    ⟨(Subgroup.equivMapOfInjective _ ψ.toMonoidHom ψ.injective).symm.trans
      (MonoidHom.ofInjective (slB_injective hσ)).symm⟩
  rw [hFun] at h₁ h₂
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h₁ h₂
  rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl
  · exact absurd rfl hne
  · exact Or.inl ⟨hL, hS⟩
  · exact Or.inr ⟨hL, hS⟩
  · exact absurd rfl hne

theorem d4_centralizer_funSet_le {X : Type} [Group X] [Finite X] [IsSimpleGroup X] {n p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .trialityD4 n p f)
    (hX : CFSG.Blueprint.LieModel X .trialityD4 n p f) (P : Sylow 2 X)
    {K₁ K₂ : Subgroup X} (h₁ : K₁ ∈ F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X))
    (h₂ : K₂ ∈ F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X)) (hne : K₁ ≠ K₂) :
    centralizer (K₁ : Set X) ≤ K₂ := by
  have : Fact p.Prime := ⟨hp⟩
  have hf : 1 ≤ f := hadm.2.1
  obtain ⟨hσ, hK1, hC₀, hgF, -, -⟩ :=
    CFSG.ClassicalInvolution.Disconnected.AschTight.S19G.d4_model_data hp2 hf
  set σ := iterateFrobenius (GaloisField p (3 * f)) p f with hσdef
  obtain ⟨ψ, hψ, hker⟩ := CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover
    .trialityD4 n p f hp hp2 (by trivial) hadm X hX
  have hCL : centralizer ((slLong σ hσ).range : Set (twistedGroup σ)) = (slB σ hσ).range :=
    CFSG.ClassicalInvolution.Disconnected.AschTight.S19G.centralizer_range_slLong hσ hK1 hC₀ hgF
  have hCS : centralizer ((slB σ hσ).range : Set (twistedGroup σ)) ≤ (slLong σ hσ).range := by
    intro x hx
    have hy : (nB σ)⁻¹ * x * nB σ ∈
        centralizer ((slShort σ hσ).range : Set (twistedGroup σ)) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨C', rfl⟩
      have h := Subgroup.mem_centralizer_iff.mp hx _ ⟨C', rfl⟩
      rw [slB_apply] at h
      calc slShort σ hσ C' * ((nB σ)⁻¹ * x * nB σ) =
            (nB σ)⁻¹ * (nB σ * slShort σ hσ C' * (nB σ)⁻¹ * x) * nB σ := by group
        _ = (nB σ)⁻¹ * (x * (nB σ * slShort σ hσ C' * (nB σ)⁻¹)) * nB σ := by rw [h]
        _ = (nB σ)⁻¹ * x * nB σ * slShort σ hσ C' := by group
    rw [CFSG.ClassicalInvolution.Disconnected.AschTight.S19G.centralizer_range_slShort hσ hK1 hC₀
      hgF] at hy
    obtain ⟨C, hC⟩ := hy
    refine ⟨C, ?_⟩
    have hC' : (nB σ)⁻¹ * slLong σ hσ C * nB σ = (nB σ)⁻¹ * x * nB σ := by
      rw [← hC]
      simp
    calc slLong σ hσ C = nB σ * ((nB σ)⁻¹ * slLong σ hσ C * nB σ) * (nB σ)⁻¹ := by group
      _ = nB σ * ((nB σ)⁻¹ * x * nB σ) * (nB σ)⁻¹ := by rw [hC']
      _ = x := by group
  let A : Bool → Subgroup (modelUniv .trialityD4 n p f hp).K :=
    fun b => cond b (slLong σ hσ).range (slB σ hσ).range
  have hA : ∀ b, A b ∈ fundamentalSubgroups .trialityD4 (modelUniv .trialityD4 n p f hp).D := by
    have hrank : ∀ i, rankOne (modelUniv .trialityD4 n p f hp).D.rootGroup i ∈
        fundamentalSubgroups .trialityD4 (modelUniv .trialityD4 n p f hp).D := fun i =>
      ⟨1, Pi.single i 1, Or.inr (Or.inr ⟨rfl,
        CFSG.ClassicalInvolution.Balance.single_mem_roots _ i⟩), (conjSub_one _).symm⟩
    intro b
    cases b
    · have hS := hrank (ng 1)
      rw [show rankOne (modelUniv .trialityD4 n p f hp).D.rootGroup (ng 1) = (slShort σ hσ).range
        from CFSG.ClassicalInvolution.ModelFacts.rankOne_short_eq_range hσ] at hS
      have hB := CFSG.ClassicalInvolution.RouteD.conjSub_mem_fundamentalSubgroups hS (nB σ)
      have heq : conjSub (nB σ) (slShort σ hσ).range = (slB σ hσ).range := by
        rw [conjSub, MonoidHom.map_range]
        rfl
      convert hB using 1
      exact heq.symm
    · have hL := hrank (ng 0)
      rwa [show rankOne (modelUniv .trialityD4 n p f hp).D.rootGroup (ng 0) = (slLong σ hσ).range
        from CFSG.ClassicalInvolution.ModelFacts.rankOne_long_eq_range hσ] at hL
  have hAc : ∀ i j, i ≠ j → Commutes (A i) (A j) := by
    intro i j hij a ha b hb
    cases i <;> cases j
    · exact absurd rfl hij
    · obtain ⟨B, rfl⟩ := ha
      obtain ⟨C, rfl⟩ := hb
      exact (slLong_comm_slB hσ C B).symm
    · obtain ⟨C, rfl⟩ := ha
      obtain ⟨B, rfl⟩ := hb
      exact slLong_comm_slB hσ C B
    · exact absurd rfl hij
  have hAfund : ∀ k, IsFundamentalOver (p ^ f) ((A k).map ψ) := fun k =>
    ⟨.trialityD4, n, p, f, hp, hp2, rfl, by trivial, hadm, ψ, hψ, hker, A k, hA k, rfl⟩
  have hnorm : ∀ i j, (A j).map ψ ≤ Subgroup.normalizer ((A i).map ψ : Set X) := by
    intro i j
    by_cases hij : i = j
    · subst j
      exact Subgroup.le_normalizer
    · have hcent : (A j).map ψ ≤ centralizer ((A i).map ψ : Set X) := fun a ha =>
        Subgroup.mem_centralizer_iff.mpr fun b hb =>
          CFSG.ClassicalInvolution.RouteD.commutes_map ψ (hAc i j hij) b hb a ha
      exact hcent.trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨c, hc⟩ := F14.exists_conj_family_mem_funSet (𝔉 := fundPred (p ^ f))
    (fun g _ h => isFundamentalOver_map_mulEquiv (MulAut.conj g) h)
    (fun k => (A k).map ψ) hAfund hnorm P
  let ψc : (modelUniv .trialityD4 n p f hp).K →* X := (MulAut.conj c).toMonoidHom.comp ψ
  have hψc : Function.Surjective ψc := (MulAut.conj c).surjective.comp hψ
  have hkerC : ψc.ker ≤ Subgroup.center (modelUniv .trialityD4 n p f hp).K := by
    intro a ha
    apply hker
    rw [MonoidHom.mem_ker] at ha ⊢
    exact (MulAut.conj c).injective (by simpa [ψc] using ha)
  have hc' : ∀ k, (A k).map ψc ∈ F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X) :=
    fun k => by simpa only [ψc, Subgroup.map_map] using hc k
  have hLS : (A true).map ψc ≠ (A false).map ψc := by
    intro heq
    obtain ⟨a, ha, b, hb, hab⟩ := F14.exists_noncommuting_map_of_equiv_sl2 ψc hkerC
      (MonoidHom.ofInjective (slLong_injective hσ)).symm
    have hb' : ψc b ∈ (A false).map ψc := by
      rw [← heq]
      exact Subgroup.mem_map_of_mem ψc hb
    obtain ⟨s, hs, hsb⟩ := Subgroup.mem_map.mp hb'
    apply hab
    rw [← hsb, ← map_mul, ← map_mul, hAc true false (by decide) a ha s hs]
  have hcard := ncard_funSet_eq_two_of_funTwoType hp hp2 hadm hX trivial P
  have hFun : F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X) =
      {(A true).map ψc, (A false).map ψc} := by
    refine (Set.eq_of_subset_of_ncard_le ?_ ?_
      (Set.finite_of_ncard_ne_zero (by rw [hcard]; norm_num))).symm
    · intro K hK
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hK
      rcases hK with rfl | rfl
      · exact hc' true
      · exact hc' false
    · rw [hcard, Set.ncard_pair hLS]
  have hstep : ∀ i : Bool,
      centralizer (((A i).map ψc : Subgroup X) : Set X) ≤ (A (!i)).map ψc := by
    intro i x hx
    obtain ⟨xt, rfl⟩ := hψc x
    have hcomm : Commutes (A i) (Subgroup.zpowers xt) := by
      apply commutes_modelFund_of_commutes_map hp2 (by trivial) hadm ψc hkerC (hA i)
      rw [MonoidHom.map_zpowers]
      intro u hu v hv
      obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
      have hux : Commute u (ψc xt) := Subgroup.mem_centralizer_iff.mp hx u hu
      exact (hux.zpow_right z).eq
    have hxtC : xt ∈ centralizer ((A i : Subgroup _) :
        Set (modelUniv .trialityD4 n p f hp).K) :=
      Subgroup.mem_centralizer_iff.mpr fun a ha => hcomm a ha xt (Subgroup.mem_zpowers xt)
    refine Subgroup.mem_map_of_mem ψc ?_
    cases i
    · exact hCS hxtC
    · exact hCL.le hxtC
  rw [hFun] at h₁ h₂
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h₁ h₂
  rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl
  · exact absurd rfl hne
  · exact hstep true
  · exact hstep false
  · exact absurd rfl hne

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
