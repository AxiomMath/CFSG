module

public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitSimplyLacedGeometry
public import CFSG.ClassicalInvolution.Asc77.AscR10E18
import CFSG.ClassicalInvolution.Asc77.AscIH8Bridge
import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.ExcModel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup Matrix Module CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.Adjoint CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.ModelFacts.Levi
open CFSG.ClassicalInvolution.ModelFacts (stdRankOne nonempty_equiv_sl2_of_mem_fundamentalSubgroups
  longestFundamental_subset fundamentalSubgroups_subset_longest
  twistedE6Phi twistedE6Phi_xFixed e6Sign e6Sign_mul_self ker_twistedE6Phi_le_center
  twistedE6Phi_mem_fixedPointsIn isLongestRoot_twistedDatum_proj)
open CFSG.ClassicalInvolution.ModelFacts.LeviE6 (commute_pinnedX_pm)
open CFSG.LieType.Steinberg.TwistedE6 CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.Steinberg.Exceptional
open CFSG.LieType.AlgebraicGroups (mem_fixedPointsIn)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.SeitzGeneration
open CFSG.StandardType.TableBExcTwo (commute_rho)
open scoped MatrixGroups




theorem rho_frameE6Root : ∀ k : Fin 4, rho (frameE6Root k) = frameE6Root k := by
  decide +kernel


theorem commute_rootRankOne_of_commutes_phi_stdRankTwE6
    {p e : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (he : 1 ≤ e)
    {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot .E6 β) (hfix : rho β = β)
    {y : ModGL .E6 (CFSG.ClassicalInvolution.ModelFacts.LeviE6.E6Closure p e)}
    (hc : ∀ x ∈ stdRankOne (twistedE6Datum p e) (proj β),
      Commute y (CFSG.ClassicalInvolution.ModelFacts.LeviE6.phiE6 p e x)) :
    ∀ x ∈ rootRankOneGroup .E6 (CFSG.ClassicalInvolution.ModelFacts.LeviE6.E6Closure p e) β, Commute y x := by
  have : NeZero (2 * e) := ⟨by omega⟩
  let L := CFSG.ClassicalInvolution.ModelFacts.LeviE6.E6Closure p e
  have h2 : (2 : L) ≠ 0 := by
    intro h
    have hd := (CharP.cast_eq_zero_iff L p 2).mp h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp hd)
  have hpinned : ∀ γ, γ = β ∨ γ = -β → ∀ c : L,
      Commute y (pinnedX .E6 L γ c) := by
    intro γ hγ c
    have hγr : IsRoot .E6 γ := by
      rcases hγ with rfl | rfl
      · exact hβ
      · exact IsRoot.neg hβ
    have hγfix : rho γ = γ := by
      rcases hγ with rfl | rfl
      · exact hfix
      · exact rho_neg_of_fixed hfix
    have hx : xFixed (frobQ p e) hγr hγfix
        (1 : GaloisField p (2 * e)) (map_one _) ∈
        stdRankOne (twistedE6Datum p e) (proj β) := by
      rcases hγ with rfl | rfl
      · exact Subgroup.mem_sup_left (xFixed_mem (frobQ p e) hβ hfix _ _)
      · apply Subgroup.mem_sup_right
        change xFixed (frobQ p e) hγr hγfix
          (1 : GaloisField p (2 * e)) (map_one _) ∈
          twistedRootGroup (GaloisField p (2 * e)) (frobQ p e) (-proj β)
        rw [← map_neg proj β]
        exact xFixed_mem (frobQ p e) (IsRoot.neg hβ) (rho_neg_of_fixed hfix) _ _
    have hh := (hc _ hx).eq
    have hφ := twistedE6Phi_xFixed p e
      (CFSG.ClassicalInvolution.ModelFacts.LeviE6.E6Closure p e) hγr hγfix
      (1 : GaloisField p (2 * e)) (map_one _)
    change CFSG.ClassicalInvolution.ModelFacts.LeviE6.phiE6 p e
        (xFixed (frobQ p e) hγr hγfix (1 : GaloisField p (2 * e)) (map_one _)) =
      pinnedX .E6 (CFSG.ClassicalInvolution.ModelFacts.LeviE6.E6Closure p e) γ
        ((e6Sign γ : CFSG.ClassicalInvolution.ModelFacts.LeviE6.E6Closure p e) *
          algebraMap (GaloisField p (2 * e))
            (CFSG.ClassicalInvolution.ModelFacts.LeviE6.E6Closure p e) 1) at hφ
    simp only [map_one, mul_one] at hφ
    rw [hφ] at hh
    have hp : Commute y (pinnedX .E6 L γ 1) :=
      commute_pinnedX_pm (e6Sign_mul_self γ) (one_mul (1 : L)) hh
    have hm : Commute y (pinnedX .E6 L γ (-1)) := by
      rw [← pinnedX_neg]
      exact hp.inv_right
    exact commute_pinnedX_of_commute_pm_one (by decide) h2 γ hp hm c
  have hle : rootRankOneGroup .E6 L β ≤ centralizer {y} := by
    rw [(exceptional_Lang_root_rank_one_torus_transport .E6 L hβ).1]
    apply sup_le
    all_goals
      rw [rootSubgroup, Subgroup.closure_le]
      rintro _ ⟨c, rfl⟩
      change pinnedX .E6 L _ c ∈ centralizer {y}
      rw [Subgroup.mem_centralizer_singleton_iff]
    · exact (hpinned β (Or.inl rfl) c).eq.symm
    · exact (hpinned (-β) (Or.inr rfl) c).eq.symm
  intro x hx
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hx)).symm

private theorem map_le_rankOne_of_closure_defining_pow
    {U : Type} [Group U] {p f : ℕ} [hp : Fact p.Prime] [NeZero f]
    {τ : Tag} {d : ℕ} (D : CFSG.StandardType.TableBExcTwo.OrthFrame τ d)
    (k : Fin (d + 1))
    (hkernel : ∀ γ ∈ rootFinset τ, (∀ j, j ≠ k → iform (D.root j) γ = 0) →
      γ = D.root k ∨ γ = -D.root k)
    (hweighted : ∀ γ ∈ rootFinset τ,
      (∑ j : Fin (d + 1), if j = k then 0 else (5 : ℤ) ^ j.val * iform γ (D.root j)) = 0 →
        γ = D.root k ∨ γ = -D.root k)
    (Φ : U →* ModGL τ (AlgClosGF p f)) (R : Subgroup U)
    (hgen : Subgroup.closure {x : R | x ^ p = 1} = ⊤)
    (hmem : ∀ x ∈ R, Φ x ∈ adjointGroup τ (AlgClosGF p f))
    (hc : ∀ j, j ≠ k → ∀ a ∈ R,
      ∀ x ∈ rootRankOneGroup τ (AlgClosGF p f) (D.root j), Commute (Φ a) x) :
    R.map Φ ≤ rootRankOneGroup τ (AlgClosGF p f) (D.root k) := by
  have hgenerators : ∀ a : R, a ^ p = 1 → Φ a.1 ∈ rootRankOneGroup τ (AlgClosGF p f) (D.root k) := by
    intro a hap
    apply mem_rankOne_of_mem_torus_mul_of_defining_pow (D.isRoot k)
    · exact mem_torus_mul_rankOne_of_commutes_other_rootFrame D k hkernel hweighted
        (hmem a.1 a.2) (fun j hj => hc j hj a.1 a.2)
    · have hh := congrArg (Φ.comp R.subtype) hap
      simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply, Subgroup.coe_pow,
        map_pow, Subgroup.coe_one, map_one] using hh
  have htop : (⊤ : Subgroup R) ≤
      (rootRankOneGroup τ (AlgClosGF p f) (D.root k)).comap (Φ.comp R.subtype) := by
    rw [← hgen, Subgroup.closure_le]
    exact hgenerators
  rintro _ ⟨a, ha, rfl⟩
  exact htop (show (⟨a, ha⟩ : R) ∈ (⊤ : Subgroup R) from trivial)

theorem phi_le_rankOne_of_commutes_other_twE6_frame
    {p e : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .twistedE6 0 p e)
    {R : Subgroup (twistedE6Group p e)}
    (hR : R ∈ fundamentalSubgroups .twistedE6 (twistedE6Datum p e)) (k : Fin 4)
    (hc : ∀ j : Fin 4, j ≠ k →
      Commutes R (stdRankOne (twistedE6Datum p e) (proj (frameE6Root j)))) :
    R.map (CFSG.ClassicalInvolution.ModelFacts.LeviE6.phiE6 p e) ≤
      rootRankOneGroup .E6 (CFSG.ClassicalInvolution.ModelFacts.LeviE6.E6Closure p e) (frameE6Root k) := by
  have he : 1 ≤ e := hadm.2.1
  have : NeZero e := ⟨by omega⟩
  have : NeZero (2 * e) := ⟨by omega⟩
  let L := CFSG.ClassicalInvolution.ModelFacts.LeviE6.E6Closure p e
  let Φ : twistedE6Group p e →* ModGL .E6 L :=
    CFSG.ClassicalInvolution.ModelFacts.LeviE6.phiE6 p e
  obtain ⟨eR⟩ := nonempty_equiv_sl2_of_mem_fundamentalSubgroups
    (p := p) (e := e) (n := 0) (R := R) hp2 (t := .twistedE6)
    (by trivial) hadm (by decide) (by decide) hR
  have hgen := CFSG.LieType.HighestRoot.closure_pow_eq_one_eq_top_of_mulEquiv
    (J := R) (F := GaloisField p e) p eR
  apply map_le_rankOne_of_closure_defining_pow (p := p) (f := 2 * e) frameE6 k
    (orthogonal_kernel_frameE6 k) (weighted_kernel_frameE6 k) Φ R hgen
  · intro a _
    exact (mem_fixedPointsIn.mp (twistedE6Phi_mem_fixedPointsIn p e hp2 he a)).1
  · intro j hj a ha
    apply commute_rootRankOne_of_commutes_phi_stdRankTwE6 hp2 he
      (frameE6.isRoot j) (rho_frameE6Root j)
    intro x hx
    exact (show Commute a x from hc j hj a ha x hx).map Φ

theorem eq_of_commutes_other_twE6_frame
    {p e : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .twistedE6 0 p e)
    {R : Subgroup (twistedE6Group p e)}
    (hR : R ∈ fundamentalSubgroups .twistedE6 (twistedE6Datum p e)) (k : Fin 4)
    (hc : ∀ j : Fin 4, j ≠ k →
      Commutes R (stdRankOne (twistedE6Datum p e) (proj (frameE6Root j)))) :
    R = stdRankOne (twistedE6Datum p e) (proj (frameE6Root k)) := by
  have he : 1 ≤ e := hadm.2.1
  have : NeZero e := ⟨by omega⟩
  let L := CFSG.ClassicalInvolution.ModelFacts.LeviE6.E6Closure p e
  let Φ := CFSG.ClassicalInvolution.ModelFacts.LeviE6.phiE6 p e
  generalize hAeq : stdRankOne (twistedE6Datum p e) (proj (frameE6Root k)) = A
  have hAf : A ∈ fundamentalSubgroups .twistedE6 (twistedE6Datum p e) := by
    rw [← hAeq]
    exact longestFundamental_subset .twistedE6 _
      (stdRank_mem_longestFundamental_TwE6 (frameE6.isRoot k) (rho_frameE6Root k))
  obtain ⟨eR⟩ := nonempty_equiv_sl2_of_mem_fundamentalSubgroups
    (p := p) (e := e) (n := 0) (R := R) hp2 (t := .twistedE6)
    (by trivial) hadm (by decide) (by decide) hR
  have hASL : Nonempty (A ≃* SL2 (GaloisField p e)) := by
    have h := CFSG.ClassicalInvolution.ModelFacts.fundamentalSL2_twistedE6 p e hadm
      (1 : twistedE6Group p e) (proj (frameE6Root k))
      (isLongestRoot_twistedDatum_proj (frobQ p e) (frameE6.isRoot k) (rho_frameE6Root k))
    have heq : ((twistedE6Datum p e).rootGroup (proj (frameE6Root k)) ⊔
        (twistedE6Datum p e).rootGroup (-proj (frameE6Root k))).map
          (MulAut.conj (1 : twistedE6Group p e)).toMonoidHom = A := by
      change CFSG.ClassicalInvolution.Generic.conjSub 1
        (stdRankOne (twistedE6Datum p e) (proj (frameE6Root k))) = A
      rw [CFSG.ClassicalInvolution.Generic.conjSub_one, hAeq]
    exact heq ▸ h
  obtain ⟨eA⟩ := hASL
  have hodd : Odd (Nat.card (GaloisField p e)) := by
    rw [GaloisField.card p e (by omega)]
    exact (hp.out.odd_of_ne_two hp2).pow
  let c := CFSG.ClassicalInvolution.Asc77.sl2Inv (R := R) (F := GaloisField p e) eR
  have hcR : c ∈ R := CFSG.ClassicalInvolution.Asc77.sl2Inv_mem eR
  have ho : orderOf c = 2 := CFSG.ClassicalInvolution.Asc77.orderOf_sl2Inv hodd eR
  let c' := CFSG.ClassicalInvolution.Asc77.sl2Inv (R := A) (F := GaloisField p e) eA
  have hcA : c' ∈ A := CFSG.ClassicalInvolution.Asc77.sl2Inv_mem eA
  have ho' : orderOf c' = 2 := CFSG.ClassicalInvolution.Asc77.orderOf_sl2Inv hodd eA
  have hcΦ : Φ c ∈ rootRankOneGroup .E6 L (frameE6Root k) :=
    phi_le_rankOne_of_commutes_other_twE6_frame hp2 hadm hR k hc
      (Subgroup.mem_map_of_mem Φ hcR)
  have hΦ1 : Φ c ≠ 1 := by
    intro h
    have h1 := phi_injOn_fundamental hadm hR c hcR h
    have := (orderOf_eq_prime_iff (p := 2)).mp ho
    exact this.2 h1
  have hΦ2 : orderOf (Φ c) = 2 := by
    apply orderOf_eq_prime
    · rw [← map_pow, ((orderOf_eq_prime_iff (p := 2)).mp ho).1, map_one]
    · exact hΦ1
  let d : adjointGroup .E6 L := ⟨Φ c,
    (mem_fixedPointsIn.mp (twistedE6Phi_mem_fixedPointsIn p e hp2 he c)).1⟩
  have hd : d ∈ stdRankOne (CFSG.ClassicalInvolution.ModelFacts.e6AdjDatum L) (frameE6Root k) := by
    apply (mem_stdRankOne_e6_iff' (K := L) (frameE6.isRoot k) d).mpr
    obtain ⟨B, hB⟩ := hcΦ
    exact ⟨B, hB.symm⟩
  have hsign : Φ c = signDiagE6 L (frameE6Root k) := by
    apply eq_signDiagE6_of_orderOf_eq_two (by rw [ringChar.eq L p]; exact hp2)
      (frameE6.isRoot k) hd
    exact Subgroup.orderOf_coe d ▸ hΦ2
  have hsign' : Φ c' = signDiagE6 L (frameE6Root k) :=
    phi_involution hp2 he hadm (frameE6.isRoot k) (rho_frameE6Root k)
      (hAeq.symm ▸ hcA) ho'
  have hRl := fundamentalSubgroups_subset_longest (by decide : StatedLieTag.twistedE6 ≠ .G2)
    (by decide) (twistedE6Datum p e) hR
  have hAl : A ∈ CFSG.ClassicalInvolution.ModelFacts.longestFundamental (twistedE6Datum p e) := by
    rw [← hAeq]
    exact stdRank_mem_longestFundamental_TwE6 (frameE6.isRoot k) (rho_frameE6Root k)
  rcases CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.eq_three_or_five_le_of_odd_prime_pow
    hp.out hp2 he with hq | hq
  · exact eq_of_mem_longestFundamental_TwE6_three hp2 he hq hadm hRl hAl hcR hcA
      ho ho' (hsign.trans hsign'.symm)
  · exact eq_of_mem_longestFundamental_TwE6 hp2 he hq hadm hRl hAl hcR hcA
      ho ho' (hsign.trans hsign'.symm)


private theorem full_frame_and_centralizingLayer_funSet_eq_of_twistedE6
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p e : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .twistedE6 0 p e)
    (hX : CFSG.Blueprint.LieModel X .twistedE6 0 p e)
    (P : Sylow 2 X) {K : Subgroup X}
    (hK : K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X)) :
    (∃ (ψ : (modelUniv .twistedE6 0 p e hp.out).K →* X), Function.Surjective ψ ∧
      ψ.ker ≤ center (modelUniv .twistedE6 0 p e hp.out).K ∧
      F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X) =
        Set.range (fun k : Fin 4 =>
          (stdRankOne (modelUniv .twistedE6 0 p e hp.out).D
            (proj (frameE6Root k))).map ψ)) ∧
      centralizingLayer {J : Subgroup X | IsFundamentalOver (p ^ e) J}
        {x : X | ∃ J ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X), J ≠ K ∧ x ∈ J} = K := by
  have he : 1 ≤ e := hadm.2.1
  let L := CFSG.ClassicalInvolution.ModelFacts.LeviE6.E6Closure p e
  let A : Fin 4 → Subgroup (modelUniv .twistedE6 0 p e hp.out).K := fun k =>
    stdRankOne (twistedE6Datum p e) (proj (frameE6Root k))
  have hA : ∀ k, A k ∈ fundamentalSubgroups .twistedE6 (modelUniv .twistedE6 0 p e hp.out).D := by
    intro k
    exact longestFundamental_subset .twistedE6 _
      (stdRank_mem_longestFundamental_TwE6 (frameE6.isRoot k) (rho_frameE6Root k))
  have hcA : ∀ i j, i ≠ j → Commutes (A i) (A j) := by
    intro i j hij
    apply commutes_modelFund_of_commutes_map hp2 (t := .twistedE6) (by trivial) hadm
      (CFSG.ClassicalInvolution.ModelFacts.LeviE6.phiE6 p e) (ker_twistedE6Phi_le_center p e L) (hA i)
    intro x hx y hy
    obtain ⟨B, rfl⟩ := phi_map_stdRank_le hp2 he (frameE6.isRoot i) (rho_frameE6Root i) hx
    obtain ⟨C, rfl⟩ := phi_map_stdRank_le hp2 he (frameE6.isRoot j) (rho_frameE6Root j) hy
    exact congrArg (fun x : adjointGroup .E6 L => (x : ModGL .E6 L)) (commute_rho frameE6 hij B C)
  have huni : ∀ R ∈ fundamentalSubgroups .twistedE6 (modelUniv .twistedE6 0 p e hp.out).D,
      ∀ k, (∀ j, j ≠ k → Commutes R (A j)) → R = A k := by
    intro R hR k hc
    exact eq_of_commutes_other_twE6_frame hp2 hadm hR k hc
  exact full_frame_and_centralizingLayer_funSet_eq_of_model_family hp2 (by trivial) hadm hX
    (by simp) A hA hcA huni P hK

theorem centralizingLayer_funSet_eq_of_twistedE6
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p e : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .twistedE6 0 p e)
    (hX : CFSG.Blueprint.LieModel X .twistedE6 0 p e)
    (P : Sylow 2 X) {K : Subgroup X}
    (hK : K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X)) :
    centralizingLayer {J : Subgroup X | IsFundamentalOver (p ^ e) J}
      {x : X | ∃ J ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X), J ≠ K ∧ x ∈ J} = K :=
  (full_frame_and_centralizingLayer_funSet_eq_of_twistedE6 hp2 hadm hX P hK).2

theorem exists_full_frame_funSet_twistedE6
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p e : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .twistedE6 0 p e)
    (hX : CFSG.Blueprint.LieModel X .twistedE6 0 p e)
    (P : Sylow 2 X) {K : Subgroup X}
    (hK : K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X)) :
    ∃ (ψ : (modelUniv .twistedE6 0 p e hp.out).K →* X), Function.Surjective ψ ∧
      ψ.ker ≤ center (modelUniv .twistedE6 0 p e hp.out).K ∧
      F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X) =
        Set.range (fun k : Fin 4 =>
          (stdRankOne (modelUniv .twistedE6 0 p e hp.out).D
            (proj (frameE6Root k))).map ψ) :=
  (full_frame_and_centralizingLayer_funSet_eq_of_twistedE6 hp2 hadm hX P hK).1

theorem ncard_funSet_le_four_of_twistedE6
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p e : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .twistedE6 0 p e)
    (hX : CFSG.Blueprint.LieModel X .twistedE6 0 p e)
    (P : Sylow 2 X) {K : Subgroup X}
    (hK : K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X)) :
    (F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X)).ncard ≤ 4 := by
  obtain ⟨ψ, hψ, hker, hfull⟩ := exists_full_frame_funSet_twistedE6 hp2 hadm hX P hK
  rw [hfull]
  simpa only [Nat.card_fin, ← Nat.card_coe_set_eq] using Finite.card_range_le
    (fun k : Fin 4 => (stdRankOne (modelUniv .twistedE6 0 p e hp.out).D
      (proj (frameE6Root k))).map ψ)

end CFSG.LocalAnalysis.UniquenessCase.UC22
