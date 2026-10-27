module

public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitLinearInner
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitNonlinearInner
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FundamentalOverModel
import CFSG.ClassicalInvolution.ModelFacts.FundamentalSL2All
import CFSG.ClassicalInvolution.AschTight.S19MFund
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FunHypOmega

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.ClassicalInvolution.Generic
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped MatrixGroups


theorem odd_normalizer_inner_fundamental_psl_model_image
    {X : Type} [Group X] [Finite X] {p n e : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .PSL n p e)
    (ψ : (modelUniv .PSL n p e Fact.out).K →* X)
    (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ center (modelUniv .PSL n p e Fact.out).K)
    {R : Subgroup (modelUniv .PSL n p e Fact.out).K}
    (hR : R ∈ fundamentalSubgroups .PSL (modelUniv .PSL n p e Fact.out).D)
    {g : X} (hg : g ∈ normalizer ((R.map ψ : Subgroup X) : Set X))
    (hgo : Odd (orderOf g)) :
    (R.map ψ).normalizerMonoidHom ⟨g, hg⟩ ∈
      (MulAut.conj : R.map ψ →* MulAut (R.map ψ)).range := by
  by_cases hn : n = 2
  · subst n
    have hRtop : R = ⊤ :=
      CFSG.ClassicalInvolution.RouteD.longRootSet_two_subset (F := GaloisField p e)
        (by omega) (CFSG.ClassicalInvolution.RouteD.fundamentalSubgroups_psl_subset
          (F := GaloisField p e) (m := 1) (by omega) hR)
    have hmap : R.map ψ = ⊤ := by
      rw [hRtop, Subgroup.map_top_of_surjective _ hψ]
    exact (CFSG.GroupTheory.normalizerMonoidHom_mem_range_conj_iff hg).mpr
      ⟨g, by rw [hmap]; trivial, fun _ _ => rfl⟩
  have hn2 : 2 ≤ n := hadm.2.2.1
  have hdisj : R ⊓ ψ.ker = ⊥ :=
    inf_ker_eq_bot_of_mem_fundamentalSubgroups (by trivial) hadm (by simp [hn])
      ψ hker hR
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := ⟨n - 1, by omega⟩
  have hodd : Odd (Nat.card (GaloisField p e)) :=
    CFSG.ClassicalInvolution.Disconnected.AschTight.S19M.odd_natCard_galoisField
      hp2 hadm.2.1
  exact odd_normalizer_inner_fundamental_psl_image_all hodd (by omega)
    ψ hψ hker hR hdisj hg hgo

theorem odd_normalizer_inner_fundamental_model_image
    {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (t : StatedLieTag) (n e : ℕ) (hfund : IsFundTag t)
    (hadm : StatedLieAdmissible t n p e)
    (ψ : (modelUniv t n p e Fact.out).K →* X)
    (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ center (modelUniv t n p e Fact.out).K)
    {R : Subgroup (modelUniv t n p e Fact.out).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D)
    {g : X} (hg : g ∈ normalizer ((R.map ψ : Subgroup X) : Set X))
    (hgo : Odd (orderOf g)) :
    (R.map ψ).normalizerMonoidHom ⟨g, hg⟩ ∈
      (MulAut.conj : R.map ψ →* MulAut (R.map ψ)).range := by
  by_cases ht : t = .PSL
  · subst t
    exact odd_normalizer_inner_fundamental_psl_model_image hp2 hadm ψ hψ hker hR hg hgo
  have : Finite (modelUniv t n p e Fact.out).K :=
    CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv hp2 Fact.out hfund hadm
  have hdisj : R ⊓ ψ.ker = ⊥ :=
    inf_ker_eq_bot_of_mem_fundamentalSubgroups hfund hadm (by simp [ht]) ψ hker hR
  have key : ∀ {F : Type} [Field F] [Finite F], Odd (Nat.card F) →
      (R ≃* SL(2, F)) →
      (R.map ψ).normalizerMonoidHom ⟨g, hg⟩ ∈
        (MulAut.conj : R.map ψ →* MulAut (R.map ψ)).range := by
    intro F _ _ hodd eR
    by_cases h3 : 3 < Nat.card F
    · have hRperf : Group.IsPerfect R :=
        CFSG.ClassicalInvolution.isPerfect_of_equiv_sl2 (by omega) eR
      apply (CFSG.GroupTheory.normalizerMonoidHom_mem_range_conj_iff hg).mpr
      exact CFSG.GroupTheory.exists_inner_normalizer_of_central_image ψ hψ hker R hRperf
        (fun y hy hyo => odd_normalizer_inner_fundamental_nonpsl hp2 t n e hfund hadm ht
          R hR hRperf y hy hyo) hg hgo
    · have hF : Nat.card F = 3 := by
        have h2 : 1 < Nat.card F := Finite.one_lt_card
        obtain ⟨k, hk⟩ := hodd
        omega
      exact normalizerMonoidHom_mem_range_conj_of_equiv_sl2_three hF
        ((CFSG.LocalAnalysis.ComponentInitial.equivMapOfInfKerEqBot ψ hdisj).symm.trans eR)
        hg hgo
  rcases CFSG.ClassicalInvolution.ModelFacts.nonempty_equiv_sl2_galoisField_of_mem_fundamentalSubgroups
      hp2 hfund hadm hR with ⟨⟨eR⟩⟩ | ⟨_, ⟨eR⟩⟩
  · exact key
      (CFSG.ClassicalInvolution.Disconnected.AschTight.S19M.odd_natCard_galoisField
        hp2 hadm.2.1) eR
  · exact key
      (CFSG.ClassicalInvolution.Disconnected.AschTight.S19M.odd_natCard_galoisField
        hp2 (by have := hadm.2.1; omega)) eR

theorem odd_normalizer_inner_of_isFundamentalOver_general
    {X : Type} [Group X] [Finite X] {q : ℕ} {K : Subgroup X}
    (hK : IsFundamentalOver q K) {g : X}
    (hg : g ∈ normalizer (K : Set X)) (hgo : Odd (orderOf g)) :
    K.normalizerMonoidHom ⟨g, hg⟩ ∈ (MulAut.conj : K →* MulAut K).range := by
  obtain ⟨t, n, p, e, hp, hp2, _, hfund, hadm, ψ, hψ, hker, R, hR, rfl⟩ := hK
  let : Fact p.Prime := ⟨hp⟩
  exact odd_normalizer_inner_fundamental_model_image hp2 t n e hfund hadm ψ hψ hker
    hR hg hgo

end CFSG.LocalAnalysis.UniquenessCase.UC22
