module

public import CFSG.LocalAnalysis.StandardType.GGFamD4Index
public import CFSG.LocalAnalysis.StandardType.GGFamTameTransfer
public import CFSG.LocalAnalysis.StandardType.GGFamIsolation
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTamePrime
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwoDFour
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcLang
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.Lattice.SteinbergBIE6EvenBruhat
public import CFSG.RankThree.Lattice.SteinbergBIE6OrderThreeTools
public import CFSG.RankThree.Lattice.SteinbergBIE6Qplus
public import CFSG.RankThree.PartOne.KE.E8D4Family

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE (d4Nodes)
open scoped commutatorElement

private theorem famD4_pin_of_pos {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    {N : ℕ} (hN : 0 < N) (hNL : (N : L) ≠ 0) {K : KacData τ} (hK : K.Facts)
    {D4C : Finset (Option (Fin τ.rank))}
    (hpin : ∀ C : Finset (Option (Fin τ.rank)), C.card = 4 → kacCount τ K.θ C = 24 → C = D4C)
    (hJ : ∀ j : Fin τ.rank, some j ∈ D4C ↔ 1 ≤ j.val ∧ j.val ≤ 4) (hnone : none ∉ D4C)
    {a : Fin τ.rank → Lˣ} (hTN : rootDiagUnit τ a ^ N = 1)
    (i : KernelComponent (rootCharHom a))
    (hrank : compRank (componentRoots (rootCharHom a) i) = 4)
    (hcard : (componentRoots (rootCharHom a) i).ncard = 24) :
    ∃ v : WeylGroup τ, componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots τ (d4Nodes τ) := by
  obtain ⟨v, μ, hall, hpinned⟩ := exists_pinnedT_of_pos hN hNL hK hTN
  obtain ⟨x, C, hxC, -, hi, hr, hc⟩ := hpinned i
  have hC : C = D4C := hpin C (hr ▸ hrank) (hc ▸ hcard)
  subst hC
  refine ⟨v, ?_⟩
  rw [hi, K.rootsOf_eq_parabolicRoots (by exact_mod_cast hnone)]
  congr 2
  exact Set.ext fun j => hJ j

theorem langFamTame_twoD_four
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) (hp2 : p ≠ 2) {ι : Type}
    {a : ι → Fin τ.rank → Lˣ} (hT : ∀ u, rootDiagUnit τ (a u) ∈ S.D.torus)
    (hap : ∀ u j, a u j ^ p = 1) (h1 : ∃ u, rootDiagUnit τ (a u) ≠ 1)
    (i : KernelComponent (famCharHom a))
    (hr : compRank (componentRoots (famCharHom a) i) = 4)
    (hc : (componentRoots (famCharHom a) i).ncard = 24)
    (hnin : ¬ twistInner (componentRoots (famCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (famCharHom a) i)])) :
    CFSG.IsQuasisimple (rationalComponentM S.ρ S.Γ (famCharHom a) i) := by
  classical
  have hχp : ∀ γ, IsRoot τ γ → famCharHom a (Multiplicative.ofAdd γ) ^ p = 1 := by
    intro γ _
    funext u
    exact rootChar_pow_eq_one_of_forall (hap u) γ
  have hχ1 : ∃ γ, IsRoot τ γ ∧ famCharHom a (Multiplicative.ofAdd γ) ≠ 1 := by
    obtain ⟨u, hu⟩ := h1
    have hau : a u ≠ 1 := fun h => hu (by rw [h, rootDiagUnit_one])
    obtain ⟨j, hj⟩ : ∃ j, a u j ≠ 1 := by
      by_contra h
      push Not at h
      exact hau (funext h)
    refine ⟨Pi.single j 1, isRoot_single τ j, ?_⟩
    intro hc'
    have hrc : rootChar (a u) (Pi.single j 1) = a u j := by
      simpa using rootChar_nsmul_single (a u) j 1
    exact hj (by
      have h1' : famCharHom a (Multiplicative.ofAdd (Pi.single j 1)) u = 1 := congrFun hc' u
      change rootChar (a u) (Pi.single j 1) = 1 at h1'
      rwa [hrc] at h1')
  have hρfam : ∀ γ ∈ kernelRoots (famCharHom a), S.ρ γ ∈ kernelRoots (famCharHom a) :=
    fun γ hγ => rho_mem_kernelRoots_famChar S a hT hγ
  have hstable := image_componentRoots_eq_of_d4_family hτ S hp hp2 hχp hχ1 hρfam i hr hc
  obtain ⟨N, b, j, hNprime, hN2, hbN, hj⟩ := exists_isolating_element hτ a hp hp2 hap i
  have hNL : (N : L) ≠ 0 := by
    intro h
    exact hN2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hNprime).1
      ((CharP.cast_eq_zero_iff L 2 N).1 h)).symm
  have hrj : compRank (componentRoots (rootCharHom b) j) = 4 := by rw [hj]; exact hr
  have hcj : (componentRoots (rootCharHom b) j).ncard = 24 := by rw [hj]; exact hc
  have himg : S.ρ '' componentRoots (rootCharHom b) j = componentRoots (rootCharHom b) j := by
    rw [hj, hstable]
  have hρb : ∀ γ ∈ componentRoots (rootCharHom b) j,
      S.ρ γ ∈ componentRoots (rootCharHom b) j := by
    intro γ hγ
    rw [← himg]
    exact ⟨γ, hγ, rfl⟩
  have hninb : ¬ twistInner (componentRoots (rootCharHom b) j)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom b) j)]) := by
    rw [hj]
    exact hnin
  have htransfer : ∀ h : CFSG.IsQuasisimple
      (rationalComponent S.ρ S.Γ (rootCharHom b) j),
      CFSG.IsQuasisimple (rationalComponentM S.ρ S.Γ (famCharHom a) i) := by
    intro h
    rw [← rationalComponentM_eq S.ρ S.Γ (rootCharHom b) j] at h
    rwa [rationalComponentM_eq_of_componentRoots_eq S.ρ S.Γ hj] at h
  rcases hτ with rfl | rfl | rfl
  ·
    obtain ⟨v, hv⟩ := famD4_pin_of_pos (K := kacE6)
      (D4C := {some 1, some 2, some 3, some 4}) hNprime.pos hNL facts_E6
      kacCount_E6_four (by decide) (by decide) hbN j hrj hcj
    have hE6 : E6FixDNAll := e6FixDNAll_proved
    obtain ⟨w, hn⟩ := S.D.n_weyl
    obtain ⟨Fr, hFr, P, hP, hΦ⟩ := S.D.steinberg
    rcases hP with rfl | ⟨t, ht, rfl⟩
    · have hΦ' : S.D.Φ = Units.map (entrywiseHom Fr) := by
        ext1 g
        rw [hΦ, one_mul, inv_one, mul_one]
      exact htransfer (isQuasisimple_rationalComponent_of_d4_outer d4Base_E6
        d4TrialityLayer_E6 (d4SwapLayer_E6 hE6) S hFr hΦ' hn
        (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ' hn hγ) j v hv hρb hninb)
    · have hfin : (componentRoots (rootCharHom b) j).Finite :=
        (finite_setOf_isRoot _).subset fun γ hγ => hγ.1.1
      have hs := componentOrbitLength_eq_one hfin hρb
      rw [hs, Function.iterate_one] at hninb
      exact htransfer (isQuasisimple_rationalComponent_of_d4_twE6 hE6 S
        ⟨t, ht, Fr, hFr, hΦ⟩ j v hv hρb hninb)
  ·
    obtain ⟨v, hv⟩ := famD4_pin_of_pos (K := kacE7)
      (D4C := {some 1, some 2, some 3, some 4}) hNprime.pos hNL facts_E7
      kacCount_E7_four (by decide) (by decide) hbN j hrj hcj
    obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted twistTag_tag_ne_E7
    obtain ⟨w, hn⟩ := S.D.n_weyl
    exact htransfer (isQuasisimple_rationalComponent_of_d4_outer d4Base_E7
      CFSG.RankThree.PartOne.KD4L.d4TrialityLayer_E7 (d4SwapLayer_E7 e6FixDNAll_proved)
      S hFr hΦ hn (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ hn hγ) j v hv hρb hninb)
  ·
    obtain ⟨v, hv⟩ := famD4_pin_of_pos (K := kacE8)
      (D4C := {some 1, some 2, some 3, some 4}) hNprime.pos hNL facts_E8
      kacCount_E8_four (by decide) (by decide) hbN j hrj hcj
    obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted twistTag_tag_ne_E8
    obtain ⟨w, hn⟩ := S.D.n_weyl
    exact htransfer (isQuasisimple_rationalComponent_of_d4_outer d4Base_E8
      CFSG.RankThree.PartOne.KD4L.d4TrialityLayer_E8 (d4SwapLayer_E8 e6FixDNAll_proved)
      S hFr hΦ hn (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ hn hγ) j v hv hρb hninb)

end CFSG.StandardType.TableCRes
