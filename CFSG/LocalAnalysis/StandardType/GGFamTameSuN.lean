module

public import CFSG.LocalAnalysis.StandardType.GGFamTameRangeSpan
public import CFSG.LocalAnalysis.StandardType.GGFamTameLang
public import CFSG.LocalAnalysis.StandardType.GGFamTameOrbit
public import CFSG.LocalAnalysis.StandardType.GGFamTameTransfer
public import CFSG.LocalAnalysis.StandardType.GGFamIsolation
public import CFSG.LocalAnalysis.StandardType.GGFamUnitaryFrameRange
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTame.Order216
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTamePrime
import CFSG.LocalAnalysis.GLTheoremA.CatA.KD147cMat

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement MatrixGroups

private theorem famSuN_frame
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {L : Type} [Field L] [IsAlgClosed L]
    [CharP L 2] {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) (hp2 : p ≠ 2) {ι : Type}
    {a : ι → Fin τ.rank → Lˣ} (hap : ∀ u j, a u j ^ p = 1)
    (i : KernelComponent (famCharHom a))
    (hk : twistKindM S.ρ (famCharHom a) i = .suN) :
    ∃ (ν : ℕ) (ψ : SL(ν, L) →* ModGL τ L) (σ : Fin ν → Fin ν → Fin τ.rank → ℤ) (κ : ℤ),
      3 ≤ ν ∧ IsSLFrame ψ σ ∧ κ ≠ 0 ∧
      (∀ a b, a ≠ b → iform (σ a b) (σ a b) = 2 * κ) ∧
      componentRoots (famCharHom a) i = frameRoots σ := by
  obtain ⟨N, b, j, hNprime, hN2, hTpb, hroots⟩ :=
    exists_isolating_element hτ a hp hp2 hap i
  have hNL : (N : L) ≠ 0 := by
    intro h
    exact hN2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hNprime).1
      ((CharP.cast_eq_zero_iff L 2 N).1 h)).symm
  have hk_bM : twistKindM S.ρ (rootCharHom b) j = .suN := by
    have h := twistKindM_eq_of_componentRoots_eq S.ρ hroots.symm
    rw [hk] at h
    exact h.symm
  have hk_b : twistKind S.ρ (rootCharHom b) j = .suN := by
    rw [← twistKindM_eq_twistKind S.ρ (rootCharHom b) j]
    exact hk_bM
  obtain ⟨h2b, hnb⟩ := suN_rank_ncard hk_b
  rcases hτ with rfl | rfl | rfl
  · obtain ⟨ν, ψ, σ, hν, hψ, hnorm, hΨb⟩ :=
      exists_frame_of_typeA_E6_T_of_prime S hNprime hNL hTpb j h2b hnb
    exact ⟨ν, ψ, σ, 1, hν, hψ, one_ne_zero, hnorm, hroots.symm.trans hΨb⟩
  · obtain ⟨ν, ψ, σ, hν, hψ, hnorm, hΨb⟩ :=
      exists_frame_of_typeA_E7_T_of_prime S hNprime hNL hTpb j h2b hnb
    exact ⟨ν, ψ, σ, 1, hν, hψ, one_ne_zero, hnorm, hroots.symm.trans hΨb⟩
  · obtain ⟨ν, ψ, σ, hν, hψ, hnorm, hΨb⟩ :=
      exists_frame_of_typeA_E8_T_of_prime S hNprime hNL hTpb j h2b hnb
    exact ⟨ν, ψ, σ, 1, hν, hψ, one_ne_zero, hnorm, hroots.symm.trans hΨb⟩

private theorem famSuN_quasisimple_or_small
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) (hp2 : p ≠ 2) {ι : Type}
    {a : ι → Fin τ.rank → Lˣ} (hT : ∀ u, rootDiagUnit τ (a u) ∈ S.D.torus)
    (hap : ∀ u j, a u j ^ p = 1) (h1 : ∃ u, rootDiagUnit τ (a u) ≠ 1)
    (i : KernelComponent (famCharHom a))
    (hk : twistKindM S.ρ (famCharHom a) i = .suN) :
    CFSG.IsQuasisimple (rationalComponentM S.ρ S.Γ (famCharHom a) i) ∨
      (Group.IsSolvable (rationalComponentM S.ρ S.Γ (famCharHom a) i) ∧
        S.D.q ^ componentOrbitLength S.ρ (componentRoots (famCharHom a) i) = 2 ∧
        (componentRoots (famCharHom a) i).ncard = 6) := by
  classical
  obtain ⟨ν, ψ, σ, κ, hν, hψ, hκ, hnorm, hΨ⟩ :=
    famSuN_frame hτ S hp hp2 hap i hk
  have hρ : ∀ γ ∈ kernelRoots (famCharHom a), S.ρ γ ∈ kernelRoots (famCharHom a) :=
    fun γ hγ => rho_mem_kernelRoots_famChar S a hT hγ
  obtain ⟨hs0, hs, hmin⟩ := fam_componentOrbitLength_spec S hρ i
  set s := componentOrbitLength S.ρ (componentRoots (famCharHom a) i) with hsdef
  have hout : ¬ twistInner (componentRoots (famCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[s]) := by
    intro h
    unfold twistKindM at hk
    rw [if_pos h] at hk
    exact absurd hk (by decide)
  have hmaps : ∀ x y, x ≠ y → (S.ρ : (Fin τ.rank → ℤ) → _)^[s] (σ x y) ∈ frameRoots σ := by
    intro x y hxy
    have h1 : σ x y ∈ componentRoots (famCharHom a) i := by
      rw [hΨ]
      exact ⟨x, y, hxy, rfl⟩
    have h2 : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] (σ x y) ∈
        (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (famCharHom a) i := ⟨_, h1, rfl⟩
    rw [hs, hΨ] at h2
    exact h2
  have hneg : ∀ (n : ℕ) (γ : Fin τ.rank → ℤ),
      (S.ρ : (Fin τ.rank → ℤ) → _)^[n] (-γ) = -(S.ρ : (Fin τ.rank → ℤ) → _)^[n] γ := by
    intro n
    induction n with
    | zero => exact fun γ => rfl
    | succ n ih =>
      intro γ
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, S.frob.neg_eq]
  rcases hψ.aut_cases hν hκ hnorm ((S.ρ : (Fin τ.rank → ℤ) → _)^[s]) hmaps (hneg s)
      (iform_rho_iterate S s) with ⟨π, hπ⟩ | ⟨π, hπ⟩
  · exfalso
    apply hout
    obtain ⟨w, hw, hwσ⟩ := hψ.exists_weyl_perm hκ hnorm π
    refine ⟨w, ?_, fun γ hγ => ?_⟩
    · rw [hΨ]
      exact hw
    · rw [hΨ] at hγ
      obtain ⟨x, y, hxy, rfl⟩ := hγ
      rw [hπ x y hxy, hwσ]
  · obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
    haveI : Fact r.Prime := ⟨hr⟩
    haveI : CharP L r := hchar
    obtain ⟨σQ, hσQ, f, hf1, hfker, hf2⟩ :=
      fam_two_suN_exists_hom S hρ i hν hψ hΨ π hπ hr hchar he hq
    obtain ⟨-, hqsC, hcardC⟩ :=
      stdUnitary_fixSubgroup hr (Nat.mul_pos he hs0) σQ hσQ hν
    have hQ : S.D.q ^ s = r ^ (e * s) := by rw [hq, ← pow_mul]
    by_cases hQ32 : (ν, S.D.q ^ s) = (3, 2)
    · have hq2 : S.D.q ^ s = 2 := congrArg Prod.snd hQ32
      have hn6 : (componentRoots (famCharHom a) i).ncard = 6 := by
        have hν3 : ν = 3 := congrArg Prod.fst hQ32
        calc (componentRoots (famCharHom a) i).ncard = (frameRoots σ).ncard := by rw [hΨ]
          _ = ν * (ν - 1) := CFSG.LocalAnalysis.GLTheoremA.kd147c_frameRoots_ncard hψ hκ hnorm
          _ = 6 := by rw [hν3]
      refine Or.inr ⟨CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.isSolvable_of_card_dvd_216 ?_,
        hq2, hn6⟩
      rw [hQ] at hQ32
      have h216 := hcardC hQ32
      rw [← h216]
      exact (Subgroup.card_dvd_of_le hf1).trans (Subgroup.card_range_dvd f)
    · refine Or.inl ?_
      have hne : (ν, r ^ (e * s)) ≠ (3, 2) := by
        intro h
        exact hQ32 (by rw [hQ]; exact h)
      have hQS := hqsC hne
      rw [le_antisymm hf1 (hf2 hQS.1)]
      exact isQuasisimple_range_of_ker_le_center hQS f hfker

theorem langFamTame_suN
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) (hp2 : p ≠ 2) {ι : Type}
    {a : ι → Fin τ.rank → Lˣ} (hT : ∀ u, rootDiagUnit τ (a u) ∈ S.D.torus)
    (hap : ∀ u j, a u j ^ p = 1) (h1 : ∃ u, rootDiagUnit τ (a u) ≠ 1)
    (i : KernelComponent (famCharHom a))
    (hk : twistKindM S.ρ (famCharHom a) i = .suN) :
    CFSG.IsQuasisimple (rationalComponentM S.ρ S.Γ (famCharHom a) i) ∨
      Group.IsSolvable (rationalComponentM S.ρ S.Γ (famCharHom a) i) :=
  (famSuN_quasisimple_or_small hτ S hp hp2 hT hap h1 i hk).imp_right And.left

theorem langFamTame_suN_isQuasisimple
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) (hp2 : p ≠ 2) {ι : Type}
    {a : ι → Fin τ.rank → Lˣ} (hT : ∀ u, rootDiagUnit τ (a u) ∈ S.D.torus)
    (hap : ∀ u j, a u j ^ p = 1) (h1 : ∃ u, rootDiagUnit τ (a u) ≠ 1)
    (i : KernelComponent (famCharHom a))
    (hk : twistKindM S.ρ (famCharHom a) i = .suN)
    (hbig : S.D.q ^ componentOrbitLength S.ρ (componentRoots (famCharHom a) i) ≠ 2 ∨
      (componentRoots (famCharHom a) i).ncard ≠ 6) :
    CFSG.IsQuasisimple (rationalComponentM S.ρ S.Γ (famCharHom a) i) := by
  rcases famSuN_quasisimple_or_small hτ S hp hp2 hT hap h1 i hk with h | ⟨-, hq2, hn6⟩
  · exact h
  · rcases hbig with hbig | hbig
    · exact absurd hq2 hbig
    · exact absurd hn6 hbig

end CFSG.StandardType.TableCRes
