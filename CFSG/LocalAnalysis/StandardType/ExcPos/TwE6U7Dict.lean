module

public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6U7Pieces
public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6U7Orbit
public import CFSG.LocalAnalysis.StandardType.ExcPos.NeighbourComponentOrbit
public import CFSG.LocalAnalysis.StandardType.GGLangExhaust
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RationalComponentEq
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwistedE6Base
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.FrobeniusOnRoots

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Assembly CFSG.Open CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.StandardType.LieCore CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] def ExcNbrDictTwo : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n f : ℕ) (ψ : (ggU .twistedE6 n f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X), GGSixPosHyp .twistedE6 n f ψ p G₀ B₁ D J L x →
    ∀ (R Rm : Subgroup X) (P : ExcPacket .E6 f p G₀ B₁ D J x R Rm),
    R ≤ J → Rm ≤ J → GGRootPosG0 .twistedE6 n f p ψ R Rm → P.b = 2 →
    ∀ e ∈ D, e ≠ 1 → ∀ K : Subgroup X, K ≤ G₀ →
      CFSG.Assembly.IsComponentOf K (Subgroup.centralizer {e}) → J ≤ K → K ≠ J →
      Odd (Nat.card (Subgroup.center ↥K)) → K ≠ G₀ →
      ∀ iK : KernelComponent (P.chiAt e), P.rootsJ ⊆ componentRoots (P.chiAt e) iK →
        componentRoots (P.chiAt e) iK ≠ P.rootsJ →
        (K.subgroupOf G₀).map P.η ≤
          rootSpan .E6 (ExcOmega f) (LieCore.ratOrbit P.ρ (componentRoots (P.chiAt e) iK)) →
        componentOrbitLength P.ρ (componentRoots (P.chiAt e) iK) = 1 →
        2 ≤ compRank P.rootsJ →
        (K.subgroupOf G₀).map P.η = rationalComponent P.ρ P.Δ.Γ (P.chiAt e) iK

private theorem lk0xu7n_image_eq_of_componentOrbitLength_eq_one {τ : Tag}
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {Ψ : Set (Fin τ.rank → ℤ)}
    (h : componentOrbitLength ρ Ψ = 1) :
    (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)) '' Ψ = Ψ := by
  let S : Set ℕ := {s : ℕ | 0 < s ∧
    (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[s] '' Ψ = Ψ}
  have hS : componentOrbitLength ρ Ψ = sInf S := rfl
  have hne : S.Nonempty := by
    by_contra hc
    rw [Set.not_nonempty_iff_eq_empty] at hc
    simp [hS, hc] at h
  have hmem := Nat.sInf_mem hne
  rw [← hS, h] at hmem
  simpa [S] using hmem.2

private theorem lk0xu7n_ratOrbit_eq_of_image_eq_self {τ : Tag}
    {ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)} {Ψ : Set (Fin τ.rank → ℤ)}
    (h : ρ '' Ψ = Ψ) : LieCore.ratOrbit ρ Ψ = Ψ := by
  ext γ
  constructor
  · rintro ⟨k, δ, hδ, rfl⟩
    induction k with
    | zero => simpa using hδ
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        simpa [h] using Set.mem_image_of_mem ρ ih
  · intro hγ
    exact ⟨0, γ, hγ, rfl⟩

private theorem lk0xu7n_ratOrbit_eq_self_of_componentOrbitLength_eq_one {τ : Tag}
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {Ψ : Set (Fin τ.rank → ℤ)}
    (h : componentOrbitLength ρ Ψ = 1) : LieCore.ratOrbit ρ Ψ = Ψ :=
  lk0xu7n_ratOrbit_eq_of_image_eq_self (lk0xu7n_image_eq_of_componentOrbitLength_eq_one h)

private theorem lk0xu7n_componentRoots_nonempty {τ : Tag} {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} (i : KernelComponent χ) :
    ∃ γ, γ ∈ componentRoots χ i := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep i
  exact ⟨x, x.2, rfl⟩

private theorem lk0xu7n_class_eq {X : Type} [Group X] {f p : ℕ}
    {G₀ B₁ D J : Subgroup X} {x : X} {R Rm : Subgroup X}
    (P : ExcPacket Tag.E6 f p G₀ B₁ D J x R Rm) {e : X} (he : e ∈ D)
    (i iK : KernelComponent (P.chiAt e))
    (hq : CFSG.IsQuasisimple ↥(rationalComponent P.ρ P.Δ.Γ (P.chiAt e) i))
    (hle : rationalComponent P.ρ P.Δ.Γ (P.chiAt e) i ≤
      rootSpan Tag.E6 (ExcOmega f) (LieCore.ratOrbit P.ρ (componentRoots (P.chiAt e) iK)))
    (horb : componentOrbitLength P.ρ (componentRoots (P.chiAt e) iK) = 1) :
    i = iK := by
  have hle_i : rationalComponent P.ρ P.Δ.Γ (P.chiAt e) i ≤
      rootSpan Tag.E6 (ExcOmega f)
        (LieCore.ratOrbit P.ρ (componentRoots (P.chiAt e) i)) := by
    rw [LieCore.rationalComponent_eq_ratComp]
    exact (Subgroup.commutator_le_self _).trans inf_le_left
  have hq' : CFSG.Assembly.IsQuasisimple
      ↥(rationalComponent P.ρ P.Δ.Γ (P.chiAt e) i) :=
    ⟨hq.1.commutator_eq_top, hq.2.1⟩
  have horbit := ratOrbit_eq_of_isQuasisimple_le (P.mapsTo_rho_chiAt he) P.frob.iform_eq
    hq' hle_i hle
  have hratK : LieCore.ratOrbit P.ρ (componentRoots (P.chiAt e) iK) =
      componentRoots (P.chiAt e) iK :=
    lk0xu7n_ratOrbit_eq_self_of_componentOrbitLength_eq_one horb
  have hsub : componentRoots (P.chiAt e) i ⊆ componentRoots (P.chiAt e) iK := by
    intro γ hγ
    have hmem : γ ∈ LieCore.ratOrbit P.ρ (componentRoots (P.chiAt e) i) :=
      ⟨0, γ, hγ, rfl⟩
    rw [horbit, hratK] at hmem
    exact hmem
  obtain ⟨α, hα⟩ := lk0xu7n_componentRoots_nonempty i
  exact eq_of_mem_componentRoots hα (hsub hα)

theorem excNbrDictTwo_holds :
    ExcNbrDictTwo := by
  intro X _ _ n f ψ p G₀ B₁ D J L x hP R Rm P hRJ hRmJ hpos hb
  intro e he he1 K hKG hKcomp hJK hKne hKodd hKG₀ iK hsub hne hspan horb h2
  obtain ⟨hψr, hψk, hLM, hZodd, hp, hp2, hB₁N, hB₁inn, hB₁el, -, hDB, hDcard,
    -, -, hJ, -, hx, hx1, -, -, -, -, -, -, -, -, -, -, -, -, hlast⟩ := hP
  obtain ⟨A, hB₁A, hAel, hAN, hAinn, hAC, hArest⟩ := hlast (Or.inr rfl)
  have hBC : B₁ ⊓ Subgroup.centralizer (G₀ : Set X) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have hyA : y ∈ A ⊓ Subgroup.centralizer (G₀ : Set X) := ⟨hB₁A hy.1, hy.2⟩
    rwa [hAC] at hyA
  obtain ⟨_hΔn, _hp_dvd, hf2, _hρgraph⟩ := excU7_orbit_data hp hp2 P hb
  have hcard : P.Δ.q = 2 ^ f := by
    rw [P.hq, GaloisField.card 2 f (by omega : f ≠ 0)]
  have hq : 5 ≤ p ∨ 4 ≤ P.Δ.q := by
    right
    rw [hcard]
    simpa using Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hf2
  have hqpow : IsPrimePow P.Δ.q ∧ ((P.Δ.q : ℕ) : GGL) = 0 := by
    constructor
    · rw [hcard]
      exact (Nat.prime_two.isPrimePow).pow (by omega : f ≠ 0)
    · rw [hcard, Nat.cast_pow]
      have htwo : ((2 : ℕ) : GGL) = 0 :=
        (CharP.cast_eq_zero_iff GGL 2 2).mpr (by norm_num : 2 ∣ 2)
      rw [htwo, zero_pow (by omega : f ≠ 0)]
  have hpq : ¬ p ∣ P.Δ.q := by
    rw [hcard]
    intro hdvd
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num : 0 < 2) (hp.dvd_of_dvd_pow hdvd)
    have hlt : 1 < p := hp.one_lt
    omega
  let S : LangSetup Tag.E6 GGL p := P.Δ.toSetup p P.ρ P.frob hp hq hqpow hpq P.finite
  let a : Fin Tag.E6.rank → GGLˣ := P.coord e
  have hT : rootDiagUnit Tag.E6 a ∈ S.D.torus := P.coord_torus e he
  have hap : ∀ i, a i ^ p = 1 := P.coord_pow e he
  have hpL : (p : GGL) ≠ 0 := by
    intro h0
    have hdvd : 2 ∣ p := (CharP.cast_eq_zero_iff GGL 2 p).mp h0
    obtain ⟨j, hj⟩ := hdvd
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
    omega
  have h1 : rootDiagUnit Tag.E6 a ≠ 1 := by
    intro hdiag
    have hΘ : P.Θ ⟨e, hDB he⟩ = 1 := by
      rw [P.Θ_eq_coord ⟨e, hDB he⟩ he, hdiag]
    have hcent : e ∈ Subgroup.centralizer (G₀ : Set X) :=
      (P.Θ_eq_one ⟨e, hDB he⟩).1 hΘ
    have hbot : e ∈ (⊥ : Subgroup X) := by
      have hmem : e ∈ B₁ ⊓ Subgroup.centralizer (G₀ : Set X) := ⟨hDB he, hcent⟩
      rwa [hBC] at hmem
    exact he1 (Subgroup.mem_bot.1 hbot)
  let Kη : Subgroup (ModGL Tag.E6 GGL) := (K.subgroupOf G₀).map P.η
  have hcomp : CFSG.Open.IsComponentOf Kη
      (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 a}) :=
    (CFSG.Assembly.isComponentOf_iff_open (L := Kη)
      (K := S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 a})).mp
      (P.attach_nbr e he K hKG hKcomp)
  obtain ⟨i, hKi, hiq⟩ :=
    CFSG.HardMathSupport.Timmesfeld.LangTorus.exists_eq_rationalComponent_of_isComponentOf
      S hp hT hap h1
      (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.langSetup_hTame_of_prime
        S hp hpL (fun h => absurd h (by decide)) hT hap h1)
      hcomp
  have hiq' : CFSG.IsQuasisimple ↥(rationalComponent P.ρ P.Δ.Γ (P.chiAt e) i) := hiq
  have hKi' : Kη = rationalComponent P.ρ P.Δ.Γ (P.chiAt e) i := hKi
  have hle : rationalComponent P.ρ P.Δ.Γ (P.chiAt e) i ≤
      rootSpan Tag.E6 (ExcOmega f) (LieCore.ratOrbit P.ρ (componentRoots (P.chiAt e) iK)) := by
    rw [← hKi']
    exact hspan
  have hclass : i = iK := lk0xu7n_class_eq P he i iK hiq' hle horb
  change Kη = rationalComponent P.ρ P.Δ.Γ (P.chiAt e) iK
  rw [hKi', hclass]

end CFSG.StandardType.LieKnownR2.ExcPos
