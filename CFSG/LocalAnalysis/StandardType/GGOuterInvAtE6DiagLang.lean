module

public import CFSG.LocalAnalysis.StandardType.GGOuterInvAtE6
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang.Core
public import CFSG.LieType.Chevalley.CLSOddE7RationalDerivedIndex
public import CFSG.LieType.AlgebraicGroups.ToralTwistPinningFrobenius
public import CFSG.LieType.Chevalley.RootDiagonalWeylTransporter
public import CFSG.LieType.AlgebraicGroups.ToralTwistSemilinearDatum
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtUntw
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LangTorusSylowFree
public import CFSG.LocalAnalysis.StandardType.GGOuterInvAtE6Holds
public import CFSG.LocalAnalysis.StandardType.GGOuterInvAtE6OddLemmas

public section

namespace CFSG.StandardType

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE

theorem exists_langSetup_of_toral_datum_of_prime_formula {τ : Tag} {L : Type} [Field L]
    [IsAlgClosed L] {ℓ f : ℕ} (hℓ : ℓ.Prime) [CharP L ℓ] (hf : 1 ≤ f) (D : LangDatum τ L)
    (hDq : D.q = ℓ ^ f) {p₀ : ℕ} (hp₀ : p₀.Prime) (hp₀ℓ : p₀ ≠ ℓ)
    (hq₀ : 5 ≤ p₀ ∨ 4 ≤ D.q) {p : ℕ} (hfin : Finite D.model) {C : Type} [Group C]
    (ι₀ : C →* ModGL τ L) (hι₀ : Function.Injective ι₀)
    (hΓ : D.Γ = ι₀.range.map (MulAut.conj D.g0⁻¹).toMonoidHom) (β : MulAut C) {u : ModGL τ L}
    (hβ : ∀ c, ι₀ (β c) = u * ι₀ c * u⁻¹)
    (hmem : u ∈ D.torus.map (MulAut.conj D.g0).toMonoidHom) (hup : u ^ p = 1) (hu1 : u ≠ 1) :
    ∃ (S : LangSetup τ L p₀) (a : Fin τ.rank → Lˣ) (ι : C →* ModGL τ L),
      S.D = D ∧ rootDiagUnit τ a ∈ S.D.torus ∧ (∀ i, a i ^ p = 1) ∧ rootDiagUnit τ a ≠ 1 ∧
      Function.Injective ι ∧ ι.range = S.Γ ∧
      (∀ c, ι c = D.g0⁻¹ * ι₀ c * D.g0) ∧
      ∀ c, ι (β c) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹ := by
  classical
  obtain ⟨y, hy, hyu⟩ := hmem
  have hyu' : y = D.g0⁻¹ * u * D.g0 := by
    have h : D.g0 * y * D.g0⁻¹ = u := hyu
    rw [← h]
    group
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 hy).1
  have hyp : y ^ p = 1 := by
    have h := conj_pow (a := D.g0⁻¹) (b := u) (i := p)
    rw [inv_inv] at h
    rw [hyu', h, hup]
    group
  have hap : ∀ i, a i ^ p = 1 := by
    have h1 : rootDiagUnit τ (a ^ p) = rootDiagUnit τ 1 := by
      have : rootDiagUnit τ (a ^ p) = rootDiagUnit τ a ^ p :=
        (rootDiagUnitHom τ L).map_pow a p
      rw [this, ← ha, hyp, CFSG.LieType.Chevalley.rootDiagUnit_one]
    have h2 : a ^ p = 1 := CFSG.LieType.Chevalley.rootDiagUnit_injective h1
    exact fun i => congrFun h2 i
  have h1 : rootDiagUnit τ a ≠ 1 := by
    intro h
    apply hu1
    rw [← ha, hyu'] at h
    have : u = D.g0 * (D.g0⁻¹ * u * D.g0) * D.g0⁻¹ := by group
    rw [this, h]
    group
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hqpow : IsPrimePow D.q ∧ ((D.q : ℕ) : L) = 0 := by
    rw [hDq]
    exact ⟨hℓ.isPrimePow.pow (by omega), (CharP.cast_eq_zero_iff L ℓ _).2
      (dvd_pow_self ℓ (by omega))⟩
  have hpq : ¬ p₀ ∣ D.q := by
    rw [hDq]
    intro h
    exact hp₀ℓ ((Nat.prime_dvd_prime_iff_eq hp₀ hℓ).1 (hp₀.dvd_of_dvd_pow h))
  obtain ⟨ρ, hρ⟩ := frobeniusOnRoots_proved τ L D
  let ι : C →* ModGL τ L := (MulAut.conj D.g0⁻¹).toMonoidHom.comp ι₀
  have hι : ∀ c, ι c = D.g0⁻¹ * ι₀ c * D.g0 := fun c => by
    change (MulAut.conj D.g0⁻¹) (ι₀ c) = _
    rw [MulAut.conj_apply, inv_inv]
  refine ⟨D.toSetup p₀ ρ hρ hp₀ hq₀ hqpow hpq hfin, a, ι, rfl, ?_, hap, h1,
    (MulAut.conj D.g0⁻¹).injective.comp hι₀, ?_, hι, fun c => ?_⟩
  · exact ha ▸ hy
  · show ι.range = D.Γ
    rw [hΓ]
    exact MonoidHom.range_comp (MulAut.conj D.g0⁻¹).toMonoidHom ι₀
  · rw [hι, hι, hβ c, ← ha, hyu']
    group

theorem e6_solvable_of_ambient_centralizer_of_diag {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (β : MulAut (adjointGroup Tag.E6 K))
    (S : LangSetup Tag.E6 (AlgebraicClosure K) p)
    (a₀ : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ)
    (ι : ↥(adjointGroup Tag.E6 K) →* ModGL Tag.E6 (AlgebraicClosure K))
    (hsol : Group.IsSolvable
      ↥(adjointGroup Tag.E6 (AlgebraicClosure K) ⊓
        Subgroup.centralizer {rootDiagUnit Tag.E6 a₀}))
    (hinj : Function.Injective ι) (hrange : ι.range = S.Γ)
    (hιconj : ∀ c, ι (β c) =
      rootDiagUnit Tag.E6 a₀ * ι c * (rootDiagUnit Tag.E6 a₀)⁻¹)
    (L₁ : Subgroup (adjointGroup Tag.E6 K)) (hL₁ : ∀ y ∈ L₁, β y = y) :
    Group.IsSolvable L₁ := by
  classical
  have hΓadj : S.Γ ≤ adjointGroup Tag.E6 (AlgebraicClosure K) := by
    change ⁅S.D.model, S.D.model⁆ ≤ adjointGroup Tag.E6 (AlgebraicClosure K)
    exact (commutator_le_self_of_subgroup S.D.model).trans inf_le_left
  let f' : ↥L₁ →* ↥(adjointGroup Tag.E6 (AlgebraicClosure K) ⊓
      Subgroup.centralizer {rootDiagUnit Tag.E6 a₀}) :=
    { toFun := fun y => ⟨ι (y : adjointGroup Tag.E6 K), by
        refine Subgroup.mem_inf.mpr ⟨hΓadj ?_, ?_⟩
        · rw [← hrange]
          exact ⟨y, rfl⟩
        · rw [Subgroup.mem_centralizer_singleton_iff]
          have hy : β (y : adjointGroup Tag.E6 K) = y := hL₁ y y.2
          have h := hιconj (y : adjointGroup Tag.E6 K)
          rw [hy] at h
          calc ι (y : adjointGroup Tag.E6 K) * rootDiagUnit Tag.E6 a₀ =
                (rootDiagUnit Tag.E6 a₀ * ι (y : adjointGroup Tag.E6 K) *
                  (rootDiagUnit Tag.E6 a₀)⁻¹) * rootDiagUnit Tag.E6 a₀ := by rw [← h]
              _ = rootDiagUnit Tag.E6 a₀ * ι (y : adjointGroup Tag.E6 K) := by group⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro y z
        apply Subtype.ext
        simp }
  have hf'inj : Function.Injective f' := by
    intro y z hyz
    apply Subtype.ext
    exact hinj (congrArg
      (fun w : ↥(adjointGroup Tag.E6 (AlgebraicClosure K) ⊓
        Subgroup.centralizer {rootDiagUnit Tag.E6 a₀}) =>
        (w : ModGL Tag.E6 (AlgebraicClosure K))) hyz)
  haveI : Group.IsSolvable ↥(adjointGroup Tag.E6 (AlgebraicClosure K) ⊓
      Subgroup.centralizer {rootDiagUnit Tag.E6 a₀}) := hsol
  exact Group.isSolvable_of_isSolvable_injective hf'inj

theorem e6_false_of_component_fixed_of_diag {K : Type} [Field K] [Finite K] [CharP K 2]
    [ExpChar (AlgebraicClosure K) 2] {f s p : ℕ} {σ : K ≃+* K}
    (g : adjointGroup Tag.E6 K) (a : Fin Tag.E6.rank → Kˣ) (ε : ℕ)
    (β : MulAut (adjointGroup Tag.E6 K))
    (S : LangSetup Tag.E6 (AlgebraicClosure K) p)
    (a₀ : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ)
    (ι : ↥(adjointGroup Tag.E6 K) →* ModGL Tag.E6 (AlgebraicClosure K))
    (i : KernelComponent (rootCharHom a₀))
    (hT : rootDiagUnit Tag.E6 a₀ ∈ S.D.torus)
    (hιconj : ∀ c, ι (β c) =
      rootDiagUnit Tag.E6 a₀ * ι c * (rootDiagUnit Tag.E6 a₀)⁻¹)
    (hinj : Function.Injective ι) (hrange : ι.range = S.Γ)
    (hDq : S.D.q = 2 ^ f) (hs0 : 0 < s) (hs : s < f)
    (z' : ModGL Tag.E6 (AlgebraicClosure K))
    (hconj : ∀ c, z' * Units.map (entrywiseHom (iterateFrobenius (AlgebraicClosure K) 2 s))
      (ι c) * z'⁻¹ = ι ((MulAut.conj g * exactNormalAut Tag.E6 K a σ ε) c))
    (hfix : ∀ y, β y = y → (MulAut.conj g * exactNormalAut Tag.E6 K a σ ε) y = y) :
    False := by
  classical
  set FrL : ModGL Tag.E6 (AlgebraicClosure K) →*
      ModGL Tag.E6 (AlgebraicClosure K) :=
    Units.map (entrywiseHom (iterateFrobenius (AlgebraicClosure K) 2 s)) with hFrL
  have hfix' : ∀ y ∈ rationalComponent S.ρ S.Γ (rootCharHom a₀) i,
      z' * FrL y * z'⁻¹ = y := by
    intro y hy
    obtain ⟨hyΓ, hyd⟩ := Subgroup.mem_inf.mp ((langSubnormal_of_mem_torus S hT i).1 hy)
    obtain ⟨c, hcy⟩ := by
      rw [← hrange] at hyΓ
      exact hyΓ
    have hcomm' : y * rootDiagUnit Tag.E6 a₀ = rootDiagUnit Tag.E6 a₀ * y :=
      Subgroup.mem_centralizer_singleton_iff.mp hyd
    have hfixc : rootDiagUnit Tag.E6 a₀ * y * (rootDiagUnit Tag.E6 a₀)⁻¹ = y := by
      calc rootDiagUnit Tag.E6 a₀ * y * (rootDiagUnit Tag.E6 a₀)⁻¹ =
            (y * rootDiagUnit Tag.E6 a₀) * (rootDiagUnit Tag.E6 a₀)⁻¹ := by
              rw [hcomm'.symm]
          _ = y := by group
    have hβc : β c = c := by
      apply hinj
      rw [hιconj c, hcy, hfixc]
    rw [← hcy, hconj c, hfix c hβc]
  have hτne : Tag.E6 ≠ .G2 := by decide
  have hq4 : S.D.q ≠ 4 ∨ SimplyLacedTag Tag.E6 := Or.inr (Or.inr (Or.inl rfl))
  exact outer_false_of_component_fixed_by_twist (S := S) (a := a₀) (i := i)
    (r := 2) (f := f) (j := s) hτne hT Nat.prime_two hDq hq4 hs0 hs z' hfix'

end CFSG.StandardType
