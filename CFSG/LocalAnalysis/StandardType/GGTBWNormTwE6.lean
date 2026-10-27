module

public import CFSG.LocalAnalysis.StandardType.GGTBWNormE6Split
public import CFSG.LocalAnalysis.StandardType.GGTBE6IndTwistAlign

public noncomputable section

namespace CFSG.StandardType.TwE6WNorm

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.TwistedE6 CFSG.StandardType.TBE6IndTwist
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem exists_coordinates_aligned {K L : Type} [Field K] [Finite K] [CharP K 2]
    [Group L] [Finite L] (θ : K ≃+* K)
    (hθ : ∀ c, θ.toRingHom (θ.toRingHom c) = c)
    (l : K) (hl : θ.toRingHom l = l + 1)
    {f p : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (hθq : ∀ c, θ.toRingHom c = c ^ (2 ^ f))
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) [NeZero p]
    (ζ : CFSG.LieType.Steinberg.normOne θ) (hζ : ζ ^ p = 1)
    (hζo : orderOf (ζ : Kˣ) = p)
    (ψ : L →* graphFixedRootGroup TwistTag.E6 K θ.toRingHom)
    (hψ : Function.Surjective ψ) (A : Subgroup (MulAut L))
    (Λ : graphFixedRootGroup TwistTag.E6 K θ.toRingHom →* MulAut L)
    (hΛ : Function.Injective Λ) (hΛn : ∀ x : L, Λ (ψ x) = MulAut.conj x)
    (hA : (((CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf hK θ.toRingHom hθq).comp
      (langPFrame K θ hθ l hl ζ hζ)).range).map Λ = A) :
    ∃ κ : Multiplicative (Fin Tag.E6.rank → ZMod p) ≃* ↥A,
      (ExcWeylOuter.torusMulAut Tag.E6 p).range.map (MulAut.congr κ).toMonoidHom =
        ggAutomizer (MulAut.conj : L →* MulAut L).range A := by
  let : Fact p.Prime := ⟨hp⟩
  let q := CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf hK θ.toRingHom hθq
  have hqs : Function.Surjective q :=
    CFSG.SeitzReduction.F4Pilot.twistedIsogenyC_surjective hf hK θ.toRingHom hθq
  have hqc : q.ker ≤ Subgroup.center (fixedGroup K θ.toRingHom) :=
    (CFSG.SeitzReduction.F4Pilot.ker_twistedIsogenyC hf hK θ.toRingHom hθq).le
  let τ := q.comp (langPFrame K θ hθ l hl ζ hζ)
  have hζo' : orderOf ζ = p := by rw [← Subgroup.orderOf_coe ζ]; exact hζo
  have hτ : Function.Injective τ :=
    cover_langPFrame_injective K θ hθ l hl hK hθq hp hp3 q hqc ζ hζ hζo'
  have hκ : (Λ.comp τ).range = A := by rw [MonoidHom.range_comp]; exact hA
  let κ : Multiplicative (Fin Tag.E6.rank → ZMod p) ≃* ↥A :=
    (MonoidHom.ofInjective (f := Λ.comp τ) (hΛ.comp hτ)).trans (MulEquiv.subgroupCongr hκ)
  have hk : ∀ u, (κ u : MulAut L) = Λ (τ u) := fun _ => rfl
  have hR : Λ.range = (MulAut.conj : L →* MulAut L).range := by
    ext a
    constructor
    · rintro ⟨g, rfl⟩
      obtain ⟨x, rfl⟩ := hψ g
      exact ⟨x, (hΛn x).symm⟩
    · rintro ⟨x, rfl⟩
      exact ⟨ψ x, hΛn x⟩
  obtain ⟨hnE, eW, heW⟩ :=
    cover_marked_langPFrame K θ hθ l hl hf hK hθq hp hp2 hp3 ζ hζ hζo q hqs hqc
  obtain ⟨hnA, eA, heA⟩ := markedWeyl_map τ.range Λ hΛ hA
    (fun i => q (langWeylHom K θ.toRingHom hθ hl (simple .E6 i))) hnE eW heW
  let ρ : WeylGroup Tag.E6 →* MulAut ↥A :=
    (MulAut.congr κ).toMonoidHom.comp (ExcWeylOuter.torusMulAut Tag.E6 p)
  have hτσ : ∀ i u, τ (ExcWeylOuter.torusMulAut Tag.E6 p (simple Tag.E6 i) u) =
      q (langWeylHom K θ.toRingHom hθ hl (simple Tag.E6 i)) * τ u *
        (q (langWeylHom K θ.toRingHom hθ hl (simple Tag.E6 i)))⁻¹ := by
    intro i u
    have hh := langWeylHom_conj_langPFrame K θ hθ l hl ζ hζ (simple Tag.E6 i)
      (Multiplicative.toAdd u)
    have hu : ExcWeylOuter.torusMulAut Tag.E6 p (simple Tag.E6 i) u =
        Multiplicative.ofAdd (TableBExc.torusAct .E6 p (simple .E6 i) (Multiplicative.toAdd u)) :=
      congrArg (fun x => ExcWeylOuter.torusMulAut Tag.E6 p (simple Tag.E6 i) x)
        (ofAdd_toAdd u).symm
    rw [hu]
    change q (langPFrame K θ hθ l hl ζ hζ (Multiplicative.ofAdd
      (TableBExc.torusAct Tag.E6 p (simple Tag.E6 i) (Multiplicative.toAdd u)))) = _
    rw [ofAdd_toAdd] at hh
    rw [← hh, map_mul, map_mul, map_inv]
    rfl
  have hκσ : ∀ i u, (κ (ExcWeylOuter.torusMulAut Tag.E6 p (simple Tag.E6 i) u) : MulAut L) =
      Λ (q (langWeylHom K θ.toRingHom hθ hl (simple Tag.E6 i))) * (κ u : MulAut L) *
        (Λ (q (langWeylHom K θ.toRingHom hθ hl (simple Tag.E6 i))))⁻¹ := by
    intro i u
    rw [hk, hτσ, map_mul, map_mul, map_inv, hk]
  have hsimple : ∀ i, ρ (simple Tag.E6 i) = ggConjAut A (hnA i) := by
    intro i
    apply MulEquiv.ext
    intro a
    have hv : ρ (simple Tag.E6 i) a =
        κ (ExcWeylOuter.torusMulAut Tag.E6 p (simple Tag.E6 i) (κ.symm a)) := by
      rw [show ρ (simple Tag.E6 i) = MulAut.congr κ
        (ExcWeylOuter.torusMulAut Tag.E6 p (simple Tag.E6 i)) from rfl, MulAut.congr_apply]
      rfl
    rw [hv]
    apply Subtype.ext
    rw [ggConjAut_apply]
    have he := hκσ i (κ.symm a)
    simpa only [κ.apply_symm_apply] using he
  have hhom : (ggAutomizer Λ.range A).subtype.comp eA.toMonoidHom = ρ := by
    apply (coxeterSystem Tag.E6).ext_simple
    intro i
    change (eA (simple Tag.E6 i) : MulAut ↥A) = ρ (simple Tag.E6 i)
    have he := heA i
    rw [← CoxeterMatrix.toCoxeterSystem_simple] at he
    exact he.trans (hsimple i).symm
  have hρ : ρ.range = ggAutomizer Λ.range A := by
    rw [← hhom]
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact (eA g).2
    · intro hx
      obtain ⟨g, hg⟩ := eA.surjective ⟨x, hx⟩
      exact ⟨g, congrArg Subtype.val hg⟩
  refine ⟨κ, ?_⟩
  rw [← hR, ← hρ]
  exact (MonoidHom.range_comp _ _).symm

theorem ggTorusWNormSC_recipe_twE6_of_ge_five {K : Type} [Field K] [Finite K] [CharP K 2]
    {f p : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ f + 1) :
    GGTorusWNormSC p (TwE6Delta.RecipeR K f) (TwE6Delta.RecipeI K f) := by
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  have hf1 : 1 ≤ f := by omega
  obtain ⟨θ, hθq, hθo, -⟩ :=
    finite_graph_field_parameter_fields TwistTag.E6 Nat.prime_two hf1 K hK
  have hθ : ∀ c, θ.toRingHom (θ.toRingHom c) = c :=
    CFSG.SeitzReduction.F4Pilot.involutive_of_natCard_eq hK (fun c => hθq c)
  have hθ1 : θ ≠ 1 := by
    change orderOf θ = 2 at hθo
    intro h
    rw [h, orderOf_one] at hθo
    omega
  have hθ2 : θ * θ = 1 := by
    change orderOf θ = 2 at hθo
    simpa only [hθo, pow_two] using pow_orderOf_eq_one θ
  obtain ⟨l, hl⟩ := CFSG.SeitzReduction.LinearPilot.exists_trace_one_of_involution hθ1 hθ2
  obtain ⟨ζ, hζo⟩ := exists_normOne_prime K θ hf1 hK (fun c => hθq c) hp hpq
  have hζ : ζ ^ p = 1 := by
    apply Subtype.ext
    change (ζ : Kˣ) ^ p = 1
    rw [← hζo, pow_orderOf_eq_one]
  intro L _ _ ψ hψ hker hperf A hA hAI h3 hsc
  obtain ⟨ψa, hψa, hka, Λ, hΛ, hΛn, hFA⟩ :=
    exists_aligned_graph_of_selfCent K θ hθ l hl hf1 hK (fun c => hθq c)
      hp (by omega) hpq ζ hζ hζo ψ A
      (show GGTorusTBGroup p 3 (TwE6Delta.RecipeR K f) (TwE6Delta.RecipeI K f) L ψ A from
        ⟨hψ, hker, hperf, hA, hAI, h3, h3, hsc⟩)
  obtain ⟨κ, hW⟩ := exists_coordinates_aligned θ hθ l hl hf1 hK (fun c => hθq c)
    hp (by omega) (by omega) ζ hζ hζo ψa hψa A Λ hΛ hΛn hFA
  intro _ Γ _ _ M C V _ _ ι φ h α _ _ _ _ hgen s hs
  exact E6WNorm.wNormConcl_of_full_frame (by omega) A κ hW ι φ h α hgen hs

theorem largeEvenLabelAll_wnorm_twE6_of_ge_five {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {lab : LargeEvenLabel} (htag : lab.tag = .twE6) (hf : 1 ≤ lab.n)
    (hpq : p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I := by
  obtain ⟨t, r, f⟩ := lab
  dsimp only at htag hpq hf ⊢
  subst htag
  have hf2 : 2 ≤ f := by
    by_contra h
    have hf' : f = 1 := by omega
    rw [hf'] at hpq
    have hpThree : p = 3 := (Nat.dvd_prime Nat.prime_three).mp hpq |>.resolve_left hp.ne_one
    omega
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQK⟩ := hQ
  let : CharP K 2 := charP_two_of_card (m := f * 2) (by rw [hK, ← pow_mul])
  refine ⟨K, i1, i2, hK, hQK, ?_⟩
  exact ggTorusWNormSC_recipe_twE6_of_ge_five hf2 hK hp hp5 hpq

end CFSG.StandardType.TwE6WNorm
