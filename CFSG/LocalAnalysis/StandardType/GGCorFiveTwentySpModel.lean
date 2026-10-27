module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpElt
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflSp

public section

namespace CFSG.StandardType

open CFSG.Assembly TableBSymp SpCoord Multiplicative

namespace SpModel

variable {K : Type} [Field K] {m : ℕ}

theorem projMk_spPermSp_conj_spTorus {p : ℕ} {ζ : Kˣ} (hζ : ζ ^ p = 1)
    (σ : Equiv.Perm (Fin m)) (f : Fin m → Multiplicative (ZMod p)) :
    LargeEvenProjMk _ (NbrSp.spPermSp (K := K) σ) * spTorus hζ f *
        (LargeEvenProjMk _ (NbrSp.spPermSp (K := K) σ))⁻¹ = spTorus hζ (permAut σ f) := by
  rw [permAut_apply]
  change LargeEvenProjMk _ (NbrSp.spPermSp (K := K) σ) * LargeEvenProjMk _ (spTorusSp hζ f) *
      (LargeEvenProjMk _ (NbrSp.spPermSp (K := K) σ))⁻¹ =
    LargeEvenProjMk _ (spTorusSp hζ (f ∘ ⇑σ⁻¹))
  rw [← map_inv, ← map_mul, ← map_mul, NbrSp.spPermSp_conj_spTorusSp]

theorem ggTorusSignedElt_sp [Finite K] [CharP K 2] [NeZero m] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) :
    GGTorusSignedElt p m (LargeEvenProj (LargeEvenSpGroup K m)) := by
  classical
  intro E hE hr _
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζo⟩ := ReflSp.exists_orderOf_eq (K := K) hp hpq
  have hζ : ζ ^ p = 1 := by
    rw [← hζo]
    exact pow_orderOf_eq_one ζ
  obtain ⟨x, hτE, hEτ⟩ := ReflSp.exists_conj_spTorus hp hp2 hζo hζ hE hr
  have hπi : Function.Injective (LargeEvenProjMk (LargeEvenSpGroup K m)) :=
    AutPSp.proj_injective (n := m) (K := K)
  set τ : (Fin m → Multiplicative (ZMod p)) →* LargeEvenProj (LargeEvenSpGroup K m) :=
    (MulAut.conj x).toMonoidHom.comp (spTorus hζ) with hτ
  have hτapp : ∀ f, τ f = x * spTorus hζ f * x⁻¹ := fun f => rfl
  have hconjτ : ∀ (s : LargeEvenProj (LargeEvenSpGroup K m))
      (α : (Fin m → Multiplicative (ZMod p)) → (Fin m → Multiplicative (ZMod p))),
      (∀ f, s * spTorus hζ f * s⁻¹ = spTorus hζ (α f)) →
      ∀ f, (x * s * x⁻¹) * τ f * (x * s * x⁻¹)⁻¹ = τ (α f) := by
    intro s α hs f
    rw [hτapp, hτapp, ← hs f]
    group
  have hg' : ∀ g : LargeEvenProj (LargeEvenSpGroup K m), (∀ e ∈ E, g * e * g⁻¹ ∈ E) →
      ∀ f, ∃ f', g * τ f * g⁻¹ = τ f' := fun g hg f => by
    obtain ⟨f', hf'⟩ := hEτ _ (hg _ (hτE f))
    exact ⟨f', hf'.symm⟩
  refine ⟨m, τ, (MulAut.conj x).injective.comp
      (spTorus_injective hζ hζo (hp.odd_of_ne_two hp2)), ?_,
    fun i => ⟨_, hconjτ _ (sgnAut i) fun f => spSwap_conj_spTorus hζ i f⟩,
    fun σ => ⟨_, hconjτ _ (permAut σ) (projMk_spPermSp_conj_spTorus hζ σ)⟩, fun g hg => ?_⟩
  · ext e
    constructor
    · rintro ⟨f, rfl⟩
      exact hτE f
    · intro he
      obtain ⟨f, hf⟩ := hEτ e he
      exact ⟨f, hf⟩
  ·
    obtain ⟨g₀, hg₀⟩ := QuotientGroup.mk'_surjective
      ((LargeEvenScalars (Fin m ⊕ Fin m) K).subgroupOf (LargeEvenSpGroup K m)) (x⁻¹ * g * x)
    obtain ⟨j, ε, hε, hj⟩ := ReflSp.exists_monomial_data hζo hζ (g₀ : GL (Fin m ⊕ Fin m) K)
    have hrel : ∀ f f', g * τ f * g⁻¹ = τ f' →
        (g₀ : GL (Fin m ⊕ Fin m) K) * spTorusGL hζ f =
          spTorusGL hζ f' * (g₀ : GL (Fin m ⊕ Fin m) K) := by
      intro f f' hff'
      rw [hτapp, hτapp] at hff'
      have h1 : (x⁻¹ * g * x) * spTorus hζ f * (x⁻¹ * g * x)⁻¹ = spTorus hζ f' := by
        calc (x⁻¹ * g * x) * spTorus hζ f * (x⁻¹ * g * x)⁻¹ =
              x⁻¹ * (g * (x * spTorus hζ f * x⁻¹) * g⁻¹) * x := by group
          _ = x⁻¹ * (x * spTorus hζ f' * x⁻¹) * x := by rw [hff']
          _ = spTorus hζ f' := by group
      have h2 : g₀ * spTorusSp hζ f * g₀⁻¹ = spTorusSp hζ f' := by
        apply hπi
        rw [map_mul, map_mul, map_inv]
        exact (congrArg (fun y => y * spTorus hζ f * y⁻¹) hg₀).trans h1
      have h4 := congrArg (fun y : LargeEvenSpGroup K m => (y : GL (Fin m ⊕ Fin m) K)) h2
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, spTorusSp_coe] at h4
      rw [← h4]
      group
    have hjinj : Function.Injective j := by
      intro i i' hii'
      by_contra hne
      obtain ⟨f', hf'⟩ := hg' g hg (Pi.mulSingle i (ofAdd (1 : ZMod p)))
      have h1 := hj _ _ (hrel _ _ hf') i
      have h2 := hj _ _ (hrel _ _ hf') i'
      rw [← hii', h1, toAdd_mulSingle, toAdd_mulSingle, ite_eq_left rfl,
        ite_eq_right (Ne.symm hne), mul_one, mul_zero] at h2
      exact coord_sign_ne_zero hp (hε i) h2
    exact ⟨Equiv.ofBijective j hjinj.bijective_of_finite, ε, hε,
      fun f f' hff' i => hj f f' (hrel f f' hff') i⟩

theorem ggTorusWeylInputs_symplectic [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) (hm : 1 ≤ m) :
    GGTorusPseudoReflGen p m (LargeEvenProj (LargeEvenSpGroup K m))
        (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m)) ∧
      GGTorusIrred p m (LargeEvenProj (LargeEvenSpGroup K m))
        (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m)) ∧
      GGTorusWeylNormInner p m (LargeEvenProj (LargeEvenSpGroup K m))
        (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m)) := by
  have : NeZero m := ⟨by omega⟩
  have h := ggTorusSignedElt_sp (K := K) (m := m) hp hp2 hpq
  exact ⟨ggTorusPseudoReflGen_of_signedElt hp hp2 sp_I_subset_inn center_spProj_eq_bot h,
    ggTorusIrred_of_signedElt hp hp2 sp_I_subset_inn center_spProj_eq_bot h,
    ggTorusWeylNormInner_of_signedElt hp hp2 sp_I_subset_inn center_spProj_eq_bot h⟩

theorem recipeSymplectic_weylInputs {l n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : p ∣ 2 ^ n - 1) (hl : 1 ≤ l) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeSymplectic l (2 ^ n) false Q) :
    LargeEvenRecipeSymplectic l (2 ^ n) false fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGTorusPseudoReflGen p r R I ∧ GGTorusIrred p r R I ∧
        GGTorusWeylNormInner p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have := charP_two_of_card hK
  have hpq : p ∣ Nat.card K - 1 := by
    rw [hK]
    exact hpn
  exact ⟨K, inferInstance, inferInstance, hK, hQ, l, ggTorusLift_symplectic hp hp2 hpq hl,
    ggTorusWeylInputs_symplectic hp hp2 hpq hl⟩

theorem largeEvenLabelAll_weylInputs_symplectic {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGReflSpLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusPseudoReflGen p r R I ∧
      GGTorusIrred p r R I ∧ GGTorusWeylNormInner p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hpn⟩ := h
  have hn : 1 ≤ n := hlab.1
  have hp2 := ne_two_of_dvd_two_pow_sub_one hn hpn
  intro Q hQ
  rcases htag with h | h <;> dsimp only at h <;> subst h <;>
    exact recipeSymplectic_weylInputs hp hp2 hpn (le_trans (by norm_num) hlab.2.1) hQ

end SpModel

end CFSG.StandardType

end
