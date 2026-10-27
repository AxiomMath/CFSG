module

public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6ThreeFrameA
public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6ThreeClassA
public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6ThreeKer
public import CFSG.LocalAnalysis.StandardType.GGTBJE6ThreeWeyl
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6Center
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCTGraphTwisted

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc
  TableBExc.E6Three CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.LieType.Steinberg.TwistedE6

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma tw1f_isReflection_of_sigma {p k : ℕ} {L' : Type} [Group L']
    {A : Subgroup (MulAut L')} {Φ : A →* Multiplicative (Fin k → ZMod p)}
    (hΦ : Function.Injective Φ) {ι : Type}
    {s : ι → (Fin k → ZMod p) → Fin k → ZMod p} {n : ι → L'} {σ : ι → A → A}
    {hnN : ∀ i, MulAut.conj (n i) ∈ Subgroup.normalizer (A : Set (MulAut L'))}
    (hgg : ∀ (i : ι) (a : A), ggConjAut A (hnN i) a = σ i a)
    (hΦσ : ∀ (i : ι) (a : A), Multiplicative.toAdd (Φ (σ i a)) =
      s i (Multiplicative.toAdd (Φ a)))
    (hinv : ∀ (i : ι) (a : A), s i (s i (Multiplicative.toAdd (Φ a))) =
      Multiplicative.toAdd (Φ a))
    (hfix : ∀ i, Nat.card {a : A // s i (Multiplicative.toAdd (Φ a)) =
      Multiplicative.toAdd (Φ a)} * p = Nat.card A) :
    ∀ i, GGIsReflection p (ggConjAut A (hnN i)) := by
  have hΦconj : ∀ (i : ι) (a : A), Multiplicative.toAdd (Φ (ggConjAut A (hnN i) a)) =
      s i (Multiplicative.toAdd (Φ a)) := by
    intro i a
    rw [hgg i a, hΦσ i a]
  intro i
  refine ⟨?_, ?_⟩
  · apply MulEquiv.ext
    intro a
    apply hΦ
    apply Multiplicative.ext
    simp only [pow_two, MulAut.mul_apply, MulAut.one_apply]
    rw [hΦconj i (ggConjAut A (hnN i) a), hΦconj i a, hinv i a]
  · have hiff2 : ∀ a : A, ggConjAut A (hnN i) a = a ↔
        s i (Multiplicative.toAdd (Φ a)) = Multiplicative.toAdd (Φ a) := by
      intro a
      constructor
      · intro h
        have h1 := congrArg (fun x : A => Multiplicative.toAdd (Φ x)) h
        rwa [hΦconj i a] at h1
      · intro h
        apply hΦ
        apply Multiplicative.ext
        rw [hΦconj i a, h]
    rw [Nat.card_congr (Equiv.subtypeEquivRight hiff2), hfix i]

theorem tw1f_tbGroup_twisted
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2)
    {L' : Type} [Group L'] [Finite L']
    {ψ₀ : L' →* TwE6Delta.RecipeR K 1} {A : Subgroup (MulAut L')}
    (hTB : GGTorusTBGroup 3 5 (TwE6Delta.RecipeR K 1) (TwE6Delta.RecipeI K 1) L' ψ₀ A) :
    ∃ (σ : K ≃+* K) (_ : ∀ c, σ c = c ^ 2 ^ 1) (ψ : L' →* ↥(twistedE6RootGroup K σ)),
      ψ.ker = ψ₀.ker ∧ GGTorusTBGroup 3 5 ↥(twistedE6RootGroup K σ)
        ((RecipeExcLang.twConj K σ).range : Set (MulAut ↥(twistedE6RootGroup K σ))) L' ψ A := by
  obtain ⟨hψ0, hker0, hperf0, hAe, hAI, h5, h3A, hsc⟩ := hTB
  obtain ⟨σ, hσ, ε, hε⟩ := TwE6Transport.exists_recipeConj (K := K) (n := 1) le_rfl hK
  let ψ : L' →* ↥(twistedE6RootGroup K σ) := ε.symm.toMonoidHom.comp ψ₀
  have hk : ψ.ker = ψ₀.ker :=
    MonoidHom.ker_comp_of_injective ψ₀ ε.symm.toMonoidHom ε.symm.injective
  refine ⟨σ, hσ, ψ, hk, ε.symm.surjective.comp hψ0, hk ▸ hker0, hperf0, hAe, ?_, h5, h3A, hsc⟩
  intro a ha
  obtain ⟨φ, hφI, hφ⟩ := hAI a ha
  obtain ⟨w, hw⟩ := (hε φ).2 hφI
  refine ⟨RecipeExcLang.twConj K σ w, ⟨w, rfl⟩, fun l => ?_⟩
  have h1 := hφ l
  rw [← hw, TwE6Transport.recipeConj_apply] at h1
  change RecipeExcLang.twConj K σ w (ε.symm (ψ₀ l)) = ε.symm (ψ₀ (a l))
  rw [← h1, MulEquiv.symm_apply_apply]

theorem tw1f_ker_pow_three
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2)
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ 1) {L' : Type} [Group L'] [Finite L']
    {ψ : L' →* ↥(twistedE6RootGroup K σ)} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    (hodd : Odd (Nat.card ψ.ker)) : ∀ z ∈ ψ.ker, z ^ 3 = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2 * 1)
    (by rw [Fintype.card_eq_nat_card, hK, ← pow_mul, mul_comm])
  obtain ⟨φ, hφs, hφ, -⟩ := TBE6IndTwist.exists_cover_fixed_of_odd (f := 1) le_rfl hK
    σ (fun c => hσ c) ψ hψ hker hperf hodd
  let q := CFSG.SeitzReduction.F4Pilot.twistedIsogenyC (f := 1) le_rfl hK σ.toRingHom
    (fun c => hσ c)
  have hq3 : ∀ x ∈ q.ker, x ^ 3 = 1 := by
    have hkerq := CFSG.SeitzReduction.F4Pilot.ker_twistedIsogenyC (f := 1) le_rfl hK
      σ.toRingHom (fun c => hσ c)
    have hZ : Nat.card (Subgroup.center
        (CFSG.LieType.Steinberg.TwistedE6.fixedGroup K σ.toRingHom)) ∣ 3 := by
      rw [(CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.card_center_fixedGroup
        hK (fun c => hσ c)).1]
      exact Nat.gcd_dvd_left _ _
    intro x hx
    have hx' : x ∈ Subgroup.center
        (CFSG.LieType.Steinberg.TwistedE6.fixedGroup K σ.toRingHom) := hkerq ▸ hx
    exact orderOf_dvd_iff_pow_eq_one.1
      ((Subgroup.orderOf_dvd_natCard _ hx').trans hZ)
  intro z hz
  obtain ⟨x, hx, hxz⟩ : ∃ x ∈ q.ker, φ x = z := by
    obtain ⟨x, hx⟩ := hφs z
    refine ⟨x, ?_, hx⟩
    have h1 : ψ (φ x) = 1 := by rw [hx]; exact hz
    rwa [hφ x] at h1
  rw [← hxz, ← map_pow, hq3 x hx, map_one]

theorem tw1f_frame_exists
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2)
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ 1) {L' : Type} [Group L'] [Finite L']
    {ψ₀ : L' →* ↥(twistedE6RootGroup K σ)} (hψ₀ : Function.Surjective ψ₀)
    (hker : ψ₀.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian 3 A)
    (hAH : ∀ a ∈ A, ∃ φ ∈ (RecipeExcLang.twConj K σ).range, ∀ l, φ (ψ₀ l) = ψ₀ (a l))
    (h5 : 3 ^ 5 ≤ Nat.card A) (hsc : GGTorusSelfCent 3 A) :
    Nonempty (TwE6ThreeFrame (n := 1) σ ψ₀ A) := by
  classical
  obtain ⟨ζ, Fr, hζ, hζo, hFr⟩ := exists_zeta_frobenius_twE6Three hK
  obtain ⟨g, κ, t, T, hg, hglang, hκinj, hκrange, ht, hconj, hTodd, hTfix, hHyp, hnorm⟩ :=
    TwE6ThreeRootGen.exists_frame_torus (L' := L') (ψ₀ := ψ₀) (A := A) (Fr := Fr)
      (ζ := ζ) le_rfl hK σ hσ (show 3 ∣ 2 ^ 1 + 1 by norm_num) hFr hζ hζo hψ₀ hker hperf hA
      hAH h5 hsc
  obtain ⟨E, F, -, hFv, hFg⟩ :=
    TwE6ThreeRootGen.exists_twE6Frame (K := K) (σ := σ) (n := 1) (p := 3) (Fr := Fr)
      (v := CFSG.HardMathSupport.Lang.E6Descent.twE6W0) (g₀ := g) hFr hg hglang
  have hv : ExcIsLongest TwistTag.E6.tag F.v := by
    rw [hFv]
    exact TwE6ThreeRootGen.excIsLongest_twE6W0
  exact ⟨⟨ζ, hζ, hζo, E, F, κ, t, T, hv, hκinj, hκrange, baseChange_twE6Three hζ ht hFg,
    hconj, hTodd, hTfix, hHyp, hnorm⟩⟩

theorem tw1f_frameA
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2)
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ 1) {L' : Type} [Group L'] [Finite L']
    {ψ₀ : L' →* ↥(twistedE6RootGroup K σ)} (hψ₀ : Function.Surjective ψ₀)
    (hker : ψ₀.ker ≤ Subgroup.center L') (hker3 : ∀ z ∈ ψ₀.ker, z ^ 3 = 1)
    (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (Fm : TwE6ThreeFrame (n := 1) σ ψ₀ A) :
    GGE6ThreeFrameA A Fm.κ := by
  classical
  let V : Set (Fin Tag.E6.rank → ZMod 3) := {x | Multiplicative.ofAdd x ∈ Fm.κ.range}
  have hVmem : ∀ x, Multiplicative.ofAdd x ∈ Fm.κ.range ↔ x ∈ V := fun _ => Iff.rfl
  have hV : V = Set.univ ∨ V = (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3)) :=
    coordSet_eq_univ_or_hypE6_twE6Three Fm.hκrange
  unfold GGE6ThreeFrameA
  refine ⟨Fm.hκinj, Fm.hκrange, fun γ hγ => ?_, Fm.hnorm⟩
  obtain ⟨m, hN, -, hWeyl, hcoord⟩ :=
    ggTwE6Three_weylLift (n := 1) hK hσ hψ₀ hker hperf hker3 Fm (J := ⊤) hγ (by
      intro r _
      exact ⟨Classical.choose (hψ₀ r), Subgroup.mem_top _, Classical.choose_spec (hψ₀ r)⟩)
  have hrefl : GGIsReflection 3 (ggConjAut A hN) :=
    tw1f_isReflection_of_sigma (p := 3) (k := Tag.E6.rank) Fm.hκinj
      (ι := Unit) (s := fun _ => ExcSplitRootGen.excRefl (p := 3) γ)
      (n := fun _ => m) (σ := fun _ a => ggConjAut A hN a) (hnN := fun _ => hN)
      (hgg := fun _ _ => rfl) (hΦσ := fun _ a => hcoord a)
      (hinv := fun _ a => ExcSplitRootGen.excRefl_excRefl (τ := Tag.E6) (p := 3) hγ _)
      (hfix := fun _ => card_fix_excRefl_mul_three_twE6Three (κ := Fm.κ) Fm.hκinj hVmem hV hγ) ()
  exact ⟨m, hN, hWeyl, hrefl, hcoord⟩

end CFSG.StandardType

end
