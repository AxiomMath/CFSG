module

public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRootGenFrame
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRootGenWeyl
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRootGenComp
public import CFSG.LocalAnalysis.StandardType.GGRootGenAvoidCoverTorus
public import CFSG.LocalAnalysis.StandardType.GGRootSL2CoverTorus
public import CFSG.LocalAnalysis.StandardType.GGTwE6FixedComponent
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXQuasi
public import CFSG.LocalAnalysis.StandardType.GGKGWeylReflOn
public import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourNotToral
public import CFSG.LocalAnalysis.StandardType.GGTwE6PlusRootGenGen
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelQ8Kernel
public import CFSG.LocalAnalysis.StandardType.GGTwE6RecipeTransport
public import CFSG.LocalAnalysis.StandardType.GGRootGenResQFourDefs
public import CFSG.LocalAnalysis.EvenBN.Common.CommutatorFixed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Amb
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263GCase
public import CFSG.LocalAnalysis.GLTheoremA.S12.Bridge
public import CFSG.LocalAnalysis.GLTheoremA.S12.Prop123

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

private theorem three_le_of_dvd_two_pow_add_one {n : ℕ} (hn : 2 ≤ n)
    (h3 : 3 ∣ 2 ^ n + 1) : 3 ≤ n := by
  by_contra h
  have hn2 : n = 2 := by omega
  rw [hn2] at h3
  norm_num at h3

private theorem ker_pow_three_and_odd_twE6Three
    {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 3 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) {L' : Type} [Group L'] [Finite L']
    {σ : K ≃+* K} {ψ : L' →* ↥(twistedE6RootGroup K σ)}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤)
    (ε : ↥(twistedE6RootGroup K σ) ≃* TwE6Delta.RecipeR K n) :
    ∀ z ∈ ψ.ker, z ^ 3 = 1 ∧ Odd (orderOf z) := by
  intro z hz
  let e : L' →* TwE6Delta.RecipeR K n := ε.toMonoidHom.comp ψ
  have hker_eq : e.ker = ψ.ker :=
    MonoidHom.ker_comp_of_injective ψ ε.toMonoidHom ε.injective
  have hsurj : Function.Surjective e := ε.surjective.comp hψ
  have hdvd : Nat.card e.ker ∣ 3 :=
    TwE6Delta.card_ker_dvd_three_q8 (K := K) (ψ := e) hn hK hsurj (by rwa [hker_eq]) hperf
  have hdvd' : Nat.card ψ.ker ∣ 3 := by rwa [← hker_eq]
  have hz_dvd : orderOf z ∣ 3 := (Subgroup.orderOf_dvd_natCard ψ.ker hz).trans hdvd'
  refine ⟨orderOf_dvd_iff_pow_eq_one.1 hz_dvd, ?_⟩
  rcases (Nat.dvd_prime Nat.prime_three).1 hz_dvd with h | h
  · rw [h]; exact ⟨0, rfl⟩
  · rw [h]; exact ⟨1, rfl⟩

theorem t_add_twE6Three
    {K L : Type} [Field K] [Field L] (ι : K →+* L)
    {g : ModGL TwistTag.E6.tag L} {ζ : Lˣ} (hζ : ζ ^ 3 = 1)
    {t : (Fin TwistTag.E6.tag.rank → ZMod 3) → ModGL TwistTag.E6.tag K}
    (ht : ∀ x, baseChangeGL ι (t x) =
      g * CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit
        TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ x) * g⁻¹) :
    ∀ x y, t (x + y) = t x * t y := by
  intro x y
  refine baseChangeGL_injective (f := ι) ?_
  rw [map_mul, ht, ht, ht, ExcFrames.zetaVec_add (τ := TwistTag.E6.tag), rootDiagUnit_mul]
  group

theorem card_fix_excRefl_mul_three_twE6Three
    {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    {κ : A →* Multiplicative (Fin Tag.E6.rank → ZMod 3)} (hκ : Function.Injective κ)
    {V : Set (Fin Tag.E6.rank → ZMod 3)}
    (hVmem : ∀ x, Multiplicative.ofAdd x ∈ κ.range ↔ x ∈ V)
    (hV : V = Set.univ ∨ V = (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3)))
    {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) :
    Nat.card {a : A // ExcSplitRootGen.excRefl (p := 3) γ (Multiplicative.toAdd (κ a)) =
      Multiplicative.toAdd (κ a)} * 3 = Nat.card A := by
  let e : A ≃ ↥V :=
    Equiv.ofBijective
      (fun a : A => (⟨Multiplicative.toAdd (κ a),
        (hVmem (Multiplicative.toAdd (κ a))).1
          (MonoidHom.mem_range.mpr ⟨a, by rw [ofAdd_toAdd]⟩)⟩ : ↥V))
      ⟨fun a a' h => hκ (by
          simpa only [ofAdd_toAdd] using
            congrArg Multiplicative.ofAdd (Subtype.ext_iff.mp h)),
        fun b => by
          obtain ⟨a, ha⟩ := (hVmem b.1).2 b.2
          exact ⟨a, Subtype.ext (by
            simpa only [toAdd_ofAdd] using congrArg Multiplicative.toAdd ha)⟩⟩
  have hcardA : Nat.card A = Nat.card V := Nat.card_congr e
  have hcardFix1 : Nat.card {a : A // ExcSplitRootGen.excRefl (p := 3) γ
        (Multiplicative.toAdd (κ a)) = Multiplicative.toAdd (κ a)} =
      Nat.card {x : ↥V // ExcSplitRootGen.excRefl (p := 3) γ
        (x : Fin Tag.E6.rank → ZMod 3) = (x : Fin Tag.E6.rank → ZMod 3)} :=
    Nat.card_congr (Equiv.subtypeEquiv e (fun a => Iff.rfl))
  have hcardFix2 : Nat.card {x : ↥V // ExcSplitRootGen.excRefl (p := 3) γ
        (x : Fin Tag.E6.rank → ZMod 3) = (x : Fin Tag.E6.rank → ZMod 3)} =
      Nat.card {x : Fin Tag.E6.rank → ZMod 3 // x ∈ V ∧
        ExcSplitRootGen.excRefl (p := 3) γ x = x} :=
    Nat.card_congr
      (Equiv.subtypeSubtypeEquivSubtypeInter (fun x => x ∈ V)
        (fun x => ExcSplitRootGen.excRefl (p := 3) γ x = x))
  rw [hcardFix1, hcardFix2, hcardA]
  exact TwE6ThreeRootGen.card_fix_excRefl_mul_three (V := V) hV hγ

theorem image_fix_eq_twE6Three
    {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    {κ : A →* Multiplicative (Fin Tag.E6.rank → ZMod 3)}
    {V : Set (Fin Tag.E6.rank → ZMod 3)}
    (hVmem : ∀ x, Multiplicative.ofAdd x ∈ κ.range ↔ x ∈ V)
    {K : Type} [Field K] {t : (Fin Tag.E6.rank → ZMod 3) → ModGL TwistTag.E6.tag K}
    {γ : Fin Tag.E6.rank → ℤ} :
    (fun a : A => t (Multiplicative.toAdd (κ a))) ''
      {a : A | ExcSplitRootGen.excRefl (p := 3) γ (Multiplicative.toAdd (κ a)) =
        Multiplicative.toAdd (κ a)} =
    t '' {x : Fin Tag.E6.rank → ZMod 3 | x ∈ V ∧
      ExcSplitRootGen.excRefl (p := 3) γ x = x} := by
  ext y
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨Multiplicative.toAdd (κ a), ⟨(hVmem _).1
      (MonoidHom.mem_range.mpr ⟨a, by rw [ofAdd_toAdd]⟩), ha⟩, rfl⟩
  · rintro ⟨x, ⟨hxV, hxfix⟩, rfl⟩
    obtain ⟨a, ha⟩ := (hVmem x).2 hxV
    have hx : Multiplicative.toAdd (κ a) = x :=
      (congrArg Multiplicative.toAdd ha).trans (toAdd_ofAdd x)
    refine ⟨a, ?_, ?_⟩
    · change ExcSplitRootGen.excRefl (p := 3) γ (Multiplicative.toAdd (κ a)) =
        Multiplicative.toAdd (κ a)
      exact (congrArg (ExcSplitRootGen.excRefl (p := 3) γ) hx).trans
        (hxfix.trans hx.symm)
    · change t (Multiplicative.toAdd (κ a)) = t x
      exact congrArg t hx

private theorem excRefl_neg_twE6Three
    {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) :
    ExcSplitRootGen.excRefl (p := 3) (-γ) = ExcSplitRootGen.excRefl (p := 3) γ := by
  simp only [ExcSplitRootGen.excRefl, rootReflection_neg hγ]

private theorem exists_excRefl_ne_iff_twE6Three
    {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    {κ : A →* Multiplicative (Fin Tag.E6.rank → ZMod 3)}
    {V : Set (Fin Tag.E6.rank → ZMod 3)}
    (hVmem : ∀ x, Multiplicative.ofAdd x ∈ κ.range ↔ x ∈ V)
    (hV : V = Set.univ ∨ V = (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3)))
    {γ δ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) (hδ : IsRoot Tag.E6 δ) :
    (∃ a : A, ExcSplitRootGen.excRefl (p := 3) γ (Multiplicative.toAdd (κ a)) ≠
      ExcSplitRootGen.excRefl (p := 3) δ (Multiplicative.toAdd (κ a))) ↔
    ExcSplitRootGen.excRefl (p := 3) γ ≠ ExcSplitRootGen.excRefl (p := 3) δ := by
  constructor
  · rintro ⟨a, ha⟩ h
    exact ha (congrFun h (Multiplicative.toAdd (κ a)))
  · intro hne
    by_contra h
    simp only [not_exists, not_not] at h
    apply hne
    have hVeq : ∀ x ∈ V, ExcSplitRootGen.excRefl (p := 3) γ x =
        ExcSplitRootGen.excRefl (p := 3) δ x := by
      intro x hxV
      obtain ⟨a, ha⟩ := (hVmem x).2 hxV
      have hx : Multiplicative.toAdd (κ a) = x := by
        simpa using congrArg Multiplicative.toAdd ha
      rw [← hx]
      exact h a
    rcases TwE6ThreeRootGen.eq_or_eq_neg_of_eqOn_excRefl hV hγ hδ hVeq with hδγ | hδγ
    · rw [hδγ]
    · rw [hδγ, excRefl_neg_twE6Three hγ]

theorem exists_t_pow_three_twE6Three
    {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    {κ : A →* Multiplicative (Fin Tag.E6.rank → ZMod 3)} {T : Subgroup L'}
    (hH : ∀ x ∈ NoOffRest.hypE6, ∃ y ∈ T, y ^ 3 = 1 ∧ ∃ b : A,
      MulAut.conj y = (b : MulAut L') ∧ Multiplicative.toAdd (κ b) = x)
    {γ : Fin Tag.E6.rank → ℤ} (a : A) :
    ∃ x ∈ T, x ^ 3 = 1 ∧ ∃ b : A, MulAut.conj x = (b : MulAut L') ∧
      Multiplicative.toAdd (κ b) = ExcSplitRootGen.excRefl (p := 3) γ
        (Multiplicative.toAdd (κ a)) - Multiplicative.toAdd (κ a) := by
  have hmem : ExcSplitRootGen.excRefl (p := 3) γ (Multiplicative.toAdd (κ a)) -
      Multiplicative.toAdd (κ a) ∈ NoOffRest.hypE6 := by
    simpa only [ExcSplitRootGen.excRefl] using
      TableBExc.E6Three.adAct_sub_mem_hypE6 (rootReflection γ)
        (Multiplicative.toAdd (κ a))
  exact hH _ hmem

theorem exists_zeta_frobenius_twE6Three
    {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) :
    ∃ (ζ : (AlgebraicClosure K)ˣ) (Fr : AlgebraicClosure K →+* AlgebraicClosure K),
      ζ ^ 3 = 1 ∧ orderOf ζ = 3 ∧ ∀ c, Fr c = c ^ 2 ^ n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2 * n)
    (by rw [Fintype.card_eq_nat_card, hK, ← pow_mul, mul_comm])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  haveI : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  obtain ⟨ζ, hζp⟩ := CFSG.LieType.SeitzGeneration.exists_primitiveRoot_units
    (L := AlgebraicClosure K) (ℓ := 2) Nat.prime_two Nat.prime_three (by norm_num)
  refine ⟨ζ, iterateFrobenius (AlgebraicClosure K) 2 n, hζp.pow_eq_one,
    hζp.eq_orderOf.symm, ?_⟩
  intro c
  exact iterateFrobenius_def (R := AlgebraicClosure K) (p := 2) (n := n) (x := c)

theorem coordSet_eq_univ_or_hypE6_twE6Three
    {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    {κ : A →* Multiplicative (Fin Tag.E6.rank → ZMod 3)}
    (hκrange : κ.range = ⊤ ∨
      ∀ x, Multiplicative.ofAdd x ∈ κ.range ↔ x ∈ NoOffRest.hypE6) :
    ({x : Fin Tag.E6.rank → ZMod 3 | Multiplicative.ofAdd x ∈ κ.range} = Set.univ ∨
      {x : Fin Tag.E6.rank → ZMod 3 | Multiplicative.ofAdd x ∈ κ.range} =
        (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3))) := by
  rcases hκrange with h | h
  · left
    ext x
    change Multiplicative.ofAdd x ∈ κ.range ↔ True
    rw [h]
    exact ⟨fun _ => trivial, fun _ => Subgroup.mem_top _⟩
  · right
    ext x
    exact h x

private theorem iSup_ggKGTwJ_ne_twE6Three
    (hGen : PhiTwoTwE6GenInput) {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)} (hn : 2 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (F : TwE6Frame K σ n 3 E) (hv : ExcIsLongest TwistTag.E6.tag F.v)
    {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    {κ : A →* Multiplicative (Fin Tag.E6.rank → ZMod 3)}
    {V : Set (Fin Tag.E6.rank → ZMod 3)}
    (hVmem : ∀ x, Multiplicative.ofAdd x ∈ κ.range ↔ x ∈ V)
    (hV : V = Set.univ ∨ V = (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3)))
    (j : {γ : Fin Tag.E6.rank → ℤ // IsRoot Tag.E6 γ}) :
    (⨆ (i : {γ : Fin Tag.E6.rank → ℤ // IsRoot Tag.E6 γ})
        (_ : ∃ a : A, ExcSplitRootGen.excRefl (p := 3) i.1
          (Multiplicative.toAdd (κ a)) ≠
          ExcSplitRootGen.excRefl (p := 3) j.1 (Multiplicative.toAdd (κ a))),
      ggKGTwJ F i.1) = ⊤ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hiff : ∀ i : {γ : Fin Tag.E6.rank → ℤ // IsRoot Tag.E6 γ},
      (∃ a : A, ExcSplitRootGen.excRefl (p := 3) i.1
        (Multiplicative.toAdd (κ a)) ≠
        ExcSplitRootGen.excRefl (p := 3) j.1 (Multiplicative.toAdd (κ a))) ↔
      ExcSplitRootGen.excRefl (p := 3) i.1 ≠
        ExcSplitRootGen.excRefl (p := 3) j.1 :=
    fun i => exists_excRefl_ne_iff_twE6Three (κ := κ) hVmem hV i.2 j.2
  refine (iSup_congr fun i => iSup_congr_Prop (hiff i) (fun _ => rfl)).trans ?_
  exact TwE6PlusRootGen.iSup_ggKGTwJ_ne hGen (by norm_num : (3 : ℕ) ≠ 2)
    hn hK hσ F hv j

theorem isComponentOf_image_fix_twE6Three
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)} (hn : 2 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (F : TwE6Frame K σ n 3 E)
    (hv : ExcIsLongest TwistTag.E6.tag F.v) {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ 3 = 1)
    (hζo : orderOf ζ = 3) {t : (Fin Tag.E6.rank → ZMod 3) → ModGL TwistTag.E6.tag K}
    (ht : ∀ x, baseChangeGL (algebraMap K (AlgebraicClosure K)) (t x) =
      F.g0 * CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit
        TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ x) * F.g0⁻¹)
    {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    {κ : A →* Multiplicative (Fin Tag.E6.rank → ZMod 3)}
    {V : Set (Fin Tag.E6.rank → ZMod 3)}
    (hVmem : ∀ x, Multiplicative.ofAdd x ∈ κ.range ↔ x ∈ V)
    (hV : V = Set.univ ∨ V = (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3)))
    (i : {γ : Fin Tag.E6.rank → ℤ // IsRoot Tag.E6 γ}) :
    IsComponentOf (ggKGTwJ F i.1)
      ((Subgroup.centralizer
        ((fun a : A => t (Multiplicative.toAdd (κ a))) ''
          {a : A | ExcSplitRootGen.excRefl (p := 3) i.1 (Multiplicative.toAdd (κ a)) =
            Multiplicative.toAdd (κ a)})).comap
        (twistedE6RootGroup K σ).subtype) := by
  have hq : 4 ≤ 2 ^ n :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h := TwE6ThreeRootGen.isComponentOf_ggKGTwJ_three (K := K) (σ := σ) (n := n)
    (p := 3) (E := E) hK hσ hq F hv hζ hζo (t := t) ht (V := V) hV i.2
  have hEq := image_fix_eq_twE6Three (κ := κ) hVmem (t := t) (γ := i.1)
  rw [hEq]
  exact h

theorem baseChange_twE6Three
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)} {g : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ 3 = 1)
    {t : (Fin 6 → ZMod 3) → ModGL TwistTag.E6.tag K}
    (ht : ∀ x, baseChangeGL (algebraMap K (AlgebraicClosure K)) (t x) =
      g * CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit
        TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ x) * g⁻¹)
    {F : TwE6Frame K σ n p E} (hFg : F.g0 = g) :
    ∀ x, baseChangeGL (algebraMap K (AlgebraicClosure K)) (t x) =
      F.g0 * CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit
        TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ x) * F.g0⁻¹ := by
  intro x
  rw [hFg]
  exact ht x

theorem ggTorusRootGenAvoidKG_twE6Three_of_lss92
    (hGen : PhiTwoTwE6GenInput) {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (h3 : 3 ∣ 2 ^ n + 1) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ n) (ε : ↥(twistedE6RootGroup K σ) ≃* TwE6Delta.RecipeR K n) :
    GGTorusRootGenAvoidKG 3 5 ↥(twistedE6RootGroup K σ)
      ((RecipeExcLang.twConj K σ).range : Set (MulAut ↥(twistedE6RootGroup K σ))) := by
  intro L' _ _ ψ hψ hker hperf A hA hAI h5 h3A hsc
  have hn1 : 1 ≤ n := by omega
  have hn3 : 3 ≤ n := three_le_of_dvd_two_pow_add_one hn h3
  obtain ⟨ζ, Fr, hζ, hζo, hFr⟩ := exists_zeta_frobenius_twE6Three hK
  obtain ⟨g, κ, t, T, hg, hglang, hκinj, hκrange, ht, hconj, hodd, hTA, hH, -⟩ :=
    TwE6ThreeRootGen.exists_frame_torus (L' := L') (ψ₀ := ψ) (A := A) (Fr := Fr)
      (ζ := ζ) hn1 hK σ hσ h3 hFr hζ hζo hψ hker hperf hA hAI h5 hsc
  obtain ⟨E, F, hFFr, hFv, hFg⟩ :=
    TwE6ThreeRootGen.exists_twE6Frame (K := K) (σ := σ) (n := n) (p := 3) (Fr := Fr)
      (v := CFSG.HardMathSupport.Lang.E6Descent.twE6W0) (g₀ := g) hFr hg hglang
  have hv : ExcIsLongest TwistTag.E6.tag F.v := by
    rw [hFv]
    exact TwE6ThreeRootGen.excIsLongest_twE6W0
  have htF := baseChange_twE6Three hζ ht hFg
  choose r hrJ hr using fun γ : {γ : Fin Tag.E6.rank → ℤ // IsRoot Tag.E6 γ} =>
    TwE6ThreeRootGen.exists_mem_ggKGTwJ_conj hK hσ F hv hζ htF γ.2
  let V : Set (Fin Tag.E6.rank → ZMod 3) := {x | Multiplicative.ofAdd x ∈ κ.range}
  have hVmem : ∀ x, Multiplicative.ofAdd x ∈ κ.range ↔ x ∈ V := fun _ => Iff.rfl
  have hV : V = Set.univ ∨ V = (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3)) :=
    coordSet_eq_univ_or_hypE6_twE6Three hκrange
  have hkerdata : ∀ z ∈ ψ.ker, z ^ 3 = 1 ∧ Odd (orderOf z) :=
    ker_pow_three_and_odd_twE6Three (K := K) (n := n) hn3 hK hψ hker hperf ε
  let ι := {γ : Fin Tag.E6.rank → ℤ // IsRoot Tag.E6 γ}
  haveI : Nonempty ι := ⟨⟨Pi.single 0 1, isRoot_single Tag.E6 0⟩⟩
  let s : ι → (Fin 6 → ZMod 3) → Fin 6 → ZMod 3 :=
    fun i => ExcSplitRootGen.excRefl (p := 3) i.1
  let S : ι → Subgroup ↥(twistedE6RootGroup K σ) := fun i => ggKGTwJ F i.1
  refine ggTorusRootGenAvoid_of_coverTorus (p := 3) (k := 6) (L' := L')
    (R := ↥(twistedE6RootGroup K σ)) (G := ModGL TwistTag.E6.tag K)
    (ψ := ψ) (A := A) (Φ := κ) (τ := t) (T := T) (ι := ι) (s := s) (r := r) (S := S)
    (ι₀ := (twistedE6RootGroup K σ).subtype)
    hψ hker hperf ?_ ?_ ?_ hκinj ?_ ?_ hTA ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact CFSG.LieType.Chevalley.center_graphFixedRootGroup_eq_bot (t := TwistTag.E6)
      (σ := σ.toRingHom) σ.surjective
  · intro z hz
    exact (hkerdata z hz).1
  · exact Subgroup.subtype_injective _
  · exact t_add_twE6Three (algebraMap K (AlgebraicClosure K)) hζ ht
  · intro a l
    exact hconj a l
  · intro z hz
    exact hodd z hz (hkerdata z hz).2
  · intro i x
    exact hr i x
  · intro i a
    exact ExcSplitRootGen.excRefl_excRefl i.2 (Multiplicative.toAdd (κ a))
  · intro i
    exact card_fix_excRefl_mul_three_twE6Three (κ := κ) hκinj hVmem hV i.2
  · intro i a
    exact exists_t_pow_three_twE6Three (κ := κ) hH a
  · intro i
    exact hrJ i
  · intro i
    exact isComponentOf_image_fix_twE6Three (κ := κ) hn hK hσ F hv hζ hζo htF hVmem hV i
  · intro i
    exact ggKGTwJ_dvd_card hK hσ F hv i.2 h3
  · intro j
    exact iSup_ggKGTwJ_ne_twE6Three (κ := κ) hGen hn hK hσ F hv hVmem hV j

theorem ggTwE6ThreePlusKGAvoid_of_lss92
    (hGen : PhiTwoTwE6GenInput) : GGTwE6ThreePlusKGAvoid := by
  intro K _ _ n hn hK h3
  obtain ⟨σ, hσ, ε, hε⟩ := TwE6Transport.exists_recipeConj (K := K) (n := n)
    (by omega : 1 ≤ n) hK
  refine ggTorusRootGenAvoidKG_of_mulEquiv (p := 3) (r := 5) (e := ε.symm) ?_
    (ggTorusRootGenAvoidKG_twE6Three_of_lss92 hGen hn hK h3 hσ ε)
  intro φ hφ
  obtain ⟨w, hw⟩ := (hε φ).2 hφ
  refine ⟨w, ?_⟩
  rw [← hw, TwE6Transport.recipeConj_eq]
  refine MulEquiv.ext fun x => ?_
  rw [MulAut.congr_apply, MulAut.congr_apply, MulEquiv.symm_symm]
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply]

namespace TwE6ThreeRootGen

open CFSG.Blueprint CFSG.Yardstones.Md0ec50421ce4


theorem isChevSimple_twistedE6RootGroup {K : Type} [Field K] [Finite K]
    {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ n)) :
    IsChevSimple 2 ↥(twistedE6RootGroup K σ) := by
  have hp := finite_fixed_root_group_perfect TwistTag.E6 Nat.prime_two hn K hK σ.toRingHom hσ
  have hZ : Subgroup.center ↥(twistedE6RootGroup K σ) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  obtain ⟨e⟩ := nonempty_derivedCentralQuotient_equiv hp.2.2.1 hZ
  let q : TauCeti.PrimePower := ⟨2, n, Nat.prime_two, hn⟩
  have hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid := TauCeti.LieTypeIndex.valid_twistedE6 _
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.twistedE6 q hv K
    (by rw [TauCeti.PrimePower.card_def]; exact hK)
    σ.toRingHom (fun c => by rw [TauCeti.PrimePower.card_def]; exact hσ c)
  exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isChevSimple_of_lie
    ⟨.twistedE6 q, hv⟩ (TauCeti.LieTypeIndex.characteristic_twistedE6 q) (e.symm.trans b)


theorem ggTorusRootSL2_twE6Three {K : Type} [Field K] [Finite K] {n : ℕ}
    (hn : 2 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) (h3 : 3 ∣ 2 ^ n + 1)
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (ε : ↥(twistedE6RootGroup K σ) ≃* TwE6Delta.RecipeR K n) :
    GGTorusRootSL2 3 5 ↥(twistedE6RootGroup K σ)
      ((RecipeExcLang.twConj K σ).range : Set (MulAut ↥(twistedE6RootGroup K σ))) := by
  classical
  intro L' _ _ ψ A hTB
  obtain ⟨hψ, hker, hperf, hA, hAI, h5, -, hsc⟩ := hTB
  have hn1 : 1 ≤ n := by omega
  have hn3 : 3 ≤ n := three_le_of_dvd_two_pow_add_one hn h3
  obtain ⟨ζ, Fr, hζ, hζo, hFr⟩ := exists_zeta_frobenius_twE6Three hK
  obtain ⟨g, κ, t, T, hg, hglang, hκinj, hκrange, ht, hconj, hodd, hTA, hH, hinner⟩ :=
    exists_frame_torus (L' := L') (ψ₀ := ψ) (A := A) (Fr := Fr) (ζ := ζ)
      hn1 hK σ hσ h3 hFr hζ hζo hψ hker hperf hA hAI h5 hsc
  obtain ⟨E, F, -, hFv, hFg⟩ :=
    exists_twE6Frame (K := K) (σ := σ) (n := n) (p := 3) (Fr := Fr)
      (v := CFSG.HardMathSupport.Lang.E6Descent.twE6W0) (g₀ := g) hFr hg hglang
  have hv : ExcIsLongest TwistTag.E6.tag F.v := by
    rw [hFv]
    exact excIsLongest_twE6W0
  have htF := baseChange_twE6Three hζ ht hFg
  choose r hrJ hr using fun γ : {γ : Fin Tag.E6.rank → ℤ // IsRoot Tag.E6 γ} =>
    exists_mem_ggKGTwJ_conj hK hσ F hv hζ htF γ.2
  let V : Set (Fin Tag.E6.rank → ZMod 3) := {x | Multiplicative.ofAdd x ∈ κ.range}
  have hVmem : ∀ x, Multiplicative.ofAdd x ∈ κ.range ↔ x ∈ V := fun _ => Iff.rfl
  have hV : V = Set.univ ∨ V = (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3)) :=
    coordSet_eq_univ_or_hypE6_twE6Three hκrange
  have hkerdata : ∀ z ∈ ψ.ker, z ^ 3 = 1 ∧ Odd (orderOf z) :=
    ker_pow_three_and_odd_twE6Three (K := K) (n := n) hn3 hK hψ hker hperf ε
  let ι := {γ : Fin Tag.E6.rank → ℤ // IsRoot Tag.E6 γ}
  let s : ι → (Fin 6 → ZMod 3) → Fin 6 → ZMod 3 :=
    fun i => ExcSplitRootGen.excRefl (p := 3) i.1
  let S : ι → Subgroup ↥(twistedE6RootGroup K σ) := fun i => ggKGTwJ F i.1
  have : Finite ↥(twistedE6RootGroup K σ) := Finite.of_surjective ψ hψ
  have hC := finite_fixed_root_group_perfect TwistTag.E6 Nat.prime_two hn1 K hK σ.toRingHom hσ
  have hR := isSimpleGroup_graphFixedRootGroup_of_perfect TwistTag.E6 K σ hC.1
  refine ggTorusRootSL2At_of_coverTorus_chev (p := 3) (k := 6) (L' := L')
    (R := ↥(twistedE6RootGroup K σ)) (G := ModGL TwistTag.E6.tag K)
    (ψ := ψ) (A := A) (Φ := κ) (τ := t) (T := T) (ι := ι) (s := s) (r := r) (S := S)
    (ι₀ := (twistedE6RootGroup K σ).subtype)
    hψ hker ?_ ?_ ?_ hκinj ?_ hconj hTA ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    hR.1 hR.2 (isChevSimple_twistedE6RootGroup hn1 hK σ hσ)
    Nat.prime_three (by norm_num) (fun a ha => hA.2 a ha) ?_ ?_
  · exact center_graphFixedRootGroup_eq_bot σ.surjective
  · intro z hz
    exact (hkerdata z hz).1
  · exact Subgroup.subtype_injective _
  · exact t_add_twE6Three (algebraMap K (AlgebraicClosure K)) hζ ht
  · intro z hz
    exact hodd z hz (hkerdata z hz).2
  · intro i x
    exact hr i x
  · intro i a
    exact ExcSplitRootGen.excRefl_excRefl i.2 (Multiplicative.toAdd (κ a))
  · intro i
    exact card_fix_excRefl_mul_three_twE6Three hκinj hVmem hV i.2
  · intro i a
    exact exists_t_pow_three_twE6Three hH a
  · intro i
    exact hrJ i
  · intro i
    exact isComponentOf_image_fix_twE6Three (κ := κ) hn hK hσ F hv hζ hζo htF hVmem hV i
  · intro i
    exact ggKGTwJ_dvd_card hK hσ F hv i.2 h3
  · intro a ha
    obtain ⟨α, -, hα⟩ := hAI a ha
    exact ⟨α, hα⟩
  · intro φ hφ hrefl
    exact E6ThreeRootGen.exists_root_of_isReflection_frame hκinj hVmem hV hinner hφ hrefl

theorem ggTorusRootSL2_recipeR_twE6Three {K : Type} [Field K] [Finite K] {n : ℕ}
    (hn : 2 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) (h3 : 3 ∣ 2 ^ n + 1) :
    GGTorusRootSL2 3 5 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) := by
  obtain ⟨σ, hσ, ε, hε⟩ := TwE6Transport.exists_recipeConj (K := K) (n := n) (by omega) hK
  refine ggTorusRootSL2_of_mulEquiv ε.symm ?_ (ggTorusRootSL2_twE6Three hn hK h3 hσ ε)
  intro α hα
  obtain ⟨w, hw⟩ := (hε α).2 hα
  refine ⟨w, ?_⟩
  apply MulEquiv.ext
  intro x
  rw [← hw]
  change (RecipeExcLang.twConj K σ w) x =
    ε.symm (TwE6Transport.recipeConj σ ε w (ε x))
  rw [TwE6Transport.recipeConj_apply, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]

theorem rootSL2_of_toral_rgrpModel
    {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    (ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* TwE6Delta.RecipeR K n)
    (hε : ∀ x : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      MulAut.congr ε x ∈ TwE6Delta.RecipeI K n ↔ x ∈ (RecipeExcLang.twConj K σ).range)
    (h3 : 3 ∣ 2 ^ n + 1) {L' : Type} [Group L'] [Finite L']
    (ψ : L' →* TwE6Delta.RecipeR K n) (A : Subgroup (MulAut L'))
    (hTB : GGTorusTBGroup 3 4 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) L' ψ A)
    (htor : SCFourCover.E6AdToral (SCFourCover.rgrpModel (by omega : 1 ≤ n)
      hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A))) :
    ∀ φ ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A, GGIsReflection 3 φ →
      ∃ (x : L') (hx : MulAut.conj x ∈ Subgroup.normalizer (A : Set (MulAut L')))
        (J : Subgroup L'), GGTorusWeylElt 3 A x ∧ ggConjAut A hx = φ ∧ x ∈ J ∧
        IsComponentOf J (ggHypCent A x) ∧ 3 ∣ Nat.card J ∧
        ∀ (a : MulAut L') (ha : a ∈ A), φ ⟨a, ha⟩ = ⟨a, ha⟩ → x ∈ LargeEvenLayer (ggFix a) := by
  obtain ⟨hψ, hker, hperf, hA, hAI, h4, h3A, hsc⟩ := hTB
  have h5 := SCFourCover.three_pow_five_le_card_of_e6AdToral_rgrpModel
    (by omega : 1 ≤ n) hK σ hσ Fr hFr ε hε h3 hψ hker hperf hA h4 hAI hsc htor
  exact ggTorusRootSL2_recipeR_twE6Three hn hK h3 L' ψ A
    ⟨hψ, hker, hperf, hA, hAI, h5, h3A, hsc⟩

section RationalComponent

open SCFourCover NoOffTwE6Three CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Lang.E6Descent CFSG.LieType.AlgebraicGroups
  CFSG.ComponentClassification.CatalogueBPrimeJoin CFSG.RankThree.Classical2

variable {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
  (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) {Ω : Type} [Field Ω] [Algebra K Ω]
  [IsAlgClosure K Ω] (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
  (ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* TwE6Delta.RecipeR K n)
  (hε : ∀ x : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
    MulAut.congr ε x ∈ TwE6Delta.RecipeI K n ↔ x ∈ (RecipeExcLang.twConj K σ).range)

variable {L' : Type} [Group L'] {ψ : L' →* TwE6Delta.RecipeR K n}
  (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
  {A : Subgroup (MulAut L')}
  (hAI : ∀ a ∈ A, ∃ φ ∈ TwE6Delta.RecipeI K n, ∀ l, φ (ψ l) = ψ (a l))


theorem rootSL2_of_quasisimple_jgeom
    [Finite L'] (hn3 : 3 ≤ n) (hA : IsElemAbelian 3 A) {g : L'}
    (hg : MulAut.conj g ∈ Subgroup.normalizer (A : Set (MulAut L')))
    (hφ : GGIsReflection 3 (ggConjAut A hg)) {m : ℕ} (hg2 : g ^ (2 ^ m) = 1) :
    let Hh := ((ggConjAut A hg).toMonoidHom.eqLocus (MonoidHom.id A)).map
      ((rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A)).subtype.comp
        (recipeActorModelEquiv hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI).toMonoidHom)
    let Kc := closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω)))
    let KF := Kc ⊓ TwistedDiag.Rgrp Ω Fr
    let P := (primeResidual 2 ↥KF).map KF.subtype
    CFSG.IsQuasisimple P →
      ∃ J : Subgroup L', g ∈ J ∧ IsComponentOf J (ggHypCent A g) ∧ 3 ∣ Nat.card J ∧
        GGTorusWeylElt 3 A g ∧
        ∀ (a : MulAut L') (ha : a ∈ A), ggConjAut A hg ⟨a, ha⟩ = ⟨a, ha⟩ →
          g ∈ LargeEvenLayer (ggFix a) := by
  classical
  dsimp only
  let Hh := ((ggConjAut A hg).toMonoidHom.eqLocus (MonoidHom.id A)).map
    ((rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A)).subtype.comp
      (recipeActorModelEquiv hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI).toMonoidHom)
  let Kc := closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
    Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω)))
  let KF := Kc ⊓ TwistedDiag.Rgrp Ω Fr
  let P := (primeResidual 2 ↥KF).map KF.subtype
  let ι : TwE6Delta.RecipeR K n →* ModGL Tag.E6 Ω :=
    (baseChangeGL (τ := Tag.E6) (algebraMap K Ω)).comp
      ((graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subtype.comp ε.symm.toMonoidHom)
  change CFSG.IsQuasisimple P → _
  intro hq
  have : Finite (TwE6Delta.RecipeR K n) := Finite.of_surjective ψ hψ
  have hgP := TwE6FixedComponent.jgeom_data_of_two_element hn hK σ hσ Fr hFr ε hε
    hψ hker hperf hAI hA hg hg2
  obtain ⟨hcomp, -⟩ := TwE6FixedComponent.isComponentOf_induced_recipe_jgeom
    hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI hg hq
  have hodd : ∀ z ∈ ψ.ker, Odd (orderOf z) := by
    have hdiv := TwE6Delta.card_ker_dvd_three_q8 hn3 hK hψ hker hperf
    intro z hz
    exact (show Odd 3 by decide).of_dvd_nat ((Subgroup.orderOf_dvd_natCard ψ.ker hz).trans hdiv)
  obtain ⟨hR, hnc⟩ := TwE6Dvd.isSimpleGroup_recipeR hn hK
  have hchev : CFSG.Yardstones.Md0ec50421ce4.IsChevSimple 2 (TwE6Delta.RecipeR K n) :=
    CFSG.LocalAnalysis.GLTheoremA.T263.DX.isChevSimple_of_equiv ε
      (TwE6ThreeRootGen.isChevSimple_twistedE6RootGroup hn hK σ hσ)
  exact rootSL2_of_two_pow_of_induced_component hψ hker hperf
    (TwE6Delta.center_recipeR_eq_bot hn hK) hodd hR hnc hchev Nat.prime_three (by decide) hA
    (fun a ha => by obtain ⟨α, -, hα⟩ := hAI a ha; exact ⟨α, hα⟩)
    hg hφ hg2 hcomp hgP


theorem ggTorusRootSL2_recipeR_twE6Three_of_jgeom
    (hn2 : 2 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    (ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* TwE6Delta.RecipeR K n)
    (hε : ∀ x : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      MulAut.congr ε x ∈ TwE6Delta.RecipeI K n ↔ x ∈ (RecipeExcLang.twConj K σ).range)
    (h3 : 3 ∣ 2 ^ n + 1)
    (hq : ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* TwE6Delta.RecipeR K n)
      (A : Subgroup (MulAut L'))
      (hTB : GGTorusTBGroup 3 4 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) L' ψ A),
      ¬ E6AdToral (rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A)) →
      ∀ (g : L') (hg : MulAut.conj g ∈ Subgroup.normalizer (A : Set (MulAut L'))),
        GGIsReflection 3 (ggConjAut A hg) → (∃ m, g ^ (2 ^ m) = 1) →
        let Hh := ((ggConjAut A hg).toMonoidHom.eqLocus (MonoidHom.id A)).map
          ((rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A)).subtype.comp
            (recipeActorModelEquiv hn hK σ hσ Fr hFr ε hε
              hTB.1 hTB.2.1 hTB.2.2.1 hTB.2.2.2.2.1).toMonoidHom)
        let KF := closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
          Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) ⊓ TwistedDiag.Rgrp Ω Fr
        CFSG.IsQuasisimple ((primeResidual 2 ↥KF).map KF.subtype)) :
    GGTorusRootSL2 3 4 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) := by
  intro L' _ _ ψ A hTB φ hφ hφr
  by_cases htor : E6AdToral (rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A))
  · exact TwE6ThreeRootGen.rootSL2_of_toral_rgrpModel hn2 hK σ hσ Fr hFr ε hε h3 ψ A hTB
      htor φ hφ hφr
  · obtain ⟨β, ⟨x, rfl⟩, hx, hβ⟩ := mem_ggAutomizer_iff.mp hφ
    have hxφ : ggConjAut A hx = φ := by
      apply MulEquiv.ext
      intro a
      exact Subtype.ext (hβ a).symm
    obtain ⟨g, hg, m, hg2, hgφ⟩ := exists_two_pow_ggConjAut hx (hxφ.symm ▸ hφr.1)
    have hgφ' : ggConjAut A hg = φ := hgφ.trans hxφ
    have hrefl : GGIsReflection 3 (ggConjAut A hg) := hgφ'.symm ▸ hφr
    have hn3 : 3 ≤ n := by
      by_contra h
      have hn2 : n = 2 := by omega
      rw [hn2] at h3
      norm_num at h3
    obtain ⟨J, hgJ, hJ, hJ3, hW, hlay⟩ := TwE6ThreeRootGen.rootSL2_of_quasisimple_jgeom
      (by omega : 1 ≤ n) hK σ hσ Fr hFr ε hε hTB.1 hTB.2.1 hTB.2.2.1 hTB.2.2.2.2.1
      hn3 hTB.2.2.2.1 hg hrefl hg2 (hq L' ψ A hTB htor g hg hrefl ⟨m, hg2⟩)
    exact ⟨g, hg, J, hW, hgφ', hgJ, hJ, hJ3, fun a ha hfix =>
      hlay a ha (by rw [hgφ']; exact hfix)⟩


end RationalComponent

end TwE6ThreeRootGen

end CFSG.StandardType

end
