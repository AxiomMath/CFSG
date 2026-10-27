module

public import CFSG.LocalAnalysis.StandardType.GGTBJXClass
public import CFSG.LocalAnalysis.StandardType.GGRealKGThreeE6Split
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeRootGenFrame
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeRootGenKG
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeRootGenComp
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelRecipeID
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelE6Kernel
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRootGenCoord
public import CFSG.LocalAnalysis.StandardType.GGTwE6FixedA2Type
public import CFSG.LocalAnalysis.StandardType.GGTBJE6ThreeCoord
public import CFSG.LocalAnalysis.StandardType.GGRootGenAvoidCoverTorus
public import CFSG.LocalAnalysis.StandardType.GGExcSplitRootGenModel
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE8FiveFrameCentralizer
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticBstar

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc
  TableBExc.E6Three CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.LieType.AlgebraicGroups

theorem ggTBJ_exists_weyl_mem_of_rootSL2 {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hSL2 : GGTorusRootSL2 p r R I) {L' : Type} [Group L'] [Finite L'] {ψ : L' →* R}
    {A : Subgroup (MulAut L')} (hTB : GGTorusTBGroup p r R I L' ψ A) {n₀ : L'}
    (hn₀ : MulAut.conj n₀ ∈ Subgroup.normalizer (A : Set (MulAut L')))
    (hr : GGIsReflection p (ggConjAut A hn₀)) {y : MulAut L'} (hy : y ∈ A)
    (hfix : ggConjAut A hn₀ ⟨y, hy⟩ = ⟨y, hy⟩) {J : Subgroup L'}
    (hJl : ∀ Q : Subgroup L', CFSG.Open.IsComponentOf Q (fixSubgroup y) → Q ≤ J) :
    ∃ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      ggConjAut A hn = ggConjAut A hn₀ ∧ GGTorusWeylElt p A n ∧ n ∈ J := by
  have hmem : MulAut.conj n₀ ∈ (MulAut.conj : L' →* MulAut L').range := ⟨n₀, rfl⟩
  have hφ : ggConjAut A hn₀ ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A :=
    ggConjAut_mem_ggAutomizer (H := (MulAut.conj : L' →* MulAut L').range) (Bs := A)
      (g := MulAut.conj n₀) hmem hn₀
  obtain ⟨n, hn, -, hweyl, hconj, -, -, -, hlayer⟩ :=
    hSL2 L' ψ A hTB (ggConjAut A hn₀) hφ hr
  refine ⟨n, hn, hconj, hweyl, ?_⟩
  have hfixEq : ggFix y = fixSubgroup y := Subgroup.ext fun _ => Iff.rfl
  have hE : LargeEvenLayer (ggFix y) ≤ J :=
    sSup_le fun Q hQ => hJl Q (hfixEq ▸ CFSG.Assembly.isComponentOf_iff_open.mp hQ)
  exact hE (hlayer y hy hfix)

section E6Three


theorem ggTBJ_e6Three_exists_refl_lift {K : Type} [Field K] [Finite K] [CharP K 2] {ζ : Kˣ}
    (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3) {L' : Type} [Group L'] [Finite L']
    {ψ₀ : L' →* ↥(adjointGroup Tag.E6 K)} (hψ₀ : Function.Surjective ψ₀)
    (hker : ψ₀.ker ≤ Subgroup.center L') (hkerp : ∀ z ∈ ψ₀.ker, z ^ 3 = 1)
    {A : Subgroup (MulAut L')} {g : ModGL Tag.E6 K} {κ : A →* Multiplicative (Fin 6 → ZMod 3)}
    {T : Subgroup L'} (hg : g ∈ adjointGroup Tag.E6 K) (hκinj : Function.Injective κ)
    (hκrange : κ.range = ⊤ ∨ ∀ x, Multiplicative.ofAdd x ∈ κ.range ↔ x ∈ NoOffRest.hypE6)
    (hreal : ∀ (a : A) (l : L'),
      ((ψ₀ ((a : MulAut L') l) : ↥(adjointGroup Tag.E6 K)) : ModGL Tag.E6 K) =
        (g * rootDiagUnit Tag.E6 (zetaVec ζ hζ (Multiplicative.toAdd (κ a))) * g⁻¹) *
          ((ψ₀ l : ↥(adjointGroup Tag.E6 K)) : ModGL Tag.E6 K) *
          (g * rootDiagUnit Tag.E6 (zetaVec ζ hζ (Multiplicative.toAdd (κ a))) * g⁻¹)⁻¹)
    (hkerT : ψ₀.ker ≤ T) (hTA : ∀ a ∈ A, ∀ y ∈ T, a y = y)
    (hH : ∀ x ∈ NoOffRest.hypE6, ∃ y ∈ T, y ^ 3 = 1 ∧ ∃ b : A,
      MulAut.conj y = (b : MulAut L') ∧ Multiplicative.toAdd (κ b) = x)
    {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) :
    ∃ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      GGTorusWeylElt 3 A n ∧ GGIsReflection 3 (ggConjAut A hn) ∧
      ∀ a : A, Multiplicative.toAdd (κ (ggConjAut A hn a)) =
        ExcSplitRootGen.excRefl (p := 3) γ (Multiplicative.toAdd (κ a)) := by
  classical
  have hZ : Subgroup.center ↥(adjointGroup Tag.E6 K) = ⊥ :=
    center_adjointGroup_eq_bot (τ := Tag.E6) (K := K)
  let V : Set (Fin Tag.E6.rank → ZMod 3) := {x | Multiplicative.ofAdd x ∈ κ.range}
  have hVmem : ∀ x, Multiplicative.ofAdd x ∈ κ.range ↔ x ∈ V := fun _ => Iff.rfl
  have hV : V = Set.univ ∨ V = (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3)) :=
    TwE6ThreeRootGen.coordSet_eq_univ_or_hypE6 hκrange
  let ι := {γ : Fin Tag.E6.rank → ℤ // IsRoot Tag.E6 γ}
  let s : ι → (Fin Tag.E6.rank → ZMod 3) → Fin Tag.E6.rank → ZMod 3 :=
    fun i => ExcSplitRootGen.excRefl (p := 3) i.1
  let τ : (Fin Tag.E6.rank → ZMod 3) → ModGL Tag.E6 K :=
    fun x => g * rootDiagUnit Tag.E6 (TableBExc.E6Three.zetaVec ζ hζ x) * g⁻¹
  let r : ι → adjointGroup Tag.E6 K :=
    fun i => ⟨g, hg⟩ * ExcSplitRootGen.excWeyl (K := K) i * ⟨g, hg⟩⁻¹
  let S : ι → Subgroup (adjointGroup Tag.E6 K) :=
    fun i => (ExcSplitRootGen.excComp (K := K) i.1).map
      (MulAut.conj (⟨g, hg⟩ : adjointGroup Tag.E6 K)).toMonoidHom
  have hτ : ∀ x y : Fin Tag.E6.rank → ZMod 3, τ (x + y) = τ x * τ y := by
    intro x y
    change g * rootDiagUnit Tag.E6 (TableBExc.E6Three.zetaVec (τ := Tag.E6) ζ hζ (x + y)) *
        g⁻¹ =
      (g * rootDiagUnit Tag.E6 (TableBExc.E6Three.zetaVec (τ := Tag.E6) ζ hζ x) * g⁻¹) *
        (g * rootDiagUnit Tag.E6 (TableBExc.E6Three.zetaVec (τ := Tag.E6) ζ hζ y) * g⁻¹)
    rw [ExcFrames.zetaVec_add (τ := Tag.E6) ζ hζ (x := x) (y := y), rootDiagUnit_mul]
    group
  have hr : ∀ (i : ι) (x : Fin Tag.E6.rank → ZMod 3),
      (adjointGroup Tag.E6 K).subtype (r i) * τ x *
        ((adjointGroup Tag.E6 K).subtype (r i))⁻¹ = τ (s i x) := by
    intro i x
    change (g * (ExcSplitRootGen.excWeyl (K := K) i : ModGL Tag.E6 K) * g⁻¹) *
        (g * rootDiagUnit Tag.E6 (TableBExc.E6Three.zetaVec ζ hζ x) * g⁻¹) *
        (g * (ExcSplitRootGen.excWeyl (K := K) i : ModGL Tag.E6 K) * g⁻¹)⁻¹ =
      g * rootDiagUnit Tag.E6 (TableBExc.E6Three.zetaVec ζ hζ
        (ExcSplitRootGen.excRefl (p := 3) i.1 x)) * g⁻¹
    calc (g * (ExcSplitRootGen.excWeyl (K := K) i : ModGL Tag.E6 K) * g⁻¹) *
          (g * rootDiagUnit Tag.E6 (TableBExc.E6Three.zetaVec ζ hζ x) * g⁻¹) *
          (g * (ExcSplitRootGen.excWeyl (K := K) i : ModGL Tag.E6 K) * g⁻¹)⁻¹
        = g * ((ExcSplitRootGen.excWeyl (K := K) i : ModGL Tag.E6 K) *
            rootDiagUnit Tag.E6 (TableBExc.E6Three.zetaVec ζ hζ x) *
            (ExcSplitRootGen.excWeyl (K := K) i : ModGL Tag.E6 K)⁻¹) * g⁻¹ := by group
      _ = g * rootDiagUnit Tag.E6 (TableBExc.E6Three.zetaVec ζ hζ
            (ExcSplitRootGen.excRefl (p := 3) i.1 x)) * g⁻¹ := by
          rw [E6ThreeRootGen.excWeyl_conj_rootDiagUnit (τ := Tag.E6) (K := K) (p := 3) hζ i x]
  obtain ⟨J, n, hnN, -, -, -, -, hW, hR, hΦ, -, -⟩ :=
    exists_lift_of_coverTorus (p := 3) (k := Tag.E6.rank) (L' := L')
      (R := ↥(adjointGroup Tag.E6 K)) (G := ModGL Tag.E6 K)
      (ψ := ψ₀) (A := A) (Φ := κ) (τ := τ) (T := T) (ι := ι) (s := s) (r := r) (S := S)
      (ι₀ := (adjointGroup Tag.E6 K).subtype)
      hψ₀ hker hZ hkerp (Subgroup.subtype_injective _) hκinj hτ hreal hTA hkerT hr
      (fun i a => ExcSplitRootGen.excRefl_excRefl (τ := Tag.E6) (p := 3) i.2 _)
      (fun i => TwE6ThreeRootGen.card_fix_excRefl_toAdd_mul_three (κ := κ) hκinj hVmem hV i.2)
      (fun i a => hH _ (TwE6ThreeRootGen.excRefl_sub_mem_hypE6 i.1
        (Multiplicative.toAdd (κ a))))
      (fun i => Subgroup.mem_map.mpr ⟨ExcSplitRootGen.excWeyl (K := K) i,
        ExcSplitRootGen.excWeyl_mem_excComp i, rfl⟩)
      (fun i => E6ThreeRootGen.isComponentOf_excComp_map_conj_e6 (g := g) hg hζo hζ hVmem hV i)
      (fun i => E6ThreeRootGen.dvd_card_excComp_map_conj_e6 (g := g) hg hζo i)
  exact ⟨n ⟨γ, hγ⟩, hnN ⟨γ, hγ⟩, hW _, hR _, hΦ ⟨γ, hγ⟩⟩

theorem ggTBJ_e6Three_torusNoncomm {K : Type} [Field K] [Finite K] [CharP K 2]
    (h3 : 3 ∣ Nat.card K - 1) {L' : Type} [Group L'] [Finite L']
    {ψ₀ : L' →* ↥(adjointGroup Tag.E6 K)} {A : Subgroup (MulAut L')}
    (hTB : GGTorusTBGroup 3 5 ↥(adjointGroup Tag.E6 K)
      ((hatAut Tag.E6 K).range : Set (MulAut ↥(adjointGroup Tag.E6 K))) L' ψ₀ A)
    {y : MulAut L'} (hy : y ∈ A) {J : Subgroup L'}
    (hJ : CFSG.Open.IsComponentOf J (fixSubgroup y))
    (hJl : ∀ Q : Subgroup L', CFSG.Open.IsComponentOf Q (fixSubgroup y) → Q ≤ J)
    (hcount : 3 ^ 2 * Nat.card ↥(A ⊓ ⨅ j : J, MulAction.stabilizer (MulAut L') (j : L')) ≤
      Nat.card ↥A) :
    ∃ (n₁ n₂ : L') (h₁ : MulAut.conj n₁ ∈ Subgroup.normalizer (A : Set (MulAut L')))
      (h₂ : MulAut.conj n₂ ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      n₁ ∈ J ∧ n₂ ∈ J ∧ GGTorusWeylElt 3 A n₁ ∧ GGTorusWeylElt 3 A n₂ ∧
        GGIsReflection 3 (ggConjAut A h₁) ∧ GGIsReflection 3 (ggConjAut A h₂) ∧
        ggConjAut A h₁ * ggConjAut A h₂ ≠ ggConjAut A h₂ * ggConjAut A h₁ := by
  classical
  obtain ⟨hψ, hker, hperf, hA, hAI, h5, -, hsc⟩ := id hTB
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ζ, hζo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := K) (p := 3) h3
  have hζ : ζ ^ 3 = 1 := hζo ▸ pow_orderOf_eq_one ζ
  have h6 : Tag.E6.rank = 6 := rfl
  have hcast : ∀ j : Fin Tag.E6.rank, Fin.cast h6 j = j := fun j => Fin.ext rfl
  have hK : 4 ≤ Nat.card K := by
    have h1 : orderOf ζ ≤ Nat.card Kˣ := orderOf_le_card
    rw [hζo, Nat.card_units] at h1
    omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hKcard⟩ := FiniteField.card K 2
  have hn : 1 ≤ (n : ℕ) := n.pos
  have hK2 : Nat.card K = 2 ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card, hKcard]
  let e := TableBExc.recipeEquiv .E6 K
  let ψr : L' →* TableBExc.RecipeGroup .E6 K := e.symm.toMonoidHom.comp ψ₀
  have hψr : Function.Surjective ψr := e.symm.surjective.comp hψ
  have hkereq : ψr.ker = ψ₀.ker :=
    MonoidHom.ker_comp_of_injective ψ₀ e.symm.toMonoidHom e.symm.injective
  have hcard : Nat.card ψ₀.ker ∣ 3 := by
    rw [← hkereq]
    exact TableBExc.E6Three.card_ker_dvd_three_e6 (n := (n : ℕ)) hn hK2 hψr
      (by rw [hkereq]; exact hker) hperf
  have hkerp : ∀ z ∈ ψ₀.ker, z ^ 3 = 1 := by
    intro z hz
    have hz3 : orderOf z ∣ 3 := (Subgroup.orderOf_dvd_natCard ψ₀.ker hz).trans hcard
    exact orderOf_dvd_iff_pow_eq_one.1 hz3
  have hodd : ∀ z ∈ ψ₀.ker, Odd (orderOf z) := by
    intro z hz
    have hz3 : orderOf z ∣ 3 := (Subgroup.orderOf_dvd_natCard ψ₀.ker hz).trans hcard
    rcases (Nat.dvd_prime Nat.prime_three).1 hz3 with h | h
    · rw [h]; exact ⟨0, rfl⟩
    · rw [h]; exact ⟨1, rfl⟩
  obtain ⟨g, κ, T, hg, hκinj, hκrange, hreal, hkerT, hTA, hH, -⟩ :=
    E6ThreeRootGen.exists_frame_torus_E (ζ := ζ) hζ hζo hψ hker hperf hcard hA hAI h5 hsc
  let V : Set (Fin Tag.E6.rank → ZMod 3) := {x | Multiplicative.ofAdd x ∈ κ.range}
  have hV : V = Set.univ ∨ V = (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3)) :=
    TwE6ThreeRootGen.coordSet_eq_univ_or_hypE6 hκrange
  have hlift : ∀ γ : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 γ →
      ∃ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
        GGTorusWeylElt 3 A n ∧ GGIsReflection 3 (ggConjAut A hn) ∧
        ∀ a : A, Multiplicative.toAdd (κ (ggConjAut A hn a)) =
          ExcSplitRootGen.excRefl (p := 3) γ (Multiplicative.toAdd (κ a)) :=
    fun γ hγ => ggTBJ_e6Three_exists_refl_lift hζ hζo hψ hker hkerp hg hκinj hκrange hreal
      (fun z hz => hkerT z hz (hodd z hz)) hTA hH hγ
  let ay : Fin Tag.E6.rank → Kˣ := zetaVec ζ hζ (Multiplicative.toAdd (κ ⟨y, hy⟩))
  let ψ₁ : L' →* ModGL Tag.E6 K :=
    (MulAut.conj g⁻¹).toMonoidHom.comp ((adjointGroup Tag.E6 K).subtype.comp ψ₀)
  have hker₁ : ψ₁.ker ≤ Subgroup.center L' := by
    rw [show ψ₁ = (MulAut.conj g⁻¹).toMonoidHom.comp
        ((adjointGroup Tag.E6 K).subtype.comp ψ₀) from rfl,
      MonoidHom.ker_comp_of_injective _ _ (MulAut.conj g⁻¹).injective,
      MonoidHom.ker_comp_of_injective _ _ (Subgroup.subtype_injective _)]
    exact hker
  have hsub₁ : ((adjointGroup Tag.E6 K).subtype.comp ψ₀).range =
      adjointGroup Tag.E6 K := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hψ, Subgroup.map_top,
      Subgroup.range_subtype]
  have hrange₁ : ψ₁.range = adjointGroup Tag.E6 K := by
    rw [show ψ₁ = (MulAut.conj g⁻¹).toMonoidHom.comp
        ((adjointGroup Tag.E6 K).subtype.comp ψ₀) from rfl,
      MonoidHom.range_comp, hsub₁]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.le_normalizer (Subgroup.inv_mem _ hg))
  have hay : ∀ i, ay i ^ 3 = 1 := by
    intro i
    change (zetaVec (τ := Tag.E6) ζ hζ (Multiplicative.toAdd (κ ⟨y, hy⟩)) i) ^ 3 = 1
    rw [zetaVec_apply, ← pow_mul, pow_mul', hζ, one_pow]
  have hconj : ∀ (a : A) (l : L'),
      ψ₁ ((a : MulAut L') l) =
        rootDiagUnit Tag.E6 (zetaVec ζ hζ (Multiplicative.toAdd (κ a))) * ψ₁ l *
          (rootDiagUnit Tag.E6 (zetaVec ζ hζ (Multiplicative.toAdd (κ a))))⁻¹ := by
    intro a l
    have h₁ : ψ₁ ((a : MulAut L') l) =
        g⁻¹ * ((ψ₀ ((a : MulAut L') l) : ↥(adjointGroup Tag.E6 K)) : ModGL Tag.E6 K) * g := by
      dsimp only [ψ₁, MonoidHom.comp_apply]
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rfl
    have h₂ : ψ₁ l =
        g⁻¹ * ((ψ₀ l : ↥(adjointGroup Tag.E6 K)) : ModGL Tag.E6 K) * g := by
      dsimp only [ψ₁, MonoidHom.comp_apply]
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rfl
    rw [h₁, h₂, hreal a l]
    group
  obtain ⟨i, hi⟩ := ggTBJ_class_fix (p := 3) Nat.prime_three hK (ψ := ψ₁) hker₁ hrange₁
    ay hay y (hconj ⟨y, hy⟩) hJ
  have hfixJ : ∀ a : A, (∀ γ ∈ componentRoots (rootCharHom ay) i,
      ∑ j, (γ j : ZMod 3) * Multiplicative.toAdd (κ a) j = 0) →
      ∀ j ∈ J, (a : MulAut L') j = j := fun a hκa =>
    ggTBJ_fix_of_kernel (ψ := ψ₁) hker₁ i hi
      (Subgroup.isPerfect_iff.1 ⟨hJ.2.2.1⟩)
      (zetaVec (τ := Tag.E6) ζ hζ (Multiplicative.toAdd (κ a)))
      (fun γ hγ => (TwE6FixedA2Type.rootChar_zetaVec_eq_one_iff_dotZ3 hζo hζ
        (Multiplicative.toAdd (κ a)) γ).2 (by exact hκa γ hγ))
      (a : MulAut L') (hconj a)
  have hcardV : 3 ^ 2 * Nat.card {x // x ∈ V ∧ ∀ γ ∈ componentRoots (rootCharHom ay) i,
      ∑ j, (γ j : ZMod 3) * x j = 0} ≤ Nat.card V := by
    let S := {x // x ∈ V ∧ ∀ γ ∈ componentRoots (rootCharHom ay) i,
      ∑ j, (γ j : ZMod 3) * x j = 0}
    have hVA : Nat.card V = Nat.card A := by
      have h1 : Nat.card V = Nat.card ↥κ.range := by
        refine Nat.card_congr (Equiv.ofBijective
          (fun x : ↥V => (⟨Multiplicative.ofAdd (x : Fin Tag.E6.rank → ZMod 3), x.2⟩ :
            ↥κ.range)) ?_)
        refine ⟨?_, ?_⟩
        · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
          apply Subtype.ext
          exact congrArg (fun z : ↥κ.range =>
            fun j : Fin Tag.E6.rank =>
              Multiplicative.toAdd (z : Multiplicative (Fin 6 → ZMod 3)) (Fin.cast h6 j)) hxy
        · intro y
          refine ⟨⟨Multiplicative.toAdd y.1, ?_⟩, ?_⟩
          · show Multiplicative.ofAdd (Multiplicative.toAdd y.1) ∈ κ.range
            simpa using y.2
          · apply Subtype.ext
            rfl
      have h2 : Nat.card ↥κ.range = Nat.card A := by
        refine (Nat.card_congr (Equiv.ofBijective
          (fun a : A => (⟨κ a, MonoidHom.mem_range.mpr ⟨a, rfl⟩⟩ : ↥κ.range)) ?_)).symm
        refine ⟨?_, ?_⟩
        · intro a b hab
          exact hκinj (Subtype.ext_iff.mp hab)
        · intro y
          obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp y.2
          exact ⟨a, Subtype.ext ha⟩
      rw [h1, h2]
    have hmem : ∀ x : S, Multiplicative.ofAdd (x : Fin Tag.E6.rank → ZMod 3) ∈ κ.range :=
      fun x => x.2.1
    let aOf : S → A := fun x => Classical.choose (MonoidHom.mem_range.mp (hmem x))
    have haOf : ∀ x : S, κ (aOf x) =
        Multiplicative.ofAdd (x : Fin Tag.E6.rank → ZMod 3) :=
      fun x => Classical.choose_spec (MonoidHom.mem_range.mp (hmem x))
    have hle : Nat.card S ≤
        Nat.card ↥(A ⊓ ⨅ j : J, MulAction.stabilizer (MulAut L') (j : L')) := by
      let f : S → ↥(A ⊓ ⨅ j : J, MulAction.stabilizer (MulAut L') (j : L')) := fun x =>
        ⟨aOf x, Subgroup.mem_inf.mpr ⟨(aOf x).2, Subgroup.mem_iInf.mpr fun j =>
          (MulAction.mem_stabilizer_iff).mpr (by
            rw [MulAut.smul_def]
            refine hfixJ (aOf x) ?_ j j.2
            intro γ hγ
            rw [haOf x]
            change ∑ j, (γ j : ZMod 3) * (x : Fin Tag.E6.rank → ZMod 3) j = 0
            exact x.2.2 γ hγ)⟩⟩
      refine Nat.card_le_card_of_injective f ?_
      intro x y hxy
      apply Subtype.ext
      have hval : aOf x = aOf y := by
        have h := congrArg (fun z : ↥(A ⊓ ⨅ j : J,
          MulAction.stabilizer (MulAut L') (j : L')) => (z : MulAut L')) hxy
        have hx' : ((f x : ↥(A ⊓ ⨅ j : J,
          MulAction.stabilizer (MulAut L') (j : L'))) : MulAut L') = (aOf x : MulAut L') := rfl
        have hy' : ((f y : ↥(A ⊓ ⨅ j : J,
          MulAction.stabilizer (MulAut L') (j : L'))) : MulAut L') = (aOf y : MulAut L') := rfl
        rw [hx', hy'] at h
        exact Subtype.ext h
      have h : Multiplicative.ofAdd (x : Fin Tag.E6.rank → ZMod 3) =
          Multiplicative.ofAdd (y : Fin Tag.E6.rank → ZMod 3) := by
        rw [← haOf x, ← haOf y, hval]
      simpa using congrArg Multiplicative.toAdd h
    calc 3 ^ 2 * Nat.card S ≤
          3 ^ 2 * Nat.card ↥(A ⊓ ⨅ j : J, MulAction.stabilizer (MulAut L') (j : L')) :=
          Nat.mul_le_mul_left _ hle
      _ ≤ Nat.card A := hcount
      _ = Nat.card V := hVA.symm
  obtain ⟨γ₁, hγ₁, γ₂, hγ₂, w, hwV, hw⟩ : ∃ γ₁ ∈ componentRoots (rootCharHom ay) i,
      ∃ γ₂ ∈ componentRoots (rootCharHom ay) i, ∃ w ∈ V,
        ExcSplitRootGen.excRefl (p := 3) γ₁ (ExcSplitRootGen.excRefl (p := 3) γ₂ w) ≠
          ExcSplitRootGen.excRefl (p := 3) γ₂ (ExcSplitRootGen.excRefl (p := 3) γ₁ w) :=
    e6Three_exists_noncomm_pair hV i hcardV
  have hγ₁r : IsRoot Tag.E6 γ₁ := by
    obtain ⟨⟨h, -⟩, -⟩ := hγ₁
    exact h
  have hγ₂r : IsRoot Tag.E6 γ₂ := by
    obtain ⟨⟨h, -⟩, -⟩ := hγ₂
    exact h
  obtain ⟨m₁, hm₁, -, hr₁, hs₁⟩ := hlift γ₁ hγ₁r
  obtain ⟨m₂, hm₂, -, hr₂, hs₂⟩ := hlift γ₂ hγ₂r
  have hfy : ∀ γ ∈ componentRoots (rootCharHom ay) i, ∀ (m : L')
      (hm : MulAut.conj m ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      (∀ a : A, Multiplicative.toAdd (κ (ggConjAut A hm a)) =
        ExcSplitRootGen.excRefl (p := 3) γ (Multiplicative.toAdd (κ a))) →
      ggConjAut A hm ⟨y, hy⟩ = ⟨y, hy⟩ := by
    intro γ hγ m hm hs
    obtain ⟨hγk, -⟩ := hγ
    have hdot : ∑ j, (γ j : ZMod 3) * Multiplicative.toAdd (κ ⟨y, hy⟩) j = 0 :=
      (TwE6FixedA2Type.rootChar_zetaVec_eq_one_iff_dotZ3 hζo hζ
        (Multiplicative.toAdd (κ ⟨y, hy⟩)) γ).1 (by simpa [ay, rootCharHom] using hγk.2)
    have hfixκ : Multiplicative.toAdd (κ (ggConjAut A hm ⟨y, hy⟩)) =
        Multiplicative.toAdd (κ ⟨y, hy⟩) := by
      rw [hs ⟨y, hy⟩]
      exact (ExcSplitRootGen.excRefl_eq_self_iff (p := 3) (by norm_num) hγk.1 _).2 hdot
    exact hκinj (Multiplicative.toAdd.injective hfixκ)
  have hSL2 : GGTorusRootSL2 3 5 ↥(adjointGroup Tag.E6 K)
      ((hatAut Tag.E6 K).range : Set (MulAut ↥(adjointGroup Tag.E6 K))) :=
    ggTorusRootSL2_of_mulEquiv (TableBExc.recipeEquiv Tag.E6 K).symm
      (by
        intro φ hφ
        refine (E6ThreeModel.recipeID_iff_hatAut _).2 ?_
        have h : MulAut.congr (TableBExc.recipeEquiv Tag.E6 K)
            (MulAut.congr (TableBExc.recipeEquiv Tag.E6 K).symm φ) = φ := by
          ext x
          simp [MulAut.congr_apply]
        rw [h]
        exact hφ)
      (E6ThreeRootGen.ggTorusRootSL2_E6Three h3)
  obtain ⟨n₁, h₁, he₁, hW₁, hn₁⟩ := ggTBJ_exists_weyl_mem_of_rootSL2 hSL2 hTB hm₁ hr₁ hy
    (hfy γ₁ hγ₁ m₁ hm₁ hs₁) hJl
  obtain ⟨n₂, h₂, he₂, hW₂, hn₂⟩ := ggTBJ_exists_weyl_mem_of_rootSL2 hSL2 hTB hm₂ hr₂ hy
    (hfy γ₂ hγ₂ m₂ hm₂ hs₂) hJl
  refine ⟨n₁, n₂, h₁, h₂, hn₁, hn₂, hW₁, hW₂, by rw [he₁]; exact hr₁, by rw [he₂]; exact hr₂, ?_⟩
  rw [he₁, he₂]
  let castE : Multiplicative (Fin 6 → ZMod 3) → Multiplicative (Fin Tag.E6.rank → ZMod 3) :=
    fun v => Multiplicative.ofAdd (fun j : Fin Tag.E6.rank =>
      Multiplicative.toAdd v (Fin.cast h6 j))
  have hs₁'' : ∀ a : A, Multiplicative.toAdd (castE (κ ((ggConjAut A hm₁) a))) =
      ExcSplitRootGen.excRefl γ₁ (Multiplicative.toAdd (castE (κ a))) := by
    intro a
    simp only [castE, hcast, ofAdd_toAdd]
    exact hs₁ a
  have hs₂'' : ∀ a : A, Multiplicative.toAdd (castE (κ ((ggConjAut A hm₂) a))) =
      ExcSplitRootGen.excRefl γ₂ (Multiplicative.toAdd (castE (κ a))) := by
    intro a
    simp only [castE, hcast, ofAdd_toAdd]
    exact hs₂ a
  intro hcomm
  obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hwV
  have ha'' : castE (κ a) = Multiplicative.ofAdd w := by
    simp only [castE, hcast, ofAdd_toAdd]
    exact ha
  have hcomm_a : (ggConjAut A hm₁ * ggConjAut A hm₂) a =
      (ggConjAut A hm₂ * ggConjAut A hm₁) a := congrArg (fun f : MulAut ↥A => f a) hcomm
  rw [MulAut.mul_apply, MulAut.mul_apply] at hcomm_a
  have hκeq : Multiplicative.toAdd (castE (κ ((ggConjAut A hm₁) ((ggConjAut A hm₂) a)))) =
      Multiplicative.toAdd (castE (κ ((ggConjAut A hm₂) ((ggConjAut A hm₁) a)))) :=
    congrArg (fun z => Multiplicative.toAdd (castE (κ z))) hcomm_a
  rw [hs₁'' (ggConjAut A hm₂ a), hs₂'' a, hs₂'' (ggConjAut A hm₁ a), hs₁'' a, ha''] at hκeq
  simpa using hw hκeq

end E6Three

end CFSG.StandardType

end
