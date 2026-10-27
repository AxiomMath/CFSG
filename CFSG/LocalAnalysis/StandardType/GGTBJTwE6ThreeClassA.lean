module

public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6ThreeFrame
public import CFSG.LocalAnalysis.StandardType.GGTBJE6ThreeData
public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6Class
public import CFSG.LocalAnalysis.StandardType.GGTBJE6ThreeD4RatLabel
public import CFSG.LocalAnalysis.StandardType.GGTBJE6ThreeWeyl
public import CFSG.LieType.Chevalley.GraphFixedCenterTrivial

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc
  TableBExc.E6Three CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.StandardType.TableCRes

@[expose] def GGTwE6D4Label {G : Type} [Group G] (J : Subgroup G) : Prop :=
  ∃ m : ℕ, 1 ≤ m ∧ GGHasLabel (⟨.D, 4, m⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J)

theorem ggTwE6Three_act
    {n : ℕ} {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    {L' : Type} [Group L'] {ψ₀ : L' →* ↥(twistedE6RootGroup K σ)} {A : Subgroup (MulAut L')}
    (Fm : TwE6ThreeFrame (n := n) σ ψ₀ A) (a : ↥A) (l : L') :
    ggKGTwY Fm.F (ψ₀ ((a : MulAut L') l)) =
      rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec Fm.ζ Fm.hζ (Multiplicative.toAdd
        (Fm.κ a))) * ggKGTwY Fm.F (ψ₀ l) * (rootDiagUnit TwistTag.E6.tag
          (TableBExc.E6Three.zetaVec Fm.ζ Fm.hζ (Multiplicative.toAdd (Fm.κ a))))⁻¹ := by
  rw [ggKGTwY_apply, ggKGTwY_apply, Fm.hconj a l, map_mul, map_mul, map_inv, Fm.htF]
  group
  rfl

theorem ggTwE6Three_ne_one
    {n : ℕ} {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    {L' : Type} [Group L'] {ψ₀ : L' →* ↥(twistedE6RootGroup K σ)}
    (hker : ψ₀.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤) {A : Subgroup (MulAut L')}
    (Fm : TwE6ThreeFrame (n := n) σ ψ₀ A) {y : ↥A} (hy1 : y ≠ 1) :
    rootDiagUnit TwistTag.E6.tag
      (TableBExc.E6Three.zetaVec Fm.ζ Fm.hζ (Multiplicative.toAdd (Fm.κ y))) ≠ 1 := by
  intro hd
  apply hy1
  have hYinj : Function.Injective (ggKGTwY Fm.F) := by
    intro x x' h
    rw [ggKGTwY_apply, ggKGTwY_apply] at h
    exact Subtype.ext (baseChangeGL_injective (f := algebraMap K (AlgebraicClosure K))
      (mul_left_cancel (mul_right_cancel h)))
  refine Subtype.ext (TypeA.mulAut_eq_of_forall ψ₀ hker hperf fun l => hYinj ?_)
  rw [ggTwE6Three_act Fm y l, hd, one_mul, inv_one, mul_one]
  rfl

theorem ggTwE6Three_weylLift
    {n : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ n) {L' : Type} [Group L'] [Finite L']
    {ψ₀ : L' →* ↥(twistedE6RootGroup K σ)} (hψ₀ : Function.Surjective ψ₀)
    (hker : ψ₀.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    (hker3 : ∀ z ∈ ψ₀.ker, z ^ 3 = 1) {A : Subgroup (MulAut L')}
    (Fm : TwE6ThreeFrame (n := n) σ ψ₀ A) {J : Subgroup L'} {c : Fin Tag.E6.rank → ℤ}
    (hc : IsRoot Tag.E6 c) (hlow : ∀ r ∈ ggKGTwJ Fm.F c, ∃ m ∈ J, ψ₀ m = r) :
    ∃ (m : L') (hN : MulAut.conj m ∈ Subgroup.normalizer (A : Set (MulAut L'))), m ∈ J ∧
      GGTorusWeylElt 3 A m ∧ ∀ a : ↥A, Multiplicative.toAdd (Fm.κ (ggConjAut A hN a)) =
        adAct Tag.E6 3 (rootReflection c) (Multiplicative.toAdd (Fm.κ a)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let V : Set (Fin Tag.E6.rank → ZMod 3) := {x | Multiplicative.ofAdd x ∈ Fm.κ.range}
  have hκV : ∀ x, Multiplicative.ofAdd x ∈ Fm.κ.range ↔ x ∈ V := fun _ => Iff.rfl
  have hV : V = Set.univ ∨ V = (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3)) :=
    coordSet_eq_univ_or_hypE6_twE6Three Fm.hκrange
  have htmul : ∀ x x', Fm.t (x + x') = Fm.t x * Fm.t x' :=
    t_add_twE6Three (algebraMap K (AlgebraicClosure K)) Fm.hζ Fm.htF
  obtain ⟨r, hrJ, hr⟩ :=
    TwE6ThreeRootGen.exists_mem_ggKGTwJ_conj hK hσ Fm.F Fm.hv Fm.hζ Fm.htF hc
  obtain ⟨m, hmJ, hmr⟩ := hlow r hrJ
  have hsH : ∀ x, ExcSplitRootGen.excRefl (p := 3) c x - x ∈ NoOffRest.hypE6 := fun x => by
    simpa only [ExcSplitRootGen.excRefl] using
      TableBExc.E6Three.adAct_sub_mem_hypE6 (rootReflection c) x
  have hsV : ∀ x ∈ V, ExcSplitRootGen.excRefl (p := 3) c x ∈ V := by
    intro x hx
    rcases hV with hV' | hV'
    · rw [hV']
      exact Set.mem_univ _
    · rw [hV'] at hx ⊢
      have h := NoOffRest.hypE6.add_mem (hsH x) (SetLike.mem_coe.1 hx)
      rw [sub_add_cancel] at h
      exact SetLike.mem_coe.2 h
  obtain ⟨hN, hWeyl, hcoord⟩ := e6Three_weylPoint hψ₀ hker hperf
    (center_graphFixedRootGroup_eq_bot (t := TwistTag.E6) (σ := σ.toRingHom) σ.surjective)
    hker3 Fm.hκinj hκV htmul Fm.hconj Fm.hTodd Fm.hTfix Fm.hHyp
    (s := ExcSplitRootGen.excRefl (p := 3) c) (ExcSplitRootGen.excRefl_excRefl hc) hsV hsH
    (m := m) (fun x => by rw [hmr]; exact hr x)
  exact ⟨m, hN, hmJ, hWeyl, fun a => hcoord a⟩

theorem ggTwE6Three_d4Label
    {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) {σ : K ≃+* K} {L' : Type} [Group L'] [Finite L']
    {ψ₀ : L' →* ↥(twistedE6RootGroup K σ)} (hker : ψ₀.ker ≤ Subgroup.center L')
    {A : Subgroup (MulAut L')} (Fm : TwE6ThreeFrame (n := n) σ ψ₀ A) {J : Subgroup L'}
    (t₀ : Fin Tag.E6.rank → ZMod 3) (hJp : Group.IsPerfect ↥J)
    (S : LangSetup Tag.E6 (AlgebraicClosure K) 3) (e : twistedE6RootGroup K σ ≃* S.Γ)
    (i : KernelComponent (rootCharHom (TableBExc.E6Three.zetaVec Fm.ζ Fm.hζ
      t₀)))
    (hρ : ∀ α, S.ρ α = -α)
    (hdT : rootDiagUnit Tag.E6 (TableBExc.E6Three.zetaVec Fm.ζ Fm.hζ
      t₀) ∈ S.D.torus)
    (hqi : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom
      (TableBExc.E6Three.zetaVec Fm.ζ Fm.hζ t₀)) i))
    (hmap : J.map (S.Γ.subtype.comp (e.toMonoidHom.comp ψ₀)) = rationalComponent S.ρ S.Γ
      (rootCharHom (TableBExc.E6Three.zetaVec Fm.ζ Fm.hζ t₀)) i)
    (hD4 : ∃ v : WeylGroup Tag.E6, componentRoots (rootCharHom
      (TableBExc.E6Three.zetaVec Fm.ζ Fm.hζ t₀)) i =
        (fun α => v • α) '' parabolicRoots Tag.E6 {j | j ∉ ({0, 5} : Finset (Fin 6))}) :
    GGTwE6D4Label J := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2 * n)
    (by rw [Fintype.card_eq_nat_card, hK, ← pow_mul, mul_comm])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hap : ∀ j, (TableBExc.E6Three.zetaVec Fm.ζ Fm.hζ t₀ j) ^ 3
      = 1 := by
    intro j
    change (Fm.ζ ^ (t₀ j).val) ^ 3 = 1
    rw [← pow_mul, mul_comm, pow_mul, Fm.hζ, one_pow]
  have hkind : twistKindOf S.ρ (componentRoots (rootCharHom
      (TableBExc.E6Three.zetaVec Fm.ζ Fm.hζ t₀)) i) =
        TwistKind.inner := by
    obtain ⟨v, hv⟩ := hD4
    rw [hv]
    exact e6D4_twistKindOf_neg S.ρ hρ v
  obtain ⟨m, hm1, hlab⟩ := e6D4_label_of_rationalComponent (p := 3) S Nat.prime_three
    (by norm_num) hdT hap i hqi hD4 hkind
  let ψ' : L' →* ModGL Tag.E6 (AlgebraicClosure K) :=
    S.Γ.subtype.comp (e.toMonoidHom.comp ψ₀)
  have hker' : ψ'.ker ≤ Subgroup.center L' := by
    intro l hl
    apply hker
    rw [MonoidHom.mem_ker] at hl ⊢
    have h1 : e (ψ₀ l) = 1 := Subtype.ext hl
    exact e.map_eq_one_iff.mp h1
  let f : ↥J →* ↥(rationalComponent S.ρ S.Γ (rootCharHom (TableBExc.E6Three.zetaVec Fm.ζ Fm.hζ
      t₀)) i) :=
    (MulEquiv.subgroupCongr hmap).toMonoidHom.comp (ψ'.subgroupMap J)
  have hf : Function.Surjective f :=
    (MulEquiv.subgroupCongr hmap).surjective.comp (ψ'.subgroupMap_surjective J)
  have hfker : f.ker ≤ Subgroup.center ↥J := by
    intro x hx
    have hx1 : ψ' (x : L') = 1 := by
      have h1 : (MulEquiv.subgroupCongr hmap) (ψ'.subgroupMap J x) = 1 := hx
      have h2 : ψ'.subgroupMap J x = 1 := (MulEquiv.subgroupCongr hmap).map_eq_one_iff.1 h1
      exact congrArg Subtype.val h2
    rw [Subgroup.mem_center_iff]
    intro z
    exact Subtype.ext (Subgroup.mem_center_iff.1 (hker' hx1) (z : L'))
  exact ⟨m, hm1, ggHasLabel_quotCenter_of_central_cover hJp f hf hfker hlab⟩

theorem ggTwE6Three_classA
    {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (h3 : 3 ∣ 2 ^ n + 1) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ n) {L' : Type} [Group L'] [Finite L']
    {ψ₀ : L' →* ↥(twistedE6RootGroup K σ)} (hψ₀ : Function.Surjective ψ₀)
    (hker : ψ₀.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    (hker3 : ∀ z ∈ ψ₀.ker, z ^ 3 = 1) {A : Subgroup (MulAut L')}
    (Fm : TwE6ThreeFrame (n := n) σ ψ₀ A) {y : ↥A} (hy1 : y ≠ 1) {J : Subgroup L'}
    (hJ : IsComponentOf J (fixSubgroup (y : MulAut L'))) :
    GGE6ThreeClassA A Fm.κ y J (GGTwE6D4Label J) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hd1 := ggTwE6Three_ne_one hker hperf Fm hy1
  obtain ⟨S, e, i, he, hρ, hdT, hqi, hmap⟩ :=
    ggTBJ_twE6_class_setup (p := 3) hn hK hσ h3 Fm.F Fm.hv Fm.hζ ψ₀ hψ₀ hker
      (Multiplicative.toAdd (Fm.κ y)) hd1 (y : MulAut L') (ggTwE6Three_act Fm y)
      (isComponentOf_iff_open.1 hJ)
  have hJp : ⁅J, J⁆ = J := Subgroup.isPerfect_iff.1 ⟨hJ.2.2.1⟩
  obtain ⟨hlow, hfix⟩ := ggTBJ_twE6_class_of_setup hn hK hσ Fm.F Fm.hv Fm.hζ ψ₀ hker
    (Multiplicative.toAdd (Fm.κ y)) hJp S e i he hρ hmap
  unfold GGE6ThreeClassA
  refine ⟨AlgebraicClosure K, inferInstance, Fm.ζ, Fm.hζ, Fm.hζo, i, ?_, ?_, ?_⟩
  ·
    intro a ha j hj
    exact hfix (a : MulAut L') (Multiplicative.toAdd (Fm.κ a)) (ggTwE6Three_act Fm a) ha j hj
  ·
    intro c hc
    exact ggTwE6Three_weylLift hK hσ hψ₀ hker hperf hker3 Fm (isRoot_of_mem_componentRoots hc)
      (hlow c hc)
  ·
    intro hD4
    haveI : Group.IsPerfect ↥J := ⟨hJ.2.2.1⟩
    exact ggTwE6Three_d4Label hn hK hker Fm (Multiplicative.toAdd (Fm.κ y)) inferInstance S e i hρ
      hdT hqi hmap hD4

end CFSG.StandardType

end
