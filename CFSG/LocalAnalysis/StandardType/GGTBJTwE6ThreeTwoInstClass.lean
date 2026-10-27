module

public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6ThreeTwoInstSetup
public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6ThreeTwoWeyl
public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6ThreeTwoDesc
public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6ThreeClassA
public import CFSG.HardMathSupport.S2MathAs1.I1486.Geometry

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc
  TableBExc.E6Three CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.StandardType.TableCRes

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem tw1i_weylLift
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {L' : Type} [Group L'] [Finite L']
    {ψ₀ : L' →* ↥(twistedE6RootGroup K σ)} (hψ₀ : Function.Surjective ψ₀)
    (hker : ψ₀.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    (hker3 : ∀ z ∈ ψ₀.ker, z ^ 3 = 1) {A : Subgroup (MulAut L')}
    (Fm : TwE6ThreeFrame (n := 1) σ ψ₀ A) {J : Subgroup L'} {c : Fin Tag.E6.rank → ℤ}
    (hc : IsRoot Tag.E6 c) {p₀ : ℕ} (S : LangSetup Tag.E6 (AlgebraicClosure K) p₀)
    (e : twistedE6RootGroup K σ ≃* S.Γ)
    (he : ∀ x, (e x : ModGL Tag.E6 (AlgebraicClosure K)) = ggKGTwY Fm.F x)
    (hW : rootSL2 Tag.E6 (AlgebraicClosure K) c WSL ∈
      J.map (S.Γ.subtype.comp (e.toMonoidHom.comp ψ₀))) :
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
  obtain ⟨m, hmJ, hmW⟩ := Subgroup.mem_map.1 hW
  let W : ModGL TwistTag.E6.tag (AlgebraicClosure K) :=
    rootSL2 Tag.E6 (AlgebraicClosure K) c WSL
  have hψm : ggKGTwY Fm.F (ψ₀ m) = W := (he (ψ₀ m)).symm.trans hmW
  have hmat : ∀ x, ((ψ₀ m : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) * Fm.t x *
      ((ψ₀ m : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K)⁻¹ =
        Fm.t (ExcSplitRootGen.excRefl (p := 3) c x) := by
    intro x
    apply baseChangeGL_injective (f := algebraMap K (AlgebraicClosure K))
    have hbc : baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((ψ₀ m : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) =
          Fm.F.g0 * W * Fm.F.g0⁻¹ := by
      rw [← hψm, ggKGTwY_apply]
      group
    have hconj : W * rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec Fm.ζ Fm.hζ x) *
        W⁻¹ = rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec Fm.ζ Fm.hζ
          (adAct Tag.E6 3 (rootReflection c) x)) := by
      have h := QTwoCav.rootWeylSL2_conj_rootDiagUnit S hc
        (TableBExc.E6Three.zetaVec Fm.ζ Fm.hζ x)
      rw [weylTuple_zetaVec] at h
      exact h
    rw [map_mul, map_mul, map_inv, hbc, Fm.htF x, Fm.htF (ExcSplitRootGen.excRefl (p := 3) c x)]
    calc Fm.F.g0 * W * Fm.F.g0⁻¹ *
          (Fm.F.g0 * rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec Fm.ζ Fm.hζ x) *
            Fm.F.g0⁻¹) * (Fm.F.g0 * W * Fm.F.g0⁻¹)⁻¹
        = Fm.F.g0 * (W * rootDiagUnit TwistTag.E6.tag
            (TableBExc.E6Three.zetaVec Fm.ζ Fm.hζ x) * W⁻¹) * Fm.F.g0⁻¹ := by group
      _ = Fm.F.g0 * rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec Fm.ζ Fm.hζ
            (ExcSplitRootGen.excRefl (p := 3) c x)) * Fm.F.g0⁻¹ := by
          rw [hconj]
          rfl
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
    (m := m) hmat
  exact ⟨m, hN, hmJ, hWeyl, fun a => hcoord a⟩

theorem tw1i_d4Label
    {n : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) {σ : K ≃+* K} {L' : Type} [Group L'] [Finite L']
    {ψ₀ : L' →* ↥(twistedE6RootGroup K σ)} (hker : ψ₀.ker ≤ Subgroup.center L')
    {A : Subgroup (MulAut L')} (Fm : TwE6ThreeFrame (n := n) σ ψ₀ A) {J : Subgroup L'}
    (t₀ : Fin Tag.E6.rank → ZMod 3) (hJp : Group.IsPerfect ↥J)
    {p₀ : ℕ} (S : LangSetup Tag.E6 (AlgebraicClosure K) p₀)
    (e : twistedE6RootGroup K σ ≃* S.Γ)
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

theorem tw1i_classA
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ 1) {L' : Type} [Group L'] [Finite L']
    {ψ₀ : L' →* ↥(twistedE6RootGroup K σ)} (hψ₀ : Function.Surjective ψ₀)
    (hker : ψ₀.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    (hker3 : ∀ z ∈ ψ₀.ker, z ^ 3 = 1) {A : Subgroup (MulAut L')}
    (Fm : TwE6ThreeFrame (n := 1) σ ψ₀ A) {y : ↥A} (hy1 : y ≠ 1) {J : Subgroup L'}
    (hJ : IsComponentOf J (fixSubgroup (y : MulAut L'))) :
    GGE6ThreeClassA A Fm.κ y J (GGTwE6D4Label J) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hd1 := ggTwE6Three_ne_one hker hperf Fm hy1
  obtain ⟨S, e, i, he, hρ, hSq, -, hdT, hqi, hmap⟩ :=
    tw1i_class_setup Nat.prime_five (Or.inl le_rfl) (by norm_num) le_rfl hK hσ (by norm_num)
      Fm.F Fm.hv Fm.hζ ψ₀ hψ₀ hker (Multiplicative.toAdd (Fm.κ y)) hd1 (y : MulAut L')
      (ggTwE6Three_act Fm y) (isComponentOf_iff_open.1 hJ)
  have hJp : ⁅J, J⁆ = J := Subgroup.isPerfect_iff.1 ⟨hJ.2.2.1⟩
  have hfix := tw1i_class_kernel Fm.F Fm.hζ ψ₀ hker (Multiplicative.toAdd (Fm.κ y)) hJp S e i he
    hρ hmap
  have hq2 : S.D.q = 2 := by rw [hSq]; norm_num
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2 * 1)
    (by rw [Fintype.card_eq_nat_card, hK, ← pow_mul, mul_comm])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hAlg : S.IsAlgebraic := S.isAlgebraic_of_algebraic K 2 (by rw [hK, hSq])
  have hap : ∀ j, (TableBExc.E6Three.zetaVec Fm.ζ Fm.hζ (Multiplicative.toAdd (Fm.κ y)) j) ^ 3
      = 1 := by
    intro j
    change (Fm.ζ ^ (Multiplicative.toAdd (Fm.κ y) j).val) ^ 3 = 1
    rw [← pow_mul, mul_comm, pow_mul, Fm.hζ, one_pow]
  have hW := tw1w_weylPoint_mem S hq2 hAlg hρ hdT hap hd1 i hqi
  unfold GGE6ThreeClassA
  refine ⟨AlgebraicClosure K, inferInstance, Fm.ζ, Fm.hζ, Fm.hζo, i, ?_, ?_, ?_⟩
  ·
    intro a ha j hj
    exact hfix (a : MulAut L') (Multiplicative.toAdd (Fm.κ a)) (ggTwE6Three_act Fm a) ha j hj
  ·
    intro c hc
    obtain ⟨m, hN, hmJ, hWeyl, hcoord⟩ := tw1i_weylLift hψ₀ hker hperf hker3 Fm
      (isRoot_of_mem_componentRoots hc) S e he (by rw [hmap]; exact hW c hc)
    exact ⟨m, hN, hmJ, hWeyl, hcoord⟩
  ·
    intro hD4
    haveI : Group.IsPerfect ↥J := ⟨hJ.2.2.1⟩
    exact tw1i_d4Label hK hker Fm (Multiplicative.toAdd (Fm.κ y)) inferInstance S e i hρ hdT hqi
      hmap hD4

theorem tw1i_comp_invariant
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ 1) {L' : Type} [Group L'] [Finite L']
    {ψ₀ : L' →* ↥(twistedE6RootGroup K σ)} (hψ₀ : Function.Surjective ψ₀)
    (hker : ψ₀.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (Fm : TwE6ThreeFrame (n := 1) σ ψ₀ A) {y : ↥A} (hy1 : y ≠ 1)
    {J : Subgroup L'} (hJ : IsComponentOf J (fixSubgroup (y : MulAut L'))) :
    ∀ a ∈ A, ∀ x ∈ J, a x ∈ J := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hd1 := ggTwE6Three_ne_one hker hperf Fm hy1
  obtain ⟨S, e, i, he, hρ, hSq, htor, hdT, hqi, hmap⟩ :=
    tw1i_class_setup Nat.prime_five (Or.inl le_rfl) (by norm_num) le_rfl hK hσ (by norm_num)
      Fm.F Fm.hv Fm.hζ ψ₀ hψ₀ hker (Multiplicative.toAdd (Fm.κ y)) hd1 (y : MulAut L')
      (ggTwE6Three_act Fm y) (isComponentOf_iff_open.1 hJ)
  have hJc : commutator ↥J = ⊤ := hJ.2.2.1
  let ψ' : L' →* ModGL Tag.E6 (AlgebraicClosure K) := S.Γ.subtype.comp (e.toMonoidHom.comp ψ₀)
  have hψ' : ∀ l, ψ' l = ggKGTwY Fm.F (ψ₀ l) := fun l => he (ψ₀ l)
  have hker' : ψ'.ker ≤ Subgroup.center L' := by
    intro l hl
    apply hker
    rw [MonoidHom.mem_ker] at hl ⊢
    have h1 : e (ψ₀ l) = 1 := Subtype.ext hl
    exact e.map_eq_one_iff.mp h1
  intro a ha
  refine TwDesc.mem_of_perfect_of_central (J := J) (C := Subgroup.center L') hJc le_rfl ?_
  intro x hx
  let a' : ↥A := ⟨a, ha⟩
  let d : ModGL Tag.E6 (AlgebraicClosure K) := rootDiagUnit Tag.E6
    (TableBExc.E6Three.zetaVec Fm.ζ Fm.hζ (Multiplicative.toAdd (Fm.κ a')))
  have hdb : rootDiagUnit Tag.E6 (TableBExc.E6Three.zetaVec Fm.ζ Fm.hζ
      (Multiplicative.toAdd (Fm.κ a'))) ∈ S.D.torus := by
    refine (htor _).2 fun j => ?_
    change (Fm.ζ ^ (Multiplicative.toAdd (Fm.κ a') j).val) ^ (2 ^ 1 + 1) = 1
    rw [← pow_mul, mul_comm, pow_mul, show 2 ^ 1 + 1 = 3 by norm_num, Fm.hζ, one_pow]
  have hF : S.D.step d = d := (S.D.mem_model.1 (S.D.torus_le_model hdb)).2
  have hψx : ψ' x ∈ rationalComponent S.ρ S.Γ (rootCharHom (TableBExc.E6Three.zetaVec Fm.ζ Fm.hζ
      (Multiplicative.toAdd (Fm.κ y)))) i := by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem ψ' hx
  have hconj := CFSG.HardMathSupport.S2MathAs1.I1486.conj_mem_rationalComponent_of_mem_sup_rootSpan
    S hdT i (y := d) (Subgroup.mem_sup_left (rootDiagUnit_mem_torusGroup _)) hF (ψ' x) hψx
  have hψax : ψ' (a x) = d * ψ' x * d⁻¹ := by
    have h := ggTwE6Three_act Fm a' x
    rw [hψ', hψ']
    exact h
  have hmem : ψ' (a x) ∈ J.map ψ' := by
    rw [hmap, hψax]
    exact hconj
  obtain ⟨j, hj, hjx⟩ := hmem
  refine ⟨j, hj, j⁻¹ * a x, hker' ?_, by group⟩
  rw [MonoidHom.mem_ker, map_mul, map_inv, hjx, inv_mul_cancel]

end CFSG.StandardType

end
