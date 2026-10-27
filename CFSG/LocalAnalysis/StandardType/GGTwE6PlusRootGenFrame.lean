module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwRootJ
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwRootC
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwLat2
public import CFSG.LocalAnalysis.StandardType.GGExcSplitRootGenDefs
public import CFSG.LocalAnalysis.StandardType.GGSuSplitRootGenDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcFldTwo
public import CFSG.LieType.Chevalley.CLSOddE7RationalEightGroup
public import CFSG.LieType.HighestRoot.CentChevalley
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcFldModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcHR2
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107

public section

namespace CFSG.StandardType.TwE6PlusRootGen

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley Multiplicative

private theorem ggKGTwStep_Y_eq
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)} (F : TwE6Frame K σ n p E)
    (hσ : ∀ c, σ c = c ^ (2 ^ n)) (x : twistedE6RootGroup K σ) :
    ggKGTwStep F (ggKGTwY F x) = ggKGTwY F x := by
  change canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) F.v *
      twistHom TwistTag.E6 (AlgebraicClosure K) F.Fr (ggKGTwY F x) *
      (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) F.v)⁻¹ =
    ggKGTwY F x
  rw [ggKGTwY_apply]
  rw [show twistHom TwistTag.E6 (AlgebraicClosure K) F.Fr
        (F.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          (x : ModGL TwistTag.E6.tag K) * F.g0) =
      (twistHom TwistTag.E6 (AlgebraicClosure K) F.Fr F.g0)⁻¹ *
        twistHom TwistTag.E6 (AlgebraicClosure K) F.Fr
          (baseChangeGL (algebraMap K (AlgebraicClosure K))
            (x : ModGL TwistTag.E6.tag K)) *
        twistHom TwistTag.E6 (AlgebraicClosure K) F.Fr F.g0 by
    rw [map_mul, map_mul, map_inv]]
  rw [F.lang, ggKGTc_twistHom_baseChange_eq_self F hσ x]
  group

private theorem ggKGTw_map_conj_rootRankOne
    {K : Type} [Field K]
    {u : WeylGroup Tag.E6} {γ : Fin Tag.E6.rank → ℤ}
    (hγ : IsRoot Tag.E6 γ) :
    (rootRankOneGroup Tag.E6 (AlgebraicClosure K) γ).map
        (MulAut.conj (canonicalRep (coxeterSystem Tag.E6)
          (AlgebraicClosure K) u)).toMonoidHom =
      rootRankOneGroup Tag.E6 (AlgebraicClosure K) (u • γ) := by
  have hU := (exceptional_Lang_root_rank_one_torus_transport Tag.E6
    (AlgebraicClosure K) hγ).1
  have hU' := (exceptional_Lang_root_rank_one_torus_transport Tag.E6
    (AlgebraicClosure K) (IsRoot.smul hγ u)).1
  have himg := (canonical_weyl_root_transport Tag.E6 (AlgebraicClosure K)).1 u
    ({γ, -γ} : Set (Fin Tag.E6.rank → ℤ)) (by
      rintro α (rfl | rfl)
      · exact hγ
      · exact IsRoot.neg hγ)
  rw [hU, hU', ← CFSG.LieType.HighestRoot.rootSpan_pair_eq (τ := Tag.E6)
      (K := AlgebraicClosure K) γ,
    ← CFSG.LieType.HighestRoot.rootSpan_pair_eq (τ := Tag.E6)
      (K := AlgebraicClosure K) (u • γ), himg]
  congr 1
  rw [Set.image_pair, smul_neg]

theorem ggKGTw_conj_rootDiagUnit
    {K : Type} [Field K] {p : ℕ} [NeZero p]
    {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ p = 1)
    {u : WeylGroup TwistTag.E6.tag} {t : Fin TwistTag.E6.tag.rank → ZMod p} :
    canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u *
        rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u)⁻¹ =
      rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ
        (TableBExc.E6Three.adAct TwistTag.E6.tag p u t)) := by
  rw [canonicalRep_conj_rootDiagUnit, TableBExc.E6Three.weylTuple_zetaVec]

private def ggKGTw_liftZ {p : ℕ} (x : Fin TwistTag.E6.tag.rank → ZMod p) :
    Fin TwistTag.E6.tag.rank → ℤ :=
  fun i => ((x i).val : ℤ)

private theorem ggKGTw_pi_lift_add
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ} [NeZero p]
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n)) (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n + 1) (F : TwE6Frame K σ n p E)
    (hv : ExcIsLongest TwistTag.E6.tag F.v) {ζ : (AlgebraicClosure K)ˣ}
    (hζ' : IsPrimitiveRoot ζ p) (x y : Fin TwistTag.E6.tag.rank → ZMod p) :
    ggKGTl_pi hK hσ hp hp5 hpq F hv ζ hζ' (ggKGTw_liftZ (x + y)) =
      ggKGTl_pi hK hσ hp hp5 hpq F hv ζ hζ' (ggKGTw_liftZ x + ggKGTw_liftZ y) := by
  rw [ggKGTl_pi_eq_iff hK hσ hp hp5 hpq F hv ζ hζ']
  intro i
  simp only [ggKGTw_liftZ, Pi.add_apply]
  push_cast
  rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]

private theorem ggKGTw_pi_lift_spec
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ} [NeZero p]
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n)) (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n + 1) (F : TwE6Frame K σ n p E)
    (hv : ExcIsLongest TwistTag.E6.tag F.v) {ζ : (AlgebraicClosure K)ˣ}
    (hζ' : IsPrimitiveRoot ζ p) (hζ : ζ ^ p = 1)
    (x : Fin TwistTag.E6.tag.rank → ZMod p) :
    ggKGTwY F ((Additive.toMul (ggKGTl_pi hK hσ hp hp5 hpq F hv ζ hζ'
        (ggKGTw_liftZ x)) : ↥E) : twistedE6RootGroup K σ) =
      rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ x) := by
  exact ggKGTl_pi_spec hK hσ hp hp5 hpq F hv ζ hζ' (ggKGTw_liftZ x)

private theorem ggKGTw_isQuasisimple_assembly
    {Q : Type*} [Group Q] (h : CFSG.IsQuasisimple Q) : CFSG.Assembly.IsQuasisimple Q :=
  ⟨h.1.commutator_eq_top, h.2.1⟩

theorem exists_twE6PlusTorus
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ} [Fact p.Prime]
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n)) (hp5 : 5 ≤ p)
    (hpq : p ∣ 2 ^ n + 1) (F : TwE6Frame K σ n p E) (hv : ExcIsLongest TwistTag.E6.tag F.v)
    {ζ : (AlgebraicClosure K)ˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) :
    ∃ T : Multiplicative (Fin Tag.E6.rank → ZMod p) →* twistedE6RootGroup K σ,
      Function.Injective T ∧ T.range = E ∧
      ∀ t : Fin Tag.E6.rank → ZMod p,
        ggKGTwY F (T (ofAdd t)) =
          rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hζ' : IsPrimitiveRoot ζ p := hζo ▸ IsPrimitiveRoot.orderOf ζ
  change ∃ T : Multiplicative (Fin TwistTag.E6.tag.rank → ZMod p) →*
      twistedE6RootGroup K σ,
    Function.Injective T ∧ T.range = E ∧
    ∀ t : Fin TwistTag.E6.tag.rank → ZMod p,
      ggKGTwY F (T (ofAdd t)) =
        rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t)
  let T : Multiplicative (Fin TwistTag.E6.tag.rank → ZMod p) →*
      twistedE6RootGroup K σ :=
    { toFun := fun t =>
        ((Additive.toMul (ggKGTl_pi hK hσ Fact.out hp5 hpq F hv ζ hζ'
          (ggKGTw_liftZ (toAdd t))) : ↥E) : twistedE6RootGroup K σ)
      map_one' := by
        show ((Additive.toMul (ggKGTl_pi hK hσ Fact.out hp5 hpq F hv ζ hζ'
          (ggKGTw_liftZ (toAdd (1 :
            Multiplicative (Fin TwistTag.E6.tag.rank → ZMod p))))) :
            ↥E) : twistedE6RootGroup K σ) = 1
        rw [toAdd_one]
        have h0 : ggKGTw_liftZ (0 : Fin TwistTag.E6.tag.rank → ZMod p) = 0 := by
          funext i
          simp [ggKGTw_liftZ]
        rw [h0, map_zero]
        rfl
      map_mul' := by
        intro t t'
        show ((Additive.toMul (ggKGTl_pi hK hσ Fact.out hp5 hpq F hv ζ hζ'
          (ggKGTw_liftZ (toAdd (t * t')))) : ↥E) :
            twistedE6RootGroup K σ) =
          ((Additive.toMul (ggKGTl_pi hK hσ Fact.out hp5 hpq F hv ζ hζ'
            (ggKGTw_liftZ (toAdd t))) : ↥E) : twistedE6RootGroup K σ) *
          ((Additive.toMul (ggKGTl_pi hK hσ Fact.out hp5 hpq F hv ζ hζ'
            (ggKGTw_liftZ (toAdd t'))) : ↥E) : twistedE6RootGroup K σ)
        rw [toAdd_mul,
          ggKGTw_pi_lift_add hK hσ Fact.out hp5 hpq F hv hζ' (toAdd t) (toAdd t'),
          map_add]
        rfl }
  refine ⟨T, ?_, ?_, ?_⟩
  · intro t t' h
    have h' : Additive.toMul (ggKGTl_pi hK hσ Fact.out hp5 hpq F hv ζ hζ'
          (ggKGTw_liftZ (toAdd t))) =
        Additive.toMul (ggKGTl_pi hK hσ Fact.out hp5 hpq F hv ζ hζ'
          (ggKGTw_liftZ (toAdd t'))) := by
      apply Subtype.ext
      exact h
    have h2 : ggKGTl_pi hK hσ Fact.out hp5 hpq F hv ζ hζ'
          (ggKGTw_liftZ (toAdd t)) =
        ggKGTl_pi hK hσ Fact.out hp5 hpq F hv ζ hζ'
          (ggKGTw_liftZ (toAdd t')) :=
      Additive.toMul.injective h'
    have h3 := (ggKGTl_pi_eq_iff hK hσ Fact.out hp5 hpq F hv ζ hζ'
      (ggKGTw_liftZ (toAdd t)) (ggKGTw_liftZ (toAdd t'))).1 h2
    apply Multiplicative.toAdd.injective
    funext i
    have h4 := h3 i
    simp only [ggKGTw_liftZ] at h4
    simpa [ZMod.natCast_zmod_val] using h4
  · ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact (Additive.toMul (ggKGTl_pi hK hσ Fact.out hp5 hpq F hv ζ hζ'
        (ggKGTw_liftZ (toAdd t)))).2
    · intro hz
      obtain ⟨y, hy⟩ := ggKGTl_pi_surjective hK hσ Fact.out hp5 hpq F hv ζ hζ'
        (Additive.ofMul ⟨z, hz⟩)
      refine ⟨ofAdd (fun i => (y i : ZMod p)), ?_⟩
      show ((Additive.toMul (ggKGTl_pi hK hσ Fact.out hp5 hpq F hv ζ hζ'
        (ggKGTw_liftZ (fun i => (y i : ZMod p)))) : ↥E) :
          twistedE6RootGroup K σ) = z
      have h2 : ggKGTl_pi hK hσ Fact.out hp5 hpq F hv ζ hζ'
            (ggKGTw_liftZ (fun i => (y i : ZMod p))) =
          ggKGTl_pi hK hσ Fact.out hp5 hpq F hv ζ hζ' y := by
        rw [ggKGTl_pi_eq_iff hK hσ Fact.out hp5 hpq F hv ζ hζ']
        intro i
        simp [ggKGTw_liftZ]
      rw [h2]
      have hy' := congrArg Additive.toMul hy
      exact congrArg Subtype.val hy'
  · intro t
    exact ggKGTw_pi_lift_spec hK hσ Fact.out hp5 hpq F hv hζ' hζ t

theorem conj_twE6PlusTorus
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ} [NeZero p]
    {E : Subgroup (twistedE6RootGroup K σ)} (F : TwE6Frame K σ n p E)
    {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ p = 1)
    {T : Multiplicative (Fin Tag.E6.rank → ZMod p) →* twistedE6RootGroup K σ}
    (hT : ∀ t : Fin Tag.E6.rank → ZMod p,
      ggKGTwY F (T (ofAdd t)) =
        rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t))
    {u : WeylGroup Tag.E6} {x : twistedE6RootGroup K σ}
    (hx : ggKGTwY F x = canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u)
    (t : Fin Tag.E6.rank → ZMod p) :
    x * T (ofAdd t) * x⁻¹ = T (ofAdd (TableBExc.E6Three.adAct Tag.E6 p u t)) := by
  let T' : Multiplicative (Fin TwistTag.E6.tag.rank → ZMod p) →*
      twistedE6RootGroup K σ := T
  have hT' : ∀ t : Fin TwistTag.E6.tag.rank → ZMod p,
      ggKGTwY F (T' (ofAdd t)) =
        rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t) := hT
  let uT : WeylGroup TwistTag.E6.tag := u
  let tT : Fin TwistTag.E6.tag.rank → ZMod p := t
  have hxT : ggKGTwY F x =
      canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) uT := hx
  change x * T' (ofAdd tT) * x⁻¹ =
    T' (ofAdd (TableBExc.E6Three.adAct TwistTag.E6.tag p uT tT))
  apply ggKGTl_conj_injective F
  change ggKGTwY F (x * T' (ofAdd tT) * x⁻¹) =
    ggKGTwY F (T' (ofAdd (TableBExc.E6Three.adAct TwistTag.E6.tag p uT tT)))
  rw [map_mul, map_mul, map_inv, hxT, hT' tT,
    hT' (TableBExc.E6Three.adAct TwistTag.E6.tag p uT tT)]
  exact ggKGTw_conj_rootDiagUnit (u := uT) hζ

theorem torusFix_excRefl_eq_ggKGTwHyp
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ} [NeZero p]
    {E : Subgroup (twistedE6RootGroup K σ)} (F : TwE6Frame K σ n p E)
    {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ p = 1)
    {T : Multiplicative (Fin Tag.E6.rank → ZMod p) →* twistedE6RootGroup K σ}
    (hTinj : Function.Injective T) (hTE : T.range = E)
    (hT : ∀ t : Fin Tag.E6.rank → ZMod p,
      ggKGTwY F (T (ofAdd t)) =
        rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t))
    (γ : Fin Tag.E6.rank → ℤ) :
    SuSplitRootGen.torusFix T (ExcSplitRootGen.excRefl (τ := Tag.E6) γ) =
      (ggKGTwHyp F γ : Set (twistedE6RootGroup K σ)) := by
  let T' : Multiplicative (Fin TwistTag.E6.tag.rank → ZMod p) →*
      twistedE6RootGroup K σ := T
  have hT' : ∀ t : Fin TwistTag.E6.tag.rank → ZMod p,
      ggKGTwY F (T' (ofAdd t)) =
        rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t) := hT
  have hTinj' : Function.Injective T' := hTinj
  have hTE' : T'.range = E := hTE
  let γT : Fin TwistTag.E6.tag.rank → ℤ := γ
  change SuSplitRootGen.torusFix T'
      (ExcSplitRootGen.excRefl (τ := TwistTag.E6.tag) γT) =
    (ggKGTwHyp F γT : Set (twistedE6RootGroup K σ))
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    unfold ggKGTwHyp
    rw [SetLike.mem_coe]
    refine Subgroup.mem_inf.2 ⟨?_, Subgroup.mem_comap.2 ?_⟩
    · rw [← hTE']
      exact ⟨t, rfl⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have hTt : ggKGTwY F (T' t) = rootDiagUnit TwistTag.E6.tag
          (TableBExc.E6Three.zetaVec ζ hζ (toAdd t)) := by
        simpa using hT' (toAdd t)
      rw [hTt]
      have hold := ggKGTw_conj_rootDiagUnit (u := rootReflection γT)
        (t := toAdd t) hζ
      have had : TableBExc.E6Three.adAct TwistTag.E6.tag p (rootReflection γT)
          (toAdd t) = toAdd t := ht
      rw [had] at hold
      have hcomm : rootDiagUnit TwistTag.E6.tag
            (TableBExc.E6Three.zetaVec ζ hζ (toAdd t)) *
            canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K)
              (rootReflection γT) =
          canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K)
              (rootReflection γT) *
            rootDiagUnit TwistTag.E6.tag
              (TableBExc.E6Three.zetaVec ζ hζ (toAdd t)) := by
        have h' : canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K)
              (rootReflection γT) *
              rootDiagUnit TwistTag.E6.tag
                (TableBExc.E6Three.zetaVec ζ hζ (toAdd t)) =
            rootDiagUnit TwistTag.E6.tag
              (TableBExc.E6Three.zetaVec ζ hζ (toAdd t)) *
              canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K)
                (rootReflection γT) := by
          calc canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K)
                (rootReflection γT) *
                rootDiagUnit TwistTag.E6.tag
                  (TableBExc.E6Three.zetaVec ζ hζ (toAdd t)) =
              (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K)
                  (rootReflection γT) *
                rootDiagUnit TwistTag.E6.tag
                  (TableBExc.E6Three.zetaVec ζ hζ (toAdd t)) *
                (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K)
                  (rootReflection γT))⁻¹) *
                canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K)
                  (rootReflection γT) := by group
            _ = rootDiagUnit TwistTag.E6.tag
                  (TableBExc.E6Three.zetaVec ζ hζ (toAdd t)) *
                canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K)
                  (rootReflection γT) := by rw [hold]
        exact h'.symm
      exact hcomm
  · intro hx
    unfold ggKGTwHyp at hx
    rw [SetLike.mem_coe] at hx
    rw [Subgroup.mem_inf, Subgroup.mem_comap] at hx
    obtain ⟨he, hc⟩ := hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hc
    have hxT : x ∈ T'.range := by
      rw [hTE']
      exact he
    obtain ⟨t, ht⟩ := hxT
    let t0 : Fin TwistTag.E6.tag.rank → ZMod p := toAdd t
    have hTt : T' (ofAdd t0) = x := by
      rw [show ofAdd t0 = t from ofAdd_toAdd t]
      exact ht
    have hTtY : ggKGTwY F (T' (ofAdd t0)) = rootDiagUnit TwistTag.E6.tag
        (TableBExc.E6Three.zetaVec ζ hζ t0) := hT' t0
    have hdn : rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t0) *
          canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K)
            (rootReflection γT) =
        canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K)
            (rootReflection γT) *
          rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t0) := by
      rw [← hTtY, hTt]
      exact hc
    have hconj : canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K)
            (rootReflection γT) *
            rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t0) *
            (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K)
              (rootReflection γT))⁻¹ =
          rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t0) := by
      calc canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K)
              (rootReflection γT) *
              rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t0) *
              (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K)
                (rootReflection γT))⁻¹ =
            (rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t0) *
              canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K)
                (rootReflection γT)) *
              (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K)
                (rootReflection γT))⁻¹ := by rw [hdn]
        _ = rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t0) := by
            group
    have hweyl : weylTuple (rootReflection γT)
          (TableBExc.E6Three.zetaVec ζ hζ t0) =
        TableBExc.E6Three.zetaVec ζ hζ t0 := by
      apply rootDiagUnit_injective (τ := TwistTag.E6.tag)
      have hcanon := canonicalRep_conj_rootDiagUnit (τ := TwistTag.E6.tag)
        (K := AlgebraicClosure K) (rootReflection γT)
        (TableBExc.E6Three.zetaVec ζ hζ t0)
      rw [← hcanon]
      exact hconj
    have hweyl' : TableBExc.E6Three.zetaVec ζ hζ
          (TableBExc.E6Three.adAct TwistTag.E6.tag p (rootReflection γT) t0) =
        TableBExc.E6Three.zetaVec ζ hζ t0 := by
      rw [← TableBExc.E6Three.weylTuple_zetaVec ζ hζ (rootReflection γT) t0]
      exact hweyl
    have hTad : T' (ofAdd (TableBExc.E6Three.adAct TwistTag.E6.tag p
          (rootReflection γT) t0)) = T' (ofAdd t0) := by
      apply ggKGTl_conj_injective F
      change ggKGTwY F (T' (ofAdd (TableBExc.E6Three.adAct TwistTag.E6.tag p
          (rootReflection γT) t0))) = ggKGTwY F (T' (ofAdd t0))
      rw [hT' (TableBExc.E6Three.adAct TwistTag.E6.tag p (rootReflection γT) t0),
        hT' t0, hweyl']
    have had : TableBExc.E6Three.adAct TwistTag.E6.tag p (rootReflection γT) t0 = t0 :=
      Multiplicative.toAdd.injective (hTinj' hTad)
    refine ⟨ofAdd t0, ?_, hTt⟩
    exact had

theorem mem_ggKGTwJ_iff
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)} (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (F : TwE6Frame K σ n p E) {γ : Fin Tag.E6.rank → ℤ} {x : twistedE6RootGroup K σ} :
    x ∈ ggKGTwJ F γ ↔
      ggKGTwY F x ∈ rootRankOneGroup TwistTag.E6.tag (AlgebraicClosure K) γ := by
  rw [ggKGTwJ, Subgroup.mem_comap, ggKGTwLhat, Subgroup.mem_inf]
  rw [show ggKGTwY F x ∈ (ggKGTwStep F).eqLocus (MonoidHom.id _) ↔
      ggKGTwStep F (ggKGTwY F x) = MonoidHom.id _ (ggKGTwY F x) from Iff.rfl]
  rw [MonoidHom.id_apply, ggKGTwStep_Y_eq F hσ x]
  simp

theorem ggKGTwJ_neg
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)} (F : TwE6Frame K σ n p E)
    {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) : ggKGTwJ F (-γ) = ggKGTwJ F γ := by
  let γT : Fin TwistTag.E6.tag.rank → ℤ := γ
  have hγT : IsRoot TwistTag.E6.tag γT := hγ
  change ggKGTwJ F (-γT) = ggKGTwJ F γT
  unfold ggKGTwJ ggKGTwLhat
  rw [CFSG.RankThree.PartOne.KE.rootRankOneGroup_neg (τ := TwistTag.E6.tag)
    (L := AlgebraicClosure K) hγT]

theorem map_conj_ggKGTwJ
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)} (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (F : TwE6Frame K σ n p E) {u : WeylGroup Tag.E6} {x : twistedE6RootGroup K σ}
    (hx : ggKGTwY F x *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u)⁻¹ ∈
      torusGroup TwistTag.E6.tag (AlgebraicClosure K))
    {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) :
    (ggKGTwJ F γ).map (MulAut.conj x).toMonoidHom = ggKGTwJ F (u • γ) := by
  let n : ModGL TwistTag.E6.tag (AlgebraicClosure K) :=
    canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u
  let h : ModGL TwistTag.E6.tag (AlgebraicClosure K) := ggKGTwY F x * n⁻¹
  have hxT : ggKGTwY F x * n⁻¹ ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K) := hx
  have hh : h ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K) := hxT
  have hYx : ggKGTwY F x = h * n := by
    dsimp [h]
    group
  have hQmap : (rootRankOneGroup TwistTag.E6.tag (AlgebraicClosure K) γ).map
        (MulAut.conj n).toMonoidHom =
      rootRankOneGroup TwistTag.E6.tag (AlgebraicClosure K) (u • γ) :=
    ggKGTw_map_conj_rootRankOne (u := u) (γ := γ) hγ
  have hP : IsRoot TwistTag.E6.tag (u • γ) := IsRoot.smul hγ u
  have hQnorm : h ∈ Subgroup.normalizer
      (rootRankOneGroup TwistTag.E6.tag (AlgebraicClosure K) (u • γ) :
        Set (ModGL TwistTag.E6.tag (AlgebraicClosure K))) :=
    CFSG.RankThree.PartOne.KE.torusGroup_le_normalizer_rootRankOneGroup
      (τ := TwistTag.E6.tag) (L := AlgebraicClosure K) (θ := u • γ) hP hh
  have hnormal : ∀ d : ModGL TwistTag.E6.tag (AlgebraicClosure K),
      h⁻¹ * d * h ∈ rootRankOneGroup TwistTag.E6.tag (AlgebraicClosure K) (u • γ) ↔
        d ∈ rootRankOneGroup TwistTag.E6.tag (AlgebraicClosure K) (u • γ) := by
    intro d
    have hmem := (Subgroup.mem_normalizer_iff.1 hQnorm) (h⁻¹ * d * h)
    simpa [mul_assoc] using hmem
  ext z
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  rw [mem_ggKGTwJ_iff hσ F (x := x⁻¹ * z * x), mem_ggKGTwJ_iff hσ F (x := z)]
  rw [map_mul, map_mul, map_inv, hYx]
  rw [show (h * n)⁻¹ * ggKGTwY F z * (h * n) =
      n⁻¹ * (h⁻¹ * ggKGTwY F z * h) * n by group]
  rw [← MulAut.conj_symm_apply, ← Subgroup.mem_map_equiv (f := MulAut.conj n), hQmap]
  rw [hnormal (ggKGTwY F z)]

theorem isComponentOf_ggKGTwJ
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n)) (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n + 1) (hq : 4 ≤ 2 ^ n) (F : TwE6Frame K σ n p E)
    (hv : ExcIsLongest TwistTag.E6.tag F.v) {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) :
    IsComponentOf (ggKGTwJ F γ)
      (Subgroup.centralizer (ggKGTwHyp F γ : Set (twistedE6RootGroup K σ))) := by
  exact ⟨ggKGTwJ_le_centralizer hp hp5 F hγ,
    ggKGTwJ_subnormal hK hσ hp hp5 hpq F hv hγ,
    ggKGTw_isQuasisimple_assembly (ggKGTwJ_quasisimple hK hσ F hv hγ hq)⟩

end CFSG.StandardType.TwE6PlusRootGen

end
