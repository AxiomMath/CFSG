module

public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6LeviRoots
public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6Lang
public import CFSG.LocalAnalysis.StandardType.GGTBJLift
public import CFSG.LocalAnalysis.StandardType.GGLangExhaust
public import CFSG.LocalAnalysis.StandardType.GGLangRatComp
public import CFSG.LocalAnalysis.StandardType.GGLangCorootPair
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE8FiveFrameCentralizer
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsExcAux.Reduce
public import CFSG.LocalAnalysis.SectionRank.LocalDet

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

theorem ggTBJTwE6_rootChar_zetaVec_eq_one {L : Type} [Field L] {p : ℕ} [NeZero p] {ζ : Lˣ}
    (hζ : ζ ^ p = 1) (t : Fin Tag.E6.rank → ZMod p) (β : Fin Tag.E6.rank → ℤ)
    (h : ∑ j, (β j : ZMod p) * t j = 0) :
    rootChar (TableBExc.E6Three.zetaVec ζ hζ t) β = 1 := by
  rw [CFSG.StandardType.NoOffE8Five.rootChar_zetaVec, h]
  simp

theorem ggTBJ_twE6_class_setup
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    [Fact p.Prime] {E : Subgroup (twistedE6RootGroup K σ)} (hn : 2 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n)) (hpq : p ∣ 2 ^ n + 1)
    (F : TwE6Frame K σ n p E) (hv : ExcIsLongest TwistTag.E6.tag F.v)
    {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ p = 1)
    {L' : Type} [Group L'] [Finite L'] (ψ : L' →* twistedE6RootGroup K σ)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (t₀ : Fin Tag.E6.rank → ZMod p)
    (hd1 : rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t₀) ≠ 1) (y : MulAut L')
    (hy : ∀ l, ggKGTwY F (ψ (y l)) =
      rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t₀) * ggKGTwY F (ψ l) *
        (rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t₀))⁻¹)
    {J : Subgroup L'} (hJ : CFSG.Open.IsComponentOf J (fixSubgroup y)) :
    ∃ (S : LangSetup Tag.E6 (AlgebraicClosure K) p) (e : twistedE6RootGroup K σ ≃* S.Γ)
      (i : KernelComponent (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ t₀))),
      (∀ x, (e x : ModGL Tag.E6 (AlgebraicClosure K)) = ggKGTwY F x) ∧ (∀ α, S.ρ α = -α) ∧
      rootDiagUnit Tag.E6 (TableBExc.E6Three.zetaVec ζ hζ t₀) ∈ S.D.torus ∧
      CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ
        (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ t₀)) i) ∧
      J.map (S.Γ.subtype.comp (e.toMonoidHom.comp ψ)) =
        rationalComponent S.ρ S.Γ (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ t₀)) i := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by
    rintro rfl
    have : (2 : ℕ) ∣ 1 := (Nat.dvd_add_right (dvd_pow_self 2 (by omega))).1 hpq
    omega
  have hpn : ¬ p ∣ 2 ^ n := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
    (hp.dvd_of_dvd_pow h))
  obtain ⟨S, e, he, hρ, -, htor⟩ :=
    exists_ggTBJTwE6FrameSetup (by omega) hK hσ F hv hp (Or.inr hn) hpn
  set a₀ : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ := TableBExc.E6Three.zetaVec ζ hζ t₀ with ha₀
  set d : ModGL Tag.E6 (AlgebraicClosure K) := rootDiagUnit Tag.E6 a₀ with hd
  let ψ' : L' →* ModGL Tag.E6 (AlgebraicClosure K) := S.Γ.subtype.comp (e.toMonoidHom.comp ψ)
  have hψ' : ∀ l, ψ' l = ggKGTwY F (ψ l) := fun l => he (ψ l)
  have hker' : ψ'.ker ≤ Subgroup.center L' := by
    intro l hl
    apply hker
    rw [MonoidHom.mem_ker] at hl ⊢
    have h1 : e (ψ l) = 1 := Subtype.ext hl
    exact e.map_eq_one_iff.mp h1
  have hrange : S.Γ ≤ ψ'.range := by
    intro g hg
    obtain ⟨r, hr⟩ := e.surjective ⟨g, hg⟩
    obtain ⟨l, rfl⟩ := hψ r
    exact ⟨l, by change ((e (ψ l) : S.Γ) : ModGL Tag.E6 (AlgebraicClosure K)) = g; rw [hr]⟩
  have hyd : ∀ l, ψ' (y l) = d * ψ' l * d⁻¹ := fun l => by rw [hψ', hψ']; exact hy l
  have hζq : ζ ^ (2 ^ n + 1) = 1 := by
    obtain ⟨k, hk⟩ := hpq
    rw [hk, pow_mul, hζ, one_pow]
  have hdT : d ∈ S.D.torus := by
    refine (htor a₀).2 fun i => ?_
    change (ζ ^ (t₀ i).val) ^ (2 ^ n + 1) = 1
    rw [← pow_mul, mul_comm, pow_mul, hζq, one_pow]
  have hap : ∀ i, a₀ i ^ p = 1 := by
    intro i
    change (ζ ^ (t₀ i).val) ^ p = 1
    rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  have hpL : (p : AlgebraicClosure K) ≠ 0 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Fintype K := Fintype.ofFinite K
    haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2)
      (by rw [Fintype.card_eq_nat_card, hK, ← pow_mul])
    haveI : CharP (AlgebraicClosure K) 2 :=
      charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
    rw [Ne, CharP.cast_eq_zero_iff (AlgebraicClosure K) 2]
    intro h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2).symm
  have hJp : ⁅J, J⁆ = J := Subgroup.isPerfect_iff.1 ⟨hJ.2.2.1⟩
  have hJperf : ⁅J.map ψ', J.map ψ'⁆ = J.map ψ' := by
    rw [← Subgroup.map_commutator, hJp]
  have hCX : ∀ c ∈ fixSubgroup y, ψ' c ∈ S.Γ ⊓ Subgroup.centralizer {d} := by
    intro c hc
    refine ⟨(e (ψ c)).2, ?_⟩
    show ψ' c ∈ Subgroup.centralizer {d}
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hyd c
    rw [mem_fixSubgroup.mp hc] at h1
    exact (mul_inv_eq_iff_eq_mul.mp h1.symm).symm
  have hJX : J.map ψ' ≤ S.Γ ⊓ Subgroup.centralizer {d} := by
    rintro _ ⟨x, hx, rfl⟩
    exact hCX x (hJ.1 hx)
  have hJle := LangRat.perfect_le_iSup_rationalComponent_of_ne_G2 S (fun h => by cases h) hp hpL
    hdT hap hd1 (J.map ψ') hJX hJperf
  obtain ⟨i, hqi, hmap⟩ : ∃ i : KernelComponent (rootCharHom a₀),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a₀) i) ∧
        J.map ψ' = rationalComponent S.ρ S.Γ (rootCharHom a₀) i := by
    by_contra hcon
    push Not at hcon
    have hcomm : ∀ i : KernelComponent (rootCharHom a₀),
        CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a₀) i) →
          rationalComponent S.ρ S.Γ (rootCharHom a₀) i ≤
            Subgroup.centralizer (J.map ψ' : Set (ModGL Tag.E6 (AlgebraicClosure K))) := by
      intro i hqi
      have hS := CFSG.HardMathSupport.Dickson.Sec6.isComponentOf_rationalComponent S hdT i hqi
      obtain ⟨Q, hQ, hQmap⟩ := ggTBJ_exists_component_lift_fix ψ' hker' y d hyd hS
        (hS.1.trans (inf_le_left.trans hrange)) (hS.1.trans inf_le_right) hCX
      have hJQ : J ≠ Q := fun h => hcon i hqi (by rw [h, hQmap])
      have hc : ⁅J, Q⁆ = ⊥ :=
        (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_eq_or_commute
          (CFSG.Assembly.isComponentOf_iff_open.2 hJ)
          (CFSG.Assembly.isComponentOf_iff_open.2 hQ)).resolve_left hJQ
      rw [← hQmap, ← Subgroup.commutator_eq_bot_iff_le_centralizer, ← Subgroup.map_commutator,
        Subgroup.commutator_comm, hc, Subgroup.map_bot]
    have hab : ⁅J.map ψ', J.map ψ'⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.2
        (hJle.trans (iSup_le fun i => iSup_le fun hi => hcomm i hi))
    have hbot : J.map ψ' = ⊥ := hJperf.symm.trans hab
    have hJker : J ≤ ψ'.ker := by
      intro x hx
      have : ψ' x ∈ J.map ψ' := Subgroup.mem_map_of_mem ψ' hx
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    haveI : Nontrivial J := CFSG.ComponentClassification.Quasisimple.nontrivial hJ.2.2
    have hJcomm : ⁅J, J⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro x hx z hz
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact Subgroup.mem_center_iff.1 (hker' (hJker hz)) x
    rw [hJp] at hJcomm
    obtain ⟨x, hx⟩ := exists_ne (1 : J)
    exact hx (Subtype.ext (by
      have : (x : L') ∈ (⊥ : Subgroup L') := hJcomm ▸ x.2
      simpa using this))
  exact ⟨S, e, i, he, hρ, hdT, hqi, hmap⟩

theorem ggTBJ_twE6_class_of_setup
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ} [Fact p.Prime]
    {E : Subgroup (twistedE6RootGroup K σ)} (hn : 2 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (F : TwE6Frame K σ n p E) (hv : ExcIsLongest TwistTag.E6.tag F.v)
    {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ p = 1)
    {L' : Type} [Group L'] [Finite L'] (ψ : L' →* twistedE6RootGroup K σ)
    (hker : ψ.ker ≤ Subgroup.center L') (t₀ : Fin Tag.E6.rank → ZMod p)
    {J : Subgroup L'} (hJp : ⁅J, J⁆ = J)
    (S : LangSetup Tag.E6 (AlgebraicClosure K) p) (e : twistedE6RootGroup K σ ≃* S.Γ)
    (i : KernelComponent (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ t₀)))
    (he : ∀ x, (e x : ModGL Tag.E6 (AlgebraicClosure K)) = ggKGTwY F x)
    (hρ : ∀ α, S.ρ α = -α)
    (hmap : J.map (S.Γ.subtype.comp (e.toMonoidHom.comp ψ)) =
      rationalComponent S.ρ S.Γ (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ t₀)) i) :
    (∀ γ ∈ componentRoots (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ t₀)) i,
      ∀ r ∈ ggKGTwJ F γ, ∃ m ∈ J, ψ m = r) ∧
    ∀ (a : MulAut L') (t : Fin Tag.E6.rank → ZMod p),
      (∀ l, ggKGTwY F (ψ (a l)) =
        rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t) * ggKGTwY F (ψ l) *
          (rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t))⁻¹) →
      (∀ γ ∈ componentRoots (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ t₀)) i,
        ∑ j, (γ j : ZMod p) * t j = 0) →
      ∀ x ∈ J, a x = x := by
  classical
  let a₀ : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ := TableBExc.E6Three.zetaVec ζ hζ t₀
  let ψ' : L' →* ModGL Tag.E6 (AlgebraicClosure K) := S.Γ.subtype.comp (e.toMonoidHom.comp ψ)
  have hψ' : ∀ l, ψ' l = ggKGTwY F (ψ l) := fun l => he (ψ l)
  have hker' : ψ'.ker ≤ Subgroup.center L' := by
    intro l hl
    apply hker
    rw [MonoidHom.mem_ker] at hl ⊢
    have h1 : e (ψ l) = 1 := Subtype.ext hl
    exact e.map_eq_one_iff.mp h1
  refine ⟨fun γ hγ r hr => ?_, fun a t ha ht x hx => ?_⟩
  ·
    have hγrat : γ ∈ rationalRoots S.ρ (rootCharHom a₀) i := ⟨0, γ, hγ, rfl⟩
    have hγroot : IsRoot Tag.E6 γ := LangRat.isRoot_of_mem_rationalRoots S i hγrat
    have hq4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have hJq := ggKGTwJ_quasisimple hK hσ F hv hγroot hq4
    let φ : twistedE6RootGroup K σ →* ModGL Tag.E6 (AlgebraicClosure K) :=
      S.Γ.subtype.comp e.toMonoidHom
    have hφ : ∀ x, φ x = ggKGTwY F x := fun x => he x
    have hspan : (ggKGTwJ F γ).map φ ≤ rationalSpan S.ρ S.Γ (rootCharHom a₀) i := by
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨?_, (e x).2⟩
      have hx' := (TwE6PlusRootGen.mem_ggKGTwJ_iff hσ F).1 hx
      obtain ⟨A, hA⟩ := hx'
      rw [hφ, ← hA]
      exact LangRat.rootSL2_mem_rootSpan_of_mem_rationalRoots S i hγrat A
    have hperf : ⁅(ggKGTwJ F γ).map φ, (ggKGTwJ F γ).map φ⁆ = (ggKGTwJ F γ).map φ := by
      have hJγp : ⁅ggKGTwJ F γ, ggKGTwJ F γ⁆ = ggKGTwJ F γ :=
        Subgroup.isPerfect_iff.1 hJq.1
      rw [← Subgroup.map_commutator, hJγp]
    have hR : (ggKGTwJ F γ).map φ ≤ rationalComponent S.ρ S.Γ (rootCharHom a₀) i := by
      rw [← hperf]
      exact Subgroup.commutator_mono hspan hspan
    have hrR : φ r ∈ J.map ψ' := by
      rw [hmap]
      exact hR (Subgroup.mem_map_of_mem φ hr)
    obtain ⟨m, hmJ, hm⟩ := hrR
    exact ⟨m, hmJ, e.injective (Subtype.ext hm)⟩
  ·
    have hb : ∀ γ ∈ rationalRoots S.ρ (rootCharHom a₀) i,
        rootChar (TableBExc.E6Three.zetaVec ζ hζ t) γ = 1 := by
      rintro _ ⟨k, δ, hδ, rfl⟩
      have h0 := ht δ hδ
      apply ggTBJTwE6_rootChar_zetaVec_eq_one
      have hiter : ∀ k : ℕ, (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[k] δ = δ ∨
          (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[k] δ = -δ := by
        intro k
        induction k with
        | zero => exact Or.inl rfl
        | succ k ih =>
          rw [Function.iterate_succ_apply', hρ]
          rcases ih with h | h <;> rw [h]
          · exact Or.inr rfl
          · exact Or.inl (neg_neg δ)
      rcases hiter k with h | h <;> rw [h]
      · exact h0
      · simp only [Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib, h0, neg_zero]
    have hcent := LangRat.rationalComponent_le_centralizer S i hb
    have hw : ∀ z ∈ J, z⁻¹ * a z ∈ Subgroup.center L' := by
      intro z hz
      apply hker'
      have hzR : ψ' z ∈ rationalComponent S.ρ S.Γ (rootCharHom a₀) i := by
        rw [← hmap]
        exact Subgroup.mem_map_of_mem ψ' hz
      have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hcent hzR)
      rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one, hψ', hψ', ha, ← hψ']
      exact (mul_inv_eq_of_eq_mul h1.symm).symm
    exact CFSG.AGLEmbedding.apply_eq_of_perfect_of_mem_center a hJp hw hx

theorem ggTBJ_twE6_class_of_component
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    [Fact p.Prime] {E : Subgroup (twistedE6RootGroup K σ)} (hn : 2 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n)) (hpq : p ∣ 2 ^ n + 1)
    (F : TwE6Frame K σ n p E) (hv : ExcIsLongest TwistTag.E6.tag F.v)
    {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ p = 1)
    {L' : Type} [Group L'] [Finite L'] (ψ : L' →* twistedE6RootGroup K σ)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (t₀ : Fin Tag.E6.rank → ZMod p)
    (hd1 : rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t₀) ≠ 1) (y : MulAut L')
    (hy : ∀ l, ggKGTwY F (ψ (y l)) =
      rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t₀) * ggKGTwY F (ψ l) *
        (rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t₀))⁻¹)
    {J : Subgroup L'} (hJ : CFSG.Open.IsComponentOf J (fixSubgroup y)) :
    ∃ i : KernelComponent (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ t₀)),
      (∀ γ ∈ componentRoots (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ t₀)) i,
        ∀ r ∈ ggKGTwJ F γ, ∃ m ∈ J, ψ m = r) ∧
      ∀ (a : MulAut L') (t : Fin Tag.E6.rank → ZMod p),
        (∀ l, ggKGTwY F (ψ (a l)) =
          rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t) * ggKGTwY F (ψ l) *
            (rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t))⁻¹) →
        (∀ γ ∈ componentRoots (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ t₀)) i,
          ∑ j, (γ j : ZMod p) * t j = 0) →
        ∀ x ∈ J, a x = x := by
  classical
  obtain ⟨S, e, i, he, hρ, -, -, hmap⟩ :=
    ggTBJ_twE6_class_setup hn hK hσ hpq F hv hζ ψ hψ hker t₀ hd1 y hy hJ
  exact ⟨i, ggTBJ_twE6_class_of_setup hn hK hσ F hv hζ ψ hker t₀
    (Subgroup.isPerfect_iff.1 ⟨hJ.2.2.1⟩) S e i he hρ hmap⟩

theorem ggTBJ_twE6_class
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    [Fact p.Prime] {E : Subgroup (twistedE6RootGroup K σ)} (hn : 2 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n)) (hpq : p ∣ 2 ^ n + 1)
    (F : TwE6Frame K σ n p E) (hv : ExcIsLongest TwistTag.E6.tag F.v)
    {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ p = 1)
    {L' : Type} [Group L'] [Finite L'] (ψ : L' →* twistedE6RootGroup K σ)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (t₀ : Fin Tag.E6.rank → ZMod p)
    (hd1 : rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t₀) ≠ 1) (y : MulAut L')
    (hy : ∀ l, ggKGTwY F (ψ (y l)) =
      rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t₀) * ggKGTwY F (ψ l) *
        (rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t₀))⁻¹)
    {J : Subgroup L'} (hJ : CFSG.Open.IsComponentOf J (fixSubgroup y))
    (hJl : ∀ Q : Subgroup L', CFSG.Open.IsComponentOf Q (fixSubgroup y) → Q ≤ J) :
    ∃ i : KernelComponent (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ t₀)),
      (∀ γ ∈ componentRoots (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ t₀)) i,
        ∀ r ∈ ggKGTwJ F γ, ∃ m ∈ J, ψ m = r) ∧
      ∀ (a : MulAut L') (t : Fin Tag.E6.rank → ZMod p),
        (∀ l, ggKGTwY F (ψ (a l)) =
          rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t) * ggKGTwY F (ψ l) *
            (rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t))⁻¹) →
        (∀ γ ∈ componentRoots (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ t₀)) i,
          ∑ j, (γ j : ZMod p) * t j = 0) →
        ∀ x ∈ J, a x = x :=
  ggTBJ_twE6_class_of_component hn hK hσ hpq F hv hζ ψ hψ hker t₀ hd1 y hy hJ

end CFSG.StandardType

end
