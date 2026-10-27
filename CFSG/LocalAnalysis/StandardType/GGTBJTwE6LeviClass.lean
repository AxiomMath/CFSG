module

public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6Class
public import CFSG.LocalAnalysis.StandardType.GGLangRatCompC
public import CFSG.LocalAnalysis.StandardType.GGRealKGCoverComp

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement


theorem ggTBJ_twE6_classComp
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    [Fact p.Prime] {E : Subgroup (twistedE6RootGroup K σ)} (hn : 2 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n)) (hpq : p ∣ 2 ^ n + 1)
    (F : TwE6Frame K σ n p E) (hv : ExcIsLongest TwistTag.E6.tag F.v)
    {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ p = 1)
    (t₀ : Fin Tag.E6.rank → ZMod p)
    (hd1 : rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t₀) ≠ 1)
    {a : twistedE6RootGroup K σ}
    (ha : ggKGTwY F a = rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t₀))
    {Y : Subgroup (twistedE6RootGroup K σ)}
    (hY : CFSG.Open.IsComponentOf Y (Subgroup.centralizer {a})) :
    ∃ i : KernelComponent (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ t₀)),
      (∀ γ ∈ componentRoots (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ t₀)) i,
        ggKGTwJ F γ ≤ Y) ∧
      ∀ (x : twistedE6RootGroup K σ) (t : Fin Tag.E6.rank → ZMod p),
        ggKGTwY F x = rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t) →
        (∀ γ ∈ componentRoots (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ t₀)) i,
          ∑ j, (γ j : ZMod p) * t j = 0) →
        x ∈ Subgroup.centralizer (Y : Set (twistedE6RootGroup K σ)) := by
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
  let ψ' : twistedE6RootGroup K σ →* ModGL Tag.E6 (AlgebraicClosure K) :=
    S.Γ.subtype.comp e.toMonoidHom
  have hψ' : ∀ l, ψ' l = ggKGTwY F l := fun l => he l
  have hinj : Function.Injective ψ' := fun x y h =>
    e.injective (Subtype.ext (by simpa [ψ'] using h))
  have hrange : ψ'.range = S.Γ := by
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      exact (e x).2
    · intro hg
      obtain ⟨r, hr⟩ := e.surjective ⟨g, hg⟩
      exact ⟨r, by change ((e r : S.Γ) : ModGL Tag.E6 (AlgebraicClosure K)) = g; rw [hr]⟩
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
  have hβ : ∀ c, ψ' (MulAut.conj a c) = d * ψ' c * d⁻¹ := by
    intro c
    have h1 : ψ' (MulAut.conj a c) = ψ' a * ψ' c * (ψ' a)⁻¹ := by
      rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
    have h2 : ψ' a = d := (hψ' a).trans ha
    rw [h1, h2]
  have hfix : fixSubgroup (MulAut.conj a) = Subgroup.centralizer {a} := by
    ext x
    rw [mem_fixSubgroup, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
    constructor
    · intro h
      calc x * a = a * x * a⁻¹ * a := by rw [h]
        _ = a * x := inv_mul_cancel_right _ _
    · intro h
      rw [← h, mul_inv_cancel_right]
  have hTame := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.langSetup_hTame_of_prime S
    hp hpL (fun h => absurd h (by decide)) hdT hap hd1
  obtain ⟨i, -, hmap⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.components_of_langSetup
    S hp ψ' hinj hrange (MulAut.conj a) hβ hdT hap hd1 hTame (hfix ▸ hY)
  refine ⟨i, fun γ hγ r hr => ?_, fun x t hx ht y hy => ?_⟩
  ·
    have hγrat : γ ∈ rationalRoots S.ρ (rootCharHom a₀) i := ⟨0, γ, hγ, rfl⟩
    have hγroot : IsRoot Tag.E6 γ := LangRat.isRoot_of_mem_rationalRoots S i hγrat
    have hq4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have hJq := ggKGTwJ_quasisimple hK hσ F hv hγroot hq4
    have hspan : (ggKGTwJ F γ).map ψ' ≤ rationalSpan S.ρ S.Γ (rootCharHom a₀) i := by
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨?_, (e x).2⟩
      have hx' := (TwE6PlusRootGen.mem_ggKGTwJ_iff hσ F).1 hx
      obtain ⟨A, hA⟩ := hx'
      rw [hψ', ← hA]
      exact LangRat.rootSL2_mem_rootSpan_of_mem_rationalRoots S i hγrat A
    have hperf : ⁅(ggKGTwJ F γ).map ψ', (ggKGTwJ F γ).map ψ'⁆ = (ggKGTwJ F γ).map ψ' := by
      have hJγp : ⁅ggKGTwJ F γ, ggKGTwJ F γ⁆ = ggKGTwJ F γ :=
        Subgroup.isPerfect_iff.1 hJq.1
      rw [← Subgroup.map_commutator, hJγp]
    have hR : (ggKGTwJ F γ).map ψ' ≤ rationalComponent S.ρ S.Γ (rootCharHom a₀) i := by
      rw [← hperf]
      exact Subgroup.commutator_mono hspan hspan
    have hrR : ψ' r ∈ Y.map ψ' := by
      rw [hmap]
      exact hR (Subgroup.mem_map_of_mem ψ' hr)
    obtain ⟨m, hmY, hm⟩ := hrR
    rw [← hinj hm]
    exact hmY
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
    have hyR : ψ' y ∈ rationalComponent S.ρ S.Γ (rootCharHom a₀) i := by
      rw [← hmap]
      exact Subgroup.mem_map_of_mem ψ' hy
    have hxψ : ψ' x = rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t) := by
      rw [hψ', hx]
    have h1 : ψ' y * ψ' x = ψ' x * ψ' y := by
      rw [hxψ]
      exact Subgroup.mem_centralizer_singleton_iff.1 (hcent hyR)
    apply hinj
    rw [map_mul, map_mul]
    exact h1


theorem ggTBJ_twE6_class_of_central_cover
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ} [Fact p.Prime]
    {E : Subgroup (twistedE6RootGroup K σ)} (hn : 2 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n)) (hpq : p ∣ 2 ^ n + 1)
    (F : TwE6Frame K σ n p E) (hv : ExcIsLongest TwistTag.E6.tag F.v)
    {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ p = 1)
    {X : Type} [Group X] [Finite X] (ψ : X →* twistedE6RootGroup K σ)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center X)
    (hkerp : ∀ z ∈ ψ.ker, z ^ p = 1 → z = 1)
    (t₀ : Fin Tag.E6.rank → ZMod p)
    (hd1 : rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t₀) ≠ 1)
    {a : X} (hap : a ^ p = 1)
    (ha : ggKGTwY F (ψ a) =
      rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t₀))
    {J : Subgroup X} (hJ : CFSG.Open.IsComponentOf J (Subgroup.centralizer {a})) :
    ∃ i : KernelComponent (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ t₀)),
      (∀ γ ∈ componentRoots (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ t₀)) i,
        ∀ r ∈ ggKGTwJ F γ, ∃ m ∈ J, ψ m = r) ∧
      ∀ (b : X) (t : Fin Tag.E6.rank → ZMod p),
        ggKGTwY F (ψ b) = rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t) →
        (∀ γ ∈ componentRoots (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ t₀)) i,
          ∑ j, (γ j : ZMod p) * t j = 0) →
        ∀ x ∈ J, b * x = x * b := by
  have hJa : CFSG.Assembly.IsComponentOf J (Subgroup.centralizer {a}) :=
    CFSG.Assembly.isComponentOf_iff_open.mpr hJ
  have hmap := RealKGCover.isComponentOf_map_centralizer hψ hker hkerp
    (X := ({a} : Set X)) (by rintro x rfl; exact hap) hJa
  have hmap' : CFSG.Open.IsComponentOf (J.map ψ) (Subgroup.centralizer {ψ a}) :=
    CFSG.Assembly.isComponentOf_iff_open.mp (by
      simpa only [Set.image_singleton] using hmap)
  obtain ⟨i, hLow, hCENT⟩ := ggTBJ_twE6_classComp hn hK hσ hpq F hv hζ t₀ hd1 ha hmap'
  have hJp : ⁅J, J⁆ = J := Subgroup.isPerfect_iff.1 ⟨hJ.2.2.1⟩
  refine ⟨i, ?_, ?_⟩
  · intro γ hγ r hr
    exact Subgroup.mem_map.mp (hLow γ hγ hr)
  · intro b t hb ht x hx
    have hdelta : ∀ z ∈ J, z⁻¹ * MulAut.conj b z ∈ Subgroup.center X := by
      intro z hz
      apply hker
      rw [MonoidHom.mem_ker, MulAut.conj_apply, map_mul, map_mul, map_mul, map_inv, map_inv]
      have hc : ψ z * ψ b = ψ b * ψ z :=
        Subgroup.mem_centralizer_iff.mp (hCENT (ψ b) t hb ht) (ψ z)
          (Subgroup.mem_map_of_mem ψ hz)
      rw [← hc]
      group
    have hfix := CFSG.AGLEmbedding.apply_eq_of_perfect_of_mem_center (MulAut.conj b) hJp hdelta hx
    change b * x * b⁻¹ = x at hfix
    exact mul_inv_eq_iff_eq_mul.mp hfix

end CFSG.StandardType

end
