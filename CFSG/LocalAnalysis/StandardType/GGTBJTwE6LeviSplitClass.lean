module

public import CFSG.LocalAnalysis.StandardType.GGTBJF4LeviFrame
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitTwE6SplitFrame
public import CFSG.LocalAnalysis.StandardType.GGTwE6SplitRootGenRoot
public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6SplitLang
public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6SplitFold
public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6SplitFoldFrame
public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6SplitWeyl
public import CFSG.LocalAnalysis.StandardType.GGLangRatComp
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Inner
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTamePrime

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


theorem twE6Split_classFacts
    {K : Type} [Field K] [Finite K] (σ : K →+* K) {n p : ℕ} [Fact p.Prime] [NeZero p]
    (hn : 2 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ n - 1)
    {ζ : Kˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) (hζσ : σ (ζ : K) = ζ)
    (t : Fin Tag.F4.rank → ZMod p)
    (ht : ExcFrames.twE6SplitFrameHom σ ζ hζ hζσ (Multiplicative.ofAdd t) ≠ 1)
    {Y : Subgroup ↥(graphFixedRootGroup TwistTag.E6 K σ)}
    (hY : IsComponentOf Y (Subgroup.centralizer
      ({ExcFrames.twE6SplitFrameHom σ ζ hζ hζσ (Multiplicative.ofAdd t)} :
        Set ↥(graphFixedRootGroup TwistTag.E6 K σ)))) :
    ∃ i : KernelComponent
        (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .F4 p t))),
      (∀ s : Fin Tag.F4.rank → ZMod p,
        (∀ γ ∈ componentRoots
            (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .F4 p t))) i,
          ∑ j, (γ j : ZMod p) * ExcFrames.frameCoord .F4 p s j = 0) →
        ExcFrames.twE6SplitFrameHom σ ζ hζ hζσ (Multiplicative.ofAdd s) ∈
          Subgroup.centralizer (Y : Set ↥(graphFixedRootGroup TwistTag.E6 K σ))) ∧
      (∀ (v : WeylGroup .F4) (Sd : Finset (Fin 4)), Sd ∈ f4LeviDel →
        componentRoots
            (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .F4 p t))) i =
          (fun α => v • α) '' parabolicRoots .F4 {j | j ∉ Sd} →
        ∀ c ∈ componentRoots
            (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .F4 p t))) i,
          ∃ y ∈ Y, ∀ s,
            y * ExcFrames.twE6SplitFrameHom σ ζ hζ hζσ (Multiplicative.ofAdd s) * y⁻¹ =
              ExcFrames.twE6SplitFrameHom σ ζ hζ hζσ
                (Multiplicative.ofAdd (TableBExc.torusAct .F4 p (rootReflection c) s))) := by
  classical
  have hp : p.Prime := Fact.out
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2)
    (by rw [Fintype.card_eq_nat_card, hK, ← pow_mul])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hpq : ¬ p ∣ 2 ^ n := by
    intro h
    have h1 : p ∣ 2 ^ n - 1 := hpn
    have h2 : 2 ^ n - 1 < 2 ^ n := by
      have : 0 < 2 ^ n := by positivity
      omega
    have h3 : p ∣ 2 ^ n - (2 ^ n - 1) := Nat.dvd_sub h h1
    have h4 : 2 ^ n - (2 ^ n - 1) = 1 := by
      have : 0 < 2 ^ n := by positivity
      omega
    rw [h4] at h3
    exact hp.ne_one (Nat.dvd_one.1 h3)
  let σe : K ≃+* K := RingEquiv.ofBijective σ
    ⟨σ.injective, Finite.injective_iff_surjective.1 σ.injective⟩
  obtain ⟨S, e, he, hρS, hq⟩ := exists_ggTBJTwE6SplitSetup (σ := σe) (n := n) (p := p)
    (by omega) hK (fun c => hσ c) hp (Or.inr hn) hpq
  let f : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  let e' : ↥(graphFixedRootGroup TwistTag.E6 K σ) ≃* S.Γ := e
  let ψ' : ↥(graphFixedRootGroup TwistTag.E6 K σ) →* ModGL TwistTag.E6.tag (AlgebraicClosure K) :=
    S.Γ.subtype.comp e'.toMonoidHom
  have hψ' : ∀ x, ψ' x = baseChangeGL f (x : ModGL TwistTag.E6.tag K) := fun x => he x
  have hinj : Function.Injective ψ' := fun x y h =>
    e'.injective (Subtype.ext (by simpa [ψ'] using h))
  have hrange : ψ'.range = S.Γ := by
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      exact (e' x).2
    · intro hg
      obtain ⟨r, hr⟩ := e'.surjective ⟨g, hg⟩
      exact ⟨r, by change ((e' r : S.Γ) : ModGL TwistTag.E6.tag (AlgebraicClosure K)) = g; rw [hr]⟩
  let ζL : (AlgebraicClosure K)ˣ := Units.map f.toMonoidHom ζ
  have hζL : ζL ^ p = 1 := by rw [← map_pow, hζ, map_one]
  have hιψ : ∀ s, ψ' (ExcFrames.twE6SplitFrameHom σ ζ hζ hζσ (Multiplicative.ofAdd s)) =
      ExcFrames.frameDiag (τ := TwistTag.E6.tag) ζL hζL (ExcFrames.twE6SplitTheta p s) := by
    intro s
    rw [hψ']
    exact twE6Split_baseChange_frameDiag f hζ hζL _
  let a₀ : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ :=
    TableBExc.E6Three.zetaVec ζL hζL
      (ExcFrames.frameCoord TwistTag.E6.tag p (ExcFrames.twE6SplitTheta p t))
  let g := ExcFrames.twE6SplitFrameHom σ ζ hζ hζσ (Multiplicative.ofAdd t)
  have hdψ : ψ' g = rootDiagUnit TwistTag.E6.tag a₀ := hιψ t
  have hdΓ : rootDiagUnit TwistTag.E6.tag a₀ ∈ S.Γ := by
    rw [← hdψ]
    exact (e' g).2
  have htor : rootDiagUnit TwistTag.E6.tag a₀ ∈
      torusGroup TwistTag.E6.tag (AlgebraicClosure K) := by
    have h := ExcFrames.torusCoordHom_zetaVec_E6 hζL (ExcFrames.twE6SplitTheta p t)
    have h2 := (torusCoordHom TwistTag.E6.tag (AlgebraicClosure K)
      (TableBExc.E6Three.zetaVec ζL hζL (ExcFrames.twE6SplitTheta p t))).2
    rw [h] at h2
    exact h2
  have hdT : rootDiagUnit TwistTag.E6.tag a₀ ∈ S.D.torus :=
    CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.2 ⟨htor, (S.D.mem_model.1 (S.Γ_le_model hdΓ)).2⟩
  have hap : ∀ i, a₀ i ^ p = 1 := by
    intro i
    change (ζL ^ (ExcFrames.frameCoord TwistTag.E6.tag p (ExcFrames.twE6SplitTheta p t) i).val) ^ p
      = 1
    rw [← pow_mul, mul_comm, pow_mul, hζL, one_pow]
  have hpL : (p : AlgebraicClosure K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (AlgebraicClosure K) 2]
    intro h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2).symm
  have hd1 : rootDiagUnit TwistTag.E6.tag a₀ ≠ 1 := by
    intro h
    apply ht
    apply hinj
    rw [hdψ, h, map_one]
  have hβ : ∀ c, ψ' (MulAut.conj g c) =
      rootDiagUnit TwistTag.E6.tag a₀ * ψ' c * (rootDiagUnit TwistTag.E6.tag a₀)⁻¹ := by
    intro c
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, hdψ]
  have hfix : CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj g) =
      Subgroup.centralizer {g} := by
    ext x
    rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup,
      Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
    constructor
    · intro h
      calc x * g = g * x * g⁻¹ * g := by rw [h]
        _ = g * x := inv_mul_cancel_right _ _
    · intro h
      rw [← h, mul_inv_cancel_right]
  have hY' := CFSG.Assembly.isComponentOf_iff_open.1 hY
  rw [← hfix] at hY'
  have hTame := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.langSetup_hTame_of_prime S
    hp hpL (fun h => absurd h (by decide)) hdT hap hd1
  obtain ⟨i₆, -, hmap⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.components_of_langSetup S hp ψ' hinj hrange
      (MulAut.conj g) hβ hdT hap hd1 hTame hY'
  have hsym : ∀ i, a₀ (TwistTag.E6.perm i) = a₀ i := twE6Split_zetaVec_perm hζL t
  obtain ⟨i₄, hA, hB⟩ := TwE6SplitFold.fold_class (rootCharHom a₀)
    (fun x => twE6Split_rootChar_perm hsym x) (fun m hm => twE6Split_two_torsion m hm)
    (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .F4 p t)))
    (Units.map f.toMonoidHom) (Units.map_injective f.injective)
    (fun γ => twE6Split_char_fold f hζ hζL t γ) i₆
  refine ⟨i₄, fun s hs => ?_, fun v Sd _ _ c hc => ?_⟩
  ·
    set y₀ := ExcFrames.frameCoord TwistTag.E6.tag p (ExcFrames.twE6SplitTheta p s) with hy₀
    have hy : ∀ i, y₀ (TwistTag.E6.perm i) = y₀ i := twE6Split_frameCoord_perm s
    have hb : ∀ β ∈ rationalRoots S.ρ (rootCharHom a₀) i₆,
        rootChar (TableBExc.E6Three.zetaVec ζL hζL y₀) β = 1 := by
      rintro _ ⟨k, δ, hδ, rfl⟩
      have hδr : IsRoot TwistTag.E6.tag δ := (isRootComponent_componentRoots i₆).isRoot δ hδ
      obtain ⟨γ, hγ, hγδ⟩ := hA δ hδ
      have h1 := hs γ hγ
      have h2 : ∑ j, ((TwE6SplitFold.twE6OrbSum δ j : ℤ) : ZMod p) * y₀ j = 0 := by
        rw [← hγδ]
        refine ((twE6Split_pairing_foldMap γ y₀).trans (Eq.trans ?_ h1))
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [hy₀, twE6Split_frameCoord_sum]
      have h3 := twE6Split_pairing_orbSum_eq_zero hp2 hy δ h2
      have h4 : ∀ k : ℕ, IsRoot TwistTag.E6.tag
          ((S.ρ : (Fin TwistTag.E6.tag.rank → ℤ) → _)^[k] δ) ∧
          ∑ j, ((((S.ρ : (Fin TwistTag.E6.tag.rank → ℤ) → _)^[k] δ) j : ℤ) : ZMod p) * y₀ j =
            ∑ j, ((δ j : ℤ) : ZMod p) * y₀ j := by
        intro k
        induction k with
        | zero => exact ⟨hδr, rfl⟩
        | succ k ih =>
          rw [Function.iterate_succ_apply']
          refine ⟨(S.frob.isRoot_iff _).2 ih.1, ?_⟩
          rw [hρS _ ih.1]
          have h5 := twE6Split_pairing_permPow hy 1
            ((S.ρ : (Fin TwistTag.E6.tag.rank → ℤ) → _)^[k] δ)
          rw [pow_one] at h5
          rw [h5, ih.2]
      rw [NoOffE8Five.rootChar_zetaVec hζL, (h4 k).2, h3, ofAdd_zero, map_one]
    have hcent := LangRat.rationalComponent_le_centralizer S i₆ hb
    refine Subgroup.mem_centralizer_iff.2 fun z hz => ?_
    have hzR : ψ' z ∈ rationalComponent S.ρ S.Γ (rootCharHom a₀) i₆ := by
      rw [← hmap]
      exact Subgroup.mem_map_of_mem ψ' hz
    apply hinj
    rw [map_mul, map_mul, hιψ s]
    exact Subgroup.mem_centralizer_singleton_iff.1 (hcent hzR)
  ·
    obtain ⟨δ, hδ, hθ⟩ := hB c hc
    have hδr : IsRoot TwistTag.E6.tag δ := (isRootComponent_componentRoots i₆).isRoot δ hδ
    have hcr : IsRoot Tag.F4 c := (isRootComponent_componentRoots _).isRoot c hc
    have hmem := twE6SplitWeyl_mem_rationalComponent S (k' := K) hn hq hρS i₆ ⟨0, δ, hδ, rfl⟩
    rw [← hmap] at hmem
    obtain ⟨y, hyY, hy⟩ := hmem
    refine ⟨y, hyY, fun s => ?_⟩
    apply hinj
    rw [map_mul, map_mul, map_inv, hy, hιψ, hιψ]
    exact twE6SplitWeyl_conj_frameDiag hζL hδr hcr hθ s

end CFSG.StandardType

end
