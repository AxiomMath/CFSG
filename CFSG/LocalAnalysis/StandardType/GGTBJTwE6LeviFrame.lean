module

public import CFSG.LocalAnalysis.StandardType.GGTBJE6LeviFrame
public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6LeviClass
public import CFSG.LocalAnalysis.StandardType.GGTBE6IndTwistAlign
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwE6Sylow
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTorus
public import CFSG.HardMathSupport.Timmesfeld.Torality.Conjugacy
public import CFSG.RankThree.PartOne.TCX.Tri.TorusCentral
public import CFSG.LieType.Chevalley.CLSOddE7RationalDerivedIndex

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.CentralCover
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups

theorem exists_weyl_of_two_frames
    {τ : Tag} {p : ℕ} [Fact p.Prime] [NeZero p] {K : Type} [Field K] {H : Subgroup (ModGL τ K)}
    {ζ : (AlgebraicClosure K)ˣ} {hζ : ζ ^ p = 1} (hζo : orderOf ζ = p)
    (hdet : IsUnit ((τ.symmetrizedCartan.det : ℤ) : ZMod p))
    {g₁ g₂ : ModGL τ (AlgebraicClosure K)}
    (hg₁ : g₁ ∈ adjointGroup τ (AlgebraicClosure K))
    (hg₂ : g₂ ∈ adjointGroup τ (AlgebraicClosure K))
    {ι₁ ι₂ : Multiplicative (Fin τ.rank → ZMod p) →* ↥H} (hrange : ι₂.range ≤ ι₁.range)
    (hb₁ : ∀ s : Fin τ.rank → ZMod p,
      baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((ι₁ (Multiplicative.ofAdd s) : H) : ModGL τ K) =
        g₁ * ExcFrames.frameDiag ζ hζ s * g₁⁻¹)
    (hb₂ : ∀ s : Fin τ.rank → ZMod p,
      baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((ι₂ (Multiplicative.ofAdd s) : H) : ModGL τ K) =
        g₂ * ExcFrames.frameDiag ζ hζ s * g₂⁻¹) :
    ∃ u : WeylGroup τ, ∀ s : Fin τ.rank → ZMod p,
      ι₂ (Multiplicative.ofAdd s) = ι₁ (Multiplicative.ofAdd (TableBExc.torusAct τ p u s)) := by
  classical
  set bc := baseChangeGL (τ := τ) (algebraMap K (AlgebraicClosure K)) with hbc
  have hσex : ∀ s : Fin τ.rank → ZMod p, ∃ t : Fin τ.rank → ZMod p,
      ι₁ (Multiplicative.ofAdd t) = ι₂ (Multiplicative.ofAdd s) := by
    intro s
    obtain ⟨x, hx⟩ := hrange ⟨Multiplicative.ofAdd s, rfl⟩
    exact ⟨Multiplicative.toAdd x, by rw [ofAdd_toAdd]; exact hx⟩
  choose σ' hσ' using hσex
  set h : ModGL τ (AlgebraicClosure K) := g₁⁻¹ * g₂ with hh
  have hhC : h ∈ adjointGroup τ (AlgebraicClosure K) :=
    mul_mem (inv_mem hg₁) hg₂
  have hconj : ∀ s : Fin τ.rank → ZMod p,
      h * ExcFrames.frameDiag ζ hζ s * h⁻¹ = ExcFrames.frameDiag ζ hζ (σ' s) := by
    intro s
    have h1 : bc ((ι₁ (Multiplicative.ofAdd (σ' s)) : H) : ModGL τ K) =
        bc ((ι₂ (Multiplicative.ofAdd s) : H) : ModGL τ K) := by rw [hσ' s]
    rw [hb₁, hb₂] at h1
    have h2 : ExcFrames.frameDiag ζ hζ (σ' s) =
        g₁⁻¹ * (g₂ * ExcFrames.frameDiag ζ hζ s * g₂⁻¹) * g₁ := by
      rw [← h1]
      group
    rw [h2, hh]
    group
  obtain ⟨u, hu⟩ := CFSG.HardMathSupport.Timmesfeld.Torality.exists_weyl_of_conj_family τ
    (AlgebraicClosure K)
    (fun s => TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord τ p (σ' s)))
    (fun s => TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord τ p s)) hhC hconj
  refine ⟨u, fun s => ?_⟩
  have h3 : ExcFrames.frameDiag ζ hζ (σ' s) =
      ExcFrames.frameDiag ζ hζ (TableBExc.torusAct τ p u s) := by
    rw [← ExcFrames.canonicalRep_conj_frameDiag]
    exact hu s
  rw [← hσ' s, ExcFrames.frameDiag_injective hζo hζ hdet h3]

theorem baseChangeGL_chevTorus_E6
    {K : Type} [Field K] {p : ℕ} [NeZero p] (ζ : Kˣ) (hζ : ζ ^ p = 1)
    (hζ' : (Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom ζ) ^ p = 1)
    (a : Multiplicative (Fin Tag.E6.rank → ZMod p)) :
    baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((chevTorus .E6 ζ hζ a : adjointGroup .E6 K) : ModGL .E6 K) =
      ExcFrames.frameDiag (τ := Tag.E6)
        (Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom ζ) hζ'
        (Multiplicative.toAdd a) := by
  have h1 : ((chevTorus .E6 ζ hζ a : adjointGroup .E6 K) : ModGL .E6 K) =
      rootDiagUnit .E6 (CFSG.Timmesfeld.ExceptionalOrders.zpowMatrix (G := Kˣ) Tag.E6.cartan
        (chevTorusExp .E6 ζ hζ a)) := by
    have h := CFSG.RankThree.PartOne.TCX.Tri.torusCoordHom_eq_rootDiagUnit (τ := Tag.E6) (K := K)
      (chevTorusExp Tag.E6 ζ hζ a)
    rw [coe_torusCoordHom] at h
    rw [coe_chevTorus]
    exact h
  rw [h1, baseChangeGL_rootDiagUnit]
  unfold ExcFrames.frameDiag
  congr 1
  funext j
  have hC : Tag.E6.cartan = CartanMatrix.E 6 := cartanE_eq 6
  have hCsymm : ∀ i j, Tag.E6.cartan i j = Tag.E6.cartan j i := fun i j => by
    rw [hC]
    exact (CartanMatrix.E_isSymm 6).apply j i
  have hS : Tag.E6.symmetrizedCartan = Tag.E6.cartan :=
    CFSG.RankThree.E6.symmetrizedCartan_E6
  have hmap : ∀ x : Multiplicative (ZMod p),
      Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom (zmodPowHom ζ hζ x) =
        zmodPowHom (Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom ζ) hζ' x := by
    intro x
    simp only [zmodPowHom, MonoidHom.coe_mk, OneHom.coe_mk, map_pow]
  have hsum : ∑ i, (Tag.E6.cartan i j) • Multiplicative.toAdd a i =
      ExcFrames.frameCoord Tag.E6 p (Multiplicative.toAdd a) j := by
    unfold ExcFrames.frameCoord
    rw [hS]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [zsmul_eq_mul, hCsymm i j]
  have key : ∀ (A : Fin Tag.E6.rank → ZMod p) (c : Fin Tag.E6.rank → ℤ),
      ∏ i, (Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom
          (zmodPowHom ζ hζ (Multiplicative.ofAdd (A i)))) ^ c i =
        zmodPowHom (Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom ζ) hζ'
          (Multiplicative.ofAdd (∑ i, c i • A i)) := by
    intro A c
    simp_rw [hmap]
    rw [ofAdd_sum, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [ofAdd_zsmul, map_zpow]
  have hz : TableBExc.E6Three.zetaVec
      (Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom ζ) hζ'
      (ExcFrames.frameCoord Tag.E6 p (Multiplicative.toAdd a)) j =
      zmodPowHom (Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom ζ) hζ'
        (Multiplicative.ofAdd (ExcFrames.frameCoord Tag.E6 p (Multiplicative.toAdd a) j)) := rfl
  rw [hz, ← hsum, ← key (fun i => Multiplicative.toAdd a i) (fun i => Tag.E6.cartan i j)]
  change Units.map _ (∏ i, (chevTorusExp Tag.E6 ζ hζ a i) ^ (Tag.E6.cartan i j)) = _
  rw [map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_zpow]
  rfl

open CFSG.LieType.Steinberg.TwistedE6 in
theorem exists_scalarWitness_of_conj
    {K : Type} [Field K] [Finite K] [CharP K 2] (θ : K ≃+* K)
    (hθ : ∀ c, θ.toRingHom (θ.toRingHom c) = c) (l : K) (hl : θ.toRingHom l = l + 1)
    {f m p : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (hθq : ∀ c, θ.toRingHom c = c ^ (2 ^ f)) (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    [NeZero p] (ζ : CFSG.LieType.Steinberg.normOne θ) (hζ : ζ ^ p = 1)
    (hζo : orderOf (ζ : Kˣ) = p)
    (e : CFSG.LieType.Steinberg.normOne θ ≃* Multiplicative (ZMod m))
    (c₃ : ↥(graphFixedRootGroup TwistTag.E6 K θ.toRingHom))
    (ι₁ : Multiplicative (Fin Tag.E6.rank → ZMod p) →*
      ↥(graphFixedRootGroup TwistTag.E6 K θ.toRingHom))
    (hc₃ : ∀ s, c₃ * (CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf hK θ.toRingHom hθq
        (TBE6IndTwist.langPFrame K θ hθ l hl ζ hζ s)) * c₃⁻¹ = ι₁ s)
    (A : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 K θ.toRingHom)))
    (hA : ι₁.range.map (MulAut.conj :
      ↥(graphFixedRootGroup TwistTag.E6 K θ.toRingHom) →*
        MulAut ↥(graphFixedRootGroup TwistTag.E6 K θ.toRingHom)) = A) :
    ∃ wt : GGTorusTorWit m 6 ↥(graphFixedRootGroup TwistTag.E6 K θ.toRingHom) A,
      wt.Holds CartanMatrix.E₆ CoxeterMatrix.E₆ ∧
      ∀ (k : Fin Tag.E6.rank) (s : Fin Tag.E6.rank → ZMod p),
        wt.n k * ι₁ (Multiplicative.ofAdd s) * (wt.n k)⁻¹ =
          ι₁ (Multiplicative.ofAdd (TableBExc.torusAct Tag.E6 p (simple Tag.E6 k) s)) := by
  classical
  let q := CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf hK θ.toRingHom hθq
  have hqs : Function.Surjective q :=
    CFSG.SeitzReduction.F4Pilot.twistedIsogenyC_surjective hf hK θ.toRingHom hθq
  have hqc : q.ker ≤ Subgroup.center (fixedGroup K θ.toRingHom) :=
    (CFSG.SeitzReduction.F4Pilot.ker_twistedIsogenyC hf hK θ.toRingHom hθq).le
  let φ : fixedGroup K θ.toRingHom →* ↥(graphFixedRootGroup TwistTag.E6 K θ.toRingHom) :=
    (MulAut.conj c₃).toMonoidHom.comp q
  let ψ : ↥(graphFixedRootGroup TwistTag.E6 K θ.toRingHom) →*
      ↥(graphFixedRootGroup TwistTag.E6 K θ.toRingHom) := (MulAut.conj c₃⁻¹).toMonoidHom
  have hψ : Function.Surjective ψ := (MulAut.conj c₃⁻¹).surjective
  have hker : ψ.ker ≤ Subgroup.center ↥(graphFixedRootGroup TwistTag.E6 K θ.toRingHom) := by
    intro x hx
    have hx1 : ψ x = 1 := hx
    have : x = 1 := (MulAut.conj c₃⁻¹).injective (hx1.trans (map_one (MulAut.conj c₃⁻¹)).symm)
    rw [this]
    exact Subgroup.one_mem _
  have hφ : ∀ x, ψ (φ x) = q x := by
    intro x
    change (MulAut.conj c₃⁻¹) ((MulAut.conj c₃) (q x)) = q x
    simp only [MulAut.conj_apply]
    group
  have hφs : Function.Surjective φ := (MulAut.conj c₃).surjective.comp hqs
  have hφc : φ.ker ≤ Subgroup.center (fixedGroup K θ.toRingHom) := by
    intro x hx
    apply hqc
    rw [MonoidHom.mem_ker] at hx ⊢
    have hx1 : (MulAut.conj c₃) (q x) = 1 := hx
    exact (MulAut.conj c₃).injective (hx1.trans (map_one (MulAut.conj c₃)).symm)
  obtain ⟨δ, hδ⟩ := TBE6IndTwist.exists_diagonal_descent hK θ hθq hθ l hl φ hφs hφc
  have hφf : φ.comp (TBE6IndTwist.langPFrame K θ hθ l hl ζ hζ) = ι₁ := by
    apply MonoidHom.ext
    intro s
    rw [← hc₃ s]
    rfl
  have hA' : ((φ.comp (TBE6IndTwist.langPFrame K θ hθ l hl ζ hζ)).range).map
      (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 K θ.toRingHom) →* _) = A := by
    rw [hφf]
    exact hA
  have hδi := TBE6IndTwist.scalar_descent_injective θ hθ l hl φ δ hK hθq hf ψ hφ hδ
  have hAD : A ≤ δ.range := by
    rw [← hA']
    exact (Subgroup.map_mono (TBE6IndTwist.scalar_frame_le_torus θ hθ l hl φ ζ hζ)).trans
      (TBE6IndTwist.scalar_inner_torus_le θ hθ l hl φ δ hK hφs hδ e)
  have hroot := TBE6IndTwist.scalarRoot_nontrivial_on_frame θ hθ l hl φ δ hK hθq hp hp3
    hφs hφc hδi hδ ζ hζ hζo e A hA'
  obtain ⟨hn, hfour⟩ := TBE6IndTwist.scalar_holdsFour θ hθ l hl φ δ hf hK hθq hp hp2 hp3
    ψ hψ hker hφ hφs hφc ζ hζ hζo e A hA'
  refine ⟨TBE6IndTwist.scalarWitness θ hθ l hl φ δ e A hn, ggTDHolds_of_parts
    (TBE6IndTwist.scalar_holdsOne θ hθ l hl φ δ hf hK hθq ψ hφ hφs hδi hδ e A hAD hn)
    (TBE6IndTwist.scalar_holdsTwo θ hθ l hl φ δ hK hδi hδ e A hroot hn)
    (TBE6IndTwist.scalar_holdsThree θ hθ l hl φ δ hf hK hθq hp hp2 hp3 hφs hφc hδ e ζ hζ hζo A
      hAD hA' hn)
    hfour, fun k s => ?_⟩
  rw [TBE6IndTwist.scalarWitness_n]
  have h1 := TBE6IndTwist.langWeylHom_conj_langPFrame K θ hθ l hl ζ hζ
    (simple Tag.E6 k) s
  have h2 := congrArg φ h1
  rw [map_mul, map_mul, map_inv] at h2
  have h3 : φ (TBE6IndTwist.langPFrame K θ hθ l hl ζ hζ (Multiplicative.ofAdd s)) =
      ι₁ (Multiplicative.ofAdd s) := by
    rw [← hφf]
    rfl
  have h4 : φ (TBE6IndTwist.langPFrame K θ hθ l hl ζ hζ
      (Multiplicative.ofAdd (TableBExc.torusAct Tag.E6 p (simple Tag.E6 k) s))) =
      ι₁ (Multiplicative.ofAdd (TableBExc.torusAct Tag.E6 p (simple Tag.E6 k) s)) := by
    rw [← hφf]
    rfl
  rw [h3, h4] at h2
  exact h2

theorem twE6_frame_class
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ} [Fact p.Prime] [NeZero p]
    {E : Subgroup (twistedE6RootGroup K σ)} (hn : 2 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hσ : ∀ c, σ c = c ^ (2 ^ n)) (hpq : p ∣ 2 ^ n + 1)
    (F : TwE6Frame K σ n p E) (hv : ExcIsLongest TwistTag.E6.tag F.v)
    {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ p = 1)
    {T : Multiplicative (Fin Tag.E6.rank → ZMod p) →* twistedE6RootGroup K σ}
    (hT : ∀ t : Fin Tag.E6.rank → ZMod p, ggKGTwY F (T (Multiplicative.ofAdd t)) =
      rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t))
    (t : Fin Tag.E6.rank → ZMod p)
    (ht : T (Multiplicative.ofAdd (ExcFrames.frameCoord Tag.E6 p t)) ≠ 1)
    {Y : Subgroup (twistedE6RootGroup K σ)}
    (hY : IsComponentOf Y (Subgroup.centralizer
      ({T (Multiplicative.ofAdd (ExcFrames.frameCoord Tag.E6 p t))} :
        Set (twistedE6RootGroup K σ)))) :
    ∃ i : KernelComponent
        (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord Tag.E6 p t))),
      (∀ s : Fin Tag.E6.rank → ZMod p,
        (∀ γ ∈ componentRoots
            (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord Tag.E6 p t))) i,
          ∑ j, (γ j : ZMod p) * ExcFrames.frameCoord Tag.E6 p s j = 0) →
        T (Multiplicative.ofAdd (ExcFrames.frameCoord Tag.E6 p s)) ∈
          Subgroup.centralizer (Y : Set (twistedE6RootGroup K σ))) ∧
      (∀ c ∈ componentRoots
          (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord Tag.E6 p t))) i,
        ∃ y ∈ Y, ∀ s : Fin Tag.E6.rank → ZMod p,
          y * T (Multiplicative.ofAdd (ExcFrames.frameCoord Tag.E6 p s)) * y⁻¹ =
            T (Multiplicative.ofAdd (ExcFrames.frameCoord Tag.E6 p
              (TableBExc.torusAct Tag.E6 p (rootReflection c) s)))) := by
  classical
  have hd1 : rootDiagUnit TwistTag.E6.tag
      (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord Tag.E6 p t)) ≠ 1 := by
    intro h
    apply ht
    apply ggKGTl_conj_injective F
    change ggKGTwY F (T (Multiplicative.ofAdd (ExcFrames.frameCoord Tag.E6 p t))) =
      ggKGTwY F 1
    rw [hT, h, map_one]
  obtain ⟨i, hlow, hker⟩ := ggTBJ_twE6_classComp hn hK hσ hpq F hv hζ
    (ExcFrames.frameCoord Tag.E6 p t) hd1 (hT _) (CFSG.Assembly.isComponentOf_iff_open.1 hY)
  refine ⟨i, fun s hs => hker _ _ (hT _) hs, fun c hc => ?_⟩
  obtain ⟨r, hrJ, hr⟩ := ggKGTwJ_weyl hK hσ F hv (isRoot_of_mem_componentRoots hc)
  refine ⟨r, hlow c hc hrJ, fun s => ?_⟩
  rw [TwE6PlusRootGen.conj_twE6PlusTorus F hζ hT hr (ExcFrames.frameCoord Tag.E6 p s)]
  exact congrArg (fun x => T (Multiplicative.ofAdd x))
    (ExcFrames.adAct_frameCoord (τ := Tag.E6) (p := p) (rootReflection c) s)

theorem ggTwE6_leviFrame
    {K : Type} [Field K] [Finite K] {n p : ℕ} [Fact p.Prime] (hn : 2 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n + 1)
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (E : Subgroup (twistedE6RootGroup K σ)) (hE : IsElemAbelian p E) (h5E : p ^ 5 ≤ Nat.card E)
    (hsc : ∀ g : twistedE6RootGroup K σ, (∀ b ∈ E, g * b = b * g) → g ^ p = 1 → g ∈ E) :
    GGE6LeviFrame (R := ↥(twistedE6RootGroup K σ)) p E := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hf1 : 1 ≤ n := by omega
  have h3E : p ^ 3 ≤ Nat.card E := le_trans (Nat.pow_le_pow_right hp.pos (by norm_num)) h5E
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2)
    (by rw [Fintype.card_eq_nat_card, hK, ← pow_mul])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  haveI : IsAlgClosed (AlgebraicClosure K) := inferInstance
  obtain ⟨θ, hθq, hθo, -⟩ := finite_graph_field_parameter_fields TwistTag.E6 Nat.prime_two hf1 K hK
  have hθσ : θ = σ := RingEquiv.ext fun c => (hθq c).trans (hσ c).symm
  subst hθσ
  have hθ : ∀ c, θ.toRingHom (θ.toRingHom c) = c :=
    CFSG.SeitzReduction.F4Pilot.involutive_of_natCard_eq hK (fun c => hθq c)
  have hθ1 : θ ≠ 1 := by
    change orderOf θ = 2 at hθo
    intro h
    rw [h, orderOf_one] at hθo
    omega
  have hθ2 : θ * θ = 1 := by
    change orderOf θ = 2 at hθo
    simpa only [hθo, pow_two] using pow_orderOf_eq_one θ
  obtain ⟨l, hl⟩ := CFSG.SeitzReduction.LinearPilot.exists_trace_one_of_involution hθ1 hθ2
  obtain ⟨ζS, hζSo⟩ := TBE6IndTwist.exists_normOne_prime K θ hf1 hK (fun c => hθq c) hp hpq
  have hζS : ζS ^ p = 1 := by
    apply Subtype.ext
    change (ζS : Kˣ) ^ p = 1
    rw [← hζSo, pow_orderOf_eq_one]
  let e : CFSG.LieType.Steinberg.normOne θ ≃* Multiplicative (ZMod (2 ^ n + 1)) := by
    have he : CFSG.LieType.Steinberg.normOne θ ≃*
        Multiplicative (ZMod (Nat.card (CFSG.LieType.Steinberg.normOne θ))) :=
      (zmodCyclicMulEquiv inferInstance).symm
    rwa [TBE6IndTwist.card_normOne K θ hK (fun c => hθq c)] at he
  obtain ⟨F, -, hv⟩ := ExcTwE6Nons.twE6SCTorusInput_nonsplit θ hp hp5 hK hσ hpq E hE h3E h5E hsc
  have hv' : ExcIsLongest TwistTag.E6.tag F.v := hv hpq
  set ζb : (AlgebraicClosure K)ˣ :=
    Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom (ζS : Kˣ) with hζbdef
  have hmapinj : Function.Injective
      (Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom) := fun a b h =>
    Units.ext ((algebraMap K (AlgebraicClosure K)).injective
      (congrArg (fun u : (AlgebraicClosure K)ˣ => (u : AlgebraicClosure K)) h))
  have hζbo : orderOf ζb = p := by
    rw [hζbdef, orderOf_injective _ hmapinj, hζSo]
  have hζb : ζb ^ p = 1 := by
    rw [← hζbo]
    exact pow_orderOf_eq_one _
  obtain ⟨T, hTinj, hTE, hT⟩ := TwE6PlusRootGen.exists_twE6PlusTorus hK hσ hp5 hpq F hv' hζbo hζb
  have hdet : IsUnit ((Tag.E6.symmetrizedCartan.det : ℤ) : ZMod p) := by
    rw [CFSG.RankThree.E6.symmetrizedCartan_E6]
    exact TableBExc.isUnit_det_cartan_of_eq hp det_cartan_E6
      ((Nat.coprime_primes Nat.prime_three hp).mpr (Ne.symm hp3))
  let fc : Multiplicative (Fin Tag.E6.rank → ZMod p) →*
      Multiplicative (Fin Tag.E6.rank → ZMod p) :=
    { toFun := fun s => Multiplicative.ofAdd
        (ExcFrames.frameCoord Tag.E6 p (Multiplicative.toAdd s))
      map_one' := by
        rw [toAdd_one, ExcFrames.frameCoord_zero]
        rfl
      map_mul' := fun s t => by
        rw [toAdd_mul, ExcFrames.frameCoord_add]
        rfl }
  have hfcinj : Function.Injective fc := fun s t h =>
    Multiplicative.toAdd.injective
      (ExcFrames.frameCoord_injective hdet (Multiplicative.ofAdd.injective h))
  have hfcsurj : Function.Surjective fc := Finite.injective_iff_surjective.mp hfcinj
  let ι₁ : Multiplicative (Fin Tag.E6.rank → ZMod p) →* ↥(twistedE6RootGroup K θ) := T.comp fc
  have hι₁inj : Function.Injective ι₁ := hTinj.comp hfcinj
  have hι₁range : ι₁.range = E := by
    rw [← hTE]
    ext x
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨fc s, rfl⟩
    · rintro ⟨s, rfl⟩
      obtain ⟨s', rfl⟩ := hfcsurj s
      exact ⟨s', rfl⟩
  let q := CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf1 hK θ.toRingHom (fun c => hθq c)
  let ρ : Multiplicative (Fin Tag.E6.rank → ZMod p) →* ↥(twistedE6RootGroup K θ) :=
    q.comp (TBE6IndTwist.langPFrame K θ hθ l hl ζS hζS)
  obtain ⟨c, hc⟩ := TBE6IndTwist.exists_graph_frame_conj_of_selfCent K θ hθ l hl hf1 hK
    (fun c => hθq c) hp hp5 hpq ζS hζS hζSo E hE hsc
  let ι₂ : Multiplicative (Fin Tag.E6.rank → ZMod p) →* ↥(twistedE6RootGroup K θ) :=
    (MulAut.conj c⁻¹).toMonoidHom.comp ρ
  have hι₂range : ι₂.range = E := by
    have h1 : ι₂.range = (ρ.range).map (MulAut.conj c⁻¹).toMonoidHom := by
      rw [MonoidHom.range_comp]
    rw [h1, ← hc, Subgroup.map_map]
    have he : (MulAut.conj c⁻¹).toMonoidHom.comp (MulAut.conj c).toMonoidHom = MonoidHom.id _ := by
      apply MonoidHom.ext
      intro x
      change c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x
      group
    rw [he, Subgroup.map_id]
  obtain ⟨g0, hg0⟩ : ∃ g0 : ModGL Tag.E6 (AlgebraicClosure K), g0 = F.g0 := ⟨_, rfl⟩
  have hg0C : g0 ∈ adjointGroup Tag.E6 (AlgebraicClosure K) := by
    rw [hg0]
    exact F.g0_mem
  have hb₁ : ∀ s : Fin Tag.E6.rank → ZMod p,
      baseChangeGL (τ := Tag.E6) (algebraMap K (AlgebraicClosure K))
          ((ι₁ (Multiplicative.ofAdd s)).1 : ModGL Tag.E6 K) =
        g0 * ExcFrames.frameDiag (τ := Tag.E6) ζb hζb s * g0⁻¹ := by
    intro s
    have h : ggKGTwY F (ι₁ (Multiplicative.ofAdd s)) =
        g0⁻¹ * baseChangeGL (τ := Tag.E6) (algebraMap K (AlgebraicClosure K))
          ((ι₁ (Multiplicative.ofAdd s)).1 : ModGL Tag.E6 K) * g0 := by
      rw [hg0]
      exact ggKGTwY_apply F _
    have h2 : ggKGTwY F (ι₁ (Multiplicative.ofAdd s)) =
        ExcFrames.frameDiag (τ := Tag.E6) ζb hζb s := hT (ExcFrames.frameCoord Tag.E6 p s)
    rw [h2] at h
    rw [h]
    group
  obtain ⟨G, hG⟩ : ∃ G : ModGL Tag.E6 (AlgebraicClosure K), G =
      baseChangeGL (τ := Tag.E6) (algebraMap K (AlgebraicClosure K))
        ((CFSG.LieType.Steinberg.Isogeny.e6Isogeny K
          (CFSG.StandardType.TwE6Lang.langG K θ.toRingHom l) : adjointGroup Tag.E6 K) :
          ModGL Tag.E6 K) := ⟨_, rfl⟩
  have hbs : ∀ s : Fin Tag.E6.rank → ZMod p,
      baseChangeGL (τ := Tag.E6) (algebraMap K (AlgebraicClosure K))
          ((ρ (Multiplicative.ofAdd s)).1 : ModGL Tag.E6 K) =
        G * ExcFrames.frameDiag (τ := Tag.E6) ζb hζb s * G⁻¹ := by
    intro s
    have h := TBE6IndTwist.isogeny_langPFrame K θ hθ l hl hf1 hK (fun c => hθq c) ζS hζS
      (Multiplicative.ofAdd s)
    have hch := baseChangeGL_chevTorus_E6 (ζS : Kˣ) (congrArg Subtype.val hζS) hζb
      (Multiplicative.ofAdd s)
    have h2 := congrArg (baseChangeGL (τ := Tag.E6) (algebraMap K (AlgebraicClosure K))) h
    rw [map_mul, map_mul, map_inv, hch, ← hG] at h2
    exact h2
  obtain ⟨g₂, hg₂def⟩ : ∃ g₂ : ModGL Tag.E6 (AlgebraicClosure K), g₂ =
      (baseChangeGL (τ := Tag.E6) (algebraMap K (AlgebraicClosure K))
        (c.1 : ModGL Tag.E6 K))⁻¹ * G := ⟨_, rfl⟩
  have hbcC : baseChangeGL (τ := Tag.E6) (algebraMap K (AlgebraicClosure K))
      (c.1 : ModGL Tag.E6 K) ∈ adjointGroup Tag.E6 (AlgebraicClosure K) :=
    map_baseChangeGL_adjointGroup_le (algebraMap K (AlgebraicClosure K))
      ⟨_, ggKGTc_coe_mem_adjointGroup c, rfl⟩
  have hGC : G ∈ adjointGroup Tag.E6 (AlgebraicClosure K) := by
    rw [hG]
    exact map_baseChangeGL_adjointGroup_le (algebraMap K (AlgebraicClosure K))
      ⟨_, (CFSG.LieType.Steinberg.Isogeny.e6Isogeny K
        (CFSG.StandardType.TwE6Lang.langG K θ.toRingHom l)).2, rfl⟩
  have hg₂ : g₂ ∈ adjointGroup Tag.E6 (AlgebraicClosure K) := by
    rw [hg₂def]
    exact mul_mem (inv_mem hbcC) hGC
  have hb₂ : ∀ s : Fin Tag.E6.rank → ZMod p,
      baseChangeGL (τ := Tag.E6) (algebraMap K (AlgebraicClosure K))
          ((ι₂ (Multiplicative.ofAdd s)).1 : ModGL Tag.E6 K) =
        g₂ * ExcFrames.frameDiag (τ := Tag.E6) ζb hζb s * g₂⁻¹ := by
    intro s
    obtain ⟨cm, hcm⟩ : ∃ cm : ModGL Tag.E6 K, cm = c.1 := ⟨_, rfl⟩
    obtain ⟨ym, hym⟩ : ∃ ym : ModGL Tag.E6 K, ym = (ρ (Multiplicative.ofAdd s)).1 := ⟨_, rfl⟩
    obtain ⟨xm, hxm⟩ : ∃ xm : ModGL Tag.E6 K, xm = (ι₂ (Multiplicative.ofAdd s)).1 :=
      ⟨_, rfl⟩
    have h1' : ((ι₂ (Multiplicative.ofAdd s) : ↥(twistedE6RootGroup K θ)) :
        ModGL TwistTag.E6.tag K) =
        (c : ModGL TwistTag.E6.tag K)⁻¹ *
          (ρ (Multiplicative.ofAdd s) : ModGL TwistTag.E6.tag K) *
          (c : ModGL TwistTag.E6.tag K) := by
      change ((c⁻¹ * ρ (Multiplicative.ofAdd s) * c⁻¹⁻¹ : ↥(twistedE6RootGroup K θ)) :
        ModGL TwistTag.E6.tag K) = _
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
    have h1 : xm = cm⁻¹ * ym * cm := by
      rw [hxm, hym, hcm]
      exact h1'
    have hbs' : baseChangeGL (τ := Tag.E6) (algebraMap K (AlgebraicClosure K)) ym =
        G * ExcFrames.frameDiag (τ := Tag.E6) ζb hζb s * G⁻¹ := by
      rw [hym]
      exact hbs s
    rw [← hxm, h1, map_mul, map_mul, map_inv, hbs', hcm, hg₂def]
    group
  obtain ⟨u, hu⟩ := exists_weyl_of_two_frames (τ := Tag.E6) (H := twistedE6RootGroup K θ)
    (ζ := ζb) (hζ := hζb) hζbo hdet hg0C hg₂ (ι₁ := ι₁) (ι₂ := ι₂)
    (le_of_eq (hι₂range.trans hι₁range.symm)) hb₁ hb₂
  obtain ⟨w, hw⟩ : ∃ w : CFSG.LieType.Steinberg.TwistedE6.fixedGroup K θ.toRingHom,
      w = TBE6IndTwist.langWeylHom K θ.toRingHom hθ hl u⁻¹ := ⟨_, rfl⟩
  let c₃ : ↥(twistedE6RootGroup K θ) := c⁻¹ * q w
  have hc₃' : ∀ s' : Fin Tag.E6.rank → ZMod p,
      c₃ * q (TBE6IndTwist.langPFrame K θ hθ l hl ζS hζS (Multiplicative.ofAdd s')) * c₃⁻¹ =
        ι₁ (Multiplicative.ofAdd s') := by
    intro s'
    have h1 : w * TBE6IndTwist.langPFrame K θ hθ l hl ζS hζS (Multiplicative.ofAdd s') * w⁻¹ =
        TBE6IndTwist.langPFrame K θ hθ l hl ζS hζS
          (Multiplicative.ofAdd (TableBExc.torusAct Tag.E6 p u⁻¹ s')) := by
      rw [hw]
      exact TBE6IndTwist.langWeylHom_conj_langPFrame K θ hθ l hl ζS hζS u⁻¹ s'
    have h2 := congrArg q h1
    rw [map_mul, map_mul, map_inv] at h2
    have h3 : ι₂ (Multiplicative.ofAdd (TableBExc.torusAct Tag.E6 p u⁻¹ s')) =
        c⁻¹ * q (TBE6IndTwist.langPFrame K θ hθ l hl ζS hζS
          (Multiplicative.ofAdd (TableBExc.torusAct Tag.E6 p u⁻¹ s'))) * c := by
      change c⁻¹ * _ * c⁻¹⁻¹ = _
      rw [inv_inv]
      rfl
    have h4 : ι₂ (Multiplicative.ofAdd (TableBExc.torusAct Tag.E6 p u⁻¹ s')) =
        ι₁ (Multiplicative.ofAdd (TableBExc.torusAct Tag.E6 p u
          (TableBExc.torusAct Tag.E6 p u⁻¹ s'))) := hu _
    rw [h3, ← h2] at h4
    rw [← TableBExc.torusAct_mul, mul_inv_cancel, TableBExc.torusAct_one] at h4
    change c⁻¹ * q w * q (TBE6IndTwist.langPFrame K θ hθ l hl ζS hζS (Multiplicative.ofAdd s')) *
      (c⁻¹ * q w)⁻¹ = _
    rw [← h4]
    simp only [mul_inv_rev, inv_inv]
    group
  have hc₃ : ∀ s, c₃ * q (TBE6IndTwist.langPFrame K θ hθ l hl ζS hζS s) * c₃⁻¹ = ι₁ s :=
    fun s => hc₃' (Multiplicative.toAdd s)
  obtain ⟨wt, hHolds, hact⟩ := exists_scalarWitness_of_conj θ hθ l hl hf1 hK (fun c => hθq c) hp
    hp2 hp3 ζS hζS hζSo e c₃ ι₁ hc₃ (E.map (MulAut.conj : ↥(twistedE6RootGroup K θ) →* _))
    (by rw [hι₁range])
  refine ⟨AlgebraicClosure K, inferInstance, ζb, hζb, ι₁, wt.n, 2 ^ n + 1, wt, hζbo, hι₁inj,
    hι₁range, hact, fun k => rfl, hHolds, ?_⟩
  intro t ht Y hY
  obtain ⟨i, hker, hlow⟩ := twE6_frame_class hn hK hσ hpq F hv' hζb hT t ht hY
  exact ⟨i, hker, hlow⟩

end CFSG.StandardType

end
