module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcLat2

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE

theorem ggKGEl_conj_mul
    {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ} {E : Subgroup (adjointGroup τ K)}
    (F : ExcFrame τ K p E) (a b : adjointGroup τ K) :
    F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) ((a * b : adjointGroup τ K) :
        ModGL τ K) * F.D.g0 =
      (F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (a : ModGL τ K) * F.D.g0) *
        (F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (b : ModGL τ K) *
          F.D.g0) := by
  rw [Subgroup.coe_mul, map_mul]
  group

theorem ggKGEl_conj_one
    {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ} {E : Subgroup (adjointGroup τ K)}
    (F : ExcFrame τ K p E) :
    F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((1 : adjointGroup τ K) : ModGL τ K) * F.D.g0 = 1 := by
  rw [Subgroup.coe_one, map_one]
  group

noncomputable def ggKGEl_pick
    {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ}
    {E : Subgroup (adjointGroup τ K)}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4)
    (F : ExcFrame τ K p E)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hΦ : ∀ g, F.D.Φ g = Units.map (entrywiseHom Fr) g)
    (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p)
    (hact : ∀ y : Fin τ.rank → ℤ,
      weylTuple F.w (fun i => Units.map Fr.toMonoidHom (ζ ^ y i)) = (fun i => ζ ^ y i))
    (y : Fin τ.rank → ℤ) : ↥E :=
  let h := ggKGEx_exists_conj_of_hact hp (by omega) (fun _ => hp5) hτ F hΦ (b := fun i => ζ ^ y i)
    (fun i => ggKGEl_zetaPow_pow_eq_one ζ hζ (y i)) (hact y)
  ⟨Classical.choose h, (Classical.choose_spec h).1⟩

theorem ggKGEl_pick_spec
    {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ}
    {E : Subgroup (adjointGroup τ K)}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4)
    (F : ExcFrame τ K p E)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hΦ : ∀ g, F.D.Φ g = Units.map (entrywiseHom Fr) g)
    (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p)
    (hact : ∀ y : Fin τ.rank → ℤ,
      weylTuple F.w (fun i => Units.map Fr.toMonoidHom (ζ ^ y i)) = (fun i => ζ ^ y i))
    (y : Fin τ.rank → ℤ) :
    F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (((ggKGEl_pick hp hp5 hτ F hΦ ζ hζ hact y : ↥E) : adjointGroup τ K) : ModGL τ K) *
        F.D.g0 =
      rootDiagUnit τ (fun i => ζ ^ y i) := by
  dsimp only [ggKGEl_pick]
  exact (Classical.choose_spec (ggKGEx_exists_conj_of_hact hp (by omega) (fun _ => hp5) hτ F hΦ
    (b := fun i => ζ ^ y i) (fun i => ggKGEl_zetaPow_pow_eq_one ζ hζ (y i)) (hact y))).2.symm

noncomputable def ggKGEl_pi
    {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ}
    {E : Subgroup (adjointGroup τ K)}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4)
    (F : ExcFrame τ K p E)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hΦ : ∀ g, F.D.Φ g = Units.map (entrywiseHom Fr) g)
    (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p)
    (hact : ∀ y : Fin τ.rank → ℤ,
      weylTuple F.w (fun i => Units.map Fr.toMonoidHom (ζ ^ y i)) = (fun i => ζ ^ y i)) :
    (Fin τ.rank → ℤ) →+ Additive ↥E where
  toFun y := Additive.ofMul (ggKGEl_pick hp hp5 hτ F hΦ ζ hζ hact y)
  map_zero' := by
    change Additive.ofMul (ggKGEl_pick hp hp5 hτ F hΦ ζ hζ hact 0) =
      Additive.ofMul (1 : ↥E)
    apply congrArg Additive.ofMul
    apply Subtype.ext
    apply ggKGEl_conj_injective F
    dsimp only
    rw [ggKGEl_pick_spec, Subgroup.coe_one, ggKGEl_conj_one]
    simp only [Pi.zero_apply, zpow_zero, Pi.one_apply]
    exact rootDiagUnit_one
  map_add' y y' := by
    change Additive.ofMul (ggKGEl_pick hp hp5 hτ F hΦ ζ hζ hact (y + y')) =
      Additive.ofMul (ggKGEl_pick hp hp5 hτ F hΦ ζ hζ hact y *
        ggKGEl_pick hp hp5 hτ F hΦ ζ hζ hact y')
    apply congrArg Additive.ofMul
    apply Subtype.ext
    apply ggKGEl_conj_injective F
    dsimp only
    rw [ggKGEl_pick_spec, Subgroup.coe_mul, ggKGEl_conj_mul, ggKGEl_pick_spec, ggKGEl_pick_spec]
    rw [show (fun i => ζ ^ (y + y') i) =
        (fun i => ζ ^ y i) * (fun i => ζ ^ y' i) from by
      funext i; simp [Pi.add_apply, zpow_add]]
    rw [rootDiagUnit_mul]

theorem ggKGEl_pi_spec
    {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ}
    {E : Subgroup (adjointGroup τ K)}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4)
    (F : ExcFrame τ K p E)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hΦ : ∀ g, F.D.Φ g = Units.map (entrywiseHom Fr) g)
    (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p)
    (hact : ∀ y : Fin τ.rank → ℤ,
      weylTuple F.w (fun i => Units.map Fr.toMonoidHom (ζ ^ y i)) = (fun i => ζ ^ y i))
    (y : Fin τ.rank → ℤ) :
    F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (((Additive.toMul (ggKGEl_pi hp hp5 hτ F hΦ ζ hζ hact y) : ↥E) :
          adjointGroup τ K) : ModGL τ K) * F.D.g0 =
      rootDiagUnit τ (fun i => ζ ^ y i) :=
  ggKGEl_pick_spec hp hp5 hτ F hΦ ζ hζ hact y

theorem ggKGEl_pi_surjective
    {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ}
    {E : Subgroup (adjointGroup τ K)}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4)
    (F : ExcFrame τ K p E)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hΦ : ∀ g, F.D.Φ g = Units.map (entrywiseHom Fr) g)
    (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p)
    (hact : ∀ y : Fin τ.rank → ℤ,
      weylTuple F.w (fun i => Units.map Fr.toMonoidHom (ζ ^ y i)) = (fun i => ζ ^ y i)) :
    Function.Surjective (ggKGEl_pi hp hp5 hτ F hΦ ζ hζ hact) := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  intro e
  let Ψ : ↥E →* ModGL τ (AlgebraicClosure K) :=
    { toFun := fun x => F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x : adjointGroup τ K) : ModGL τ K) * F.D.g0
      map_one' := ggKGEl_conj_one F
      map_mul' := fun a b => ggKGEl_conj_mul F (a : adjointGroup τ K) (b : adjointGroup τ K) }
  have he : ((Additive.toMul e : ↥E) : adjointGroup τ K) ^ p = 1 :=
    ((F.mem_iff ((Additive.toMul e : ↥E) : adjointGroup τ K)).1 (Additive.toMul e).2).1
  have heT : F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (((Additive.toMul e : ↥E) : adjointGroup τ K) : ModGL τ K) * F.D.g0 ∈ F.D.torus :=
    ((F.mem_iff ((Additive.toMul e : ↥E) : adjointGroup τ K)).1 (Additive.toMul e).2).2
  have heG : F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (((Additive.toMul e : ↥E) : adjointGroup τ K) : ModGL τ K) * F.D.g0 ∈
      torusGroup τ (AlgebraicClosure K) := (mem_twistedTorusOf.1 heT).1
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup heG
  have hbp : ∀ i, b i ^ p = 1 := by
    have h1 : (rootDiagUnit τ b) ^ p = 1 := by
      rw [← hb]
      change (Ψ (Additive.toMul e)) ^ p = 1
      rw [← map_pow, show (Additive.toMul e : ↥E) ^ p = 1 from Subtype.ext he, map_one]
    have hbp' : b ^ p = 1 := rootDiagUnit_injective (τ := τ)
      (by rw [← rootDiagUnit_pow, h1, rootDiagUnit_one])
    intro i
    simpa using congrFun hbp' i
  choose y hy using fun i => ggKGEl_eq_zetaPow_of_pow_eq_one ζ hζ (hbp i)
  refine ⟨y, ?_⟩
  apply Additive.toMul.injective
  apply Subtype.ext
  apply ggKGEl_conj_injective F
  dsimp only
  rw [ggKGEl_pi_spec, hb]
  congr 1
  funext i
  exact (hy i).symm

end CFSG.StandardType

end
