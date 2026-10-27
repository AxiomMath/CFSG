module

public import CFSG.LocalAnalysis.StandardType.GGE0ShapeDefs
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidTwE6
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Stroth.HeisD4.StraightenTw
public import CFSG.LocalAnalysis.StandardType.GGTwE6RootKillDefs
public import CFSG.RankThree.PartOne.KE.CTLang
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.LieType.Chevalley.RootDiagonalWeylTransporter
public import CFSG.LieType.Chevalley.CLSOddE7RationalDerivedIndex
public import CFSG.LieType.Chevalley.GraphFixedF4GroupRestriction
public import CFSG.LieType.Chevalley.DiagramCoordinateFixedStructure
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigidTools
public import CFSG.LieType.Chevalley.LangActualInvolutionReduction
public import CFSG.LieType.Chevalley.OddDiagramFrobeniusFixedDerived

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.SeitzGeneration.ExcWideThree
  CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.ExcWideThree.HeisD4

private theorem baseChangeGL_comp_algebraMap
    {t : Tag} {K Ω Kbar : Type} [Field K] [Field Ω] [Field Kbar]
    [Algebra K Ω] [Algebra K Kbar]
    (τ : Ω ≃ₐ[K] Kbar) (x : ModGL t K) :
    baseChangeGL (τ : Ω →+* Kbar) (baseChangeGL (algebraMap K Ω) x) =
      baseChangeGL (algebraMap K Kbar) x := by
  rw [baseChangeGL_baseChangeGL]
  have h : (τ : Ω →+* Kbar).comp (algebraMap K Ω) = algebraMap K Kbar := by
    ext c
    exact τ.commutes c
  rw [h]

private theorem baseChangeGL_mem_twistedTorusOf
    {τ : Tag} {R S : Type} [Field R] [Field S] [IsAlgClosed S]
    (f : R →+* S) {n : ModGL τ R} {Φ : ModGL τ R →* ModGL τ R}
    {Φ' : ModGL τ S →* ModGL τ S}
    (hcomm : ∀ x, Φ' (baseChangeGL f x) = baseChangeGL f (Φ x)) {x : ModGL τ R}
    (hx : x ∈ CFSG.RankThree.PartOne.KE.twistedTorusOf n Φ) :
    baseChangeGL f x ∈ CFSG.RankThree.PartOne.KE.twistedTorusOf (baseChangeGL f n) Φ' := by
  obtain ⟨a, rfl⟩ := CFSG.LieType.Chevalley.exists_rootDiagUnit_eq_of_mem_torusGroup
    (CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.1 hx).1
  rw [CFSG.RankThree.PartOne.KE.mem_twistedTorusOf]
  constructor
  · rw [baseChangeGL_rootDiagUnit]
    exact CFSG.LieType.Chevalley.rootDiagUnit_mem_torusGroup _
  · rw [hcomm (rootDiagUnit τ a)]
    have hfix := (CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.1 hx).2
    simpa only [map_mul, map_inv] using congrArg (baseChangeGL f) hfix

theorem twisted_langData_of_setup
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ)
    (hK : Nat.card K = q ^ 2) (hσ : ∀ c, σ c = c ^ q)
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2] [Algebra K Ω] [IsAlgClosure K Ω]
    (S : LangSetup .E6 Ω 5) (hq : S.D.q = q)
    (hΦ : ∃ Fr : Ω →+* Ω, (∀ c, Fr c = c ^ q) ∧ S.D.Φ = twistHom .E6 Ω Fr)
    (A : Subgroup (ModGL TwistTag.E6.tag K)) (hAI : A ≤ twistedE6InndiagGL K σ)
    (A₀ : Subgroup (ModGL .E6 Ω)) (hA₀ : A₀ ≤ S.D.torus ⊓ S.D.model)
    (hrel : A.map ((MulAut.conj S.D.g0⁻¹).toMonoidHom.comp
      (baseChangeGL (algebraMap K Ω) : ModGL TwistTag.E6.tag K →* ModGL Tag.E6 Ω)) = A₀)
    {v : WeylGroup TwistTag.E6.tag}
    (hv : S.D.n = canonicalRep (coxeterSystem TwistTag.E6.tag) Ω v) :
    ∃ D : TwLangData K σ q A, D.v = v ∧ ∀ α, TwE6RootKill.TwDataKills D α →
      ∀ x ∈ A, ∃ a : Fin Tag.E6.rank → Ωˣ,
        rootDiagUnit .E6 a = S.D.g0⁻¹ *
            (baseChangeGL (algebraMap K Ω) x : ModGL Tag.E6 Ω) * S.D.g0 ∧
          rootChar a α = 1 := by
  obtain ⟨Frω, hFrω, hΦeq⟩ := hΦ
  let τ : Ω ≃ₐ[K] AlgebraicClosure K := IsAlgClosure.equiv K Ω (AlgebraicClosure K)
  let Fr : AlgebraicClosure K →+* AlgebraicClosure K :=
    (τ : Ω →+* AlgebraicClosure K).comp (Frω.comp (τ.symm : AlgebraicClosure K →+* Ω))
  have hcommHom : (τ : Ω →+* AlgebraicClosure K).comp Frω =
      Fr.comp (τ : Ω →+* AlgebraicClosure K) := by
    ext c
    show τ (Frω c) = τ (Frω (τ.symm (τ c)))
    rw [AlgEquiv.symm_apply_apply]
  have hFr : ∀ c, Fr c = c ^ q := by
    intro c
    show τ (Frω (τ.symm c)) = c ^ q
    simp only [hFrω, map_pow, AlgEquiv.apply_symm_apply]
  let g0t : ModGL TwistTag.E6.tag Ω := S.D.g0
  let nt : ModGL TwistTag.E6.tag Ω := S.D.n
  let PhiΩ : ModGL TwistTag.E6.tag Ω →* ModGL TwistTag.E6.tag Ω :=
    twistHom TwistTag.E6 Ω Frω
  let PhiK : ModGL TwistTag.E6.tag (AlgebraicClosure K) →*
      ModGL TwistTag.E6.tag (AlgebraicClosure K) :=
    twistHom TwistTag.E6 (AlgebraicClosure K) Fr
  let T : ModGL TwistTag.E6.tag Ω →* ModGL TwistTag.E6.tag (AlgebraicClosure K) :=
    baseChangeGL (τ : Ω →+* AlgebraicClosure K)
  have hΦcomm : ∀ x : ModGL TwistTag.E6.tag Ω,
      PhiK (baseChangeGL (τ : Ω →+* AlgebraicClosure K) x) =
        baseChangeGL (τ : Ω →+* AlgebraicClosure K) (PhiΩ x) :=
    fun x => twistHom_baseChangeGL (t := TwistTag.E6) (ι := (τ : Ω →+* AlgebraicClosure K))
      hcommHom x
  have hg0C : T g0t ∈ adjointGroup Tag.E6 (AlgebraicClosure K) :=
    map_baseChangeGL_adjointGroup_le (τ := Tag.E6) (f := (τ : Ω →+* AlgebraicClosure K))
      ⟨S.D.g0, S.D.g0_mem, rfl⟩
  have hg0 : PhiK (T g0t) =
      T g0t * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v := by
    have hlang : PhiΩ g0t = g0t * nt := by
      have h : S.D.Φ g0t = g0t * nt := S.D.lang
      rwa [show S.D.Φ = PhiΩ from hΦeq] at h
    have h1 : T (PhiΩ g0t) = T (g0t * nt) := congrArg T hlang
    dsimp only [T] at h1
    rw [← hΦcomm g0t, map_mul] at h1
    have hnt : nt = canonicalRep (coxeterSystem TwistTag.E6.tag) Ω v := hv
    rw [hnt, baseChangeGL_canonicalRep] at h1
    exact h1
  have hy_mem : ∀ (x : ModGL TwistTag.E6.tag K), x ∈ A →
      g0t⁻¹ * baseChangeGL (algebraMap K Ω) x * g0t ∈ A₀ := by
    intro x hxA
    have hmem : (MulAut.conj S.D.g0⁻¹).toMonoidHom
        (baseChangeGL (algebraMap K Ω) x) ∈ A₀ := by
      rw [← hrel]
      exact ⟨x, hxA, rfl⟩
    have hconj : (MulAut.conj S.D.g0⁻¹).toMonoidHom
        (baseChangeGL (algebraMap K Ω) x) =
        g0t⁻¹ * baseChangeGL (algebraMap K Ω) x * g0t := by
      change (MulAut.conj S.D.g0⁻¹) (baseChangeGL (algebraMap K Ω) x) =
        g0t⁻¹ * baseChangeGL (algebraMap K Ω) x * g0t
      rw [MulAut.conj_apply, inv_inv]
      rfl
    rwa [hconj] at hmem
  have hc : ∀ x ∈ A, baseChangeGL (algebraMap K (AlgebraicClosure K))
      (1 * x * 1⁻¹ : ModGL TwistTag.E6.tag K) ∈
      (CFSG.RankThree.PartOne.KE.twistedTorusOf
        (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
        PhiK).map (MulAut.conj (T g0t)).toMonoidHom := by
    intro x hxA
    let y : ModGL TwistTag.E6.tag Ω := g0t⁻¹ * baseChangeGL (algebraMap K Ω) x * g0t
    have hyA₀ : y ∈ A₀ := by
      simpa only [y] using hy_mem x hxA
    have hyT : y ∈ S.D.torus := (hA₀ hyA₀).1
    have hyT' : y ∈ CFSG.RankThree.PartOne.KE.twistedTorusOf nt PhiΩ := by
      rw [show nt = S.D.n from rfl, show PhiΩ = S.D.Φ from hΦeq.symm]
      exact hyT
    have htrans : T y ∈ CFSG.RankThree.PartOne.KE.twistedTorusOf
        (baseChangeGL (τ : Ω →+* AlgebraicClosure K) nt) PhiK :=
      baseChangeGL_mem_twistedTorusOf (τ := TwistTag.E6.tag)
        (f := (τ : Ω →+* AlgebraicClosure K))
        (n := nt) (Φ := PhiΩ) (Φ' := PhiK) hΦcomm hyT'
    have hntK : baseChangeGL (τ : Ω →+* AlgebraicClosure K) nt =
        canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v := by
      have hnt_eq : nt = canonicalRep (coxeterSystem TwistTag.E6.tag) Ω v := hv
      rw [hnt_eq, baseChangeGL_canonicalRep]
    have htrans' : T y ∈ CFSG.RankThree.PartOne.KE.twistedTorusOf
        (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v) PhiK := by
      rwa [hntK] at htrans
    refine ⟨T y, htrans', ?_⟩
    change T g0t * T y * (T g0t)⁻¹ =
      baseChangeGL (algebraMap K (AlgebraicClosure K))
        (1 * x * 1⁻¹ : ModGL TwistTag.E6.tag K)
    have hTy : T y = (T g0t)⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) x *
        T g0t := by
      dsimp only [y, T]
      simp only [map_mul, map_inv, baseChangeGL_comp_algebraMap]
    rw [hTy]
    simp only [one_mul, inv_one, mul_one]
    group <;> rfl
  let D : TwLangData K σ q A :=
    { v := v, Fr := Fr, hFr := hFr, g0 := T g0t, hg0C := hg0C, hg0 := hg0,
      c := 1, hcI := Subgroup.one_mem _, hc := hc }
  refine ⟨D, rfl, ?_⟩
  intro α hkill x hxA
  obtain ⟨a', hroot', hchar'⟩ := hkill x hxA
  have hroot'' : rootDiagUnit TwistTag.E6.tag a' = D.g0⁻¹ *
      baseChangeGL (algebraMap K (AlgebraicClosure K)) x * D.g0 := by
    have h := hroot'
    simpa only [D, one_mul, inv_one, mul_one] using h
  let y : ModGL TwistTag.E6.tag Ω := g0t⁻¹ * baseChangeGL (algebraMap K Ω) x * g0t
  have hyA₀ : y ∈ A₀ := by
    simpa only [y] using hy_mem x hxA
  have hyT : y ∈ S.D.torus := (hA₀ hyA₀).1
  have hyT' : y ∈ CFSG.RankThree.PartOne.KE.twistedTorusOf nt PhiΩ := by
    rw [show nt = S.D.n from rfl, show PhiΩ = S.D.Φ from hΦeq.symm]
    exact hyT
  obtain ⟨a, ha⟩ := CFSG.LieType.Chevalley.exists_rootDiagUnit_eq_of_mem_torusGroup
    (τ := TwistTag.E6.tag) (K := Ω)
    (CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.1 hyT').1
  have hTy_rootDiag : T y = rootDiagUnit TwistTag.E6.tag
      (fun i => Units.map (τ : Ω →+* AlgebraicClosure K).toMonoidHom (a i)) := by
    dsimp only [T]
    rw [ha]
    exact baseChangeGL_rootDiagUnit (τ := TwistTag.E6.tag)
      (f := (τ : Ω →+* AlgebraicClosure K)) a
  have hTy_BC : T y = D.g0⁻¹ *
      baseChangeGL (algebraMap K (AlgebraicClosure K)) x * D.g0 := by
    dsimp only [y, T, D]
    simp only [map_mul, map_inv, baseChangeGL_comp_algebraMap]
  have hEq : rootDiagUnit TwistTag.E6.tag a' = rootDiagUnit TwistTag.E6.tag
      (fun i => Units.map (τ : Ω →+* AlgebraicClosure K).toMonoidHom (a i)) := by
    rw [hroot'', ← hTy_BC, hTy_rootDiag]
  have hfun : a' = fun i => Units.map (τ : Ω →+* AlgebraicClosure K).toMonoidHom (a i) :=
    CFSG.LieType.Chevalley.rootDiagUnit_injective hEq
  refine ⟨a, ha.symm, ?_⟩
  let f : Ω →+* AlgebraicClosure K := (τ : Ω →+* AlgebraicClosure K)
  have hmap : Units.map f.toMonoidHom (rootChar a α) =
      rootChar (fun i => Units.map f.toMonoidHom (a i)) α := by
    simp only [rootChar, map_prod, map_zpow]
  have h1 : Units.map f.toMonoidHom (rootChar a α) = 1 := by
    rw [hmap]
    simpa only [hfun] using hchar'
  have h2 : f (rootChar a α : Ω) = (1 : AlgebraicClosure K) := by
    simpa using congrArg (fun u : (AlgebraicClosure K)ˣ => (u : AlgebraicClosure K)) h1
  refine Units.ext ?_
  apply f.injective
  exact h2.trans (map_one f).symm

end CFSG.StandardType
