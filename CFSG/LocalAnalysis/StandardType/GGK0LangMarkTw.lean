module

public import CFSG.LocalAnalysis.StandardType.GGK0StageDefs
public import CFSG.LocalAnalysis.StandardType.GGFinModelRat
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangTwE6Conj
public import Certificates.Certificate1952
import CFSG.LocalAnalysis.StandardType.GGK0KacRowTw
import CFSG.LocalAnalysis.StandardType.GGK0LangModelTw
import CFSG.LocalAnalysis.StandardType.GGK0LangMarkUntw
import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Delta
import CFSG.LocalAnalysis.StandardType.GGTwE6DD2Recipe
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompAlcoveLangNormalTw
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompTree
import CFSG.LocalAnalysis.StandardType.GGFinModelEps
import CFSG.LocalAnalysis.StandardType.GGL45NtExcBridgeTwE6
import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRankFiveAmbient
import CFSG.LieType.Chevalley.AlgebraicClosurePrimeField
import CFSG.LieType.Chevalley.GraphFixedBruhatEquivariance
import CFSG.LieType.Chevalley.TwistMap

public section

namespace CFSG.StandardType.GGK0MarkedKacIface1587

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.GGFinModel
  CFSG.StandardType.RecipeExcLang

theorem largeEvenLabelAll_k0LangMark_tw
    {lab : LargeEvenLabel} {p : ℕ} (htag : lab.tag = .twE6)
    (h : ∀ (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ lab.n) ^ 2 →
      ∀ (σ : K ≃+* K), (∀ c, σ c = c ^ (2 ^ lab.n)) →
        ∀ y : twInndiagGroup K σ, orderOf (twConj K σ y) = p →
          Nonempty (K0LangMark GGL lab p (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)
            (Set.range (twConj K σ)) (twConj K σ y))) :
    LargeEvenLabelAll lab (fun R _ I _ => ∀ phi : MulAut R, phi ∈ I → orderOf phi = p →
      Nonempty (K0LangMark GGL lab p R I phi)) := by
  classical
  refine TwE6Delta.labelAll htag (Q := fun R _ I => ∀ phi : MulAut R, phi ∈ I →
    orderOf phi = p → Nonempty (K0LangMark GGL lab p R I phi)) ?_
  intro K _ _ hK phi hphi hphip
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : 1 ≤ lab.n := by
    have h2 : 2 ≤ Nat.card K := Finite.one_lt_card
    rw [hK] at h2
    rcases Nat.eq_zero_or_pos lab.n with h | h
    · rw [h] at h2
      norm_num at h2
    · exact h
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := by
    have hcard : Fintype.card K = 2 ^ (lab.n * 2) := by
      rw [← Nat.card_eq_fintype_card, hK, pow_mul]
    exact charP_of_card_eq_prime_pow (p := 2) (f := lab.n * 2) hcard
  have hinj : Function.Injective (iterateFrobenius K 2 lab.n) :=
    (iterateFrobenius K 2 lab.n).injective
  let σ : K ≃+* K := RingEquiv.ofBijective (iterateFrobenius K 2 lab.n)
    ⟨hinj, Finite.surjective_of_injective hinj⟩
  have hσ : ∀ c, σ c = c ^ (2 ^ lab.n) := fun c => iterateFrobenius_def 2 lab.n c
  obtain ⟨ε, hε⟩ := TwE6DD2.exists_recipeEquiv hn hK σ hσ
  have hcongr : ∀ z : MulAut (TwE6Delta.RecipeR K lab.n),
      MulAut.congr ε (MulAut.congr ε.symm z) = z :=
    fun z => MulEquiv.apply_symm_apply (MulAut.congr ε) z
  have hxmem : MulAut.congr ε.symm phi ∈ (twConj K σ).range := by
    refine (hε (MulAut.congr ε.symm phi)).1 ?_
    rw [hcongr phi]
    exact hphi
  obtain ⟨y, hy⟩ := hxmem
  have hord : orderOf (twConj K σ y) = p := by
    rw [hy, MulEquiv.orderOf_eq]
    exact hphip
  obtain ⟨M⟩ := h K hK σ hσ y hord
  have hI : MulAut.congr ε '' Set.range (twConj K σ) = TwE6Delta.RecipeI K lab.n := by
    ext z
    constructor
    · rintro ⟨x, ⟨w, rfl⟩, rfl⟩
      exact (hε (twConj K σ w)).2 ⟨w, rfl⟩
    · intro hz
      refine ⟨MulAut.congr ε.symm z, ?_, hcongr z⟩
      refine (hε (MulAut.congr ε.symm z)).1 ?_
      rw [hcongr z]
      exact hz
  have hM := K0LangMark.nonempty_congr ⟨M⟩ ε
  rw [hI] at hM
  have hphi' : MulAut.congr ε (twConj K σ y) = phi := by
    rw [hy]
    exact hcongr phi
  rw [hphi'] at hM
  exact hM

private theorem k0LangMark_tw_y_facts
    {lab : LargeEvenLabel} {p : ℕ} (hpair : GGKacExcPair lab p)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ lab.n) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ lab.n)) (y : twInndiagGroup K σ)
    (hy : orderOf (twConj K σ y) = p) :
    1 ≤ lab.n ∧ orderOf y = p ∧ (y : ModGL TwistTag.E6.tag K) ^ p = 1 ∧ y ≠ 1 := by
  have hp : p.Prime := hpair.1
  have hn : 1 ≤ lab.n := by
    have h2 : 2 ≤ Nat.card K := Finite.one_lt_card
    rw [hK] at h2
    rcases Nat.eq_zero_or_pos lab.n with h | h
    · rw [h] at h2
      norm_num at h2
    · exact h
  have hinj : Function.Injective (twConj K σ) :=
    CFSG.StandardType.NoOffTwE6Three.twConj_injective hn hK σ hσ
  have hyord : orderOf y = p :=
    (orderOf_injective (twConj K σ) hinj y).symm.trans hy
  have hyp : (y : ModGL TwistTag.E6.tag K) ^ p = 1 := by
    rw [← hyord]
    exact congrArg (Subtype.val) (pow_orderOf_eq_one y)
  refine ⟨hn, hyord, hyp, ?_⟩
  intro h1
  apply hp.ne_one
  rw [← hyord, h1, orderOf_one]

private theorem k0LangMark_tw_u_facts
    {K : Type} [Field K] [Finite K] [Algebra K GGL] {n p : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (y : twInndiagGroup K σ) (hyp : (y : ModGL TwistTag.E6.tag K) ^ p = 1) (hyne : y ≠ 1) :
    baseChangeGL (algebraMap K GGL) (y : ModGL TwistTag.E6.tag K) ∈
        adjointGroup TwistTag.E6.tag GGL ∧
      twistHom TwistTag.E6 GGL (ggFrobT n)
          (baseChangeGL (algebraMap K GGL) (y : ModGL TwistTag.E6.tag K)) =
        baseChangeGL (algebraMap K GGL) (y : ModGL TwistTag.E6.tag K) ∧
      (baseChangeGL (algebraMap K GGL) (y : ModGL TwistTag.E6.tag K)) ^ p = 1 ∧
      baseChangeGL (algebraMap K GGL) (y : ModGL TwistTag.E6.tag K) ≠ 1 := by
  have hfixed := CFSG.HardMathSupport.C14ExcBridgeTwE6.twisted_fixed_eq_map (n := n)
    hn hK σ hσ (ggFrobT n) (ggFrobT_apply n)
  have hu_mem : baseChangeGL (algebraMap K GGL) (y : ModGL TwistTag.E6.tag K) ∈
      (twInndiagGroup K σ).map (baseChangeGL (algebraMap K GGL)) := ⟨y, y.2, rfl⟩
  rw [← hfixed] at hu_mem
  refine ⟨hu_mem.1, hu_mem.2, ?_, ?_⟩
  · rw [← map_pow, hyp, map_one]
  · intro h1
    apply hyne
    have h2 : baseChangeGL (algebraMap K GGL) (y : ModGL TwistTag.E6.tag K) =
        baseChangeGL (algebraMap K GGL) (1 : ModGL TwistTag.E6.tag K) := by
      rw [map_one]
      exact h1
    exact Subtype.ext (baseChangeGL_injective (algebraMap K GGL) h2)

private theorem k0LangMark_tw_kac
    {lab : LargeEvenLabel} {p : ℕ} (hpair : GGKacExcPair lab p)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ lab.n) ^ 2)
    (hT : ggKacTypeOfLabel lab = some (.E6, true))
    {u : ModGL (absTag .E6) GGL} (hu : u ∈ adjointGroup TwistTag.E6.tag GGL)
    (huF : twistHom TwistTag.E6 GGL (ggFrobT lab.n) u = u) (hup : u ^ p = 1)
    {ζ : GGLˣ} (hζ : orderOf ζ = p) :
    ∃ (row : KacRow lab p) (_ : row.T = .E6) (g : ModGL (absTag .E6) GGL)
      (μ : Fin (absTag .E6).rank → ℤ) (w : WeylGroup (absTag .E6))
      (nodeMap : (Fin row.diagram.marks.length → ℤ) →ₗ[ℤ] (Fin (absTag .E6).rank → ℤ))
      (frobLinear : (Fin (absTag .E6).rank → ℤ) ≃ₗ[ℤ] (Fin (absTag .E6).rank → ℤ)),
      let F : ModGL (absTag .E6) GGL →* ModGL (absTag .E6) GGL :=
        twistHom TwistTag.E6 GGL (ggFrobT lab.n)
      g ∈ adjointGroup TwistTag.E6.tag GGL ∧
      g⁻¹ * u * g = rootDiagUnit (absTag .E6) (fun i => ζ ^ μ i) ∧
      g⁻¹ * F g = canonicalRep (coxeterSystem (absTag .E6)) GGL w ∧
      Function.Surjective nodeMap ∧
      nodeMap.ker = Submodule.span ℤ
        ({fun i : Fin row.diagram.marks.length => (row.diagram.marks.getD i.val 0 : ℤ)} :
          Set (Fin row.diagram.marks.length → ℤ)) ∧
      (∀ i, IsRoot (absTag .E6) (nodeMap (Pi.single i 1))) ∧
      (∀ i : Fin row.diagram.marks.length,
        rootChar (fun j => ζ ^ μ j) (nodeMap (Pi.single i 1)) = ζ ^ (row.s.getD i.val 0)) ∧
      Submodule.span ℤ (kernelRoots (rootCharHom (fun j => ζ ^ μ j))) =
        Submodule.span ℤ {γ | ∃ i : Fin row.diagram.marks.length,
          row.s.getD i.val 0 = 0 ∧ γ = nodeMap (Pi.single i 1)} ∧
      (∀ γ, IsRoot (absTag .E6) γ → frobLinear γ = w •
        ((LinearEquiv.funCongrLeft ℤ ℤ TwistTag.E6.perm.symm :
          (Fin (absTag .E6).rank → ℤ) ≃ₗ[ℤ] (Fin (absTag .E6).rank → ℤ)) γ)) ∧
      (∀ i : Fin row.diagram.marks.length, frobLinear (nodeMap (Pi.single i 1)) =
        (if row.d = 1 then 1 else -1 : ℤ) • nodeMap (Pi.single (row.nodePerm i) 1)) ∧
      ∀ (i : Fin row.diagram.marks.length) (j : Fin (absTag .E6).rank), i.val = j.val + 1 →
        nodeMap (Pi.single i 1) = Pi.single j 1 := by
  classical
  have hp : p.Prime := hpair.1
  have hp2 : p ≠ 2 := hpair.2.1
  have hn : 1 ≤ lab.n := by
    have h2 : 2 ≤ Nat.card K := Finite.one_lt_card
    rw [hK] at h2
    rcases Nat.eq_zero_or_pos lab.n with h | h
    · rw [h] at h2
      norm_num at h2
    · exact h
  let π₀ : (Fin TwistTag.E6.tag.rank → ℤ) ≃ₗ[ℤ] (Fin TwistTag.E6.tag.rank → ℤ) :=
    LinearEquiv.funCongrLeft ℤ ℤ TwistTag.E6.perm.symm
  have hπ₀ : ∀ v, π₀ v = permLattice TwistTag.E6.perm v := fun v => rfl
  let ε : ℤ := if p ∣ 2 ^ lab.n - 1 then 1 else -1
  have hε : ε = 1 ∨ ε = -1 := by
    dsimp only [ε]
    split_ifs <;> norm_num
  have hq : (p : ℤ) ∣ 2 ^ lab.n - ε := by
    simpa [ε] using k0_eps_dvd (lab := lab) (p := p) hpair
  have h0 := CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_lang_alcove_normal_twE6
    (K := k0Kac .E6) (L := GGL) (k0Kac_facts .E6) (k0Kac_hup .E6) (k0Kac_hdown .E6)
    (CFSG.LieType.Chevalley.algebraicClosure_isAlgebraic_zmod 2 (ZMod 2)) lab.n hn hp hp2 hε hq
    hζ hu huF hup
  have hF : ∀ v, twistHom TwistTag.E6 GGL (ggFrobT lab.n)
      (canonicalRep (coxeterSystem TwistTag.E6.tag) GGL v) =
      canonicalRep (coxeterSystem TwistTag.E6.tag) GGL (weylTwist TwistTag.E6 v) :=
    fun v => twistHom_canonicalRep (t := TwistTag.E6) (K := GGL) (σ := ggFrobT lab.n) v
  have hθ : ∀ (v : WeylGroup TwistTag.E6.tag) (γ : Fin TwistTag.E6.tag.rank → ℤ),
      weylTwist TwistTag.E6 v • π₀ γ = π₀ (v • γ) := by
    intro v γ
    rw [hπ₀ γ, hπ₀ (v • γ)]
    exact weylTwist_smul_permLattice (t := TwistTag.E6) v γ
  have hεd : ε = 1 ∧ (if p ∣ 2 ^ lab.n - 1 then 1 else 2) = 1 ∨
      ε = -1 ∧ (if p ∣ 2 ^ lab.n - 1 then 1 else 2) = 2 := by
    dsimp only [ε]
    split_ifs <;> simp
  have hrat : ∀ (w₁ : WeylGroup TwistTag.E6.tag) (rho : List ℕ),
      rho.Perm (List.range (k0DiagOf .E6).marks.length) →
      (∀ i, i < (k0DiagOf .E6).marks.length →
        (if p ∣ 2 ^ lab.n - 1 then (1 : ℤ) else -1) •
          (w₁ • π₀ ((k0Kac .E6).extRoot
            (CFSG.HardMathSupport.Timmesfeld.CrossChar.idxNode (r := (absTag .E6).rank) i))) =
          (k0Kac .E6).extRoot
            (CFSG.HardMathSupport.Timmesfeld.CrossChar.idxNode
              (r := (absTag .E6).rank) (rho.getD i 0))) →
      ∃ a ∈ (k0DiagOf .E6).omega,
        rho = k0pMul a (k0Rho0 (k0DiagOf .E6) true (if p ∣ 2 ^ lab.n - 1 then 1 else 2)) := by
    intro w₁ rho hrho hact
    refine k0_rat_twE6 hεd w₁ hrho ?_
    intro i hi
    exact hact i hi
  exact exists_k0KacPart_of hpair hT (twistHom TwistTag.E6 GGL (ggFrobT lab.n))
    (weylTwist TwistTag.E6) π₀ hF hθ hζ h0 hrat

private theorem k0LangMark_tw_diag
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {p : ℕ}
    {S : CFSG.HardMathSupport.Timmesfeld.LangTorus.LangSetup TwistTag.E6.tag GGL 5}
    {act : S.D.model →* MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)}
    {y : twInndiagGroup K σ} {g u : ModGL (absTag .E6) GGL}
    {μ : Fin (absTag .E6).rank → ℤ} {ζ : GGLˣ}
    (hζ : orderOf ζ = p) (hune : u ≠ 1)
    (hmem : g⁻¹ * u * g ∈ S.D.model)
    (hgu : g⁻¹ * u * g = rootDiagUnit (absTag .E6) (fun j => ζ ^ μ j))
    (hact_y : act ⟨g⁻¹ * u * g, hmem⟩ = twConj K σ y) :
    (∀ i, (fun j : Fin (absTag .E6).rank => ζ ^ μ j) i ^ p = 1) ∧
      rootDiagUnit TwistTag.E6.tag (fun j => ζ ^ μ j) ∈ S.D.torus ∧
      rootDiagUnit (absTag .E6) (fun j => ζ ^ μ j) ∈ S.D.model ∧
      rootDiagUnit (absTag .E6) (fun j => ζ ^ μ j) ≠ 1 ∧
      ∀ (h : rootDiagUnit (absTag .E6) (fun j => ζ ^ μ j) ∈ S.D.model),
        act ⟨rootDiagUnit (absTag .E6) (fun j => ζ ^ μ j), h⟩ = twConj K σ y := by
  have hζp : ζ ^ p = 1 := by
    rw [← hζ]
    exact pow_orderOf_eq_one ζ
  have ha_model : rootDiagUnit (absTag .E6) (fun j => ζ ^ μ j) ∈ S.D.model := by
    rw [← hgu]
    exact hmem
  have ha_torus : rootDiagUnit TwistTag.E6.tag (fun j => ζ ^ μ j) ∈ S.D.torus := by
    rw [CFSG.HardMathSupport.Timmesfeld.LangTorus.LangDatum.torus,
      CFSG.RankThree.PartOne.KE.mem_twistedTorusOf]
    exact ⟨rootDiagUnit_mem_torusGroup _,
      ((CFSG.HardMathSupport.Timmesfeld.LangTorus.LangDatum.mem_model S.D).1 ha_model).2⟩
  have ha_pow : ∀ i, (fun j : Fin (absTag .E6).rank => ζ ^ μ j) i ^ p = 1 := by
    intro i
    show (ζ ^ μ i) ^ p = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζp, one_zpow]
  have ha_ne : rootDiagUnit (absTag .E6) (fun j => ζ ^ μ j) ≠ 1 := by
    intro h1
    apply hune
    have h2 : g⁻¹ * u * g = 1 := hgu.trans h1
    calc u = g * (g⁻¹ * u * g) * g⁻¹ := by group
      _ = g * 1 * g⁻¹ := by rw [h2]
      _ = 1 := by group
  refine ⟨ha_pow, ha_torus, ha_model, ha_ne, ?_⟩
  intro h
  rw [← hact_y]
  congr 1
  exact Subtype.ext hgu.symm

private theorem k0LangMark_tw_mark
    {lab : LargeEvenLabel} {p : ℕ} {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    {y : twInndiagGroup K σ} {ζ : GGLˣ} (hζ : orderOf ζ = p)
    {row : KacRow lab p} (hrowT : row.T = .E6) (htw : row.tw = true)
    {S : CFSG.HardMathSupport.Timmesfeld.LangTorus.LangSetup TwistTag.E6.tag GGL 5} (hqS : S.D.q = 2 ^ lab.n)
    (hΦ : ∀ x, S.D.Φ x = twistHom TwistTag.E6 GGL (ggFrobT lab.n) x)
    {iota : graphFixedRootGroup TwistTag.E6 K σ.toRingHom →* ModGL TwistTag.E6.tag GGL}
    {act : S.D.model →* MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)}
    (hiota_inj : Function.Injective iota) (hiota_range : iota.range = S.Γ)
    (hact_inj : Function.Injective act) (hact_range : Set.range act = Set.range (twConj K σ))
    (hcompat : ∀ x r, iota (act x r) =
      (x : ModGL TwistTag.E6.tag GGL) * iota r * (x : ModGL TwistTag.E6.tag GGL)⁻¹)
    {μ : Fin (absTag .E6).rank → ℤ} {w : WeylGroup (absTag .E6)}
    {nodeMap : (Fin row.diagram.marks.length → ℤ) →ₗ[ℤ] (Fin (absTag .E6).rank → ℤ)}
    {frobLinear : (Fin (absTag .E6).rank → ℤ) ≃ₗ[ℤ] (Fin (absTag .E6).rank → ℤ)}
    (hsurj : Function.Surjective nodeMap)
    (hker : nodeMap.ker = Submodule.span ℤ
      ({fun i : Fin row.diagram.marks.length => (row.diagram.marks.getD i.val 0 : ℤ)} :
        Set (Fin row.diagram.marks.length → ℤ)))
    (hroot : ∀ i, IsRoot (absTag .E6) (nodeMap (Pi.single i 1)))
    (heval : ∀ i : Fin row.diagram.marks.length,
      rootChar (fun j => ζ ^ μ j) (nodeMap (Pi.single i 1)) = ζ ^ (row.s.getD i.val 0))
    (hspan : Submodule.span ℤ (kernelRoots (rootCharHom (fun j => ζ ^ μ j))) =
      Submodule.span ℤ {γ | ∃ i : Fin row.diagram.marks.length,
        row.s.getD i.val 0 = 0 ∧ γ = nodeMap (Pi.single i 1)})
    (hfr : ∀ γ : Fin (absTag .E6).rank → ℤ, IsRoot (absTag .E6) γ → frobLinear γ = w •
      ((LinearEquiv.funCongrLeft ℤ ℤ TwistTag.E6.perm.symm :
        (Fin (absTag .E6).rank → ℤ) ≃ₗ[ℤ] (Fin (absTag .E6).rank → ℤ)) γ))
    (hρ : ∀ γ : Fin (absTag .E6).rank → ℤ, IsRoot (absTag .E6) γ → S.ρ γ = w •
      ((LinearEquiv.funCongrLeft ℤ ℤ TwistTag.E6.perm.symm :
        (Fin (absTag .E6).rank → ℤ) ≃ₗ[ℤ] (Fin (absTag .E6).rank → ℤ)) γ))
    (hnodes : ∀ i : Fin row.diagram.marks.length, frobLinear (nodeMap (Pi.single i 1)) =
      (if row.d = 1 then 1 else -1 : ℤ) • nodeMap (Pi.single (row.nodePerm i) 1))
    (hstd : ∀ (i : Fin row.diagram.marks.length) (j : Fin (absTag .E6).rank),
      i.val = j.val + 1 → nodeMap (Pi.single i 1) = Pi.single j 1)
    (ha_pow : ∀ i, (fun j : Fin (absTag .E6).rank => ζ ^ μ j) i ^ p = 1)
    (ha_torus : rootDiagUnit TwistTag.E6.tag (fun j => ζ ^ μ j) ∈ S.D.torus)
    (ha_model : rootDiagUnit (absTag .E6) (fun j => ζ ^ μ j) ∈ S.D.model)
    (ha_ne : rootDiagUnit (absTag .E6) (fun j => ζ ^ μ j) ≠ 1)
    (hact : act ⟨rootDiagUnit (absTag .E6) (fun j => ζ ^ μ j), ha_model⟩ = twConj K σ y) :
    Nonempty (K0LangMark GGL lab p (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)
      (Set.range (twConj K σ)) (twConj K σ y)) := by
  let A : K0LangMark GGL lab p (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)
      (Set.range (twConj K σ)) (twConj K σ y) :=
    { row := row
      tau := TwistTag.E6.tag
      tau_eq := by rw [hrowT]; rfl
      setup := S
      q_eq := hqS
      fr := ggFrobT lab.n
      fr_eq := ggFrobT_apply lab.n
      phi_split := fun h => absurd h (by rw [htw]; decide)
      phi_twisted := fun _ => ⟨rfl, fun g => (hΦ g).trans rfl⟩
      iota := iota
      iota_inj := hiota_inj
      iota_range := hiota_range
      modelAction := act
      modelAction_inj := hact_inj
      modelAction_range := hact_range
      modelAction_compat := hcompat
      a := fun j => ζ ^ μ j
      a_pow := ha_pow
      a_torus := ha_torus
      a_model := ha_model
      a_ne := ha_ne
      action_eq := hact
      zeta := ζ
      zeta_order := hζ
      nodeMap := nodeMap
      nodeMap_surj := hsurj
      nodeMap_ker := hker
      node_isRoot := hroot
      node_eval := heval
      kernel_span_eq := hspan
      epsilon := if row.d = 1 then 1 else -1
      epsilon_eq := rfl
      frobLinear := frobLinear
      frob_roots := fun v hv => (hfr v hv).trans (hρ v hv).symm
      frob_nodes := hnodes
      node_std := hstd }
  exact ⟨A⟩

theorem k0LangMark_tw_nonempty
    {lab : LargeEvenLabel} {p : ℕ} (hpair : GGKacExcPair lab p) (htag : lab.tag = .twE6)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (2 ^ lab.n) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (2 ^ lab.n)) (y : twInndiagGroup K σ)
    (hy : orderOf (twConj K σ y) = p) :
    Nonempty (K0LangMark GGL lab p (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)
      (Set.range (twConj K σ)) (twConj K σ y)) := by
  classical
  have hp : p.Prime := hpair.1
  have hp2 : p ≠ 2 := hpair.2.1
  obtain ⟨hn, hyord, hyp, hyne⟩ := k0LangMark_tw_y_facts hpair hK σ hσ y hy
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := by
    have hcard : Fintype.card K = 2 ^ (lab.n * 2) := by
      rw [← Nat.card_eq_fintype_card, hK, pow_mul]
    exact charP_of_card_eq_prime_pow (p := 2) (f := lab.n * 2) hcard
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  let : Algebra K GGL := (IsAlgClosed.lift : K →ₐ[ZMod 2] GGL).toRingHom.toAlgebra
  let u : ModGL (absTag .E6) GGL :=
    baseChangeGL (algebraMap K GGL) (y : ModGL TwistTag.E6.tag K)
  obtain ⟨hu, huF, hup, hune⟩ := k0LangMark_tw_u_facts (n := lab.n) hn hK σ hσ y hyp hyne
  obtain ⟨ζ, hζ⟩ := exists_zeta GGL hp hp2
  have hT : ggKacTypeOfLabel lab = some (.E6, true) := by
    obtain ⟨t, l, n⟩ := lab
    cases htag
    rfl
  obtain ⟨row, hrowT, g, μ, w, nodeMap, frobLinear, hg, hgu, hgw, hsurj, hker, hroot, heval,
    hspan, hfr, hnodes, hstd⟩ :=
    k0LangMark_tw_kac hpair hK hT hu huF hup hζ
  have hgw' : twistHom TwistTag.E6 GGL (ggFrobT lab.n) g =
      g * canonicalRep (coxeterSystem (absTag .E6)) GGL w :=
    (inv_mul_eq_iff_eq_mul).1 hgw
  obtain ⟨S, iota, act, hmem, hqS, hΦ, -, hiota_inj, hiota_range, hact_inj, hact_range,
    hcompat, hact_y, hρ⟩ := exists_k0LangModel_tw (n := lab.n) hn hK σ hσ hg hgw'
  have htw : row.tw = true := by
    have h2 : (row.T, row.tw) = (.E6, true) := by
      rw [← Option.some.injEq]
      exact row.type_eq.symm.trans hT
    exact (Prod.ext_iff.1 h2).2
  obtain ⟨ha_pow, ha_torus, ha_model, ha_ne, hact⟩ :=
    k0LangMark_tw_diag hζ hune (hmem y) hgu (hact_y y)
  exact k0LangMark_tw_mark hζ hrowT htw hqS hΦ hiota_inj hiota_range hact_inj hact_range
    hcompat hsurj hker hroot heval hspan hfr hρ hnodes hstd ha_pow ha_torus ha_model ha_ne
    (hact ha_model)

theorem k0LangMark_hA_tw :
    ∀ p : ℕ, ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → GGKacExcPair lab p →
      lab.tag = .twE6 → LargeEvenLabelAll lab (fun R _ I _ => ∀ phi : MulAut R, phi ∈ I →
        orderOf phi = p → Nonempty (K0LangMark GGL lab p R I phi)) := by
  intro p lab _ hpair htag
  exact largeEvenLabelAll_k0LangMark_tw htag fun K _ _ hK σ hσ y hy =>
    k0LangMark_tw_nonempty hpair htag K hK σ hσ y hy

end CFSG.StandardType.GGK0MarkedKacIface1587

end
