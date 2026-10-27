module

public import CFSG.LocalAnalysis.StandardType.GGFinModelRat
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangPow
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
import CFSG.LocalAnalysis.StandardType.GGLangUniform
import CFSG.LocalAnalysis.StandardType.GGL45NtExcBridgeE6
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigidSplit
import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcRoots
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangInj
import CFSG.LieType.Chevalley.SingleEdgePerfect
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwLangConsumers
import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanDiagOuterE6Adj
import CFSG.LocalAnalysis.AGLEmbedding.SporadicData
import CFSG.RankThree.PartOne.K133H.G2Plane

public section

namespace CFSG.StandardType.GGK0MarkedKacIface1587

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.StandardType.GGFinModel CFSG.StandardType.RecipeExcLang

theorem isAlgClosure_ggl (K : Type) [Field K] [Finite K] [Algebra K GGL] [CharP K 2] :
    IsAlgClosure K GGL := by
  have : Algebra (ZMod 2) K := ZMod.algebra K 2
  have : IsScalarTower (ZMod 2) K GGL :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
  exact { isAlgClosed := inferInstance
          isAlgebraic := Algebra.IsAlgebraic.tower_top (K := ZMod 2) (L := K) }

theorem exists_model_mulEquiv_of
    {τ : Tag} {K : Type} [Field K] [Algebra K GGL]
    (S : LangSetup τ GGL 5) {g : ModGL τ GGL} {Δ : Subgroup (ModGL τ K)}
    (hmodel : ∀ x : ModGL τ GGL, x ∈ S.D.model ↔ ∃ y : Δ,
      x = g⁻¹ * baseChangeGL (algebraMap K GGL) (y : ModGL τ K) * g) :
    ∃ ψ : Δ ≃* S.D.model, ∀ y,
      (ψ y : ModGL τ GGL) = g⁻¹ * baseChangeGL (algebraMap K GGL) (y : ModGL τ K) * g := by
  classical
  let φ : Δ →* S.D.model :=
    { toFun := fun y => ⟨g⁻¹ * baseChangeGL (algebraMap K GGL) (y : ModGL τ K) * g,
        (hmodel _).2 ⟨y, rfl⟩⟩
      map_one' := Subtype.ext (by
        show g⁻¹ * baseChangeGL (algebraMap K GGL) ((1 : Δ) : ModGL τ K) * g = 1
        rw [show ((1 : Δ) : ModGL τ K) = 1 from rfl, map_one]
        group)
      map_mul' := fun a b => Subtype.ext (by
        show g⁻¹ * baseChangeGL (algebraMap K GGL) ((a * b : Δ) : ModGL τ K) * g =
          (g⁻¹ * baseChangeGL (algebraMap K GGL) (a : ModGL τ K) * g) *
            (g⁻¹ * baseChangeGL (algebraMap K GGL) (b : ModGL τ K) * g)
        rw [show ((a * b : Δ) : ModGL τ K) = (a : ModGL τ K) * (b : ModGL τ K) from rfl, map_mul]
        group) }
  have hφinj : Function.Injective φ := by
    intro a b hab
    have h : g⁻¹ * baseChangeGL (algebraMap K GGL) (a : ModGL τ K) * g =
        g⁻¹ * baseChangeGL (algebraMap K GGL) (b : ModGL τ K) * g :=
      congrArg (fun z : S.D.model => (z : ModGL τ GGL)) hab
    apply Subtype.ext
    refine baseChangeGL_injective (algebraMap K GGL) ?_
    calc baseChangeGL (algebraMap K GGL) (a : ModGL τ K)
        = g * (g⁻¹ * baseChangeGL (algebraMap K GGL) (a : ModGL τ K) * g) * g⁻¹ := by group
      _ = g * (g⁻¹ * baseChangeGL (algebraMap K GGL) (b : ModGL τ K) * g) * g⁻¹ := by rw [h]
      _ = baseChangeGL (algebraMap K GGL) (b : ModGL τ K) := by group
  have hφsurj : Function.Surjective φ := by
    intro x
    obtain ⟨y, hy⟩ := (hmodel x).1 x.2
    have hφy : (φ y : ModGL τ GGL) = (x : ModGL τ GGL) := by
      show g⁻¹ * baseChangeGL (algebraMap K GGL) (y : ModGL τ K) * g = (x : ModGL τ GGL)
      rw [hy]
    exact ⟨y, Subtype.ext hφy⟩
  exact ⟨MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩, fun y => rfl⟩

theorem exists_langModel_action_of
    {τ : Tag} {K : Type} [Field K] [Algebra K GGL]
    (S : LangSetup τ GGL 5) {g : ModGL τ GGL} {Δ : Subgroup (ModGL τ K)} {C : Type} [Group C]
    (e : C →* ModGL τ K) (c : Δ →* MulAut C) (hinj : Function.Injective c)
    (hc : ∀ (y : Δ) (r : C), e (c y r) = (y : ModGL τ K) * e r * (y : ModGL τ K)⁻¹)
    (ι : C →* ModGL τ GGL)
    (hmodel : ∀ x : ModGL τ GGL, x ∈ S.D.model ↔ ∃ y : Δ,
      x = g⁻¹ * baseChangeGL (algebraMap K GGL) (y : ModGL τ K) * g)
    (hιeq : ∀ r : C, ι r = g⁻¹ * baseChangeGL (algebraMap K GGL) (e r) * g) :
    ∃ (act : S.D.model →* MulAut C)
      (hmem : ∀ y : Δ, g⁻¹ * baseChangeGL (algebraMap K GGL) (y : ModGL τ K) * g ∈ S.D.model),
      Function.Injective act ∧ Set.range (fun x => act x) = Set.range c ∧
      (∀ x r, ι (act x r) = (x : ModGL τ GGL) * ι r * (x : ModGL τ GGL)⁻¹) ∧
      (∀ y, act ⟨_, hmem y⟩ = c y) := by
  classical
  obtain ⟨ψ, hψ⟩ := exists_model_mulEquiv_of S hmodel
  let hmem : ∀ y : Δ, g⁻¹ * baseChangeGL (algebraMap K GGL) (y : ModGL τ K) * g ∈ S.D.model :=
    fun y => (hmodel _).2 ⟨y, rfl⟩
  let act : S.D.model →* MulAut C := c.comp ψ.symm.toMonoidHom
  refine ⟨act, hmem, hinj.comp ψ.symm.injective, ?_, ?_, ?_⟩
  · ext χ
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨ψ.symm x, rfl⟩
    · rintro ⟨y, rfl⟩
      refine ⟨ψ y, ?_⟩
      change act (ψ y) = c y
      rw [show act (ψ y) = c (ψ.symm (ψ y)) from rfl, MulEquiv.symm_apply_apply]
  · intro x r
    have hx : (x : ModGL τ GGL) = g⁻¹ * baseChangeGL (algebraMap K GGL)
        ((ψ.symm x : Δ) : ModGL τ K) * g := by
      rw [← hψ (ψ.symm x), ψ.apply_symm_apply]
    have hact : act x = c (ψ.symm x) := rfl
    simp only [hact, hιeq, hx, hc, map_mul, map_inv]
    group
  · intro y
    have h : ψ y = (⟨g⁻¹ * baseChangeGL (algebraMap K GGL) (y : ModGL τ K) * g, hmem y⟩ :
        S.D.model) := Subtype.ext (hψ y)
    rw [show act ⟨_, hmem y⟩ = c (ψ.symm ⟨_, hmem y⟩) from rfl, ← h, ψ.symm_apply_apply]

theorem exists_k0LangModel
    {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] [Algebra K GGL] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) {w : WeylGroup τ} {g : ModGL τ GGL}
    (hg : g ∈ adjointGroup τ GGL)
    (hgw : Units.map (entrywiseHom (ggFrobT n)) g = g * canonicalRep (coxeterSystem τ) GGL w) :
    ∃ (S : LangSetup τ GGL 5) (iota : adjointGroup τ K →* ModGL τ GGL)
      (act : S.D.model →* MulAut (adjointGroup τ K))
      (hmem : ∀ y : inndiagGroup τ K,
        g⁻¹ * baseChangeGL (algebraMap K GGL) (y : ModGL τ K) * g ∈ S.D.model),
      S.D.q = 2 ^ n ∧ (∀ x, S.D.Φ x = Units.map (entrywiseHom (ggFrobT n)) x) ∧
      S.D.n = canonicalRep (coxeterSystem τ) GGL w ∧
      Function.Injective iota ∧ iota.range = S.Γ ∧
      Function.Injective act ∧ Set.range (fun x => act x) = Set.range (inndiagConj τ K) ∧
      (∀ x r, iota (act x r) = (x : ModGL τ GGL) * iota r * (x : ModGL τ GGL)⁻¹) ∧
      (∀ y, act ⟨_, hmem y⟩ = inndiagConj τ K y) ∧
      ∀ γ, IsRoot τ γ → S.ρ γ = w • γ := by
  classical
  have : CharP K 2 := RingHom.charP (algebraMap K GGL) (algebraMap K GGL).injective 2
  have : IsAlgClosure K GGL := isAlgClosure_ggl K
  have hFr : ∀ c : GGL, ggFrobT n c = c ^ Nat.card K := fun c => by rw [ggFrobT_apply, hK]
  let D : LangDatum τ GGL :=
    LangDatum.ofFrobenius (ggFrobT n) (2 ^ n) (ggFrobT_apply n) w hg hgw
  let ι₀ : adjointGroup τ K →* ModGL τ GGL :=
    (baseChangeGL (algebraMap K GGL)).comp (adjointGroup τ K).subtype
  have hperf : commutator ↥(adjointGroup τ K) = ⊤ :=
    single_edge_perfect τ K (hτ.elim Or.inl fun h => Or.inr (Or.inr h))
  have hdesc : LangDescent D 7 ι₀ := by
    rcases hτ with h | h | h | h
    · exact langDescent_exact (Or.inr h) hFr D rfl hperf
    · exact langDescent_untw 3 (Or.inl ⟨h, rfl⟩) hFr D rfl Nat.prime_seven (by norm_num) hperf
    · exact langDescent_untw 2 (Or.inr (Or.inl ⟨h, rfl⟩)) hFr D rfl Nat.prime_seven (by norm_num)
        hperf
    · exact langDescent_untw 1 (Or.inr (Or.inr ⟨h, rfl⟩)) hFr D rfl Nat.prime_seven (by norm_num)
        hperf
  obtain ⟨S, ι, hSD, hιeq, hιinj, hιrange, -⟩ :=
    CFSG.StandardType.LangRat.exists_langSetup_of_toral_datum_uniform (τ := τ) (L := GGL)
      (ℓ := 2) (f := n) Nat.prime_two hn D rfl Nat.prime_five (by norm_num) (Or.inl le_rfl)
      hdesc.finite_model ι₀
      ((baseChangeGL_injective (algebraMap K GGL)).comp (Subgroup.subtype_injective _))
      hdesc.Γ_eq
  have hq : S.D.q = 2 ^ n := by rw [hSD]; rfl
  have hΦf : S.D.Φ = Units.map (entrywiseHom (ggFrobT n)) := by rw [hSD]; rfl
  have hΦ : ∀ x, S.D.Φ x = Units.map (entrywiseHom (ggFrobT n)) x := fun x => by rw [hΦf]
  have hn' : S.D.n = canonicalRep (coxeterSystem τ) GGL w := by rw [hSD]; rfl
  have hDg0 : D.g0 = g := rfl
  have hfix : D.fix = (inndiagGroup τ K).map (baseChangeGL (algebraMap K GGL)) := by
    show adjointGroup τ GGL ⊓ (Units.map (entrywiseHom (ggFrobT n))).eqLocus (MonoidHom.id _) =
      (inndiagGroup τ K).map (baseChangeGL (algebraMap K GGL))
    exact CFSG.HardMathSupport.C14ExcBridgeE6.fixed_eq_map_inndiag (τ := τ) (K := K) (L := GGL)
      (ggFrobT n) hFr (iterateFrobeniusEquiv GGL 2 n).bijective
  have hmodel : ∀ x : ModGL τ GGL, x ∈ S.D.model ↔ ∃ y : inndiagGroup τ K,
      x = g⁻¹ * baseChangeGL (algebraMap K GGL) (y : ModGL τ K) * g := by
    intro x
    rw [hSD, LangDescent.model_eq, hfix, Subgroup.map_map, hDg0]
    constructor
    · rintro ⟨y, hy, hxy⟩
      exact ⟨⟨y, hy⟩, by simpa [MulAut.conj_apply] using hxy.symm⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, y.2, by simp⟩
  have hρ : ∀ γ, IsRoot τ γ → S.ρ γ = w • γ := by
    intro γ hγ
    exact S.rho_eq_smul_of_frob (Fr := ggFrobT n) (fun c => by rw [hq, ggFrobT_apply])
      hΦf hn' hγ
  obtain ⟨act, hmem, hactinj, hactrange, hactcompat, hacteq⟩ :=
    exists_langModel_action_of S (adjointGroup τ K).subtype (inndiagConj τ K)
      (inndiagConj_injective_of_card_eq_two_pow hK) (fun y r => coe_inndiagConj y r) ι hmodel hιeq
  exact ⟨S, ι, act, hmem, hq, hΦ, hn', hιinj, hιrange, hactinj, hactrange, hactcompat, hacteq,
    hρ⟩

end CFSG.StandardType.GGK0MarkedKacIface1587

end
