module

public import CFSG.LocalAnalysis.StandardType.GGExcReflTBWeylDatum
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepNine
import CFSG.LocalAnalysis.StandardType.GGReflClosedOfWeyl
import CFSG.LocalAnalysis.StandardType.GGSecFiveRootRefl

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] noncomputable def ggReflSpan {p : ℕ} [Fact p.Prime] {G : Type} [Group G]
    (Bs L : Subgroup G) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ιV : Additive ↥Bs ≃+ V) : Submodule (ZMod p) V :=
  ⨆ φ : {φ : MulAut ↥Bs // φ ∈ ggAutomizer L Bs ∧ GGIsReflection p φ},
    LinearMap.range ((ggLin (p := p) ιV φ.1 : V →ₗ[ZMod p] V) - LinearMap.id)

theorem ggExcReflTBWeylDatum_of_weylOfType {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {G : Type}
    [Group G] [Finite G] {Bs L J : Subgroup G} (hNT : GGNoTransvection p Bs) {Λ : Type}
    [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ}
    (hM : GGIsWeylMatrix M) (h3 : 3 ≤ Fintype.card Λ) {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C)
    (hno6 : ∀ i j, M i j ≠ 6) (par : Λ → Λ) (root : Λ) (depth : Λ → ℕ)
    (hpar : ∀ i j, i ≠ j → (C i j ≠ 0 ↔ ((i ≠ root ∧ par i = j) ∨ (j ≠ root ∧ par j = i))))
    (hdepth : ∀ i, i ≠ root → depth (par i) < depth i)
    (hW : GGWeylOfType p M (ggAutomizer L Bs)) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ιV : Additive ↥Bs ≃+ V)
    (htb : Module.finrank (ZMod p) V ≤ Module.finrank (ZMod p) (ggReflSpan (p := p) Bs L ιV) + 1 ∨
      Module.finrank (ZMod p) (ggFixedSubmodule (p := p) ιV (ggAutNormalClosure L J Bs)) ≤ 1) :
    Nonempty (GGExcReflTBWeylDatum p Bs L J) := by
  classical
  have hind : ∀ φ ∈ ggAutomizer L Bs, φ ∈ ggInduced ⊤ Bs :=
    fun φ hφ => mem_ggInduced_top_of_mem_ggAutomizer hφ
  obtain ⟨e, h, α, hα, hrefl, hpair⟩ :=
    SecFiveRootRefl.exists_cartan_pairing_of_weylOfType' (p := p) hp2 hNT hC hno6 par root depth
      hpar hdepth hW hind ιV
  let φ : Λ → MulAut ↥Bs := fun i => ((e (M.simple i) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs)
  have hsimple_apply : ∀ i w, ggLin (p := p) ιV (φ i) w = w - α i w • h i :=
    fun i w => by rw [hrefl i]; exact Module.reflection_apply w (hα i)
  have hmap : ((Subgroup.subtype (ggAutomizer L Bs)).comp e.toMonoidHom) '' Set.range M.simple =
      Set.range φ := by
    ext x
    constructor
    · rintro ⟨w, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨M.simple i, ⟨i, rfl⟩, rfl⟩
  have hfr : ((Subgroup.subtype (ggAutomizer L Bs)).comp e.toMonoidHom).range =
      ggAutomizer L Bs := by
    ext x
    constructor
    · rintro ⟨m, rfl⟩
      exact (e m).2
    · intro hx
      obtain ⟨m, hm⟩ := e.surjective ⟨x, hx⟩
      exact ⟨m, congrArg Subtype.val hm⟩
  have hsimple_eq : (M.toCoxeterSystem).simple = M.simple := by
    funext i
    rw [CoxeterMatrix.toCoxeterSystem_simple]
  have hsimple_range : Set.range M.simple = Set.range (M.toCoxeterSystem).simple := by
    rw [hsimple_eq]
  have hAL : ggAutomizer L Bs = Subgroup.closure (Set.range φ) := by
    have hc : Subgroup.closure (Set.range φ) = ggAutomizer L Bs := by
      rw [← hmap, ← MonoidHom.map_closure, hsimple_range,
        (M.toCoxeterSystem).subgroup_closure_range_simple, Subgroup.map_top, hfr]
    exact hc.symm
  have hfin : Finite V := Finite.of_equiv (Additive ↥Bs) ιV.toEquiv
  have hmodfin : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hspan : ggReflSpan (p := p) Bs L ιV ≤ Submodule.span (ZMod p) (Set.range h) := by
    rw [ggReflSpan]
    refine iSup_le fun q => ?_
    rintro v ⟨w, rfl⟩
    exact ggAutomizer_sub_mem_span (p := p) hsimple_apply hAL q.2.1 w
  have htb' : Module.finrank (ZMod p) V ≤
      Module.finrank (ZMod p) (Submodule.span (ZMod p) (Set.range h)) + 1 ∨
      Module.finrank (ZMod p)
        (ggFixedSubmodule (p := p) ιV (ggAutNormalClosure L J Bs)) ≤ 1 := by
    rcases htb with hcodim | hline
    · exact Or.inl (le_trans hcodim (add_le_add (Submodule.finrank_mono hspan) le_rfl))
    · exact Or.inr hline
  have _hRC : GGReflConjSimple p (ggAutomizer L Bs) φ :=
    ggReflConjSimple_of_weylMatrix hp2 (hM : GGIsWeylMatrixFixed M) h3 hC ιV φ h α hpair
      hsimple_apply hAL
  first
    | exact ⟨Λ, M, C, V, ιV, φ, h, α, hM, hC, h3, hpair, hsimple_apply, hAL, htb'⟩
    | exact ⟨Λ, M, C, V, ιV, φ, h, α, hM, hC, h3, hpair, hsimple_apply, hAL, htb', _hRC⟩

end CFSG.StandardType

end
