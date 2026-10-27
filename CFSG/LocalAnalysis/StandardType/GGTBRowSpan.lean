module

public import CFSG.LocalAnalysis.StandardType.GGExcReflTBWeylDatum
public import CFSG.LocalAnalysis.StandardType.GGExcReflTBWeylDatumOfWeyl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRootRefl

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggReflSpan_card_le_finrank_of_weylOfType {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {G : Type}
    [Group G] [Finite G] {Bs L : Subgroup G} (hNT : GGNoTransvection p Bs) {Λ : Type}
    [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C)
    (hno6 : ∀ i j, M i j ≠ 6) (par : Λ → Λ) (root : Λ) (depth : Λ → ℕ)
    (hpar : ∀ i j, i ≠ j → (C i j ≠ 0 ↔ ((i ≠ root ∧ par i = j) ∨ (j ≠ root ∧ par j = i))))
    (hdepth : ∀ i, i ≠ root → depth (par i) < depth i) (hdet : ((C.det : ℤ) : ZMod p) ≠ 0)
    (hW : GGWeylOfType p M (ggAutomizer L Bs)) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ιV : Additive ↥Bs ≃+ V) :
    Fintype.card Λ ≤ Module.finrank (ZMod p) (ggReflSpan (p := p) Bs L ιV) := by
  classical
  have hind : ∀ φ ∈ ggAutomizer L Bs, φ ∈ ggInduced ⊤ Bs :=
    fun φ hφ => mem_ggInduced_top_of_mem_ggAutomizer hφ
  obtain ⟨e, h, α, hα, hrefl, hpair⟩ :=
    SecFiveRootRefl.exists_cartan_pairing_of_weylOfType' (p := p) hp2 hNT hC hno6 par root
      depth hpar hdepth hW hind ιV
  let φ : Λ → MulAut ↥Bs := fun i => ((e (M.simple i) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs)
  have hdet' : (Matrix.of fun i j => α i (h j)).det ≠ 0 := by
    have hmat : (Matrix.of fun i j => α i (h j)) = C.map (Int.castRingHom (ZMod p)) := by
      ext i j
      exact hpair i j
    rw [hmat]
    change (((Int.castRingHom (ZMod p)).mapMatrix C).det) ≠ 0
    rw [← RingHom.map_det]
    simpa using hdet
  have hindep : LinearIndependent (ZMod p) h :=
    linearIndependent_of_det_ne_zero (K := ZMod p) h α hdet'
  have hmem : ∀ i, h i ∈ ggReflSpan (p := p) Bs L ιV := by
    intro i
    have hφi : φ i ∈ ggAutomizer L Bs := (e (M.simple i)).2
    have hrefli : GGIsReflection p (φ i) :=
      ggIsReflection_of_eq_reflection hp2 ιV (hα i) (hrefl i)
    have hrange : h i ∈ LinearMap.range
        ((ggLin (p := p) ιV (φ i) : V →ₗ[ZMod p] V) - LinearMap.id) := by
      refine ⟨(2 : ZMod p)⁻¹ • (-h i), ?_⟩
      have hself : ((ggLin (p := p) ιV (φ i) : V →ₗ[ZMod p] V)) (h i) = -h i := by
        change (ggLin (p := p) ιV (φ i)) (h i) = -h i
        rw [hrefl i]
        exact Module.reflection_apply_self (hα i)
      have h1 : ((ggLin (p := p) ιV (φ i) : V →ₗ[ZMod p] V) -
            (LinearMap.id : V →ₗ[ZMod p] V)) (-h i) = (2 : ZMod p) • h i := by
        rw [LinearMap.sub_apply, LinearMap.id_apply, map_neg, hself, neg_neg, sub_neg_eq_add,
          ← two_smul (ZMod p) (h i)]
      rw [map_smul (f := ((ggLin (p := p) ιV (φ i) : V →ₗ[ZMod p] V) -
        (LinearMap.id : V →ₗ[ZMod p] V))), h1, smul_smul,
        inv_mul_cancel₀ (zmod_two_ne_zero hp2), one_smul]
    rw [ggReflSpan]
    exact le_iSup (fun q : {φ : MulAut ↥Bs // φ ∈ ggAutomizer L Bs ∧ GGIsReflection p φ} =>
      LinearMap.range ((ggLin (p := p) ιV q.1 : V →ₗ[ZMod p] V) - LinearMap.id))
      ⟨φ i, hφi, hrefli⟩ hrange
  have hspan_le : Submodule.span (ZMod p) (Set.range h) ≤ ggReflSpan (p := p) Bs L ιV :=
    Submodule.span_le.mpr fun v hv => by
      obtain ⟨i, rfl⟩ := hv
      exact hmem i
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ιV.toEquiv
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  calc Fintype.card Λ
      = Module.finrank (ZMod p) (Submodule.span (ZMod p) (Set.range h)) :=
        (finrank_span_eq_card hindep).symm
    _ ≤ Module.finrank (ZMod p) (ggReflSpan (p := p) Bs L ιV) :=
        Submodule.finrank_mono hspan_le

end CFSG.StandardType

end
