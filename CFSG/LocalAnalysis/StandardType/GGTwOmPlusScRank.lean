module

public import CFSG.LocalAnalysis.StandardType.GGTwAutDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBRank
public import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenFrame
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173MixedFrame

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB
open CFSG.RankThree.Classical2 (orthDerived)

private theorem twops_selfCentRankGE_of_mulEquiv {p r : ℕ} {R R' : Type} [Group R] [Group R']
    (e : R ≃* R') (h : GGSelfCentRankGE p r R') : GGSelfCentRankGE p r R := by
  intro E hE hsc
  have hcard : Nat.card (E.map e.toMonoidHom) = Nat.card E :=
    (Nat.card_congr (E.equivMapOfInjective _ e.injective).toEquiv).symm
  have hmem : ∀ x : R, e x ∈ E.map e.toMonoidHom ↔ x ∈ E := by
    intro x
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := e.injective hyx
      rwa [this] at hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hE' : CFSG.Open.IsElemAbelian p (E.map e.toMonoidHom) :=
    CFSG.StandardType.TableB.isElemAbelian_map hE e.toMonoidHom
  have hsc' : ∀ g : R', (∀ x ∈ E.map e.toMonoidHom, g * x = x * g) → g ^ p = 1 →
      g ∈ E.map e.toMonoidHom := by
    intro g hg hgp
    obtain ⟨y, rfl⟩ := e.surjective g
    rw [hmem]
    refine hsc y (fun x hx => e.injective ?_) ?_
    · rw [map_mul, map_mul]
      exact hg _ ((hmem x).mpr hx)
    · apply e.injective
      rw [map_pow, hgp, map_one]
  have h1 := h (E.map e.toMonoidHom) hE' hsc'
  rwa [hcard] at h1

private theorem twops_card_eq_of_planeFrame {F : Type} [Field F] [Finite F] [CharP F 2]
    {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V] {Q : QuadraticForm F V}
    {p k : ℕ} {U : Fin k → Submodule F V} {e : Fin k → ↥(orthDerived Q)}
    {E : Subgroup ↥(orthDerived Q)}
    (hp : p.Prime)
    (hF : CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.IsPlaneFrame Q p U e E) :
    Nat.card E = p ^ k := by
  have hF' : CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.IsPlaneFrame Q p U e
      (Subgroup.closure (Set.range e)) := by
    rw [hF.closure_eq]
    exact hF
  have h1 := CFSG.LocalAnalysis.GLTheoremA.T173M.card_torus_eq (Q := Q) hp hF'
  rw [← hF.closure_eq]
  exact h1

theorem ggTwOmPlus_scRank_rec {K : Type} [Field K] [Finite K] [CharP K 2] {n m r : ℕ}
    (hK : Nat.card K = 2 ^ n) (hr : 3 ≤ r) (hev : Even r) (hmr : m = r + 1)
    (h3 : 3 ∣ 2 ^ n + 1) :
    GGSelfCentRankGE 3 r (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))) := by
  subst hmr
  have hpq : 3 ∣ Nat.card K + 1 := by
    rw [hK]
    exact h3
  refine twops_selfCentRankGE_of_mulEquiv (OrthTorus.rPlusEquiv K (m := r + 1) (by omega)) ?_
  intro E hE hsc
  obtain ⟨k, U, e, hframe, hdisj⟩ :=
    OmNsRootGen.exists_planeFrame_of_selfCentralizing
      (Q := TableBOrth.qPlusForm K (r + 1)) (TableBOrth.nondegenerate_qPlusForm (r + 1))
      Nat.prime_three (by norm_num) hpq (ℓ := r + 1)
      (by
        rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
        ring)
      (by omega) hE hsc
  have hcard := twops_card_eq_of_planeFrame (Q := TableBOrth.qPlusForm K (r + 1))
    Nat.prime_three hframe
  have hrk : r ≤ k := by
    rcases hdisj with ⟨hk, -⟩ | ⟨hk, -⟩ <;> omega
  rw [hcard]
  exact Nat.pow_le_pow_right (by norm_num) hrk

end CFSG.StandardType

end
