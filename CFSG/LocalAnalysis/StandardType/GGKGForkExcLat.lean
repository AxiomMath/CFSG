module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcCent
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcNorm
public import CFSG.LocalAnalysis.StandardType.GGKGForkLatticeInvol
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcRootsC
public import CFSG.LocalAnalysis.StandardType.GGKGForkLatticeElt
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcLat1
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcLat2
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcLat3
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcLat4
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcLatPhi

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem ggKGEl_latticeAt_caseA
    {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    {E : Subgroup (adjointGroup τ K)} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4)
    (hp : p.Prime) (hp5 : 5 ≤ p) (F : ExcFrame τ K p E)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hΦ : ∀ g, F.D.Φ g = Units.map (entrywiseHom Fr) g)
    (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p)
    (hact : ∀ y : Fin τ.rank → ℤ,
      weylTuple F.w (fun i => Units.map Fr.toMonoidHom (ζ ^ y i)) = (fun i => ζ ^ y i))
    (hw : (p ∣ Nat.card K - 1 ∧ F.w = 1) ∨ (p ∣ Nat.card K + 1 ∧ ExcIsLongest τ F.w)) :
    GGKGLatticeAt p E := by
  refine ⟨τ.rank, ggKGEl_Q τ, ggKGEl_pi hp hp5 hτ F hΦ ζ hζ hact,
    ggKGEl_Q_form (τ := τ), ggKGEl_pi_surjective hp hp5 hτ F hΦ ζ hζ hact, ?_⟩
  intro w₀ hrefl
  obtain ⟨v, hv, hv2, hactV⟩ :=
    ggKGEl_normalizer_data hτ hp hp5 F hw hΦ ζ hζ hact hrefl
  obtain ⟨w, hwroot, hwform⟩ := ggKGLat_involution_isRoot hp (by omega)
    (ggKGEl_Q_form (τ := τ)) (ggKGEl_mat v) (ggKGEl_Q_invariant v) (ggKGEl_mat_mul_self hv2)
    (ggKGEl_fix_count hτ hp hp5 F hΦ ζ hζ hact hrefl v hactV)
    (by rcases hτ with rfl | rfl | rfl | rfl <;> decide)
  exact ⟨w, hwroot, fun y => by rw [hactV y, hwform y]⟩

theorem ggKGExc_latticeAt
    {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    {E : Subgroup (adjointGroup τ K)} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4) (hp : p.Prime)
    (hp5 : 5 ≤ p) (F : ExcFrame τ K p E)
    (hw : (p ∣ Nat.card K - 1 ∧ F.w = 1) ∨ (p ∣ Nat.card K + 1 ∧ ExcIsLongest τ F.w)) :
    GGKGLatticeAt p E := by
  obtain ⟨Fr, hFr, hΦ⟩ := F.frob
  obtain ⟨ζu, hζu⟩ :=
    CFSG.LieType.SeitzGeneration.exists_primitiveRoot_units (L := AlgebraicClosure K) (ℓ := 2)
      (by norm_num) hp (by omega)
  let ζ : (AlgebraicClosure K)ˣ := ζu
  have hζ : IsPrimitiveRoot ζ p := hζu
  rcases hw with ⟨hpq, hwn⟩ | ⟨hpq, hlong⟩
  · refine ggKGEl_latticeAt_caseA hτ hp hp5 F hΦ ζ hζ ?_ (Or.inl ⟨hpq, hwn⟩)
    intro y
    exact ggKGEx_hact_w_one F hFr hwn hpq (fun i => ggKGEl_zetaPow_pow_eq_one ζ hζ (y i))
  · by_cases hE6 : τ = .E6
    · subst hE6
      exact ggKGExc_latticeAt_E6phi hp hp5 F hpq hlong
    · have hτ' : τ = .E7 ∨ τ = .E8 ∨ τ = .F4 := by
        rcases hτ with h | h | h | h
        · exact absurd h hE6
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      refine ggKGEl_latticeAt_caseA hτ hp hp5 F hΦ ζ hζ ?_ (Or.inr ⟨hpq, hlong⟩)
      intro y
      exact ggKGEx_hact_w_neg F hFr hτ' hlong hpq (fun i => ggKGEl_zetaPow_pow_eq_one ζ hζ (y i))

end CFSG.StandardType

end
