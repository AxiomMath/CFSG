module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcCent
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcLat
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcRoot

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus

theorem ggKGExc_latticeElt 
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4)
    {K : Type} [Field K] [Finite K] [CharP K 2] {p r₀ : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ Nat.card K - 1 ∨ p ∣ Nat.card K + 1) (h : ExcSCTorusInput τ K p r₀) :
    GGKGLatticeElt p r₀ (adjointGroup τ K) := by
  intro E hE h3 hr hsc
  obtain ⟨F, h1, h2⟩ := h E hE h3 hr hsc
  exact ggKGExc_latticeAt hτ hp hp5 F (hpq.imp (fun h => ⟨h, h1 h⟩) fun h => ⟨h, h2 h⟩)

theorem ggKGExc_rootDatum
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4)
    {K : Type} [Field K] [Finite K] [CharP K 2] {p r₀ : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hτ6 : τ = .E6 → 5 ≤ p)
    (hpq : p ∣ Nat.card K - 1) (h : ExcSCTorusInput τ K p r₀) :
    GGKGRootDatum p r₀ (adjointGroup τ K) := by
  intro E hE h3 hr hsc
  obtain ⟨F, h1, -⟩ := h E hE h3 hr hsc
  exact ggKGExc_rootDatumAt hτ hp hp3 hτ6 hpq F (h1 hpq)

end CFSG.StandardType
