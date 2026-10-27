module

public import CFSG.LocalAnalysis.StandardType.GGMemberRowsDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRankOneConj
import CFSG.GH74.L5U5.ModelsPairsUnitary

public section

namespace CFSG.StandardType

variable {G : Type} [Group G] [Finite G]

theorem ggPairConcl_of_automizer_conj {X Bs : Subgroup G} {a r s : MulAut ↥Bs}
    (ha : a ∈ ggAutomizer X Bs) (hp : GGPairConcl Bs X r s) :
    GGPairConcl Bs X (a * r * a⁻¹) (a * s * a⁻¹) := by
  obtain ⟨g, hgX, _hgN, hg⟩ := mem_ggAutomizer_iff.mp ha
  let cg := (MulAut.conj g).toMonoidHom
  have hX : X.map cg = X :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hgX)
  have hR (t : MulAut ↥Bs) : (ggRankOneIn X Bs t).map cg =
      ggRankOneIn X Bs (a * t * a⁻¹) := by
    rw [ggRankOneIn_map_conj hg t, hX]
  have hc : (a * r * a⁻¹) * (a * s * a⁻¹) =
      (a * s * a⁻¹) * (a * r * a⁻¹) ↔ r * s = s * r := by
    change (MulAut.conj a) r * (MulAut.conj a) s =
      (MulAut.conj a) s * (MulAut.conj a) r ↔ _
    rw [← map_mul, ← map_mul]
    exact (MulAut.conj a).injective.eq_iff
  refine ⟨?_, ?_⟩
  · intro hcomm u hu v hv
    rw [← hR r] at hu
    rw [← hR s] at hv
    obtain ⟨u₀, hu₀, rfl⟩ := Subgroup.mem_map.mp hu
    obtain ⟨v₀, hv₀, rfl⟩ := Subgroup.mem_map.mp hv
    rw [← map_mul, ← map_mul, hp.1 (hc.mp hcomm) u₀ hu₀ v₀ hv₀]
  · intro hnon K _ _ _ f hK hcard
    have hnon₀ : r * s ≠ s * r := fun h => hnon (hc.mpr h)
    have hcard₀ : Nat.card (ggRankOneIn X Bs r) = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
      rw [← hR r] at hcard
      rw [← Nat.card_congr ((ggRankOneIn X Bs r).equivMapOfInjective cg
        (MulAut.conj g).injective).toEquiv] at hcard
      exact hcard
    obtain ⟨W, hW⟩ := hp.2 hnon₀ K f hK hcard₀
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine ⟨W.map cg, ?_⟩
    rw [← hR r, ← hR s]
    exact CFSG.GH74.L5U5.unitaryBlockStandardPair_map' hW cg (MulAut.conj g).injective

end CFSG.StandardType
