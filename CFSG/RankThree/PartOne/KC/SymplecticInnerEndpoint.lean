module

public import CFSG.RankThree.PartOne.KC.SymplecticInnerEndpointProducts
public import CFSG.RankThree.PartOne.KC.SymplecticInnerEndpointWiring

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.RankThree.LocalRank
open CFSG.Assembly.RankThreeEven (localRank)

theorem symplectic_actual_rank_inner_plane_local_core_product_centralizes_of_full
    (hfull : ∀ (ℓ f r p : ℕ), StatedLieAdmissible .PSp r ℓ f → p.Prime → 3 < p → p ≠ ℓ → ∀ (K :
        Type) [Field K] [Finite K], Nat.card K = ℓ ^ f → CommonLayerCentralizerTrivial (StatedProj
        (StatedSp r K)) p) :
    SymplecticActualRankInnerPlaneLocalCoreProductCentralizes := by
  intro Q _ _ p ℓ f r hp hp3 hrank hr hℓp E hE hEcard t htE ht1 L hL hmod hEL hSL
  have hpℓ : p ≠ ℓ := fun h => hℓp h.symm
  have hmod' := hmod
  obtain ⟨⟨hℓ, hf, -, hrq'⟩, K, _, _, hK, ⟨e⟩⟩ := hmod
  have hrq : ¬ (r = 2 ∧ ℓ ^ f = 2) := fun ⟨h1, h2⟩ => hrq' (by rw [h1, h2])
  set φ : L →* StatedProj (StatedSp r K) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L)) with hφ
  have hφsurj : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker ≤ Subgroup.center L := by
    intro g hg
    have h1 : e (QuotientGroup.mk' (Subgroup.center L) g) = 1 := hg
    have h2 : QuotientGroup.mk' (Subgroup.center L) g = 1 :=
      e.injective (h1.trans (map_one e).symm)
    exact (QuotientGroup.eq_one_iff g).mp h2
  have hint := symplectic_inner_plane_planeLocalCoreInner hℓ hf hK hp hp3 hpℓ hr hrq
    (hfull ℓ f r p hmod'.1 hp hp3 hpℓ K hK)
  exact inner_actual_component_of_planeLocalCoreInner hp hp3 hE hEcard htE ht1 hL hEL hSL e hint
    (fun _ => spLiftMultiplicitiesCoprime_of_cover L hℓ hf hK hp hp3 hpℓ hr hrank φ hφsurj hker _)

end CFSG.RankThree.PartOne
