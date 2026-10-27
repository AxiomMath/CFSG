module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256h
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OrthFieldExport

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256h
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedLieTag)

theorem noA5_omegaOdd_outer {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {G : Type} [Group G]
    {n ℓ f : ℕ} (hG : StatedClassicalModel G .POmegaOdd n ℓ f)
    (β : MulAut G) (hβ : β ^ p = 1) (hout : ∀ a : G, MulAut.conj a ≠ β) (J : Subgroup G)
    (hJ : CFSG.Open.IsComponentOf J (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β)) :
    ¬ Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* alternatingGroup (Fin 5)) := by
  have hconj : OmegaFieldConj G β ℓ p := omegaFieldConj_odd hp hp2 hG β hβ hout
  obtain ⟨K, _, _, k, d, Q₀, Q, σ, S, e, hd, hch, he⟩ := hconj.out
  have hd0 : 0 < d := by omega
  obtain ⟨-, hK⟩ := fieldAutT_layer_and_eq S hd0
  obtain ⟨hqT, π, hπ, hπk⟩ := exists_central_epi_omega S hd0
  have hJ1 := InputsL33.isComponentOf_map_congr e hJ
  rw [he] at hJ1
  have hJeq := hK _ hJ1
  intro hL
  have hL1 := Claims1110h.a5Center_map e hL
  rw [hJeq] at hL1
  have : Finite k := Finite.of_injective (algebraMap k K) (algebraMap k K).injective
  letI : Fintype k := Fintype.ofFinite k
  exact not_a5_of_surj hqT.1.commutator_eq_top π hπ hπk
    (not_a5_top rfl (large_noA5 S.hnd₀ (by rw [Module.finrank_fin_fun]; exact hd))) hL1

end CFSG.RankThree.PartTwo.Sec21.FF79
