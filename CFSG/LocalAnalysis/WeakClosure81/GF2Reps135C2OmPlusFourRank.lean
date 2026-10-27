module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusFourMoved
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusFourOrbit
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQPlusKappaOne
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQPlusRankOrbit

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.Quasithin.SmithCurtis CFSG.LieType.RootSystem
open CFSG.StandardType

theorem omqPlusSevenRoots_four : OmqPlusSevenRoots (by norm_num : 3 ≤ 4) := by
  intro m hm3 a b hab δ δ' hδ hδ' π s hs hprod hx
  exact omq_exists_seven_orbit_roots_four hm3 hab hδ hδ' hs hprod hx

theorem omq_omPlus_four_le_rank_of_node_one {F : Type} [Field F] [Finite F] [CharP F 2]
    {k V : Type} [Field k] [CharP k 2] [AddCommGroup V] [Module k V] [Module.Finite k V]
    {σ : Representation k (spinGroup (quadPlus 4 F)) V} (hσ : IsSimpleRep σ) {y₀ : V}
    {χ : spinGroup (quadPlus 4 F) → k} {μ : Fin 4 → k}
    (ht : (omPlusCurtisDatum 4 F (by norm_num)).IsCurtisType σ y₀ χ μ)
    (hsep : μ 1 = (omPlusCurtisDatum 4 F (by norm_num)).dScalar χ 1)
    {g : spinGroup (quadPlus 4 F)} (hg2 : g * g = 1) (hg1 : g ≠ 1) :
    4 ≤ Module.finrank k (LinearMap.range (σ g - 1)) := by
  refine omq_omPlus_four_le_rank_of_orbit (n := 4) (by norm_num) hσ ht hg2 hg1 ?_
  intro x π s hxr hs hprod hx
  obtain ⟨v, hfix, hu⟩ := exists_four_orbit_omPlus_four_node_one hxr hs hprod hx
  refine ⟨v, ?_, hu⟩
  intro t htne
  exact hfix t (fun h => htne (by rw [show t = 1 from Fin.ext h]; exact hsep))

theorem omq_omPlus_four_le_rank_of_pair {F : Type} [Field F] [Finite F] [CharP F 2]
    {k V : Type} [Field k] [CharP k 2] [AddCommGroup V] [Module k V] [Module.Finite k V]
    {σ : Representation k (spinGroup (quadPlus 4 F)) V} (hσ : IsSimpleRep σ) {y₀ : V}
    {χ : spinGroup (quadPlus 4 F) → k} {μ : Fin 4 → k}
    (ht : (omPlusCurtisDatum 4 F (by norm_num)).IsCurtisType σ y₀ χ μ) {i j : Fin 4}
    (hij : i ≠ j) (hi : i.val ≠ 1) (hj : j.val ≠ 1)
    (hsi : μ i = (omPlusCurtisDatum 4 F (by norm_num)).dScalar χ i)
    (hsj : μ j = (omPlusCurtisDatum 4 F (by norm_num)).dScalar χ j)
    {g : spinGroup (quadPlus 4 F)} (hg2 : g * g = 1) (hg1 : g ≠ 1) :
    4 ≤ Module.finrank k (LinearMap.range (σ g - 1)) := by
  refine omq_omPlus_four_le_rank_of_orbit (n := 4) (by norm_num) hσ ht hg2 hg1 ?_
  intro x π s hxr hs hprod hx
  obtain ⟨v, hfix, hu⟩ := exists_four_orbit_omPlus_four_pair hij hi hj hxr hs hprod hx
  exact ⟨v, fun t htne =>
    hfix t (fun h => htne (by rw [h]; exact hsi)) (fun h => htne (by rw [h]; exact hsj)), hu⟩

end CFSG.LocalAnalysis.WeakClosure81
