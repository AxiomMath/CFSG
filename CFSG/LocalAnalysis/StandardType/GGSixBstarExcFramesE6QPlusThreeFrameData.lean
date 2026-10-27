module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcThreeAct

public section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace CFSG.StandardType.ExcFrames.E6QPlusThree

structure E6QPlusThreeFrame (K : Type) [Field K] [Finite K] : Type where
  N : Subgroup (adjointGroup .E6 K)
  weyl : N →* WeylGroup .F4
  frame : Multiplicative (Fin Tag.F4.rank → ZMod 3) →* adjointGroup .E6 K
  frame_injective : Function.Injective frame
  frame_range_le : frame.range ≤ N
  conj_frame : ∀ (a : N) (s : Fin Tag.F4.rank → ZMod 3),
    (a : adjointGroup .E6 K) * frame (Multiplicative.ofAdd s) * (a : adjointGroup .E6 K)⁻¹ =
      frame (Multiplicative.ofAdd (TableBExc.torusAct .F4 3 (weyl a) s))
  mem_frame_range_of_weyl_eq_one : ∀ a : N, weyl a = 1 → (a : adjointGroup .E6 K) ^ 3 = 1 →
    (a : adjointGroup .E6 K) ∈ frame.range
  exists_sylow_le : ∃ P : Sylow 3 (adjointGroup .E6 K), (P : Subgroup (adjointGroup .E6 K)) ≤ N
  mem_frame_range_of_commute : ∀ c : adjointGroup .E6 K,
    (∀ s, c * frame s = frame s * c) → c ^ 3 = 1 → c ∈ frame.range
  mem_N_of_conj : ∀ x : adjointGroup .E6 K, (∀ s, x * frame s * x⁻¹ ∈ frame.range) → x ∈ N
  entrywise_frame : ∀ (σ : K →+* K) (s : Multiplicative (Fin Tag.F4.rank → ZMod 3)),
    Units.map (entrywiseHom σ) ((frame s : adjointGroup .E6 K) : ModGL .E6 K) = frame s

end CFSG.StandardType.ExcFrames.E6QPlusThree
