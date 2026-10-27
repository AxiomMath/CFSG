module

public import Certificates.Data.A8Nbr476
public import CFSG.LocalAnalysis.StandardType.GGA8NbrInfData

public section

namespace CFSG.StandardType.A8NbrInfB

open Certificates.A8Nbr476 CFSG.StandardType.A8NbrInf

@[expose] def genLInfB (a μ : ZMod 7) (i : Fin 3) : M4 :=
  basInfInv a * blk (psi (false, 0, 0, μ) * wgen false i * psiInv (false, 0, 0, μ)) * basInf a

@[expose] def gensInfB (a μ : ZMod 7) (k : Fin 6) : M4 :=
  if h : k.val < 3 then genLInfB a μ ⟨k.val, h⟩ else genK ⟨k.val - 3, by omega⟩

@[expose] def wordDataInfB : List (ZMod 7 × List (Fin 6)) := [
  (1, [0, 1, 2, 1, 0, 5, 0, 1, 2, 1, 0, 5, 5]),
  (2, [0, 1, 5, 2, 1, 5, 5, 0, 5, 2, 5, 5]),
  (3, [0, 2, 5, 0, 2, 5, 5]),
  (4, [0, 1, 5, 5, 2, 1, 5, 0, 5, 5, 2, 5]),
  (5, [1, 2, 5, 2, 1, 2, 5, 5, 2]),
  (6, [2, 5, 2, 5, 5, 2, 5, 2, 5, 5])]

theorem a8InfB_cover : ∀ μ : ZMod 7, μ ≠ 0 → μ ∈ wordDataInfB.map Prod.fst := by
  decide +kernel

theorem a8InfB_transv : ∀ e ∈ wordDataInfB, ∀ a : ZMod 7, a ≠ 0 →
    IsTransv ((e.2.map (gensInfB a e.1)).prod) := by
  decide +kernel

theorem a8InfB_exists_transv {a μ : ZMod 7} (ha : a ≠ 0) (hμ : μ ≠ 0) (S : Submonoid M4)
    (hgen : ∀ k : Fin 6, gensInfB a μ k ∈ S) : ∃ g ∈ S, IsTransv g := by
  obtain ⟨⟨μ', w⟩, he, hfst⟩ := List.mem_map.mp (a8InfB_cover μ hμ)
  obtain rfl : μ' = μ := hfst
  have hmem : (w.map (gensInfB a μ')).prod ∈ S := by
    refine S.list_prod_mem fun g hg => ?_
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp hg
    exact hgen k
  exact ⟨_, hmem, a8InfB_transv _ he a ha⟩

end CFSG.StandardType.A8NbrInfB

end
