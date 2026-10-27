module

public import Certificates.Data.A8Nbr476

public section

namespace CFSG.StandardType.A8NbrInf

open Certificates.A8Nbr476

@[expose] def basInf (a : ZMod 7) : M4 :=
  !![a, 1, 1, 1; 0, 1, -1, 0; 0, 0, 1, -1; 0, 1, 1, 1]

@[expose] def basInfInv (a : ZMod 7) : M4 :=
  !![a⁻¹, 0, 0, -a⁻¹; 0, 3, 5, 5; 0, 2, 5, 5; 0, 2, 4, 5]

@[expose] def genLInf (a μ : ZMod 7) (i : Fin 3) : M4 :=
  basInfInv a * blk (psi (true, 0, 0, μ) * wgen true i * psiInv (true, 0, 0, μ)) * basInf a

@[expose] def gensInf (a μ : ZMod 7) (k : Fin 6) : M4 :=
  if h : k.val < 3 then genLInf a μ ⟨k.val, h⟩ else genK ⟨k.val - 3, by omega⟩

@[expose] def wordDataInf : List (ZMod 7 × List (Fin 6)) := [
  (1, [0, 1, 0, 5, 5, 2, 5, 0, 5, 5, 2, 5]),
  (2, [0, 1, 2, 0, 5, 0, 1, 2, 0, 5, 5]),
  (3, [2, 5, 2, 5, 5]),
  (4, [0, 1, 0, 5, 2, 5, 5, 0, 5, 2, 5, 5]),
  (5, [0, 5, 2, 5, 5, 0, 5, 2, 5, 5]),
  (6, [0, 2, 0, 5, 0, 2, 0, 5, 5])]

theorem a8Inf_cover : ∀ μ : ZMod 7, μ ≠ 0 → μ ∈ wordDataInf.map Prod.fst := by
  decide +kernel

theorem a8Inf_transv : ∀ e ∈ wordDataInf, ∀ a : ZMod 7, a ≠ 0 →
    IsTransv ((e.2.map (gensInf a e.1)).prod) := by
  decide +kernel

theorem a8Inf_exists_transv {a μ : ZMod 7} (ha : a ≠ 0) (hμ : μ ≠ 0) (S : Submonoid M4)
    (hgen : ∀ k : Fin 6, gensInf a μ k ∈ S) : ∃ g ∈ S, IsTransv g := by
  obtain ⟨⟨μ', w⟩, he, hfst⟩ := List.mem_map.mp (a8Inf_cover μ hμ)
  obtain rfl : μ' = μ := hfst
  have hmem : (w.map (gensInf a μ')).prod ∈ S := by
    refine S.list_prod_mem fun g hg => ?_
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp hg
    exact hgen k
  exact ⟨_, hmem, a8Inf_transv _ he a ha⟩

end CFSG.StandardType.A8NbrInf

end
