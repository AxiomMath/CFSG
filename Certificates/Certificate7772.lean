module

public import CFSG.Milestones.ASVolI.F48.Rest.U52Inputs3
import Certificates.Kernel.U52.PtLnGlue

public section

namespace Certificates

open CFSG.KC.U52PL in
open CFSG CFSG.ASVolI in
theorem certificate7772 :
    ((burnsideF48t_u52Pt ()).size = 165 ∧ burnsideF48t_u52LnPts.size = 297 ∧
      (burnsideF48t_u52Gens ()).size = 6 ∧
      (∀ p ∈ burnsideF48t_u52Pt (), p.size = 5 ∧ ∀ x ∈ p, x < 4) ∧
      (∀ i < 165, ∀ j < 165, i ≠ j → ∀ l ∈ [1, 2, 3],
        (burnsideF48t_u52Pt ())[i]! ≠ burnsideF48t_u52Scale l (burnsideF48t_u52Pt ())[j]!) ∧
      (∀ L ∈ burnsideF48t_u52LnPts, L.size = 5 ∧ (∀ p ∈ L, p < 165) ∧
        ∀ a < 5, ∀ b < 5, a ≠ b → L[a]! ≠ L[b]!) ∧
      (∀ l < 297, ∀ l' < 297, l ≠ l' →
        ∃ p ∈ burnsideF48t_u52LnPts[l]!, p ∉ burnsideF48t_u52LnPts[l']!) ∧
      (∀ k < 6, ∀ i < 165, ((burnsideF48t_u52Gens ())[k]!)[i]! < 165 ∧
        ∃ l ∈ [1, 2, 3], burnsideF48t_u52TV burnsideF48t_u52U[k]! (burnsideF48t_u52Pt ())[i]! =
          burnsideF48t_u52Scale l (burnsideF48t_u52Pt ())[((burnsideF48t_u52Gens ())[k]!)[i]!]!) ∧
      (∀ k < 6, ∀ l < 297, 165 ≤ ((burnsideF48t_u52Gens ())[k]!)[165 + l]! ∧
        ((burnsideF48t_u52Gens ())[k]!)[165 + l]! < 462 ∧
        (∀ p ∈ burnsideF48t_u52LnPts[l]!, ((burnsideF48t_u52Gens ())[k]!)[p]! ∈
          burnsideF48t_u52LnPts[((burnsideF48t_u52Gens ())[k]!)[165 + l]! - 165]!) ∧
        (∀ q ∈ burnsideF48t_u52LnPts[((burnsideF48t_u52Gens ())[k]!)[165 + l]! - 165]!,
          ∃ p ∈ burnsideF48t_u52LnPts[l]!, ((burnsideF48t_u52Gens ())[k]!)[p]! = q))) ∧
    ∀ k < 6, (∀ j < 5, (burnsideF48t_u52U[k]!)[j]! < 4) ∧
      burnsideF48t_u52Dot (burnsideF48t_u52Bar burnsideF48t_u52U[k]!) burnsideF48t_u52U[k]! = 0 :=
  ⟨⟨pt_size, ln_size, g_size, pts_small, pts_ne, lns_small, lns_ne, gen_pt, gen_ln⟩, iso⟩

end Certificates

end
