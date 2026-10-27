module

public import Certificates.Data.Kernel.AE6Par.Defs

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelAE6Par

open Equiv CFSG.ClassicalInvolution.Q3 Certificates.AE6Par Certificates.AE6Par.K

theorem ae6par_gens : gens.length = 18 ∧ ∀ g ∈ List.range 18, inS0 (genElt g) = true := by
  decide +kernel

theorem ae6par_rows : ∀ e ∈ dcTable, RowOK e := by
  decide +kernel

theorem ae6par_codes : (codeOf 1 :: dcTable.map Prod.fst).Nodup ∧ dcTable.length = 104 := by
  decide +kernel

theorem ae6par_t01 : codeOf 1 :: (dcTable.filter fun e => e.2.1 = 0).map Prod.fst = t0L ∧
    codeOf 1 :: (dcTable.filter fun e => e.2.1 = 1).map Prod.fst = t1L := by
  decide +kernel

theorem ae6par_notin : stabB AE.affinePlanes (tau 1) = false ∧ stabB planes2 (tau 0) = false := by
  decide +kernel

theorem ae6par_p2 : planes2 = AE.affinePlanes.map fun s => s.map (swap 0 1).toEmbedding := by
  decide +kernel

theorem ae6par_vk : (∀ g ∈ gens, g.1 ∈ six ∧ vkPred g.1 (swapsPerm g.2) = true) ∧
    ∀ x y : Fin 8, x ≠ y → ∃ δ ∈ six, x ∈ δ ∧ y ∈ δ := by
  decide +kernel

theorem ae6par_six : six = sixL.map q4 ∧ ∀ q ∈ sixL, sixB q.1 q.2.1 q.2.2.1 q.2.2.2 = true := by
  decide +kernel

theorem ae6par_pfst : ptab1.map Prod.fst = AE.affinePlanes ∧ ptab2.map Prod.fst = planes2 := by
  decide +kernel

theorem ae6par_ptab : (∀ e ∈ ptab1, ptabB t0L e = true) ∧ ∀ e ∈ ptab2, ptabB t1L e = true := by
  decide +kernel

end CertificateChecks.KernelAE6Par
