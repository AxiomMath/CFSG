module

public import Certificates.Data.E8Frame
import Certificates.Data.E8FrameFast
import CFSG.Certificates.Kernel.PermCent.CVSound

public section

namespace CertificateChecks.Batch20190

open CFSG.Certificates.Kernel.PkCV

private theorem closureList_map_hom {G H : Type} [Group G] [DecidableEq G] [Group H]
    [DecidableEq H] (f : H → G) (hmul : ∀ a b, f (a * b) = f a * f b) (hone : f 1 = 1)
    (hf : Function.Injective f) (gens : List H) (n : ℕ) :
    CFSG.LieType.Chevalley.E8Frame.closureList (gens.map f) n =
      (CFSG.LieType.Chevalley.E8Frame.closureList gens n).map f := by
  unfold CFSG.LieType.Chevalley.E8Frame.closureList
  induction n with
  | zero => simp [hone]
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      ← List.dedup_map_of_injective hf]
    congr 1
    simp only [List.map_append, List.map_flatMap, List.flatMap_map, List.map_map,
      Function.comp_def, hmul]

private theorem map_cOf_ev {m : ℕ} [CFSG.Certificates.Kernel.PkCV.Small m]
    (L : List (Equiv.Perm (Fin m))) : (L.map cOf).map ev = L := by
  rw [List.map_map]
  simp only [Function.comp_def, ev_cOf, List.map_id']

open CFSG.LieType.Chevalley.E8Frame in
private theorem lineList_eq : lineList () =
    (closureList ((frameGens.map fun g => g.2.2).map cOf) 6).map ev := by
  unfold lineList
  rw [← closureList_map_hom ev ev_mul ev_one ev_injective, map_cOf_ev]

open CFSG.LieType.Chevalley.E8Frame in
private theorem transList_eq : transList () = (closureList (transGens.map cOf) 3).map ev := by
  unfold transList
  rw [← closureList_map_hom ev ev_mul ev_one ev_injective, map_cOf_ev]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
open CFSG.LieType.Chevalley.E8Frame in
theorem lineCheck_true : lineCheck () = true := by
  unfold lineCheck
  simp only [lineList_eq, transList_eq, List.length_map, nodup_map_ev, List.all_map, List.any_map,
    Function.comp_def, ev_mul', ev_inv', decide_mem_map_ev, one_eq_ev, ev_eq_iff, decide_ev_eq]
  decide +kernel

end CertificateChecks.Batch20190

namespace Certificates

open CFSG.LieType.Chevalley.E8Frame

theorem certificate20190 : CFSG.LieType.Chevalley.E8Frame.gensCheck () = true ∧
    CFSG.LieType.Chevalley.E8Frame.reflCheck () = true ∧
    CFSG.LieType.Chevalley.E8Frame.frameCheck () = true ∧
    CFSG.LieType.Chevalley.E8Frame.lineCheck () = true :=
  ⟨by rw [Certificates.E8FrameFast.gensCheck_eq_gensCheckFast]; decide +kernel,
    by decide +kernel, by decide +kernel, CertificateChecks.Batch20190.lineCheck_true⟩

end Certificates
