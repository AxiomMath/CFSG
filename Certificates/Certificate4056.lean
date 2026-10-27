module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinRadL33Inputs
import Certificates.Kernel.LocalQT.Small.C4056

public section

namespace Certificates

open CFSG.QuasithinUnique.Fin253 in
theorem s3Model_elems : s3Model.elems = CFSG.QuasithinUnique.Unc25K1.rawList := by
  dsimp only [s3Model]

open CFSG.QuasithinUnique.Unc25K1 in
private def encR (r : R9) : ℕ := r.i.val + 3 * (r.h.val + 3 * (r.g.val + 3 * (r.f.val +
  3 * (r.e.val + 3 * (r.d.val + 3 * (r.c.val + 3 * (r.b.val + 3 * r.a.val)))))))

set_option maxRecDepth 100000 in
open CFSG.QuasithinUnique.Unc25K1 in
private theorem rawAll_map : rawAll.map encR = List.range 19683 := by decide +kernel

open CFSG.QuasithinUnique.Unc25K1 in
theorem rawList_nodup : rawList.Nodup :=
  (List.Nodup.of_map encR (by rw [rawAll_map]; exact List.nodup_range)).filter _

open CFSG.KD.LQT.C4056 CFSG.QuasithinUnique.Fin253 in
open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Fin253 in
open CFSG.QuasithinUnique.Unc25K1 in
theorem certificate4056 : (CenterOK s3Model.mul s3Model.one s3Model.elems)
    ∧ (OddOK s3Model.mul s3Model.one 351 s3Model.elems s3Invs s3Ord4)
    ∧ (QuatAll s3Model.mul s3Model.one s3Model.elems s3Invs)
    ∧ (CoreAll s3Model.mul s3Model.one s3Model.inv s3Model.elems s3Invs) :=
  CFSG.KC.LQT.R.s4056k s3Model (by dsimp only [s3Model]) (by dsimp only [s3Model])
    (by dsimp only [s3Model]) (by rw [s3Model_elems]; exact CFSG.KC.LQT.R.mem_rawList)
    (by rw [s3Model_elems]; exact rawList_nodup) hk hs

end Certificates
