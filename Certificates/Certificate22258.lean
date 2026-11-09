module

public import Certificates.Data.SolMaxNineE32

public section

open CFSG.ComponentClassification.SolMax.NineE32

namespace CertificateChecks.Batch22258

open CFSG.ComponentClassification.SolMax.NineE32

private theorem range_split : List.range 10000 =
    List.range' 0 1000 ++ List.range' 1000 1000 ++ List.range' 2000 1000 ++ List.range' 3000 1000 ++ List.range' 4000 1000 ++
    List.range' 5000 1000 ++ List.range' 6000 1000 ++ List.range' 7000 1000 ++ List.range' 8000 1000 ++ List.range' 9000 1000 := by
  decide +kernel

set_option maxHeartbeats 0

private theorem nine_e32_chunk_0 : (List.range' 0 1000).all checkOne = true := by
  decide +kernel

private theorem nine_e32_chunk_1 : (List.range' 1000 1000).all checkOne = true := by
  decide +kernel

private theorem nine_e32_chunk_2 : (List.range' 2000 1000).all checkOne = true := by
  decide +kernel

private theorem nine_e32_chunk_3 : (List.range' 3000 1000).all checkOne = true := by
  decide +kernel

private theorem nine_e32_chunk_4 : (List.range' 4000 1000).all checkOne = true := by
  decide +kernel

private theorem nine_e32_chunk_5 : (List.range' 5000 1000).all checkOne = true := by
  decide +kernel

private theorem nine_e32_chunk_6 : (List.range' 6000 1000).all checkOne = true := by
  decide +kernel

private theorem nine_e32_chunk_7 : (List.range' 7000 1000).all checkOne = true := by
  decide +kernel

private theorem nine_e32_chunk_8 : (List.range' 8000 1000).all checkOne = true := by
  decide +kernel

private theorem nine_e32_chunk_9 : (List.range' 9000 1000).all checkOne = true := by
  decide +kernel

private theorem nine_e32_0 : check () = true := by
  unfold check
  rw [range_split]
  simp only [List.all_append, nine_e32_chunk_0, nine_e32_chunk_1, nine_e32_chunk_2, nine_e32_chunk_3, nine_e32_chunk_4, nine_e32_chunk_5, nine_e32_chunk_6, nine_e32_chunk_7, nine_e32_chunk_8, nine_e32_chunk_9, Bool.and_self, Bool.true_and, Bool.and_true]

end CertificateChecks.Batch22258

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.SolMax.NineE32 in
theorem certificate22258 : check () = true := by
  exact CertificateChecks.Batch22258.nine_e32_0

end Certificates
