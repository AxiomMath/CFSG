
module


public import CFSG.Quasithin.Vol2.KGFactC31RuRefDefs
import Certificates.Kernel.Misc.RuBigZ.BigZ

public section

open CFSG.Sporadic.RuSchreier CFSG.Quasithin.KGC31.Ru

public section

namespace Certificates

open CertificateChecks.KernelMisc.RuBigZ

open CFSG.Sporadic.RuSchreier CFSG.Quasithin.KGC31.Ru in
theorem certificate7233 : RefFacts ∧ ∀ g ∈ ruC, BigZ g :=
  ⟨⟨ebasisK, ruZ_memK, uE_le_uV32EK, fun _ hg h1 => ncard_fix_uEK hg h1,
      fun _ hg hE => ncard_fix_uV32EK hg hE, x16_mem_normK, ruC_le_norm32K, orderOfK,
      conj_x16_not_normK, conj_k16_u32K, fun _ hi _ hj hij => conj64_distinctK hi hj hij,
      fun _ ha _ hb => ruK_sq_commK ha hb, vE_commK, ruNs_wordsK, commut_not_centK, cQ_memJK,
      vE_conjK, fun _ hv h1 hz => exists_conj_r30K hv h1 hz⟩,
    bigZ_allK⟩

end Certificates

end
