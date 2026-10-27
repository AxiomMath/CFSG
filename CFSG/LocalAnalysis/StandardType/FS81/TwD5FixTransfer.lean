module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Weak
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Offender

public section

namespace CFSG.StandardType.FrameRoute.FS81

theorem t5FixTransfer_holds :
    T5FixTransfer := by
  intro G _ _ b₀ K E hstd B hB ε hε hX
  have hb : b₀ ∈ E := hstd.2.2.2.1 ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers b₀)
  have hdvd := card_wE6_dvd hε
  exact not_mem_commutator_normalizer_of_wE6 hstd hB hε hX (wE6Gen ε) (isLiftable_wE6Gen hε)
    (closure_range_wE6Gen hε) hdvd hb
    (mem_commutator_normalizer_of_wE6 hstd hB hε hX
      (fun _ hA hel hne => wE6_noOffender hε hdvd hA hel hne) hb)

theorem t5Fix_of_matFix
    (hM : T5MatFix) : T5Fix :=
  t5Fix_of_mat hM t5FixTransfer_holds

end CFSG.StandardType.FrameRoute.FS81
