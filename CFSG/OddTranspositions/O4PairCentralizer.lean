module

public import CFSG.OddTranspositions.O4Minus5Pair

public section

namespace CFSG.OddTranspositions.QZ

open SemidirectProduct

theorem mem_centralizer_inr_frob25_iff (q : PSL225) (σ : K25 ≃+* K25) :
    (SemidirectProduct.mk q σ : PSigmaL225) ∈
      Subgroup.centralizer ({SemidirectProduct.inr frob25} : Set PSigmaL225) ↔
    q = CFSG.GorensteinWalter.psl2FieldAut K25 frob25 q := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have hleft := congrArg SemidirectProduct.left h
    change q * (CFSG.GorensteinWalter.psl2FieldAut K25 σ) 1 =
      1 * (CFSG.GorensteinWalter.psl2FieldAut K25 frob25) q at hleft
    simpa using hleft
  · intro hq
    apply SemidirectProduct.ext
    · change q * (CFSG.GorensteinWalter.psl2FieldAut K25 σ) 1 =
        1 * (CFSG.GorensteinWalter.psl2FieldAut K25 frob25) q
      simpa using hq
    · change σ * frob25 = frob25 * σ
      ext x
      change σ (x ^ 5) = (σ x) ^ 5
      rw [map_pow]

end CFSG.OddTranspositions.QZ
