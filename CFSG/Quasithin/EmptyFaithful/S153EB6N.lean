module

public import CFSG.Quasithin.EmptyFaithful.S153EB6M
public import CFSG.Quasithin.EmptyFaithful.S153EB6L

public section

namespace CFSG.Quasithin

namespace S153EB6

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

theorem model_facts {V : Type} [CommGroup V] [Finite V] {G Kb : Subgroup (MulAut V)} {a : MulAut V}
    (hI : Induced V G Kb a) : ModelFacts V G Kb a := by
  rcases hI.mt with ⟨n, hn2, hn5, hmt⟩ | ⟨n, hn5, hn8, hreal⟩ | ⟨n, hn, hreal⟩
  · have hcard := G64.BinaryNaturalSL.card_eq hmt
    have hn3 : 3 ≤ n := by
      by_contra hlt
      have : 2 ^ n ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 := hI.big
      omega
    exact modelFacts_of_binary hI hn3 hmt
  · exact modelFacts_of_perm hI hn5 (Z := Subgroup.zpowers (G6.allOnes n) ⊓ G6.coreMod n) le_rfl
      (G64.symDn_faithful hn5) hreal
  · exact modelFacts_of_perm hI (by omega : 5 ≤ n) (Z := ⊥) bot_le
      (G64.symCore_faithful (by omega : 3 ≤ n)) hreal

end S153EB6

end CFSG.Quasithin
