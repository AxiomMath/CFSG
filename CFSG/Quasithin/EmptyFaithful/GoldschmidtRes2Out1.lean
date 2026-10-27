module

public import CFSG.Quasithin.Vol2.GoldschmidtRes2WDefs

public section

namespace CFSG.Quasithin.Res2

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem outcome1_false_W (hE : E215MemberW) {K T N V M : Subgroup G}
    (hyp : E2.Hyp28 K T N V) (hchar : CharTwo K) (hns : ¬ Group.IsSolvable K) (hTM : T ≤ M)
    (hq : ¬ qhatOf (autI hyp.elem M) < ((2 : ℚ) : WithTop ℚ))
    (hb : ∀ A : Subgroup G, A ≤ T → IsElemAbelian 2 A →
      (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A ≤ 4) : False := by
  obtain ⟨g, -, hP, hcI, hIV, hlt⟩ := hE G K T N V hyp hchar hns hb
  obtain ⟨hAT, -, hAel, hcub, hnot, -⟩ := Ch3n.exists_cubic_of_pair hP hcI hIV
  have hAT' := hAT.trans inf_le_left
  exact hq (E2.qhatOf_lt_two_of_cubic (hV := hyp.elem) (hAT'.trans hTM)
    (hAT'.trans hyp.normal_T) hAel hcub hnot hlt)

end CFSG.Quasithin.Res2
