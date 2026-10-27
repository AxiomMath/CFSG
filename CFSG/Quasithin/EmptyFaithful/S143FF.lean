module

public import CFSG.Quasithin.EmptyFaithful.S143FE
public import CFSG.Quasithin.EmptyFaithful.S143FA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

theorem lemma_14_3_18_b : S143.Lemma14318b := by
  intro G _ _ T M g c _
  obtain ⟨r, hrW, hrV, hr2⟩ := S143.Counter.exists_involution_wOfU c
  obtain ⟨t, htT, htRQ⟩ : ∃ t ∈ T, t ∉ S143.rOf T M ⊔ S143.qOf T := by
    by_contra hall
    push Not at hall
    have h1 : (S143.rOf T M ⊔ S143.qOf T).relIndex T = 1 := Subgroup.relIndex_eq_one.mpr hall
    have h2 := S143.rq_index_of c
    omega
  refine ⟨c.Ac hrW hrV hr2, t, ?_⟩
  exact
    { t_mem := htT
      t_nmem := htRQ
      A_elem := ⟨⟨⟨fun a b => Subtype.ext (S143.mul_comm_of_sq_eq_one
        (fun x hx => c.sq_Ac hrW hrV hr2 hx) a.2 b.2)⟩⟩, fun x hx => by
          rw [sq]; exact c.sq_Ac hrW hrV hr2 hx⟩
      A_card := c.card_Ac hrW hrV hr2
      A_le := c.Ac_le_rOf hrW hrV hr2
      r_eq_AAt := (c.Ac_sup_conj hrW hrV hr2 htT htRQ).symm
      card_R := S143.card_rOf c
      v_eq_inf := (c.Ac_inf_conj hrW hrV hr2 htT htRQ).symm
      maximal := fun B hB hBe => c.maximal_Ac hrW hrV hr2 htT htRQ hB hBe
      normal_A := c.normal_Ac hrW hrV hr2 }

end CFSG.Quasithin
