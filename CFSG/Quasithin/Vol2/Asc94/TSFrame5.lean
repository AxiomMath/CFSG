module

public import CFSG.Quasithin.Vol2.Asc94.TSFrame4
public import CFSG.Quasithin.Vol2.Asc94.TS40f
public import CFSG.Quasithin.Vol2.Asc94.TSModel11

public section

namespace CFSG.Quasithin.A94

open CFSG.CGT.M24S CFSG.Open

variable {G : Type} [Group G] {z : G} (e : ↥(Cz z) ≃* L52.Hc)

@[expose] noncomputable def frame5 [Finite G] (hz : orderOf z = 2) (hF6 : L52.F6Model) :
    Frame5 G z :=
  have specΔ := Classical.choose_spec L52.A1_orbits
  { toFrame4 := frame4 e hz hF6
    z_mem_closure_Δ3 := by
      obtain ⟨-, -, -, -, -, -, -, -, h3⟩ := specΔ
      show z ∈ Subgroup.closure (emb e '' (Classical.choose L52.A1_orbits 3))
      have hmem : emb e L52.zt ∈ (Subgroup.closure L52.TQA).map (emb e) :=
        ⟨L52.zt, L52.zt_mem_closure_TQA, rfl⟩
      rw [MonoidHom.map_closure, emb_zt e hz] at hmem
      rw [h3]
      exact hmem
    card_A_Q := by
      show Nat.card ↥(tr e L52.A1 ⊓ tr e L52.Qh) = 16
      rw [← tr_inf, card_tr, L52.card_A1_inf_Qh]
      norm_num }

end CFSG.Quasithin.A94
