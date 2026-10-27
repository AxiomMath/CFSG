module

public import CFSG.Quasithin.H13.A5M12Cent
public import CFSG.Quasithin.H13.A5Facts1321

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Monster.Code CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.Vol2.Ch10.SecA.C10P01 CFSG.Quasithin.H13.A5.M12

theorem factM12Row1321_holds :
    FactM12Row1321 := by
  intro V _ _ G L hLG hGN hM v hvG hv2
  obtain ⟨e, he⟩ := m12_std hM
  have hvN : congrHom e v ∈ (rhoC12 m24Pair le_rfl).range :=
    map_le_of_normalizer ⟨hLG, hGN⟩ he normalizer_rhoC12 (Subgroup.zpowers_le.2 hvG)
      ⟨v, Subgroup.mem_zpowers v, rfl⟩
  obtain ⟨σ, hσ⟩ := hvN
  have hv2' : orderOf (congrHom e v) = 2 :=
    (orderOf_injective _ (congrHom_injective e) v).trans hv2
  have hσ2 : orderOf σ = 2 := by
    rw [← orderOf_injective _ rhoC12_m24Pair_injective σ, hσ]
    exact hv2'
  obtain ⟨t, ht⟩ : ∃ t : MulAut W11, t = rhoC11 AutPerm le_rfl ⟨σ, σ.2.1⟩ := ⟨_, rfl⟩
  have ht2 : orderOf t = 2 := by
    rw [ht, orderOf_injective _ (rhoC11_injective AutPerm le_rfl), Subgroup.orderOf_mk,
      Subgroup.orderOf_coe, hσ2]
  have h4 := four_le_rkIdx_rhoC11 (t := t) (by rw [ht]; exact ⟨_, rfl⟩) ht2
  have hle := rkIdx_le_of_proj W10_sq projYW projYW_surjective projYW_eq_one_iff
    (φ := t) (φ' := congrHom e v) (fun u => by
      rw [← hσ, ht]
      exact projYW_rhoHom σ.2 u)
  have hV : rkIdx (fixV (Subgroup.zpowers (congrHom e v))) =
      rkIdx (fixV (Subgroup.zpowers v)) :=
    calc rkIdx (fixV (Subgroup.zpowers (congrHom e v)))
        = rkIdx (fixV ((Subgroup.zpowers v).map (congrHom e))) := by
          rw [MonoidHom.map_zpowers]
      _ = rkIdx (fixV (Subgroup.zpowers v)) := rkIdx_fixV_map_congrHom e _
  have h4' : 4 ≤ rkIdx (fixV (Subgroup.zpowers t)) := h4
  have hle' : rkIdx (fixV (Subgroup.zpowers t)) ≤
      rkIdx (fixV (Subgroup.zpowers (congrHom e v))) + 1 := hle
  omega

end CFSG.Quasithin.H13.A5
