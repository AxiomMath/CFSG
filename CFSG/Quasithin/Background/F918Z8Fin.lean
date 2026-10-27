module

public import CFSG.Quasithin.Background.F918Z8j
public import CFSG.Quasithin.Background.F918Z8Alt2
public import CFSG.Quasithin.Background.F918Z8Kz
public import CFSG.Quasithin.Background.F918Z8Ex4
public import CFSG.Quasithin.Background.F918Z8Su4
public import CFSG.Quasithin.Background.F918Z8Sy5
public import CFSG.Quasithin.Background.F918Z8Sw1
public import CFSG.Quasithin.Background.F918Z8Ox4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

theorem d321_qhat_congr {W : Type} [CommGroup W] [Finite W] {X : Subgroup (MulAut W)}
    {V₁ V₂ : Subgroup W} (h : V₁ = V₂) : qhatOf (autSub X V₁) = qhatOf (autSub X V₂) := by
  subst h
  rfl

theorem d321_norm_case (hL38 : D3L38) (hDeep : D310Deep)
    (hC : D321Core)
    {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
    {t : MulAut W} {A : Subgroup (MulAut W)} (hstd : D3Std M Mp T L V) (htT : t ∈ T)
    (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W))) (hMp : Mp = L ⊔ conjAutSub t L)
    (hqM : qhatOf M ≤ ((2 : ℚ) : WithTop ℚ)) (hA : QOff Mp T A (orbSup T V))
    (htop : orbSup T V ≠ ⊤) (hlt : V < orbSup T V) (hc : D36cConcl Mp T L V t) :
    D321Concl Mp L t := by
  have htriv := hc.1
  rcases hc.2.2.2 with h1 | ⟨-, ⟨s, hsT, hsL, hsV⟩, hs2, -⟩
  · have hqV : qhatOf (autSub (Mp ⊔ T) V) ≤ ((2 : ℚ) : WithTop ℚ) := by
      rw [← d321_qhat_congr h1]
      exact hc.2.2.1
    exact ⟨(d321_struct hL38 hstd htT htL hMp htriv).1,
      (d321_struct hL38 hstd htT htL hMp htriv).2,
      hC W M Mp T L V t A hstd htT htL hMp hqM hA htriv hlt h1 hqV htop⟩
  · exfalso
    apply htop
    have hVL := d321_comm_eq hstd hMp htriv
    have h2 := (hs2 s hsT hsL hsV).1
    have hstrict : V < commSub (orbSup T V) L := by
      rw [h2]
      have hne : V.map s.toMonoidHom ≠ V := fun h => hsV (mem_stabSub_iff_map_eq.mpr h)
      refine lt_of_le_of_ne le_sup_left fun h => hne ?_
      have hle : V.map s.toMonoidHom ≤ V :=
        (le_sup_right : V.map s.toMonoidHom ≤ V ⊔ V.map s.toMonoidHom).trans h.ge
      exact Subgroup.eq_of_le_of_card_ge hle (by
        rw [Subgroup.card_map_of_injective s.injective])
    exact d321_alt2_of_deep hL38 hDeep hstd htT htL hMp hA htriv hc.2.2.1 hstrict

theorem d321_of_parts (hL38 : D3L38) (h36 : D36c)
    (hTop : D391LLTop) (hDeep : D310Deep) (hC : D321Core) : D321 := by
  intro W _ _ M Mp T L V hstd t htT htL hMp hqM A hAle hAne hAel hAq hAr hAf hAfV
  have hA : QOff Mp T A (orbSup T V) := ⟨hAle, hAne, hAel, hAq, hAr, hAf, hAfV⟩
  by_cases htop : orbSup T V = ⊤
  · exact Or.inl htop
  right
  by_cases hVeq : V = orbSup T V
  · exact absurd (hTop W M Mp T L V hstd hqM t htT htL hMp hVeq A hA) htop
  have hlt : V < orbSup T V := lt_of_le_of_ne (le_orbSup T V) hVeq
  rcases h36 W M Mp T L V hstd hlt t htT htL hMp with hc | hc
  · exact d321_norm_case hL38 hDeep hC hstd htT htL hMp hqM hA htop hlt hc
  · have hD' : D31 M Mp T (conjAutSub t L) V := hstd.hyp.conj htT
    have hMp' : Mp = conjAutSub t L ⊔ conjAutSub t⁻¹ (conjAutSub t L) := by
      rw [conjAutSub_inv_conjAutSub, sup_comm]
      exact hMp
    have hstd' : D3Std M Mp T (conjAutSub t L) V := ⟨hD', hstd.qhat, hstd.irrT⟩
    have htL' : t⁻¹ ∉ Subgroup.normalizer
        ((conjAutSub t L : Subgroup (MulAut W)) : Set (MulAut W)) :=
      not_mem_normalizer_conjAutSub htL
    exact d321_concl_symm hL38 hstd htT htL hMp
      (d321_norm_case hL38 hDeep hC hstd' (T.inv_mem htT) htL' hMp' hqM hA htop hlt hc)

theorem d321_proved
    (hL38 : D3L38) (h38 : CFSG.QuasithinUnique.Vol2Native.A38ForSQTKCat) (h36 : D36c)
    (hDeep : D310Deep) (hD392 : D392) (hB42 : AsB42) (hB45 : AsB45) (hB56 : AsB56)
    (hA21 : AsA21SQTKSection) (hF : Vol2.Ch10.SecA.Facts10_1) (hX : Insp5aNonShape) : D321 :=
  d321_of_parts hL38 h36 (d391LLTop_of_notFF hL38 (d391NotFFTop_of_b56 hL38 hB56)) hDeep
    (d321Core_of_local hL38
      (d321Local_of_parts hD392
        (d321LocSuz_of_inputs hD392 hB45 hA21 hF hX
          (suzFFClass_of_b42 hB42 hB45 hA21 hF hX (suzSingle_proved hB45 hA21 hF hX h38)
            (suzXirr_proved hB42 hA21)))
        (d321LocFaith_of_inputs hB42 hA21 hF hX))
      (d321OpPrimeC_of_inputs hL38 (d321OpExc_of_inputs hL38 h38))
      (d321Exact_of_inputs hL38))
