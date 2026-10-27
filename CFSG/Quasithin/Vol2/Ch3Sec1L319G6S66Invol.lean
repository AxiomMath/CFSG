module

public import CFSG.Quasithin.Vol2.Ch3zStep

public section

namespace CFSG.Quasithin.H13.L319.S66

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.Ch3z

theorem exists_conj_involution {G : Type} [Group G] [Finite G] {H T M₂ U A L N : Subgroup G}
    {V : Subgroup G} (hB1 : B69One) (h : Ch3z.Setting H T M₂ U A)
    (hstep : IsChiefStep H U L N) (hnc : ¬ IsCentralStep H L N)
    {𝓗 : Finset (Subgroup (MulAut ↥(chiefMod L N)))}
    (hctx : @Ch3z.BlkCtx ↥(chiefMod L N) (chiefCG (h.hE hstep)) (chiefAut H L N)
        (chiefImg (Setting.hHL hstep) (Setting.hHN hstep) T)
        (chiefImg (Setting.hHL hstep) (Setting.hHN hstep) M₂) 𝓗)
    {K₀ : Subgroup (MulAut ↥(chiefMod L N))} (hK₀ : K₀ ∈ 𝓗)
    (hAV : ∀ a ∈ A, ∀ v ∈ V, a * v = v * a) (hTV : ∀ t ∈ T, ∀ v ∈ V, t * v * t⁻¹ ∈ V) :
    ∃ c : G, ∃ hc : c ∈ H, (∀ v ∈ V, c * v = v * c) ∧ c ^ 2 = 1 ∧
      chiefPsi (Setting.hHL hstep) (Setting.hHN hstep) ⟨c, hc⟩ ∈ ⨆ K ∈ 𝓗, K ∧
      ∃ w ∈ (@CFSG.Quasithin.commV ↥(chiefMod L N) (chiefCG (h.hE hstep)) K₀),
        chiefPsi (Setting.hHL hstep) (Setting.hHN hstep) ⟨c, hc⟩ w ≠ w := by
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := Setting.hHL hstep
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := Setting.hHN hstep
  have hE := h.hE hstep
  let _ : CommGroup ↥(chiefMod L N) := chiefCG hE
  have hstrong := h.noStrong hB1 hstep hnc
  obtain ⟨hAe, hA1, hoff⟩ := h.offender hstep hnc
  have hAffJ : chiefImg hHL hHN A ≤ CFSG.Quasithin.ffJ (chiefAut H L N) :=
    CFSG.Quasithin.Ch3z.le_ffJ_of_offender hstrong (chiefImg_le_chiefAut hHL hHN A) hAe hA1 hoff
  obtain ⟨a, ha, haA, hψa⟩ : ∃ a : G, ∃ ha : a ∈ H, a ∈ A ∧ chiefPsi hHL hHN ⟨a, ha⟩ ≠ 1 := by
    by_contra hcon
    apply hA1
    rw [eq_bot_iff]
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_bot]
    by_contra hx1
    exact hcon ⟨x, x.2, Subgroup.mem_subgroupOf.mp hx, hx1⟩
  have ha2 : a ^ 2 = 1 := h.AT.2.1.2 a haA
  have hmove : ∃ K ∈ 𝓗, ∃ w ∈ @CFSG.Quasithin.commV ↥(chiefMod L N) (chiefCG hE) K,
      chiefPsi hHL hHN ⟨a, ha⟩ w ≠ w := by
    by_contra hcon
    push Not at hcon
    apply hψa
    let F : Subgroup ↥(chiefMod L N) :=
      { carrier := {v | chiefPsi hHL hHN ⟨a, ha⟩ v = v}
        one_mem' := by
          show chiefPsi hHL hHN ⟨a, ha⟩ 1 = 1
          exact map_one _
        mul_mem' := by
          intro u v hu hv
          have hu' : chiefPsi hHL hHN ⟨a, ha⟩ u = u := hu
          have hv' : chiefPsi hHL hHN ⟨a, ha⟩ v = v := hv
          show chiefPsi hHL hHN ⟨a, ha⟩ (u * v) = u * v
          rw [map_mul, hu', hv']
        inv_mem' := by
          intro u hu
          have hu' : chiefPsi hHL hHN ⟨a, ha⟩ u = u := hu
          show chiefPsi hHL hHN ⟨a, ha⟩ u⁻¹ = u⁻¹
          rw [map_inv, hu'] }
    have hsup : (⨆ K ∈ 𝓗, @CFSG.Quasithin.commV ↥(chiefMod L N) (chiefCG hE) K) ≤ F := by
      refine iSup₂_le fun K hK => ?_
      intro w hw
      exact hcon K hK w hw
    have htop : ∀ v : ↥(chiefMod L N), chiefPsi hHL hHN ⟨a, ha⟩ v = v := fun v => by
      have hv : v ∈ (⨆ K ∈ 𝓗, @CFSG.Quasithin.commV ↥(chiefMod L N) (chiefCG hE) K) := by
        rw [hctx.iSup_comm]
        exact Subgroup.mem_top v
      exact hsup hv
    exact MulEquiv.ext htop
  obtain ⟨K, hK, w, hw, hψw⟩ := hmove
  obtain ⟨t, ht, htK⟩ := hctx.trans hK hK₀
  obtain ⟨τH, hτT, hτt⟩ := Subgroup.mem_map.mp ht
  have hτT' : (τH : G) ∈ T := Subgroup.mem_subgroupOf.mp hτT
  obtain ⟨c, hcdef⟩ : ∃ c : G, c = (τH : G) * a * (τH : G)⁻¹ := ⟨_, rfl⟩
  have hc : c ∈ H := by
    rw [hcdef]
    exact H.mul_mem (H.mul_mem τH.2 ha) (H.inv_mem τH.2)
  have e : (⟨c, hc⟩ : ↥H) = τH * ⟨a, ha⟩ * τH⁻¹ := Subtype.ext hcdef
  have hPc : chiefPsi hHL hHN ⟨c, hc⟩ = t * chiefPsi hHL hHN ⟨a, ha⟩ * t⁻¹ := by
    rw [← hτt, e, map_mul, map_mul, map_inv]
  have hPa_mem : (⟨a, ha⟩ : ↥H) ∈ A.subgroupOf H := Subgroup.mem_subgroupOf.mpr haA
  have hPa : chiefPsi hHL hHN ⟨a, ha⟩ ∈ CFSG.Quasithin.ffJ (chiefAut H L N) :=
    hAffJ (Subgroup.mem_map_of_mem (chiefPsi hHL hHN) hPa_mem)
  have ht_aut : t ∈ chiefAut H L N := by
    rw [← hτt]
    exact chiefPsi_mem hHL hHN τH
  have hnorm := Subgroup.mem_normalizer_iff.mp
    (CFSG.Quasithin.B6.le_normalizer_ffJ (chiefAut H L N) ht_aut)
  have hmem : chiefPsi hHL hHN ⟨c, hc⟩ ∈ ⨆ K ∈ 𝓗, K := by
    rw [← hctx.ffJ_eq, hPc]
    exact (hnorm (chiefPsi hHL hHN ⟨a, ha⟩)).mp hPa
  have hcV : ∀ v ∈ V, c * v = v * c := by
    intro v hv
    have hv' : (τH : G)⁻¹ * v * (τH : G) ∈ V := by
      have := hTV (τH : G)⁻¹ (T.inv_mem hτT') v hv
      simpa only [inv_inv] using this
    have hcomm' := hAV a haA _ hv'
    rw [hcdef]
    calc (τH : G) * a * (τH : G)⁻¹ * v
        = (τH : G) * (a * ((τH : G)⁻¹ * v * (τH : G))) * (τH : G)⁻¹ := by group
      _ = (τH : G) * (((τH : G)⁻¹ * v * (τH : G)) * a) * (τH : G)⁻¹ := by rw [hcomm']
      _ = v * ((τH : G) * a * (τH : G)⁻¹) := by group
  have hc2 : c ^ 2 = 1 := by
    rw [hcdef, sq]
    calc (τH : G) * a * (τH : G)⁻¹ * ((τH : G) * a * (τH : G)⁻¹)
        = (τH : G) * (a * a) * (τH : G)⁻¹ := by group
      _ = 1 := by rw [← sq, ha2]; group
  have hkey : chiefPsi hHL hHN ⟨c, hc⟩ * t = t * chiefPsi hHL hHN ⟨a, ha⟩ := by
    rw [hPc]
    group
  have hcommK₀ : @CFSG.Quasithin.commV ↥(chiefMod L N) (chiefCG hE) K₀ =
      (@CFSG.Quasithin.commV ↥(chiefMod L N) (chiefCG hE) K).map t.toMonoidHom := by
    rw [← htK]
    exact CFSG.Quasithin.commV_map_conj_eq K t
  have hw₀ : t w ∈ @CFSG.Quasithin.commV ↥(chiefMod L N) (chiefCG hE) K₀ := by
    rw [hcommK₀]
    exact Subgroup.mem_map_of_mem t.toMonoidHom hw
  have hne : chiefPsi hHL hHN ⟨c, hc⟩ (t w) ≠ t w := by
    have h1 : chiefPsi hHL hHN ⟨c, hc⟩ (t w) = t (chiefPsi hHL hHN ⟨a, ha⟩ w) := by
      calc chiefPsi hHL hHN ⟨c, hc⟩ (t w) = (chiefPsi hHL hHN ⟨c, hc⟩ * t) w := rfl
        _ = (t * chiefPsi hHL hHN ⟨a, ha⟩) w := by rw [hkey]
        _ = t (chiefPsi hHL hHN ⟨a, ha⟩ w) := rfl
    rw [h1]
    intro heq
    exact hψw (MulEquiv.injective t heq)
  exact ⟨c, hc, hcV, hc2, hmem, t w, hw₀, hne⟩

end CFSG.Quasithin.H13.L319.S66

end
