module

public import CFSG.Quasithin.H13.GoldschmidtU43BP1

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

theorem Aset_add : ∀ τ α v w : V4, Aset τ α v → Aset τ α w → Aset τ α (v + w) := by
  decide +kernel

theorem vapp_add (g : MulAut (Multiplicative V4)) (v w : V4) :
    vapp g (v + w) = vapp g v + vapp g w := by
  unfold vapp
  rw [ofAdd_add, map_mul, toAdd_mul]

theorem vapp_zero (g : MulAut (Multiplicative V4)) : vapp g 0 = 0 := by
  unfold vapp
  rw [ofAdd_zero, map_one, toAdd_one]

theorem Aset_vapp {τ α v : V4} {ρ : MulAut (Multiplicative V4)} (hρ : ρ ∈ StabA τ α)
    (hv : Aset τ α v) : Aset τ α (vapp ρ v) := by
  rcases hv with rfl | rfl | rfl | rfl
  · rw [vapp_zero]; exact Or.inl rfl
  · exact hρ.2.1
  · exact hρ.2.2
  · rw [vapp_add]; exact Aset_add _ _ _ _ hρ.2.1 hρ.2.2

namespace Swap

variable {z t w a : G}

abbrev Pg (z t w a : G) : Subgroup G := Hz z ⊓ Subgroup.normalizer (Eg z t w a : Set G)

theorem U_le_P [Finite G] (s : Swap z t w) (ha : Good z t a) : Uz z ≤ Pg z t w a := by
  intro u hu
  refine ⟨Uz_le_Hz z hu, s.mem_normalizer_Eg_of ha (Uz_le_Hz z hu) fun x hx => ?_⟩
  obtain ⟨hxU, hA⟩ := hx
  have huxU : u * x * u⁻¹ ∈ Uz z := mul_mem (mul_mem hu hxU) ((Uz z).inv_mem hu)
  refine ⟨huxU, ?_⟩
  have e : s.hyp.θ ⟨u * x * u⁻¹, huxU⟩ = s.hyp.θ ⟨x, hxU⟩ := by
    have : (⟨u * x * u⁻¹, huxU⟩ : ↥(Uz z)) = ⟨u, hu⟩ * ⟨x, hxU⟩ * ⟨u, hu⟩⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv]
    have hc : ∀ p q : Multiplicative V4, p * q * p⁻¹ = q := fun p q => mul_inv_cancel_comm p q
    exact hc _ _
  rw [e]
  exact hA

theorem U_le_T [Finite G] (s : Swap z t w) : Uz z ≤ Tn z t := by
  intro u hu
  refine s.hyp.mem_Tn_of s.ht (Uz_le_Hz z hu) ?_
  have := s.hyp.comm_eq ⟨u, hu⟩ ⟨t, s.ht.1⟩
  have e : u * t * u⁻¹ = zp z (bq (Multiplicative.toAdd (s.hyp.θ ⟨u, hu⟩))
      (Multiplicative.toAdd (s.hyp.θ ⟨t, s.ht.1⟩))) * t := by
    rw [← this]; group
  rw [e]
  exact mul_mem (zp_z_mem z t _) (t_mem_Vg z t)

theorem T_le_P [Finite G] (s : Swap z t w) (ha : Good z t a) : Tn z t ≤ Pg z t w a :=
  fun _ hg => ⟨hg.1, s.T_le_normalizer ha hg⟩

theorem card_map_act_T [Finite G] (s : Swap z t w) :
    Nat.card (((Tn z t).subgroupOf (Hz z)).map s.hyp.act) = 4 := by
  have h1 := s.hyp.card_map_act_mul (Tn z t) s.U_le_T inf_le_left
  rw [s.hyp.card_Tn s.ht] at h1
  omega

theorem card_actP_le [Finite G] (s : Swap z t w) (ha : Good z t a) :
    Nat.card (((Pg z t w a).subgroupOf (Hz z)).map s.hyp.act) ≤ 12 := by
  set S := ((Pg z t w a).subgroupOf (Hz z)).map s.hyp.act with hS
  have hsub : (S : Set (MulAut (Multiplicative V4))) ⊆ StabA s.tauV (s.alphaV ha) := by
    intro g hg
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hg
    have hcP : (c : G) ∈ Pg z t w a := hc
    exact s.act_mem_StabA ha c.2 hcP.2
  rw [show Nat.card ↥S = Set.ncard (S : Set (MulAut (Multiplicative V4))) from
    Nat.card_coe_set_eq _]
  calc Set.ncard (S : Set (MulAut (Multiplicative V4)))
      ≤ Set.ncard (StabA s.tauV (s.alphaV ha)) := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = Nat.card (StabA s.tauV (s.alphaV ha)) := (Nat.card_coe_set_eq _).symm
    _ ≤ 12 := card_StabA_le (s.linePair_ta ha)

theorem twelve_dvd_actP [Finite G] (s : Swap z t w) (ha : Good z t a) :
    12 ∣ Nat.card (((Pg z t w a).subgroupOf (Hz z)).map s.hyp.act) := by
  have h := s.hyp
  set S := ((Pg z t w a).subgroupOf (Hz z)).map h.act with hS
  have h4 : 4 ∣ Nat.card S := by
    have hle : ((Tn z t).subgroupOf (Hz z)).map h.act ≤ S :=
      Subgroup.map_mono (fun x hx => s.T_le_P ha hx)
    have := Subgroup.card_dvd_of_le hle
    rwa [s.card_map_act_T] at this
  have h3 : 3 ∣ Nat.card S := by
    obtain ⟨ρ, hρS, hρ1, hρ3, -⟩ := exists_rho (s.linePair_ta ha)
    have hρO : ρ ∈ Oq := hρS.1
    obtain ⟨c, hc⟩ := h.mem_range_of_pow_three hρO hρ3
    have hcP : (c : G) ∈ Pg z t w a := by
      refine ⟨c.2, s.mem_normalizer_Eg_of ha c.2 fun x hx => ?_⟩
      obtain ⟨hxU, hA⟩ := hx
      have e := s.vapp_act c.2 hxU
      have hcc : h.act ⟨(c : G), c.2⟩ = ρ := hc
      rw [hcc] at e
      have hxcU : (c : G) * x * (c : G)⁻¹ ∈ Uz z :=
        (Subgroup.mem_normalizer_iff.mp (Hz_le_normalizer z c.2) x).mp hxU
      refine ⟨hxcU, ?_⟩
      rw [← e]
      exact Aset_vapp hρS hA
    have hρmem : ρ ∈ S := Subgroup.mem_map.mpr ⟨c, hcP, hc⟩
    have hord : orderOf ρ = 3 := orderOf_eq_prime hρ3 hρ1
    have := orderOf_dvd_natCard (⟨ρ, hρmem⟩ : ↥S)
    rwa [Subgroup.orderOf_mk, hord] at this
  exact (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h4 h3 : 4 * 3 ∣ _)

theorem card_P [Finite G] (s : Swap z t w) (ha : Good z t a) : Nat.card (Pg z t w a) = 384 := by
  have hle := s.card_actP_le ha
  have hdvd := s.twelve_dvd_actP ha
  have hpos : 0 < Nat.card (((Pg z t w a).subgroupOf (Hz z)).map s.hyp.act) := Nat.card_pos
  have h12 : Nat.card (((Pg z t w a).subgroupOf (Hz z)).map s.hyp.act) = 12 :=
    le_antisymm hle (Nat.le_of_dvd hpos hdvd)
  have := s.hyp.card_map_act_mul (Pg z t w a) (s.U_le_P ha) inf_le_left
  rw [h12] at this
  omega

theorem exists_sigma [Finite G] (s : Swap z t w) (ha : Good z t a) :
    ∃ σ : G, σ ∈ Pg z t w a ∧ orderOf σ = 3 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hd : 3 ∣ Nat.card (Pg z t w a) := by rw [s.card_P ha]; norm_num
  obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Pg z t w a)) 3 hd
  exact ⟨σ, σ.2, by rw [Subgroup.orderOf_coe]; exact hσ⟩

end Swap

end CFSG.Quasithin.H13.U43
