module

public import CFSG.Quasithin.Recognition.RuTypeJ27h

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace Sigma

theorem exists_conj_mul_order_three : ∀ a : SigmaL2F4, a ^ 2 = 1 → a ≠ 1 →
    ∃ g : SigmaL2F4, (a * (g * a * g⁻¹)) ^ 3 = 1 ∧ a * (g * a * g⁻¹) ≠ 1 := by
  decide +kernel

theorem exists_center_U0 : ∃ u ∈ U0, u ≠ 1 ∧ ∀ g ∈ SP0, g * u = u * g := by
  decide +kernel

theorem centralizer_center_U0 : ∀ u ∈ U0, u ≠ 1 → (∀ g ∈ SP0, g * u = u * g) →
    ∀ g : SigmaL2F4, g * u = u * g → g ∈ SP0 := by
  decide +kernel

end Sigma

variable {G : Type} [Group G]

namespace RuDataM

variable (M : RuDataM G) [Finite G]

theorem exists_conj_inv_bel {x : G} (hxH : x ∈ ruH M.T) (hx2 : x ^ 2 = 1) (hxQ : x ∉ ruQ M.T) :
    ∃ h ∈ ruH M.T, (h * x * h⁻¹) * M.bel * (h * x * h⁻¹)⁻¹ = (M.bel : G)⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hxx : x * x = 1 := by rw [← pow_two]; exact hx2
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  set a := M.φ ⟨x, hxH⟩ with ha
  have ha2 : a ^ 2 = 1 := by
    rw [ha, ← map_pow, show (⟨x, hxH⟩ : ruH M.T) ^ 2 = 1 from Subtype.ext hx2, map_one]
  have ha1 : a ≠ 1 := by
    intro h1
    apply hxQ
    have : (⟨x, hxH⟩ : ruH M.T) ∈ M.φ.ker := h1
    rw [M.φ_ker, Subgroup.mem_subgroupOf] at this
    exact this
  obtain ⟨gs, hg3, hg1⟩ := Sigma.exists_conj_mul_order_three a ha2 ha1
  obtain ⟨⟨g, hgH⟩, hg⟩ := M.φ_surj gs
  set y : G := x * (g * x * g⁻¹) with hy
  have hyH : y ∈ ruH M.T := mul_mem hxH (mul_mem (mul_mem hgH hxH) (inv_mem hgH))
  set Y : ruH M.T := ⟨y, hyH⟩
  have hφy : M.φ Y = a * (gs * a * gs⁻¹) := by
    rw [← hg, ha, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    rfl
  have hy3Q : y ^ 3 ∈ ruQ M.T := by
    have : Y ^ 3 ∈ M.φ.ker := by
      rw [MonoidHom.mem_ker, map_pow, hφy, hg3]
    rw [M.φ_ker, Subgroup.mem_subgroupOf] at this
    simpa [Y] using this
  set d := y ^ (2 ^ 11) with hd
  have hd3 : d ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := ruQ M.T) (x := ⟨y ^ 3, hy3Q⟩)
    rw [M.toRuData.card_Q] at h
    have h' : (y ^ 3) ^ (2 ^ 11) = 1 := by
      have := congrArg Subtype.val h
      simpa using this
    rw [hd, ← pow_mul, mul_comm, pow_mul, h']
  have hd1 : d ≠ 1 := by
    intro h1
    apply hg1
    have hY : Y ^ (2 ^ 11) = 1 :=
      Subtype.ext (by rw [SubgroupClass.coe_pow, OneMemClass.coe_one]; exact h1)
    have hw : (a * (gs * a * gs⁻¹)) ^ (2 ^ 11) = (a * (gs * a * gs⁻¹)) ^ 2 :=
      pow_eq_pow_of_modEq (by norm_num [Nat.ModEq]) hg3
    have h2 : (a * (gs * a * gs⁻¹)) ^ 2 = 1 := by
      have := congrArg M.φ hY
      rw [map_pow, hφy, map_one, hw] at this
      exact this
    calc a * (gs * a * gs⁻¹) = (a * (gs * a * gs⁻¹)) ^ 3 * ((a * (gs * a * gs⁻¹)) ^ 2)⁻¹ := by
          group
      _ = 1 := by rw [hg3, h2]; group
  have hord : orderOf d = 3 := orderOf_eq_prime hd3 hd1
  have hinv : x * y * x⁻¹ = y⁻¹ := by
    rw [hy]
    calc x * (x * (g * x * g⁻¹)) * x⁻¹ = (x * x) * (g * x * g⁻¹) * x⁻¹ := by group
      _ = g * x * g⁻¹ * x⁻¹ := by rw [hxx, one_mul]
      _ = g * x⁻¹ * g⁻¹ * x⁻¹ := by rw [hxinv]
      _ = (x * (g * x * g⁻¹))⁻¹ := by group
  have hxd : x * d * x⁻¹ = d⁻¹ := by rw [hd, ← conj_pow, hinv, inv_pow]
  obtain ⟨h, hh, h1 | h1⟩ := M.exists_conj_bel (y := d) (pow_mem hyH _) hord
  · refine ⟨h, hh, ?_⟩
    calc (h * x * h⁻¹) * M.bel * (h * x * h⁻¹)⁻¹ = h * (x * d * x⁻¹) * h⁻¹ := by rw [← h1]; group
      _ = (h * d * h⁻¹)⁻¹ := by rw [hxd]; group
      _ = _ := by rw [h1]
  · refine ⟨h, hh, ?_⟩
    have hb : (M.bel : G) = (h * d * h⁻¹)⁻¹ := by rw [h1, inv_inv]
    calc (h * x * h⁻¹) * M.bel * (h * x * h⁻¹)⁻¹ = h * (x * d * x⁻¹)⁻¹ * h⁻¹ := by
          rw [hb]; group
      _ = h * d * h⁻¹ := by rw [hxd, inv_inv]
      _ = _ := h1

theorem conj_B_of_inv {y : G} (hy : y * M.bel * y⁻¹ = (M.bel : G)⁻¹) {b : G} (hb : b ∈ M.B) :
    y * b * y⁻¹ = b⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  rw [← conj_zpow, hy, inv_zpow]

theorem mul_eq_conj_of_inv {y : G} (hy : y * M.bel * y⁻¹ = (M.bel : G)⁻¹) {b : G}
    (hb : b ∈ M.B) : y * b = b * y * b⁻¹ := by
  have h1 : y⁻¹ * b * y = b⁻¹ := by
    have h := M.conj_B_of_inv hy (inv_mem hb)
    calc y⁻¹ * b * y = y⁻¹ * (y * b⁻¹ * y⁻¹) * y := by rw [h, inv_inv]
      _ = b⁻¹ := by group
  have h3 : b ^ 3 = 1 := M.pow_three_of_mem_B hb
  have hb2 : b⁻¹ * b⁻¹ = b := by
    calc b⁻¹ * b⁻¹ = b⁻¹ * b⁻¹ * b ^ 3 := by rw [h3, mul_one]
      _ = b := by group
  calc y * b = y * (b⁻¹ * b⁻¹) := by rw [hb2]
    _ = y * (y⁻¹ * b * y) * b⁻¹ := by rw [h1, mul_assoc]
    _ = b * y * b⁻¹ := by group

theorem sq_eq_one_of_inv {x : G} (hx : x * M.bel * x⁻¹ = (M.bel : G)⁻¹) (hx2 : x * x ∈ M.B) :
    x * x = 1 := by
  have hc : x * (x * x) * x⁻¹ = x * x := by group
  have hi := M.conj_B_of_inv hx hx2
  rw [hc] at hi
  rcases M.mem_B_iff.mp hx2 with h | h | h
  · exact h
  · exact absurd (h.symm.trans (hi.trans (congrArg (·⁻¹) h))) M.bel_ne_inv
  · have e : (M.bel : G)⁻¹ = M.bel := h.symm.trans (hi.trans (by rw [h, inv_inv]))
    exact absurd e.symm M.bel_ne_inv

theorem S0_le_H : M.S0 ≤ ruH M.T := fun _ hx =>
  M.toRuData.T_le_H (M.toRuData.S_le_T (M.mem_S0.mp hx).1)

theorem eq_one_of_mem_S0_Q {x : G} (hx : x ∈ M.S0) (hxQ : x ∈ ruQ M.T) : x = 1 := by
  by_contra h1
  have hx2 : x ^ 2 = 1 := M.S0_elem.2 x hx
  obtain ⟨g, hg⟩ := isConj_iff.mp (M.lemma_J26.2.2.2.2.1 x hxQ hx2 h1)
  exact M.lemma_J23_2 g (hg ▸ hx)

@[expose] noncomputable def φS0 : M.S0 →* SigmaL2F4 :=
  M.φ.comp (Subgroup.inclusion M.S0_le_H)

theorem φS0_injective : Function.Injective M.φS0 := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have : Subgroup.inclusion M.S0_le_H x ∈ M.φ.ker := hx
  rw [M.φ_ker, Subgroup.mem_subgroupOf] at this
  exact Subtype.ext (M.eq_one_of_mem_S0_Q x.2 this)

theorem range_φS0 : M.φS0.range = Sigma.U0 := by
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨x, rfl⟩
    exact M.φ_S_mem (M.mem_S0.mp x.2).1
  · rw [Sigma.card_U0, ← Nat.card_congr (MonoidHom.ofInjective M.φS0_injective).toEquiv,
      M.card_S0]

theorem exists_s1 : ∃ s, ∃ hs : s ∈ M.S0, s ≠ 1 ∧ ∀ g ∈ Sigma.SP0,
    g * M.φ ⟨s, M.S0_le_H hs⟩ = M.φ ⟨s, M.S0_le_H hs⟩ * g := by
  obtain ⟨u, hu, hu1, huc⟩ := Sigma.exists_center_U0
  rw [← M.range_φS0] at hu
  obtain ⟨x, rfl⟩ := hu
  refine ⟨x, x.2, fun h => hu1 ?_, huc⟩
  rw [show x = 1 from Subtype.ext h, map_one]

@[expose] noncomputable def s1el : G := M.exists_s1.choose

theorem s1el_mem_S0 : M.s1el ∈ M.S0 := M.exists_s1.choose_spec.fst

theorem s1el_ne_one : M.s1el ≠ 1 := M.exists_s1.choose_spec.snd.1

theorem s1el_central : ∀ g ∈ Sigma.SP0, g * M.φ ⟨M.s1el, M.S0_le_H M.s1el_mem_S0⟩ =
    M.φ ⟨M.s1el, M.S0_le_H M.s1el_mem_S0⟩ * g := M.exists_s1.choose_spec.snd.2

theorem mem_T_of_comm_s1el {x : G} (hx : x ∈ ruH M.T) (hc : x * M.s1el = M.s1el * x) :
    x ∈ (M.T : Subgroup G) := by
  have hu : M.φ ⟨M.s1el, M.S0_le_H M.s1el_mem_S0⟩ ∈ Sigma.U0 := by
    rw [← M.range_φS0]
    exact ⟨⟨M.s1el, M.s1el_mem_S0⟩, rfl⟩
  have hu1 : M.φ ⟨M.s1el, M.S0_le_H M.s1el_mem_S0⟩ ≠ 1 := by
    intro h
    apply M.s1el_ne_one
    have : (⟨M.s1el, M.S0_le_H M.s1el_mem_S0⟩ : ruH M.T) ∈ M.φ.ker := h
    rw [M.φ_ker, Subgroup.mem_subgroupOf] at this
    exact M.eq_one_of_mem_S0_Q M.s1el_mem_S0 this
  have hφ : M.φ ⟨x, hx⟩ ∈ Sigma.SP0 := by
    refine Sigma.centralizer_center_U0 _ hu hu1 M.s1el_central _ ?_
    rw [← map_mul, ← map_mul]
    exact congrArg M.φ (Subtype.ext hc)
  obtain ⟨t, ht, hφt⟩ := M.exists_T_of_SP0 hφ
  have hk : (⟨t, M.toRuData.T_le_H ht⟩ : ruH M.T)⁻¹ * ⟨x, hx⟩ ∈ M.φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hφt, inv_mul_cancel]
  rw [M.φ_ker, Subgroup.mem_subgroupOf] at hk
  have hQT : ruQ M.T ≤ (M.T : Subgroup G) := M.Q_le_T
  have e : x = t * (t⁻¹ * x) := by group
  rw [e]
  exact mul_mem ht (hQT hk)

theorem mem_S_of_comm_s1el {x : G} (hx : x ∈ ruH M.T) (hc : x * M.s1el = M.s1el * x) :
    x ∈ ruS M.L := by
  have hxT := M.mem_T_of_comm_s1el hx hc
  have hxL : x ∈ M.L := M.toRuData.T_le_L hxT
  obtain ⟨k, hk⟩ := M.θ_mem_of_comm M.s1el_mem_S0 M.s1el_ne_one (l := ⟨x, hxL⟩) hc
  have hP := M.θ_mem_P0 hxT
  rw [hk] at hP
  have h1 : SL3.c0 ^ k.val = 1 := by
    have h7 : orderOf (SL3.c0 ^ k.val) ∣ 7 := orderOf_dvd_of_pow_eq_one (by
      rw [← pow_mul, mul_comm, pow_mul, SL3.c0_pow_seven, one_pow])
    have h8 : orderOf (SL3.c0 ^ k.val) ∣ 8 := by
      rw [← SL3.card_P0]
      exact Subgroup.orderOf_dvd_natCard _ hP
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (by norm_num) h7 h8)
  have hker : (⟨x, hxL⟩ : M.L) ∈ M.θ.ker := by rw [MonoidHom.mem_ker, hk, h1]
  rw [M.θ_ker, Subgroup.mem_subgroupOf] at hker
  exact hker

theorem pow_four_of_comm_s1el {x : G} (hx : x ∈ ruH M.T) (hc : x * M.s1el = M.s1el * x) :
    x ^ 4 = 1 :=
  M.pow_four_S (M.mem_S_of_comm_s1el hx hc)

end RuDataM

end CFSG.Quasithin.RuType
