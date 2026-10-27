module

public import CFSG.Quasithin.EmptyFaithful.S153E56P13

public section

namespace CFSG.Quasithin

namespace S153E56p

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S153E CFSG.Quasithin.S153E57
  CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

section Fixed

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {s : ℕ} {y t₁ : G}
  (S : Ctx56 T Mc M V₁ V₂ t N₁ N₂ s y t₁)

include S

theorem exists_zS : ∃ z ∈ ZS153 T M V₁, z ∉ quasithinOmegaOneCenter T := by
  by_contra h
  push Not at h
  have hle : ZS153 T M V₁ ≤ quasithinOmegaOneCenter T := h
  have := Subgroup.card_le_of_le hle
  rw [Decomp153.card_ZS S.cx.c.hyp S.cx.c.decomp, Z_card S.cx] at this
  omega

theorem ZS_index_two : ((quasithinOmegaOneCenter T).subgroupOf (ZS153 T M V₁)).index = 2 := by
  have hmul := Subgroup.card_mul_index ((quasithinOmegaOneCenter T).subgroupOf (ZS153 T M V₁))
  have hc : Nat.card ↥((quasithinOmegaOneCenter T).subgroupOf (ZS153 T M V₁)) = 2 := by
    rw [← Z_card S.cx]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Z_le_ZS S.cx)).toEquiv
  rw [hc, Decomp153.card_ZS S.cx.c.hyp S.cx.c.decomp] at hmul
  omega

theorem conj_ZS {u : G} (hu : u ∈ ZS153 T M V₁) : t₁ * u * t₁⁻¹ ∈ ZS153 T M V₁ := by
  refine ⟨conj_t₁_V S hu.1, Subgroup.mem_centralizer_iff.2 fun s' hs' => ?_⟩
  have hN := Hyp153.T_le_normalizer_Sgp153 S.cx.c.hyp S.cx.c.decomp (t₁_mem_T S)
  have hs'' : t₁⁻¹ * s' * t₁ ∈ Sgp153 T V₁ := by
    have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (Sgp153 T V₁ : Set G)).inv_mem hN)
      s').1 hs'
    simpa using this
  have h1 := Subgroup.mem_centralizer_iff.1 hu.2 _ hs''
  calc s' * (t₁ * u * t₁⁻¹) = t₁ * ((t₁⁻¹ * s' * t₁) * u) * t₁⁻¹ := by group
    _ = t₁ * (u * (t₁⁻¹ * s' * t₁)) * t₁⁻¹ := by rw [h1]
    _ = (t₁ * u * t₁⁻¹) * s' := by group

theorem t₁_comm_ZS {u : G} (hu : u ∈ ZS153 T M V₁) :
    t₁ * u * t₁⁻¹ * u⁻¹ ∈ quasithinOmegaOneCenter T := by
  by_cases huZ : u ∈ quasithinOmegaOneCenter T
  · rw [t₁_conj_Z S huZ]
    simp
  · have hu' := conj_ZS S hu
    have hu'Z : t₁ * u * t₁⁻¹ ∉ quasithinOmegaOneCenter T := fun h => by
      apply huZ
      have e : u = t₁⁻¹ * (t₁ * u * t₁⁻¹) * t₁ := by group
      rw [e, t₁_inv_conj_Z S h]
      exact h
    have hmem : (⟨u, hu⟩ : ↥(ZS153 T M V₁))⁻¹ * ⟨t₁ * u * t₁⁻¹, hu'⟩ ∈
        (quasithinOmegaOneCenter T).subgroupOf (ZS153 T M V₁) := by
      rw [Subgroup.mul_mem_iff_of_index_two (ZS_index_two S)]
      constructor
      · intro h
        exact absurd (by simpa [Subgroup.mem_subgroupOf] using h) huZ
      · intro h
        exact absurd (by simpa [Subgroup.mem_subgroupOf] using h) hu'Z
    have hw : u⁻¹ * (t₁ * u * t₁⁻¹) ∈ quasithinOmegaOneCenter T := by
      simpa [Subgroup.mem_subgroupOf] using hmem
    have hc := Z_comm_Mc S hw (U_le_Mc S (ZS_le_U S.cx hu))
    have e : t₁ * u * t₁⁻¹ * u⁻¹ = u * (u⁻¹ * (t₁ * u * t₁⁻¹)) * u⁻¹ := by group
    rw [e, ← hc]
    simpa using hw

theorem fixed_sub {u : G} (hu : u ∈ ZS153 T M V₁) :
    u ∈ centralizerMod (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)
      (Xgp153 T M V₁ Mc y ⊔ Subgroup.zpowers t₁) := by
  have hle : Xgp153 T M V₁ Mc y ⊔ Subgroup.zpowers t₁ ≤
      centralizerMod (quasithinOmegaOneCenter T) ⊤ (ZS153 T M V₁) := by
    refine sup_le (fun x hx => ⟨Subgroup.mem_top _, X_le_NZ S hx, fun u hu => ?_⟩)
      (Subgroup.zpowers_le.2 ⟨Subgroup.mem_top _, t₁_mem_NZ' S, fun u hu => t₁_comm_ZS S hu⟩)
    exact S.hG.X_perp x hx u ⟨ZS_le_V S.cx hu, ZS_le_U S.cx hu⟩
  refine ⟨ZS_le_U S.cx hu, Mc_le_NZ S.cx (U_le_Mc S (ZS_le_U S.cx hu)), fun g hg => ?_⟩
  have h1 := (hle hg).2.2 u hu
  have e : u * g * u⁻¹ * g⁻¹ = (g * u * g⁻¹ * u⁻¹)⁻¹ := by group
  rw [e]
  exact Subgroup.inv_mem _ h1

theorem tau_aa : tau S (aa S) = aq S := by
  obtain ⟨c', hc', htt⟩ := tau_sq S
  have h1 : tau S (aa S) = rho S.cx c' (aq S) := by
    rw [← tau_aq S, ← MulAut.mul_apply, htt]
  rw [h1, aq_eq]
  have hcn : (c' : G) ∈ Mc := T_le_Mc S.cx hc'.1
  rw [← pi_conj S.cx c' hcn]
  congr 1
  apply Subtype.ext
  show (c' : G) * (t₁⁻¹ * zp S * t₁) * (c' : G)⁻¹ = t₁⁻¹ * zp S * t₁
  have hv : t₁⁻¹ * zp S * t₁ ∈ VZ T M := conj_t₁_inv_V S (Z'_le_V S (zp_mem S))
  have := Subgroup.mem_centralizer_iff.1 hc'.2 _ hv
  rw [← this]
  group

theorem fixed_ctr {u : G} (hu : u ∈ centralizerMod (quasithinOmegaOneCenter T)
    (UH153 T M V₁ Mc) (Xgp153 T M V₁ Mc y ⊔ Subgroup.zpowers t₁)) :
    pi S.cx ⟨u, hu.1⟩ = 1 ∨ pi S.cx ⟨u, hu.1⟩ = aa S * aq S := by
  have hsplit := split_model S
  set q := pi S.cx ⟨u, hu.1⟩ with hq
  have hX : ∀ (x : G) (hx : x ∈ Xgp153 T M V₁ Mc y), rhoX S hx q = q := by
    intro x hx
    have h1 := hu.2.2 x (Subgroup.mem_sup_left hx)
    rw [hq, rhoX_pi]
    have e : x * u * x⁻¹ = (u * x * u⁻¹ * x⁻¹)⁻¹ * u := by group
    have hz : (u * x * u⁻¹ * x⁻¹)⁻¹ ∈ quasithinOmegaOneCenter T := Subgroup.inv_mem _ h1
    have e2 : (⟨x * u * x⁻¹, U_conj_mem (X_le_Mc S hx) hu.1⟩ : ↥(UH153 T M V₁ Mc)) =
        ⟨(u * x * u⁻¹ * x⁻¹)⁻¹, Z_le_U S hz⟩ * ⟨u, hu.1⟩ := Subtype.ext e
    rw [e2, map_mul, (pi_eq_one_iff S.cx _).2 hz, one_mul]
  have hτ : tau S q = q := by
    have h1 := hu.2.2 t₁ (Subgroup.mem_sup_right (Subgroup.mem_zpowers t₁))
    rw [hq, tau_pi]
    have e : t₁ * u * t₁⁻¹ = (u * t₁ * u⁻¹ * t₁⁻¹)⁻¹ * u := by group
    have hz : (u * t₁ * u⁻¹ * t₁⁻¹)⁻¹ ∈ quasithinOmegaOneCenter T := Subgroup.inv_mem _ h1
    have e2 : (⟨t₁ * u * t₁⁻¹, conj_t₁_U S hu.1⟩ : ↥(UH153 T M V₁ Mc)) =
        ⟨(u * t₁ * u⁻¹ * t₁⁻¹)⁻¹, Z_le_U S hz⟩ * ⟨u, hu.1⟩ := Subtype.ext e
    rw [e2, map_mul, (pi_eq_one_iff S.cx _).2 hz, one_mul]
  obtain ⟨e, he, e', he', hqee⟩ := Et_dec S (y := y) (t₁ := t₁) q
  have hXe : ∀ (x : G) (hx : x ∈ Xgp153 T M V₁ Mc y), rhoX S hx e = e := by
    intro x hx
    have h1 := hX x hx
    rw [hqee, map_mul] at h1
    exact (hsplit.dec_unique ((rhoX_isOO S hx).map₁ e he) he ((rhoX_isOO S hx).map₂ e' he') he' h1).1
  have hτe : tau S e = e' ∧ tau S e' = e := by
    have h1 := hτ
    rw [hqee, map_mul, Ut_comm S.cx] at h1
    have := hsplit.dec_unique (tau_map₂ S e' he') he (tau_map₁ S e he) he' h1
    exact ⟨this.2, this.1⟩
  have he1 : e = 1 ∨ e = aa S := by
    obtain ⟨ê, hê, rfl⟩ := (mem_Et1 S).1 he
    have hcomm : ∀ x ∈ Xgp153 T M V₁ Mc y, ⁅x, (ê : G)⁆ = 1 := by
      intro x hx
      have hc := comm_XE S hx hê
      have h1 := hXe x hx
      rw [rhoX_pi] at h1
      have e1 : x * (ê : G) * x⁻¹ = ⁅x, (ê : G)⁆ * ê := by
        simp only [commutatorElement_def]
        group
      have e2 : (⟨x * (ê : G) * x⁻¹, U_conj_mem (X_le_Mc S hx) ê.2⟩ : ↥(UH153 T M V₁ Mc)) =
          ⟨⁅x, (ê : G)⁆, S.hG.Z'_le_U hc⟩ * ê := Subtype.ext e1
      rw [e2, map_mul] at h1
      have h3 : pi S.cx ⟨⁅x, (ê : G)⁆, S.hG.Z'_le_U hc⟩ = 1 := mul_eq_right.1 h1
      have h4 := (pi_eq_one_iff S.cx _).1 h3
      have h5 : ⁅x, (ê : G)⁆ ∈ quasithinOmegaOneCenter T ⊓
          conjSubgroup (quasithinOmegaOneCenter T) y := ⟨h4, hc⟩
      rw [S.hG.Z_inf_Z', Subgroup.mem_bot] at h5
      exact h5
    obtain ⟨b, hb, hbz⟩ := (exPair_U' S).dc (B := quasithinOmegaOneCenter T) S.hG.Z_le_U'
      (E_le_U' S hê) (fun w hw hwc => by
        have hwX : w ∈ Xgp153 T M V₁ Mc y := by
          rw [S.hG.X_eq]
          refine ⟨hw, Subgroup.mem_centralizer_iff.2 fun z hz => ?_⟩
          exact commutatorElement_eq_one_iff_mul_comm.1 (hwc z hz)
        rw [← commutatorElement_inv]
        have := hcomm w hwX
        rw [this]
        simp)
    have hbU : b ∈ UH153 T M V₁ Mc := Z_le_U S hb
    have hcU : (ê : G) * b⁻¹ ∈ UH153 T M V₁ Mc := S.hG.Z'_le_U hbz
    have e1 : ê = ⟨(ê : G) * b⁻¹, hcU⟩ * ⟨b, hbU⟩ := by
      apply Subtype.ext
      show (ê : G) = (ê : G) * b⁻¹ * b
      group
    have e2 : pi S.cx ê = pi S.cx ⟨(ê : G) * b⁻¹, hcU⟩ := by
      conv_lhs => rw [e1]
      rw [map_mul, (pi_eq_one_iff S.cx ⟨b, hbU⟩).2 hb, mul_one]
    rw [e2]
    rcases (mem_Z'_iff S).1 hbz with h | h
    · left
      have : (⟨(ê : G) * b⁻¹, hcU⟩ : ↥(UH153 T M V₁ Mc)) = 1 := Subtype.ext h
      rw [this, map_one]
    · right
      have : (⟨(ê : G) * b⁻¹, hcU⟩ : ↥(UH153 T M V₁ Mc)) = ⟨zp S, zp_mem_U S⟩ := Subtype.ext h
      rw [this, aa_eq]
  rcases he1 with rfl | rfl
  · left
    have : e' = 1 := by rw [← hτe.1, map_one]
    rw [hqee, this, mul_one]
  · right
    have : e' = aq S := by rw [← hτe.1, tau_aa]
    rw [hqee, this]

theorem fixed_field : ZS153 T M V₁ = centralizerMod (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)
    (Xgp153 T M V₁ Mc y ⊔ Subgroup.zpowers t₁) := by
  obtain ⟨u₀, hu₀, hu₀Z⟩ := exists_zS S
  refine le_antisymm (fun u hu => fixed_sub S hu) (fun u hu => ?_)
  have h1 := fixed_ctr S hu
  have hu₀c := fixed_sub S (y := y) hu₀
  have h0 := fixed_ctr S hu₀c
  have hq₀ : pi S.cx ⟨u₀, hu₀c.1⟩ ≠ 1 := fun h => hu₀Z ((pi_eq_one_iff S.cx _).1 h)
  have hq₀' : pi S.cx ⟨u₀, hu₀c.1⟩ = aa S * aq S := h0.resolve_left hq₀
  rcases h1 with h | h
  · exact Z_le_ZS S.cx ((pi_eq_one_iff S.cx _).1 h)
  · have h2 : pi S.cx ⟨u₀, hu₀c.1⟩ = pi S.cx ⟨u, hu.1⟩ := hq₀'.trans h.symm
    have hz := (pi_eq_iff S.cx _ _).1 h2
    have e : u = u₀ * (u₀⁻¹ * u) := by group
    rw [e]
    exact (ZS153 T M V₁).mul_mem hu₀ (Z_le_ZS S.cx hz)

end Fixed

end S153E56p

end CFSG.Quasithin
