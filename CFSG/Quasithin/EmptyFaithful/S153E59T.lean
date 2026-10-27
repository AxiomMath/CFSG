module

public import CFSG.Quasithin.EmptyFaithful.S153E59S
public import CFSG.Quasithin.EmptyFaithful.T1531Stage4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E59

section IndexThree

variable {X : Type*} [Group X] [Finite X]

theorem false_of_card_112 {Hs Ks Y : Subgroup X} (hKH : Ks ≤ Hs) (hsimple : IsSimpleGroup ↥Ks)
    (hK : Nat.card ↥Ks = 168) (hYH : Y ≤ Hs) (hH : Nat.card ↥Hs = 336) (hY : Nat.card ↥Y = 112) :
    False := by
  let Y' : Subgroup ↥Hs := Y.subgroupOf Hs
  let K' : Subgroup ↥Hs := Ks.subgroupOf Hs
  have hcY : Nat.card ↥Y' = 112 := by
    rw [← hY]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYH).toEquiv
  have hcK : Nat.card ↥K' = 168 := by
    rw [← hK]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv
  have : IsSimpleGroup ↥Ks := hsimple
  have hsK' : IsSimpleGroup ↥K' := (Subgroup.subgroupOfEquivOfLe hKH).isSimpleGroup
  have h3 : Y'.index = 3 := by
    have := Subgroup.card_mul_index Y'
    rw [hcY, hH] at this
    omega
  let φ : ↥K' →* Equiv.Perm (↥Hs ⧸ Y') := MulAction.toPermHom ↥K' (↥Hs ⧸ Y')
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hsK' φ.ker φ.normal_ker with hb | ht
  · have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 hb
    have h1 : Nat.card ↥K' ≤ Nat.card (Equiv.Perm (↥Hs ⧸ Y')) := Nat.card_le_card_of_injective φ hinj
    have h2 : Nat.card (↥Hs ⧸ Y') = 3 := by
      rw [← Subgroup.index, h3]
    rw [Nat.card_perm, h2, hcK] at h1
    norm_num [Nat.factorial] at h1
  · have hKY : K' ≤ Y' := by
      intro k hk
      have h1 : φ ⟨k, hk⟩ = 1 := by
        have : (⟨k, hk⟩ : ↥K') ∈ φ.ker := by rw [ht]; exact Subgroup.mem_top _
        exact MonoidHom.mem_ker.1 this
      have h2 := congrArg (fun p : Equiv.Perm (↥Hs ⧸ Y') => p (QuotientGroup.mk 1)) h1
      simp only [Equiv.Perm.coe_one, id_eq] at h2
      have h3' : (QuotientGroup.mk (k * 1) : ↥Hs ⧸ Y') = QuotientGroup.mk 1 := h2
      rw [QuotientGroup.eq] at h3'
      simpa using h3'
    have := Subgroup.card_dvd_of_le hKY
    rw [hcK, hcY] at this
    omega

end IndexThree

section MInf

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  (cx : Ctx15350 T Mc M V₁ V₂ t) {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ}
  {y t₁ : G}

include cx in
theorem inf_Mc_le_T (c : Chain15358 cx N₁ N₂ g s y t₁) :
    M ⊓ Mc ≤ T := by
  have hH := hstarFacts cx c.h58 c.ht₁.1 c.ht₁.2
  have hTX : T ≤ M ⊓ Mc := le_inf (S153E.T_le_M cx) (S153E.T_le_Mc cx)
  have hX₀M : M ⊓ Mc ≤ Mc := inf_le_right
  have hQT : pCoreOf 2 Mc ≤ T := S153E.Q_le_T cx
  have hQX₀ : pCoreOf 2 Mc ≤ M ⊓ Mc := hQT.trans hTX
  have hcT := card_eq_card_pCoreOf_mul cx hQT (S153E.T_le_Mc cx)
  have hcTeq := card_T_eq cx hH
  have hQpos : 0 < Nat.card ↥(pCoreOf 2 Mc) := Nat.card_pos
  have hT16 : Nat.card ↥((T.subgroupOf Mc).map (rho cx)) = 16 := by
    have h : Nat.card ↥(pCoreOf 2 Mc) * Nat.card ↥((T.subgroupOf Mc).map (rho cx)) =
        Nat.card ↥(pCoreOf 2 Mc) * 16 := by
      rw [← hcT, hcTeq]
      ring
    exact Nat.eq_of_mul_eq_mul_left hQpos h
  have hcX := card_eq_card_pCoreOf_mul cx hQX₀ hX₀M
  have h3 : ¬ 3 ∣ Nat.card ↥(M ⊓ Mc) := cx.r49.threePrime_MH Mc (isHTM153_mc cx.c)
  have hY3 : ¬ 3 ∣ Nat.card ↥(((M ⊓ Mc).subgroupOf Mc).map (rho cx)) := by
    intro hd
    exact h3 (hcX ▸ Dvd.dvd.mul_left hd _)
  have hle : (T.subgroupOf Mc).map (rho cx) ≤ ((M ⊓ Mc).subgroupOf Mc).map (rho cx) :=
    Subgroup.map_mono (fun x hx => hTX hx)
  have hd16 : 16 ∣ Nat.card ↥(((M ⊓ Mc).subgroupOf Mc).map (rho cx)) := by
    have := Subgroup.card_dvd_of_le hle
    rwa [hT16] at this
  have hYH : ((M ⊓ Mc).subgroupOf Mc).map (rho cx) ≤ HStar153 T M V₁ Mc := by
    rw [← range_rho cx]
    exact Subgroup.map_le_range _ _
  have hd336 : Nat.card ↥(((M ⊓ Mc).subgroupOf Mc).map (rho cx)) ∣ 336 := by
    have := Subgroup.card_dvd_of_le hYH
    rwa [hH.card_Hs] at this
  have hY16 : Nat.card ↥(((M ⊓ Mc).subgroupOf Mc).map (rho cx)) = 16 := by
    obtain ⟨k, hk⟩ := hd16
    rw [hk] at hd336 hY3 ⊢
    have hk21 : k ∣ 21 := by
      have : 16 * k ∣ 16 * 21 := by simpa using hd336
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
    have hk21' : k ≤ 21 := Nat.le_of_dvd (by norm_num) hk21
    have hk17 : k = 1 ∨ k = 7 := by
      interval_cases k <;> omega
    rcases hk17 with rfl | rfl
    · rfl
    · exfalso
      exact false_of_card_112 (Hs := HStar153 T M V₁ Mc) (Ks := oTwoUpper (HStar153 T M V₁ Mc))
        (Y := ((M ⊓ Mc).subgroupOf Mc).map (rho cx)) (oTwoUpper_le _) hH.simple hH.card_Ks hYH
        hH.card_Hs (by omega)
  have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hY16, hT16])
  intro x hx
  have hxM : x ∈ Mc := hX₀M hx
  have hmem : rho cx ⟨x, hxM⟩ ∈ ((M ⊓ Mc).subgroupOf Mc).map (rho cx) :=
    ⟨⟨x, hxM⟩, hx, rfl⟩
  rw [← heq] at hmem
  obtain ⟨t', ht', hρ⟩ := hmem
  have hker : rho cx (t'⁻¹ * ⟨x, hxM⟩) = 1 := by rw [map_mul, map_inv, hρ, inv_mul_cancel]
  have hq := (rho_eq_one_iff cx _).1 hker
  have ht'T : (t' : G) ∈ T := Subgroup.mem_subgroupOf.1 ht'
  have e : x = (t' : G) * ((t'⁻¹ * ⟨x, hxM⟩ : ↥Mc) : G) := by
    show x = (t' : G) * ((t' : G)⁻¹ * x)
    group
  rw [e]
  exact T.mul_mem ht'T (hQT hq)

include cx in
theorem eq_YT (h113 : StageLemma14113) (c : Chain15358 cx N₁ N₂ g s y t₁) :
    M = Y153 Mc M ⊔ T := by
  refine le_antisymm ?_ (sup_le (Y153_le Mc M) (S153E.T_le_M cx))
  intro m hm
  have hMN := cx.c.hyp.le_normalizer
  have hmN : m ∈ Subgroup.normalizer (VZ T M : Set G) := hMN hm
  have h1 : conjAct (VZ T M) ⟨m, hmN⟩ ∈ autOn M (VZ T M) :=
    mem_autOn_iff.mpr ⟨⟨m, hmN⟩, hm, rfl⟩
  rw [← Hyp153.autOn_Y153_sup_T h113 cx.c.hyp] at h1
  obtain ⟨w, hw, hwe⟩ := Subgroup.mem_map.1 h1
  have hwYT : (w : G) ∈ Y153 Mc M ⊔ T := Subgroup.mem_subgroupOf.1 hw
  have hwM : (w : G) ∈ M := (sup_le (Y153_le Mc M) (S153E.T_le_M cx)) hwYT
  have h2 : conjAct (VZ T M) (w⁻¹ * ⟨m, hmN⟩) = 1 := by
    rw [map_mul, map_inv, hwe, inv_mul_cancel]
  have h3 : ((w⁻¹ * ⟨m, hmN⟩ : ↥(Subgroup.normalizer (VZ T M : Set G))) : G) ∈
      Subgroup.centralizer (VZ T M : Set G) := (conjAct_eq_one_iff _ _).1 h2
  have h4 : (w : G)⁻¹ * m ∈ Subgroup.centralizer (VZ T M : Set G) := h3
  have h5 : (w : G)⁻¹ * m ∈ M := M.mul_mem (M.inv_mem hwM) hm
  have h6 : (w : G)⁻¹ * m ∈ Mc := by
    rw [← centralizer_Z_eq cx]
    exact Subgroup.centralizer_le cx.c.hyp.Z_le_VZ h4
  have h7 : (w : G)⁻¹ * m ∈ T := inf_Mc_le_T cx c ⟨h5, h6⟩
  have e : m = (w : G) * ((w : G)⁻¹ * m) := by group
  rw [e]
  exact (Y153 Mc M ⊔ T).mul_mem hwYT (Subgroup.mem_sup_right h7)

end MInf

end S153E59

end CFSG.Quasithin
