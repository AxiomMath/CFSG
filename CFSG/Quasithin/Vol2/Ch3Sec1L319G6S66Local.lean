module

public import CFSG.Quasithin.Vol2.Ch3Sec1L319G6S66Nat
public import CFSG.Quasithin.Vol2.Ch3Sec1L319G6S66Block
public import CFSG.Quasithin.Vol2.Ch3Sec1L319G6S66Act
public import CFSG.Quasithin.Vol2.Ch3zStep

public section

namespace CFSG.Quasithin.H13.L319.S66

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.Ch3z

theorem coboundary_le_four_of_natBlock {G : Type} [Group G] [Finite G] {H T M₂ U A L N : Subgroup G}
    {V : Subgroup G} (h : Ch3z.Setting H T M₂ U A) (hstep : IsChiefStep H U L N)
    {𝓗 : Finset (Subgroup (MulAut ↥(chiefMod L N)))}
    (hctx : @Ch3z.BlkCtx ↥(chiefMod L N) (chiefCG (h.hE hstep)) (chiefAut H L N)
        (chiefImg (Setting.hHL hstep) (Setting.hHN hstep) T)
        (chiefImg (Setting.hHL hstep) (Setting.hHN hstep) M₂) 𝓗)
    {K₀ : Subgroup (MulAut ↥(chiefMod L N))} (hK₀ : K₀ ∈ 𝓗)
    (hK₀nat : @Ch3z.NatBlockData ↥(chiefMod L N) (chiefCG (h.hE hstep)) K₀
        (@CFSG.Quasithin.commV ↥(chiefMod L N) (chiefCG (h.hE hstep)) K₀) 2)
    {y : G} (hy : y ∈ H) (hyK : chiefPsi (Setting.hHL hstep) (Setting.hHN hstep) ⟨y, hy⟩ ∈ K₀)
    {c : G} (hc : c ∈ H) (hcV : ∀ v ∈ V, c * v = v * c) (hc2 : c ^ 2 = 1)
    (hcY : chiefPsi (Setting.hHL hstep) (Setting.hHN hstep) ⟨c, hc⟩ ∈ ⨆ K ∈ 𝓗, K)
    (hcW : ∃ w ∈ (@CFSG.Quasithin.commV ↥(chiefMod L N) (chiefCG (h.hE hstep)) K₀),
      chiefPsi (Setting.hHL hstep) (Setting.hHN hstep) ⟨c, hc⟩ w ≠ w) :
    Set.ncard ((fun v => chiefPsi (Setting.hHL hstep) (Setting.hHN hstep) ⟨y, hy⟩ v * v⁻¹) ''
      (↑(Subgroup.map (chiefIota (h.hNL hstep)) ((V ⊓ N).subgroupOf N)) : Set ↥(chiefMod L N))) ≤ 4 := by
  classical
  letI : CommGroup ↥(chiefMod L N) := chiefCG (h.hE hstep)
  haveI : Finite ↥(chiefMod L N) := inferInstance
  have hsum : (⨆ K ∈ 𝓗, CFSG.Quasithin.commV K) = ⊤ := hctx.iSup_comm
  have hdir : CFSG.Quasithin.commV K₀ ⊓ (⨆ K ∈ 𝓗, ⨆ (_ : K ≠ K₀), CFSG.Quasithin.commV K) = ⊥ :=
    hctx.inf_iSup_comm hK₀
  have hσ : ∀ K ∈ 𝓗, K ≠ K₀ → ∀ w ∈ CFSG.Quasithin.commV K,
      chiefPsi (Setting.hHL hstep) (Setting.hHN hstep) ⟨y, hy⟩ w = w :=
    fun K hK hne w hw => hctx.act_commV_of_ne hK hK₀ hne hyK hw
  have hstab : ∀ K ∈ 𝓗, ∀ k ∈ K, ∀ K' ∈ 𝓗, ∀ w : ↥(chiefMod L N),
      k • w ∈ CFSG.Quasithin.commV K' ↔ w ∈ CFSG.Quasithin.commV K' := by
    intro K hK k hk K' hK' w
    by_cases hKK : K' = K
    · rw [hKK]
      constructor
      · intro hkw
        have h3 : k⁻¹ • (k • w) ∈ CFSG.Quasithin.commV K :=
          apply_mem_commV_of_mem (inv_mem hk) hkw
        rwa [inv_smul_smul] at h3
      · intro hw
        exact apply_mem_commV_of_mem hk hw
    · constructor
      · intro hkw
        have h3 : k⁻¹ • (k • w) = k • w :=
          hctx.act_commV_of_ne hK' hK hKK (inv_mem hk) hkw
        rw [inv_smul_smul] at h3
        rw [h3]
        exact hkw
      · intro hw
        have e1 : k • w = w := hctx.act_commV_of_ne hK' hK hKK hk hw
        rw [e1]
        exact hw
  have he : ∀ K ∈ 𝓗, ∀ w ∈ CFSG.Quasithin.commV K,
      chiefPsi (Setting.hHL hstep) (Setting.hHN hstep) ⟨c, hc⟩ w ∈ CFSG.Quasithin.commV K := by
    intro K hK w hw
    exact (stable_of_mem_iSup 𝓗 (fun K => CFSG.Quasithin.commV K) hstab _ hcY K hK w).mpr hw
  have hmul1 : (⟨c, hc⟩ : ↥H) * ⟨c, hc⟩ = 1 :=
    Subtype.ext (by show c * c = 1; rw [← pow_two]; exact hc2)
  have hpow : chiefPsi (Setting.hHL hstep) (Setting.hHN hstep) ⟨c, hc⟩ *
      chiefPsi (Setting.hHL hstep) (Setting.hHN hstep) ⟨c, hc⟩ = 1 := by
    rw [← map_mul, hmul1, map_one]
  have hsq0 : ∀ u : ↥(chiefMod L N),
      chiefPsi (Setting.hHL hstep) (Setting.hHN hstep) ⟨c, hc⟩
        (chiefPsi (Setting.hHL hstep) (Setting.hHN hstep) ⟨c, hc⟩ u) = u := by
    intro u
    have h0 := DFunLike.congr_fun hpow u
    first
    | exact h0
    | simpa [MulAut.mul_apply, MulAut.one_apply] using h0
  have h1 : ∀ K ∈ 𝓗, K ≠ K₀ → ∀ k ∈ K, ∀ w ∈ CFSG.Quasithin.commV K₀, k • w = w :=
    fun K hK hne k hk w hw => hctx.act_commV_of_ne hK₀ hK (Ne.symm hne) hk hw
  have h2 : ∀ k ∈ K₀, ∀ w ∈ CFSG.Quasithin.commV K₀, k • w ∈ CFSG.Quasithin.commV K₀ :=
    fun k hk w hw => apply_mem_commV_of_mem hk hw
  obtain ⟨k, hkK₀, hkagree⟩ :=
    exists_agree_of_mem_iSup 𝓗 K₀ (CFSG.Quasithin.commV K₀) h1 h2 _ hcY
  have hagree : ∀ w ∈ CFSG.Quasithin.commV K₀,
      chiefPsi (Setting.hHL hstep) (Setting.hHN hstep) ⟨c, hc⟩ w = k w :=
    fun w hw => hkagree w hw
  have hkU : ∀ u ∈ CFSG.Quasithin.commV K₀, k u ∈ CFSG.Quasithin.commV K₀ :=
    fun u hu => apply_mem_commV_of_mem hkK₀ hu
  have hsq : ∀ u ∈ CFSG.Quasithin.commV K₀, k (k u) = u := by
    intro u hu
    have e1 : k u = chiefPsi (Setting.hHL hstep) (Setting.hHN hstep) ⟨c, hc⟩ u :=
      (hagree u hu).symm
    have e2 : k (k u) = chiefPsi (Setting.hHL hstep) (Setting.hHN hstep) ⟨c, hc⟩ (k u) :=
      (hagree (k u) (hkU u hu)).symm
    rw [e2, e1, hsq0]
  obtain ⟨w₀, hw₀, hw₀ne⟩ := hcW
  have hkne : ∃ u ∈ CFSG.Quasithin.commV K₀, k u ≠ u :=
    ⟨w₀, hw₀, fun hkw => hw₀ne ((hagree w₀ hw₀).trans hkw)⟩
  have hnat := natBlock_fix_ncard_le_four hK₀nat hkK₀ hkU hsq hkne
  have hset : {w : ↥(chiefMod L N) | w ∈ CFSG.Quasithin.commV K₀ ∧
      chiefPsi (Setting.hHL hstep) (Setting.hHN hstep) ⟨c, hc⟩ w = w} =
      {u : ↥(chiefMod L N) | u ∈ CFSG.Quasithin.commV K₀ ∧ k u = u} := by
    ext w
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨hw, hw'⟩
      exact ⟨hw, (hagree w hw).symm.trans hw'⟩
    · rintro ⟨hw, hw'⟩
      exact ⟨hw, (hagree w hw).trans hw'⟩
  have hfix : Set.ncard {w : ↥(chiefMod L N) | w ∈ CFSG.Quasithin.commV K₀ ∧
      chiefPsi (Setting.hHL hstep) (Setting.hHN hstep) ⟨c, hc⟩ w = w} ≤ 4 := by
    rw [hset]
    exact hnat
  have hVs : ∀ v ∈ Subgroup.map (chiefIota (h.hNL hstep)) ((V ⊓ N).subgroupOf N),
      chiefPsi (Setting.hHL hstep) (Setting.hHN hstep) ⟨c, hc⟩ v = v := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hv
    have hxV : (x : G) ∈ V := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)).1
    have hgn : c * (x : G) * c⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp (Setting.hHN hstep hc) (x : G)).mp x.2
    rw [chiefPsi_iota (Setting.hHL hstep) (Setting.hHN hstep) (h.hNL hstep) ⟨c, hc⟩ x hgn]
    congr 1
    apply Subtype.ext
    show c * (x : G) * c⁻¹ = (x : G)
    rw [hcV _ hxV, mul_inv_cancel_right]
  exact ncard_coboundary_le_four_of_blocks 𝓗 (fun K => CFSG.Quasithin.commV K) K₀ hK₀ hsum hdir
    (MulEquiv.toMonoidHom (chiefPsi (Setting.hHL hstep) (Setting.hHN hstep) ⟨y, hy⟩)) hσ
    (MulEquiv.toMonoidHom (chiefPsi (Setting.hHL hstep) (Setting.hHN hstep) ⟨c, hc⟩)) he
    (Subgroup.map (chiefIota (h.hNL hstep)) ((V ⊓ N).subgroupOf N)) hVs hfix

end CFSG.Quasithin.H13.L319.S66

end
