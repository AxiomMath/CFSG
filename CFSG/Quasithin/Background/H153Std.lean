module

public import CFSG.Quasithin.Background.H153Grp
public import CFSG.Quasithin.Background.H153Gen
public import CFSG.Quasithin.Background.H153Chk
public import CFSG.Quasithin.Background.HZCoc24B

public section

open scoped Pointwise

namespace CFSG.Quasithin.H153

open CFSG.ASVolI.ChH CFSG.Open CFSG.Monster.Code CFSG.Quasithin CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.Coc24 CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.FixSyl CFSG.Quasithin.H.ZTrans

theorem z0_mul_self : z0 * z0 = 1 := by
  rw [← toW_xor, Nat.xor_self, toW_zero]

theorem z0_ne_one : z0 ≠ 1 := by
  intro h
  have : (31 : ℕ) = 0 := toW_inj (by norm_num) (by norm_num) (h.trans (toW_zero 11).symm)
  omega

theorem orderOf_z0 : orderOf z0 = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact z0_mul_self) z0_ne_one

theorem card_zpowers_z0 : Nat.card ↥(Subgroup.zpowers z0) = 2 := by
  rw [Nat.card_zpowers, orderOf_z0]

theorem zpowers_z0_lt_W0 : Subgroup.zpowers z0 < W0 := by
  refine lt_of_le_of_ne ((Subgroup.zpowers_le).2 z0_mem_W0) fun h => ?_
  have h1 : Nat.card ↥(Subgroup.zpowers z0) = Nat.card ↥W0 :=
    congrArg (fun K : Subgroup W11 => Nat.card ↥K) h
  rw [card_zpowers_z0, card_W0] at h1
  omega

theorem fixV_KS : fixV (img11 KSp) = Subgroup.zpowers z0 := by
  refine le_antisymm (fun w hw => ?_) ?_
  · rcases fix_ksRho w (fun i => hw _ (ksRho_mem_img11_KSp i)) with rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
  · refine Subgroup.zpowers_le.2 ?_
    intro φ hφ
    obtain ⟨c, rfl⟩ := mem_img11_KSp.1 hφ
    exact (rho11_toW AutPerm le_rfl ⟨ksP c, ksP_mem_autPerm c⟩ (hasArr_ksP c) 31).trans
      (congrArg (toW 11) (ksC_fix c c.2))

theorem KS_comm_mem {k : MulAut W11} (hk : k ∈ img11 KSp) {x : W11} (hx : x ∈ W0) :
    k x * x⁻¹ ∈ Subgroup.zpowers z0 := by
  obtain ⟨c, rfl⟩ := mem_img11_KSp.1 hk
  obtain ⟨m, hm, rfl⟩ := hx
  have e : rho11 AutPerm le_rfl ⟨ksP c, ksP_mem_autPerm c⟩ (toW 11 m) * (toW 11 m)⁻¹ =
      toW 11 (act11 (ksC c) m ^^^ m) := by
    rw [rho11_toW AutPerm le_rfl _ (hasArr_ksP c) m, toW_inv, toW_xor]
  rw [e]
  rcases ks_trans_check c c.2 m hm with h | h
  · rw [h, toW_zero]
    exact Subgroup.one_mem _
  · rw [h]
    exact Subgroup.mem_zpowers _

theorem W0_iff {x : W11} : x ∈ W0 ↔ ∀ k ∈ img11 KSp, k x * x⁻¹ ∈ Subgroup.zpowers z0 := by
  refine ⟨fun hx k hk => KS_comm_mem hk hx, fun h => ?_⟩
  obtain ⟨m, hm, rfl⟩ := toW_surj 11 x
  refine toW_mem_maskSub (w0_of_gens_check m hm fun i hi => ?_)
  have hk := h _ (ksRho_mem_img11_KSp ⟨i, hi⟩)
  have e : rho11 AutPerm le_rfl ⟨ksPerm ⟨i, hi⟩, ksPerm_mem _⟩ (toW 11 m) * (toW 11 m)⁻¹ =
      toW 11 (act11 (ksArr i) m ^^^ m) := by
    rw [rho11_toW AutPerm le_rfl _ (hasArr_permOfArr (ksArr_ok ⟨i, hi⟩).1) m, toW_inv, toW_xor]
  rw [e] at hk
  have hlt : act11 (ksArr i) m ^^^ m < 2 ^ 11 := Nat.xor_lt_two_pow (act11_lt _ _) hm
  rcases eq_one_or_of_mem_zpowers z0_mul_self hk with h1 | h1
  · left
    exact toW_inj hlt (by norm_num) (h1.trans (toW_zero 11).symm)
  · right
    exact toW_inj hlt (by norm_num) h1

theorem KS_faithful {k : MulAut W11} (hk : k ∈ img11 KSp) (h : ∀ x ∈ W0, k x = x) : k = 1 := by
  obtain ⟨c, rfl⟩ := mem_img11_KSp.1 hk
  have hc : c.val = 0 := by
    refine ks_faith_check c.val c.2 fun b hb => ?_
    have hbW : toW 11 b ∈ W0 := toW_mem_maskSub (w0Basis_mem_combos b hb)
    have h1 := h _ hbW
    rw [rho11_toW AutPerm le_rfl _ (hasArr_ksP c) b] at h1
    have hblt : b < 2 ^ 11 := w0_lt b hb
    exact toW_inj (act11_lt _ _) hblt h1
  have hc0 : c = 0 := Fin.ext hc
  have h0 : (⟨ksP c, ksP_mem_autPerm c⟩ : ↥AutPerm) = 1 := by
    apply Subtype.ext
    show ksP c = 1
    rw [hc0]
    exact ksP_zero
  rw [h0, map_one]

theorem toW_xor31 (b : ℕ) : toW 11 (b ^^^ 31) = toW 11 b * z0 := toW_xor 11 b 31

theorem eps_of_mem (m : ℕ) (y : W11) (h : y * (toW 11 m)⁻¹ ∈ Subgroup.zpowers z0) :
    ∃ ε : Bool, y = toW 11 (m ^^^ (if ε then 31 else 0)) := by
  rcases eq_one_or_of_mem_zpowers z0_mul_self h with h1 | h1
  · refine ⟨false, ?_⟩
    rw [if_neg (by decide), Nat.xor_zero]
    exact mul_inv_eq_one.1 h1
  · refine ⟨true, ?_⟩
    rw [if_pos rfl, toW_xor31]
    calc y = (y * (toW 11 m)⁻¹) * toW 11 m := (inv_mul_cancel_right y _).symm
      _ = toW 11 m * z0 := by rw [h1, mul_comm]

theorem transv_std_surj (τ : MulAut ↥W0)
    (hτ : ∀ x : ↥W0, ((τ x : ↥W0) : W11) * ((x : ↥W0) : W11)⁻¹ ∈ Subgroup.zpowers z0) :
    ∃ g ∈ img11 KSp, ∀ x : ↥W0, g (x : W11) = ((τ x : ↥W0) : W11) := by
  have hb : ∀ i : Fin 7, toW 11 (w0Basis.getD i 0) ∈ W0 := fun i =>
    toW_mem_maskSub (w0Basis_getD_mem i)
  have h1 : ∀ i : Fin 7, ∃ ε : Bool, ((τ ⟨toW 11 (w0Basis.getD i 0), hb i⟩ : ↥W0) : W11) =
      toW 11 (w0Basis.getD i 0 ^^^ (if ε then 31 else 0)) := fun i =>
    eps_of_mem _ _ (hτ ⟨toW 11 (w0Basis.getD i 0), hb i⟩)
  choose ε hε using h1
  have hε3 : ε 3 = false := by
    by_contra hne
    have hε3' : ε 3 = true := by simpa using hne
    have h3 := hε 3
    have h31 : toW 11 (w0Basis.getD ((3 : Fin 7) : ℕ) 0) = z0 := by rw [w0Basis_three]
    have hx : w0Basis.getD ((3 : Fin 7) : ℕ) 0 ^^^ (if ε 3 then 31 else 0) = 0 := by
      rw [hε3', if_pos rfl, w0Basis_three, Nat.xor_self]
    rw [hx, toW_zero] at h3
    have h4 : (τ ⟨toW 11 (w0Basis.getD ((3 : Fin 7) : ℕ) 0), hb 3⟩ : ↥W0) = 1 :=
      Subtype.ext h3
    have h5 : (⟨toW 11 (w0Basis.getD ((3 : Fin 7) : ℕ) 0), hb 3⟩ : ↥W0) = 1 :=
      τ.injective (h4.trans (map_one τ).symm)
    have h6 : toW 11 (w0Basis.getD ((3 : Fin 7) : ℕ) 0) = 1 := congrArg Subtype.val h5
    exact z0_ne_one (h31 ▸ h6)
  obtain ⟨c, hc⟩ := pat_check ε hε3
  set g := rho11 AutPerm le_rfl ⟨ksP c, ksP_mem_autPerm c⟩ with hg
  refine ⟨g, mem_img11_KSp.2 ⟨c, rfl⟩, ?_⟩
  have key : ∀ m ∈ combos w0Basis, ∃ h : toW 11 m ∈ W0,
      g (toW 11 m) = ((τ ⟨toW 11 m, h⟩ : ↥W0) : W11) := by
    refine mem_of_combos (fun m => ∃ h : toW 11 m ∈ W0,
      g (toW 11 m) = ((τ ⟨toW 11 m, h⟩ : ↥W0) : W11)) ?_ ?_ w0Basis ?_
    · have h0 : toW 11 0 ∈ W0 := by
        rw [toW_zero]
        exact W0.one_mem
      refine ⟨h0, ?_⟩
      have : (⟨toW 11 0, h0⟩ : ↥W0) = 1 := Subtype.ext (toW_zero 11)
      rw [this, map_one, toW_zero, map_one]
      rfl
    · rintro a b ⟨ha, hga⟩ ⟨hb', hgb⟩
      have hab : toW 11 (a ^^^ b) ∈ W0 := by
        rw [toW_xor]
        exact W0.mul_mem ha hb'
      refine ⟨hab, ?_⟩
      have : (⟨toW 11 (a ^^^ b), hab⟩ : ↥W0) = ⟨toW 11 a, ha⟩ * ⟨toW 11 b, hb'⟩ :=
        Subtype.ext (toW_xor 11 a b)
      rw [this, map_mul, toW_xor, map_mul, hga, hgb]
      rfl
    · intro a ha
      obtain ⟨i, rfl⟩ := w0Basis_getD a ha
      refine ⟨hb i, ?_⟩
      rw [hg, rho11_toW AutPerm le_rfl _ (hasArr_ksP c) _, hc i, hε i]
  intro x
  obtain ⟨x', hx'⟩ := x
  obtain ⟨m, hm, rfl⟩ := hx'
  obtain ⟨h, hgm⟩ := key m hm
  exact hgm

theorem fullTransp_std :
    FullTranspCenter' (img11 (MY M24g S0)) (img11 KSp) W0 (Subgroup.zpowers z0) := by
  refine ⟨fun g hg x hx => KS_comm_mem hg hx, fun τ hτ => transv_std_surj τ hτ,
    fun g hg h => KS_faithful hg h, ?_⟩
  rintro h ⟨σ, hσ, rfl⟩ g ⟨k, hk, rfl⟩
  have hσ' : (σ : S24) ∈ MY M24g S0 := Subgroup.mem_subgroupOf.1 hσ
  have hk' : (k : S24) ∈ KSp := Subgroup.mem_subgroupOf.1 hk
  refine ⟨σ * k * σ⁻¹, Subgroup.mem_subgroupOf.2 ?_, by rw [map_mul, map_mul, map_inv]; rfl⟩
  exact MY0_conj_KSp hσ' hk'

theorem ksP_ne_one (c : Fin 64) (hc : c ≠ 0) : ksP c ≠ 1 := by
  intro h
  apply hc
  apply ksP_injective
  rw [h, ksP_zero]

theorem xi_std : xiSub (img11 KSp) = ⊤ := by
  have hl : ∀ a ∈ xiData.map Prod.snd, (MaskCoords.std 11).vm a ∈ xiSub (img11 KSp) := by
    intro a ha
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 ha
    obtain ⟨he0, he64, hfix⟩ := xi_fix e he
    set c : Fin 64 := ⟨e.1, he64⟩ with hc
    have hc0 : c ≠ 0 := fun h => by
      have := congrArg Fin.val h
      simp [hc] at this
      omega
    set φ : MulAut W11 := rho11 AutPerm le_rfl ⟨ksP c, ksP_mem_autPerm c⟩ with hφ
    have hφK : φ ∈ img11 KSp := mem_img11_KSp.2 ⟨c, rfl⟩
    have hφ1 : φ ≠ 1 := by
      intro h
      have := rho11_injective AutPerm le_rfl (h.trans (map_one _).symm)
      exact ksP_ne_one c hc0 (congrArg Subtype.val this)
    have hv : toW 11 e.2 ∈ fixV (Subgroup.zpowers φ) := by
      refine CFSG.Quasithin.mem_fixV_zpowers_iff_apply.2 ?_
      exact (rho11_toW AutPerm le_rfl ⟨ksP c, ksP_mem_autPerm c⟩ (hasArr_ksP c) e.2).trans
        (congrArg (toW 11) hfix)
    exact (le_iSup₂_of_le φ hφK (le_iSup_of_le hφ1 le_rfl) :
      fixV (Subgroup.zpowers φ) ≤ xiSub (img11 KSp)) hv
  refine eq_top_iff.2 fun v _ => ?_
  obtain ⟨m, hm, rfl⟩ := toW_surj 11 v
  exact (MaskCoords.std 11).vm_mem_of_combos (xiSub (img11 KSp)) hl m (xi_span m hm)

theorem img11_mono' {A B : Subgroup S24} (h : A ≤ B) : img11 A ≤ img11 B :=
  Subgroup.map_mono fun _ hx => h hx

theorem map_mem_zpowers_z0 {h : MulAut W11} (hz : h z0 = z0) {c : W11}
    (hc : c ∈ Subgroup.zpowers z0) : h c ∈ Subgroup.zpowers z0 := by
  rcases eq_one_or_of_mem_zpowers z0_mul_self hc with rfl | rfl
  · rw [map_one]
    exact Subgroup.one_mem _
  · rw [hz]
    exact hc

theorem HS_fix_z0
    {h : MulAut W11} (hh : h ∈ img11 (MY M24g S0)) : h z0 = z0 := by
  obtain ⟨σ, hσ, rfl⟩ := hh
  exact rho11_z0_of_mem (Subgroup.mem_subgroupOf.1 hσ).2

theorem HS_stab_W0
    {h : MulAut W11} (hh : h ∈ img11 (MY M24g S0)) {w : W11}
    (hw : w ∈ W0) : h w ∈ W0 := by
  rw [W0_iff]
  intro k hk
  have hk' : h⁻¹ * k * h⁻¹⁻¹ ∈ img11 KSp :=
    fullTransp_std.2.2.2 h⁻¹ ((img11 (MY M24g S0)).inv_mem hh) k hk
  have hc := (W0_iff.1 hw) _ hk'
  have e1 : h ((h⁻¹ * k * h⁻¹⁻¹) w) = k (h w) := by
    show h (h⁻¹ (k (h⁻¹⁻¹ w))) = k (h w)
    rw [MulAut.apply_inv_self, inv_inv]
  have e2 : h w⁻¹ = (h w)⁻¹ := map_inv h w
  have e : k (h w) * (h w)⁻¹ = h ((h⁻¹ * k * h⁻¹⁻¹) w * w⁻¹) := by
    rw [MulEquiv.map_mul, e2, e1]
  rw [e]
  exact map_mem_zpowers_z0 (HS_fix_z0 hh) hc

theorem chief_V1_V7 :
    IsChiefFactorUnder (actsOnModule (img11 (MY M24g S0))) (Subgroup.zpowers z0) W0 := by
  refine ⟨zpowers_z0_lt_W0, ?_, ?_, ?_⟩
  · rintro f ⟨g, hg, rfl⟩ u hu
    exact map_mem_zpowers_z0 (HS_fix_z0 hg) hu
  · rintro f ⟨g, hg, rfl⟩ u hu
    exact HS_stab_W0 hg hu
  · intro Y h1 h2 hY
    by_cases hYe : Y = Subgroup.zpowers z0
    · exact Or.inl hYe
    · right
      refine eq_W0_of_lt (lt_of_le_of_ne h1 (Ne.symm hYe)) h2 ?_
      intro g hg u
      have hLM : img11 Lz ≤ img11 (MY M24g S0) := img11_mono' Lz_le_MY0
      constructor
      · intro hgu
        have h3 : g⁻¹ (g u) ∈ Y :=
          hY (fun v => g⁻¹ v) ⟨g⁻¹, hLM ((img11 Lz).inv_mem hg), rfl⟩ _ hgu
        rwa [MulAut.inv_apply_self] at h3
      · intro hu
        exact hY (fun v => g v) ⟨g, hLM hg, rfl⟩ u hu

end CFSG.Quasithin.H153
