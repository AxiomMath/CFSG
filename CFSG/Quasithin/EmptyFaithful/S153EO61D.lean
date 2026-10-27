module

public import CFSG.Quasithin.EmptyFaithful.S153EO61B
public import CFSG.Quasithin.EmptyFaithful.S153EO61C
public import CFSG.Quasithin.EmptyFaithful.S153E58P
public import CFSG.Quasithin.EmptyFaithful.S153E58S
public import CFSG.Quasithin.EmptyFaithful.S153EGen

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise

namespace S153EO61

open S153E57

section Order

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem exists_order_three_commuting (cx : Ctx15350 T Mc M V₁ V₂ t) {t₂ : G} {y : NZ T}
    (hyMc : (y : G) ∈ Mc)
    (hyz : (y : G) * t₂ * (y : G)⁻¹ * t₂⁻¹ ∈ quasithinOmegaOneCenter T)
    {d : MulAut (UTil T M V₁ Mc)} (hyd : rho cx y = d) (hd3 : orderOf d = 3) :
    ∃ e : G, e ∈ Mc ∧ orderOf e = 3 ∧ t₂ * e = e * t₂ := by
  set z : G := (y : G) * t₂ * (y : G)⁻¹ * t₂⁻¹ with hz
  have hzsq : z * z = 1 := by
    have h := pow_card_eq_one' (G := ↥(quasithinOmegaOneCenter T)) (x := ⟨z, hyz⟩)
    rw [Z_card cx, pow_two] at h
    exact congrArg Subtype.val h
  have hyc : (y : G) * z = z * (y : G) :=
    ((Subgroup.mem_centralizer_iff.1 (Mc_le_centralizer_Z cx hyMc)) z hyz).symm
  have hyt : (y : G) * t₂ = z * t₂ * (y : G) := by
    rw [hz]
    group
  have hy2 : (y : G) * y * t₂ = t₂ * ((y : G) * y) :=
    calc (y : G) * y * t₂ = y * (y * t₂) := by group
      _ = y * (z * t₂ * y) := by rw [hyt]
      _ = (y * z) * t₂ * y := by group
      _ = (z * y) * t₂ * y := by rw [hyc]
      _ = z * (y * t₂) * y := by group
      _ = z * (z * t₂ * y) * y := by rw [hyt]
      _ = (z * z) * t₂ * (y * y) := by group
      _ = t₂ * (y * y) := by rw [hzsq, one_mul]
  let y2 : NZ T := y * y
  have hy2G : (y2 : G) = (y : G) * y := rfl
  have hcomm2 : Commute t₂ (y2 : G) := by
    show t₂ * (y2 : G) = (y2 : G) * t₂
    rw [hy2G]
    exact hy2.symm
  have hρ : rho cx y2 = d * d := by rw [map_mul, hyd]
  have hd2 : orderOf (rho cx y2) = 3 := by
    rw [hρ, ← pow_two, Nat.Coprime.orderOf_pow (by rw [hd3]; norm_num), hd3]
  have h3dvd : 3 ∣ orderOf y2 := by
    have := orderOf_map_dvd (rho cx) y2
    rwa [hd2] at this
  have hpos : orderOf y2 ≠ 0 := (orderOf_pos y2).ne'
  refine ⟨((y2 ^ (orderOf y2 / 3) : NZ T) : G), ?_, ?_, ?_⟩
  · rw [Subgroup.coe_pow]
    exact Mc.pow_mem (Mc.mul_mem hyMc hyMc) _
  · rw [Subgroup.orderOf_coe]
    exact orderOf_pow_orderOf_div hpos h3dvd
  · rw [Subgroup.coe_pow]
    exact (hcomm2.pow_right _).eq

theorem card_three_group_le (cx : Ctx15350 T Mc M V₁ V₂ t) (hUQ : UH153 T M V₁ Mc = pCoreOf 2 Mc)
    (hH : Nat.card ↥(HStar153 T M V₁ Mc) = 336) {D : Subgroup G} (hDMc : D ≤ Mc) (hD : IsPGroup 3 D) :
    Nat.card D ≤ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f : ↥D →* MulAut (UTil T M V₁ Mc) :=
    (rho cx).comp (Subgroup.inclusion (hDMc.trans (Mc_le_NZ cx)))
  have hf : ∀ x : ↥D, f x = rho cx ⟨(x : G), Mc_le_NZ cx (hDMc x.2)⟩ := fun x => rfl
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    rw [hf] at hx
    have hxU := mem_U_of_rho_eq_one cx hUQ _ hx
    obtain ⟨n, hn⟩ := hD x
    have h3 : orderOf (x : G) ∣ 3 ^ n := by
      apply orderOf_dvd_of_pow_eq_one
      have := congrArg Subtype.val hn
      simpa using this
    have hU2 : IsPGroup 2 (UH153 T M V₁ Mc) := hUQ ▸ pCoreOf_isPGroup (r := 2) Mc
    obtain ⟨m, hm⟩ := hU2 ⟨(x : G), hxU⟩
    have h2 : orderOf (x : G) ∣ 2 ^ m := by
      apply orderOf_dvd_of_pow_eq_one
      have := congrArg Subtype.val hm
      simpa using this
    have hcop : Nat.Coprime (3 ^ n) (2 ^ m) := Nat.Coprime.pow n m (by norm_num)
    have h1 : orderOf (x : G) ∣ Nat.gcd (3 ^ n) (2 ^ m) := Nat.dvd_gcd h3 h2
    rw [hcop] at h1
    exact Subtype.ext (orderOf_eq_one_iff.1 (Nat.dvd_one.1 h1))
  have hrange : f.range ≤ HStar153 T M V₁ Mc := by
    rintro _ ⟨x, rfl⟩
    rw [hf]
    exact rho_mem_XStar (B := Mc) cx _ (hDMc x.2)
  have hcard : Nat.card D = Nat.card f.range := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  have hdvd : Nat.card D ∣ 336 := by
    rw [hcard, ← hH]
    exact Subgroup.card_dvd_of_le hrange
  obtain ⟨k, hk⟩ := hD.exists_card_eq
  rw [hk] at hdvd ⊢
  by_contra hlt
  push Not at hlt
  have hk2 : 2 ≤ k := by
    by_contra h
    push Not at h
    interval_cases k <;> simp at hlt
  have h9 : 3 ^ 2 ∣ 3 ^ k := pow_dvd_pow 3 hk2
  have := h9.trans hdvd
  norm_num at this

end Order

end S153EO61

namespace S153E

open S153EO61 S153E57

section Lemma61One

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem lemma_61one (cx : Ctx15350 T Mc M V₁ V₂ t) {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G}
    {s : ℕ} {y t₁ : G} (c : Chain15359 cx N₁ N₂ g s y t₁) {DH : Subgroup G}
    (hDH : IsSylowThreeOf153 DH Mc) {t₂ : G} (ht₂ : t₂ ∈ T) (hord : orderOf t₂ = 2)
    (hUCT : t₂ ∉ UCT153 T M V₁ Mc) :
    ∃ h ∈ Mc, ∀ d ∈ DH, t₂ * (h * d * h⁻¹) = (h * d * h⁻¹) * t₂ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let _ : CommGroup (UTil T M V₁ Mc) := commGroupOfElemAbelian cx.hF.isElemAbelian_tilde
  have hUQ : UH153 T M V₁ Mc = pCoreOf 2 Mc := c.h59.one
  have ht₂sq : t₂ * t₂ = 1 := by
    rw [← pow_two]
    have := pow_orderOf_eq_one t₂
    rwa [hord] at this
  have hinv : t₂⁻¹ = t₂ := inv_eq_of_mul_eq_one_right ht₂sq
  have ht₂N : t₂ ∈ NZ T := t₁_mem_NZ cx ht₂
  have ht₂Mc : t₂ ∈ Mc := T_le_Mc cx ht₂
  have hH336 : Nat.card ↥(HStar153 T M V₁ Mc) = 336 := by
    obtain ⟨eH⟩ := c.h58.one
    rw [Nat.card_congr eH.toEquiv]
    exact S153E58.card_mulAut_statedSL_three_two
  obtain ⟨π, U₁, hZU₁, hU₁U, hdir, hnat, hdual⟩ := c.h58.three t₂ ht₂ hUCT
  set W₁ : Subgroup (UTil T M V₁ Mc) :=
    (tildeOf (quasithinOmegaOneCenter T) U₁).subgroupOf
      (tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)) with hW₁
  set W₂ : Subgroup (UTil T M V₁ Mc) :=
    (tildeOf (quasithinOmegaOneCenter T) (conjSubgroup U₁ t₂)).subgroupOf
      (tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)) with hW₂
  let t₂N : NZ T := ⟨t₂, ht₂N⟩
  set τ := rho cx t₂N with hτdef
  have hτ2 : τ * τ = 1 := by
    rw [hτdef, ← map_mul]
    have : (t₂N * t₂N : NZ T) = 1 := Subtype.ext ht₂sq
    rw [this, map_one]
  have hττ : ∀ w, τ (τ w) = w := fun w => by
    have := congrArg (fun f : MulAut (UTil T M V₁ Mc) => f w) hτ2
    simpa using this
  have hτH : τ ∈ HStar153 T M V₁ Mc := rho_mem_XStar (B := Mc) cx t₂N ht₂Mc
  have hswap : ∀ w, w ∈ W₂ ↔ ∃ v ∈ W₁, τ v = w := by
    intro w
    have h := S153E58.mem_tilde_conj_iff cx (U₁ := U₁) ht₂Mc w
    have hinvN : (⟨t₂⁻¹, Mc_le_NZ cx (Mc.inv_mem ht₂Mc)⟩ : NZ T) = t₂N := Subtype.ext hinv
    rw [hinvN] at h
    exact h
  have hτ₁ : ∀ x ∈ W₁, τ x ∈ W₂ := fun x hx => (hswap _).2 ⟨x, hx, rfl⟩
  have hτ₂ : ∀ x ∈ W₂, τ x ∈ W₁ := fun x hx => by
    obtain ⟨v, hv, rfl⟩ := (hswap x).1 hx
    rwa [hττ]
  have hsq : ∀ a : UTil T M V₁ Mc, a * a = 1 := by
    intro a
    have := cx.hF.isElemAbelian_tilde.2 a a.2
    rw [← pow_two]
    exact Subtype.ext (by simpa using this)
  have hdec : ∀ w : UTil T M V₁ Mc, ∃ a ∈ W₁, ∃ b ∈ W₂, a * b = w := fun w =>
    Subgroup.mem_sup.1 (hdir.1 ▸ Subgroup.mem_top w)
  have hint : ∀ w : UTil T M V₁ Mc, w ∈ W₁ → w ∈ W₂ → w = 1 := fun w h1 h2 => by
    have : w ∈ W₁ ⊓ W₂ := ⟨h1, h2⟩
    rw [hdir.2, Subgroup.mem_bot] at this
    exact this
  obtain ⟨d, hdK, hd3, hdτ⟩ := exists_commuting_order_three (K := oTwoUpper (HStar153 T M V₁ Mc))
    (W₁ := W₁) (W₂ := W₂) (S153E58.bilU cx) (S153E58.bilU_right cx) (S153E58.bilU_symm cx)
    (fun a ha => S153E58.bilU_nondeg cx c.h56.orth_nondeg a ha)
    (fun k hk a b => S153E58.bilU_inv cx (oTwoUpper_le _ hk) a b) hdir hnat
    (fun k hk u hu => hdual.2.2.2.1 ⟨k, hk⟩ u hu) hτ2 (fun a b => S153E58.bilU_inv cx hτH a b) hτ₁ hτ₂
  have hdH : d ∈ HStar153 T M V₁ Mc := oTwoUpper_le _ hdK
  obtain ⟨y', hyMc, hyd, hyz⟩ := exists_lift cx hUQ ht₂ ht₂sq (fun a b => mul_comm a b) hsq hdec hint
    hτ₁ hτ₂ hdH hdτ
  obtain ⟨e, heMc, he3, hcomme⟩ := exists_order_three_commuting cx hyMc hyz hyd hd3
  have hQp : IsPGroup 3 (Subgroup.zpowers e) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, he3]; norm_num)
  have hQMc : Subgroup.zpowers e ≤ Mc := Subgroup.zpowers_le.2 heMc
  obtain ⟨k, hk, hkle⟩ := exists_conj_of_isSylow (p := 3) hDH hQp hQMc
  have hcardDH : Nat.card DH ≤ 3 := card_three_group_le cx hUQ hH336 hDH.1 hDH.2.1
  have hc1 : Nat.card (conjSubgroup DH k) ≤ Nat.card (Subgroup.zpowers e) := by
    rw [card_conjSubgroup153, Nat.card_zpowers, he3]
    exact hcardDH
  have hQeq : Subgroup.zpowers e = conjSubgroup DH k := Subgroup.eq_of_le_of_card_ge hkle hc1
  refine ⟨k⁻¹, Mc.inv_mem hk, fun d' hd' => ?_⟩
  have hx : k⁻¹ * d' * k⁻¹⁻¹ ∈ conjSubgroup DH k := by
    rw [mem_conjSubgroup_iff]
    have : k * (k⁻¹ * d' * k⁻¹⁻¹) * k⁻¹ = d' := by group
    rw [this]
    exact hd'
  rw [← hQeq] at hx
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hx
  rw [← hn]
  exact ((Commute.zpow_right (show Commute t₂ e from hcomme) n).eq)

end Lemma61One

end S153E

end CFSG.Quasithin
