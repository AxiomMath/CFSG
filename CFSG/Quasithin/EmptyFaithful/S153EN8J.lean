module

public import CFSG.Quasithin.EmptyFaithful.S153EN8I
public import CFSG.Quasithin.EmptyFaithful.S14110AuxS4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153EN8

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {cx : Ctx15350 T Mc M V₁ V₂ t} {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} {y t₁ : G}

section S4

variable (h113 : StageLemma14113) (c : Chain15359 cx N₁ N₂ g s y t₁) (B : BarModel cx)
  {d : G} (hdM : d ∈ M) (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) (hbd : barM cx hdM ∈ B.L₂)

include c B hd3 hd1 hbd in
theorem exists_order_three_Jgp (h24 : Nat.card (Jgp M V₂ d) = 24) :
    ∃ (x : G) (hx : x ∈ M), x ∈ Jgp M V₂ d ∧ x ^ 3 = 1 ∧ barM cx hx ≠ 1 := by
  obtain ⟨ℓ, hℓ, hℓ3, hℓ1⟩ := exists_orderThree B.hS.nat₁
  obtain ⟨x, hxM, hxJ, hxℓ⟩ := exists_lift_J c B hdM hd3 hd1 hbd hℓ
  obtain ⟨k, hk⟩ := S153E55.exists_pow_two_pow_odd x
  have hx'M : x ^ 2 ^ k ∈ M := M.pow_mem hxM _
  have hx'J : x ^ 2 ^ k ∈ Jgp M V₂ d := Subgroup.pow_mem _ hxJ _
  have hbar : barM cx hx'M = ℓ ^ 2 ^ k := by
    rw [barM_pow hxM, hxℓ]
  have hℓk : ℓ ^ 2 ^ k ≠ 1 := by
    intro h
    have h2 : ℓ ^ Nat.gcd (2 ^ k) 3 = 1 := pow_gcd_eq_one.2 ⟨h, hℓ3⟩
    have h3 : Nat.gcd (2 ^ k) 3 = 1 := Nat.Coprime.pow_left k (by norm_num)
    rw [h3, pow_one] at h2
    exact hℓ1 h2
  refine ⟨x ^ 2 ^ k, hx'M, hx'J, ?_, by rw [hbar]; exact hℓk⟩
  have hdvd : orderOf (x ^ 2 ^ k) ∣ 24 := by
    have := orderOf_dvd_natCard (⟨x ^ 2 ^ k, hx'J⟩ : ↥(Jgp M V₂ d))
    rw [Subgroup.orderOf_mk, h24] at this
    exact this
  have hcop : Nat.Coprime (orderOf (x ^ 2 ^ k)) 8 := by
    have h2 : Nat.Coprime (orderOf (x ^ 2 ^ k)) 2 := Nat.coprime_two_right.mpr hk
    exact Nat.Coprime.pow_right 3 h2
  have h3 : orderOf (x ^ 2 ^ k) ∣ 3 := hcop.dvd_of_dvd_mul_right (by simpa using hdvd)
  exact orderOf_dvd_iff_pow_eq_one.mp h3

include B in
theorem exists_mem_commV₁ {w : G} (hw : w ∈ V₁) : ∃ u ∈ commV B.L₁, u.val = w := by
  have hw' := hw
  rw [← B.hV₁, mem_map_inclMod_iff] at hw'
  exact hw'

include B in
theorem fpf_V₁ {x : G} (hxM : x ∈ M) (hxJ : x ∈ Jgp M V₂ d) (hx3 : x ^ 3 = 1)
    (hxb : barM cx hxM ≠ 1) {w : G} (hw : w ∈ V₁) (hw1 : w ≠ 1) : x * w * x⁻¹ ≠ w := by
  intro hfix
  obtain ⟨u, hu, rfl⟩ := exists_mem_commV₁ B hw
  have hu1 : u ≠ 1 := fun h => hw1 (by rw [h]; rfl)
  have hL : barM cx hxM ∈ B.L₁ := by
    obtain ⟨_, h1⟩ := (mem_M₁_iff B).1 (show x ∈ M ⊓ Subgroup.centralizer (V₂ : Set G) from
      ⟨(mem_Jgp.1 hxJ).1.1, (mem_Jgp.1 hxJ).1.2⟩)
    exact h1
  have hfixb : barM cx hxM u = u := IntMod.val_injective (by rw [barM_apply_val]; exact hfix)
  exact hxb (S1417.eq_one_of_odd_of_fixed B.hS.nat₁ (fun l hl u hu => commV_stable B.L₁ hl hu) hL
    (odd_orderOf_of_cube (barM_cube hxM hx3)) hu hu1 hfixb)

include h113 c B hdM hd3 hd1 hbd in
theorem mem_V₁_of_centralizes {h : G} (hhM : h ∈ M) (hhJ : h ∈ Jgp M V₂ d)
    (hc : ∀ w ∈ V₁, h * w = w * h) : h ∈ V₁ := by
  have hV := cx.c.hyp.elemAbelian
  have hL : barM cx hhM ∈ B.L₁ := by
    obtain ⟨_, h1⟩ := (mem_M₁_iff B).1 (show h ∈ M ⊓ Subgroup.centralizer (V₂ : Set G) from
      ⟨(mem_Jgp.1 hhJ).1.1, (mem_Jgp.1 hhJ).1.2⟩)
    exact h1
  have h1 : barM cx hhM = 1 := by
    refine S1417.eq_one_of_forall_apply_eq B.hS.nat₁ (fun l hl u hu => commV_stable B.L₁ hl hu) hL
      (fun u hu => ?_)
    have hw : u.val ∈ V₁ := by
      have h2 := (mem_map_inclMod_iff hV (U := commV B.L₁) (v := u.val)).2 ⟨u, hu, rfl⟩
      rwa [B.hV₁] at h2
    refine IntMod.val_injective ?_
    rw [barM_apply_val]
    have := hc u.val hw
    calc h * u.val * h⁻¹ = (u.val * h) * h⁻¹ := by rw [← this]
      _ = u.val := by group
  rw [← inf_centralizer_Jgp h113 c B hdM hd3 hd1 hbd]
  exact Subgroup.mem_inf.2 ⟨hhJ, (barM_eq_one_iff hhM).1 h1⟩

include h113 c B hdM hd3 hd1 hbd in
theorem nonempty_equiv_perm_four_Jgp : Nonempty (↥(Jgp M V₂ d) ≃* Equiv.Perm (Fin 4)) := by
  have hV := cx.c.hyp.elemAbelian
  have h24 := card_Jgp h113 c B hdM hd3 hd1 hbd
  obtain ⟨c₀, hc₀M, hc₀J, hc₀3, hc₀b⟩ := exists_order_three_Jgp c B hdM hd3 hd1 hbd h24
  have hc₀1 : c₀ ≠ 1 := by
    intro h
    apply hc₀b
    exact (barM_eq_one_iff hc₀M).2 (by rw [h]; exact Subgroup.one_mem _)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf c₀ = 3 := orderOf_eq_prime hc₀3 hc₀1
  have hnormc : c₀ ∈ Subgroup.normalizer (V₁ : Set G) :=
    mem_normalizer_V₁ B ⟨hc₀M, (mem_Jgp.1 hc₀J).1.2⟩
  have hnormz : Subgroup.zpowers c₀ ≤ Subgroup.normalizer (V₁ : Set G) :=
    Subgroup.zpowers_le.2 hnormc
  have hV₁le : V₁ ≤ VZ T M := cx.c.decomp.le₁
  have hinf : Subgroup.zpowers c₀ ⊓ V₁ = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx.1
    have h3 : (c₀ ^ k) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc₀3, one_zpow]
    have h2 : (c₀ ^ k) ^ 2 = 1 := hV.2 _ (hV₁le hx.2)
    calc c₀ ^ k = (c₀ ^ k) ^ 3 * ((c₀ ^ k) ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, h2]; simp
  have hcardX : Nat.card ↥(V₁ ⊔ Subgroup.zpowers c₀) = 12 := by
    have h1 := S153E59.card_sup_mul_card_inf_of_normalizes hnormz
    rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, hord, cx.c.decomp.card₁, sup_comm] at h1
    omega
  have hVJ : V₁ ≤ Jgp M V₂ d := V₁_le_Jgp h113 c B hdM hd3 hd1 hbd
  have hXJ : V₁ ⊔ Subgroup.zpowers c₀ ≤ Jgp M V₂ d :=
    sup_le hVJ (Subgroup.zpowers_le.2 hc₀J)
  have hC : ∀ h ∈ Jgp M V₂ d, (∀ x ∈ V₁ ⊔ Subgroup.zpowers c₀, h * x = x * h) → h = 1 := by
    intro h hhJ hcomm
    have hhM := (mem_Jgp.1 hhJ).1.1
    have hhV₁ : h ∈ V₁ := mem_V₁_of_centralizes h113 c B hdM hd3 hd1 hbd hhM hhJ
      (fun w hw => hcomm w (Subgroup.mem_sup_left hw))
    by_contra hne
    refine fpf_V₁ B hc₀M hc₀J hc₀3 hc₀b hhV₁ hne ?_
    have := hcomm c₀ (Subgroup.mem_sup_right (Subgroup.mem_zpowers c₀))
    calc c₀ * h * c₀⁻¹ = (h * c₀) * c₀⁻¹ := by rw [this]
      _ = h := by group
  have hX : S14110.A4Data (V₁ ⊔ Subgroup.zpowers c₀) V₁ c₀ :=
    { le := le_sup_left
      card_W := cx.c.decomp.card₁
      sq_eq_one := fun w hw => hV.2 w (hV₁le hw)
      comm := fun u hu v hv => B2F.isElemAbelian_comm hV (hV₁le hu) (hV₁le hv)
      mem_X := Subgroup.mem_sup_right (Subgroup.mem_zpowers c₀)
      order_c := hord
      mem_normalizer := hnormc
      fpf := fun w hw hw1 => fpf_V₁ B hc₀M hc₀J hc₀3 hc₀b hw hw1
      eq_sup := rfl
      card_X := hcardX
      center := fun g hg hcg => hC g (hXJ hg) (fun x hx => hcg x hx) }
  have hXidx : (V₁ ⊔ Subgroup.zpowers c₀).relIndex (Jgp M V₂ d) = 2 := by
    have h1 := Subgroup.relIndex_mul_card (V₁ ⊔ Subgroup.zpowers c₀) (Jgp M V₂ d)
    rw [inf_eq_left.2 hXJ, hcardX, h24] at h1
    omega
  have hnormal : ((V₁ ⊔ Subgroup.zpowers c₀).subgroupOf (Jgp M V₂ d)).Normal :=
    Subgroup.normal_of_index_eq_two hXidx
  refine S14110.nonempty_mulEquiv_perm_four hX hXJ ?_ hC ?_
  · intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have key : ∀ (h : G) (hh : h ∈ Jgp M V₂ d) (x : G), x ∈ V₁ ⊔ Subgroup.zpowers c₀ →
        h * x * h⁻¹ ∈ V₁ ⊔ Subgroup.zpowers c₀ := by
      intro h hh x hx
      have := hnormal.conj_mem ⟨x, hXJ hx⟩ (Subgroup.mem_subgroupOf.2 hx) ⟨h, hh⟩
      exact Subgroup.mem_subgroupOf.1 this
    refine ⟨key h hh x, fun hx => ?_⟩
    have := key h⁻¹ ((Jgp M V₂ d).inv_mem hh) _ hx
    simpa [mul_assoc] using this
  · obtain ⟨ℓ₁, hℓ₁, hℓ₁2, hℓ₁1⟩ := exists_involution B.hS.nat₁
    obtain ⟨h, hhM, hhJ, hhb⟩ := exists_lift_J c B hdM hd3 hd1 hbd hℓ₁
    refine ⟨h, hhJ, fun hhX => ?_⟩
    obtain ⟨w, hw, k, hk⟩ := hX.mem_decomp hhX
    have hwM : w ∈ M := (cx.c.hyp.VZ_le_T.trans (S153E.T_le_M cx)) (hV₁le hw)
    have hwC : w ∈ Subgroup.centralizer (VZ T M : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact B2F.isElemAbelian_comm hV hv (hV₁le hw)
    have hbw : barM cx hwM = 1 := (barM_eq_one_iff hwM).2 hwC
    have hbh : barM cx hhM = barM cx (M.mul_mem hwM (M.zpow_mem hc₀M k)) := barM_congr _ _ hk
    rw [barM_mul hwM (M.zpow_mem hc₀M k), barM_zpow hc₀M, hbw, one_mul, hhb] at hbh
    have hc3 : (barM cx hc₀M) ^ 3 = 1 := barM_cube hc₀M hc₀3
    have h3 : ℓ₁ ^ 3 = 1 := by
      rw [hbh, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc3, one_zpow]
    apply hℓ₁1
    calc ℓ₁ = ℓ₁ ^ 3 * (ℓ₁ ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, hℓ₁2]; simp

end S4

end S153EN8

end CFSG.Quasithin
