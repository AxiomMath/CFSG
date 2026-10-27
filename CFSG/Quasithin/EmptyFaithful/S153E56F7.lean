module

public import CFSG.Quasithin.EmptyFaithful.S153E56F6
public import CFSG.Quasithin.EmptyFaithful.S153E55F

public section

namespace CFSG.Quasithin

namespace S153E56f

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits CFSG.Quasithin.S153E
open scoped commutatorElement Pointwise

section Abstract

variable {W : Type} [CommGroup W]

theorem fix_all {Ub : Subgroup (MulAut W)} {a b : MulAut W}
    (hUb : ∀ x ∈ Ub, x = 1 ∨ x = a ∨ x = b ∨ x = a * b) {w : W} (ha : a w = w) (hb : b w = w) :
    ∀ x ∈ Ub, x w = w := by
  intro x hx
  rcases hUb x hx with h | h | h | h
  · rw [h, MulAut.one_apply]
  · rw [h]
    exact ha
  · rw [h]
    exact hb
  · rw [h, MulAut.mul_apply, hb, ha]

theorem stab_aux {Ub : Subgroup (MulAut W)} {a b : MulAut W}
    (hUb : ∀ x ∈ Ub, x = 1 ∨ x = a ∨ x = b ∨ x = a * b) {w : W} (hb : b w = w)
    (hall : (∀ x ∈ Ub, x w = w) → False) : ∀ x ∈ Ub, x w = w → x = 1 ∨ x = b := by
  intro x hx hxw
  rcases hUb x hx with h | h | h | h
  · exact Or.inl h
  · exfalso
    apply hall
    apply fix_all hUb _ hb
    rw [← h]
    exact hxw
  · exact Or.inr h
  · exfalso
    apply hall
    apply fix_all hUb _ hb
    rw [h, MulAut.mul_apply, hb] at hxw
    exact hxw

end Abstract

section Context

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} {y t₁ : G}

theorem F_comm_z' (cx : Ctx15350 T Mc M V₁ V₂ t) {z e : G} (hz : z ∈ quasithinOmegaOneCenter T)
    (he : e ∈ Fgp153 T M V₁ Mc y) : e * (y⁻¹ * z * y) = (y⁻¹ * z * y) * e := by
  have h1 : y * e * y⁻¹ ∈ Mc := mem_conjSubgroup_iff.1 he.2
  have h2 : z * (y * e * y⁻¹) = (y * e * y⁻¹) * z :=
    Subgroup.mem_centralizer_iff.1 (cx.hF.H_le_centralizer h1) z hz
  calc e * (y⁻¹ * z * y) = y⁻¹ * ((y * e * y⁻¹) * z) * y := by group
    _ = y⁻¹ * (z * (y * e * y⁻¹)) * y := by rw [h2]
    _ = (y⁻¹ * z * y) * e := by group

theorem fixed_by_Ub_mem_Z (cx : Ctx15350 T Mc M V₁ V₂ t) {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))}
    (c : Chain15353 cx N₁ N₂) {w : Wd cx}
    (hw : ∀ x ∈ autI cx.c.hyp.elemAbelian (UH153 T M V₁ Mc), x w = w) :
    w.val ∈ quasithinOmegaOneCenter T := by
  have hwf : w ∈ fixV (autI cx.c.hyp.elemAbelian (UH153 T M V₁ Mc)) := hw
  have hc := (mem_fixV_autI cx.c.hyp.elemAbelian (U_le_N cx) w).1 hwf
  exact S153E55.centralizer_U_le_Z cx c.h51.one c.h52 w.val_mem fun u hu =>
    Subgroup.mem_centralizer_iff.1 hc u hu

theorem cb_pow_three (cx : Ctx15350 T Mc M V₁ V₂ t) {x : G}
    (hx : x ∈ Subgroup.normalizer (VZ T M : Set G))
    (hx3 : x ^ 3 ∈ Subgroup.normalizer (VZ T M : Set G)) :
    cb cx (x ^ 3) hx3 = (cb cx x hx) ^ 3 := by
  have e : (⟨x ^ 3, hx3⟩ : Subgroup.normalizer (VZ T M : Set G)) = ⟨x, hx⟩ ^ 3 :=
    Subtype.ext (by simp)
  show convI _ ⟨x ^ 3, hx3⟩ = (convI _ ⟨x, hx⟩) ^ 3
  rw [e, map_pow]

theorem not_mem_P {cx : Ctx15350 T Mc M V₁ V₂ t} (c : Chain15354 cx N₁ N₂ g s) {x : G}
    (hx : x ∈ Subgroup.normalizer (VZ T M : Set G)) (hx1 : cb cx x hx ≠ 1) :
    x ∉ Pgp153 T M V₁ Mc g := fun h => hx1 ((cb_eq_one_iff cx x hx).2 (P_le_centralizer c h))

theorem pow_three_mem_P (cx : Ctx15350 T Mc M V₁ V₂ t) (c : Chain15354 cx N₁ N₂ g s) {x : G}
    (hxYU : x ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc) (hx : x ∈ Subgroup.normalizer (VZ T M : Set G))
    (hx3 : cb cx x hx ^ 3 = 1) : x ^ 3 ∈ Pgp153 T M V₁ Mc g := by
  have hxN3 : x ^ 3 ∈ Subgroup.normalizer (VZ T M : Set G) := Subgroup.pow_mem _ hx 3
  have hC : x ^ 3 ∈ Subgroup.centralizer (VZ T M : Set G) := by
    rw [← cb_eq_one_iff cx _ hxN3, cb_pow_three cx hx hxN3]
    exact hx3
  exact S153E55.centralizer_le_P c.h54.one cx ⟨Subgroup.pow_mem _ hxYU 3, hC⟩

theorem tb_facts (cx : Ctx15350 T Mc M V₁ V₂ t) (ht₁ : t₁ ∈ T ∧ t₁ ∉ UCT153 T M V₁ Mc) :
    ∃ ht1N : t₁ ∈ Subgroup.normalizer (VZ T M : Set G),
      cb cx t₁ ht1N ∈ autI cx.c.hyp.elemAbelian T ∧
        cb cx t₁ ht1N ∉ autI cx.c.hyp.elemAbelian (UH153 T M V₁ Mc) := by
  have hV := cx.c.hyp.elemAbelian
  have ht1N : t₁ ∈ Subgroup.normalizer (VZ T M : Set G) := T_le_N cx ht₁.1
  refine ⟨ht1N, convI_mem_autI hV ht₁.1 ht1N, fun h => ht₁.2 ?_⟩
  obtain ⟨⟨u, huN⟩, huU, hu⟩ := (mem_autI hV).1 h
  have hC : u⁻¹ * t₁ ∈ Subgroup.centralizer (VZ T M : Set G) := by
    have hN : u⁻¹ * t₁ ∈ Subgroup.normalizer (VZ T M : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ huN) ht1N
    rw [← cb_eq_one_iff cx _ hN, cb_mul cx u⁻¹ t₁ (Subgroup.inv_mem _ huN) ht1N, cb_inv cx u huN]
    have h' : cb cx u huN = cb cx t₁ ht1N := hu
    rw [h']
    exact inv_mul_cancel _
  have hmem : t₁ = u * (u⁻¹ * t₁) := by group
  rw [hmem]
  exact Subgroup.mul_mem_sup huU ⟨T.mul_mem (T.inv_mem (U_le_T cx huU)) ht₁.1, hC⟩

theorem inf_F_le_P (h113 : StageLemma14113) (cx : Ctx15350 T Mc M V₁ V₂ t)
    (c : Chain15355 cx N₁ N₂ g s)
    (hy : y ∈ Yi153 T Mc M V₁ N₁ ∧ y ∉ pCoreOf 2 (Yi153 T Mc M V₁ N₁))
    (ht₁ : t₁ ∈ T ∧ t₁ ∉ UCT153 T M V₁ Mc) :
    ∀ k ∈ Fgp153 T M V₁ Mc y ⊓ conjSubgroup (Fgp153 T M V₁ Mc y) t₁,
      k ∈ Pgp153 T M V₁ Mc g := by
  intro k hk
  have hV := cx.c.hyp.elemAbelian
  have c' : Chain15353 cx N₁ N₂ := c.toChain15354.toChain15353
  obtain ⟨hyN, hybN₁, hyb1, hyb3, hybfix⟩ := yb_facts h113 cx c hy
  obtain ⟨z, hzZ, hz1, hzu⟩ := exists_z cx
  obtain ⟨a, b, haU, hbU, haN, hbN, ha1, hb1, haa, hbb, hUb, hswap⟩ := ubdata cx c'
  obtain ⟨ht1N, htbT, htbU⟩ := tb_facts cx ht₁
  have hzV : z ∈ VZ T M := cx.c.hyp.Z_le_VZ hzZ
  have hexp : ∀ w : Wd cx, w * w = 1 := fun w => by rw [← pow_two]; exact IntMod.sq_eq_one w
  have hyY : y ∈ Y153 Mc M := (oTwoUpper_le _ hy.1).1
  have hyM : y ∈ M := Y153_le Mc M hyY
  have hzW1 : (IntMod.mk hV ⟨z, hzV⟩ : Wd cx) ≠ 1 := fun h => hz1 (congrArg IntMod.val h)
  have hqz : qW cx (IntMod.mk hV ⟨z, hzV⟩) = 0 := qW_Z cx hzZ
  obtain ⟨hz'1, hz'z, -, -, -, -⟩ :=
    pair_of_order_three hexp (cb_mem_O cx hyM hyN) hyb3 hybfix hzW1 hqz
  obtain ⟨hta, htb'⟩ := hswap _ htbT htbU
  have hN12 : ∀ x : MulAut ↥(VZ T M), x ∈ N₁ → x ∈ N₂ → x = 1 := by
    intro x h1 h2
    have h3 : x ∈ N₁ ⊓ N₂ := ⟨h1, h2⟩
    rw [c.h53one.inf, Subgroup.mem_bot] at h3
    exact h3
  have hUz : ∀ x ∈ autI hV (UH153 T M V₁ Mc),
      x (IntMod.mk hV ⟨z, hzV⟩) = IntMod.mk hV ⟨z, hzV⟩ :=
    fun x hx => (mem_fixV_autI_T_iff cx (IntMod.mk hV ⟨z, hzV⟩)).2 hzZ x (autI_U_le_T cx hx)
  have hbz' : b ((cb cx y hyN)⁻¹ (IntMod.mk hV ⟨z, hzV⟩)) =
      (cb cx y hyN)⁻¹ (IntMod.mk hV ⟨z, hzV⟩) := by
    have hcomm : Commute (cb cx y hyN) b := c.h53one.comm _ hybN₁ b hbN
    have hcomm' : b * (cb cx y hyN)⁻¹ = (cb cx y hyN)⁻¹ * b := hcomm.inv_left.eq.symm
    calc b ((cb cx y hyN)⁻¹ (IntMod.mk hV ⟨z, hzV⟩))
        = (b * (cb cx y hyN)⁻¹) (IntMod.mk hV ⟨z, hzV⟩) := rfl
      _ = ((cb cx y hyN)⁻¹ * b) (IntMod.mk hV ⟨z, hzV⟩) := by rw [hcomm']
      _ = (cb cx y hyN)⁻¹ (b (IntMod.mk hV ⟨z, hzV⟩)) := rfl
      _ = (cb cx y hyN)⁻¹ (IntMod.mk hV ⟨z, hzV⟩) := by rw [hUz b hbU]
  have hall : (∀ x ∈ autI hV (UH153 T M V₁ Mc),
      x ((cb cx y hyN)⁻¹ (IntMod.mk hV ⟨z, hzV⟩)) = (cb cx y hyN)⁻¹ (IntMod.mk hV ⟨z, hzV⟩)) →
      False := by
    intro hall
    have hmem := fixed_by_Ub_mem_Z cx c' hall
    rcases hzu _ hmem with h | h
    · exact hz'1 (IntMod.val_injective h)
    · exact hz'z (IntMod.val_injective h)
  have hstab := stab_aux hUb hbz' hall
  have hfixF : ∀ e (heN : e ∈ Subgroup.normalizer (VZ T M : Set G)), e ∈ Fgp153 T M V₁ Mc y →
      cb cx e heN ((cb cx y hyN)⁻¹ (IntMod.mk hV ⟨z, hzV⟩)) =
        (cb cx y hyN)⁻¹ (IntMod.mk hV ⟨z, hzV⟩) := by
    intro e heN he
    refine IntMod.val_injective ?_
    rw [cb_val, cb_inv_val]
    have h1 := F_comm_z' cx hzZ he
    show e * (y⁻¹ * z * y) * e⁻¹ = y⁻¹ * z * y
    calc e * (y⁻¹ * z * y) * e⁻¹ = (y⁻¹ * z * y) * e * e⁻¹ := by rw [h1]
      _ = y⁻¹ * z * y := by group
  have hkF : k ∈ Fgp153 T M V₁ Mc y := hk.1
  have hkF' : t₁ * k * t₁⁻¹ ∈ Fgp153 T M V₁ Mc y := mem_conjSubgroup_iff.1 hk.2
  have hkU : k ∈ UH153 T M V₁ Mc := hkF.1
  have hkN : k ∈ Subgroup.normalizer (VZ T M : Set G) := U_le_N cx hkU
  have hkb : cb cx k hkN ∈ autI hV (UH153 T M V₁ Mc) := convI_mem_autI hV hkU hkN
  have hk1 := hstab _ hkb (hfixF k hkN hkF)
  have hktN : t₁ * k * t₁⁻¹ ∈ Subgroup.normalizer (VZ T M : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ ht1N hkN) (Subgroup.inv_mem _ ht1N)
  have hcbk' : cb cx (t₁ * k * t₁⁻¹) hktN = cb cx t₁ ht1N * cb cx k hkN * (cb cx t₁ ht1N)⁻¹ := by
    rw [cb_mul cx (t₁ * k) t₁⁻¹ (Subgroup.mul_mem _ ht1N hkN) (Subgroup.inv_mem _ ht1N),
      cb_mul cx t₁ k ht1N hkN, cb_inv cx t₁ ht1N]
  have hkb' : cb cx t₁ ht1N * cb cx k hkN * (cb cx t₁ ht1N)⁻¹ ∈ autI hV (UH153 T M V₁ Mc) :=
    autI_U_normal cx htbT hkb
  have hk2 := hstab _ hkb' (by rw [← hcbk']; exact hfixF _ hktN hkF')
  have hkb1 : cb cx k hkN = 1 := by
    rcases hk1 with h | h
    · exact h
    · exfalso
      rw [h, htb'] at hk2
      rcases hk2 with h2 | h2
      · exact ha1 h2
      · exact ha1 (hN12 a haN (h2 ▸ hbN))
  exact S153E55.centralizer_le_P c.h54.one cx
    ⟨Subgroup.mem_sup_right hkU, (cb_eq_one_iff cx k hkN).1 hkb1⟩

theorem w_facts (h113 : StageLemma14113) (cx : Ctx15350 T Mc M V₁ V₂ t)
    (c : Chain15355 cx N₁ N₂ g s)
    (hy : y ∈ Yi153 T Mc M V₁ N₁ ∧ y ∉ pCoreOf 2 (Yi153 T Mc M V₁ N₁))
    (ht₁ : t₁ ∈ T ∧ t₁ ∉ UCT153 T M V₁ Mc) :
    t₁⁻¹ * y * t₁ ∈ Ni153 T Mc M V₁ N₂ ∧ t₁⁻¹ * y * t₁ ∉ Pgp153 T M V₁ Mc g ∧
      (t₁⁻¹ * y * t₁) ^ 3 ∈ Pgp153 T M V₁ Mc g := by
  have hV := cx.c.hyp.elemAbelian
  obtain ⟨hyN, hybN₁, hyb1, hyb3, -⟩ := yb_facts h113 cx c hy
  obtain ⟨a, b, haU, hbU, haN, hbN, ha1, hb1, haa, hbb, hUb, hswap⟩ :=
    ubdata cx c.toChain15354.toChain15353
  obtain ⟨ht1N, htbT, htbU⟩ := tb_facts cx ht₁
  obtain ⟨e₁⟩ := c.h53one.iso₁
  have hapa : a * cb cx y hyN * a⁻¹ = (cb cx y hyN)⁻¹ :=
    inv_of_invol (W := Wd cx) e₁ haN hybN₁ haa ha1 hyb3 hyb1
  obtain ⟨hta, htb'⟩ := hswap _ htbT htbU
  have hyY : y ∈ Y153 Mc M := (oTwoUpper_le _ hy.1).1
  have hwY : t₁⁻¹ * y * t₁ ∈ Y153 Mc M := by
    have := (Subgroup.mem_normalizer_iff.1
      (S153E55.T_le_normalizer_Y cx (T.inv_mem ht₁.1)) y).1 hyY
    simpa using this
  have hwYU : t₁⁻¹ * y * t₁ ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc := Subgroup.mem_sup_left hwY
  have hwN : t₁⁻¹ * y * t₁ ∈ Subgroup.normalizer (VZ T M : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ ht1N) hyN) ht1N
  have hwb : cb cx (t₁⁻¹ * y * t₁) hwN = (cb cx t₁ ht1N)⁻¹ * cb cx y hyN * cb cx t₁ ht1N :=
    cb_conj cx t₁ y ht1N hyN hwN
  obtain ⟨Ω, hΩ, hΩsup, hΩeq⟩ := c.h53one.omega
  have hwbΩ : cb cx (t₁⁻¹ * y * t₁) hwN ∈ Ω := by
    rw [← hΩsup]
    exact Subgroup.mem_sup_right (convI_mem_autI hV hwY hwN)
  have hwbN : cb cx (t₁⁻¹ * y * t₁) hwN ∈ N₁ ⊔ N₂ := by
    rw [hΩeq]
    exact hwbΩ
  have hwb3 : cb cx (t₁⁻¹ * y * t₁) hwN ^ 3 = 1 := by
    have h := conj_pow (a := (cb cx t₁ ht1N)⁻¹) (b := cb cx y hyN) (i := 3)
    rw [inv_inv] at h
    rw [hwb, h, hyb3]
    group
  have hb' : (cb cx t₁ ht1N)⁻¹ * a * cb cx t₁ ht1N = b := by
    calc (cb cx t₁ ht1N)⁻¹ * a * cb cx t₁ ht1N
        = (cb cx t₁ ht1N)⁻¹ * (cb cx t₁ ht1N * b * (cb cx t₁ ht1N)⁻¹) * cb cx t₁ ht1N := by
          rw [htb']
      _ = b := by group
  have hbwb : b * cb cx (t₁⁻¹ * y * t₁) hwN * b⁻¹ = (cb cx (t₁⁻¹ * y * t₁) hwN)⁻¹ := by
    calc b * cb cx (t₁⁻¹ * y * t₁) hwN * b⁻¹
        = ((cb cx t₁ ht1N)⁻¹ * a * cb cx t₁ ht1N) * ((cb cx t₁ ht1N)⁻¹ * cb cx y hyN * cb cx t₁ ht1N) *
            ((cb cx t₁ ht1N)⁻¹ * a * cb cx t₁ ht1N)⁻¹ := by rw [hwb, hb']
      _ = (cb cx t₁ ht1N)⁻¹ * (a * cb cx y hyN * a⁻¹) * cb cx t₁ ht1N := by group
      _ = (cb cx t₁ ht1N)⁻¹ * (cb cx y hyN)⁻¹ * cb cx t₁ ht1N := by rw [hapa]
      _ = (cb cx (t₁⁻¹ * y * t₁) hwN)⁻¹ := by rw [hwb]; group
  have hwbN₂ : cb cx (t₁⁻¹ * y * t₁) hwN ∈ N₂ :=
    mem_N₂_of_inv (W := Wd cx) c.h53one.comm c.h53one.inf hbN hwbN hwb3 hbwb
  have hwb1 : cb cx (t₁⁻¹ * y * t₁) hwN ≠ 1 := by
    intro h
    apply hyb1
    rw [hwb] at h
    have e : cb cx y hyN = cb cx t₁ ht1N * ((cb cx t₁ ht1N)⁻¹ * cb cx y hyN * cb cx t₁ ht1N) *
        (cb cx t₁ ht1N)⁻¹ := by group
    rw [e, h]
    group
  refine ⟨?_, not_mem_P c.toChain15354 hwN hwb1, pow_three_mem_P cx c.toChain15354 hwYU hwN hwb3⟩
  exact mem_preAut153.2 ⟨hwYU, hwN, hwbN₂⟩

theorem orth_z_of_mem (cx : Ctx15350 T Mc M V₁ V₂ t) {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))}
    (c : Chain15353 cx N₁ N₂) {z : G} (hzZ : z ∈ quasithinOmegaOneCenter T) {v : G}
    (hv : v ∈ VZ T M ⊓ UH153 T M V₁ Mc) :
    quadPolar (qW cx) (IntMod.mk cx.c.hyp.elemAbelian ⟨z, cx.c.hyp.Z_le_VZ hzZ⟩)
      (IntMod.mk cx.c.hyp.elemAbelian ⟨v, hv.1⟩) = 0 := by
  obtain ⟨P', hP', -, hVU, -⟩ := c.h53two.perp
  have hvP : v ∈ P' := hVU ▸ hv
  obtain ⟨hvV, hvort⟩ := (hP' v).1 hvP
  obtain ⟨hzV', hvV', hB⟩ := hvort z hzZ
  exact hB

end Context

end S153E56f

end CFSG.Quasithin
