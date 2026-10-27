module

public import CFSG.Quasithin.Recognition.HSType15b

public section

namespace CFSG.Quasithin.HSType

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.L34Amalgam

variable {G : Type*} [Group G]

namespace HSSetting

variable {z : G} {V : Subgroup G} {s : G}

namespace S6Model

variable (M : S6Model z s)

abbrev L1 : Subgroup G := M.pre lamS

theorem hsB_le_L1 : hsB z s ≤ M.L1 := M.hsB_le_pre lamS

theorem R_le_L1 : M.R ≤ M.L1 := M.pre_mono (inf_le_left : kleinS ≤ lamS)

theorem RX_le_L1 : M.RX ≤ M.L1 := M.pre_mono (inf_le_left : lam0 ≤ lamS)

theorem L1_le_hsNB : M.L1 ≤ hsNB z s := M.pre_le_hsNB lamS

section Complement

variable [Finite G] (h : HSSetting z V) (hsmemH : s ∈ hsH z) (hsnotK : s ∉ hsK z)
  (hss : s * s = 1) {g₀ : G} (hg₀ : g₀ * z * g₀⁻¹ = s)

include h hsmemH hsnotK hss hg₀ in
theorem card_L1 : Nat.card M.L1 = 960 := by
  show Nat.card ↥(M.pre lamS) = 960
  rw [M.card_pre h hsmemH hsnotK hss hg₀, card_lamS]

include h hsmemH hsnotK hss hg₀ in
theorem card_RX : Nat.card M.RX = 192 := by
  show Nat.card ↥(M.pre lam0) = 192
  rw [M.card_pre h hsmemH hsnotK hss hg₀, card_lam0]

include h hsmemH hsnotK hss hg₀ in
theorem exists_complement_L1 :
    ∃ C : Subgroup G, C ≤ M.L1 ∧ hsB z s ⊓ C = ⊥ ∧ Nat.card C = 60 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg, hgNN⟩ := M.exists_g h hsmemH hsnotK hss hg₀
  have hBL := M.hsB_le_L1
  set Pm : Subgroup ↥M.L1 := (hsB z s).subgroupOf M.L1 with hPm
  have hPn : Pm.Normal := ⟨fun n hn x => by
    rw [hPm, Subgroup.mem_subgroupOf] at hn ⊢
    exact conj_mem_hsB_of_mem (M.L1_le_hsNB x.2) hn⟩
  have hPc : IsMulCommutative ↥Pm := ⟨⟨fun a b => Subtype.ext (Subtype.ext
    (h.hsB_comm hsmemH hsnotK hss (Subgroup.mem_subgroupOf.mp a.2)
      (Subgroup.mem_subgroupOf.mp b.2)))⟩⟩
  have hPcard : Nat.card Pm = 16 := by
    rw [hPm, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv,
      h.card_hsB hsmemH hsnotK hss]
  have hPp : IsPGroup 2 ↥Pm := IsPGroup.of_card (n := 4) (by rw [hPcard]; norm_num)
  have hRL := M.R_le_L1
  have hRcard : Nat.card M.R = 64 := by
    show Nat.card ↥(M.pre kleinS) = 64
    rw [M.card_pre h hsmemH hsnotK hss hg₀, card_kleinS]
  have hRp : IsPGroup 2 ↥(M.R.subgroupOf M.L1) := IsPGroup.of_card (n := 6) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRL).toEquiv, hRcard]
    norm_num)
  have hRidx : ¬ 2 ∣ (M.R.subgroupOf M.L1).index := by
    have h1 := (M.R.subgroupOf M.L1).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRL).toEquiv, hRcard,
      M.card_L1 h hsmemH hsnotK hss hg₀] at h1
    have h15 : (M.R.subgroupOf M.L1).index = 15 := by omega
    rw [h15]
    decide
  let S : Sylow 2 ↥M.L1 := hRp.toSylow hRidx
  have hS : (S : Subgroup ↥M.L1) = M.R.subgroupOf M.L1 := rfl
  have hC0L : M.C0 g ≤ M.L1 :=
    M.C0_le_hsB'.trans ((M.hsB'_le_R h hsmemH hsnotK hss hg₀ hg).trans hRL)
  have hinf : Pm ⊓ (M.C0 g).subgroupOf M.L1 = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun x ⟨hxP, hxC⟩ => Subtype.ext ?_
    have hx : (x : G) ∈ M.C0 g ⊓ hsB z s := ⟨hxC, hxP⟩
    rw [M.C0_inf_hsB h hsmemH hsnotK hss hg₀ hg hgNN, Subgroup.mem_bot] at hx
    exact hx
  have hsup : Pm ⊔ (M.C0 g).subgroupOf M.L1 = (S : Subgroup ↥M.L1) := by
    rw [hS, hPm, ← Subgroup.subgroupOf_sup hBL hC0L,
      M.hsB_sup_C0 h hsmemH hsnotK hss hg₀ hg hgNN]
  obtain ⟨K, hK1, hK2⟩ := (CFSG.Quasithin.gaschutz (G := ↥M.L1) hPp S).mpr
    ⟨(M.C0 g).subgroupOf M.L1, (le_sup_right : _ ≤ Pm ⊔ _).trans hsup.le, hinf, hsup⟩
  refine ⟨K.map M.L1.subtype, Subgroup.map_subtype_le K, ?_, ?_⟩
  · refine (Subgroup.eq_bot_iff_forall _).mpr fun x ⟨hxB, hxK⟩ => ?_
    obtain ⟨k, hk, rfl⟩ := hxK
    have hkP : k ∈ Pm := Subgroup.mem_subgroupOf.mpr hxB
    have hk1 : k ∈ Pm ⊓ K := ⟨hkP, hk⟩
    rw [hK1, Subgroup.mem_bot] at hk1
    rw [hk1, map_one]
  · have hKN : K ≤ Subgroup.normalizer (Pm : Set ↥M.L1) := by
      rw [Subgroup.normalizer_eq_top]
      exact le_top
    have hp := card_sup_mul_card_inf_of_le_normalizer hKN
    rw [sup_comm, hK2, inf_comm, hK1, Subgroup.card_top, Subgroup.card_bot, mul_one,
      M.card_L1 h hsmemH hsnotK hss hg₀, hPcard] at hp
    rw [Subgroup.card_map_of_injective M.L1.subtype_injective]
    omega

include h hsmemH hsnotK hss hg₀ in
theorem isParabolic_L1 : ∃ a b : G, IsParabolic M.L1 (hsB z s) a b := by
  obtain ⟨C, hCL, hBC, hCc⟩ := M.exists_complement_L1 h hsmemH hsnotK hss hg₀
  have hCN : C ≤ hsNB z s := hCL.trans M.L1_le_hsNB
  set πC : ↥C →* Equiv.Perm (Fin 6) := M.π.comp (Subgroup.inclusion hCN) with hπCdef
  have hπC : ∀ c : ↥C, πC c = M.π ⟨c, hCN c.2⟩ := fun c => rfl
  have hinj : Function.Injective πC := by
    rw [injective_iff_map_eq_one]
    intro c hc
    rw [hπC] at hc
    have hcB : (c : G) ∈ hsB z s := (M.ker ⟨c, hCN c.2⟩).mp hc
    have hcBC : (c : G) ∈ hsB z s ⊓ C := ⟨hcB, c.2⟩
    rw [hBC, Subgroup.mem_bot] at hcBC
    exact Subtype.ext hcBC
  have hrange : πC.range = lamS := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · intro x hx
      obtain ⟨c, rfl⟩ := MonoidHom.mem_range.mp hx
      rw [hπC]
      exact M.π_mem_of_mem_pre (hCL c.2) (hCN c.2)
    · rw [card_lamS, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hCc]
  obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp (show αS ∈ πC.range by rw [hrange]; exact αS_mem)
  obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp (show βS ∈ πC.range by rw [hrange]; exact βS_mem)
  have ha2 : a * a = 1 := hinj (by rw [map_mul, ha, αS_mul_self, map_one])
  have hb3 : b ^ 3 = 1 := hinj (by rw [map_pow, hb, βS_pow_three, map_one])
  have hab5 : (a * b) ^ 5 = 1 := hinj (by rw [map_pow, map_mul, ha, hb, αS_βS_pow_five, map_one])
  have hcl : Subgroup.closure {(a : G), (b : G)} = C := by
    refine le_antisymm ?_ fun c hc => ?_
    · rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact a.2
      · exact b.2
    · have hmem : πC ⟨c, hc⟩ ∈ (Subgroup.closure {a, b}).map πC := by
        rw [MonoidHom.map_closure, Set.image_pair, ha, hb, closure_αS_βS, ← hrange]
        exact MonoidHom.mem_range.mpr ⟨⟨c, hc⟩, rfl⟩
      obtain ⟨d, hd, hdc⟩ := hmem
      rw [hinj hdc] at hd
      have hmap : (Subgroup.closure {a, b}).map C.subtype =
          Subgroup.closure {(a : G), (b : G)} := by
        rw [MonoidHom.map_closure, Set.image_pair, Subgroup.coe_subtype]
      rw [← hmap]
      exact ⟨⟨c, hc⟩, hd, rfl⟩
  refine ⟨(a : G), (b : G), M.hsB_le_L1,
    fun x hx e he => conj_mem_hsB_of_mem (M.L1_le_hsNB hx) he,
    fun e he => h.hsB_sq hsmemH hsnotK hss he, h.card_hsB hsmemH hsnotK hss,
    M.card_L1 h hsmemH hsnotK hss hg₀, hCL a.2, hCL b.2, by rw [hcl]; exact hBC,
    by rw [hcl]; exact hCc, congrArg Subtype.val ha2,
    by rw [← Subgroup.coe_pow, hb3, Subgroup.coe_one],
    by rw [← Subgroup.coe_mul, ← Subgroup.coe_pow, hab5, Subgroup.coe_one], fun e he hbe => ?_⟩
  obtain ⟨v, rfl⟩ := M.surj e he
  have h1 : (b : G) * M.Φ v * (b : G)⁻¹ = M.Φ v := by rw [hbe, mul_inv_cancel_right]
  rw [M.act' (hCN b.2) v, ← hπC, hb] at h1
  rw [eq_zero_of_actS6_βS v (M.inj h1), M.Φ_zero]

include h hsmemH hsnotK hss hg₀ in
theorem parabolics_of_g {g : G} (hg : g ∈ Subgroup.normalizer (M.V2 : Set G)) (hgNN : g ∉ M.NN) :
    ∃ a b : G, IsParabolic M.L1 (hsB z s) a b ∧
      IsParabolic (M.L1.map (MulAut.conj g).toMonoidHom)
        ((hsB z s).map (MulAut.conj g).toMonoidHom) (g * a * g⁻¹) (g * b * g⁻¹) ∧
      hsB z s ≤ M.L1.map (MulAut.conj g).toMonoidHom ∧
      (hsB z s).map (MulAut.conj g).toMonoidHom ≤ M.L1 ∧
      hsB z s ≠ (hsB z s).map (MulAut.conj g).toMonoidHom ∧
      M.L1 ⊓ M.L1.map (MulAut.conj g).toMonoidHom = M.RX ∧
      Nat.card ↥(M.L1 ⊓ M.L1.map (MulAut.conj g).toMonoidHom) = 192 := by
  obtain ⟨a, b, hab⟩ := M.isParabolic_L1 h hsmemH hsnotK hss hg₀
  have hg' : g⁻¹ ∈ Subgroup.normalizer (M.V2 : Set G) := (Subgroup.normalizer _).inv_mem hg
  have hRX : M.RX ≤ M.L1.map (MulAut.conj g).toMonoidHom := fun x hx => by
    rw [mem_map_conj_iff]
    have := M.conj_mem_RX h hsmemH hsnotK hss hg₀ hg' hx
    rw [inv_inv] at this
    exact M.RX_le_L1 this
  have hinf : M.L1 ⊓ M.L1.map (MulAut.conj g).toMonoidHom = M.RX := by
    refine le_antisymm (fun y ⟨hy₁, hy₂⟩ => ?_) (le_inf M.RX_le_L1 hRX)
    have hyN := M.L1_le_hsNB hy₁
    have hB' : ∀ u ∈ (hsB z s).map (MulAut.conj g).toMonoidHom, ∀ x ∈ M.L1.map
        (MulAut.conj g).toMonoidHom, x * u * x⁻¹ ∈ (hsB z s).map (MulAut.conj g).toMonoidHom := by
      intro u hu x hx
      rw [mem_map_conj_iff] at hu hx ⊢
      have := conj_mem_hsB_of_mem (M.L1_le_hsNB hx) hu
      rwa [show g⁻¹ * x * g * (g⁻¹ * u * g) * (g⁻¹ * x * g)⁻¹ = g⁻¹ * (x * u * x⁻¹) * g by
        group] at this
    have hV : ∀ u ∈ M.V2, ∀ x, x ∈ M.L1 → x ∈ M.L1.map (MulAut.conj g).toMonoidHom →
        x * u * x⁻¹ ∈ M.V2 := by
      intro u hu x hx₁ hx₂
      rw [← M.hsB_inf_hsB' h hsmemH hsnotK hss hg₀ hg hgNN] at hu ⊢
      exact ⟨conj_mem_hsB_of_mem (M.L1_le_hsNB hx₁) hu.1, hB' u hu.2 x hx₂⟩
    have hyV : y ∈ Subgroup.normalizer (M.V2 : Set G) := by
      refine Subgroup.mem_normalizer_iff.mpr fun u => ⟨fun hu => hV u hu y hy₁ hy₂, fun hu => ?_⟩
      have := hV _ hu y⁻¹ (M.L1.inv_mem hy₁) (Subgroup.inv_mem _ hy₂)
      rwa [show y⁻¹ * (y * u * y⁻¹) * y⁻¹⁻¹ = u by group] at this
    have hyNN := M.mem_NN_of_normalizes hyN hyV
    refine M.mem_pre.mpr ⟨hyN, ⟨M.π_mem_of_mem_pre hy₁ hyN, M.π_mem_of_mem_pre hyNN hyN⟩⟩
  refine ⟨a, b, hab, hab.map (MulAut.conj g).toMonoidHom (MulAut.conj g).injective,
    (M.hsB_le_pre lam0).trans hRX, (M.hsB'_le_RX h hsmemH hsnotK hss hg₀ hg).trans M.RX_le_L1,
    (M.hsB'_ne hg hgNN).symm, hinf, ?_⟩
  rw [hinf, M.card_RX h hsmemH hsnotK hss hg₀]

end Complement

end S6Model

end HSSetting

end CFSG.Quasithin.HSType
