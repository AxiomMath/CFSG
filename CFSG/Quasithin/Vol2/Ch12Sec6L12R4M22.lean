module

public import CFSG.Quasithin.Vol2.Ch12Sec6L12c
public import CFSG.Quasithin.Vol2.KGFact1262
public import CFSG.Sporadic.Bridge.M22

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126N S126T2 CFSG.LieType.BorelTits
open scoped IsMulCommutative Pointwise commutatorElement

theorem m22_branch (h1222 : Stmt12_2_2) (h36 : QuasithinUnique.Vol2Native.A36ForSQTKCat)
    (hb : FactM22HexadAut) {G : Type} [Group G] [Finite G] {T L V : Subgroup G}
    [IsMulCommutative ↥V] {F : Frame126 T L V} {v : G} {Kv S : Subgroup G} (hC : Ctx1262 F v Kv S)
    (hq : CFSG.IsQuasisimple ↥Kv)
    (eM : Nonempty (↥Kv ⧸ Subgroup.center ↥Kv ≃* ↥NativeSporadic.M22)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eM⟩ := eM
  have hH := hC.hyp
  have hv := hC.mem
  have hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1) := hC.coord
  have hK : ⁅Kv, Kv⁆ = Kv := perfect_of_mem_cComp hC.cComp
  have hLK : S126T2.Lv L v ≤ Kv := hC.lv_le
  obtain ⟨-, hVe⟩ := V_facts h1222 hH
  have hVvO := S126T2.Vv_le_pCoreOf h1222 hH hv
  have hVvL : S126T2.Vv L V v ≤ S126T2.Lv L v := hVvO.trans (pCoreOf_le 2 _)
  have hM22 : Nat.card ↥NativeSporadic.M22 = 443520 := by
    obtain ⟨hfin, hle⟩ := CFSG.Sporadic.Bridge.M22.finite_card_le
    exact le_antisymm ((Nat.card_le_card_of_surjective _
      CFSG.Sporadic.Bridge.M22.toNative_surjective).trans hle)
      CFSG.Sporadic.Bridge.M22.le_card_native
  have hM : Nat.card (↥Kv ⧸ Subgroup.center ↥Kv) = 443520 := by
    rw [Nat.card_congr eM.toEquiv, hM22]
  obtain ⟨hL5760, hE16⟩ := S126T2.card_images h1222 h36 hC hq hM
  set π := QuotientGroup.mk' (Subgroup.center ↥Kv) with hπ
  set Lb := ((S126T2.Lv L v).subgroupOf Kv).map π with hLb
  set Eb := ((S126T2.Vv L V v).subgroupOf Kv).map π with hEb
  have hEL : Eb ≤ Lb := Subgroup.map_mono fun z hz => hVvL hz
  have hLN : Lb ≤ Subgroup.normalizer (Eb : Set (↥Kv ⧸ Subgroup.center ↥Kv)) := by
    refine (Subgroup.map_mono fun l hl => ?_).trans (Subgroup.le_normalizer_map π)
    rw [Subgroup.mem_normalizer_iff]
    intro w
    have h1 := Subgroup.mem_normalizer_iff.1 (S126T2.Lv_le_normalizer_Vv hH v hl) (w : G)
    simpa [Subgroup.mem_subgroupOf] using h1
  obtain ⟨x', hx'⟩ := F.β_surj (QuotientGroup.mk (pe 0 2))
  have hxG : (x' : G) ∈ S126T2.Gv v := by
    show (x' : G) ∈ Subgroup.centralizer {v}
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hVe.1.is_comm.comm x' ⟨v, hv⟩)
  have hxN : (x' : G) ∈ Subgroup.normalizer (Kv : Set G) := hC.normal hxG
  set φx : MulAut ↥Kv := Kv.normalizerMonoidHom ⟨x', hxN⟩ with hφx
  have hφc : (Subgroup.center ↥Kv).map φx.toMonoidHom = Subgroup.center ↥Kv :=
    Subgroup.characteristic_iff_map_eq.1 inferInstance φx
  let α : MulAut (↥Kv ⧸ Subgroup.center ↥Kv) :=
    QuotientGroup.congr (Subgroup.center ↥Kv) (Subgroup.center ↥Kv) φx hφc
  have hα : ∀ k : ↥Kv, α (π k) = π (φx k) := fun k =>
    QuotientGroup.congr_mk (Subgroup.center ↥Kv) (Subgroup.center ↥Kv) φx hφc k
  have hfix : ∀ e ∈ Eb, α e = e := by
    rintro _ ⟨w, hw, rfl⟩
    rw [hα]
    congr 1
    apply Subtype.ext
    show (x' : G) * w * (x' : G)⁻¹ = w
    have hwV : (w : G) ∈ V := S126T2.Vv_le_V hH v hw
    have := congrArg Subtype.val (hVe.1.is_comm.comm x' ⟨w, hwV⟩)
    simp only [Subgroup.coe_mul] at this
    rw [this, mul_inv_cancel_right]
  obtain ⟨e, he, hαe⟩ := hb _ ⟨eM⟩ Lb Eb hL5760 hEL hLN hE16 α hfix
  obtain ⟨u, hu, rfl⟩ := he
  have huV : (u : G) ∈ V := S126T2.Vv_le_V hH v hu
  have hy : ∀ k ∈ Kv, (u : G)⁻¹ * x' * k * ((u : G)⁻¹ * x')⁻¹ * k⁻¹ ∈
      Kv ⊓ Subgroup.centralizer (Kv : Set G) := by
    intro k hk
    have h1 := congrArg (fun f : MulAut (↥Kv ⧸ Subgroup.center ↥Kv) => f (π ⟨k, hk⟩)) hαe
    simp only [hα, MulAut.conj_apply] at h1
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      QuotientGroup.eq] at h1
    set z : ↥Kv := (φx ⟨k, hk⟩)⁻¹ * (u * ⟨k, hk⟩ * u⁻¹) with hz
    have hzc := Subgroup.mem_center_iff.1 h1
    have hzK : (z : G) ∈ Kv := z.2
    have hzC : ∀ w ∈ Kv, w * (z : G) = (z : G) * w := fun w hw =>
      congrArg Subtype.val (hzc ⟨w, hw⟩)
    have hφk : ((φx ⟨k, hk⟩ : ↥Kv) : G) = (x' : G) * k * (x' : G)⁻¹ := rfl
    have hzG : (z : G) = ((x' : G) * k * (x' : G)⁻¹)⁻¹ * ((u : G) * k * (u : G)⁻¹) := by
      rw [hz]
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv, hφk]
    have e1 : (u : G)⁻¹ * x' * k * ((u : G)⁻¹ * x')⁻¹ * k⁻¹ =
        k * ((u : G)⁻¹ * (z : G)⁻¹ * u) * k⁻¹ := by
      rw [hzG]
      group
    have e2 : (u : G)⁻¹ * (z : G)⁻¹ * u = (z : G)⁻¹ := by
      have h2 := hzC _ (Kv.inv_mem u.2)
      calc (u : G)⁻¹ * (z : G)⁻¹ * u = ((u : G)⁻¹ * z * u)⁻¹ := by group
        _ = ((z : G) * (u : G)⁻¹ * u)⁻¹ := by rw [h2]
        _ = (z : G)⁻¹ := by group
    have e3 : k * (z : G)⁻¹ * k⁻¹ = (z : G)⁻¹ := by
      have h2 := hzC k hk
      calc k * (z : G)⁻¹ * k⁻¹ = (k * z * k⁻¹)⁻¹ := by group
        _ = ((z : G) * k * k⁻¹)⁻¹ := by rw [h2]
        _ = (z : G)⁻¹ := by group
    rw [e1, e2, e3]
    refine ⟨Kv.inv_mem hzK, Subgroup.inv_mem _ (Subgroup.mem_centralizer_iff.2 fun w hw => ?_)⟩
    exact hzC w hw
  have hyC := S126T2.mem_centralizer_of_comm_mem_center hK (y := (u : G)⁻¹ * x') fun k hk => by
    have := hy k hk
    simpa [mul_assoc] using this
  have hyL : (u : G)⁻¹ * x' ∈ Subgroup.centralizer (S126T2.Lv L v : Set G) :=
    Subgroup.centralizer_le hLK hyC
  have hyV : (u : G)⁻¹ * x' ∈ V := V.mul_mem (V.inv_mem huV) x'.2
  obtain ⟨c, hc⟩ := QuotientGroup.mk_surjective (F.β ⟨_, hyV⟩)
  have hc01 := S126T2.coord01_of_mem_centralizer h1222 F hH hv hβ hyV hyL hc.symm
  obtain ⟨c', hc', hβu⟩ := S126T2.beta_mem_of_mem_Vv h1222 F hH hv hβ huV hu
  have hx : F.β x' = QuotientGroup.mk (c' * c) := by
    have e : x' = ⟨u, huV⟩ * ⟨_, hyV⟩ := Subtype.ext (by simp)
    rw [e, map_mul, hβu, ← hc, QuotientGroup.mk_mul]
  rw [hx'] at hx
  have h1 : (QuotientGroup.mk ((pe 0 2)⁻¹ * (c' * c)) : D8) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hx, inv_mul_cancel]
  have hpe0 : Multiplicative.toAdd ((pe 0 2 : ↥(coreMod 8)) : PermMod 8) 0 = 1 := by
    rw [S126L20a.toAdd_pe]; exact S126T2.pv02_zero
  have hpe1 : Multiplicative.toAdd ((pe 0 2 : ↥(coreMod 8)) : PermMod 8) 1 = 0 := by
    rw [S126L20a.toAdd_pe]; exact S126T2.pv02_one
  obtain ⟨hc'0, hc'1⟩ := mem_core01.1 hc'
  have hd : ∀ d : ↥(coreMod 8), d = 1 ∨ d = S126FE.eOm →
      Multiplicative.toAdd (d : PermMod 8) 0 = Multiplicative.toAdd (d : PermMod 8) 1 := by
    rintro d (rfl | rfl)
    · rfl
    · rfl
  have h2 := hd _ ((S126FE.mk_eq_one_iff _).1 h1)
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, toAdd_mul, toAdd_inv, Pi.add_apply,
    Pi.neg_apply, hpe0, hpe1, hc'0, hc'1, hc01] at h2
  have h3 : (-1 : ZMod 2) = 0 := by linear_combination h2
  exact S126T2.zmod2_neg_one_ne_zero h3

end CFSG.Quasithin.H13
