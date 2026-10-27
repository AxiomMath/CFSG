module

public import CFSG.Quasithin.Vol2.Ch12Sec6L12b
public import CFSG.Quasithin.Vol2.Ch12Sec6L12a

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126N S126T2 CFSG.LieType.BorelTits
open scoped IsMulCommutative Pointwise commutatorElement

namespace S126T2

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem pv02_zero : B5FinS8.pv 0 2 0 = 1 := by
  decide

theorem pv02_one : B5FinS8.pv 0 2 1 = 0 := by
  decide

theorem zmod2_neg_one_ne_zero : (-1 : ZMod 2) ≠ 0 := by
  decide

theorem card_map_mul {X Y : Type*} [Group X] [Group Y] (f : X →* Y) (H : Subgroup X) :
    Nat.card ↥(H.map f) * Nat.card ↥(f.ker ⊓ H) = Nat.card ↥H := by
  rw [← Subgroup.relIndex_ker, Subgroup.relIndex_mul_card]

theorem card_images (h1222 : Stmt12_2_2) (h36 : QuasithinUnique.Vol2Native.A36ForSQTKCat)
    {F : Frame126 T L V} {v : G} {Kv S : Subgroup G} (hC : Ctx1262 F v Kv S)
    (hq : CFSG.IsQuasisimple ↥Kv)
    (hM : Nat.card (↥Kv ⧸ Subgroup.center ↥Kv) = 443520) :
    Nat.card ↥(((Lv L v).subgroupOf Kv).map (QuotientGroup.mk' (Subgroup.center ↥Kv))) = 5760 ∧
      Nat.card ↥(((Vv L V v).subgroupOf Kv).map (QuotientGroup.mk' (Subgroup.center ↥Kv))) =
        16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH := hC.hyp
  have hv := hC.mem
  have hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1) := hC.coord
  have hLK : Lv L v ≤ Kv := hC.lv_le
  have hOL : pCoreOf 2 (Lv L v) ≤ Lv L v := pCoreOf_le 2 _
  have hVO : Vv L V v ≤ pCoreOf 2 (Lv L v) := Vv_le_pCoreOf h1222 hH hv
  set π := QuotientGroup.mk' (Subgroup.center ↥Kv) with hπ
  have hker : π.ker = Subgroup.center ↥Kv := QuotientGroup.ker_mk' _
  have hsub : ∀ H : Subgroup G, H ≤ Kv → Nat.card ↥(H.subgroupOf Kv) = Nat.card ↥H :=
    fun H hHK => Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv
  have hE16 : 16 ≤ Nat.card ↥(((Vv L V v).subgroupOf Kv).map π) := by
    have h1 := card_map_mul π ((Vv L V v).subgroupOf Kv)
    rw [hsub _ (hVO.trans (hOL.trans hLK)), card_Vv h1222 hH hv hβ] at h1
    have h2 : Nat.card ↥(π.ker ⊓ (Vv L V v).subgroupOf Kv) ≤ 2 := by
      rw [← card_Vv_inf h1222 hH hv hβ]
      refine Nat.card_le_card_of_injective
        (fun z => ⟨((z : ↥Kv) : G), z.2.2, Subgroup.mem_centralizer_iff.2 fun l hl => ?_⟩)
        fun a b h => ?_
      · have hz : (z : ↥Kv) ∈ Subgroup.center ↥Kv := hker.le z.2.1
        exact congrArg Subtype.val ((Subgroup.mem_center_iff.1 hz) ⟨l, hLK hl⟩)
      · exact Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val h))
    have h3 : 0 < Nat.card ↥(π.ker ⊓ (Vv L V v).subgroupOf Kv) := Nat.card_pos
    nlinarith
  have hZO : π.ker ⊓ (Lv L v).subgroupOf Kv = π.ker ⊓ (pCoreOf 2 (Lv L v)).subgroupOf Kv := by
    refine le_antisymm (le_inf inf_le_left fun z hz => ?_)
      (inf_le_inf_left _ fun z hz => hOL hz)
    have hzc : z ∈ Subgroup.center ↥Kv := hker.le hz.1
    set Zc := (Subgroup.center ↥Kv).map Kv.subtype with hZc
    have hZ2 : IsPGroup 2 ↥Zc := by
      have h2 : IsPGroup 2 ↥(Subgroup.center ↥Kv) := by
        rw [center_Kv_eq h1222 h36 hC hq]
        exact CFSG.pCore_isPGroup
      exact h2.map _
    have key : ∀ l ∈ Lv L v, ∀ w ∈ Lv L v ⊓ Zc, l * w * l⁻¹ = w := by
      rintro l hl w ⟨-, ⟨w', hw', rfl⟩⟩
      have := (Subgroup.mem_center_iff.1 hw') ⟨l, hLK hl⟩
      have e := congrArg Subtype.val this
      simp only [Subgroup.coe_mul] at e
      show l * (w' : G) * l⁻¹ = (w' : G)
      rw [e, mul_inv_cancel_right]
    have hle : Lv L v ⊓ Zc ≤ pCoreOf 2 (Lv L v) := by
      refine le_pCoreOf_of_le_normalizer 2 inf_le_left (fun l hl => ?_) (hZ2.to_le inf_le_right)
      rw [Subgroup.mem_normalizer_iff]
      intro w
      constructor
      · intro hw
        rw [key l hl w hw]
        exact hw
      · intro hw
        have h1 := key l⁻¹ ((Lv L v).inv_mem hl) _ hw
        have e : w = l * w * l⁻¹ := by
          rw [← h1]
          group
        rw [e]
        exact hw
    exact hle ⟨hz.2, ⟨z, hzc, rfl⟩⟩
  have hL := card_map_mul π ((Lv L v).subgroupOf Kv)
  rw [hsub _ hLK, card_Lv h1222 F hH hv hβ, hZO] at hL
  have hO := card_map_mul π ((pCoreOf 2 (Lv L v)).subgroupOf Kv)
  rw [hsub _ (hOL.trans hLK)] at hO
  have hm : 0 < Nat.card ↥(π.ker ⊓ (pCoreOf 2 (Lv L v)).subgroupOf Kv) := Nat.card_pos
  have hLO : Nat.card ↥(((Lv L v).subgroupOf Kv).map π) =
      360 * Nat.card ↥(((pCoreOf 2 (Lv L v)).subgroupOf Kv).map π) := by
    rw [← hO, ← mul_assoc] at hL
    exact Nat.eq_of_mul_eq_mul_right hm hL
  have hO2 : IsPGroup 2 ↥(((pCoreOf 2 (Lv L v)).subgroupOf Kv).map π) :=
    (((pCoreOf_isPGroup 2 (Lv L v)).of_equiv
      (Subgroup.subgroupOfEquivOfLe (hOL.trans hLK)).symm).map π)
  obtain ⟨k, hk⟩ := hO2.exists_card_eq
  have hdvd : Nat.card ↥(((Lv L v).subgroupOf Kv).map π) ∣ 443520 :=
    hM ▸ Subgroup.card_subgroup_dvd_card _
  rw [hLO, hk] at hdvd
  have hk4 : k ≤ 4 := by
    by_contra h
    have h5 : 360 * 2 ^ 5 ∣ 360 * 2 ^ k := Nat.mul_dvd_mul_left 360 (pow_dvd_pow 2 (by omega))
    have := h5.trans hdvd
    norm_num at this
  have hEO : ((Vv L V v).subgroupOf Kv).map π ≤ ((pCoreOf 2 (Lv L v)).subgroupOf Kv).map π :=
    Subgroup.map_mono fun z hz => hVO hz
  have hEle := Subgroup.card_le_of_le hEO
  rw [hk] at hEle
  have hk' : k = 4 := by
    interval_cases k <;> omega
  subst hk'
  refine ⟨by rw [hLO, hk]; norm_num, ?_⟩
  have h16 : (2 : ℕ) ^ 4 = 16 := by norm_num
  rw [h16] at hEle
  omega

end S126T2

end CFSG.Quasithin.H13
