module

public import CFSG.Quasithin.Vol2.Ch12Sec6L12R1Defs
public import CFSG.Quasithin.Vol2.Ch12Sec6L12c

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126N S126T2 CFSG.LieType.BorelTits
open scoped IsMulCommutative Pointwise commutatorElement

namespace S126T2

variable {G : Type} [Group G]

abbrev rhoK (Kv : Subgroup G) : ↥Kv →* ↥Kv ⧸ Subgroup.center ↥Kv :=
  QuotientGroup.mk' (Subgroup.center ↥Kv)

noncomputable abbrev Lbar (L : Subgroup G) (v : G) (Kv : Subgroup G) :
    Subgroup (↥Kv ⧸ Subgroup.center ↥Kv) :=
  ((Lv L v).subgroupOf Kv).map (rhoK Kv)

noncomputable abbrev Pbar (L : Subgroup G) (v : G) (Kv : Subgroup G) :
    Subgroup (↥Kv ⧸ Subgroup.center ↥Kv) :=
  ((pCoreOf 2 (Lv L v)).subgroupOf Kv).map (rhoK Kv)

noncomputable abbrev Ebar (L V : Subgroup G) (v : G) (Kv : Subgroup G) :
    Subgroup (↥Kv ⧸ Subgroup.center ↥Kv) :=
  ((Vv L V v).subgroupOf Kv).map (rhoK Kv)

variable [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem a6LocalData_of_ctx (h1222 : Stmt12_2_2) (h36 : QuasithinUnique.Vol2Native.A36ForSQTKCat)
    {F : Frame126 T L V} {v : G} {Kv S : Subgroup G} (hC : Ctx1262 F v Kv S)
    (hq : CFSG.IsQuasisimple ↥Kv)
    (hcent : Vv L V v ⊓ Subgroup.centralizer (Lv L v : Set G) ≤
      (Subgroup.center ↥Kv).map Kv.subtype) :
    A6LocalData (Lbar L v Kv) (Pbar L v Kv) (Ebar L V v Kv) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH := hC.hyp
  have hv := hC.mem
  have hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1) := hC.coord
  have hLK : Lv L v ≤ Kv := hC.lv_le
  have hOL : pCoreOf 2 (Lv L v) ≤ Lv L v := pCoreOf_le 2 _
  have hVO : Vv L V v ≤ pCoreOf 2 (Lv L v) := Vv_le_pCoreOf h1222 hH hv
  obtain ⟨-, hVe⟩ := V_facts h1222 hH
  set π := rhoK Kv with hπ
  have hker : π.ker = Subgroup.center ↥Kv := QuotientGroup.ker_mk' _
  have hsub : ∀ H : Subgroup G, H ≤ Kv → Nat.card ↥(H.subgroupOf Kv) = Nat.card ↥H :=
    fun H hHK => Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv
  have hkerV : Nat.card ↥(π.ker ⊓ (Vv L V v).subgroupOf Kv) = 2 := by
    have hle2 : Nat.card ↥(π.ker ⊓ (Vv L V v).subgroupOf Kv) ≤ 2 := by
      rw [← card_Vv_inf h1222 hH hv hC.coord]
      refine Nat.card_le_card_of_injective
        (fun z => ⟨((z : ↥Kv) : G), z.2.2, Subgroup.mem_centralizer_iff.2 fun l hl => ?_⟩)
        fun a b h => ?_
      · have hz : (z : ↥Kv) ∈ Subgroup.center ↥Kv := hker.le z.2.1
        exact congrArg Subtype.val ((Subgroup.mem_center_iff.1 hz) ⟨l, hLK hl⟩)
      · exact Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val h))
    have hge2 : 2 ≤ Nat.card ↥(π.ker ⊓ (Vv L V v).subgroupOf Kv) := by
      rw [← card_Vv_inf h1222 hH hv hC.coord]
      have hVK : Vv L V v ≤ Kv := hVO.trans (hOL.trans hLK)
      refine Nat.card_le_card_of_injective
        (fun y => ⟨⟨(y : G), hVK y.2.1⟩, ?_, y.2.1⟩) fun a b h => ?_
      · rw [hker]
        obtain ⟨z, hz, hzy⟩ := hcent y.2
        have : (⟨(y : G), hVK y.2.1⟩ : ↥Kv) = z := Subtype.ext hzy.symm
        rw [this]
        exact hz
      · have h' := congrArg
          (fun w : ↥(π.ker ⊓ (Vv L V v).subgroupOf Kv) => ((w : ↥Kv) : G)) h
        exact Subtype.ext h'
    omega
  have hE16 : Nat.card ↥(Ebar L V v Kv) = 16 := by
    have h1 := card_map_mul π ((Vv L V v).subgroupOf Kv)
    rw [hsub _ (hVO.trans (hOL.trans hLK)), card_Vv h1222 hH hv hC.coord, hkerV] at h1
    have h2 : Nat.card ↥(Ebar L V v Kv) * 2 = 32 := h1
    omega
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
  rw [hsub _ hLK, card_Lv h1222 F hH hv hC.coord, hZO] at hL
  have hO := card_map_mul π ((pCoreOf 2 (Lv L v)).subgroupOf Kv)
  rw [hsub _ (hOL.trans hLK)] at hO
  have hm : 0 < Nat.card ↥(π.ker ⊓ (pCoreOf 2 (Lv L v)).subgroupOf Kv) := Nat.card_pos
  have hLO : Nat.card ↥(Lbar L v Kv) = 360 * Nat.card ↥(Pbar L v Kv) := by
    rw [← hO, ← mul_assoc] at hL
    exact Nat.eq_of_mul_eq_mul_right hm hL
  have hO2 : IsPGroup 2 ↥(Pbar L v Kv) :=
    (((pCoreOf_isPGroup 2 (Lv L v)).of_equiv
      (Subgroup.subgroupOfEquivOfLe (hOL.trans hLK)).symm).map π)
  have hEO : Ebar L V v Kv ≤ Pbar L v Kv := Subgroup.map_mono fun z hz => hVO hz
  have hLNP : Lbar L v Kv ≤
      Subgroup.normalizer (Pbar L v Kv : Set (↥Kv ⧸ Subgroup.center ↥Kv)) := by
    refine (Subgroup.map_mono fun l hl => ?_).trans (Subgroup.le_normalizer_map π)
    rw [Subgroup.mem_normalizer_iff]
    intro w
    have h1 := Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 (Lv L v) hl) (w : G)
    simpa [Subgroup.mem_subgroupOf] using h1
  have hLNE : Lbar L v Kv ≤
      Subgroup.normalizer (Ebar L V v Kv : Set (↥Kv ⧸ Subgroup.center ↥Kv)) := by
    refine (Subgroup.map_mono fun l hl => ?_).trans (Subgroup.le_normalizer_map π)
    rw [Subgroup.mem_normalizer_iff]
    intro w
    have h1 := Subgroup.mem_normalizer_iff.1 (Lv_le_normalizer_Vv hH v hl) (w : G)
    simpa [Subgroup.mem_subgroupOf] using h1
  have hperf : ⁅(Lv L v).subgroupOf Kv, (Lv L v).subgroupOf Kv⁆ = (Lv L v).subgroupOf Kv := by
    apply Subgroup.map_injective Kv.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hLK]
    exact perfectCore_perfect _
  have hEl : IsElemAbelian 2 (Ebar L V v Kv) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · rcases a with ⟨_, a', ha', rfl⟩
      rcases b with ⟨_, b', hb', rfl⟩
      apply Subtype.ext
      show π a' * π b' = π b' * π a'
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      show (a' : G) * b' = b' * a'
      exact congrArg (fun z : ↥V => (z : G)) (hVe.1.is_comm.comm ⟨a', Vv_le_V hH v ha'⟩
        ⟨b', Vv_le_V hH v hb'⟩)
    · obtain ⟨a', ha', rfl⟩ := hx
      rw [← map_pow]
      have : a' ^ 2 = 1 := Subtype.ext (hVe.2 (a' : G) (Vv_le_V hH v ha'))
      rw [this, map_one]
  exact
    { perfect := by rw [Lbar, ← Subgroup.map_commutator, hperf]
      le := Subgroup.map_mono fun z hz => hOL hz
      pGroup := hO2
      normalizes := hLNP
      card := hLO
      le_P := hEO
      elemAbelian := hEl
      card_E := hE16
      normalizes_E := hLNE }

end S126T2

end CFSG.Quasithin.H13
