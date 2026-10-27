module

public import CFSG.Quasithin.EmptyFaithful.SBd14Mid
public import CFSG.Quasithin.EmptyFaithful.SBd15Comp

public section

namespace CFSG.Quasithin.SBd19

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits CFSG.Blueprint

@[expose] def M23NoDoubleCover : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Group.IsPerfect X → ∀ (Z : Subgroup X) [Z.Normal],
    Z ≤ Subgroup.center X → Nat.card Z = 2 → ¬ IsSporadic .M23 (X ⧸ Z)

theorem M23NoDoubleCover.not_order_four (hM : M23NoDoubleCover) {X : Type} [Group X] [Finite X]
    (hX : Group.IsPerfect X) (Z : Subgroup X) [Z.Normal] (hZ : Z ≤ Subgroup.center X)
    (hcard : Nat.card Z = 4) : ¬ IsSporadic .M23 (X ⧸ Z) := by
  classical
  intro hspor
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hX
  obtain ⟨z, hz⟩ : ∃ z : Z, orderOf z = 2 :=
    exists_prime_orderOf_dvd_card' 2 (by rw [hcard]; norm_num)
  set W : Subgroup X := Subgroup.zpowers (z : X) with hW
  have hWZ : W ≤ Z := (Subgroup.zpowers_le).2 z.2
  have hWc : W ≤ Subgroup.center X := hWZ.trans hZ
  have hWn : W.Normal := ⟨fun n hn g => by
    have h := Subgroup.mem_center_iff.mp (hWc hn) g
    rw [h, mul_inv_cancel_right]
    exact hn⟩
  have hWcard : Nat.card W = 2 := by
    rw [hW, Nat.card_zpowers, Subgroup.orderOf_coe, hz]
  set π : X →* (X ⧸ W) := QuotientGroup.mk' W with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective W
  set Z' : Subgroup (X ⧸ W) := Z.map π with hZ'
  have hZ'n : Z'.Normal := Subgroup.Normal.map inferInstance π hπs
  have hZ'c : Z' ≤ Subgroup.center (X ⧸ W) :=
    (Subgroup.map_mono hZ).trans (Subgroup.map_center_le_center hπs)
  have e1 : Nat.card X = Nat.card (X ⧸ Z) * Nat.card Z := Subgroup.card_eq_card_quotient_mul_card_subgroup Z
  have e2 : Nat.card X = Nat.card (X ⧸ W) * Nat.card W := Subgroup.card_eq_card_quotient_mul_card_subgroup W
  have e3 : Nat.card (X ⧸ W) = Nat.card ((X ⧸ W) ⧸ Z') * Nat.card Z' :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup Z'
  have e4 : Nat.card ((X ⧸ W) ⧸ Z') = Nat.card (X ⧸ Z) :=
    Nat.card_congr (QuotientGroup.quotientQuotientEquivQuotient W Z hWZ).toEquiv
  have hq : 0 < Nat.card (X ⧸ Z) := Nat.card_pos
  have hZ'card : Nat.card Z' = 2 := by
    rw [hcard] at e1
    rw [hWcard] at e2
    rw [e4] at e3
    have h : Nat.card (X ⧸ Z) * Nat.card Z' = Nat.card (X ⧸ Z) * 2 := by
      rw [← e3]
      omega
    exact Nat.eq_of_mul_eq_mul_left hq h
  refine hM (X ⧸ W) inferInstance Z' hZ'c hZ'card ?_
  obtain ⟨e⟩ := hspor
  exact ⟨(QuotientGroup.quotientQuotientEquivQuotient W Z hWZ).trans e⟩

end CFSG.Quasithin.SBd19

namespace CFSG.Quasithin.SBd14

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem RestHyp.false_of_m23_dc (r : RestHyp T Mc M V₁ V₂ Yp I L t) (h113 : StageLemma14113)
    (hM : SBd19.M23NoDoubleCover) {Hv L' : Subgroup G} (hLL' : L ≤ L') (hL' : L' ∈ cComp Hv)
    (hΩ : pCoreOf 2 Hv = V₁) (hm23 : IsSporadic .M23 ↥(modO2Image Hv L')) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have D0 := r.ctx.hyp.decomp
  have hV₁L : V₁ ≤ L := by
    rw [r.V₁_eq_center h113]
    exact fun x hx => hx.1
  have hL'H : L' ≤ Hv := le_of_mem_cComp hL'
  have hperfS : ⁅L', L'⁆ = L' := perfect_of_mem_cComp hL'
  have hperf : Group.IsPerfect ↥L' := Subgroup.isPerfect_iff.mpr hperfS
  have hnormV : L' ≤ Subgroup.normalizer (V₁ : Set G) := by
    intro x hx
    rw [← hΩ]
    exact le_normalizer_pCoreOf 2 Hv (hL'H hx)
  have hcentV : L' ≤ Subgroup.centralizer (V₁ : Set G) :=
    SBd15.le_centralizer_of_isPerfect_of_card_le_four D0.card₁.le hnormV hperfS
  let f : ↥L' →* (↥Hv ⧸ CFSG.pCore 2 ↥Hv) :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥Hv)).comp (Subgroup.inclusion hL'H)
  have hrange : f.range = modO2Image Hv L' := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  have hker : ∀ x : ↥L', x ∈ f.ker ↔ (x : G) ∈ V₁ := by
    intro x
    rw [MonoidHom.mem_ker]
    have h1 : f x = 1 ↔ (⟨(x : G), hL'H x.2⟩ : ↥Hv) ∈ CFSG.pCore 2 ↥Hv := by
      simp only [f, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact Iff.rfl
    rw [h1, S153D.mem_pCore_iff, hΩ]
  have hZc : f.ker ≤ Subgroup.center ↥L' := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have h1 := (hker x).mp hx
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hcentV y.2) _ h1).symm
  have hspor : IsSporadic .M23 (↥L' ⧸ f.ker) := by
    obtain ⟨e⟩ := hm23
    exact ⟨((QuotientGroup.quotientKerEquivRange f).trans (MulEquiv.subgroupCongr hrange)).trans e⟩
  have hV₁L' : V₁ ≤ L' := fun x hx => hLL' (hV₁L hx)
  have hkereq : f.ker = V₁.subgroupOf L' := by
    ext x
    rw [hker x, Subgroup.mem_subgroupOf]
  have hcard4 : Nat.card f.ker = 4 := by
    rw [hkereq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV₁L').toEquiv]
    exact D0.card₁
  exact hM.not_order_four hperf f.ker hZc hcard4 hspor

end CFSG.Quasithin.SBd14
