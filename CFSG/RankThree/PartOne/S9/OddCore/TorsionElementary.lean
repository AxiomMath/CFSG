module

public import CFSG.RankThree.PartOne.S9.StatementsAlpha
public import CFSG.RankThree.PartOne.S9.OddCore.TorsionInflate
public import CFSG.RankThree.PartOne.S9.OddCore.TorsionModule
public import CFSG.RankThree.PartOne.S9.OddCore.TorsionCommon
public import CFSG.RankThree.PGroups.MaximalNormalElementaryCentralizer
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBMFrattiniGeneratorBound

public section

namespace CFSG.RankThree.PartOne.Torsion37

open CFSG Subgroup
open scoped commutatorElement

theorem le_normalizer_of_normal {G : Type*} [Group G] (R Y : Subgroup G) [hY : Y.Normal] :
    R ≤ Subgroup.normalizer (Y : Set G) :=
  le_normalizer_of_forall fun _ _ y hy => hY.conj_mem y hy _

theorem omegaOne_eq_of_elementary
    (hET32 : ExtraspecialThirtyTwoFixedRankTwoAction) (hPG2C : PGOddSecondCenterPrimeTorsion)
    {G : Type} [Group G] [Finite G] {q : ℕ} {A R Q D : Subgroup G} (hq : q.Prime)
    (hq2 : q ≠ 2) (hq5 : q ≠ 5) (hA : Nat.card A = 5)
    (hAR : A ≤ Subgroup.normalizer (R : Set G))
    (hR : IsExtraspecialPGroup 2 R) (hR32 : Nat.card R = 32)
    (ha : ∃ a ∈ A, ∀ r ∈ R, r ∉ inSubgroup Subgroup.center R →
      ⁅a, r⁆ ∉ inSubgroup Subgroup.center R)
    [hQn : Q.Normal] (hQp : IsPGroup q Q) (hDQ : D ≤ Q) [hDn : D.Normal]
    (hRD : R ⊓ Subgroup.centralizer (D : Set G) = ⊥)
    (hDel : IsElementaryAbelian q D) (hDcard : Nat.card D = q ^ 4)
    (hrank : ∀ r ∈ R, r ≠ 1 → CFSG.pRank q ↥(Q ⊓ Subgroup.centralizer ({r} : Set G)) ≤ 2) :
    omegaOne q Q = D := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  have hDexp : ∀ x ∈ D, x ^ q = 1 := fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx
  have hDq : IsPGroup q D := hQp.to_le hDQ
  have hrel : (inSubgroup frattini D).relIndex D = q ^ 4 :=
    OddCore37.isQDShape_relIndex_frattini hq (Or.inl ⟨hDel, hDcard⟩)
  obtain ⟨hirr, -⟩ := frattini_module_facts hq hq2 hDq hrel hR hR32 hRD
  have hΦ : inSubgroup frattini D = ⊥ := by
    have : Fact (IsPGroup q D) := ⟨hDq⟩
    unfold inSubgroup
    rw [frattini_eq_bot_of_isElementaryAbelian (R := ↥D) (p := q), Subgroup.map_bot]
  have hDQcard : Nat.card (D.subgroupOf Q) = q ^ 4 := by
    rw [← hDcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDQ).toEquiv
  have hNne : D.subgroupOf Q ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hDQcard
    have : 1 < q ^ 4 := Nat.one_lt_pow (by norm_num) hq.one_lt
    omega
  obtain ⟨-, hle⟩ := CFSG.SectionRank.Ccomm.normal_inf_center_card hQp hNne
  set Y : Subgroup G := ((D.subgroupOf Q) ⊓ Subgroup.center ↥Q).map Q.subtype with hY
  have hYne : Y ≠ ⊥ := by
    intro h
    rw [hY, Subgroup.map_eq_bot_iff_of_injective _ Q.subtype_injective] at h
    rw [h, Subgroup.card_bot] at hle
    have := hq.one_lt
    omega
  have hYD : Y ≤ D := by
    rintro _ ⟨y, ⟨hyD, -⟩, rfl⟩
    exact hyD
  have hYcomm : ∀ y ∈ Y, ∀ x ∈ Q, x * y = y * x := by
    rintro _ ⟨y, ⟨-, hyc⟩, rfl⟩ x hx
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hyc ⟨x, hx⟩)
  have hRY : R ≤ Subgroup.normalizer (Y : Set G) := by
    refine le_normalizer_of_forall fun r hr y hy => ?_
    have hyD := hYD hy
    have hryD : r * y * r⁻¹ ∈ D := hDn.conj_mem y hyD r
    have hryQ : r * y * r⁻¹ ∈ Q := hDQ hryD
    refine ⟨⟨r * y * r⁻¹, hryQ⟩, ⟨hryD, ?_⟩, rfl⟩
    refine Subgroup.mem_center_iff.mpr fun x => ?_
    apply Subtype.ext
    change (x : G) * (r * y * r⁻¹) = r * y * r⁻¹ * x
    have hxQ : r⁻¹ * x * r ∈ Q := by
      simpa using hQn.conj_mem (x : G) x.2 r⁻¹
    have h1 := hYcomm y hy (r⁻¹ * x * r) hxQ
    calc (x : G) * (r * y * r⁻¹) = r * ((r⁻¹ * x * r) * y) * r⁻¹ := by group
      _ = r * (y * (r⁻¹ * x * r)) * r⁻¹ := by rw [h1]
      _ = r * y * r⁻¹ * x := by group
  have hYD' : Y = D := by
    rcases hirr Y (by rw [hΦ]; exact bot_le) hYD hRY with h | h
    · exact absurd (h.trans hΦ) hYne
    · exact h
  have hDQcomm : ∀ d ∈ D, ∀ x ∈ Q, x * d = d * x := by
    intro d hd x hx
    rw [← hYD'] at hd
    exact hYcomm d hd x hx
  obtain ⟨hWchar, hWiff, hWcomm, -⟩ := hPG2C ↥Q q hq hq2 hQp
  set Wq : Subgroup ↥Q :=
    Subgroup.closure {x : ↥Q | x ∈ Subgroup.upperCentralSeries ↥Q 2 ∧ x ^ q = 1} with hWq
  have : Wq.Characteristic := hWchar
  set W : Subgroup G := Wq.map Q.subtype with hW
  have hWn : W.Normal :=
    CFSG.LocalAnalysis.GorensteinLyons.map_subtype_normal_of_characteristic Q Wq
  have hWQ : W ≤ Q := Subgroup.map_subtype_le Wq
  have hWexp : ∀ x ∈ W, x ^ q = 1 := by
    rintro _ ⟨w, hw, rfl⟩
    have h := ((hWiff w).1 hw).2
    simpa using congrArg Subtype.val h
  have hWclass : ⁅⁅W, W⁆, W⁆ = ⊥ := by
    refine commutator_commutator_eq_bot_of_central hWQ ?_
    rintro _ ⟨w, hw, rfl⟩ g hg u hu
    have h1 := ((hWcomm w hw ⟨g, hg⟩).1)
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp h1 ⟨u, hu⟩)
  have hDW : D ≤ W := by
    intro d hd
    have hdQ := hDQ hd
    have hdc : (⟨d, hdQ⟩ : ↥Q) ∈ Subgroup.center ↥Q :=
      Subgroup.mem_center_iff.mpr fun x => Subtype.ext (hDQcomm d hd x x.2)
    have hd2 : (⟨d, hdQ⟩ : ↥Q) ∈ Subgroup.upperCentralSeries ↥Q 2 :=
      Subgroup.upperCentralSeries_mono ↥Q (by norm_num : 1 ≤ 2)
        (by rw [Subgroup.upperCentralSeries_one]; exact hdc)
    refine ⟨⟨d, hdQ⟩, (hWiff ⟨d, hdQ⟩).2 ⟨hd2, Subtype.ext (by simpa using hDexp d hd)⟩, rfl⟩
  have hRW : R ⊓ Subgroup.centralizer (W : Set G) = ⊥ := by
    rw [eq_bot_iff, ← hRD]
    exact inf_le_inf_left R (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hDW))
  have hrankW : ∀ r ∈ R, r ≠ 1 →
      CFSG.pRank q ↥(W ⊓ Subgroup.centralizer ({r} : Set G)) ≤ 2 := fun r hr hr1 =>
    (OddCore37.pRank_le_of_le hq (inf_le_inf_right _ hWQ)).trans (hrank r hr hr1)
  obtain ⟨-, -, hshape⟩ := fixedRankTwo_of_order_five hET32 hq hq2 hq5 hA hAR hR hR32 ha
    (sup_le (le_normalizer_of_normal R W) (le_normalizer_of_normal A W)) (hQp.to_le hWQ)
    hWexp hWclass hRW hrankW
  have hWD : W = D := by
    refine le_antisymm ?_ hDW
    rcases hshape with ⟨-, hc⟩ | ⟨-, hc, hcomm, hZ, -⟩
    · exact (Subgroup.eq_of_le_of_card_ge hDW (by rw [hc, hDcard])).ge
    · exfalso
      have hDle : D ≤ W ⊓ Subgroup.centralizer (W : Set G) := by
        intro d hd
        refine ⟨hDW hd, Subgroup.mem_centralizer_iff.2 fun w hw => ?_⟩
        exact hDQcomm d hd w (hWQ hw)
      have h1 := Subgroup.card_le_of_le hDle
      rw [hZ, hcomm, hDcard] at h1
      have h2 : q ^ 1 < q ^ 4 := Nat.pow_lt_pow_right hq.one_lt (by norm_num)
      rw [pow_one] at h2
      omega
  have hWqD : Wq = D.subgroupOf Q := by
    have h1 : W.subgroupOf Q = Wq := Subgroup.comap_map_eq_self_of_injective Q.subtype_injective Wq
    rw [← h1, hWD]
  have hD'el : IsElementaryAbelian q (D.subgroupOf Q) := by
    have := hDel
    exact IsElementaryAbelian.subgroupOf hDQ
  have hD'Z : D.subgroupOf Q ≤ Subgroup.center ↥Q := fun d hd =>
    Subgroup.mem_center_iff.mpr fun x => Subtype.ext (hDQcomm d hd x x.2)
  have hmax : ∀ B : Subgroup ↥Q, B.Normal → IsElementaryAbelian q B → D.subgroupOf Q ≤ B →
      B = D.subgroupOf Q := by
    intro B hBn hBel hDB
    by_contra hne
    have hlt : D.subgroupOf Q < B := lt_of_le_of_ne hDB (Ne.symm hne)
    obtain ⟨b, hbB, hbD, hbp, B', hB'n, hD'B', hB'B, hbB', hform, hcen⟩ :=
      CFSG.SectionRank.Ccomm.exists_central_extension hQp hlt
    have hB'W : B' ≤ Wq := by
      intro x hx
      refine (hWiff x).2 ⟨?_, ?_⟩
      · rw [show (2 : ℕ) = 1 + 1 from rfl, Subgroup.mem_upperCentralSeries_succ_iff]
        intro y
        rw [Subgroup.upperCentralSeries_one]
        exact hD'Z (hcen x hx y)
      · exact elemPow_eq_one_of_isElementaryAbelian x (hB'B hx)
    rw [hWqD] at hB'W
    exact hD'B'.not_ge hB'W
  have hcentral := (CFSG.RankThree.PGroups.maximal_normal_elementary_centralizer_torsion hq hq2
    hQp (E := D.subgroupOf Q) hD'el hmax).2
  refine omegaOne_eq_of_forall hDQ hDexp fun x hxQ hxq => ?_
  have hxc : (⟨x, hxQ⟩ : ↥Q) ∈ Subgroup.centralizer ((D.subgroupOf Q : Subgroup ↥Q) : Set ↥Q) := by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact (Subgroup.mem_center_iff.mp (hD'Z hd) ⟨x, hxQ⟩).symm
  exact hcentral ⟨x, hxQ⟩ hxc (Subtype.ext (by simpa using hxq))

end CFSG.RankThree.PartOne.Torsion37
