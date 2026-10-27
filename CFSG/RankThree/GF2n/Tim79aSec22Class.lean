module

public import CFSG.RankThree.GF2n.Tim79aSec22Min
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.GF2n.Tim79aSec2Root

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G] {M V Q P H : Subgroup G} [Finite G]

namespace MinCex

variable (hc : MinCex M V Q P H)
include hc

theorem dbarOf_exists_odd_partner :
    ∀ a ∈ dbarOf V H, ∃ c ∈ dbarOf V H, Odd (orderOf (a * c)) ∧ a * c ≠ 1 := by
  intro a ha
  obtain ⟨y, hy, hodd, h1⟩ := CFSG.Timmesfeld.exists_odd_partner_of_not_mem_pCoreOf
    (Y := barOf V H (xOf V H)) hc.dbarOf_isRootInvolutionSet hc.dbarOf_subset_barOf_xOf
    (fun y _ x hx => hc.conj_mem_dbarOf hx) ha (hc.dbarOf_not_mem_pCoreOf a ha)
  exact ⟨y * a * y⁻¹, hc.conj_mem_dbarOf ha, hodd, h1⟩

theorem barOf_V_conj {a b : Hbar V H} (ha : a ∈ barOf V H V) (hb : b ∈ barOf V H V)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    ∃ x ∈ barOf V H (xOf V H), x * a * x⁻¹ = b := by
  by_cases hab : a = b
  · exact ⟨1, Subgroup.one_mem _, by rw [hab]; group⟩
  have hVb : IsElemAbelian 2 (barOf V H V) := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨v, hv, hvx⟩ := mem_barOf_iff.mp x.2
      obtain ⟨w, hw, hwy⟩ := mem_barOf_iff.mp y.2
      apply Subtype.ext
      show (x : Hbar V H) * y = y * x
      rw [← hvx, ← hwy, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (congrArg (Subtype.val : ↥V → G) (hc.elemAb.1.is_comm.comm ⟨v, hv⟩ ⟨w, hw⟩))
    · obtain ⟨v, hv, rfl⟩ := mem_barOf_iff.mp hx
      rw [← map_pow]
      have : v ^ 2 = 1 := Subtype.ext (hc.elemAb.2 _ hv)
      rw [this, map_one]
  have hcomm : a * b = b * a :=
    congrArg Subtype.val (hVb.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hab1 : a * b ≠ 1 := by
    intro h
    apply hab
    have h2 : b = a⁻¹ := by
      calc b = a⁻¹ * (a * b) := by group
        _ = a⁻¹ := by rw [h, mul_one]
    rw [h2]
    have : a ^ 2 = 1 := hVb.2 a ha
    exact (inv_eq_of_mul_eq_one_right (by rw [← sq]; exact this)).symm
  exact CFSG.Timmesfeld.exists_conj_of_commuting_pair_sub (Y := barOf V H (xOf V H))
    hc.dbarOf_isRootInvolutionSet hc.dbarOf_subset_barOf_xOf
    (fun y _ x hx => hc.conj_mem_dbarOf hx) hc.dbarOf_exists_odd_partner
    (hc.barOf_V_subset_dbarOf ha ha1) (hc.barOf_V_subset_dbarOf hb hb1) hab hcomm
    (hc.barOf_V_subset_dbarOf ((barOf V H V).mul_mem ha hb) hab1)

theorem dbarOf_isClass : ∃ d₀ ∈ dbarOf V H, ∀ y : Hbar V H,
    y ∈ dbarOf V H ↔ ∃ x ∈ barOf V H (xOf V H), y = x * d₀ * x⁻¹ := by
  obtain ⟨d, hdV, hdW⟩ := SetLike.not_le_iff_exists.mp hc.not_V_le_wOf
  have hdH : d ∈ H := hc.V_le_H hdV
  have hd1 : piBar V H ⟨d, hdH⟩ ≠ 1 := fun h => hdW ((piBar_eq_one_iff _).1 h)
  have hd0 : piBar V H ⟨d, hdH⟩ ∈ dbarOf V H :=
    hc.barOf_V_subset_dbarOf (mem_barOf_iff.mpr ⟨⟨d, hdH⟩, hdV, rfl⟩) hd1
  refine ⟨piBar V H ⟨d, hdH⟩, hd0, fun y => ⟨fun hy => ?_, ?_⟩⟩
  · obtain ⟨e, ⟨he1, U, hU, heU⟩, heW, rfl⟩ := mem_dbarOf_iff.mp hy
    obtain ⟨g, hg, rfl⟩ := hU
    obtain ⟨x, hx, hgx⟩ := hc.exists_conj_xOf hg
    rw [hgx] at heU
    have hxH : x ∈ H := xOf_le_H hc.V_le_H hx
    set v : G := x⁻¹ * (e : G) * x with hv
    have hvV : v ∈ V := mem_conjSubgroup.mp heU
    have hvH : v ∈ H := hc.V_le_H hvV
    have hvW : v ∉ wOf V H := fun h => heW (by
      have := (Subgroup.mem_normalizer_iff.mp (H_le_normalizer_wOf V H hxH) v).mp h
      rwa [show x * v * x⁻¹ = e by rw [hv]; group] at this)
    have hv1 : piBar V H ⟨v, hvH⟩ ≠ 1 := fun h => hvW ((piBar_eq_one_iff _).1 h)
    obtain ⟨z, hz, hzv⟩ := hc.barOf_V_conj (mem_barOf_iff.mpr ⟨⟨d, hdH⟩, hdV, rfl⟩)
      (mem_barOf_iff.mpr ⟨⟨v, hvH⟩, hvV, rfl⟩) hd1 hv1
    have hxb : piBar V H ⟨x, hxH⟩ ∈ barOf V H (xOf V H) := mem_barOf_iff.mpr ⟨⟨x, hxH⟩, hx, rfl⟩
    refine ⟨piBar V H ⟨x, hxH⟩ * z, (barOf V H (xOf V H)).mul_mem hxb hz, ?_⟩
    have e1 : (e : G) = x * v * x⁻¹ := by rw [hv]; group
    have e2 : e = ⟨x, hxH⟩ * ⟨v, hvH⟩ * ⟨x, hxH⟩⁻¹ := Subtype.ext (by simpa using e1)
    rw [e2, map_mul, map_mul, map_inv, ← hzv]
    group
  · rintro ⟨x, -, rfl⟩
    exact hc.conj_mem_dbarOf (y := x) hd0

end MinCex

end CFSG.RankThree.GF2n.Tim79a
