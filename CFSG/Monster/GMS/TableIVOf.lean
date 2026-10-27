module

public import CFSG.Monster.GMS.BabyCover
public import CFSG.Monster.GMS.Facts.TableIV

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

section Main

variable {G : Type} [Group G]

theorem IsBabyCover.babyInv_zero_of_isTwoACls [Finite G] {a : G}
    {φ : Subgroup.centralizer ({a} : Set G) →* B} (h : IsBabyCover a φ) (hT3 : BabyTableIII)
    {b z u : G} (hV : TableV a b z u) {x : G} (hx : x ∈ Subgroup.centralizer ({a} : Set G))
    (hxb : IsTwoACls a b x) : BabyInv 0 (coverMap φ x) := by
  have hb0 := (h.babyInv_zero_of_tableV hT3 hV).1
  obtain ⟨g, hg, hgx⟩ := hxb
  have himg : coverMap φ (g * x * g⁻¹) = coverMap φ g * coverMap φ x * (coverMap φ g)⁻¹ :=
    coverMap_conj hg hx
  have hbC : b ∈ Subgroup.centralizer ({a} : Set G) := hV.1
  have hconj : IsConj (coverMap φ x) (coverMap φ b) := by
    rcases hgx with hgx | hgx
    · rw [hgx] at himg
      exact isConj_iff.mpr ⟨coverMap φ g, himg.symm⟩
    · rw [hgx, h.coverMap_mul_b hbC] at himg
      exact isConj_iff.mpr ⟨coverMap φ g, himg.symm⟩
  exact hb0.of_isConj hconj.symm

private theorem orderOf_mul_dvd_two {H : Type*} [Group H] {r s : H} (hr : orderOf r = 2)
    (hs : orderOf s = 2) (hrs : r * s = s * r) : orderOf (r * s) ∣ 2 := by
  have hr' : r * r = 1 := mul_self_eq_one_of_orderOf hr
  have hs' : s * s = 1 := mul_self_eq_one_of_orderOf hs
  apply orderOf_dvd_of_pow_eq_one
  rw [pow_two]
  calc r * s * (r * s) = r * r * (s * s) := by
        rw [mul_assoc, ← mul_assoc s r s, ← hrs, mul_assoc, mul_assoc]
    _ = 1 := by rw [hr', hs', one_mul]

theorem tableIVProduct_of [Finite G] (hT3 : BabyTableIII) (hT4 : BabyTableIV) {a b z u : G}
    (ha : IsTwoBabyCentralizer a) (hV : TableV a b z u) : TableIVProduct a b := by
  obtain ⟨φ, h⟩ := ha.exists_cover
  intro x hx y hy hxb hyb hxy hne hne' hxyb
  have hr := h.babyInv_zero_of_isTwoACls hT3 hV hx hxb
  have hs := h.babyInv_zero_of_isTwoACls hT3 hV hy hyb
  have hrs0 := h.babyInv_zero_of_isTwoACls hT3 hV (Subgroup.mul_mem _ hx hy) hxyb
  have hmul : coverMap φ (x * y) = coverMap φ x * coverMap φ y := coverMap_mul hx hy
  have hcomm : coverMap φ x * coverMap φ y = coverMap φ y * coverMap φ x := by
    rw [← coverMap_mul hx hy, ← coverMap_mul hy hx, hxy]
  have hsr : coverMap φ y ≠ coverMap φ x := by
    intro heq
    rcases (h.coverMap_eq_iff hx hy).mp heq.symm with h1 | h1
    · exact hne h1.symm
    · exact hne' (by rw [h1, ← mul_assoc, h.mul_self_b, one_mul])
  obtain ⟨k, hk⟩ := (hT4 _ hr).1 _ hs hsr
  have hdvd := orderOf_mul_dvd_two hr.1 hs.1 hcomm
  rw [← hmul] at hdvd
  match k, hk with
  | 0, hk =>
    rw [BabyOrbit, ← hmul] at hk
    exact absurd (BabyInv.unique hrs0 hk) (by decide)
  | 1, hk =>
    rw [BabyOrbit, ← hmul] at hk
    exact absurd (BabyInv.unique hrs0 hk) (by decide)
  | 2, hk =>
    rw [BabyOrbit, ← hmul] at hk
    rw [hk] at hdvd
    exact absurd hdvd (by decide)
  | 3, hk =>
    rw [BabyOrbit, ← hmul] at hk
    rw [hk.1] at hdvd
    exact absurd hdvd (by decide)

end Main

theorem tableIVStatement_of (hT3 : BabyTableIII) (hT4 : BabyTableIV) : TableIVStatement :=
  fun _ _ _ _ _ _ _ ha hV => tableIVProduct_of hT3 hT4 ha hV

theorem tableIVIn_of {G : Type} [Group G] [Finite G] (hT3 : BabyTableIII) (hT4 : BabyTableIV) :
    TableIVIn G :=
  (tableIVStatement_of hT3 hT4).inG

end CFSG.Monster.GMS
