module

public import CFSG.Timmesfeld.Bridge.Asc72Triangle

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge

variable {G : Type*} [Group G] {D : Set G}

theorem not_firstKind (hN : IsNormalSet D) (hD : Asc72.IsOddTransp D)
    (hsolv : Group.IsSolvable G) {u w v : G} (h : Asc72.IsTriangle D u w v) :
    ¬ (Odd (orderOf (u * v * w)) ∧ 1 < orderOf (u * v * w)) := by
  rintro ⟨hodd, -⟩
  haveI : Group.IsSolvable G := hsolv
  have huvD : u * v ∈ D := h.mul_mem_of_odd hD hN hodd
  have hnc : ¬ Commute w (u * v) := h.not_commute_mul hD
  let K : Subgroup G := Subgroup.closure ({u, w, v} : Set G)
  have huK : u ∈ K := Subgroup.subset_closure (by simp)
  have hwK : w ∈ K := Subgroup.subset_closure (by simp)
  have hvK : v ∈ K := Subgroup.subset_closure (by simp)
  have huvK : u * v ∈ K := K.mul_mem huK hvK
  have hconj : ∀ {a b : G} (ha : a ∈ K) (hb : b ∈ K) (haD : a ∈ D) (hbD : b ∈ D),
      ¬ Commute a b → IsConj (⟨a, ha⟩ : K) (⟨b, hb⟩ : K) := by
    intro a b ha hb haD hbD hab
    obtain ⟨g, hg, hgab⟩ := hD.exists_conj haD hbD hab
    have hgK : g ∈ K := by
      have hle : Subgroup.closure ({a, b} : Set G) ≤ K := by
        rw [Subgroup.closure_le]
        intro x hx
        rcases hx with rfl | rfl
        · exact ha
        · exact hb
      exact hle hg
    exact isConj_iff.mpr ⟨⟨g, hgK⟩, Subtype.ext hgab⟩
  have huw : IsConj (⟨u, huK⟩ : K) (⟨w, hwK⟩ : K) :=
    hconj huK hwK h.1 h.2.2.1 h.2.2.2.2.2.1
  have hvw : IsConj (⟨v, hvK⟩ : K) (⟨w, hwK⟩ : K) :=
    hconj hvK hwK h.2.1 h.2.2.1 h.2.2.2.2.2.2
  have huvw : IsConj (⟨u * v, huvK⟩ : K) (⟨w, hwK⟩ : K) :=
    hconj huvK hwK huvD h.2.2.1 fun hc => hnc hc.symm
  have hab : ∀ {x y : K}, IsConj x y → Abelianization.of x = Abelianization.of y := by
    intro x y hxy
    obtain ⟨g, hg⟩ := isConj_iff.mp hxy
    rw [← hg, map_mul, map_mul, map_inv]
    exact (mul_inv_cancel_comm (a := Abelianization.of g) (b := Abelianization.of x)).symm
  let t : Abelianization K := Abelianization.of ⟨u, huK⟩
  have htw : Abelianization.of ⟨w, hwK⟩ = t := by
    rw [← hab huw]
  have htv : Abelianization.of ⟨v, hvK⟩ = t := (hab hvw).trans htw
  have htuv : Abelianization.of ⟨u * v, huvK⟩ = t := (hab huvw).trans htw
  have ht2 : t = t * t := by
    calc t = Abelianization.of ⟨u * v, huvK⟩ := htuv.symm
      _ = Abelianization.of (⟨u, huK⟩ * ⟨v, hvK⟩) := by
        rw [show (⟨u, huK⟩ * ⟨v, hvK⟩ : K) = ⟨u * v, huvK⟩ from rfl]
      _ = Abelianization.of ⟨u, huK⟩ * Abelianization.of ⟨v, hvK⟩ := map_mul _ _ _
      _ = t * t := by rw [show Abelianization.of ⟨u, huK⟩ = t from rfl, htv]
  have ht1 : t = 1 := by
    have h : t * t = 1 * t := by rw [one_mul, ← ht2]
    exact mul_right_cancel h
  have huC : (⟨u, huK⟩ : K) ∈ commutator K := by
    rw [← Abelianization.ker_of, MonoidHom.mem_ker,
      show Abelianization.of ⟨u, huK⟩ = t from rfl, ht1]
  have hwC : (⟨w, hwK⟩ : K) ∈ commutator K := by
    rw [← Abelianization.ker_of, MonoidHom.mem_ker, htw, ht1]
  have hvC : (⟨v, hvK⟩ : K) ∈ commutator K := by
    rw [← Abelianization.ker_of, MonoidHom.mem_ker, htv, ht1]
  have hpre : Subgroup.closure (((↑) : K → G) ⁻¹' ({u, w, v} : Set G)) = ⊤ :=
    Subgroup.closure_closure_coe_preimage
  have hle : (⊤ : Subgroup K) ≤ commutator K := by
    rw [← hpre]
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx
    · have hx' : x = ⟨u, huK⟩ := Subtype.ext hx
      rw [hx']
      exact huC
    · have hx' : x = ⟨w, hwK⟩ := Subtype.ext hx
      rw [hx']
      exact hwC
    · have hx' : x = ⟨v, hvK⟩ := Subtype.ext hx
      rw [hx']
      exact hvC
  have htop : commutator K = ⊤ := le_antisymm le_top hle
  haveI : Nontrivial K :=
    ⟨⟨⟨u, huK⟩, 1, fun h1 => hD.ne_one h.1 (congrArg Subtype.val h1)⟩⟩
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (G := K)).ne htop

theorem not_thirdKind (hN : IsNormalSet D) (hD : Asc72.IsOddTransp D)
    (hsolv : Group.IsSolvable G) {u w v : G} (h : Asc72.IsTriangle D u w v) :
    ¬ Asc72.IsThirdKind u w v := by
  rintro ⟨n, hn, hn1, hord⟩
  haveI : Group.IsSolvable G := hsolv
  obtain ⟨hzz, hz1, hzu, hzv, hzw, -⟩ := h.third_kind hD hN hn hord
  let z : G := (u * v * w) ^ n
  let X : Subgroup G := Subgroup.closure ({u, w, v} : Set G)
  have huX : u ∈ X := Subgroup.subset_closure (by simp)
  have hwX : w ∈ X := Subgroup.subset_closure (by simp)
  have hvX : v ∈ X := Subgroup.subset_closure (by simp)
  have hzX : z ∈ X := X.pow_mem (X.mul_mem (X.mul_mem huX hvX) hwX) n
  let zX : X := ⟨z, hzX⟩
  have hzX2 : zX * zX = 1 := Subtype.ext hzz
  have hzXpow : zX ^ 2 = 1 := by rw [pow_two]; exact hzX2
  have hzXne : zX ≠ 1 := fun h1 => hz1 (congrArg Subtype.val h1)
  have hzXord : orderOf zX = 2 := orderOf_eq_prime hzXpow hzXne
  have hcenter : ∀ (x : G) (hx : x ∈ X), Commute z x := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl | rfl
        · exact hzu
        · exact hzw
        · exact hzv
    | one => exact Commute.one_right z
    | mul x y _ _ ihx ihy => exact ihx.mul_right ihy
    | inv x _ ih => exact ih.inv_right
  have hcenterX : ∀ x : X, Commute zX x := fun x => Subtype.ext (hcenter x.1 x.2).eq
  let N : Subgroup X := Subgroup.zpowers zX
  have hNnormal : N.Normal := by
    refine ⟨fun a ha g => ?_⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ha
    rw [← hk]
    have hg : g * zX * g⁻¹ = zX := by
      have hc : Commute zX g := hcenterX g
      calc g * zX * g⁻¹ = zX * g * g⁻¹ := by rw [hc.eq]
        _ = zX := by rw [mul_assoc, mul_inv_cancel, mul_one]
    rw [← conj_zpow, hg]
    exact Subgroup.zpow_mem_zpowers zX k
  haveI : N.Normal := hNnormal
  have hmemN : ∀ d : X, d ∈ N → d = 1 ∨ d = zX := by
    intro d hd
    classical
    have hfin : IsOfFinOrder zX := isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by norm_num, hzXpow⟩
    have hd' := (hfin.mem_zpowers_iff_mem_range_orderOf (y := d)).mp hd
    rw [hzXord] at hd'
    simp only [Finset.mem_range, Finset.mem_image] at hd'
    obtain ⟨k, hk, rfl⟩ := hd'
    interval_cases k
    · left; simp
    · right; simp
  let DX : Set X := {x | (x : G) ∈ D ∧ (x : G) ≠ z}
  have huDX : (⟨u, huX⟩ : X) ∈ DX := by
    refine ⟨h.1, ?_⟩
    intro h1
    change u = z at h1
    exact h.2.2.2.2.2.1 (by rw [h1]; exact hzw)
  have hvDX : (⟨v, hvX⟩ : X) ∈ DX := by
    refine ⟨h.2.1, ?_⟩
    intro h1
    change v = z at h1
    exact h.2.2.2.2.2.2 (by rw [h1]; exact hzw)
  have hwDX : (⟨w, hwX⟩ : X) ∈ DX := by
    refine ⟨h.2.2.1, ?_⟩
    intro h1
    change w = z at h1
    exact h.2.2.2.2.2.1 (by rw [h1]; exact hzu.symm)
  have hDXnormal : IsNormalSet DX := by
    intro g x hx
    refine ⟨hN (g : G) (x : G) hx.1, fun hconj => hx.2 ?_⟩
    change (g : G) * (x : G) * (g : G)⁻¹ = z at hconj
    calc (x : G) = (g : G)⁻¹ * ((g : G) * (x : G) * (g : G)⁻¹) * (g : G) := by group
      _ = (g : G)⁻¹ * z * (g : G) := by rw [hconj]
      _ = z := by
        have hc : Commute z (g : G) := hcenter (g : G) g.2
        calc (g : G)⁻¹ * z * (g : G) = (g : G)⁻¹ * (z * (g : G)) := by rw [mul_assoc]
          _ = (g : G)⁻¹ * ((g : G) * z) := by rw [hc.eq]
          _ = z := by rw [← mul_assoc, inv_mul_cancel, one_mul]
  have hDXodd : Asc72.IsOddTransp DX :=
    (hD.preimage X).mono fun x hx => hx.1
  let Q := X ⧸ N
  let φ : X →* Q := QuotientGroup.mk' N
  let DQ : Set Q := φ '' DX
  have hDQnormal : IsNormalSet DQ :=
    isNormalSet_image hDXnormal φ (QuotientGroup.mk'_surjective N)
  have hφne : ∀ d ∈ DX, φ d ≠ 1 := by
    intro d hd h1
    have hdN : d ∈ N := (QuotientGroup.eq_one_iff d).mp h1
    rcases hmemN d hdN with h1 | h1
    · exact hDXodd.ne_one hd h1
    · exact hd.2 (congrArg Subtype.val h1)
  have hDQodd : Asc72.IsOddTransp DQ := hDXodd.image φ hφne
  have hsolvQ : Group.IsSolvable Q := inferInstance
  let uX : X := ⟨u, huX⟩
  let wX : X := ⟨w, hwX⟩
  let vX : X := ⟨v, hvX⟩
  let xX : X := uX * vX * wX
  have hxXn : xX ^ n = zX := Subtype.ext rfl
  have hxXord : orderOf xX = 2 * n := by
    change orderOf (⟨u * v * w, X.mul_mem (X.mul_mem huX hvX) hwX⟩ : X) = 2 * n
    rw [Subgroup.orderOf_mk, hord]
  let uQ : Q := φ uX
  let wQ : Q := φ wX
  let vQ : Q := φ vX
  have huDQ : uQ ∈ DQ := ⟨uX, huDX, rfl⟩
  have hvDQ : vQ ∈ DQ := ⟨vX, hvDX, rfl⟩
  have hwDQ : wQ ∈ DQ := ⟨wX, hwDX, rfl⟩
  have hNodd : ∀ y : X, y ∈ N → Odd (orderOf y) → y = 1 := by
    intro y hy hodd
    rcases hmemN y hy with h1 | h1
    · exact h1
    · rw [h1, hzXord] at hodd
      exact absurd hodd (by norm_num)
  have hnotComm : ∀ {a b : G} (ha : a ∈ X) (hb : b ∈ X) (haD : a ∈ D) (hbD : b ∈ D),
      ¬ Commute a b → ¬ Commute (φ ⟨a, ha⟩) (φ ⟨b, hb⟩) := by
    intro a b ha hb haD hbD hab hc
    have ha2 : (⟨a, ha⟩ : X) * ⟨a, ha⟩ = 1 := Subtype.ext (hD.mul_self_eq_one haD)
    have hb2 : (⟨b, hb⟩ : X) * ⟨b, hb⟩ = 1 := Subtype.ext (hD.mul_self_eq_one hbD)
    have hq : φ ((⟨a, ha⟩ : X) * ⟨b, hb⟩) = φ ((⟨b, hb⟩ : X) * ⟨a, ha⟩) := by
      rw [map_mul, map_mul]
      exact hc.eq
    have hmem : ((⟨a, ha⟩ : X) * ⟨b, hb⟩) / ((⟨b, hb⟩ : X) * ⟨a, ha⟩) ∈ N :=
      QuotientGroup.eq_iff_div_mem.mp hq
    have hdiv : ((⟨a, ha⟩ : X) * ⟨b, hb⟩) / ((⟨b, hb⟩ : X) * ⟨a, ha⟩) =
        ((⟨a, ha⟩ : X) * ⟨b, hb⟩) ^ 2 := by
      rw [div_eq_mul_inv, mul_inv_rev, inv_eq_of_mul_eq_one_right ha2,
        inv_eq_of_mul_eq_one_right hb2, pow_two]
    have hsq : ((⟨a, ha⟩ : X) * ⟨b, hb⟩) ^ 2 ∈ N := hdiv ▸ hmem
    have hodd : Odd (orderOf ((⟨a, ha⟩ : X) * ⟨b, hb⟩)) := by
      rw [show (⟨a, ha⟩ : X) * ⟨b, hb⟩ = ⟨a * b, X.mul_mem ha hb⟩ from rfl,
        Subgroup.orderOf_mk]
      exact hD.odd_of_not_commute haD hbD hab
    have hodd2 : Odd (orderOf (((⟨a, ha⟩ : X) * ⟨b, hb⟩) ^ 2)) :=
      Odd.of_dvd_nat hodd (orderOf_pow_dvd 2)
    have hsq1 : ((⟨a, ha⟩ : X) * ⟨b, hb⟩) ^ 2 = 1 := hNodd _ hsq hodd2
    exact hab (((commute_iff_mul_sq_eq_one ha2 hb2).mpr hsq1).map X.subtype)
  have htriQ : Asc72.IsTriangle DQ uQ wQ vQ := by
    refine ⟨huDQ, hvDQ, hwDQ, ?_, ?_, ?_, ?_⟩
    ·
      intro h1
      have hmem : uX / vX ∈ N := QuotientGroup.eq_iff_div_mem.mp h1
      have hv2 : vX * vX = 1 := Subtype.ext (hD.mul_self_eq_one h.2.1)
      have hmem' : uX * vX ∈ N := by
        rwa [div_eq_mul_inv, inv_eq_of_mul_eq_one_right hv2] at hmem
      rcases hmemN (uX * vX) hmem' with h1 | h1
      · have huv : uX = vX := by
          calc uX = uX * (vX * vX) := by rw [hv2, mul_one]
            _ = (uX * vX) * vX := by group
            _ = vX := by rw [h1, one_mul]
        exact h.2.2.2.1 (congrArg Subtype.val huv)
      · have hxw : xX = zX * wX := by
          change uX * vX * wX = zX * wX
          rw [h1]
        have hcw : Commute zX wX := hcenterX wX
        have hwX2 : wX * wX = 1 := Subtype.ext (hD.mul_self_eq_one h.2.2.1)
        have hzw2 : (zX * wX) ^ 2 = 1 := by
          rw [pow_two]
          calc zX * wX * (zX * wX) = zX * (wX * zX) * wX := by group
            _ = zX * (zX * wX) * wX := by rw [← hcw.eq]
            _ = zX * zX * wX * wX := by group
            _ = 1 := by rw [hzX2, one_mul, hwX2]
        have hle : orderOf (zX * wX) ≤ 2 := orderOf_le_of_pow_eq_one (by norm_num) hzw2
        have hxle : orderOf xX ≤ 2 := hxw ▸ hle
        rw [hxXord] at hxle
        omega
    · have huvX : Commute uX vX := Subtype.ext h.2.2.2.2.1.eq
      exact huvX.map φ
    · exact hnotComm huX hwX h.1 h.2.2.1 h.2.2.2.2.2.1
    · exact hnotComm hvX hwX h.2.1 h.2.2.1 h.2.2.2.2.2.2
  have hφxord : orderOf (φ xX) = n := by
    refine (orderOf_eq_iff hn.pos).mpr ⟨?_, ?_⟩
    · rw [← map_pow, hxXn]
      exact (QuotientGroup.eq_one_iff zX).mpr (Subgroup.mem_zpowers zX)
    · intro m hm hpos h1
      have h1' : φ (xX ^ m) = 1 := by rw [← map_pow] at h1; exact h1
      have hmem : xX ^ m ∈ N := (QuotientGroup.eq_one_iff _).mp h1'
      rcases hmemN (xX ^ m) hmem with hx1 | hxz
      · exact pow_ne_one_of_lt_orderOf (by omega) (by rw [hxXord]; omega) hx1
      · have hmn : m = n := by
          have hmod : m ≡ n [MOD orderOf xX] :=
            (pow_eq_pow_iff_modEq (x := xX)).mp (by rw [hxz, hxXn])
          rw [hxXord] at hmod
          exact hmod.eq_of_lt_of_lt (by omega) (by omega)
        omega
  have hprodQ : uQ * vQ * wQ = φ xX := by
    rw [show uQ * vQ * wQ = φ (uX * vX * wX) from by rw [map_mul, map_mul]]
  exact not_firstKind hDQnormal hDQodd hsolvQ htriQ
    ⟨hprodQ ▸ (hφxord ▸ hn), hprodQ ▸ (hφxord ▸ hn1)⟩

theorem triangle_secondKind_of_solvable {G : Type} [Group G] [Finite G] {D : Set G}
    (hN : IsNormalSet D) (hodd : Asc72.IsOddTransp D)
    (hgen : Subgroup.closure D = ⊤) (hsolv : Group.IsSolvable G)
    {u w v : G} (h : Asc72.IsTriangle D u w v) :
    orderOf (u * v * w) = 4 := by
  rcases h.orderOf_cases hodd hN with ⟨hoddord, h1⟩ | h4 | h3
  · exact absurd ⟨hoddord, h1⟩ (not_firstKind hN hodd hsolv h)
  · exact h4
  · exact absurd h3 (not_thirdKind hN hodd hsolv h)

end CFSG.OddTranspositions
