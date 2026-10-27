module

public import CFSG.OddTranspositions.PartFour.LineFibres
public import CFSG.OddTranspositions.PartThree.EightSeven
public import CFSG.OddTranspositions.PartTwoSec6
public import CFSG.OddTranspositions.PartFour.LineSpan
public import CFSG.OddTranspositions.PartFour.SeventeenTwo

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] [Finite G] {D : Set G}

abbrev blockImage (hC : HypothesisC D) (γ : Set G) :
    Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) :=
  QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) ''
    {c : Halpha D hC.alpha | (c : G) ∈ γ}

theorem mem_perp_of_commute (hC : HypothesisC D) {δ ε : Set G}
    (hδ : δ ∈ blockClass hC.alpha) (hε : ε ∈ blockClass hC.alpha) {d e : G} (hd : d ∈ δ)
    (he : e ∈ ε) (hde : Commute d e) : ε ∈ perp D δ := by
  by_cases hEq : δ = ε
  · rw [hEq]
    exact mem_perp_iff.mpr (Or.inr rfl)
  · exact mem_perp_iff.mpr (Or.inl
      (PartThree.mem_Dalpha_of_commute_mem hC.setup.normal hC.setup.oddT hC.isBlock_alpha hδ hε hEq
        hd he hde))

theorem mk_mul_eq_one_of_not_commute (hC : HypothesisC D)
    {d v : Halpha D hC.alpha} (hd : d ∈ DstarH hC) (hv : v ∈ DstarH hC)
    (hdv : Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) d)
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) v))
    (hnc : ¬ Commute d v) :
    QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) (d * v) = 1 := by
  let H := Halpha D hC.alpha
  let R := CFSG.solvableRadical H
  let mk := QuotientGroup.mk' R
  have hodd := (DstarH_isOddTransp hC).odd_of_not_commute hd hv hnc
  have hd2 : d * d = 1 := by
    rw [← pow_two, ← (DstarH_isOddTransp hC).1 d hd]
    exact pow_orderOf_eq_one d
  have hv2 : v * v = 1 := by
    rw [← pow_two, ← (DstarH_isOddTransp hC).1 v hv]
    exact pow_orderOf_eq_one v
  have hmd2 : (mk d) ^ 2 = 1 := by rw [pow_two, ← map_mul, hd2, map_one]
  have hmv2 : (mk v) ^ 2 = 1 := by rw [pow_two, ← map_mul, hv2, map_one]
  have hsq : (mk (d * v)) ^ 2 = 1 := by
    rw [map_mul, hdv.mul_pow 2, hmd2, hmv2, one_mul]
  have hdvd2 : orderOf (mk (d * v)) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  have himgodd : Odd (orderOf (mk (d * v))) :=
    hodd.of_dvd_nat (orderOf_map_dvd mk (d * v))
  have himg1 : mk (d * v) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h1 | h2
    · exact orderOf_eq_one_iff.mp h1
    · rw [h2] at himgodd
      exact absurd himgodd (by simp [Nat.not_odd_iff_even])
  exact himg1

theorem commute_of_commute_mk (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    {d v : Halpha D hC.alpha} (hd : d ∈ DstarH hC) (hv : v ∈ DstarH hC)
    (hdv : Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) d)
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) v)) :
    Commute d v := by
  let H := Halpha D hC.alpha
  let R := CFSG.solvableRadical H
  let mk := QuotientGroup.mk' R
  by_contra hnc
  have himg1 : mk (d * v) = 1 := mk_mul_eq_one_of_not_commute hC hd hv hdv hnc
  have hodd := (DstarH_isOddTransp hC).odd_of_not_commute hd hv hnc
  have hd2 : d * d = 1 := by
    rw [← pow_two, ← (DstarH_isOddTransp hC).1 d hd]
    exact pow_orderOf_eq_one d
  have hv2 : v * v = 1 := by
    rw [← pow_two, ← (DstarH_isOddTransp hC).1 v hv]
    exact pow_orderOf_eq_one v
  have hmemR : d * v ∈ R := (QuotientGroup.eq_one_iff (d * v)).mp himg1
  have hdinv : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd2
  have hbcR : d⁻¹ * v ∈ R := by simpa [hdinv] using hmemR
  have hvdQ : v * d⁻¹ ∈ CFSG.pCore 2 H :=
    mul_inv_mem_pCore_of_inv_mul_mem h113 hC hrad hn3 hd hv hbcR
  have hvdQ' : v * d ∈ CFSG.pCore 2 H := by simpa [hdinv] using hvdQ
  have hvdinv : v * d = (d * v)⁻¹ := by
    rw [mul_inv_rev, hdinv, inv_eq_of_mul_eq_one_right hv2]
  have hoddvd : Odd (orderOf (v * d)) := by
    rw [hvdinv, orderOf_inv]
    exact hodd
  have hvd1 : v * d = 1 :=
    CFSG.Timmesfeld.Bridge.OddTransp.eq_one_of_isPGroup_of_odd
      (CFSG.pCore_isPGroup (G := H) (p := 2)) hvdQ' hoddvd
  have hveq : v = d := by
    have h1 : v = d⁻¹ := eq_inv_of_mul_eq_one_left hvd1
    simpa [hdinv] using h1
  rw [hveq] at hnc
  exact hnc (Commute.refl d)

theorem perpMem_mk_subset (h89 : PartThree.Lemma8_9) (h113 : PartThree.Theorem11_3)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {β γ : Set G} (hβ : β ∈ Dalpha D hC.alpha) (hγ : γ ∈ blockLine D hC.alpha β)
    (hγα : γ ≠ hC.alpha) {b c : Halpha D hC.alpha} (hb : (b : G) ∈ β) (hc : (c : G) ∈ γ) :
    perpMem (imageClass hC) (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b) ⊆
      perpMem (imageClass hC) (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c) := by
  rintro w hw
  rw [mem_perpMem] at hw
  obtain ⟨d, hd, rfl⟩ := hw.1
  have hbStar : b ∈ DstarH hC := ⟨β, hβ, hb⟩
  have hcomm : Commute d b :=
    commute_of_commute_mk h113 hC hrad hn3 hd hbStar hw.2
  have hcommG : Commute (d : G) (b : G) := hcomm.map (Subgroup.subtype _)
  obtain ⟨δ, hδD, hdδ⟩ := (mem_DalphaStar_iff.mp ((mem_DstarH_iff hC).mp hd))
  have hγD : γ ∈ Dalpha D hC.alpha :=
    mem_Dalpha_of_mem_blockLine hC.isBlock_alpha.1 hβ hγ hγα
  have hδperpβ : δ ∈ perp D β :=
    mem_perp_of_commute hC hβ.1 hδD.1 hb hdδ hcommG.symm
  have hδperpα : δ ∈ perp D hC.alpha := mem_perp_iff.mpr (Or.inl hδD)
  have hγperpδ : γ ∈ perp D δ := hγ.2 δ ⟨hδperpα, hδperpβ⟩
  have hdcG : Commute (d : G) (c : G) := by
    rcases mem_perp_iff.mp hγperpδ with hγDδ | hγδ
    · exact (mem_Dalpha_iff.mp hγDδ).2.2.2 d hdδ c hc
    · exact commute_of_mem_Dalpha h89 h113 hC hrad hW hn3 hMZ hδD hdδ (hγδ ▸ hc)
  have hdc : Commute d c := Subtype.ext hdcG.eq
  exact ⟨⟨d, hd, rfl⟩, hdc.map (QuotientGroup.mk' _)⟩

theorem blockImage_subset_Vmem (h89 : PartThree.Lemma8_9) (h113 : PartThree.Theorem11_3)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {β γ : Set G} (hβ : β ∈ Dalpha D hC.alpha) (hγ : γ ∈ blockLine D hC.alpha β)
    (hγα : γ ≠ hC.alpha) {b : Halpha D hC.alpha} (hb : (b : G) ∈ β) :
    blockImage hC γ ⊆
      Vmem (imageClass hC) (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b) := by
  rintro s ⟨c, hcγ, rfl⟩
  have hγD : γ ∈ Dalpha D hC.alpha :=
    mem_Dalpha_of_mem_blockLine hC.isBlock_alpha.1 hβ hγ hγα
  have hcStar : c ∈ DstarH hC := ⟨γ, hγD, hcγ⟩
  have hbStar : b ∈ DstarH hC := ⟨β, hβ, hb⟩
  refine mem_Vmem.mpr ⟨⟨c, hcStar, rfl⟩, ?_⟩
  refine Set.Subset.antisymm ?_ ?_
  · have hβline : β ∈ blockLine D hC.alpha γ := by
      rw [blockLine_eq_of_mem hC hβ hγD hγ]
      exact right_mem_blockLine hβ.1 hβ.2.1
    exact perpMem_mk_subset h89 h113 hC hrad hW hn3 hMZ hγD hβline hβ.2.2.1 hcγ hb
  · exact perpMem_mk_subset h89 h113 hC hrad hW hn3 hMZ hβ hγ hγα hb hcγ

theorem mem_blockLine_of_mk_mem_Vmem (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {β ε : Set G} (hβ : β ∈ Dalpha D hC.alpha) (hε : ε ∈ Dalpha D hC.alpha)
    {b e : Halpha D hC.alpha} (hb : (b : G) ∈ β) (he : (e : G) ∈ ε)
    (hv : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) e ∈
      Vmem (imageClass hC) (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b)) :
    ε ∈ blockLine D hC.alpha β := by
  have heStar : e ∈ DstarH hC := ⟨ε, hε, he⟩
  refine ⟨hε.1, fun δ hδ => ?_⟩
  by_cases hδα : δ = hC.alpha
  · rw [hδα]
    exact mem_perp_iff.mpr (Or.inl hε)
  have hδD : δ ∈ Dalpha D hC.alpha := (mem_perp_iff.mp hδ.1).resolve_right hδα
  obtain ⟨d, hdδ⟩ := nonempty_of_mem_blockClass hC.isBlock_alpha.nonempty hδD.1
  let dH : Halpha D hC.alpha := ⟨d, Subgroup.subset_closure ⟨δ, hδD, hdδ⟩⟩
  have hdH : dH ∈ DstarH hC := ⟨δ, hδD, hdδ⟩
  have hcommdb : Commute d (b : G) := by
    rcases mem_perp_iff.mp hδ.2 with hδDβ | hδβ
    · exact ((mem_Dalpha_iff.mp hδDβ).2.2.2 (b : G) hb d hdδ).symm
    · exact commute_of_mem_Dalpha h89 h113 hC hrad hW hn3 hMZ hδD hdδ (hδβ ▸ hb)
  have hdb : Commute dH b := Subtype.ext hcommdb.eq
  have hmkdH : QuotientGroup.mk' _ dH ∈ perpMem (imageClass hC) (QuotientGroup.mk' _ e) := by
    rw [hv.2]
    exact ⟨⟨dH, hdH, rfl⟩, hdb.map (QuotientGroup.mk' _)⟩
  have hcommH : Commute dH e := commute_of_commute_mk h113 hC hrad hn3 hdH heStar hmkdH.2
  exact mem_perp_of_commute hC hδD.1 hε.1 hdδ he (hcommH.map (Subgroup.subtype _))

theorem exists_mem_blockLine_of_mem_Vmem (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) {b : Halpha D hC.alpha} (hb : (b : G) ∈ β)
    {v : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hv : v ∈
      Vmem (imageClass hC) (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b)) :
    ∃ ε ∈ blockLine D hC.alpha β, ε ≠ hC.alpha ∧ v ∈ blockImage hC ε := by
  obtain ⟨⟨v₀, hv₀, rfl⟩, -⟩ := id hv
  obtain ⟨ε, hε, hv₀ε⟩ := mem_DalphaStar_iff.mp ((mem_DstarH_iff hC).mp hv₀)
  exact ⟨ε, mem_blockLine_of_mk_mem_Vmem h89 h113 hC hrad hW hn3 hMZ hβ hε hb hv₀ε hv,
    hε.2.2.1, ⟨v₀, hv₀ε, rfl⟩⟩

theorem iUnion_blockImage_eq_Vmem (h89 : PartThree.Lemma8_9) (h113 : PartThree.Theorem11_3)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) {b : Halpha D hC.alpha} (hb : (b : G) ∈ β) :
    ⋃ γ ∈ blockLine D hC.alpha β \ {hC.alpha}, blockImage hC γ =
      Vmem (imageClass hC) (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b) := by
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    obtain ⟨γ, hγ, hxγ⟩ := Set.mem_iUnion₂.mp hx
    exact blockImage_subset_Vmem h89 h113 hC hrad hW hn3 hMZ hβ hγ.1
      (by simpa using hγ.2) hb hxγ
  · intro x hx
    obtain ⟨ε, hε, hεα, hxε⟩ :=
      exists_mem_blockLine_of_mem_Vmem h89 h113 hC hrad hW hn3 hMZ hβ hb hx
    exact Set.mem_iUnion₂.mpr ⟨ε, ⟨hε, by simpa using hεα⟩, hxε⟩

end CFSG.OddTranspositions.PartFour
