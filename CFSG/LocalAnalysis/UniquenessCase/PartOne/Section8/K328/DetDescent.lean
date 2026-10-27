module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.DetDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC6K332Lists
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Cover
import CFSG.CGT.PushingUpLit.CGT6.SixFourPrinted
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67SmallK
import CFSG.CGT.T75P.SylowSplit
import CFSG.LocalAnalysis.UniquenessCase.UC6K332K33Inj

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSpor)
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover K33)
open CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route (K33Models K34Models)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82 (K34odd)
open scoped commutatorElement

private theorem k328dds_isQuasisimple_of_open {Q : Type} [Group Q]
    (h : CFSG.Open.IsQuasisimple Q) : CFSG.IsQuasisimple Q := by
  refine ⟨⟨h.1⟩, h.2, ?_⟩
  by_contra hcon
  push Not at hcon
  have hsimple := h.2
  have hle : commutator Q ≤ Subgroup.center Q := by
    rw [commutator, Subgroup.commutator_le]
    intro x _ y _
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact hcon _ _
  have htop : (⊤ : Subgroup Q) ≤ Subgroup.center Q := h.1 ▸ hle
  obtain ⟨a, ha⟩ := (nontrivial_iff_exists_ne (1 : Q ⧸ Subgroup.center Q)).mp
    hsimple.toNontrivial
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  exact ha ((QuotientGroup.eq_one_iff x).mpr (htop (Subgroup.mem_top x)))

private theorem k328dds_mul_center_mul_inv {K : Type} [Group K] {c : K}
    (hc : c ∈ Subgroup.center K) (g : K) : g * c * g⁻¹ = c := by
  rw [Subgroup.mem_center_iff] at hc
  rw [hc g]
  group

private theorem k328dds_commutator_quotient_center {K : Type} [Group K]
    (h : commutator K = ⊤) : commutator (K ⧸ Subgroup.center K) = ⊤ := by
  have hcomm : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤ := by simpa [commutator] using h
  have h1 := Subgroup.map_commutator (⊤ : Subgroup K) ⊤
    (QuotientGroup.mk' (Subgroup.center K))
  rw [hcomm, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h1
  rw [commutator]
  exact h1.symm

private theorem k328dds_center_eq_bot_of_perfect_of_simple {S : Type} [Group S]
    (hperf : commutator S = ⊤) (hsimple : IsSimpleGroup S) :
    Subgroup.center S = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
  · exact h
  · exfalso
    have hbot : commutator S = ⊥ := by
      rw [commutator]
      exact Subgroup.commutator_top_right_eq_bot_iff_le_center.mpr h.ge
    have htb : (⊤ : Subgroup S) = ⊥ := by rw [← hperf, hbot]
    obtain ⟨a, b, hab⟩ := hsimple.toNontrivial.exists_pair_ne
    have ha1 : a = 1 := by
      have : a ∈ (⊥ : Subgroup S) := by rw [← htb]; exact Subgroup.mem_top a
      simpa using this
    have hb1 : b = 1 := by
      have : b ∈ (⊥ : Subgroup S) := by rw [← htb]; exact Subgroup.mem_top b
      simpa using this
    exact hab (ha1.trans hb1.symm)

private theorem k328dds_Z_eq_center {K : Type} [Group K] [Finite K] {Z X : Subgroup K}
    (hZ : Nat.card Z = 3) (hZX : Z ≤ X) (hXC : X ≤ Subgroup.centralizer (Z : Set K))
    (hcen : Nat.card (Subgroup.center ↥X) = 3) :
    Z = (Subgroup.center ↥X).map X.subtype := by
  have hsub_le : Z.subgroupOf X ≤ Subgroup.center ↥X := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (hXC y.2) (z : K) hz).symm
  have hcard_sub : Nat.card (Z.subgroupOf X) = 3 := by
    rw [card_subgroupOf_of_le hZX, hZ]
  have heq : Z.subgroupOf X = Subgroup.center ↥X :=
    Subgroup.eq_of_le_of_card_ge hsub_le (by rw [hcen, hcard_sub])
  rw [← heq, Subgroup.map_subgroupOf_eq_of_le hZX]

private theorem k328dds_Z_inf_center {K : Type} [Group K] [Finite K] {Z X : Subgroup K}
    (hq : CFSG.Open.IsQuasisimple K) (hperfX : commutator ↥X = ⊤) (hZ : Nat.card Z = 3)
    (hZX : Z ≤ X) (hXC : X ≤ Subgroup.centralizer (Z : Set K))
    (hsub : (X.subgroupOf (Subgroup.centralizer (Z : Set K))).IsSubnormal)
    (hX : X ≠ ⊤) : Z ⊓ Subgroup.center K = ⊥ := by
  by_contra hne
  have hlt : 1 < Nat.card ↥(Z ⊓ Subgroup.center K) :=
    (Subgroup.one_lt_card_iff_ne_bot (H := Z ⊓ Subgroup.center K)).mpr hne
  have hdiv : Nat.card ↥(Z ⊓ Subgroup.center K) ∣ 3 := by
    have := Subgroup.card_dvd_of_le (inf_le_left : Z ⊓ Subgroup.center K ≤ Z)
    rwa [hZ] at this
  have hcard : Nat.card ↥(Z ⊓ Subgroup.center K) = 3 := by
    rcases Nat.prime_three.eq_one_or_self_of_dvd _ hdiv with h1 | h3
    · omega
    · exact h3
  have heq : Z ⊓ Subgroup.center K = Z :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hZ, hcard])
  have hZle : Z ≤ Subgroup.center K := heq ▸ inf_le_right
  have hCtop : Subgroup.centralizer (Z : Set K) = ⊤ :=
    Subgroup.centralizer_eq_top_iff_subset.mpr (by simpa using hZle)
  have hXsub : X.IsSubnormal :=
    Subgroup.IsSubnormal.trans hXC hsub (hCtop ▸ Subgroup.IsSubnormal.top)
  have hQ : CFSG.IsQuasisimple K := k328dds_isQuasisimple_of_open hq
  rcases CFSG.CGT.PushingUpLit.CGT6.isSubnormal_le_center_or_eq_top_of_quasisimple hQ hXsub with
    hXle | hXtop
  · exfalso
    have hcomm_le : commutator ↥X ≤ ⊥ := by
      rw [commutator]
      refine Subgroup.commutator_le.mpr ?_
      intro a _ b _
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact Subtype.ext (Subgroup.mem_center_iff.1 (hXle a.2) (b : K)).symm
    have htopbot : (⊤ : Subgroup ↥X) = ⊥ := by
      rw [← hperfX, commutator]
      exact le_bot_iff.mp hcomm_le
    have hcardX : Nat.card ↥X ≤ 1 := by
      rw [← Nat.card_congr (Subgroup.topEquiv (G := ↥X)).toEquiv]
      exact (Subgroup.card_le_one_iff_eq_bot (H := ⊤)).mpr htopbot
    have hle : Nat.card Z ≤ Nat.card ↥X := Subgroup.card_le_of_le hZX
    omega
  · exact hX hXtop

private theorem k328dds_X_inf_center {K : Type} [Group K] {Z X : Subgroup K}
    (hZc : Z = (Subgroup.center ↥X).map X.subtype)
    (hZd : Z ⊓ Subgroup.center K = ⊥) : X ⊓ Subgroup.center K = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hxX : x ∈ X := (Subgroup.mem_inf.1 hx).1
  have hxZ : x ∈ Subgroup.center K := (Subgroup.mem_inf.1 hx).2
  have hxcen : (⟨x, hxX⟩ : ↥X) ∈ Subgroup.center ↥X := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.1 hxZ (y : K))
  have hxmap : x ∈ (Subgroup.center ↥X).map X.subtype := ⟨⟨x, hxX⟩, hxcen, rfl⟩
  rw [← hZc] at hxmap
  have : x ∈ Z ⊓ Subgroup.center K := ⟨hxmap, hxZ⟩
  rw [hZd] at this
  simpa using this

private theorem k328dds_mk_injective_on_X {K : Type} [Group K] {X : Subgroup K}
    (hXc : X ⊓ Subgroup.center K = ⊥) :
    ∀ x ∈ X, (QuotientGroup.mk' (Subgroup.center K)) x = 1 → x = 1 := by
  intro x hx hx1
  have hxC : x ∈ Subgroup.center K := (QuotientGroup.eq_one_iff x).1 hx1
  have : x ∈ X ⊓ Subgroup.center K := ⟨hx, hxC⟩
  rw [hXc] at this
  simpa using this

private theorem k328dds_pos_map {K : Type} [Group K] [Finite K] {Z X : Subgroup K}
    (hp : Pos K Z X)
    (hinjX : ∀ x ∈ X, (QuotientGroup.mk' (Subgroup.center K)) x = 1 → x = 1)
    (hsubbar : ((X.map (QuotientGroup.mk' (Subgroup.center K))).subgroupOf (Subgroup.centralizer
      (((Z.map (QuotientGroup.mk' (Subgroup.center K)) : Subgroup (K ⧸ Subgroup.center K)) :
        Set (K ⧸ Subgroup.center K))))).IsSubnormal) :
    Pos (K ⧸ Subgroup.center K)
      (Z.map (QuotientGroup.mk' (Subgroup.center K)))
      (X.map (QuotientGroup.mk' (Subgroup.center K))) := by
  obtain ⟨hZ, hZX, hXC, -, hqs, hcen, hlie⟩ := hp
  set π := QuotientGroup.mk' (Subgroup.center K) with hπ
  obtain ⟨eX, -⟩ := exists_mulEquiv_map π hinjX
  obtain ⟨eZ, -⟩ := exists_mulEquiv_map π (X := Z) fun z hz => hinjX z (hZX hz)
  refine ⟨?_, Subgroup.map_mono hZX, ?_, hsubbar, isQuasisimple_of_mulEquiv' eX hqs, ?_, ?_⟩
  · rw [← hZ]
    exact (Nat.card_congr eZ.toEquiv).symm
  · rintro _ ⟨x, hxX, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨z, hz, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 (hXC hxX) z hz]
  · rw [← hcen]
    exact (Nat.card_congr (Subgroup.centerCongr eX).toEquiv).symm
  · let f := QuotientGroup.congr (Subgroup.center X) (Subgroup.center (X.map π)) eX
      (Subgroup.map_center_eq eX)
    rcases hlie with hl | hl
    · exact Or.inl (LieModel.of_mulEquiv f hl)
    · exact Or.inr (LieModel.of_mulEquiv f hl)

private theorem k328dds_isSubnormal_map_of_normal_range {A Γ : Type} [Group A] [Group Γ]
    (f : A →* Γ) (hn : f.range.Normal) {K : Subgroup A} (hK : K.IsSubnormal) :
    (K.map f).IsSubnormal := by
  have h1 : (K.map f.rangeRestrict).IsSubnormal :=
    Subgroup.IsSubnormal.map (f := f.rangeRestrict) f.rangeRestrict_surjective hK
  have h2 := Subgroup.IsSubnormal.trans' h1 hn.isSubnormal
  rwa [Subgroup.map_map, MonoidHom.subtype_comp_rangeRestrict] at h2

private theorem k328dds_isSubnormal_subgroupOf_mono {G : Type} [Group G] {X C H : Subgroup G}
    (hXC : X ≤ C) (hCH : C ≤ H) (hN : (C.subgroupOf H).Normal)
    (hsub : (X.subgroupOf C).IsSubnormal) : (X.subgroupOf H).IsSubnormal := by
  have hN' : (Subgroup.inclusion hCH).range.Normal := by simpa using hN
  have h := k328dds_isSubnormal_map_of_normal_range (Subgroup.inclusion hCH) hN' hsub
  have heq : (X.subgroupOf C).map (Subgroup.inclusion hCH) = X.subgroupOf H := by
    ext z
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact hc
    · intro hz
      exact ⟨⟨(z : G), hXC hz⟩, hz, Subtype.ext rfl⟩
  rwa [heq] at h

private theorem k328dds_exists_zpow_eq {K : Type} [Group K] [Finite K] {Z : Subgroup K}
    (hZ : Nat.card Z = 3) : ∃ z : K, Subgroup.zpowers z = Z := by
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥Z) 3 (by rw [hZ])
  refine ⟨(z : K), ?_⟩
  have hcard : Nat.card (Subgroup.zpowers z) = 3 := by rw [Nat.card_zpowers, hz]
  have htop : Subgroup.zpowers z = ⊤ :=
    Subgroup.eq_of_le_of_card_ge (le_top : Subgroup.zpowers z ≤ (⊤ : Subgroup ↥Z)) (by
      rw [Nat.card_congr (Subgroup.topEquiv (G := ↥Z)).toEquiv, hZ, hcard])
  have hrange : (⊤ : Subgroup ↥Z).map Z.subtype = Z := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hmap := congrArg (Subgroup.map Z.subtype) htop
  rwa [MonoidHom.map_zpowers, hrange] at hmap

private theorem k328dds_subnormal_map {K : Type} [Group K] [Finite K] {Z X : Subgroup K}
    (hp : Pos K Z X) :
    ((X.map (QuotientGroup.mk' (Subgroup.center K))).subgroupOf (Subgroup.centralizer
      (((Z.map (QuotientGroup.mk' (Subgroup.center K)) : Subgroup (K ⧸ Subgroup.center K)) :
        Set (K ⧸ Subgroup.center K))))).IsSubnormal := by
  obtain ⟨hZ, -, hXC, hsub, -, -, -⟩ := hp
  obtain ⟨z, hzgen⟩ := k328dds_exists_zpow_eq hZ
  set π := QuotientGroup.mk' (Subgroup.center K) with hπ
  set Zb : Subgroup (K ⧸ Subgroup.center K) := Z.map π with hZb
  set Cb : Subgroup (K ⧸ Subgroup.center K) := Subgroup.centralizer (Zb : Set _) with hCb
  set C : Subgroup K := Subgroup.centralizer (Z : Set K) with hC
  set H : Subgroup K := Cb.comap π with hH
  have hzZ : z ∈ Z := by
    rw [← hzgen]
    simp
  have hzmem : π z ∈ Zb := by
    rw [hZb]
    exact Subgroup.mem_map_of_mem π hzZ
  have hCH : C ≤ H := by
    intro c hc
    rw [hH, Subgroup.mem_comap]
    rw [hCb, Subgroup.mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 hc y hy]
  have hcentral : ∀ h : ↥H, ⁅(h : K), z⁆ ∈ Subgroup.center K := by
    intro h
    rw [← QuotientGroup.eq_one_iff]
    change (QuotientGroup.mk' (Subgroup.center K)) ⁅(h : K), z⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_comap.mp (by simp))
      (π z) hzmem).symm
  let f : ↥H →* K :=
    { toFun := fun h => ⁅(h : K), z⁆
      map_one' := by simp
      map_mul' := fun a b => by
        have ha := hcentral a
        have hb := hcentral b
        show ⁅((a * b : ↥H) : K), z⁆ = ⁅(a : K), z⁆ * ⁅(b : K), z⁆
        rw [show ((a * b : ↥H) : K) = (a : K) * (b : K) from rfl]
        rw [commutatorElement_mul_left_eq_conj_mul, k328dds_mul_center_mul_inv hb]
        exact (Subgroup.mem_center_iff.1 hb ⁅(a : K), z⁆).symm }
  have hker : f.ker = C.subgroupOf H := by
    ext h
    rw [MonoidHom.mem_ker]
    constructor
    · intro hh
      rw [Subgroup.mem_subgroupOf, hC, Subgroup.mem_centralizer_iff]
      intro y hy
      rw [← hzgen] at hy
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [← hk]
      exact (commutatorElement_eq_one_iff_commute.mp (show ⁅(h : K), z⁆ = 1 from hh)).zpow_right
        k |>.eq.symm
    · intro hh
      rw [Subgroup.mem_subgroupOf, hC, Subgroup.mem_centralizer_iff] at hh
      show ⁅(h : K), z⁆ = 1
      refine commutatorElement_eq_one_iff_commute.mpr ?_
      exact (hh z hzZ).symm
  have hN : (C.subgroupOf H).Normal := by
    rw [← hker]
    exact f.normal_ker
  have hXH : X ≤ H := hXC.trans hCH
  have hXHsub : (X.subgroupOf H).IsSubnormal :=
    k328dds_isSubnormal_subgroupOf_mono hXC hCH hN hsub
  let πH : ↥H →* ↥Cb :=
    { toFun := fun h => ⟨π (h : K), by
        have hh : (h : K) ∈ Cb.comap π := hH ▸ h.2
        exact Subgroup.mem_comap.mp hh⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp [map_mul] }
  have hsurj : Function.Surjective πH := by
    intro y
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (Subgroup.center K) (y : K ⧸ Subgroup.center K)
    have hxH : x ∈ H := by
      rw [hH, Subgroup.mem_comap]
      rw [hx]
      exact y.2
    exact ⟨⟨x, hxH⟩, Subtype.ext hx⟩
  have hmapX : (X.subgroupOf H).map πH = (X.map π).subgroupOf Cb := by
    ext y
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact ⟨(h : K), hh, rfl⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨⟨x, hXH hx⟩, hx, Subtype.ext hxy⟩
  have h := Subgroup.IsSubnormal.map (f := πH) hsurj hXHsub
  rw [hmapX] at h
  simpa [hZb, hCb] using h

private theorem k328dds_map_ne_top {K : Type} [Group K] [Finite K] {X : Subgroup K}
    (hq : CFSG.Open.IsQuasisimple K)
    (hcard : Nat.card (Subgroup.center
      ↥(X.map (QuotientGroup.mk' (Subgroup.center K)))) = 3) :
    X.map (QuotientGroup.mk' (Subgroup.center K)) ≠ ⊤ := by
  intro htop
  have hperf : commutator (K ⧸ Subgroup.center K) = ⊤ :=
    k328dds_commutator_quotient_center hq.1
  have hcenter : Subgroup.center (K ⧸ Subgroup.center K) = ⊥ :=
    k328dds_center_eq_bot_of_perfect_of_simple hperf hq.2
  have hcardS : Nat.card (Subgroup.center
      ↥(X.map (QuotientGroup.mk' (Subgroup.center K)))) =
      Nat.card (Subgroup.center (K ⧸ Subgroup.center K)) := by
    rw [htop]
    exact Nat.card_congr (Subgroup.centerCongr Subgroup.topEquiv).toEquiv
  have h1 : Nat.card (Subgroup.center (K ⧸ Subgroup.center K)) = 1 := by
    rw [hcenter]
    simp
  rw [hcardS, h1] at hcard
  omega

private theorem k328dcc_isQuasisimple_of_open {Q : Type} [Group Q]
    (h : CFSG.Open.IsQuasisimple Q) : CFSG.IsQuasisimple Q := by
  refine ⟨⟨h.1⟩, h.2, ?_⟩
  by_contra hcon
  push Not at hcon
  have hsimple := h.2
  have hle : commutator Q ≤ Subgroup.center Q := by
    rw [commutator, Subgroup.commutator_le]
    intro x _ y _
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact hcon _ _
  have htop : (⊤ : Subgroup Q) ≤ Subgroup.center Q := h.1 ▸ hle
  obtain ⟨a, ha⟩ := (nontrivial_iff_exists_ne (1 : Q ⧸ Subgroup.center Q)).mp
    hsimple.toNontrivial
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  exact ha ((QuotientGroup.eq_one_iff x).mpr (htop (Subgroup.mem_top x)))

private theorem k328dcc_three_dvd_card_center {K : Type} [Group K] [Finite K]
    (hc : IsPGroup 3 (Subgroup.center K)) (hne : Subgroup.center K ≠ ⊥) :
    3 ∣ Nat.card (Subgroup.center K) := by
  rcases IsPGroup.card_eq_or_dvd (p := 3) (G := ↥(Subgroup.center K)) hc with h1 | h3
  · exact absurd (Subgroup.card_eq_one.mp h1) hne
  · exact h3

private theorem k328dcc_exists_order_three_center {K : Type} [Group K] [Finite K]
    (hc : IsPGroup 3 (Subgroup.center K)) (hne : Subgroup.center K ≠ ⊥) :
    ∃ Z0 : Subgroup K, Z0 ≤ Subgroup.center K ∧ Nat.card Z0 = 3 ∧
      CFSG.Open.IsElemAbelian 3 Z0 := by
  have hdiv := k328dcc_three_dvd_card_center hc hne
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center K)) 3 hdiv
  have hzpow : (z : K) ^ 3 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, Subgroup.orderOf_coe, hz]
  exact ⟨Subgroup.zpowers (z : K), Subgroup.zpowers_le.mpr z.2,
    by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hz],
    CFSG.Open.isElemAbelian_zpowers hzpow⟩

private theorem k328dcc_exists_elemAbelian_sq {K : Type} [Group K] [Finite K]
    {X : Subgroup K} (hqsX : CFSG.Open.IsQuasisimple ↥X)
    (hcenX : Nat.card (Subgroup.center ↥X) = 3) :
    ∃ E : Subgroup K, E ≤ X ∧ CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Group.IsPerfect ↥X := ⟨hqsX.1⟩
  have hZ : 3 ∣ Nat.card (Subgroup.center ↥X) := by rw [hcenX]
  obtain ⟨E, hE, hEcard⟩ :=
    CFSG.SectionRank.exists_elemAbelian_sq_of_dvd_card_center (L := ↥X) (p := 3)
      (by norm_num : (3 : ℕ) ≠ 2) hZ
  refine ⟨E.map X.subtype, Subgroup.map_subtype_le (H := X) E, hE.map X.subtype, ?_⟩
  rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective X), hEcard]
  norm_num

private theorem k328dcc_inf_center_eq_bot {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) {Z X : Subgroup K} (hpos : Pos K Z X) (hXne : X ≠ ⊤) :
    X ⊓ Subgroup.center K = ⊥ := by
  obtain ⟨hZcard, hZX, hXC, hsub, hqsX, hcenX, -⟩ := hpos
  set ZX : Subgroup K := (Subgroup.center ↥X).map X.subtype with hZXdef
  have hZXcard : Nat.card ZX = 3 := by
    rw [hZXdef, Subgroup.card_map_of_injective (Subgroup.subtype_injective X), hcenX]
  have hZleZX : Z ≤ ZX := by
    intro z hz
    refine Subgroup.mem_map.mpr ⟨⟨z, hZX hz⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    simpa using (Subgroup.mem_centralizer_iff.mp (hXC y.2) z hz).symm
  have hZeq : Z = ZX :=
    Subgroup.eq_of_le_of_card_ge hZleZX (by rw [hZXcard, hZcard])
  have hZcenter : Z ⊓ Subgroup.center K = ⊥ := by
    by_contra hne
    have hdvd : Nat.card ↥(Z ⊓ Subgroup.center K) ∣ 3 := by
      rw [← hZcard]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hcardne : Nat.card ↥(Z ⊓ Subgroup.center K) ≠ 1 := fun h1 =>
      hne (Subgroup.card_eq_one.mp h1)
    have hZle : Z ≤ Subgroup.center K := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
      · exact absurd h1 hcardne
      · have heq : Z ⊓ Subgroup.center K = Z :=
          Subgroup.eq_of_le_of_card_ge (H := Z ⊓ Subgroup.center K) (K := Z) inf_le_left
            (by rw [h3, hZcard])
        exact heq ▸ inf_le_right
    have hCtop : Subgroup.centralizer (Z : Set K) = ⊤ :=
      Subgroup.centralizer_eq_top_iff_subset.mpr (fun z hz => hZle hz)
    have hsub' : (X.subgroupOf (⊤ : Subgroup K)).IsSubnormal := by
      have h := hsub
      rwa [hCtop] at h
    have hXsub : X.IsSubnormal :=
      Subgroup.IsSubnormal.trans le_top hsub' Subgroup.IsSubnormal.top
    rcases CFSG.CGT.PushingUpLit.CGT6.isSubnormal_le_center_or_eq_top_of_quasisimple
        (k328dcc_isQuasisimple_of_open hq) hXsub with hXc | hXtop
    · have : Group.IsPerfect ↥X := ⟨hqsX.1⟩
      have : IsMulCommutative ↥X := IsMulCommutative.of_comm (fun a b => Subtype.ext (by
        simpa using (Subgroup.mem_center_iff.mp (hXc a.2) (b : K)).symm))
      have : Subsingleton ↥X := Group.IsPerfect.subsingleton_of_isMulCommutative
      have hbot : Subgroup.center ↥X = ⊥ := Subgroup.eq_bot_of_subsingleton _
      rw [hbot, Subgroup.card_bot] at hcenX
      omega
    · exact hXne hXtop
  have hle : X ⊓ Subgroup.center K ≤ Z ⊓ Subgroup.center K := by
    refine le_inf ?_ inf_le_right
    rw [hZeq]
    intro x hx
    obtain ⟨hxX, hxC⟩ := hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hxX⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    simpa using Subgroup.mem_center_iff.mp hxC (y : K)
  rw [hZcenter] at hle
  exact le_bot_iff.mp hle

private theorem k328dcc_pRank_three_eq_three {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) (hc : IsPGroup 3 (Subgroup.center K))
    (hne : Subgroup.center K ≠ ⊥) {Z X : Subgroup K} (hpos : Pos K Z X) (hXne : X ≠ ⊤)
    (h3 : CFSG.Open.pRank 3 (⊤ : Subgroup K) ≤ 3) :
    CFSG.Open.pRank 3 (⊤ : Subgroup K) = 3 := by
  have hinf : X ⊓ Subgroup.center K = ⊥ := k328dcc_inf_center_eq_bot hq hpos hXne
  obtain ⟨-, -, -, -, hqsX, hcenX, -⟩ := hpos
  obtain ⟨E, hEX, hEea, hEcard⟩ := k328dcc_exists_elemAbelian_sq hqsX hcenX
  obtain ⟨Z0, hZ0le, hZ0card, hZ0ea⟩ := k328dcc_exists_order_three_center hc hne
  have hEin : E ⊓ Z0 = ⊥ := by
    apply le_bot_iff.mp
    calc E ⊓ Z0 ≤ X ⊓ Subgroup.center K :=
          le_inf (le_trans inf_le_left hEX) (le_trans inf_le_right hZ0le)
      _ = ⊥ := hinf
  have hcomm : ∀ a ∈ E, ∀ b ∈ Z0, a * b = b * a := by
    intro a _ b hb
    exact Subgroup.mem_center_iff.mp (hZ0le hb) a
  have hsup_ea : CFSG.Open.IsElemAbelian 3 (E ⊔ Z0) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hEea hZ0ea hcomm
  have hsup_card : Nat.card ↥(E ⊔ Z0) = 3 ^ 3 := by
    rw [CFSG.CGT.T75P.card_sup_of_commute hcomm hEin, hEcard, hZ0card]
    norm_num
  have hle3 : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup K) :=
    CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_top hsup_ea hsup_card
  exact le_antisymm h3 hle3

theorem k328det_descend :
    ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → ∀ Z X : Subgroup K,
      Pos K Z X → X ≠ ⊤ → X ⊓ Subgroup.center K = ⊥ ∧ K328DetPosIn (K ⧸ Subgroup.center K) := by
  intro K _ _ hq Z X hp hX
  obtain ⟨hZ, hZX, hXC, hsub, hqs, hcen, hlie⟩ := hp
  have hZc : Z = (Subgroup.center ↥X).map X.subtype := k328dds_Z_eq_center hZ hZX hXC hcen
  have hZd : Z ⊓ Subgroup.center K = ⊥ := k328dds_Z_inf_center hq hqs.1 hZ hZX hXC hsub hX
  have hXc : X ⊓ Subgroup.center K = ⊥ := k328dds_X_inf_center hZc hZd
  refine ⟨hXc, ?_⟩
  have hinjX := k328dds_mk_injective_on_X hXc
  have hpos : Pos (K ⧸ Subgroup.center K)
      (Z.map (QuotientGroup.mk' (Subgroup.center K)))
      (X.map (QuotientGroup.mk' (Subgroup.center K))) :=
    k328dds_pos_map ⟨hZ, hZX, hXC, hsub, hqs, hcen, hlie⟩ hinjX
      (k328dds_subnormal_map ⟨hZ, hZX, hXC, hsub, hqs, hcen, hlie⟩)
  refine ⟨Z.map (QuotientGroup.mk' (Subgroup.center K)),
    X.map (QuotientGroup.mk' (Subgroup.center K)), hpos, ?_⟩
  have hcard : Nat.card (Subgroup.center
      ↥(X.map (QuotientGroup.mk' (Subgroup.center K)))) = 3 := by
    obtain ⟨eX, -⟩ := exists_mulEquiv_map (QuotientGroup.mk' (Subgroup.center K)) hinjX
    rw [← hcen]
    exact (Nat.card_congr (Subgroup.centerCongr eX).toEquiv).symm
  exact k328dds_map_ne_top hq hcard

theorem k328det_centerCases :
    K34odd → ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
      IsPGroup 3 (Subgroup.center K) → CFSG.Open.IsKGroup (K ⧸ Subgroup.center K) →
      CFSG.Open.pRank 3 (⊤ : Subgroup K) ≤ 3 → ∀ Z X : Subgroup K, Pos K Z X → X ≠ ⊤ →
        Subgroup.center K = ⊥ ∨ ThreeCover (fun Y _ => IsSpor Y .ONan) K := by
  intro h34 K _ _ hq hc hK h3 Z X hpos hXne
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hZ : Subgroup.center K = ⊥
  · exact Or.inl hZ
  · right
    have hq' : CFSG.IsQuasisimple K := k328dcc_isQuasisimple_of_open hq
    have hcat : CFSG.Open.IsCatalogGroup (K ⧸ Subgroup.center K) :=
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small.isCatalogGroup_of_isKGroup_of_simple
        hK hq.2 hq'.2.2
    have hodd : Odd (Nat.card (Subgroup.center K)) := by
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 3) (G := ↥(Subgroup.center K))).mp hc
      rw [hn]
      exact Odd.pow (by norm_num : Odd (3 : ℕ))
    have hm3 : CFSG.Open.pRank 3 (⊤ : Subgroup K) = 3 :=
      k328dcc_pRank_three_eq_three hq hc hZ hpos hXne h3
    rcases h34 K hq hcat hodd hm3 with hON | ⟨hnot3, -⟩
    · exact hON
    · exact absurd (k328dcc_three_dvd_card_center hc hZ) hnot3

open CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route

private theorem k328dsl_nonab_of_openQuasi {Q : Type} [Group Q]
    (h : CFSG.Open.IsQuasisimple Q) :
    ∃ a b : Q ⧸ Subgroup.center Q, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have hle : commutator Q ≤ Subgroup.center Q := by
    rw [commutator, Subgroup.commutator_le]
    intro x _ y _
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact hcon _ _
  have htop : (⊤ : Subgroup Q) ≤ Subgroup.center Q := h.1 ▸ hle
  obtain ⟨a, ha⟩ := (nontrivial_iff_exists_ne (1 : Q ⧸ Subgroup.center Q)).mp
    h.2.toNontrivial
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  exact ha ((QuotientGroup.eq_one_iff x).mpr (htop (Subgroup.mem_top x)))

private theorem k328dsl_two_le_pRank_of_pos {K : Type} [Group K] [Finite K]
    {Z X : Subgroup K} (hp : Pos K Z X) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup K) := by
  obtain ⟨-, -, -, -, hqs, hcen, -⟩ := hp
  have : Group.IsPerfect ↥X := ⟨hqs.1⟩
  have h3dvd : 3 ∣ Nat.card (Subgroup.center ↥X) := ⟨1, by rw [hcen]⟩
  obtain ⟨E, hE, hEcard⟩ :=
    CFSG.SectionRank.exists_elemAbelian_sq_of_dvd_card_center (L := ↥X) (p := 3)
      (by norm_num) h3dvd
  have hmap : CFSG.Open.IsElemAbelian 3 (E.map X.subtype) :=
    CFSG.SectionRank.isElemAbelian_map hE X.subtype
  have hcard : Nat.card (E.map X.subtype) = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective X.subtype_injective, hEcard]
  exact CFSG.SectionRank.le_pRank (p := 3) (G := K) (by norm_num) le_top hmap hcard

private theorem k328dsl_k33Models_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : K33Models B) : K33Models A := by
  rcases h with (h | h) | (h | h) | (⟨p, f, hq, h⟩ | ⟨p, f, hq, h⟩ | ⟨p, f, h⟩ | ⟨p, f, h⟩ |
    ⟨p, f, h⟩ | ⟨f, h⟩ | h | ⟨p, f, hq, h⟩ | ⟨p, f, hq, h⟩ | ⟨p, f, hq, h⟩ | ⟨p, f, hq, h⟩) |
    ⟨s, hsp, h⟩
  · obtain ⟨φ⟩ := h; exact K33Models.of_isAlt_seven ⟨e.trans φ⟩
  · obtain ⟨φ⟩ := h; exact K33Models.of_isAlt_six ⟨e.trans φ⟩
  · exact K33Models.of_psl3_three_one (LieModel.of_mulEquiv e.symm h)
  · exact K33Models.of_psu3_three_one (LieModel.of_mulEquiv e.symm h)
  · exact K33Models.of_psl3 hq (LieModel.of_mulEquiv e.symm h)
  · exact K33Models.of_psu3 hq (LieModel.of_mulEquiv e.symm h)
  · exact K33Models.of_psp4 (LieModel.of_mulEquiv e.symm h)
  · exact K33Models.of_g2 (LieModel.of_mulEquiv e.symm h)
  · exact K33Models.of_trialityD4 (LieModel.of_mulEquiv e.symm h)
  · exact K33Models.of_twistedF4 (LieModel.of_mulEquiv e.symm h)
  · exact K33Models.of_tits (LieModel.of_mulEquiv e.symm h)
  · exact K33Models.of_psl4 hq (LieModel.of_mulEquiv e.symm h)
  · exact K33Models.of_psu4 hq (LieModel.of_mulEquiv e.symm h)
  · exact K33Models.of_psl5 hq (LieModel.of_mulEquiv e.symm h)
  · exact K33Models.of_psu5 hq (LieModel.of_mulEquiv e.symm h)
  · obtain ⟨φ⟩ := h; exact K33Models.of_spor hsp ⟨e.trans φ⟩

private theorem k328dsl_k33Models_of_pRank_two {K : Type} [Group K] [Finite K]
    (h33 : K33) (hq : CFSG.Open.IsQuasisimple K) (hZ : Subgroup.center K = ⊥)
    (hK : CFSG.Open.IsKGroup (K ⧸ Subgroup.center K))
    (hr2 : CFSG.Open.pRank 3 (⊤ : Subgroup K) = 2) : K33Models K := by
  have : IsSimpleGroup (K ⧸ Subgroup.center K) := hq.2
  have hnonab : ∃ a b : K ⧸ Subgroup.center K, a * b ≠ b * a :=
    k328dsl_nonab_of_openQuasi hq
  have hcat : CFSG.Open.IsCatalogGroup (K ⧸ Subgroup.center K) :=
    hK.isCatalogGroup_of_surjective ⊤ hnonab
      (Subgroup.topEquiv (G := K ⧸ Subgroup.center K)).toMonoidHom
      (Subgroup.topEquiv (G := K ⧸ Subgroup.center K)).surjective
  have hpgrp : IsPGroup 3 (Subgroup.center K) := by rw [hZ]; exact IsPGroup.of_bot
  rcases h33 K hq hcat hpgrp hr2 with hcover | hmodels
  · exfalso
    have h3 : Nat.card (Subgroup.center K) = 3 := by
      rcases hcover with h | h | h | ⟨p, f, -, h⟩ | ⟨p, f, -, h⟩ <;> exact h.2.1
    rw [hZ] at h3
    have hbot : Nat.card (⊥ : Subgroup K) = 1 := Nat.card_unique
    omega
  · exact hmodels

private theorem k328dsl_k34Models_of_pRank_three {K : Type} [Group K] [Finite K]
    (h34 : K34odd) (hq : CFSG.Open.IsQuasisimple K) (hZ : Subgroup.center K = ⊥)
    (hK : CFSG.Open.IsKGroup (K ⧸ Subgroup.center K))
    (hr3 : CFSG.Open.pRank 3 (⊤ : Subgroup K) = 3) :
    K34Models (K ⧸ Subgroup.center K) := by
  have : IsSimpleGroup (K ⧸ Subgroup.center K) := hq.2
  have hnonab : ∃ a b : K ⧸ Subgroup.center K, a * b ≠ b * a :=
    k328dsl_nonab_of_openQuasi hq
  have hcat : CFSG.Open.IsCatalogGroup (K ⧸ Subgroup.center K) :=
    hK.isCatalogGroup_of_surjective ⊤ hnonab
      (Subgroup.topEquiv (G := K ⧸ Subgroup.center K)).toMonoidHom
      (Subgroup.topEquiv (G := K ⧸ Subgroup.center K)).surjective
  have hodd : Odd (Nat.card (Subgroup.center K)) := by
    rw [hZ, Nat.card_unique]; exact ⟨0, by norm_num⟩
  rcases h34 K hq hcat hodd hr3 with hcover | ⟨-, hmodels⟩
  · exfalso
    have h3 : Nat.card (Subgroup.center K) = 3 := hcover.2.1
    rw [hZ] at h3
    have hbot : Nat.card (⊥ : Subgroup K) = 1 := Nat.card_unique
    omega
  · exact hmodels

theorem k328det_simpleLists :
    K33 → K34odd → ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
      Subgroup.center K = ⊥ → CFSG.Open.IsKGroup (K ⧸ Subgroup.center K) →
      CFSG.Open.pRank 3 (⊤ : Subgroup K) ≤ 3 → ∀ Z X : Subgroup K, Pos K Z X →
        CFSG.Open.pRank 3 (⊤ : Subgroup (K ⧸ Subgroup.center K)) ≤ 3 ∧
          (K33Models (K ⧸ Subgroup.center K) ∨ K34Models (K ⧸ Subgroup.center K)) := by
  intro h33 h34 K _ _ hq hZ hK h3 Z X hp
  let e : (K ⧸ Subgroup.center K) ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hpRank : CFSG.Open.pRank 3 (⊤ : Subgroup (K ⧸ Subgroup.center K)) =
      CFSG.Open.pRank 3 (⊤ : Subgroup K) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e
  refine ⟨?_, ?_⟩
  · rw [hpRank]; exact h3
  · have h2 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup K) := k328dsl_two_le_pRank_of_pos hp
    have hr : CFSG.Open.pRank 3 (⊤ : Subgroup K) = 2 ∨
        CFSG.Open.pRank 3 (⊤ : Subgroup K) = 3 := by
      by_cases h : CFSG.Open.pRank 3 (⊤ : Subgroup K) = 2
      · exact Or.inl h
      · exact Or.inr (by omega)
    rcases hr with hr2 | hr3
    · exact Or.inl (k328dsl_k33Models_of_mulEquiv e
        (k328dsl_k33Models_of_pRank_two h33 hq hZ hK hr2))
    · exact Or.inr (k328dsl_k34Models_of_pRank_three h34 hq hZ hK hr3)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
