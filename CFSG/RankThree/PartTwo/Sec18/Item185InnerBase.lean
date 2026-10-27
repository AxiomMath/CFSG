module

public import CFSG.RankThree.PartTwo.Sec18.Item185Leaves
public import CFSG.RankThree.PartTwo.Sec8.Item812Res12ProofIrred
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowTools
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporRankTwo
public import CFSG.RankThree.PartTwo.Sec18.Item185O23
public import CFSG.RankThree.PartTwo.Sec4.RonanK429Rows

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item185Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late (IsE27)
open CFSG.Assembly (IsElemAbelian)
open CFSG.RankThree.PartTwo.Sec19.SimsC198 (RankHyp)
open CFSG.RankThree.PartTwo.Sec4.Item434Kit (WreathFacts vecElt baseA wreathW)
open CFSG.RankThree.PartTwo.Sec8.Item812Res12 (sgnV)
open CFSG.RankThree.PartTwo.Sec4.RonanK429 (NoE27 AutNoE27)

structure InnerData (X : Type) [Group X] (A B : Subgroup X) (c : X) : Prop where
  isElemAbelian : IsElemAbelian 3 A
  card_A : Nat.card A = 27
  le_B : B ≤ A
  card_B : Nat.card B = 9
  eq_sup : A = Subgroup.zpowers c ⊔ B
  not_mem : c ∉ B
  inf_center : A ⊓ Subgroup.center X = ⊥
  normalizer_le : Subgroup.normalizer (A : Set X) ≤ Subgroup.normalizer (B : Set X)
  omega : B ≤ (Sec4.oTwoP 3 (Subgroup.centralizer ({c} : Set X))).map
    (Subgroup.centralizer ({c} : Set X)).subtype

theorem leafInner_of_data
    (h : ∀ (X : Type) [Group X] [Finite X], RankHyp X → ∀ (A B : Subgroup X) (c : X),
      InnerData X A B c → False) : LeafInner := by
  intro X _ _ hX A B c hA h27 hB h9 hsup hc hAZ hN hO
  exact h X hX A B c ⟨hA, h27, hB, h9, hsup, hc, hAZ, hN, hO⟩

@[expose] def NoInnerData (S : Type) [Group S] : Prop :=
  ∀ (A B : Subgroup S) (c : S), InnerData S A B c → False

@[expose] def InnerCase (P : (S : Type) → [Group S] → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], RankHyp X → ∀ (A B : Subgroup X) (c : X),
    InnerData X A B c → P (X ⧸ Subgroup.center X) → False

private theorem eq_one_of_center_pow_three {G : Type} [Group G] [Finite G]
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center G)) {z : G} (hz : z ∈ Subgroup.center G)
    (h3 : z ^ 3 = 1) : z = 1 := by
  have hw : (⟨z, hz⟩ : Subgroup.center G) ^ 3 = 1 := Subtype.ext (by simpa using h3)
  rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hw) with h1 | h1
  · exact congrArg Subtype.val (orderOf_eq_one_iff.mp h1)
  · have hdvd := orderOf_dvd_natCard (⟨z, hz⟩ : Subgroup.center G)
    rw [h1] at hdvd
    exact absurd hdvd hZ

private theorem four_le_pRank_of_card_eq_81 {G : Type} [Group G] [Finite G] {E : Subgroup G}
    (hE : IsElemAbelian 3 E) (h81 : Nat.card E = 81) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G) := by
  unfold CFSG.Open.pRank
  have hbdd : BddAbove {k : ℕ | ∃ F : Subgroup G, F ≤ ⊤ ∧ IsElemAbelian 3 F ∧
      Nat.card F = 3 ^ k} := by
    refine ⟨Nat.card G, ?_⟩
    rintro k ⟨F, -, -, hF⟩
    have hk : k < 3 ^ k := Nat.lt_pow_self (by norm_num)
    have h1 : 3 ^ k ≤ Nat.card G := by
      rw [← hF]
      exact Nat.card_le_card_of_injective _ Subtype.val_injective
    exact hk.le.trans h1
  exact le_csSup hbdd ⟨E, le_top, hE, h81.trans (by norm_num)⟩

private theorem normal_zpowers_of_mem_center {G : Type} [Group G] {z : G}
    (hz : z ∈ Subgroup.center G) : (Subgroup.zpowers z).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
  have hc : z ^ m ∈ Subgroup.center G := (Subgroup.center G).zpow_mem hz m
  rw [Subgroup.mem_center_iff.mp hc g, mul_inv_cancel_right]
  exact Subgroup.mem_zpowers_iff.mpr ⟨m, rfl⟩

private theorem isElemAbelian_sup_zpowers_central {G : Type} [Group G] {A : Subgroup G}
    (hA : IsElemAbelian 3 A) {z : G} (hz : z ∈ Subgroup.center G) (hz3 : z ^ 3 = 1) :
    IsElemAbelian 3 (A ⊔ Subgroup.zpowers z) := by
  have hcen : ∀ k ∈ Subgroup.zpowers z, k ∈ Subgroup.center G := by
    intro k hk
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    exact (Subgroup.center G).zpow_mem hz m
  have hcube : ∀ k ∈ Subgroup.zpowers z, k ^ 3 = 1 := by
    intro k hk
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz3, one_zpow]
  haveI : (Subgroup.zpowers z).Normal := normal_zpowers_of_mem_center hz
  have hsplit : ∀ x ∈ A ⊔ Subgroup.zpowers z,
      ∃ a ∈ A, ∃ k ∈ Subgroup.zpowers z, a * k = x :=
    fun x hx => Subgroup.mem_sup_of_normal_right.mp hx
  have hcomm : ∀ x ∈ A ⊔ Subgroup.zpowers z, ∀ y ∈ A ⊔ Subgroup.zpowers z, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, k, hk, rfl⟩ := hsplit x hx
    obtain ⟨b, hb, l, hl, rfl⟩ := hsplit y hy
    have hab : Commute a b :=
      congrArg Subtype.val (isMulCommutative_iff.mp hA.1 ⟨a, ha⟩ ⟨b, hb⟩)
    have hkb : Commute k b := (Subgroup.mem_center_iff.mp (hcen k hk) b).symm
    have hal : Commute a l := Subgroup.mem_center_iff.mp (hcen l hl) a
    have hkl : Commute k l := Subgroup.mem_center_iff.mp (hcen l hl) k
    exact Commute.mul_left (Commute.mul_right hab hal) (Commute.mul_right hkb hkl)
  refine ⟨isMulCommutative_iff.mpr (fun x y => Subtype.ext (hcomm _ x.2 _ y.2)),
    fun x hx => ?_⟩
  obtain ⟨a, ha, k, hk, rfl⟩ := hsplit x hx
  have hak : Commute a k := Subgroup.mem_center_iff.mp (hcen k hk) a
  rw [hak.mul_pow, hA.2 a ha, hcube k hk, one_mul]

private theorem card_sup_zpowers_eq_81 {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (hA : Nat.card A = 27) {z : G} (hz : z ∈ Subgroup.center G) (hz3 : orderOf z = 3)
    (hzA : z ∉ A) : Nat.card (A ⊔ Subgroup.zpowers z : Subgroup G) = 81 := by
  haveI : (Subgroup.zpowers z).Normal := normal_zpowers_of_mem_center hz
  have hW : Nat.card (Subgroup.zpowers z) = 3 := by rw [Nat.card_zpowers, hz3]
  have hWA : Subgroup.zpowers z ⊓ A = ⊥ := by
    have hdvd : Nat.card (Subgroup.zpowers z ⊓ A : Subgroup G) ∣ 3 := by
      rw [← hW]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h1
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      have heq : Subgroup.zpowers z ⊓ A = Subgroup.zpowers z :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (le_of_eq (by rw [hW, h1]))
      have hzmem : z ∈ Subgroup.zpowers z ⊓ A := by
        rw [heq]
        exact Subgroup.mem_zpowers z
      exact hzA (Subgroup.mem_inf.mp hzmem).2
  have hrel1 : (Subgroup.zpowers z).relIndex A = 27 := by
    have h1 : (Subgroup.zpowers z).relIndex A *
        Nat.card (Subgroup.zpowers z ⊓ A : Subgroup G) = Nat.card A :=
      Subgroup.relIndex_mul_card (Subgroup.zpowers z) A
    rw [hWA, Subgroup.card_bot, hA, mul_one] at h1
    exact h1
  have hrel2 : (Subgroup.zpowers z).relIndex (A ⊔ Subgroup.zpowers z) = 27 := by
    rw [Subgroup.relIndex_sup_right, hrel1]
  have h2 : (Subgroup.zpowers z).relIndex (A ⊔ Subgroup.zpowers z) *
      Nat.card (Subgroup.zpowers z ⊓ (A ⊔ Subgroup.zpowers z) : Subgroup G) =
      Nat.card (A ⊔ Subgroup.zpowers z : Subgroup G) :=
    Subgroup.relIndex_mul_card (Subgroup.zpowers z) (A ⊔ Subgroup.zpowers z)
  have hinf : Subgroup.zpowers z ⊓ (A ⊔ Subgroup.zpowers z) = Subgroup.zpowers z :=
    inf_eq_left.mpr le_sup_right
  rw [hrel2, hinf, hW] at h2
  omega

private theorem card_map_mk_center {G : Type} [Group G] {A : Subgroup G}
    (hA : A ⊓ Subgroup.center G = ⊥) :
    Nat.card (A.map (QuotientGroup.mk' (Subgroup.center G))) = Nat.card A := by
  let f : A →* (A.map (QuotientGroup.mk' (Subgroup.center G))) :=
    ((QuotientGroup.mk' (Subgroup.center G)).comp A.subtype).codRestrict
      (A.map (QuotientGroup.mk' (Subgroup.center G))) (fun a => Subgroup.mem_map_of_mem _ a.2)
  have hf : Function.Bijective f := by
    refine ⟨fun a b hab => ?_, ?_⟩
    · have hab' : QuotientGroup.mk' (Subgroup.center G) (a : G) =
          QuotientGroup.mk' (Subgroup.center G) (b : G) := congrArg Subtype.val hab
      have hmem : (a : G)⁻¹ * (b : G) ∈ A ⊓ Subgroup.center G :=
        ⟨A.mul_mem (A.inv_mem a.2) b.2, QuotientGroup.eq.mp hab'⟩
      rw [hA, Subgroup.mem_bot, inv_mul_eq_one] at hmem
      exact Subtype.ext hmem
    · rintro ⟨y, hy⟩
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      exact ⟨⟨x, hx⟩, rfl⟩
  exact (Nat.card_congr (MulEquiv.ofBijective f hf).toEquiv).symm

private theorem le_oTwoP_image {G H : Type} [Group G] [Group H] [Finite G] [Finite H]
    (C : Subgroup G) (f : G →* H) (M Q : Subgroup H) (hMQ : M ≤ Q)
    (hfC : ∀ x ∈ C, f x ∈ M) (hfM : ∀ y ∈ M, ∃ x ∈ C, f x = y)
    (hMn : (M.subgroupOf Q).Normal) {B : Subgroup G}
    (hB : B ≤ (Sec4.oTwoP 3 ↥C).map C.subtype) :
    B.map f ≤ (Sec4.oTwoP 3 ↥Q).map Q.subtype := by
  let g : ↥C →* ↥M := (f.comp C.subtype).codRestrict M (fun x => hfC x x.2)
  have hg : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := hfM y hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hcomp : M.subtype.comp g = f.comp C.subtype := by
    ext x
    rfl
  have h3 : (Sec4.oTwoP 3 ↥C).map (f.comp C.subtype) ≤ (Sec4.oTwoP 3 ↥M).map M.subtype := by
    rw [← hcomp, ← Subgroup.map_map]
    exact Subgroup.map_mono (oTwoP_map_le_of_surjective g hg)
  have h4 : (Sec4.oTwoP 3 ↥M).map M.subtype ≤ (Sec4.oTwoP 3 ↥Q).map Q.subtype :=
    oTwoP_le_of_normal hMQ hMn
  calc B.map f ≤ ((Sec4.oTwoP 3 ↥C).map C.subtype).map f := Subgroup.map_mono hB
    _ = (Sec4.oTwoP 3 ↥C).map (f.comp C.subtype) := by rw [Subgroup.map_map]
    _ ≤ (Sec4.oTwoP 3 ↥Q).map Q.subtype := h3.trans h4

private theorem conj_mem_of_mem_normalizer_quot {G : Type} [Group G] {A : Subgroup G}
    (hA : IsElemAbelian 3 A) (hZ : ∀ z ∈ Subgroup.center G, z ^ 3 = 1 → z = 1) {x : G}
    (hx : QuotientGroup.mk' (Subgroup.center G) x ∈ Subgroup.normalizer
      ((A.map (QuotientGroup.mk' (Subgroup.center G)) : Subgroup (G ⧸ Subgroup.center G)) :
        Set (G ⧸ Subgroup.center G))) :
    ∀ a ∈ A, x * a * x⁻¹ ∈ A := by
  intro a ha
  have h1 : QuotientGroup.mk' (Subgroup.center G) a ∈
      A.map (QuotientGroup.mk' (Subgroup.center G)) := Subgroup.mem_map_of_mem _ ha
  have h2 : QuotientGroup.mk' (Subgroup.center G) (x * a * x⁻¹) ∈
      A.map (QuotientGroup.mk' (Subgroup.center G)) := by
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hx _).mp h1
  obtain ⟨a', ha', ha'eq⟩ := Subgroup.mem_map.mp h2
  obtain ⟨z, hz⟩ : ∃ z, z = a'⁻¹ * (x * a * x⁻¹) := ⟨_, rfl⟩
  have hzc : z ∈ Subgroup.center G := by
    rw [hz]
    exact QuotientGroup.eq.mp ha'eq
  have hcomm : Commute a' z := Subgroup.mem_center_iff.mp hzc a'
  have hg3 : (x * a * x⁻¹) ^ 3 = 1 := by
    rw [conj_pow, hA.2 a ha, mul_one, mul_inv_cancel]
  have hgz : x * a * x⁻¹ = a' * z := by
    rw [hz, mul_inv_cancel_left]
  have hz3 : z ^ 3 = 1 := by
    have h := hg3
    rw [hgz, hcomm.mul_pow, hA.2 a' ha', one_mul] at h
    exact h
  have hz1 : z = 1 := hZ z hzc hz3
  rw [hgz, hz1, mul_one]
  exact ha'

private theorem conj_mem_centralizer_of_quot {G : Type} [Group G] {c d x : G}
    (hd : QuotientGroup.mk' (Subgroup.center G) d ∈ Subgroup.centralizer
      ({QuotientGroup.mk' (Subgroup.center G) c} : Set (G ⧸ Subgroup.center G)))
    (hx : x ∈ Subgroup.centralizer ({c} : Set G)) :
    d * x * d⁻¹ ∈ Subgroup.centralizer ({c} : Set G) := by
  have hcd : QuotientGroup.mk' (Subgroup.center G) (c * d) =
      QuotientGroup.mk' (Subgroup.center G) (d * c) := by
    have h := (Subgroup.mem_centralizer_iff.mp hd) (QuotientGroup.mk' (Subgroup.center G) c)
      (Set.mem_singleton _)
    rw [map_mul, map_mul]
    exact h
  obtain ⟨w, hw⟩ : ∃ w, w = (c * d)⁻¹ * (d * c) := ⟨_, rfl⟩
  have hwc : w ∈ Subgroup.center G := by
    rw [hw]
    exact QuotientGroup.eq.mp hcd
  have hdc : d⁻¹ * c * d = c * w⁻¹ := by
    rw [hw]
    group
  have hxc : x * c = c * x := (Subgroup.mem_centralizer_iff.mp hx c (Set.mem_singleton c)).symm
  have hwx : x * w⁻¹ = w⁻¹ * x := Subgroup.mem_center_iff.mp ((Subgroup.center G).inv_mem hwc) x
  have key : x * (d⁻¹ * c * d) = (d⁻¹ * c * d) * x := by
    rw [hdc]
    calc x * (c * w⁻¹) = (x * c) * w⁻¹ := by group
      _ = (c * x) * w⁻¹ := by rw [hxc]
      _ = c * (x * w⁻¹) := by group
      _ = c * (w⁻¹ * x) := by rw [hwx]
      _ = (c * w⁻¹) * x := by group
  have final : d * x * d⁻¹ * c = c * (d * x * d⁻¹) := by
    calc d * x * d⁻¹ * c = d * (x * (d⁻¹ * c * d)) * d⁻¹ := by group
      _ = d * ((d⁻¹ * c * d) * x) * d⁻¹ := by rw [key]
      _ = c * (d * x * d⁻¹) := by group
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  rw [hh]
  exact final.symm

private theorem map_conj_map_conj_inv {H : Type} [Group H] (K : Subgroup H) (g : H) :
    (K.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = K := by
  rw [Subgroup.map_map]
  have hcomp : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id H := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [hcomp, Subgroup.map_id]

private theorem oTwoP_normal_aux (p : ℕ) (H : Type) [Group H] : (Sec4.oTwoP p H).Normal := by
  unfold Sec4.oTwoP
  exact Subgroup.Normal.comap CFSG.pCore_normal _

section Reduction

variable {X : Type} [Group X] [Finite X]

theorem InnerData.three_not_dvd_card_center (hX : RankHyp X) {A B : Subgroup X} {c : X}
    (h : InnerData X A B c) : ¬ 3 ∣ Nat.card (Subgroup.center X) := by
  intro hdvd
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center X) 3 hdvd
  have hzc : (w : X) ∈ Subgroup.center X := w.2
  have hw3 : (w : X) ^ 3 = 1 := by
    have h3 : w ^ 3 = 1 := by
      rw [← hw]
      exact pow_orderOf_eq_one w
    simpa using congrArg Subtype.val h3
  have hw1 : (w : X) ≠ 1 := by
    intro h1
    have hw' : w = 1 := Subtype.ext h1
    rw [hw', orderOf_one] at hw
    norm_num at hw
  have hwA : (w : X) ∉ A := by
    intro hwA
    have hmem : (w : X) ∈ A ⊓ Subgroup.center X := ⟨hwA, hzc⟩
    rw [h.inf_center, Subgroup.mem_bot] at hmem
    exact hw1 hmem
  have hord : orderOf (w : X) = 3 := by
    rw [Subgroup.orderOf_coe, hw]
  have hE := isElemAbelian_sup_zpowers_central h.isElemAbelian hzc hw3
  have hE81 := card_sup_zpowers_eq_81 h.card_A hzc hord hwA
  have h4 := four_le_pRank_of_card_eq_81 hE hE81
  have h3 := hX.rank_three
  omega

theorem center_quotient_eq_bot (hX : RankHyp X) :
    Subgroup.center (X ⧸ Subgroup.center X) = ⊥ :=
  Sec4.RonanK429.center_eq_bot_of_isSimpleGroup hX.quasisimple.2.1 hX.quasisimple.2.2

theorem isSimpleGroup_quotient (hX : RankHyp X) : IsSimpleGroup (X ⧸ Subgroup.center X) :=
  hX.quasisimple.2.1

theorem oTwoP_normal_le {G : Type} [Group G] [Finite G] (N : Subgroup G) [N.Normal] :
    (Sec4.oTwoP 3 N).map N.subtype ≤ Sec4.oTwoP 3 G := by
  have hn : (N.subgroupOf (⊤ : Subgroup G)).Normal := inferInstance
  have h1 := oTwoP_le_of_normal (le_top : N ≤ ⊤) hn
  have h2 := oTwoP_map_le_of_surjective (⊤ : Subgroup G).subtype
    (fun g => ⟨⟨g, Subgroup.mem_top g⟩, rfl⟩)
  exact h1.trans h2

theorem oTwoP_map_mulEquiv {G H : Type} [Group G] [Group H] [Finite G] (e : G ≃* H) :
    (Sec4.oTwoP 3 G).map e.toMonoidHom = Sec4.oTwoP 3 H := by
  haveI : Finite H := Finite.of_surjective _ e.surjective
  have hsub : (Sec4.oTwoP 3 H).map e.symm.toMonoidHom ≤ Sec4.oTwoP 3 G :=
    oTwoP_map_le_of_surjective e.symm.toMonoidHom e.symm.surjective
  apply le_antisymm
  · exact oTwoP_map_le_of_surjective e.toMonoidHom e.surjective
  · intro y hy
    have h2 : e.symm y ∈ Sec4.oTwoP 3 G := hsub (Subgroup.mem_map_of_mem _ hy)
    exact Subgroup.mem_map.mpr ⟨e.symm y, h2, by simp⟩

theorem InnerData.quotient (hX : RankHyp X) {A B : Subgroup X} {c : X} (h : InnerData X A B c) :
    InnerData (X ⧸ Subgroup.center X) (A.map (QuotientGroup.mk' (Subgroup.center X)))
      (B.map (QuotientGroup.mk' (Subgroup.center X))) (QuotientGroup.mk c) := by
  have hZ : ¬ 3 ∣ Nat.card (Subgroup.center X) := h.three_not_dvd_card_center hX
  have hZ1 : ∀ z ∈ Subgroup.center X, z ^ 3 = 1 → z = 1 :=
    fun z hz h3 => eq_one_of_center_pow_three hZ hz h3
  have hZc : Subgroup.center (X ⧸ Subgroup.center X) = ⊥ := center_quotient_eq_bot hX
  have hAc : A ⊓ Subgroup.center X = ⊥ := h.inf_center
  have hBc : B ⊓ Subgroup.center X = ⊥ :=
    le_bot_iff.mp ((inf_le_inf_right (Subgroup.center X) h.le_B).trans hAc.le)
  have hcA : c ∈ A := by
    rw [h.eq_sup]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers c)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3
      (QuotientGroup.mk' (Subgroup.center X)) A h.isElemAbelian
  · rw [card_map_mk_center hAc, h.card_A]
  · exact Subgroup.map_mono h.le_B
  · rw [card_map_mk_center hBc, h.card_B]
  · rw [h.eq_sup, Subgroup.map_sup, MonoidHom.map_zpowers] <;> rfl
  · intro hmem
    obtain ⟨b, hb, hbc⟩ := Subgroup.mem_map.mp hmem
    have hbc' : b⁻¹ * c ∈ Subgroup.center X := QuotientGroup.eq.mp hbc
    have hbA : b⁻¹ * c ∈ A := A.mul_mem (A.inv_mem (h.le_B hb)) hcA
    have hmem' : b⁻¹ * c ∈ A ⊓ Subgroup.center X := ⟨hbA, hbc'⟩
    rw [hAc, Subgroup.mem_bot, inv_mul_eq_one] at hmem'
    exact h.not_mem (by rw [← hmem']; exact hb)
  · rw [hZc, inf_bot_eq]
  · intro s hs
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center X) s
    have hsx : ∀ a ∈ A, x * a * x⁻¹ ∈ A :=
      conj_mem_of_mem_normalizer_quot h.isElemAbelian hZ1 hs
    have hs' : QuotientGroup.mk' (Subgroup.center X) x⁻¹ ∈ Subgroup.normalizer
        ((A.map (QuotientGroup.mk' (Subgroup.center X)) : Subgroup (X ⧸ Subgroup.center X)) :
          Set (X ⧸ Subgroup.center X)) := by
      rw [map_inv]
      exact Subgroup.inv_mem _ hs
    have hsx' : ∀ a ∈ A, x⁻¹ * a * x⁻¹⁻¹ ∈ A :=
      conj_mem_of_mem_normalizer_quot h.isElemAbelian hZ1 hs'
    have hxA : x ∈ Subgroup.normalizer (A : Set X) := by
      rw [Subgroup.mem_normalizer_iff]
      intro g
      constructor
      · intro hg
        exact hsx g hg
      · intro hg
        have h' := hsx' _ hg
        have e : x⁻¹ * (x * g * x⁻¹) * x⁻¹⁻¹ = g := by group
        rw [e] at h'
        exact h'
    exact Subgroup.le_normalizer_map (QuotientGroup.mk' (Subgroup.center X))
      (Subgroup.mem_map_of_mem (QuotientGroup.mk' (Subgroup.center X)) (h.normalizer_le hxA))
  · set M := (Subgroup.centralizer ({c} : Set X)).map (QuotientGroup.mk' (Subgroup.center X))
      with hM
    set Q := Subgroup.centralizer ({QuotientGroup.mk c} : Set (X ⧸ Subgroup.center X))
      with hQ
    have hMQ : M ≤ Q := by
      rintro _ ⟨x, hx, rfl⟩
      rw [hQ, Subgroup.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      have key : QuotientGroup.mk' (Subgroup.center X) c *
          QuotientGroup.mk' (Subgroup.center X) x =
          QuotientGroup.mk' (Subgroup.center X) x * QuotientGroup.mk' (Subgroup.center X) c := by
        rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hx c (Set.mem_singleton c)]
      rw [hg]
      exact key
    have hfC : ∀ x ∈ Subgroup.centralizer ({c} : Set X),
        QuotientGroup.mk' (Subgroup.center X) x ∈ M := fun x hx => Subgroup.mem_map_of_mem _ hx
    have hfM : ∀ y ∈ M, ∃ x ∈ Subgroup.centralizer ({c} : Set X),
        QuotientGroup.mk' (Subgroup.center X) x = y := fun y hy => Subgroup.mem_map.mp hy
    have hMn : (M.subgroupOf Q).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      obtain ⟨x, hx, hxn⟩ := Subgroup.mem_map.mp hn
      obtain ⟨d, hd⟩ :=
        QuotientGroup.mk'_surjective (Subgroup.center X) (g : X ⧸ Subgroup.center X)
      have hdQ : QuotientGroup.mk' (Subgroup.center X) d ∈ Q := by
        rw [hd]
        exact g.2
      have hpm : QuotientGroup.mk' (Subgroup.center X) (d * x * d⁻¹) ∈ M :=
        Subgroup.mem_map_of_mem _ (conj_mem_centralizer_of_quot hdQ hx)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hd, ← hxn]
      simpa only [map_mul, map_inv] using hpm
    exact le_oTwoP_image (Subgroup.centralizer ({c} : Set X))
      (QuotientGroup.mk' (Subgroup.center X)) M Q hMQ hfC hfM hMn h.omega

theorem false_of_four_le_pRank (hX : RankHyp X) (hZ : ¬ 3 ∣ Nat.card (Subgroup.center X))
    {G : Type} [Group G] [Finite G] (e : X ⧸ Subgroup.center X ≃* G)
    (h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G)) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq := CFSG.SectionRank.pRank_quotient_eq (p := 3) (Subgroup.center X) hZ
  have he := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e
  have h3 := hX.rank_three
  omega

end Reduction

theorem InnerCase.of_rankHyp {P : (S : Type) → [Group S] → Prop}
    (h : ∀ (X : Type) [Group X] [Finite X], RankHyp X → P (X ⧸ Subgroup.center X) → False) :
    InnerCase P :=
  fun X _ _ hX _ _ _ _ hP => h X hX hP

theorem InnerData.of_mulEquiv {S T : Type} [Group S] [Group T] [Finite S] (e : S ≃* T)
    {A B : Subgroup S} {c : S} (h : InnerData S A B c) :
    InnerData T (A.map e.toMonoidHom) (B.map e.toMonoidHom) (e c) := by
  haveI : Finite T := Finite.of_surjective _ e.surjective
  have hinj : Function.Injective e.toMonoidHom := e.injective
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 e.toMonoidHom A
      h.isElemAbelian
  · rw [Subgroup.card_map_of_injective hinj, h.card_A]
  · exact Subgroup.map_mono h.le_B
  · rw [Subgroup.card_map_of_injective hinj, h.card_B]
  · rw [h.eq_sup, Subgroup.map_sup, MonoidHom.map_zpowers] <;> rfl
  · intro hmem
    obtain ⟨b, hb, hbc⟩ := Subgroup.mem_map.mp hmem
    have hbc' : b = c := by
      apply hinj
      simpa using hbc
    exact h.not_mem (by rw [← hbc']; exact hb)
  · rw [eq_bot_iff]
    rintro x ⟨hx, hxz⟩
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    have hac : a ∈ Subgroup.center S := by
      have hxz' : e.toMonoidHom a ∈ Subgroup.center T := hxz
      rw [Subgroup.mem_center_iff]
      intro g
      apply hinj
      show e (g * a) = e (a * g)
      rw [map_mul, map_mul]
      exact Subgroup.mem_center_iff.mp hxz' (e g)
    have h1 : a ∈ A ⊓ Subgroup.center S := ⟨ha, hac⟩
    rw [h.inf_center, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot, h1, map_one]
  · exact Sec8.Item812Res12.normalizer_map_le e h.normalizer_le
  · have hC : ∀ x ∈ Subgroup.centralizer ({c} : Set S),
        e x ∈ Subgroup.centralizer ({e c} : Set T) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff] at hx ⊢
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      rw [hg, ← map_mul, ← map_mul, hx c (Set.mem_singleton c)]
    have hS : ∀ y ∈ Subgroup.centralizer ({e c} : Set T),
        ∃ x ∈ Subgroup.centralizer ({c} : Set S), e x = y := by
      intro y hy
      refine ⟨e.symm y, ?_, by simp⟩
      rw [Subgroup.mem_centralizer_iff] at hy ⊢
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      rw [hg]
      apply e.injective
      simp only [map_mul, MulEquiv.apply_symm_apply]
      exact hy (e c) (Set.mem_singleton _)
    exact le_oTwoP_image (Subgroup.centralizer ({c} : Set S)) e.toMonoidHom
      (Subgroup.centralizer ({e c} : Set T)) (Subgroup.centralizer ({e c} : Set T)) le_rfl hC hS
      (by rw [Subgroup.subgroupOf_self]; infer_instance) h.omega

theorem NoInnerData.of_mulEquiv {S T : Type} [Group S] [Group T] [Finite S] (e : S ≃* T)
    (h : NoInnerData T) : NoInnerData S :=
  fun A B c hd => h _ _ _ (hd.of_mulEquiv e)

theorem noInnerData_of_noE27 {S : Type} [Group S] (h : NoE27 S) : NoInnerData S :=
  fun A _ _ hd => h A ⟨hd.isElemAbelian, hd.card_A⟩

theorem noE27_of_autNoE27 {S : Type} [Group S] (hZ : Subgroup.center S = ⊥) (h : AutNoE27 S) :
    NoE27 S := by
  intro D hD
  have hinj : Function.Injective (MulAut.conj : S →* MulAut S) :=
    Sec4.RonanK429.conj_injective_of_center_eq_bot hZ
  have hA : IsElemAbelian 3 (D.map (MulAut.conj : S →* MulAut S)) :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 (MulAut.conj : S →* MulAut S)
      D hD.1
  exact h (D.map (MulAut.conj : S →* MulAut S))
    ⟨hA, by rw [Subgroup.card_map_of_injective hinj, hD.2]⟩

theorem autNoE27_of_card_le_nine {S : Type} [Group S]
    (h : ∀ B : Subgroup (MulAut S), IsElemAbelian 3 B → Nat.card B ≤ 9) : AutNoE27 S := by
  intro A hA
  have := h A hA.1
  have := hA.2
  omega

@[expose] def NormIrred (S : Type) [Group S] : Prop :=
  ∀ E U : Subgroup S, IsE27 E → U ≤ E →
    Subgroup.normalizer (E : Set S) ≤ Subgroup.normalizer (U : Set S) → U = ⊥ ∨ U = E

theorem NormIrred.noInnerData {S : Type} [Group S] (h : NormIrred S) : NoInnerData S := by
  intro A B c hd
  rcases h A B ⟨hd.isElemAbelian, hd.card_A⟩ hd.le_B hd.normalizer_le with hB | hB
  · have := hd.card_B
    rw [hB, Subgroup.card_bot] at this
    omega
  · have := hd.card_B
    rw [hB, hd.card_A] at this
    omega

theorem NormIrred.of_mulEquiv {S T : Type} [Group S] [Group T] (e : S ≃* T) (h : NormIrred T) :
    NormIrred S := by
  intro E U hE hUE hN
  have hinj : Function.Injective e.toMonoidHom := e.injective
  rcases h (E.map e.toMonoidHom) (U.map e.toMonoidHom) (hE.map e)
      (Subgroup.map_mono hUE) (Sec8.Item812Res12.normalizer_map_le e hN) with hU | hU
  · left
    exact (Subgroup.map_eq_bot_iff_of_injective _ hinj).mp hU
  · right
    exact Subgroup.map_injective hinj hU

theorem NormIrred.of_sylowModel {H : Type} [Group H] [Finite H] {z : Fin 3 → H} {t s : H}
    (hf : WreathFacts z t) (hW : Nat.card (wreathW z t) = 3 ^ (Nat.card H).factorization 3)
    (h81 : Nat.card (wreathW z t) = 81)
    (hs : ∀ w : Fin 3 → ZMod 3, s * vecElt z w * s⁻¹ = vecElt z (sgnV w)) : NormIrred H :=
  fun E U hE hUE hN =>
    Sec8.Item812Res12.irred_of_model hf hW h81 hs hE.1 hE.2 hUE hN

theorem NormIrred.of_conjModel {H : Type} [Group H] {z : Fin 3 → H} {t s : H}
    (hf : WreathFacts z t)
    (hs : ∀ w : Fin 3 → ZMod 3, s * vecElt z w * s⁻¹ = vecElt z (sgnV w))
    (hconj : ∀ E : Subgroup H, IsE27 E →
      ∃ g : H, E = (baseA z).map (MulAut.conj g).toMonoidHom) : NormIrred H := by
  intro E U hE hUE hN
  obtain ⟨g, rfl⟩ := hconj E hE
  have hE' : ((baseA z).map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj g⁻¹).toMonoidHom = baseA z :=
    map_conj_map_conj_inv (baseA z) g
  have hinj : Function.Injective (MulAut.conj g⁻¹).toMonoidHom := (MulAut.conj g⁻¹).injective
  have hN' := Sec8.Item812Res12.normalizer_map_le (MulAut.conj g⁻¹ : H ≃* H) hN
  rw [hE'] at hN'
  have hU' : U.map (MulAut.conj g⁻¹).toMonoidHom ≤ baseA z :=
    (Subgroup.map_mono hUE).trans hE'.le
  rcases Sec8.Item812Res12.eq_bot_or_eq_baseA hf hs hU' hN' with h | h
  · left
    exact (Subgroup.map_eq_bot_iff_of_injective _ hinj).mp h
  · right
    rw [← hE'] at h
    exact Subgroup.map_injective hinj h

theorem InnerCase.of_autNoE27 {P : (S : Type) → [Group S] → Prop}
    (h : ∀ (S : Type) [Group S] [Finite S], P S → AutNoE27 S) : InnerCase P := by
  intro X _ _ hX A B c hd hP
  exact noInnerData_of_noE27 (noE27_of_autNoE27 (center_quotient_eq_bot hX) (h _ hP)) _ _ _
    (hd.quotient hX)

theorem noE27_of_openPRank_le_two {S : Type} [Group S] [Finite S]
    (h : CFSG.Open.pRank 3 (⊤ : Subgroup S) ≤ 2) : NoE27 S := by
  intro D hD
  have h' : CFSG.pRank 3 S ≤ 2 := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top]; exact h
  exact Sec4.Item434Spor.noE27_of_pRank_le_two h' D hD.1 hD.2

theorem autNoE27_of_mulEquiv {S T : Type} [Group S] [Group T] (e : S ≃* T) (h : AutNoE27 T) :
    AutNoE27 S := AutNoE27.of_mulEquiv e h

theorem noE27_of_mulEquiv {S T : Type} [Group S] [Group T] (e : S ≃* T) (h : NoE27 T) :
    NoE27 S := Sec4.RonanK429.NoE27.of_mulEquiv e h

theorem isSolvable_oTwoP {H : Type} [Group H] [Finite H] : IsSolvable (Sec4.oTwoP 3 H) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP2 : IsPGroup 2 (CFSG.pCore 2 H) := CFSG.pCore_isPGroup
  have hP3 : IsPGroup 3 (CFSG.pCore 3 (H ⧸ CFSG.pCore 2 H)) := CFSG.pCore_isPGroup
  haveI : Group.IsNilpotent (CFSG.pCore 2 H) := hP2.isNilpotent
  haveI : Group.IsNilpotent (CFSG.pCore 3 (H ⧸ CFSG.pCore 2 H)) := hP3.isNilpotent
  have hPO : CFSG.pCore 2 H ≤ Sec4.oTwoP 3 H := Sec4.pCore_two_le_oTwoP 3 H
  let φ : ↥(Sec4.oTwoP 3 H) →* ↥(CFSG.pCore 3 (H ⧸ CFSG.pCore 2 H)) :=
    ((QuotientGroup.mk' (CFSG.pCore 2 H)).comp (Sec4.oTwoP 3 H).subtype).codRestrict _
      (fun x => x.2)
  refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hPO) φ ?_
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 H) (x : H) = 1 := congrArg Subtype.val hx
  exact MonoidHom.mem_range.mpr ⟨⟨(x : H), (QuotientGroup.eq_one_iff (x : H)).mp h1⟩, rfl⟩

theorem oTwoP_le_centralizer_of_simple_normal {H : Type} [Group H] [Finite H] (N : Subgroup H)
    [N.Normal] (hN : IsSimpleGroup N) (hna : ¬ ∀ x y : N, x * y = y * x) :
    Sec4.oTwoP 3 H ≤ Subgroup.centralizer (N : Set H) := by
  haveI : IsSimpleGroup N := hN
  haveI : Group.IsSolvable (Sec4.oTwoP 3 H) := isSolvable_oTwoP
  haveI hOn : (Sec4.oTwoP 3 H).Normal := oTwoP_normal_aux 3 H
  haveI hK : ((Sec4.oTwoP 3 H).subgroupOf N).Normal := inferInstance
  intro o ho
  rw [Subgroup.mem_centralizer_iff]
  intro n hn
  have hnN : n ∈ N := hn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Sec4.oTwoP 3 H).subgroupOf N) with
    hK1 | hK1
  · have hcO : o * n * o⁻¹ * n⁻¹ ∈ Sec4.oTwoP 3 H := by
      have h1 : n * o⁻¹ * n⁻¹ ∈ Sec4.oTwoP 3 H :=
        hOn.conj_mem _ ((Sec4.oTwoP 3 H).inv_mem ho) n
      have e : o * n * o⁻¹ * n⁻¹ = o * (n * o⁻¹ * n⁻¹) := by group
      rw [e]
      exact (Sec4.oTwoP 3 H).mul_mem ho h1
    have hcN : o * n * o⁻¹ * n⁻¹ ∈ N :=
      N.mul_mem (‹N.Normal›.conj_mem _ hnN o) (N.inv_mem hnN)
    have hmem : (⟨o * n * o⁻¹ * n⁻¹, hcN⟩ : N) ∈ (Sec4.oTwoP 3 H).subgroupOf N :=
      Subgroup.mem_subgroupOf.mpr hcO
    rw [hK1, Subgroup.mem_bot] at hmem
    have hc1 : o * n * o⁻¹ * n⁻¹ = 1 := congrArg Subtype.val hmem
    have h1 : o * n * o⁻¹ = n := mul_inv_eq_one.mp hc1
    calc n * o = o * n * o⁻¹ * o := by rw [h1]
      _ = o * n := by group
  · exfalso
    have hsub : ∀ m : N, (m : H) ∈ Sec4.oTwoP 3 H := fun m => by
      have hm : m ∈ (Sec4.oTwoP 3 H).subgroupOf N := by
        rw [hK1]
        exact Subgroup.mem_top m
      exact Subgroup.mem_subgroupOf.mp hm
    let f : N →* ↥(Sec4.oTwoP 3 H) := N.subtype.codRestrict (Sec4.oTwoP 3 H) hsub
    have hf : Function.Injective f := by
      intro a b hab
      have h' := congrArg Subtype.val hab
      exact Subtype.ext h'
    haveI : Group.IsSolvable N := Group.isSolvable_of_isSolvable_injective hf
    exact hna ((IsSimpleGroup.comm_iff_isSolvable).mpr inferInstance)

@[expose] def SylowSignModel (H : Type) [Group H] [Finite H] : Prop :=
  ∃ (z : Fin 3 → H) (t s : H), WreathFacts z t ∧
    Nat.card (wreathW z t) = 3 ^ (Nat.card H).factorization 3 ∧ Nat.card (wreathW z t) = 81 ∧
    ∀ w : Fin 3 → ZMod 3, s * vecElt z w * s⁻¹ = vecElt z (sgnV w)

theorem NormIrred.of_sylowSignModel {H : Type} [Group H] [Finite H] (h : SylowSignModel H) :
    NormIrred H := by
  obtain ⟨z, t, s, hf, hW, h81, hs⟩ := h
  exact NormIrred.of_sylowModel hf hW h81 hs

@[expose] def ConjSignModel (H : Type) [Group H] : Prop :=
  ∃ (z : Fin 3 → H) (t s : H), WreathFacts z t ∧
    (∀ w : Fin 3 → ZMod 3, s * vecElt z w * s⁻¹ = vecElt z (sgnV w)) ∧
    ∀ E : Subgroup H, IsE27 E → ∃ g : H, E = (baseA z).map (MulAut.conj g).toMonoidHom

theorem NormIrred.of_conjSignModel {H : Type} [Group H] (h : ConjSignModel H) : NormIrred H := by
  obtain ⟨z, t, s, hf, hs, hconj⟩ := h
  exact NormIrred.of_conjModel hf hs hconj

end CFSG.RankThree.PartTwo.Sec18.Item185Proof
