module

public import CFSG.RankThree.PartTwo.Sec21.HeringSec217OutJ3
public import CFSG.RankThree.PartTwo.Sec21.Item2119End6ProofRank
public import CFSG.RankThree.PartTwo.Sec21.HeringSec217NoCycle
public import CFSG.RankThree.PartTwo.Sec21.HeringSec217OutAux

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec21 CFSG.Blueprint

structure CoverOut {G : Type} [Group G] [Finite G] (A E U : Subgroup G) (c : G)
    (L : Subgroup G) : Prop where
  pair : Sec21Pair G A E U c L
  quot : Nonempty (L ⧸ Subgroup.center L ≃* NativeSporadic.J3)
  notMem : c ∉ L
  card : Nat.card A = 3 ^ 4
  ext : Sec4.IsExtOf ↥(starOf A L) (Multiplicative (ZMod 8)) (Multiplicative (ZMod 3 × ZMod 3))

section Basic

variable {G : Type} [Group G] [Finite G] {A E U : Subgroup G} {c : G} {L : Subgroup G}

theorem CoverOut.c_mem_A (h : CoverOut A E U c L) : c ∈ A :=
  h.pair.mem_E.2 (mem_lThreeStarPairs_iff.mp h.pair.mem_pair).1.1

theorem CoverOut.c_ne_one (h : CoverOut A E U c L) : c ≠ 1 :=
  (mem_lThreeStarPairs_iff.mp h.pair.mem_pair).2.1

theorem CoverOut.isElemAbelian_A (h : CoverOut A E U c L) : CFSG.Assembly.IsElemAbelian 3 A :=
  h.pair.mem_S.1.1

theorem CoverOut.maximal (h : CoverOut A E U c L) :
    ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → A ≤ B → B = A :=
  h.pair.mem_S.1.2.1

theorem CoverOut.mem_thetaComponentsAt (h : CoverOut A E U c L) : L ∈ thetaComponentsAt 3 c :=
  (lZeroStarAt_subset A c) (mem_lThreeStarPairs_iff.mp h.pair.mem_pair).2.2.1

theorem CoverOut.c_comm (h : CoverOut A E U c L) : ∀ x ∈ L, c * x = x * c := by
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  intro x hx
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hLc hx)).symm

theorem CoverOut.perfect (h : CoverOut A E U c L) : Group.IsPerfect ↥L :=
  Sec6.isPerfect_of_mem_thetaComponentsAt h.mem_thetaComponentsAt

theorem CoverOut.c_cubed (h : CoverOut A E U c L) : c ^ 3 = 1 :=
  h.isElemAbelian_A.2 c h.c_mem_A

theorem CoverOut.A_le_normalizer (h45 : Sec4.Item4_5) (h : CoverOut A E U c L) :
    A ≤ Subgroup.normalizer (L : Set G) :=
  Sec6.le_normalizer_of_mem_thetaComponentsAt h45 h.pair.standing.toTheoremFourHyp
    h.isElemAbelian_A h.c_mem_A h.c_ne_one L h.mem_thetaComponentsAt

theorem CoverOut.localRank_le (h : CoverOut A E U c L) :
    CFSG.Assembly.RankThreeEven.localRank 3 G ≤ 3 :=
  h.pair.standing.toTheoremFourHyp.localRank_three.le

end Basic


theorem prime_eq_three_aux {X : Type*} [Group X] [Finite X] (hperf : Group.IsPerfect X)
    {Q : Type*} [Group Q] [IsSimpleGroup Q] (e : X ⧸ center X ≃* Q)
    (hodd : Odd (Nat.card (center X)))
    (hcyc : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → p ≠ 3 → ∀ S : Subgroup Q, IsPGroup p S →
      IsCyclic S) {p : ℕ} (hp : p.Prime) (hpd : p ∣ Nat.card (center X)) : p = 3 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨π, hπs, hπker⟩ : ∃ π : X →* Q, Function.Surjective π ∧ π.ker = center X :=
    ⟨e.toMonoidHom.comp (QuotientGroup.mk' (center X)),
      e.surjective.comp (QuotientGroup.mk'_surjective _), by
        ext x
        simp [MonoidHom.mem_ker, QuotientGroup.eq_one_iff]⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpd
  have hxc : (x : X) ∈ center X := x.2
  have hxo : orderOf (x : X) = p := by rw [Subgroup.orderOf_coe]; exact hx
  by_contra hp3
  by_cases hp2 : p = 2
  · subst hp2
    have h2d : 2 ∣ Nat.card (center X) := hpd
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2d)
  · have := eq_one_of_mem_center_of_cyclic_quotient hperf π hπker.le
      (fun S hS => hcyc p hp2 hp3 S hS) hxc hxo
    rw [this, orderOf_one] at hxo
    exact hp.one_lt.ne hxo

section Center


set_option linter.unusedSectionVars false

theorem isQuasisimple_of_perfect_J3 {X : Type} [Group X] (hp : Group.IsPerfect X)
    (e : X ⧸ center X ≃* NativeSporadic.J3) : CFSG.IsQuasisimple X := by
  have hs : IsSimpleGroup NativeSporadic.J3 := CFSG.Sporadic.J3.isSimpleGroup_J3
  have hsq : IsSimpleGroup (X ⧸ center X) := @MulEquiv.isSimpleGroup _ _ _ _ hs e
  refine ⟨hp, hsq, ?_⟩
  by_contra hcon
  push Not at hcon
  have hcomm : ∀ a b : NativeSporadic.J3, a * b = b * a := by
    intro a b
    obtain ⟨a', rfl⟩ := e.surjective a
    obtain ⟨b', rfl⟩ := e.surjective b
    rw [← map_mul, ← map_mul, hcon a' b']
  exact not_isSolvable_J3 (Group.isSolvable_of_comm hcomm)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
theorem prime_eq_three_of_dvd_card_center {X : Type} [Group X] [Finite X]
    (hperf : Group.IsPerfect X) (e : X ⧸ center X ≃* NativeSporadic.J3) {p : ℕ} (hp : p.Prime)
    (hpd : p ∣ Nat.card (center X)) : p = 3 := by
  have hs : IsSimpleGroup NativeSporadic.J3 := CFSG.Sporadic.J3.isSimpleGroup_J3
  have hodd : Odd (Nat.card (center X)) :=
    CFSG.ComponentClassification.RankTwoSporadic.oddMultiplier_of_noPerfectDoubleCover
      CFSG.Sporadic.Recognition.J3Multiplier.noPerfectDoubleCover_nativeJ3_of_certificate
      X (Group.isPerfect_def.1 hperf) ⟨e⟩
  have hcyc : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → p ≠ 3 → ∀ S : Subgroup NativeSporadic.J3,
      IsPGroup p S → IsCyclic S := fun p _ h2 h3 S hS => isCyclic_of_isPGroup_J3 h2 h3 S hS
  exact @prime_eq_three_aux X _ _ hperf NativeSporadic.J3 _ hs e hodd hcyc p hp hpd

theorem isPGroup_three_center {X : Type} [Group X] [Finite X] (hperf : Group.IsPerfect X)
    (e : X ⧸ center X ≃* NativeSporadic.J3) : IsPGroup 3 (center X) := by
  have hpos : Nat.card (center X) ≠ 0 := Nat.card_pos.ne'
  exact IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd hpos
    (fun {d} hd hdd => prime_eq_three_of_dvd_card_center hperf e hd hdd))

end Center

theorem mem_normalizer_map_center {G : Type} [Group G] [Finite G] {L : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G)) :
    x ∈ Subgroup.normalizer (((center ↥L).map L.subtype : Subgroup G) : Set G) := by
  refine mem_normalizer_of_forall_conj_mem fun g hg => ?_
  obtain ⟨z, hz, rfl⟩ := hg
  have hxz : x * (z : G) * x⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hx z).1 z.2
  refine ⟨⟨x * (z : G) * x⁻¹, hxz⟩, ?_, rfl⟩
  change (⟨x * (z : G) * x⁻¹, hxz⟩ : ↥L) ∈ center ↥L
  rw [Subgroup.mem_center_iff]
  intro l
  apply Subtype.ext
  have hl : x⁻¹ * (l : G) * x ∈ L := by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hx) l).1 l.2
    simpa using this
  have hzc : (z : G) * (x⁻¹ * (l : G) * x) = (x⁻¹ * (l : G) * x) * z := by
    have := Subgroup.mem_center_iff.1 hz ⟨_, hl⟩
    exact (congrArg Subtype.val this).symm
  show (l : G) * (x * (z : G) * x⁻¹) = x * (z : G) * x⁻¹ * (l : G)
  calc (l : G) * (x * (z : G) * x⁻¹) = x * (x⁻¹ * (l : G) * x) * (z : G) * x⁻¹ := by group
    _ = x * ((x⁻¹ * (l : G) * x) * (z : G)) * x⁻¹ := by group
    _ = x * ((z : G) * (x⁻¹ * (l : G) * x)) * x⁻¹ := by rw [hzc]
    _ = x * (z : G) * x⁻¹ * (l : G) := by group


section ZeroCenter

variable {G : Type} [Group G] [Finite G] {A E U : Subgroup G} {c : G} {L : Subgroup G}


set_option linter.unusedSectionVars false

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem CoverOut.center_eq_bot (h45 : Sec4.Item4_5) (h : CoverOut A E U c L) :
    Subgroup.center L = ⊥ := by
  obtain ⟨e⟩ := h.quot
  have hperf := h.perfect
  have hq := isQuasisimple_of_perfect_J3 hperf e
  have hZp := isPGroup_three_center hperf e
  have hdvd := CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest.card_center_dvd_three_of_J3 hq hZp e
  by_contra hne
  have hZ3 : Nat.card (center ↥L) = 3 := by
    have h1 : Nat.card (center ↥L) ≠ 1 := fun h1 => hne (Subgroup.card_eq_one.1 h1)
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1' | h3
    · exact absurd h1' h1
    · exact h3
  set Z' : Subgroup G := (center ↥L).map L.subtype with hZ'
  have hZ'card : Nat.card Z' = 3 := by
    rw [hZ', Subgroup.card_map_of_injective L.subtype_injective, hZ3]
  have hAN := h.A_le_normalizer h45
  have hAZ : A ≤ Subgroup.normalizer (Z' : Set G) := fun x hx => mem_normalizer_map_center (hAN hx)
  have hApg : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using h.isElemAbelian_A.2 g g.2)⟩
  obtain ⟨b, hbZ', hb1, hbA⟩ := Item2113Res3Proof.exists_fixed_of_isPGroup hApg hAZ
    (by rw [hZ'card])
  obtain ⟨zb, hzb, rfl⟩ := hbZ'
  have hb3 : (zb : G) ^ 3 = 1 := by
    have := pow_card_eq_one' (G := ↥(center ↥L)) (x := ⟨zb, hzb⟩)
    rw [hZ3] at this
    have := congrArg (fun x : ↥(center ↥L) => (x : ↥L)) this
    have := congrArg (fun x : ↥L => (x : G)) this
    simpa using this
  have hbc : ∀ x ∈ A, x * (zb : G) = (zb : G) * x := by
    intro x hx
    have this : x * (zb : G) * x⁻¹ = (zb : G) := hbA x hx
    calc x * (zb : G) = x * (zb : G) * x⁻¹ * x := by group
      _ = (zb : G) * x := by rw [this]
  have hbmem : (zb : G) ∈ A := by
    have hAe := h.isElemAbelian_A
    have hbe : CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers (zb : G)) := isElemAbelian_zpowers hb3
    have hsup : CFSG.Assembly.IsElemAbelian 3 (A ⊔ Subgroup.zpowers (zb : G)) :=
      isElemAbelian_sup_of_commute hAe hbe (by
        intro a ha t ht
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht
        exact ((show Commute a (zb : G) from hbc a ha).zpow_right i).eq)
    have := h.maximal _ hsup le_sup_left
    rw [← this]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  set D : Subgroup G := Subgroup.zpowers (zb : G) ⊔ Subgroup.zpowers c with hD
  have hc3 := h.c_cubed
  have hcb : c * (zb : G) = (zb : G) * c := h.c_comm zb zb.2
  have hDe : CFSG.Assembly.IsElemAbelian 3 D :=
    isElemAbelian_sup_of_commute (isElemAbelian_zpowers hb3) (isElemAbelian_zpowers hc3) (by
      intro x hx y hy
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      exact (((show Commute (zb : G) c from hcb.symm).zpow_zpow i j).eq))
  have hDC : ∀ d ∈ D, ∀ x ∈ L, d * x = x * d := by
    have hle : D ≤ Subgroup.centralizer (L : Set G) := by
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        intro x hx
        exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hzb ⟨x, hx⟩)
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        intro x hx
        exact (h.c_comm x hx).symm
    intro d hd x hx
    exact (Subgroup.mem_centralizer_iff.1 (hle hd) x hx).symm
  have hdisj : Disjoint (Subgroup.zpowers (zb : G)) (Subgroup.zpowers c) := by
    rw [Subgroup.disjoint_def]
    intro x hxb hxc
    rcases mem_zpowers_of_pow_three hc3 hxc with h1 | h1 | h1
    · exact h1
    · exfalso
      apply h.notMem
      rw [← h1]
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hxb
      rw [← hi]
      exact L.zpow_mem zb.2 i
    · exfalso
      apply h.notMem
      have hcx : c = x ^ 2 := by
        rw [h1]
        have : (c ^ 2) ^ 2 = c ^ 3 * c := by group
        rw [this, hc3, one_mul]
      rw [hcx]
      exact L.pow_mem (by
        obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hxb
        rw [← hi]
        exact L.zpow_mem zb.2 i) 2
  have hD9 : 9 ≤ Nat.card D := by
    have := card_mul_le_card_sup_of_disjoint (Subgroup.zpowers (zb : G)) (Subgroup.zpowers c) hdisj
    have hob : orderOf (zb : G) = 3 := orderOf_eq_prime hb3 hb1
    have hoc : orderOf c = 3 := orderOf_eq_prime hc3 h.c_ne_one
    rw [Nat.card_zpowers, Nat.card_zpowers, hob, hoc] at this
    rw [hD]
    omega
  obtain ⟨a, y, W, ha, ha3, hy3, hy1, hay, hyD, hW0, hW2, haW, hyN⟩ :=
    exists_local_frame_cover hq hZ3 e
  exact false_of_frame_big_abelian a y W ha ha3 hy3 hy1 hay hyD hW0 hW2 haW hyN D hDe hDC hD9
    h.localRank_le

end ZeroCenter


section Components

variable {G : Type} [Group G] (A L : Subgroup G)

def projL : Subgroup G where
  carrier := {l | l ∈ L ∧ ∃ w ∈ Subgroup.centralizer (L : Set G), l * w ∈ A}
  one_mem' := ⟨L.one_mem, 1, Subgroup.one_mem _, by simpa using A.one_mem⟩
  mul_mem' := by
    rintro l₁ l₂ ⟨hl1, w₁, hw1, h1⟩ ⟨hl2, w₂, hw2, h2⟩
    refine ⟨L.mul_mem hl1 hl2, w₁ * w₂, Subgroup.mul_mem _ hw1 hw2, ?_⟩
    have hc : l₂ * w₁ = w₁ * l₂ := (Subgroup.mem_centralizer_iff.1 hw1) _ hl2
    have : l₁ * l₂ * (w₁ * w₂) = l₁ * w₁ * (l₂ * w₂) := by
      calc l₁ * l₂ * (w₁ * w₂) = l₁ * (l₂ * w₁) * w₂ := by group
        _ = l₁ * (w₁ * l₂) * w₂ := by rw [hc]
        _ = l₁ * w₁ * (l₂ * w₂) := by group
    rw [this]
    exact A.mul_mem h1 h2
  inv_mem' := by
    rintro l ⟨hl, w, hw, h1⟩
    refine ⟨L.inv_mem hl, w⁻¹, Subgroup.inv_mem _ hw, ?_⟩
    have hc : l * w = w * l := (Subgroup.mem_centralizer_iff.1 hw) _ hl
    have hc' : l⁻¹ * w⁻¹ = (l * w)⁻¹ := by
      calc l⁻¹ * w⁻¹ = (w * l)⁻¹ := by rw [mul_inv_rev]
        _ = (l * w)⁻¹ := by rw [hc]
    rw [hc']
    exact A.inv_mem h1

def projC : Subgroup G where
  carrier := {w | w ∈ Subgroup.centralizer (L : Set G) ∧ ∃ l ∈ L, l * w ∈ A}
  one_mem' := ⟨Subgroup.one_mem _, 1, L.one_mem, by simpa using A.one_mem⟩
  mul_mem' := by
    rintro w₁ w₂ ⟨hw1, l₁, hl1, h1⟩ ⟨hw2, l₂, hl2, h2⟩
    refine ⟨Subgroup.mul_mem _ hw1 hw2, l₁ * l₂, L.mul_mem hl1 hl2, ?_⟩
    have hc : l₂ * w₁ = w₁ * l₂ := (Subgroup.mem_centralizer_iff.1 hw1) _ hl2
    have : l₁ * l₂ * (w₁ * w₂) = l₁ * w₁ * (l₂ * w₂) := by
      calc l₁ * l₂ * (w₁ * w₂) = l₁ * (l₂ * w₁) * w₂ := by group
        _ = l₁ * (w₁ * l₂) * w₂ := by rw [hc]
        _ = l₁ * w₁ * (l₂ * w₂) := by group
    rw [this]
    exact A.mul_mem h1 h2
  inv_mem' := by
    rintro w ⟨hw, l, hl, h1⟩
    refine ⟨Subgroup.inv_mem _ hw, l⁻¹, L.inv_mem hl, ?_⟩
    have hc : l * w = w * l := (Subgroup.mem_centralizer_iff.1 hw) _ hl
    have hc' : l⁻¹ * w⁻¹ = (l * w)⁻¹ := by
      calc l⁻¹ * w⁻¹ = (w * l)⁻¹ := by rw [mul_inv_rev]
        _ = (l * w)⁻¹ := by rw [hc]
    rw [hc']
    exact A.inv_mem h1

variable {A L}

theorem projL_le : projL A L ≤ L := fun _ hl => hl.1

theorem projC_le : projC A L ≤ Subgroup.centralizer (L : Set G) := fun _ hw => hw.1

theorem projL_commute_projC : ∀ l ∈ projL A L, ∀ w ∈ projC A L, l * w = w * l :=
  fun l hl w hw => (Subgroup.mem_centralizer_iff.1 hw.1 l hl.1)

theorem commute_components (hLC : L ⊓ Subgroup.centralizer (L : Set G) = ⊥) {l₁ l₂ w₁ w₂ : G}
    (hl₁ : l₁ ∈ L) (hl₂ : l₂ ∈ L) (hw₁ : w₁ ∈ Subgroup.centralizer (L : Set G))
    (hw₂ : w₂ ∈ Subgroup.centralizer (L : Set G))
    (hcomm : l₁ * w₁ * (l₂ * w₂) = l₂ * w₂ * (l₁ * w₁)) : l₁ * l₂ = l₂ * l₁ := by
  have c12 : l₂ * w₁ = w₁ * l₂ := (Subgroup.mem_centralizer_iff.1 hw₁) _ hl₂
  have c21 : l₁ * w₂ = w₂ * l₁ := (Subgroup.mem_centralizer_iff.1 hw₂) _ hl₁
  have h1 : l₁ * l₂ * (w₁ * w₂) = l₂ * l₁ * (w₂ * w₁) := by
    calc l₁ * l₂ * (w₁ * w₂) = l₁ * (l₂ * w₁) * w₂ := by group
      _ = l₁ * (w₁ * l₂) * w₂ := by rw [c12]
      _ = l₁ * w₁ * (l₂ * w₂) := by group
      _ = l₂ * w₂ * (l₁ * w₁) := hcomm
      _ = l₂ * (w₂ * l₁) * w₁ := by group
      _ = l₂ * (l₁ * w₂) * w₁ := by rw [c21]
      _ = l₂ * l₁ * (w₂ * w₁) := by group
  have hmemL : (l₂ * l₁)⁻¹ * (l₁ * l₂) ∈ L :=
    L.mul_mem (L.inv_mem (L.mul_mem hl₂ hl₁)) (L.mul_mem hl₁ hl₂)
  have heq : (l₂ * l₁)⁻¹ * (l₁ * l₂) = (w₂ * w₁) * (w₁ * w₂)⁻¹ := by
    calc (l₂ * l₁)⁻¹ * (l₁ * l₂) = (l₂ * l₁)⁻¹ * (l₁ * l₂ * (w₁ * w₂)) * (w₁ * w₂)⁻¹ := by group
      _ = (l₂ * l₁)⁻¹ * (l₂ * l₁ * (w₂ * w₁)) * (w₁ * w₂)⁻¹ := by rw [h1]
      _ = (w₂ * w₁) * (w₁ * w₂)⁻¹ := by group
  have hmemC : (w₂ * w₁) * (w₁ * w₂)⁻¹ ∈ Subgroup.centralizer (L : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hw₂ hw₁) (Subgroup.inv_mem _ (Subgroup.mul_mem _ hw₁ hw₂))
  have hbot : (l₂ * l₁)⁻¹ * (l₁ * l₂) ∈ L ⊓ Subgroup.centralizer (L : Set G) :=
    ⟨hmemL, heq ▸ hmemC⟩
  rw [hLC, Subgroup.mem_bot, inv_mul_eq_one] at hbot
  exact hbot.symm

theorem commute_components' (hLC : L ⊓ Subgroup.centralizer (L : Set G) = ⊥) {l₁ l₂ w₁ w₂ : G}
    (hl₁ : l₁ ∈ L) (hl₂ : l₂ ∈ L) (hw₁ : w₁ ∈ Subgroup.centralizer (L : Set G))
    (hw₂ : w₂ ∈ Subgroup.centralizer (L : Set G))
    (hcomm : l₁ * w₁ * (l₂ * w₂) = l₂ * w₂ * (l₁ * w₁)) : w₁ * w₂ = w₂ * w₁ := by
  have h := commute_components hLC hl₁ hl₂ hw₁ hw₂ hcomm
  have c12 : l₂ * w₁ = w₁ * l₂ := (Subgroup.mem_centralizer_iff.1 hw₁) _ hl₂
  have c21 : l₁ * w₂ = w₂ * l₁ := (Subgroup.mem_centralizer_iff.1 hw₂) _ hl₁
  have h1 : l₁ * l₂ * (w₁ * w₂) = l₂ * l₁ * (w₂ * w₁) := by
    calc l₁ * l₂ * (w₁ * w₂) = l₁ * (l₂ * w₁) * w₂ := by group
      _ = l₁ * (w₁ * l₂) * w₂ := by rw [c12]
      _ = l₁ * w₁ * (l₂ * w₂) := by group
      _ = l₂ * w₂ * (l₁ * w₁) := hcomm
      _ = l₂ * (w₂ * l₁) * w₁ := by group
      _ = l₂ * (l₁ * w₂) * w₁ := by rw [c21]
      _ = l₂ * l₁ * (w₂ * w₁) := by group
  rw [h] at h1
  exact mul_left_cancel h1

theorem cube_components (hLC : L ⊓ Subgroup.centralizer (L : Set G) = ⊥) {l w : G} (hl : l ∈ L)
    (hw : w ∈ Subgroup.centralizer (L : Set G)) (h3 : (l * w) ^ 3 = 1) : l ^ 3 = 1 ∧ w ^ 3 = 1 := by
  have hc : Commute l w := (Subgroup.mem_centralizer_iff.1 hw) _ hl
  rw [hc.mul_pow] at h3
  have hmemL : l ^ 3 ∈ L := L.pow_mem hl 3
  have hmemC : l ^ 3 ∈ Subgroup.centralizer (L : Set G) := by
    have : l ^ 3 = (w ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left h3
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hw 3)
  have hbot : l ^ 3 ∈ L ⊓ Subgroup.centralizer (L : Set G) := ⟨hmemL, hmemC⟩
  rw [hLC, Subgroup.mem_bot] at hbot
  rw [hbot, one_mul] at h3
  exact ⟨hbot, h3⟩


set_option maxRecDepth 20000 in
theorem card_inf_eq_of_components {c : G} (hLC : L ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    (hAe : CFSG.Assembly.IsElemAbelian 3 A)
    (hmax : ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → A ≤ B → B = A)
    (hdec : ∀ x ∈ A, ∃ l ∈ L, ∃ w ∈ Subgroup.centralizer (L : Set G), x = l * w)
    (hcA : c ∈ A) (hcC : c ∈ Subgroup.centralizer (L : Set G)) (hc1 : c ≠ 1)
    [Finite G] (h81 : Nat.card A = 3 ^ 4)
    (hbound : ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B →
      (∀ d ∈ B, ∀ x ∈ L, d * x = x * d) → Nat.card B < 9) :
    Nat.card (A ⊓ L : Subgroup G) = 27 ∧
      ∀ x ∈ A, ∃ l ∈ (A ⊓ L : Subgroup G), ∃ i : ℤ, x = l * c ^ i := by
  have hAe' := isElemAbelian_iff.1 hAe
  have hPL : CFSG.Assembly.IsElemAbelian 3 (projL A L) := by
    rw [isElemAbelian_iff]
    refine ⟨?_, ?_⟩
    · rintro l₁ ⟨hl₁, w₁, hw₁, h₁⟩ l₂ ⟨hl₂, w₂, hw₂, h₂⟩
      exact commute_components hLC hl₁ hl₂ hw₁ hw₂ (hAe'.1 _ h₁ _ h₂)
    · rintro l ⟨hl, w, hw, h₁⟩
      exact (cube_components hLC hl hw (hAe'.2 _ h₁)).1
  have hPC : CFSG.Assembly.IsElemAbelian 3 (projC A L) := by
    rw [isElemAbelian_iff]
    refine ⟨?_, ?_⟩
    · rintro w₁ ⟨hw₁, l₁, hl₁, h₁⟩ w₂ ⟨hw₂, l₂, hl₂, h₂⟩
      exact commute_components' hLC hl₁ hl₂ hw₁ hw₂ (hAe'.1 _ h₁ _ h₂)
    · rintro w ⟨hw, l, hl, h₁⟩
      exact (cube_components hLC hl hw (hAe'.2 _ h₁)).2
  have hbot : projL A L ⊓ projC A L = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ L ⊓ Subgroup.centralizer (L : Set G) := ⟨projL_le hx.1, projC_le hx.2⟩
    rwa [hLC] at this
  have hsup := Item2119End6Proof.isElemAbelian_sup_of_commute hPL hPC projL_commute_projC hbot
  have hAle : A ≤ projL A L ⊔ projC A L := by
    intro x hx
    obtain ⟨l, hl, w, hw, rfl⟩ := hdec x hx
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hl, w, hw, hx⟩)
      (Subgroup.mem_sup_right ⟨hw, l, hl, hx⟩)
  have hAeq : projL A L ⊔ projC A L = A := hmax _ hsup.1 hAle
  have hcardA : Nat.card A = Nat.card (projL A L) * Nat.card (projC A L) := by
    have := hsup.2
    rwa [hAeq] at this
  have hPLA : projL A L ≤ A := le_trans le_sup_left hAeq.le
  have hinf : A ⊓ L = projL A L := by
    apply le_antisymm
    · rintro x ⟨hxA, hxL⟩
      exact ⟨hxL, 1, Subgroup.one_mem _, by simpa using hxA⟩
    · exact le_inf hPLA projL_le
  have hcPC : c ∈ projC A L := ⟨hcC, 1, L.one_mem, by simpa using hcA⟩
  have hPC9 : Nat.card (projC A L) < 9 :=
    hbound _ hPC fun d hd x hx => (Subgroup.mem_centralizer_iff.1 (projC_le hd) x hx).symm
  obtain ⟨k, hk⟩ := isElemAbelian_card_eq_pow hPC
  have hk1 : 1 ≤ k := by
    by_contra hk0
    have hk0' : k = 0 := by omega
    rw [hk0', pow_zero] at hk
    have : projC A L = ⊥ := Subgroup.card_eq_one.1 hk
    have h1 : c ∈ (⊥ : Subgroup G) := this ▸ hcPC
    exact hc1 (Subgroup.mem_bot.1 h1)
  have hk1' : k = 1 := by
    by_contra hne
    have : 3 ^ 2 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rw [hk1', pow_one] at hk
  rw [hk, h81] at hcardA
  refine ⟨by rw [hinf]; omega, ?_⟩
  have hc3 : c ^ 3 = 1 := hAe'.2 c hcA
  have hoc : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hPCeq : projC A L = Subgroup.zpowers c := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hcPC) ?_).symm
    rw [hk, Nat.card_zpowers, hoc]
  intro x hx
  obtain ⟨l, hl, w, hw, rfl⟩ := hdec x hx
  have hlP : l ∈ projL A L := ⟨hl, w, hw, hx⟩
  have hwP : w ∈ projC A L := ⟨hw, l, hl, hx⟩
  rw [hPCeq] at hwP
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hwP
  exact ⟨l, ⟨hPLA hlP, hl⟩, i, rfl⟩

end Components


section Card

variable {G : Type} [Group G] [Finite G] {A E U : Subgroup G} {c : G} {L : Subgroup G}


set_option linter.unusedSectionVars false

@[expose] noncomputable def CoverOut.equivJ3 (h : CoverOut A E U c L) (hZ : Subgroup.center L = ⊥) :
    ↥L ≃* NativeSporadic.J3 :=
  QuotientGroup.quotientBot.symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hZ).symm.trans h.quot.some)

theorem CoverOut.exists_decomp (h45 : Sec4.Item4_5) (h : CoverOut A E U c L) {x : G} (hx : x ∈ A) :
    ∃ l ∈ L, ∃ w ∈ Subgroup.centralizer (L : Set G), x = l * w := by
  obtain ⟨e⟩ := h.quot
  have hxN : x ∈ Subgroup.normalizer (L : Set G) := h.A_le_normalizer h45 hx
  set σ : MulAut ↥L := L.normalizerMonoidHom ⟨x, hxN⟩ with hσ
  have hσ3 : σ ^ 3 = 1 := by
    rw [hσ, ← map_pow]
    have : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ 3 = 1 :=
      Subtype.ext (by simpa using h.isElemAbelian_A.2 x hx)
    rw [this, map_one]
  obtain ⟨k, hk⟩ := inner_of_pow_three_J3 h.perfect e σ hσ3
  refine ⟨k, k.2, (k : G)⁻¹ * x, ?_, by group⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h1 : ((σ ⟨y, hy⟩ : ↥L) : G) = x * y * x⁻¹ := rfl
  have h2 : ((σ ⟨y, hy⟩ : ↥L) : G) = (k : G) * y * (k : G)⁻¹ := by
    rw [hk]; rfl
  have h3 : x * y * x⁻¹ = (k : G) * y * (k : G)⁻¹ := h1.symm.trans h2
  calc y * ((k : G)⁻¹ * x) = (k : G)⁻¹ * ((k : G) * y * (k : G)⁻¹) * x := by group
    _ = (k : G)⁻¹ * (x * y * x⁻¹) * x := by rw [h3]
    _ = (k : G)⁻¹ * x * y := by group

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem CoverOut.card_le_three_of_centralizes (h45 : Sec4.Item4_5) (h : CoverOut A E U c L)
    (hZ : Subgroup.center L = ⊥) {B : Subgroup G} (hB : CFSG.Assembly.IsElemAbelian 3 B)
    (hBC : ∀ d ∈ B, ∀ x ∈ L, d * x = x * d) : Nat.card B < 9 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨a, y, W, ha1, ha3, hy3, hy1, hay, hya, hW0, hW2, haW, hyN⟩ :=
    exists_local_frame_J3 (h.equivJ3 hZ)
  have hLZ : ∀ z : ↥L, z ∈ Subgroup.center ↥L → z = 1 := fun z hz => by
    rw [hZ] at hz
    exact Subgroup.mem_bot.1 hz
  exact false_of_frame_big_abelian a y W (fun hc => ha1 (hLZ a hc)) ha3 hy3 hy1 hay
    (by rw [hZ, sup_bot_eq]; exact hya) hW0 hW2 haW hyN B hB hBC hlt h.localRank_le


theorem CoverOut.inf_centralizer_eq_bot (h45 : Sec4.Item4_5) (h : CoverOut A E U c L) :
    L ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  have hZ := h.center_eq_bot h45
  rw [eq_bot_iff]
  rintro x ⟨hxL, hxC⟩
  have : (⟨x, hxL⟩ : ↥L) ∈ center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hxC g g.2)
  rw [hZ, Subgroup.mem_bot] at this
  exact Subgroup.mem_bot.2 (congrArg Subtype.val this)

theorem CoverOut.card_inf_eq_and_decomp (h45 : Sec4.Item4_5) (h : CoverOut A E U c L) :
    Nat.card (A ⊓ L : Subgroup G) = 27 ∧
      ∀ x ∈ A, ∃ l ∈ (A ⊓ L : Subgroup G), ∃ i : ℤ, x = l * c ^ i :=
  card_inf_eq_of_components (h.inf_centralizer_eq_bot h45) h.isElemAbelian_A h.maximal
    (fun x hx => h.exists_decomp h45 hx) h.c_mem_A
    (Subgroup.mem_centralizer_iff.2 (fun x hx => (h.c_comm x hx).symm)) h.c_ne_one h.card
    (fun B hB hBC => h.card_le_three_of_centralizes h45 (h.center_eq_bot h45) hB hBC)

theorem CoverOut.card_inf_eq (h45 : Sec4.Item4_5) (h : CoverOut A E U c L) :
    Nat.card (A ⊓ L : Subgroup G) = 27 :=
  (h.card_inf_eq_and_decomp h45).1

theorem CoverOut.decomp_A (h45 : Sec4.Item4_5) (h : CoverOut A E U c L) :
    ∀ x ∈ A, ∃ l ∈ (A ⊓ L : Subgroup G), ∃ i : ℤ, x = l * c ^ i :=
  (h.card_inf_eq_and_decomp h45).2

end Card

section Final


set_option linter.unusedSectionVars false

theorem sec217OutNoFix_holds (h45 : Sec4.Item4_5) : Sec217OutNoFix := by
  refine sec217OutNoFix_of ?_ ?_
  · intro G _ _ A E U c L hp hq hc h81 hext
    have := (CoverOut.mk hp hq hc h81 hext).card_inf_eq h45
    rw [this]
  · intro G _ _ A E U c L hp hq hc h81 hext
    exact (CoverOut.mk hp hq hc h81 hext).center_eq_bot h45

end Final

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
