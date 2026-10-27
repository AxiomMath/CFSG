module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432SylowCount
public import CFSG.RankThree.PartTwo.Sec4.RonanK432SylowCountP27
public import CFSG.RankThree.PartTwo.Sec4.RonanK432SylowCenter
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

structure SylowThreeData (G : Type) [Group G] (xA xB : G) (g' m : ℕ) : Prop where
  card : Nat.card G = 27 * g'
  card_mod : g' % 3 = 2
  orderA : orderOf xA = 3
  orderB : orderOf xB = 3
  centB : Nat.card (Subgroup.centralizer ({xB} : Set G)) = 9 * m
  centB_mod : m % 3 = 2
  cover : ∀ z : G, orderOf z = 3 → IsConj xA z ∨ IsConj xB z
  disj : ¬ IsConj xA xB

section Generic

variable {G : Type} [Group G]

theorem orderOf_eq_orderOf_of_isConj {a b : G} (h : IsConj a b) : orderOf a = orderOf b := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  exact (MulEquiv.orderOf_eq (MulAut.conj c) a).symm

theorem card_centralizer_eq_of_isConj [Finite G] {a b : G} (h : IsConj a b) :
    Nat.card (Subgroup.centralizer ({a} : Set G)) =
      Nat.card (Subgroup.centralizer ({b} : Set G)) := by
  have h1 := ncard_conjugatesOf_mul_card_centralizer a
  have h2 := ncard_conjugatesOf_mul_card_centralizer b
  rw [h.conjugatesOf_eq] at h1
  have hpos : 0 < (conjugatesOf b).ncard := by
    rcases Nat.eq_zero_or_pos (conjugatesOf b).ncard with h0 | h0
    · rw [h0, zero_mul] at h2
      exact absurd h2.symm Nat.card_pos.ne'
    · exact h0
  exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2.symm)

end Generic

namespace SylowThreeData

variable {G : Type} [Group G] [Finite G] {xA xB : G} {g' m : ℕ}

theorem isConj_of_central (hD : SylowThreeData G xA xB g' m) (P : Sylow 3 G) {u : G}
    (hu3 : orderOf u = 3) (huc : ∀ q ∈ (P : Subgroup G), q * u = u * q) : IsConj xA u := by
  rcases hD.cover u hu3 with h | h
  · exact h
  · exfalso
    have hcu : Nat.card (Subgroup.centralizer ({u} : Set G)) = 9 * m :=
      (card_centralizer_eq_of_isConj h).symm.trans hD.centB
    have hle : (P : Subgroup G) ≤ Subgroup.centralizer ({u} : Set G) := fun q hq =>
      Subgroup.mem_centralizer_singleton_iff.2 (huc q hq)
    have h27 : 27 ∣ Nat.card (Subgroup.centralizer ({u} : Set G)) :=
      (card_sylow_eq_27 hD.card hD.card_mod P) ▸ Subgroup.card_dvd_of_le hle
    rw [hcu] at h27
    have := hD.centB_mod
    omega

theorem ncard_pow_three_eq (hD : SylowThreeData G xA xB g' m) (P : Sylow 3 G) :
    {y : G | y ∈ (P : Subgroup G) ∧ y ^ 3 = 1}.ncard =
      {y : G | y ∈ (P : Subgroup G) ∧ IsConj xA y}.ncard +
        {y : G | y ∈ conjugatesOf xB ∧ y ∈ (P : Subgroup G)}.ncard + 1 := by
  have hdisj : Disjoint {y : G | y ∈ (P : Subgroup G) ∧ IsConj xA y}
      {y : G | y ∈ conjugatesOf xB ∧ y ∈ (P : Subgroup G)} := by
    rw [Set.disjoint_left]
    rintro y ⟨-, hA⟩ ⟨hB, -⟩
    exact hD.disj (hA.trans (show IsConj xB y from hB).symm)
  have hone : (1 : G) ∉ {y : G | y ∈ (P : Subgroup G) ∧ IsConj xA y} ∪
      {y : G | y ∈ conjugatesOf xB ∧ y ∈ (P : Subgroup G)} := by
    rintro (⟨-, hA⟩ | ⟨hB, -⟩)
    · have := orderOf_eq_orderOf_of_isConj hA
      rw [hD.orderA, orderOf_one] at this
      omega
    · have := orderOf_eq_orderOf_of_isConj (show IsConj xB 1 from hB)
      rw [hD.orderB, orderOf_one] at this
      omega
  have hset : {y : G | y ∈ (P : Subgroup G) ∧ y ^ 3 = 1} =
      insert 1 ({y : G | y ∈ (P : Subgroup G) ∧ IsConj xA y} ∪
        {y : G | y ∈ conjugatesOf xB ∧ y ∈ (P : Subgroup G)}) := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_union]
    constructor
    · rintro ⟨hyP, hy3⟩
      by_cases hy1 : y = 1
      · exact Or.inl hy1
      · have hyo : orderOf y = 3 := orderOf_eq_prime hy3 hy1
        rcases hD.cover y hyo with h | h
        · exact Or.inr (Or.inl ⟨hyP, h⟩)
        · exact Or.inr (Or.inr ⟨h, hyP⟩)
    · rintro (rfl | ⟨hyP, h⟩ | ⟨h, hyP⟩)
      · exact ⟨(P : Subgroup G).one_mem, one_pow 3⟩
      · refine ⟨hyP, ?_⟩
        rw [← hD.orderA, orderOf_eq_orderOf_of_isConj h]
        exact pow_orderOf_eq_one y
      · refine ⟨hyP, ?_⟩
        have h3 : orderOf y = 3 := by
          rw [← orderOf_eq_orderOf_of_isConj (show IsConj xB y from h), hD.orderB]
        rw [← h3]
        exact pow_orderOf_eq_one y
  rw [hset, Set.ncard_insert_of_notMem hone (Set.toFinite _),
    Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)]

theorem exists_noncentral (hD : SylowThreeData G xA xB g' m) (P : Sylow 3 G) :
    ∃ y ∈ (P : Subgroup G), IsConj xA y ∧ ∃ q ∈ (P : Subgroup G), q * y ≠ y * q := by
  by_contra hcon
  push Not at hcon
  have hP27 : Nat.card ↥(P : Subgroup G) = 27 := card_sylow_eq_27 hD.card hD.card_mod P
  have hxB3 : xB ^ 3 = 1 := by
    rw [← hD.orderB]
    exact pow_orderOf_eq_one xB
  have htB := card_class_inter_sylow_mod_nine hD.card hD.card_mod hxB3 hD.centB hD.centB_mod P
  have hna : ∃ a b : ↥(P : Subgroup G), a * b ≠ b * a := by
    by_contra hab
    push Not at hab
    have hpos : 0 < Nat.card {y : G // y ∈ conjugatesOf xB ∧ y ∈ P} := by omega
    obtain ⟨⟨y, hyB, hyP⟩⟩ := (Nat.card_pos_iff.1 hpos).1
    have hyo : orderOf y = 3 := by
      rw [← orderOf_eq_orderOf_of_isConj (show IsConj xB y from hyB), hD.orderB]
    have hyc : ∀ q ∈ (P : Subgroup G), q * y = y * q := fun q hq =>
      congrArg Subtype.val (hab ⟨q, hq⟩ ⟨y, hyP⟩)
    exact hD.disj ((hD.isConj_of_central P hyo hyc).trans (show IsConj xB y from hyB).symm)
  have hZ := card_center_eq_three_of_card_27 hP27 hna
  have hK := card_pow_three_eq_one_of_card_27 hP27 hna
  have hKG : {y : G | y ∈ (P : Subgroup G) ∧ y ^ 3 = 1}.ncard =
      Nat.card {x : ↥(P : Subgroup G) // x ^ 3 = 1} := by
    have himg : {y : G | y ∈ (P : Subgroup G) ∧ y ^ 3 = 1} =
        Subtype.val '' {x : ↥(P : Subgroup G) | x ^ 3 = 1} := by
      ext y
      constructor
      · rintro ⟨hyP, hy3⟩
        exact ⟨⟨y, hyP⟩, Subtype.ext (by simpa using hy3), rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x.2, by simpa using congrArg Subtype.val hx⟩
    rw [himg, Set.ncard_image_of_injective _ Subtype.val_injective, ← Nat.card_coe_set_eq]
    rfl
  have hA2 : {y : G | y ∈ (P : Subgroup G) ∧ IsConj xA y}.ncard ≤ 2 := by
    have hone : (1 : G) ∉ {y : G | y ∈ (P : Subgroup G) ∧ IsConj xA y} := by
      rintro ⟨-, hA⟩
      have := orderOf_eq_orderOf_of_isConj hA
      rw [hD.orderA, orderOf_one] at this
      omega
    have hsub : insert (1 : G) {y : G | y ∈ (P : Subgroup G) ∧ IsConj xA y} ⊆
        Subtype.val '' ((Subgroup.center ↥(P : Subgroup G) : Subgroup _) :
          Set ↥(P : Subgroup G)) := by
      rintro y (rfl | ⟨hyP, hA⟩)
      · exact ⟨1, (Subgroup.center _).one_mem, rfl⟩
      · refine ⟨⟨y, hyP⟩, Subgroup.mem_center_iff.2 fun g => ?_, rfl⟩
        exact Subtype.ext (hcon y hyP hA g.1 g.2)
    have hZset : (Subtype.val '' ((Subgroup.center ↥(P : Subgroup G) : Subgroup _) :
        Set ↥(P : Subgroup G))).ncard = 3 := by
      rw [Set.ncard_image_of_injective _ Subtype.val_injective, ← Nat.card_coe_set_eq]
      exact hZ
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_insert_of_notMem hone (Set.toFinite _), hZset] at hle
    omega
  have hcount := hD.ncard_pow_three_eq P
  rw [hKG] at hcount
  have hBeq : {y : G | y ∈ conjugatesOf xB ∧ y ∈ (P : Subgroup G)}.ncard =
      Nat.card {y : G // y ∈ conjugatesOf xB ∧ y ∈ P} := (Nat.card_coe_set_eq _).symm
  rw [hBeq] at hcount
  omega

end SylowThreeData

theorem listRow_of_sylowThreeData {G : Type} [Group G] [Finite G] {xA xB : G} {g' m : ℕ}
    (hD : SylowThreeData G xA xB g' m) : ListRow G := by
  obtain ⟨P⟩ := (Sylow.nonempty : Nonempty (Sylow 3 G))
  have hP27 : Nat.card ↥(P : Subgroup G) = 27 := card_sylow_eq_27 hD.card hD.card_mod P
  refine listRow_of_sylow_center 3 (P : Subgroup G) (by rw [hP27]; norm_num) ?_ ?_
  · have h1 := hD.card
    have h2 := hD.card_mod
    rw [h1]
    omega
  · intro u huP hu3 huc
    obtain ⟨y, hyP, hyA, q₀, hq₀P, hq₀⟩ := hD.exists_noncentral P
    obtain ⟨g, hg⟩ := isConj_iff.1 ((hD.isConj_of_central P hu3 huc).symm.trans hyA)
    refine ⟨g, ?_, ?_⟩
    · rw [hg]
      exact huc y hyP
    · rw [hg]
      intro hy
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hy
      apply hq₀
      rw [← hk]
      exact (Commute.zpow_right (huc q₀ hq₀P) k).eq

end CFSG.RankThree.PartTwo.Sec4.RonanK432
