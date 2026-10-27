module

public import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank
public import CFSG.RankThree.Classical.EvenSurvivingScalarRank
public import CFSG.RankThree.PartOne.S9.Defs

public section

namespace CFSG.RankThree.PartOne.OddCore37

open CFSG CFSG.Assembly.RankThreeEven
open scoped commutatorElement

section Rank

variable {G : Type*} [Group G] [Finite G]

theorem pRank_le_of_le {q : ℕ} (hq : q.Prime) {H K : Subgroup G} (h : H ≤ K) :
    CFSG.pRank q ↥H ≤ CFSG.pRank q ↥K := by
  rw [← assembly_pRank_eq hq H, ← assembly_pRank_eq hq K]
  exact CFSG.SectionRank.pRank_mono hq.one_lt h

theorem pRank_map_eq {G' : Type*} [Group G'] [Finite G'] (f : G →* G')
    (hf : Function.Injective f) {q : ℕ} (hq : q.Prime) (K : Subgroup G) :
    CFSG.pRank q ↥(K.map f) = CFSG.pRank q ↥K := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact CFSG.SectionRank.pRank_top_eq_of_mulEquiv hq.one_lt (K.equivMapOfInjective f hf).symm

theorem pRank_normalizer_zpowers_le_localRank {q : ℕ} (hq : q.Prime) {r : G} (hr1 : r ≠ 1)
    (hr2 : IsPGroup 2 (Subgroup.zpowers r)) :
    CFSG.pRank q ↥(Subgroup.normalizer ((Subgroup.zpowers r : Subgroup G) : Set G)) ≤
      localRank q G := by
  rw [← assembly_pRank_eq hq]
  exact CFSG.RankThree.Classical.pRank_le_localRank hq.one_lt
    ⟨Subgroup.zpowers r, fun h => hr1 (Subgroup.zpowers_eq_bot.1 h), hr2, rfl⟩

theorem pRank_inf_centralizer_le_localRank {q : ℕ} (hq : q.Prime) (K : Subgroup G) {r : G}
    (hr1 : r ≠ 1) (hr2 : IsPGroup 2 (Subgroup.zpowers r)) :
    CFSG.pRank q ↥(K ⊓ Subgroup.centralizer ({r} : Set G)) ≤ localRank q G := by
  refine (pRank_le_of_le hq ?_).trans (pRank_normalizer_zpowers_le_localRank hq hr1 hr2)
  intro x hx
  refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun h hh => ?_)
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
  have hxr : x * r = r * x := Subgroup.mem_centralizer_singleton_iff.1 hx.2
  exact (Commute.zpow_left (show Commute r x from hxr.symm) k).eq

theorem localRank_subgroup_le {q : ℕ} (hq : q.Prime) (H : Subgroup G) :
    localRank q ↥H ≤ localRank q G := by
  refine csSup_le' ?_
  rintro k ⟨U, ⟨T, hT0, hT2, rfl⟩, rfl⟩
  set T' : Subgroup G := T.map H.subtype with hT'
  have hT'0 : T' ≠ ⊥ := by
    intro h
    exact hT0 ((Subgroup.map_eq_bot_iff_of_injective T H.subtype_injective).1 h)
  have hT'2 : IsPGroup 2 T' := hT2.map _
  have hle : (Subgroup.normalizer (T : Set ↥H)).map H.subtype ≤
      Subgroup.normalizer (T' : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    have hx : x ∈ Subgroup.normalizer (T : Set ↥H) := hx
    rw [Subgroup.mem_normalizer_iff] at hx ⊢
    intro g
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨x * t * x⁻¹, (hx t).1 ht, rfl⟩
    · rintro ⟨t, ht, hte⟩
      have hte' : (t : G) = (x : G) * g * (x : G)⁻¹ := hte
      refine ⟨x⁻¹ * t * x, (hx _).2 (by
        rw [show x * (x⁻¹ * t * x) * x⁻¹ = t by group]; exact ht), ?_⟩
      change (x : G)⁻¹ * (t : G) * (x : G) = g
      rw [hte']
      group
  calc CFSG.Assembly.pRank q (Subgroup.normalizer (T : Set ↥H))
      ≤ CFSG.Assembly.pRank q ((Subgroup.normalizer (T : Set ↥H)).map H.subtype) :=
        CFSG.SectionRank.pRank_le_map hq.one_lt H.subtype H.subtype_injective _
    _ ≤ CFSG.Assembly.pRank q (Subgroup.normalizer (T' : Set G)) :=
        CFSG.SectionRank.pRank_mono hq.one_lt hle
    _ ≤ localRank q G :=
        CFSG.RankThree.Classical.pRank_le_localRank hq.one_lt ⟨T', hT'0, hT'2, rfl⟩

end Rank

section Characteristic

variable {G : Type*} [Group G]

theorem normal_of_characteristic {Q D : Subgroup G} [Q.Normal] (hDQ : D ≤ Q)
    (hD : (D.subgroupOf Q).Characteristic) : D.Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hnQ : n ∈ Q := hDQ hn
  have h := Subgroup.characteristic_iff_le_comap.1 hD (MulAut.conjNormal (H := Q) g)
  have hx : (⟨n, hnQ⟩ : Q) ∈ D.subgroupOf Q := hn
  have h2 : (MulAut.conjNormal (H := Q) g ⟨n, hnQ⟩) ∈ D.subgroupOf Q := h hx
  rw [Subgroup.mem_subgroupOf, MulAut.conjNormal_apply] at h2
  exact h2

end Characteristic

section Shape

variable {G : Type*} [Group G]

theorem isQDShape_pow_eq_one {q : ℕ} {D : Subgroup G} (h : IsQDShape q D) :
    ∀ x ∈ D, x ^ q = 1 := by
  rcases h with ⟨hel, -⟩ | ⟨hexp, -⟩
  · intro x hx
    have := hel
    exact elemPow_eq_one_of_isElementaryAbelian x hx
  · exact hexp

theorem isQDShape_card {q : ℕ} {D : Subgroup G} (h : IsQDShape q D) :
    Nat.card D = q ^ 4 ∨ Nat.card D = q ^ 5 := by
  rcases h with ⟨-, hc⟩ | ⟨-, hc, -⟩
  · exact Or.inl hc
  · exact Or.inr hc

theorem isQDShape_isPGroup {q : ℕ} {D : Subgroup G} (h : IsQDShape q D) : IsPGroup q D := by
  rcases isQDShape_card h with hc | hc
  · exact IsPGroup.of_card hc
  · exact IsPGroup.of_card hc

theorem map_subtype_commutator (D : Subgroup G) :
    (commutator ↥D).map D.subtype = ⁅D, D⁆ := by
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem isQDShape_relIndex_frattini [Finite G] {q : ℕ} (hq : q.Prime) {D : Subgroup G}
    (h : IsQDShape q D) : (inSubgroup frattini D).relIndex D = q ^ 4 := by
  have : Fact q.Prime := ⟨hq⟩
  rcases h with ⟨hel, hc⟩ | ⟨hexp, hc, hcomm, hz, hf⟩
  · have := hel
    have : Fact (IsPGroup q D) := ⟨IsPGroup.of_card hc⟩
    have hfr : inSubgroup frattini D = ⊥ := by
      unfold inSubgroup
      rw [frattini_eq_bot_of_isElementaryAbelian (R := ↥D) (p := q), Subgroup.map_bot]
    rw [hfr, Subgroup.relIndex_bot_left, hc]
  · rw [hf]
    have h1 := Subgroup.relIndex_mul_card (H := ⁅D, D⁆) (K := D)
    rw [inf_of_le_left (Subgroup.commutator_le_self D), hcomm, hc] at h1
    have h2 : q ^ 5 = q ^ 4 * q := by ring
    exact Nat.eq_of_mul_eq_mul_right hq.pos (h1.trans h2)

theorem three_le_pRank_of_isQDShape [Finite G] {q : ℕ} (hq : q.Prime) {D : Subgroup G}
    (h : IsQDShape q D) : 3 ≤ CFSG.pRank q ↥D := by
  have : Fact q.Prime := ⟨hq⟩
  rcases h with ⟨hel, hc⟩ | ⟨hexp, hc, hcomm, hz, hf⟩
  · have := hel
    have hexp : ∀ x : ↥D, x ^ q = 1 := fun x =>
      Subtype.ext (by simpa using elemPow_eq_one_of_isElementaryAbelian (p := q) (x : G) x.2)
    have htop : IsMulCommutative (⊤ : Subgroup ↥D) :=
      ⟨⟨fun a b => Subtype.ext (Subtype.ext (by
        have := hel.toIsMulCommutative.is_comm.comm (a : ↥D) b
        exact congrArg Subtype.val this))⟩⟩
    have h4 := CFSG.RankThree.PartTwo.le_pRank_of_isMulCommutative hq hexp htop
      (k := 4) (by rw [Subgroup.card_top, Nat.card_congr (Equiv.refl _), hc])
    omega
  · by_contra hlt
    push Not at hlt
    have hP : IsPGroup q ↥D := IsPGroup.of_card hc
    have hexp' : ∀ x : ↥D, x ^ q = 1 := fun x => Subtype.ext (by simpa using hexp x x.2)
    have hclass : commutator ↥D ≤ Subgroup.center ↥D := by
      rw [commutator_def, Subgroup.commutator_le]
      intro x _ y _
      rw [Subgroup.mem_center_iff]
      intro z
      have hxy : ((⁅x, y⁆ : ↥D) : G) ∈ ⁅D, D⁆ := Subgroup.commutator_mem_commutator x.2 y.2
      rw [← hz] at hxy
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hxy.2 z z.2)
    obtain ⟨h1, -, -⟩ := CFSG.RankThree.PartTwo.class_two_small_rank_order_bounds hP hexp' hclass
    have h2 := h1 (by omega)
    have hcard : Nat.card (commutator ↥D) = q := by
      rw [← hcomm, ← map_subtype_commutator,
        Subgroup.card_map_of_injective D.subtype_injective]
    have hk : Nat.card (↥D ⧸ commutator ↥D) = q ^ 4 := by
      have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup (commutator ↥D)
      rw [hcard, hc] at h3
      have h4 : q ^ 5 = q ^ 4 * q := by ring
      exact Nat.eq_of_mul_eq_mul_right hq.pos (h3.symm.trans h4)
    have h5 := (CFSG.RankThree.PartTwo.quotient_commutator_rank hq hexp' hk).2
    omega

end Shape

section Transport

variable {G G' : Type*} [Group G] [Group G']

theorem map_frattini_mulEquiv {P Q : Type*} [Group P] [Group Q] (e : P ≃* Q) :
    (frattini P).map e.toMonoidHom = frattini Q :=
  OrderIso.map_radical (MulEquiv.mapSubgroup e)

theorem inSubgroup_frattini_map (f : G →* G') (hf : Function.Injective f) (D : Subgroup G) :
    inSubgroup frattini (D.map f) = (inSubgroup frattini D).map f := by
  unfold inSubgroup
  rw [← map_frattini_mulEquiv (D.equivMapOfInjective f hf), Subgroup.map_map, Subgroup.map_map]
  rfl

theorem map_inf_centralizer (f : G →* G') (hf : Function.Injective f) (D : Subgroup G) :
    D.map f ⊓ Subgroup.centralizer ((D.map f : Subgroup G') : Set G') =
      (D ⊓ Subgroup.centralizer (D : Set G)).map f := by
  ext x
  constructor
  · rintro ⟨⟨d, hd, rfl⟩, hx⟩
    refine ⟨d, ⟨hd, Subgroup.mem_centralizer_iff.2 fun d' hd' => hf ?_⟩, rfl⟩
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_iff.1 hx (f d') (Subgroup.mem_map_of_mem f hd')
  · rintro ⟨d, ⟨hd, hdc⟩, rfl⟩
    refine ⟨Subgroup.mem_map_of_mem f hd, Subgroup.mem_centralizer_iff.2 ?_⟩
    rintro _ ⟨d', hd', rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 hdc d' hd']

theorem isElementaryAbelian_map_iff {p : ℕ} (f : G →* G') (hf : Function.Injective f)
    (D : Subgroup G) : IsElementaryAbelian p ↥(D.map f) ↔ IsElementaryAbelian p ↥D := by
  rw [CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian,
    CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian]
  constructor
  · rintro ⟨hc, hp⟩
    refine ⟨⟨⟨fun a b => Subtype.ext (hf ?_)⟩⟩, fun x hx => hf ?_⟩
    · have := congrArg Subtype.val (hc.is_comm.comm ⟨f a, Subgroup.mem_map_of_mem f a.2⟩
        ⟨f b, Subgroup.mem_map_of_mem f b.2⟩)
      simpa using this
    · rw [map_pow, map_one]
      exact hp (f x) (Subgroup.mem_map_of_mem f hx)
  · intro h
    exact CFSG.SectionRank.isElemAbelian_map h f

theorem isQDShape_map_iff (f : G →* G') (hf : Function.Injective f) (q : ℕ) (D : Subgroup G) :
    IsQDShape q (D.map f) ↔ IsQDShape q D := by
  have hexp : (∀ x ∈ D.map f, x ^ q = 1) ↔ ∀ x ∈ D, x ^ q = 1 := by
    constructor
    · intro h x hx
      exact hf (by rw [map_pow, map_one]; exact h (f x) (Subgroup.mem_map_of_mem f hx))
    · rintro h _ ⟨x, hx, rfl⟩
      rw [← map_pow, h x hx, map_one]
  have hcard : Nat.card (D.map f) = Nat.card D := Subgroup.card_map_of_injective hf
  have hcomm : (⁅D.map f, D.map f⁆ : Subgroup G') = (⁅D, D⁆ : Subgroup G).map f :=
    (Subgroup.map_commutator D D f).symm
  have hcommcard : Nat.card (⁅D.map f, D.map f⁆ : Subgroup G') = Nat.card (⁅D, D⁆ : Subgroup G) :=
    by rw [hcomm, Subgroup.card_map_of_injective hf]
  have hcen : (D.map f ⊓ Subgroup.centralizer ((D.map f : Subgroup G') : Set G') =
      ⁅D.map f, D.map f⁆) ↔ (D ⊓ Subgroup.centralizer (D : Set G) = ⁅D, D⁆) := by
    rw [map_inf_centralizer f hf, hcomm]
    exact (Subgroup.map_injective hf).eq_iff
  have hfr : (inSubgroup frattini (D.map f) = ⁅D.map f, D.map f⁆) ↔
      (inSubgroup frattini D = ⁅D, D⁆) := by
    rw [inSubgroup_frattini_map f hf, hcomm]
    exact (Subgroup.map_injective hf).eq_iff
  unfold IsQDShape
  rw [isElementaryAbelian_map_iff f hf, hexp, hcard, hcommcard, hcen, hfr]

end Transport

end CFSG.RankThree.PartOne.OddCore37
