module

public import CFSG.Quasithin.Background.BlueprintB2Basic

public section

namespace CFSG.Quasithin

open CFSG CFSG.Quasithin.BlueprintB2

namespace BlueprintB2

variable {R : Type*} [Group R]

section Generic

variable {p : ℕ}

theorem le_elemThompson {A : Subgroup R} (hA : A ∈ elemThompsonFamily R p) :
    A ≤ elemThompson R p :=
  le_sSup hA

theorem map_mem_elemThompsonFamily (φ : R ≃* R) {A : Subgroup R}
    (hA : A ∈ elemThompsonFamily R p) : A.map φ.toMonoidHom ∈ elemThompsonFamily R p :=
  ⟨isElementaryAbelian_map hA.1 _, by
    rw [Subgroup.card_map_of_injective φ.injective]
    exact hA.2⟩

theorem isElementaryAbelian_subgroupOf {Y A : Subgroup R} (hA : IsElementaryAbelian p A) :
    IsElementaryAbelian p (A.subgroupOf Y) := by
  obtain ⟨hc, hp⟩ := isElementaryAbelian_iff.mp hA
  refine isElementaryAbelian_iff.mpr ⟨?_, ?_⟩
  · intro a ha b hb
    exact Subtype.ext (hc a (Subgroup.mem_subgroupOf.mp ha) b (Subgroup.mem_subgroupOf.mp hb))
  · intro a ha
    exact Subtype.ext (by simpa using hp a (Subgroup.mem_subgroupOf.mp ha))

theorem card_subgroupOf_eq {Y A : Subgroup R} (hAY : A ≤ Y) :
    Nat.card (A.subgroupOf Y) = Nat.card A :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAY).toEquiv

end Generic

section Finite

variable [Finite R] {p : ℕ} [Fact p.Prime]

theorem exists_card_eq_pow_of_isElementaryAbelian {A : Subgroup R} (hA : IsElementaryAbelian p A) :
    ∃ k : ℕ, Nat.card A = p ^ k := by
  have := hA
  exact IsPGroup.iff_card.mp (IsElementaryAbelian.isPGroup p A)

theorem bddAbove_pRank_set (R : Type*) [Group R] [Finite R] (p : ℕ) [Fact p.Prime] :
    BddAbove {r : ℕ | ∃ A : Subgroup R, IsElementaryAbelian p A ∧ Nat.card A = p ^ r} := by
  refine ⟨Nat.card R, ?_⟩
  rintro r ⟨A, -, hA⟩
  have h1 : r < p ^ r := Nat.lt_pow_self (Fact.out : p.Prime).one_lt
  have h2 : p ^ r ≤ Nat.card R := hA ▸ A.card_le_card_group
  omega

theorem card_le_pow_pRank {A : Subgroup R} (hA : IsElementaryAbelian p A) :
    Nat.card A ≤ p ^ pRank p R := by
  obtain ⟨k, hk⟩ := exists_card_eq_pow_of_isElementaryAbelian hA
  have hk' : k ≤ pRank p R := le_csSup (bddAbove_pRank_set R p) ⟨A, hA, hk⟩
  rw [hk]
  exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hk'

theorem exists_card_eq_pow_pRank (R : Type*) [Group R] [Finite R] (p : ℕ) [Fact p.Prime] :
    ∃ A : Subgroup R, IsElementaryAbelian p A ∧ Nat.card A = p ^ pRank p R := by
  have hne : {r : ℕ | ∃ A : Subgroup R, IsElementaryAbelian p A ∧ Nat.card A = p ^ r}.Nonempty :=
    ⟨0, ⊥, isElementaryAbelian_bot p, by simp⟩
  exact Nat.sSup_mem hne (bddAbove_pRank_set R p)

theorem elemThompsonFamily_nonempty (R : Type*) [Group R] [Finite R] (p : ℕ) [Fact p.Prime] :
    (elemThompsonFamily R p).Nonempty := by
  obtain ⟨A, hA, hc⟩ := exists_card_eq_pow_pRank R p
  exact ⟨A, hA, hc⟩

theorem mem_elemThompsonFamily_iff {A : Subgroup R} :
    A ∈ elemThompsonFamily R p ↔
      IsElementaryAbelian p A ∧
        ∀ B : Subgroup R, IsElementaryAbelian p B → Nat.card B ≤ Nat.card A := by
  constructor
  · rintro ⟨hA, hc⟩
    exact ⟨hA, fun B hB => hc ▸ card_le_pow_pRank hB⟩
  · rintro ⟨hA, hmax⟩
    obtain ⟨A₀, hA₀, hc₀⟩ := exists_card_eq_pow_pRank R p
    exact ⟨hA, le_antisymm (card_le_pow_pRank hA) (hc₀ ▸ hmax A₀ hA₀)⟩

omit [Fact p.Prime] in
theorem mem_of_mem_centralizer_of_pow_eq_one {A : Subgroup R} (hA : IsElementaryAbelian p A)
    (hmax : ∀ B : Subgroup R, IsElementaryAbelian p B → Nat.card B ≤ Nat.card A) {x : R}
    (hx : x ∈ Subgroup.centralizer (A : Set R)) (hxp : x ^ p = 1) : x ∈ A := by
  have hz : IsElementaryAbelian p (Subgroup.zpowers x) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one hxp
  have hle : Subgroup.zpowers x ≤ Subgroup.centralizer (A : Set R) := by
    rw [Subgroup.zpowers_le]
    exact hx
  have hB : IsElementaryAbelian p (A ⊔ Subgroup.zpowers x : Subgroup R) := by
    have := hA
    have := hz
    exact IsElementaryAbelian.sup_of_le_centralizer hle
  have heq : A = A ⊔ Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (hmax _ hB)
  rw [heq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)

theorem mem_elemThompsonCenterTorsion_iff_centralizer {x : R} :
    x ∈ elemThompsonCenterTorsion R p ↔
      x ∈ Subgroup.centralizer (elemThompson R p : Set R) ∧ x ^ p = 1 := by
  constructor
  · intro h
    obtain ⟨-, hc, hp⟩ := mem_centerTorsion_iff.mp h
    exact ⟨Subgroup.mem_centralizer_iff.mpr hc, hp⟩
  · rintro ⟨hc, hp⟩
    obtain ⟨A₀, hA₀⟩ := elemThompsonFamily_nonempty R p
    have hx0 : x ∈ A₀ :=
      mem_of_mem_centralizer_of_pow_eq_one hA₀.1 (mem_elemThompsonFamily_iff.mp hA₀).2
        (Subgroup.centralizer_le (fun _ ha => le_elemThompson hA₀ ha) hc) hp
    exact mem_centerTorsion_iff.mpr
      ⟨le_elemThompson hA₀ hx0, Subgroup.mem_centralizer_iff.mp hc, hp⟩

theorem mem_elemThompsonCenterTorsion_iff_forall {x : R} :
    x ∈ elemThompsonCenterTorsion R p ↔ ∀ A ∈ elemThompsonFamily R p, x ∈ A := by
  constructor
  · intro h A hA
    obtain ⟨hc, hp⟩ := mem_elemThompsonCenterTorsion_iff_centralizer.mp h
    exact mem_of_mem_centralizer_of_pow_eq_one hA.1 (mem_elemThompsonFamily_iff.mp hA).2
      (Subgroup.centralizer_le (fun _ ha => le_elemThompson hA ha) hc) hp
  · intro h
    obtain ⟨A₀, hA₀⟩ := elemThompsonFamily_nonempty R p
    have hp : x ^ p = 1 := (isElementaryAbelian_iff.mp hA₀.1).2 x (h A₀ hA₀)
    have hJ : elemThompson R p ≤ Subgroup.centralizer ({x} : Set R) := by
      refine sSup_le fun A hA a ha => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact (isElementaryAbelian_iff.mp hA.1).1 x (h A hA) a ha
    refine mem_elemThompsonCenterTorsion_iff_centralizer.mpr ⟨?_, hp⟩
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    exact (Subgroup.mem_centralizer_iff.mp (hJ hj) x (Set.mem_singleton x)).symm

theorem elemThompsonCenterTorsion_eq_sInf (R : Type*) [Group R] [Finite R] (p : ℕ)
    [Fact p.Prime] :
    elemThompsonCenterTorsion R p = sInf (elemThompsonFamily R p) :=
  Subgroup.ext fun _ => by
    rw [Subgroup.mem_sInf]
    exact mem_elemThompsonCenterTorsion_iff_forall

theorem coe_elemThompsonCenterTorsion (R : Type*) [Group R] [Finite R] (p : ℕ) [Fact p.Prime] :
    (elemThompsonCenterTorsion R p : Set R) =
      {x | x ∈ Subgroup.centralizer (elemThompson R p : Set R) ∧ x ^ p = 1} :=
  Set.ext fun _ => mem_elemThompsonCenterTorsion_iff_centralizer

theorem elemThompson_characteristic (R : Type*) [Group R] [Finite R] (p : ℕ) [Fact p.Prime] :
    (elemThompson R p).Characteristic := by
  rw [Subgroup.characteristic_iff_le_comap]
  intro φ
  refine sSup_le fun A hA => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact le_elemThompson (map_mem_elemThompsonFamily φ hA)

theorem elemThompsonCenterTorsion_characteristic (R : Type*) [Group R] [Finite R] (p : ℕ)
    [Fact p.Prime] : (elemThompsonCenterTorsion R p).Characteristic := by
  have hJ := elemThompson_characteristic R p
  rw [Subgroup.characteristic_iff_le_comap]
  intro φ x hx
  obtain ⟨hc, hp⟩ := mem_elemThompsonCenterTorsion_iff_centralizer.mp hx
  refine mem_elemThompsonCenterTorsion_iff_centralizer.mpr ⟨?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro j hj
    have hj' : φ.symm j ∈ elemThompson R p := by
      have := Subgroup.characteristic_iff_le_comap.mp hJ φ.symm hj
      exact this
    have := Subgroup.mem_centralizer_iff.mp hc (φ.symm j) hj'
    apply φ.symm.injective
    simpa using this
  · show (φ x) ^ p = 1
    rw [← map_pow, hp, map_one]

theorem pRank_eq_of_elemThompson_le {Y : Subgroup R} (hY : elemThompson R p ≤ Y) :
    pRank p Y = pRank p R := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  apply le_antisymm
  · obtain ⟨A', hA', hc'⟩ := exists_card_eq_pow_pRank Y p
    have hle := card_le_pow_pRank (R := R) (isElementaryAbelian_map hA' Y.subtype)
    rw [Subgroup.card_map_of_injective Y.subtype_injective, hc'] at hle
    exact (Nat.pow_le_pow_iff_right hp1).mp hle
  · obtain ⟨A, hA, hc⟩ := exists_card_eq_pow_pRank R p
    have hAY : A ≤ Y := (le_elemThompson ⟨hA, hc⟩).trans hY
    have hle := card_le_pow_pRank (R := Y) (isElementaryAbelian_subgroupOf (Y := Y) hA)
    rw [card_subgroupOf_eq hAY, hc] at hle
    exact (Nat.pow_le_pow_iff_right hp1).mp hle

theorem elemThompson_map_subtype {Y : Subgroup R} (hY : elemThompson R p ≤ Y) :
    (elemThompson Y p).map Y.subtype = elemThompson R p := by
  have hrk := pRank_eq_of_elemThompson_le (p := p) hY
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun A' hA' => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    refine le_elemThompson ⟨isElementaryAbelian_map hA'.1 _, ?_⟩
    rw [Subgroup.card_map_of_injective Y.subtype_injective, hA'.2, hrk]
  · refine sSup_le fun A hA => ?_
    have hAY : A ≤ Y := (le_elemThompson hA).trans hY
    rw [← Subgroup.map_subgroupOf_eq_of_le hAY]
    refine Subgroup.map_mono (le_sSup ⟨isElementaryAbelian_subgroupOf hA.1, ?_⟩)
    rw [card_subgroupOf_eq hAY, hA.2, hrk]

theorem elemThompsonCenterTorsion_map_subtype {Y : Subgroup R} (hY : elemThompson R p ≤ Y) :
    (elemThompsonCenterTorsion Y p).map Y.subtype = elemThompsonCenterTorsion R p := by
  have hJ := elemThompson_map_subtype (p := p) hY
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hc, hp⟩ := mem_elemThompsonCenterTorsion_iff_centralizer.mp hx
    refine mem_elemThompsonCenterTorsion_iff_centralizer.mpr ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro j hj
      rw [← hJ] at hj
      obtain ⟨j', hj', rfl⟩ := hj
      have := Subgroup.mem_centralizer_iff.mp hc j' hj'
      exact congrArg Subtype.val this
    · simpa using congrArg Subtype.val hp
  · intro hz
    obtain ⟨hc, hp⟩ := mem_elemThompsonCenterTorsion_iff_centralizer.mp hz
    have hzJ : z ∈ elemThompson R p := (mem_centerTorsion_iff.mp hz).1
    have hzY : z ∈ Y := hY hzJ
    refine ⟨⟨z, hzY⟩, ?_, rfl⟩
    refine mem_elemThompsonCenterTorsion_iff_centralizer.mpr ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro j hj
      have hjR : (j : R) ∈ elemThompson R p := by
        rw [← hJ]
        exact ⟨j, hj, rfl⟩
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hc _ hjR)
    · exact Subtype.ext (by simpa using hp)

end Finite

end BlueprintB2

theorem qt_nq_thompson_center_maximal_elementary_intersection {R : Type*} [Group R] [Finite R]
    (p : ℕ) [Fact p.Prime] (_hR : IsPGroup p R) :
    elemThompsonCenterTorsion R p = sInf (elemThompsonFamily R p) ∧
      (elemThompsonCenterTorsion R p : Set R) =
        {x | x ∈ Subgroup.centralizer (elemThompson R p : Set R) ∧ x ^ p = 1} ∧
      (elemThompson R p).Characteristic ∧ (elemThompsonCenterTorsion R p).Characteristic ∧
      ∀ Y : Subgroup R, elemThompson R p ≤ Y →
        (elemThompson Y p).map Y.subtype = elemThompson R p ∧
          (elemThompsonCenterTorsion Y p).map Y.subtype = elemThompsonCenterTorsion R p :=
  ⟨BlueprintB2.elemThompsonCenterTorsion_eq_sInf R p, BlueprintB2.coe_elemThompsonCenterTorsion R p,
    BlueprintB2.elemThompson_characteristic R p,
    BlueprintB2.elemThompsonCenterTorsion_characteristic R p, fun _ hY =>
    ⟨BlueprintB2.elemThompson_map_subtype hY, BlueprintB2.elemThompsonCenterTorsion_map_subtype hY⟩⟩

namespace BlueprintB2

section ActionInequality

variable {S : Type*} [Group S] [Finite S] {p : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
theorem inf_centralizer_eq_inf_of_max {V A : Subgroup S} (hV : IsElementaryAbelian p V)
    (hA : IsElementaryAbelian p A)
    (hmax : ∀ B : Subgroup S, IsElementaryAbelian p B → Nat.card B ≤ Nat.card A) :
    V ⊓ Subgroup.centralizer (A : Set S) = A ⊓ V := by
  apply le_antisymm
  · rintro c ⟨hcV, hcA⟩
    exact ⟨mem_of_mem_centralizer_of_pow_eq_one hA hmax hcA
      ((isElementaryAbelian_iff.mp hV).2 c hcV), hcV⟩
  · rintro c ⟨hcA, hcV⟩
    exact ⟨hcV, Subgroup.mem_centralizer_iff.mpr fun a ha =>
      (isElementaryAbelian_iff.mp hA).1 a ha c hcA⟩

omit [Fact p.Prime] in
theorem relIndex_inf_centralizer_le {V A : Subgroup S} [V.Normal] (hV : IsElementaryAbelian p V)
    (hA : IsElementaryAbelian p A)
    (hmax : ∀ B : Subgroup S, IsElementaryAbelian p B → Nat.card B ≤ Nat.card A) :
    (V ⊓ Subgroup.centralizer (A : Set S)).relIndex V ≤
      (A ⊓ Subgroup.centralizer (V : Set S)).relIndex A := by
  set C : Subgroup S := A ⊓ Subgroup.centralizer (V : Set S) with hC
  have hCA : IsElementaryAbelian p C := isElementaryAbelian_of_le inf_le_left hA
  have hCV : C ≤ Subgroup.centralizer (V : Set S) := inf_le_right
  have hW : IsElementaryAbelian p (V ⊔ C : Subgroup S) := by
    have := hV
    have := hCA
    exact IsElementaryAbelian.sup_of_le_centralizer hCV
  have hWA : Nat.card (V ⊔ C : Subgroup S) ≤ Nat.card A := hmax _ hW
  have hVA : V ⊓ Subgroup.centralizer (A : Set S) = A ⊓ V :=
    inf_centralizer_eq_inf_of_max hV hA hmax
  have h1 : V.relIndex (V ⊔ C) = V.relIndex C := Subgroup.relIndex_sup_left C V
  have h2 := Subgroup.relIndex_mul_card V (V ⊔ C)
  rw [inf_of_le_left le_sup_left, h1] at h2
  have h5 : V ⊓ C = A ⊓ V := by
    apply le_antisymm
    · rintro x ⟨hxV, hxA, -⟩
      exact ⟨hxA, hxV⟩
    · rintro x ⟨hxA, hxV⟩
      exact ⟨hxV, hxA, Subgroup.mem_centralizer_iff.mpr fun v hv =>
        (isElementaryAbelian_iff.mp hV).1 v hv x hxV⟩
  have h3 := Subgroup.relIndex_mul_card V C
  rw [h5] at h3
  have h4 := Subgroup.relIndex_mul_card C A
  rw [inf_of_le_left inf_le_left] at h4
  have h6 := Subgroup.relIndex_mul_card (V ⊓ Subgroup.centralizer (A : Set S)) V
  have h6' : Nat.card ↥((V ⊓ Subgroup.centralizer (A : Set S)) ⊓ V) = Nat.card ↥(A ⊓ V) := by
    rw [inf_of_le_left inf_le_left, hVA]
  rw [h6'] at h6
  have hpos : 0 < V.relIndex C * Nat.card ↥(A ⊓ V) := by
    rw [h3]
    exact Nat.card_pos
  refine Nat.le_of_mul_le_mul_left ?_ hpos
  calc V.relIndex C * Nat.card ↥(A ⊓ V) * (V ⊓ Subgroup.centralizer (A : Set S)).relIndex V
      = V.relIndex C * ((V ⊓ Subgroup.centralizer (A : Set S)).relIndex V *
          Nat.card ↥(A ⊓ V)) := by ring
    _ = Nat.card (V ⊔ C : Subgroup S) := by rw [h6, h2]
    _ ≤ Nat.card A := hWA
    _ = C.relIndex A * (V.relIndex C * Nat.card ↥(A ⊓ V)) := by rw [h3, h4]
    _ = V.relIndex C * Nat.card ↥(A ⊓ V) * (A ⊓ Subgroup.centralizer (V : Set S)).relIndex A := by
      rw [hC]; ring

theorem exists_rank_le_of_max {V A : Subgroup S} [V.Normal] (hV : IsElementaryAbelian p V)
    (hA : IsElementaryAbelian p A)
    (hmax : ∀ B : Subgroup S, IsElementaryAbelian p B → Nat.card B ≤ Nat.card A) :
    ∃ k l : ℕ, k ≤ l ∧ (V ⊓ Subgroup.centralizer (A : Set S)).relIndex V = p ^ k ∧
      (A ⊓ Subgroup.centralizer (V : Set S)).relIndex A = p ^ l := by
  obtain ⟨m, hm⟩ := exists_card_eq_pow_of_isElementaryAbelian hV
  obtain ⟨m', hm'⟩ := exists_card_eq_pow_of_isElementaryAbelian hA
  have hdV : (V ⊓ Subgroup.centralizer (A : Set S)).relIndex V ∣ p ^ m :=
    hm ▸ ⟨_, (Subgroup.relIndex_mul_card _ V).symm⟩
  have hdA : (A ⊓ Subgroup.centralizer (V : Set S)).relIndex A ∣ p ^ m' :=
    hm' ▸ ⟨_, (Subgroup.relIndex_mul_card _ A).symm⟩
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdV
  obtain ⟨l, -, hl⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdA
  refine ⟨k, l, ?_, hk, hl⟩
  have := relIndex_inf_centralizer_le hV hA hmax
  rw [hk, hl] at this
  exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp this

end ActionInequality

end BlueprintB2

theorem qt_A7_maximal_elementary_action_inequality {S : Type*} [Group S] [Finite S] (p : ℕ)
    [Fact p.Prime] (_hS : IsPGroup p S) (V : Subgroup S) [V.Normal]
    (hV : IsElementaryAbelian p V) (A : Subgroup S) (hA : IsElementaryAbelian p A)
    (hmax : ∀ B : Subgroup S, IsElementaryAbelian p B → Nat.card B ≤ Nat.card A) :
    V ⊓ Subgroup.centralizer (A : Set S) = A ⊓ V ∧
      (V ⊓ Subgroup.centralizer (A : Set S)).relIndex V ≤
        (A ⊓ Subgroup.centralizer (V : Set S)).relIndex A ∧
      ∃ k l : ℕ, k ≤ l ∧ (V ⊓ Subgroup.centralizer (A : Set S)).relIndex V = p ^ k ∧
        (A ⊓ Subgroup.centralizer (V : Set S)).relIndex A = p ^ l :=
  ⟨BlueprintB2.inf_centralizer_eq_inf_of_max hV hA hmax,
    BlueprintB2.relIndex_inf_centralizer_le hV hA hmax,
    BlueprintB2.exists_rank_le_of_max hV hA hmax⟩

end CFSG.Quasithin
