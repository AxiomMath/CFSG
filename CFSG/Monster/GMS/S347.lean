module

public import CFSG.Monster.GMS.Facts.LeechOddPairs
public import CFSG.Monster.GMS.S344

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

section Defs

variable {G : Type*} [Group G]

@[expose] def IsOddPair (a w x y : G) : Prop :=
  x ∈ Subgroup.centralizer ({w} : Set G) ∧ y ∈ Subgroup.centralizer ({w} : Set G) ∧
    IsConj a x ∧ IsConj a y ∧ x ≠ y ∧ Odd (orderOf (x * y))

@[expose] def oddNbr (a z₀ x : G) : Set G :=
  {y | IsConj a y ∧ y ≠ x ∧ Odd (orderOf (x * y)) ∧
    ∃ w ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y}, IsConj z₀ w}

@[expose] def OddNbrType (z₀ x y : G) (k : Fin 3) : Prop :=
  ∀ w ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y}, IsConj z₀ w →
    LeechOddType w x y k

@[expose] def oddTypeOrder : Fin 3 → ℕ
  | 0 => 3
  | 1 => 3
  | 2 => 5

@[expose] def oddTypeCard : Fin 3 → ℕ
  | 0 => 2 ^ 18 * 3 ^ 5 * 5
  | 1 => 2 ^ 15 * 3 ^ 4 * 5 * 7
  | 2 => 2 ^ 14 * 3 ^ 2 * 5 ^ 2

end Defs

section Helpers

variable {G : Type*} [Group G]

private theorem mem_centralizer_singleton_comm {x w : G} :
    x ∈ Subgroup.centralizer ({w} : Set G) ↔ w ∈ Subgroup.centralizer ({x} : Set G) := by
  simp only [Subgroup.mem_centralizer_singleton_iff]
  exact ⟨Eq.symm, Eq.symm⟩

private theorem conj_eq_self_of_mem_centralizer {g w : G}
    (hg : g ∈ Subgroup.centralizer ({w} : Set G)) : g * w * g⁻¹ = w := by
  rw [mul_inv_eq_iff_eq_mul]
  exact Subgroup.mem_centralizer_singleton_iff.mp hg

private theorem mem_centralizer_of_conj_eq {c x : G} (h : c * x * c⁻¹ = x) :
    c ∈ Subgroup.centralizer ({x} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp h)

theorem exists_mem_centralizer_conj_of_odd {w x y : G}
    (hxC : x ∈ Subgroup.centralizer ({w} : Set G)) (hyC : y ∈ Subgroup.centralizer ({w} : Set G))
    (hx : x * x = 1) (hy : y * y = 1) (hodd : Odd (orderOf (x * y))) :
    ∃ c ∈ Subgroup.centralizer ({w} : Set G), c * x * c⁻¹ = y := by
  set H := Subgroup.centralizer ({w} : Set G) with hH
  have hx' : (⟨x, hxC⟩ : H) * ⟨x, hxC⟩ = 1 := Subtype.ext hx
  have hy' : (⟨y, hyC⟩ : H) * ⟨y, hyC⟩ = 1 := Subtype.ext hy
  have hodd' : Odd (orderOf ((⟨x, hxC⟩ : H) * ⟨y, hyC⟩)) := by
    rw [← Subgroup.orderOf_coe]
    exact hodd
  obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_of_involutions_of_odd_orderOf_mul hx' hy' hodd')
  refine ⟨c, c.2, ?_⟩
  have := congrArg Subtype.val hc
  simpa using this

private theorem card_leechQ_inf_inf_map {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (z t y : X) :
    Nat.card ↥(leechQ (e z) ⊓ Subgroup.centralizer ({e t} : Set Y) ⊓
        Subgroup.centralizer ({e y} : Set Y)) =
      Nat.card ↥(leechQ z ⊓ Subgroup.centralizer ({t} : Set X) ⊓
        Subgroup.centralizer ({y} : Set X)) := by
  rw [← leechQ_map e z, ← map_centralizer_singleton e t, ← map_centralizer_singleton e y,
    ← Subgroup.map_inf _ _ e.toMonoidHom e.injective,
    ← Subgroup.map_inf _ _ e.toMonoidHom e.injective,
    Subgroup.card_map_of_injective e.injective]

private theorem card_centralizer_inf_inf_map {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (z t y : X) :
    Nat.card ↥(Subgroup.centralizer ({e z} : Set Y) ⊓ Subgroup.centralizer ({e t} : Set Y) ⊓
        Subgroup.centralizer ({e y} : Set Y)) =
      Nat.card ↥(Subgroup.centralizer ({z} : Set X) ⊓ Subgroup.centralizer ({t} : Set X) ⊓
        Subgroup.centralizer ({y} : Set X)) := by
  rw [← map_centralizer_singleton e z, ← map_centralizer_singleton e t,
    ← map_centralizer_singleton e y,
    ← Subgroup.map_inf _ _ e.toMonoidHom e.injective,
    ← Subgroup.map_inf _ _ e.toMonoidHom e.injective,
    Subgroup.card_map_of_injective e.injective]

end Helpers

section LeechOddType

variable {G : Type*} [Group G]

theorem LeechOddType.orderOf_mul {z t y : G} {k : Fin 3} (h : LeechOddType z t y k) :
    orderOf (t * y) = oddTypeOrder k := by
  fin_cases k
  · exact h.1
  · exact h.1
  · exact h.1

theorem LeechOddType.card_triple {z t y : G} {k : Fin 3} (h : LeechOddType z t y k) :
    Nat.card ↥(Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer {t} ⊓
      Subgroup.centralizer {y}) = oddTypeCard k := by
  fin_cases k
  · exact h.2.2
  · exact h.2.2
  · exact h.2.2

theorem LeechOddType.odd_orderOf_mul {z t y : G} {k : Fin 3} (h : LeechOddType z t y k) :
    Odd (orderOf (t * y)) := by
  rw [h.orderOf_mul]
  fin_cases k <;> decide

theorem LeechOddType.conj_iff (c z t y : G) (k : Fin 3) :
    LeechOddType (c * z * c⁻¹) (c * t * c⁻¹) (c * y * c⁻¹) k ↔ LeechOddType z t y k := by
  have hq : Nat.card ↥(leechQ (c * z * c⁻¹) ⊓ Subgroup.centralizer ({c * t * c⁻¹} : Set G) ⊓
        Subgroup.centralizer ({c * y * c⁻¹} : Set G)) =
      Nat.card ↥(leechQ z ⊓ Subgroup.centralizer ({t} : Set G) ⊓
        Subgroup.centralizer ({y} : Set G)) := card_leechQ_inf_inf_map (MulAut.conj c) z t y
  have hc : Nat.card ↥(Subgroup.centralizer ({c * z * c⁻¹} : Set G) ⊓
        Subgroup.centralizer ({c * t * c⁻¹} : Set G) ⊓
        Subgroup.centralizer ({c * y * c⁻¹} : Set G)) =
      Nat.card ↥(Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({t} : Set G) ⊓
        Subgroup.centralizer ({y} : Set G)) := card_centralizer_inf_inf_map (MulAut.conj c) z t y
  have ho : orderOf (c * t * c⁻¹ * (c * y * c⁻¹)) = orderOf (t * y) := by
    rw [← conj_mul_conj, orderOf_conj_eq]
  fin_cases k <;> simp only [LeechOddType, ho, hq, hc]

end LeechOddType

section OddPair

variable {G : Type*} [Group G]

theorem IsOddPair.conj {a w x y : G} (h : IsOddPair a w x y) (c : G) :
    IsOddPair a (c * w * c⁻¹) (c * x * c⁻¹) (c * y * c⁻¹) := by
  obtain ⟨hxC, hyC, hxA, hyA, hxy, hodd⟩ := h
  refine ⟨(mem_centralizer_singleton_map_iff (MulAut.conj c) w x).mpr hxC,
    (mem_centralizer_singleton_map_iff (MulAut.conj c) w y).mpr hyC,
    hxA.trans (isConj_iff.mpr ⟨c, rfl⟩), hyA.trans (isConj_iff.mpr ⟨c, rfl⟩),
    fun e => hxy (mul_left_cancel (mul_right_cancel e)), ?_⟩
  rw [← conj_mul_conj, orderOf_conj_eq]
  exact hodd

theorem IsOddPair.of_mem_inf {a w x y : G} (hx : IsConj a x) (hy : IsConj a y) (hxy : x ≠ y)
    (hodd : Odd (orderOf (x * y)))
    (hw : w ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y}) :
    IsOddPair a w x y :=
  ⟨mem_centralizer_singleton_comm.mpr (Subgroup.mem_inf.mp hw).1,
    mem_centralizer_singleton_comm.mpr (Subgroup.mem_inf.mp hw).2, hx, hy, hxy, hodd⟩

theorem IsOddPair.mem_inf {a w x y : G} (h : IsOddPair a w x y) :
    w ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y} :=
  Subgroup.mem_inf.mpr ⟨mem_centralizer_singleton_comm.mp h.1,
    mem_centralizer_singleton_comm.mp h.2.1⟩

theorem IsOddPair.mem_oddNbr {a z₀ w x y : G} (h : IsOddPair a w x y) (hw : IsConj z₀ w) :
    y ∈ oddNbr a z₀ x :=
  ⟨h.2.2.2.1, h.2.2.2.2.1.symm, h.2.2.2.2.2, w, h.mem_inf, hw⟩

theorem oddNbr.exists_isOddPair {a z₀ x y : G} (hx : IsConj a x) (hy : y ∈ oddNbr a z₀ x) :
    ∃ w, IsConj z₀ w ∧ IsOddPair a w x y := by
  obtain ⟨hyA, hyx, hodd, w, hw, hwB⟩ := hy
  exact ⟨w, hwB, IsOddPair.of_mem_inf hx hyA hyx.symm hodd hw⟩

theorem oddNbr.conj_mem {a z₀ x y c : G} (hc : c ∈ Subgroup.centralizer ({x} : Set G))
    (hy : y ∈ oddNbr a z₀ x) : c * y * c⁻¹ ∈ oddNbr a z₀ x := by
  obtain ⟨hyA, hyx, hodd, w, hw, hwB⟩ := hy
  have hcx := conj_eq_self_of_mem_centralizer hc
  refine ⟨hyA.trans (isConj_iff.mpr ⟨c, rfl⟩),
    fun e => hyx (mul_left_cancel (mul_right_cancel (e.trans hcx.symm))), ?_, c * w * c⁻¹, ?_,
    hwB.trans (isConj_iff.mpr ⟨c, rfl⟩)⟩
  · have : x * (c * y * c⁻¹) = c * (x * y) * c⁻¹ := by rw [conj_mul_conj, hcx]
    rw [this, orderOf_conj_eq]
    exact hodd
  · obtain ⟨hwx, hwy⟩ := Subgroup.mem_inf.mp hw
    have h1 := (mem_centralizer_singleton_map_iff (MulAut.conj c) x w).mpr hwx
    have h2 := (mem_centralizer_singleton_map_iff (MulAut.conj c) y w).mpr hwy
    rw [MulAut.conj_apply, MulAut.conj_apply, hcx] at h1
    exact Subgroup.mem_inf.mpr ⟨h1, h2⟩

theorem OddNbrType.conj {z₀ x y c : G} {k : Fin 3} (hc : c ∈ Subgroup.centralizer ({x} : Set G))
    (h : OddNbrType z₀ x y k) : OddNbrType z₀ x (c * y * c⁻¹) k := by
  intro w' hw' hw'B
  obtain ⟨hwx, hwy⟩ := Subgroup.mem_inf.mp hw'
  have hcx := conj_eq_self_of_mem_centralizer hc
  have hcx' := conj_eq_self_of_mem_centralizer (Subgroup.inv_mem _ hc)
  have h1 := (mem_centralizer_singleton_map_iff (MulAut.conj c⁻¹) x w').mpr hwx
  have h2 := (mem_centralizer_singleton_map_iff (MulAut.conj c⁻¹) (c * y * c⁻¹) w').mpr hwy
  rw [MulAut.conj_apply, MulAut.conj_apply, hcx'] at h1
  rw [MulAut.conj_apply, MulAut.conj_apply, show c⁻¹ * (c * y * c⁻¹) * c⁻¹⁻¹ = y by group] at h2
  have hwB : IsConj z₀ (c⁻¹ * w' * c⁻¹⁻¹) := hw'B.trans (isConj_iff.mpr ⟨c⁻¹, rfl⟩)
  have := (LeechOddType.conj_iff c (c⁻¹ * w' * c⁻¹⁻¹) x y k).mpr
    (h _ (Subgroup.mem_inf.mpr ⟨h1, h2⟩) hwB)
  rwa [show c * (c⁻¹ * w' * c⁻¹⁻¹) * c⁻¹ = w' by group, hcx] at this

end OddPair

section Odd

variable {G : Type*} [Group G]

theorem not_mem_leechQ_of_odd {a : G} (ha : orderOf a = 2) {w x y : G} (h : IsOddPair a w x y) :
    x ∉ leechQ w ∧ y ∉ leechQ w ∧
      ∃ g ∈ Subgroup.centralizer ({w} : Set G), g * x * g⁻¹ = y := by
  obtain ⟨hxC, hyC, hxA, hyA, hxy, hodd⟩ := h
  have hxx : x * x = 1 := mul_self_eq_one_of_orderOf ((orderOf_eq_of_isConj hxA).symm.trans ha)
  have hyy : y * y = 1 := mul_self_eq_one_of_orderOf ((orderOf_eq_of_isConj hyA).symm.trans ha)
  obtain ⟨c, hc, hcxy⟩ := exists_mem_centralizer_conj_of_odd hxC hyC hxx hyy hodd
  have hnot : x ∈ leechQ w → False := by
    intro hxQ
    have hyQ : y ∈ leechQ w := hcxy ▸ conj_mem_leechQ hc hxQ
    obtain ⟨n, hn⟩ := exists_orderOf_eq_two_pow_of_mem_leechQ ((leechQ w).mul_mem hxQ hyQ)
    have hn0 : n = 0 := by
      by_contra hn0
      obtain ⟨m, hm⟩ := hodd
      rw [hn] at hm
      have : 2 ∣ 2 ^ n := dvd_pow_self 2 hn0
      omega
    rw [hn0, pow_zero, orderOf_eq_one_iff] at hn
    exact hxy ((eq_inv_of_mul_eq_one_left hn).trans (inv_eq_of_mul_eq_one_right hyy))
  refine ⟨hnot, fun hyQ => hnot ?_, c, hc, hcxy⟩
  have hx : x = c⁻¹ * y * c⁻¹⁻¹ := by rw [← hcxy]; group
  rw [hx]
  exact conj_mem_leechQ (Subgroup.inv_mem _ hc) hyQ

theorem s348_card {z₀ x y : G} {k : Fin 3} (hk : OddNbrType z₀ x y k) {w : G}
    (hw : w ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y})
    (hwB : IsConj z₀ w) :
    orderOf (x * y) = oddTypeOrder k ∧
      Nat.card ↥(Subgroup.centralizer ({w} : Set G) ⊓ Subgroup.centralizer {x} ⊓
        Subgroup.centralizer {y}) = oddTypeCard k :=
  ⟨(hk w hw hwB).orderOf_mul, (hk w hw hwB).card_triple⟩

end Odd

section Main

variable {G : Type} [Group G] [Finite G] {d₀ : B}

theorem isLeechCentralLift_of_not_mem_leechQ
    (hSLS : SLSStatement d₀) (hTV : TableVIn G)
    (hL : LeechStatement) {a z₀ : G} (hG : GMSF1Type d₀ a z₀) {w x : G} (hw : IsConj z₀ w)
    (hxC : x ∈ Subgroup.centralizer ({w} : Set G)) (hxA : IsConj a x) (hxQ : x ∉ leechQ w) :
    IsLeechCentralLift w x := by
  obtain ⟨b, z, u, h⟩ := exists_twoClasses hSLS hTV hL hG
  have hx2 : orderOf x = 2 := (orderOf_eq_of_isConj hxA).symm.trans hG.1.1
  refine ⟨hxC, hx2, hxQ, ?_, ?_⟩
  · rw [card_centralizer_inf_of_not_mem_leechQ hSLS hTV hL hG hw hxC hxQ hxA]
    rfl
  · intro g _ hg
    exact hxQ (h.mem_leechQ_of_isConj_mul hxA hw
      (Subgroup.mem_centralizer_singleton_iff.mp hxC) (hxA.trans (isConj_iff.mpr ⟨g, hg⟩)))

theorem hasCommonLeechFour_of_isOddPair
    (hSLS : SLSStatement d₀) (hTV : TableVIn G)
    (hL : LeechStatement) (hT4 : TableIVIn G) {a z₀ : G} (hG : GMSF1Type d₀ a z₀) {w : G}
    (hw : IsConj z₀ w) {x y : G} (h : IsOddPair a w x y) : HasCommonLeechFour w x y := by
  obtain ⟨w₀, hw₀, hw₀w, hz₀w₀, -⟩ :=
    s344_exists hSLS hTV hL hT4 hG hw h.1 h.2.1 h.2.2.1 h.2.2.2.1
  obtain ⟨hw₀', hw₀y⟩ := Subgroup.mem_inf.mp hw₀
  obtain ⟨hw₀Q, hw₀x⟩ := Subgroup.mem_inf.mp hw₀'
  have hord : orderOf w₀ = 2 := (orderOf_eq_of_isConj hz₀w₀).symm.trans hG.2.1
  have hsq : w₀ * w₀ = 1 := by
    have := pow_orderOf_eq_one w₀
    rwa [hord, pow_two] at this
  refine ⟨w₀, ⟨hw₀Q, ?_, hw₀w, hsq, ?_⟩, hw₀x, hw₀y⟩
  · rintro rfl
    simp at hord
  · exact card_centralizer_inf_of_mem_leechQ_four hSLS hTV hL hG hw hw₀Q hw₀w hz₀w₀

theorem s347_type
    (hSLS : SLSStatement d₀) (hTV : TableVIn G) (hL : LeechStatement)
    (hLO : LeechOddPairStatement) (hT4 : TableIVIn G)
    {a z₀ : G} (hG : GMSF1Type d₀ a z₀) {w : G} (hw : IsConj z₀ w)
    {x y : G} (h : IsOddPair a w x y) : ∃! k, LeechOddType w x y k := by
  obtain ⟨hxQ, -, g, hg, hgxy⟩ := not_mem_leechQ_of_odd hG.1.1 h
  have hlift := isLeechCentralLift_of_not_mem_leechQ hSLS hTV hL hG hw h.1 h.2.2.1 hxQ
  exact (hLO G w (hG.2.of_isConj hw) x hlift).1 y ⟨g, hg, hgxy⟩ h.2.2.2.2.1.symm h.2.2.2.2.2
    (hasCommonLeechFour_of_isOddPair hSLS hTV hL hT4 hG hw h)

theorem s347_orbit
    (hSLS : SLSStatement d₀) (hTV : TableVIn G) (hL : LeechStatement)
    (hLO : LeechOddPairStatement) (hT4 : TableIVIn G)
    {a z₀ : G} (hG : GMSF1Type d₀ a z₀) {w : G} (hw : IsConj z₀ w)
    {x y x' y' : G} (h : IsOddPair a w x y) (h' : IsOddPair a w x' y') {k : Fin 3}
    (hk : LeechOddType w x y k) (hk' : LeechOddType w x' y' k) :
    ∃ g ∈ Subgroup.centralizer ({w} : Set G), g * x * g⁻¹ = x' ∧ g * y * g⁻¹ = y' := by
  obtain ⟨hxQ, -, -⟩ := not_mem_leechQ_of_odd hG.1.1 h
  obtain ⟨hxQ', -, -⟩ := not_mem_leechQ_of_odd hG.1.1 h'
  obtain ⟨g₁, hg₁, hg₁x⟩ := isConj_of_not_mem_leechQ hSLS hTV hL hG hw h.1 h'.1 hxQ hxQ' h.2.2.1
    h'.2.2.1
  have hg₁w := conj_eq_self_of_mem_centralizer hg₁
  have hY : IsOddPair a w x' (g₁ * y * g₁⁻¹) := by
    have := h.conj g₁
    rwa [hg₁w, hg₁x] at this
  have hk₁ : LeechOddType w x' (g₁ * y * g₁⁻¹) k := by
    have := (LeechOddType.conj_iff g₁ w x y k).mpr hk
    rwa [hg₁w, hg₁x] at this
  have hlift := isLeechCentralLift_of_not_mem_leechQ hSLS hTV hL hG hw h'.1 h'.2.2.1 hxQ'
  obtain ⟨g₂, hg₂, hg₂y⟩ := (hLO G w (hG.2.of_isConj hw) x' hlift).2.2.1 k _ y'
    (not_mem_leechQ_of_odd hG.1.1 hY).2.2 (not_mem_leechQ_of_odd hG.1.1 h').2.2
    (hasCommonLeechFour_of_isOddPair hSLS hTV hL hT4 hG hw hY)
    (hasCommonLeechFour_of_isOddPair hSLS hTV hL hT4 hG hw h') hk₁ hk'
  obtain ⟨hg₂w, hg₂x⟩ := Subgroup.mem_inf.mp hg₂
  have hg₂x' := conj_eq_self_of_mem_centralizer hg₂x
  refine ⟨g₂ * g₁, Subgroup.mul_mem _ hg₂w hg₁, ?_, ?_⟩
  · calc g₂ * g₁ * x * (g₂ * g₁)⁻¹ = g₂ * (g₁ * x * g₁⁻¹) * g₂⁻¹ := by group
      _ = x' := by rw [hg₁x, hg₂x']
  · calc g₂ * g₁ * y * (g₂ * g₁)⁻¹ = g₂ * (g₁ * y * g₁⁻¹) * g₂⁻¹ := by group
      _ = y' := hg₂y

theorem s347_exists
    (hSLS : SLSStatement d₀) (hTV : TableVIn G) (hL : LeechStatement)
    (hLO : LeechOddPairStatement) {a z₀ : G} (hG : GMSF1Type d₀ a z₀) {w : G} (hw : IsConj z₀ w)
    {x : G} (hxC : x ∈ Subgroup.centralizer ({w} : Set G)) (hxA : IsConj a x) (hxQ : x ∉ leechQ w)
    (k : Fin 3) : ∃ y, IsOddPair a w x y ∧ LeechOddType w x y k := by
  have hlift := isLeechCentralLift_of_not_mem_leechQ hSLS hTV hL hG hw hxC hxA hxQ
  obtain ⟨y, ⟨g, hg, hgy⟩, hyx, -, hty⟩ := (hLO G w (hG.2.of_isConj hw) x hlift).2.1 k
  refine ⟨y, ⟨hxC, ?_, hxA, hxA.trans (isConj_iff.mpr ⟨g, hgy⟩), hyx.symm, hty.odd_orderOf_mul⟩,
    hty⟩
  rw [← hgy]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hxC) (Subgroup.inv_mem _ hg)

theorem s347_isConj_mul
    (hSLS : SLSStatement d₀) (hTV : TableVIn G) (hL : LeechStatement)
    {a z₀ : G} (hG : GMSF1Type d₀ a z₀) {w : G} (hw : IsConj z₀ w) {x y : G}
    (h : IsOddPair a w x y) : IsConj z₀ (x * w) ∧ IsConj z₀ (y * w) := by
  obtain ⟨b, z, u, hT⟩ := exists_twoClasses hSLS hTV hL hG
  obtain ⟨hxQ, hyQ, -⟩ := not_mem_leechQ_of_odd hG.1.1 h
  have key : ∀ {t : G}, t ∈ Subgroup.centralizer ({w} : Set G) → IsConj a t → t ∉ leechQ w →
      IsConj z₀ (t * w) := by
    intro t htC htA htQ
    obtain ⟨g, hg1, hg2⟩ := hT.exists_conj_of_not_mem_leechQ hw htA htC htQ
    refine hT.isConj_au.trans (isConj_iff.mpr ⟨g, ?_⟩)
    rw [← hg1, ← hg2]
    group
  exact ⟨key h.1 h.2.2.1 hxQ, key h.2.1 h.2.2.2.1 hyQ⟩

end Main

section Sylow

variable {G : Type*} [Group G] [Finite G]

private theorem exists_mem_center_ne_one {P : Subgroup G} (hP : IsPGroup 2 P) (hne : P ≠ ⊥) :
    ∃ s ∈ P, s ≠ 1 ∧ ∀ s' ∈ P, s * s' = s' * s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).mpr hne
  have : Nontrivial (Subgroup.center P) := hP.center_nontrivial
  obtain ⟨s, hs⟩ := exists_ne (1 : Subgroup.center P)
  refine ⟨(s.1 : G), s.1.2, fun h => hs ?_, fun s' hs' => ?_⟩
  · exact Subtype.ext (Subtype.ext h)
  · exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp s.2 ⟨s', hs'⟩)).symm

private theorem mem_of_forall_center {P₀ : Subgroup G} {w : G} (hP₀ : IsPGroup 2 P₀)
    (hne : P₀ ≠ ⊥)
    (hZ : ∀ s ∈ P₀, (∀ s' ∈ P₀, s * s' = s' * s) → s = 1 ∨ s = w) : w ∈ P₀ := by
  obtain ⟨s, hsP, hs1, hsc⟩ := exists_mem_center_ne_one hP₀ hne
  rcases hZ s hsP hsc with h | h
  · exact absurd h hs1
  · rw [← h]
    exact hsP

private theorem eq_of_isPGroup_of_center {K T P₀ : Subgroup G} {w : G}
    (hT : ∀ g ∈ K, g * w = w * g → g ∈ T) (hP₀T : P₀ ≤ T) (hP₀ : IsPGroup 2 P₀) (hne : P₀ ≠ ⊥)
    (hmax : ∀ R : Subgroup G, R ≤ T → IsPGroup 2 R → P₀ ≤ R → R = P₀)
    (hZ : ∀ s ∈ P₀, (∀ s' ∈ P₀, s * s' = s' * s) → s = 1 ∨ s = w)
    {R : Subgroup G} (hRK : R ≤ K) (hR : IsPGroup 2 R) (hP₀R : P₀ ≤ R) : R = P₀ := by
  have hw : w ∈ P₀ := mem_of_forall_center hP₀ hne hZ
  have hRne : R ≠ ⊥ := fun h => hne (le_bot_iff.mp (h ▸ hP₀R))
  obtain ⟨s, hsR, hs1, hsc⟩ := exists_mem_center_ne_one hR hRne
  have hsT : s ∈ T := hT s (hRK hsR) (hsc w (hP₀R hw))
  have hR'R : P₀ ⊔ Subgroup.zpowers s ≤ R := sup_le hP₀R ((Subgroup.zpowers_le).mpr hsR)
  have hR'T : P₀ ⊔ Subgroup.zpowers s ≤ T := sup_le hP₀T ((Subgroup.zpowers_le).mpr hsT)
  have hR'eq : P₀ ⊔ Subgroup.zpowers s = P₀ := hmax _ hR'T (hR.to_le hR'R) le_sup_left
  have hsP₀ : s ∈ P₀ := by
    rw [← hR'eq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers s)
  have hsw : s = w := (hZ s hsP₀ (fun s' hs' => hsc s' (hP₀R hs'))).resolve_left hs1
  have hRT : R ≤ T := fun r hr => hT r (hRK hr) (by rw [← hsw]; exact (hsc r hr).symm)
  exact hmax R hRT hR hP₀R

omit [Finite G] in
private theorem exists_sylow_of_maximal {K P : Subgroup G} (hPK : P ≤ K) (hP : IsPGroup 2 P)
    (hmax : ∀ R : Subgroup G, R ≤ K → IsPGroup 2 R → P ≤ R → R = P) :
    ∃ S : Sylow 2 ↥K, ∀ s : ↥K, s ∈ S ↔ (s : G) ∈ P := by
  refine ⟨⟨P.subgroupOf K, hP.comap_subtype, fun {Q} hQ hle => ?_⟩, fun s => Iff.rfl⟩
  have hQ' : Q.map K.subtype = P :=
    hmax _ (Subgroup.map_subtype_le Q) (hQ.map K.subtype) (fun p hp =>
      ⟨⟨p, hPK hp⟩, hle (show (⟨p, hPK hp⟩ : K) ∈ P.subgroupOf K from hp), rfl⟩)
  ext q
  constructor
  · intro hq
    exact hQ' ▸ Subgroup.mem_map_of_mem K.subtype hq
  · intro hq
    exact hle hq

private theorem factorization_two_pow_mul_odd {n m : ℕ} (hm : Odd m) :
    (2 ^ n * m).factorization 2 = n := by
  rw [Nat.factorization_mul (pow_ne_zero _ two_ne_zero) hm.pos.ne', Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by rwa [← even_iff_two_dvd, Nat.not_even_iff_odd]),
    smul_eq_mul, mul_one, add_zero]

end Sylow

section SylowMain

variable {G : Type} [Group G] [Finite G] {d₀ : B}

theorem s347_sylow
    (hSLS : SLSStatement d₀) (hTV : TableVIn G) (hL : LeechStatement)
    (hLO : LeechOddPairStatement) (hT4 : TableIVIn G)
    {a z₀ : G} (hG : GMSF1Type d₀ a z₀) {w : G} (hw : IsConj z₀ w)
    {x y : G} (h : IsOddPair a w x y) {k : Fin 3} (hk : k ≠ 0) (hty : LeechOddType w x y k) :
    ∃ S : Sylow 2 ↥(Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y}),
      (∀ s ∈ S, (s : G) ∈ Subgroup.centralizer ({w} : Set G)) ∧
      ∀ s : ↥(Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y}),
        (s ∈ S ∧ ∀ s' ∈ S, s * s' = s' * s) ↔ ((s : G) = 1 ∨ (s : G) = w) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hxQ, -, g, hg, hgxy⟩ := not_mem_leechQ_of_odd hG.1.1 h
  have hlift := isLeechCentralLift_of_not_mem_leechQ hSLS hTV hL hG hw h.1 h.2.2.1 hxQ
  have hZ := (hLO G w (hG.2.of_isConj hw) x hlift).2.2.2 k y hk ⟨g, hg, hgxy⟩
    (hasCommonLeechFour_of_isOddPair hSLS hTV hL hT4 hG hw h) hty
  set K := Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y} with hK
  set T := leechTriple w x y with hT
  have hTK : T ≤ K := inf_le_inf_right _ inf_le_right
  have hTw : T ≤ Subgroup.centralizer ({w} : Set G) := inf_le_left.trans inf_le_left
  have h2 : 2 ∣ Nat.card T := by
    have hc : Nat.card T = oddTypeCard k := hty.card_triple
    rw [hc]
    fin_cases k
    · exact absurd rfl hk
    · norm_num [oddTypeCard]
    · norm_num [oddTypeCard]
  obtain S₀ : Sylow 2 ↥T := default
  set P₀ : Subgroup G := (S₀ : Subgroup ↥T).map T.subtype with hP₀
  have hP₀T : P₀ ≤ T := Subgroup.map_subtype_le _
  have hP₀p : IsPGroup 2 P₀ := S₀.isPGroup'.map T.subtype
  have hne : P₀ ≠ ⊥ := by
    intro hbot
    exact S₀.ne_bot_of_dvd_card h2
      (Subgroup.map_injective T.subtype_injective (hbot.trans (Subgroup.map_bot _).symm))
  have hmax : ∀ R : Subgroup G, R ≤ T → IsPGroup 2 R → P₀ ≤ R → R = P₀ := by
    intro R hRT hR hP₀R
    have heq : R.subgroupOf T = (S₀ : Subgroup ↥T) :=
      S₀.is_maximal' hR.comap_subtype (fun s hs => hP₀R ⟨s, hs, rfl⟩)
    ext g
    refine ⟨fun hg => ?_, fun hg => hP₀R hg⟩
    have hmem : (⟨g, hRT hg⟩ : T) ∈ R.subgroupOf T := hg
    rw [heq] at hmem
    exact ⟨_, hmem, rfl⟩
  have hZ' : ∀ s ∈ P₀, (∀ s' ∈ P₀, s * s' = s' * s) → s = 1 ∨ s = w := by
    intro s hs hc
    obtain ⟨s₀, hs₀, rfl⟩ := Subgroup.mem_map.mp hs
    exact hZ S₀ s₀ hs₀ (fun s' hs' => Subtype.ext (hc (s' : G) ⟨s', hs', rfl⟩))
  have hKT : ∀ g ∈ K, g * w = w * g → g ∈ T := fun g hg hgw =>
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr hgw,
      (Subgroup.mem_inf.mp hg).1⟩, (Subgroup.mem_inf.mp hg).2⟩
  have hwP₀ : w ∈ P₀ := mem_of_forall_center hP₀p hne hZ'
  obtain ⟨S, hS⟩ := exists_sylow_of_maximal (hP₀T.trans hTK) hP₀p
    (fun R hRK hR hP₀R => eq_of_isPGroup_of_center hKT hP₀T hP₀p hne hmax hZ' hRK hR hP₀R)
  refine ⟨S, fun s hs => hTw (hP₀T ((hS s).mp hs)), fun s => ⟨?_, ?_⟩⟩
  · rintro ⟨hs, hc⟩
    refine hZ' s ((hS s).mp hs) (fun s' hs' => ?_)
    exact congrArg Subtype.val (hc ⟨s', hTK (hP₀T hs')⟩ ((hS _).mpr hs'))
  · rintro (h1 | h1)
    · have : s = 1 := Subtype.ext h1
      subst this
      exact ⟨one_mem S, fun s' _ => by rw [one_mul, mul_one]⟩
    · refine ⟨(hS s).mpr (h1 ▸ hwP₀), fun s' hs' => Subtype.ext ?_⟩
      have := hTw (hP₀T ((hS s').mp hs'))
      show (s : G) * (s' : G) = (s' : G) * (s : G)
      rw [h1]
      exact (Subgroup.mem_centralizer_singleton_iff.mp this).symm

theorem s347_factorization
    (hSLS : SLSStatement d₀) (hTV : TableVIn G)
    (hL : LeechStatement) (hLO : LeechOddPairStatement) (hT4 : TableIVIn G)
    {a z₀ : G} (hG : GMSF1Type d₀ a z₀)
    {w : G} (hw : IsConj z₀ w) {x y : G} (h : IsOddPair a w x y) {k : Fin 3} (hk : k ≠ 0)
    (hty : LeechOddType w x y k) :
    (Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y})).factorization 2 =
      (Nat.card ↥(leechTriple w x y)).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y} with hK
  obtain ⟨S, hSw, -⟩ := s347_sylow hSLS hTV hL hLO hT4 hG hw h hk hty
  have hcard : Nat.card S = 2 ^ (Nat.card K).factorization 2 := S.card_eq_multiplicity
  have hST : (S : Subgroup ↥K).map K.subtype ≤ leechTriple w x y := by
    rintro _ ⟨s, hs, rfl⟩
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hSw s hs, (Subgroup.mem_inf.mp s.2).1⟩,
      (Subgroup.mem_inf.mp s.2).2⟩
  have hd1 : Nat.card S ∣ Nat.card ↥(leechTriple w x y) := by
    have := Subgroup.card_dvd_of_le hST
    rwa [Subgroup.card_map_of_injective K.subtype_injective] at this
  have hd2 : Nat.card ↥(leechTriple w x y) ∣ Nat.card K :=
    Subgroup.card_dvd_of_le (inf_le_inf_right _ inf_le_right)
  refine le_antisymm ?_ ?_
  · rw [hcard] at hd1
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp hd1
  · exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr hd2 2

theorem s347_factorization_three_C
    (hSLS : SLSStatement d₀) (hTV : TableVIn G)
    (hL : LeechStatement) (hLO : LeechOddPairStatement) (hT4 : TableIVIn G)
    {a z₀ : G} (hG : GMSF1Type d₀ a z₀)
    {w : G} (hw : IsConj z₀ w) {x y : G} (h : IsOddPair a w x y) (hty : LeechOddType w x y 1) :
    (Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y})).factorization 2 =
      15 := by
  rw [s347_factorization hSLS hTV hL hLO hT4 hG hw h (k := 1) (by decide) hty, leechTriple,
    hty.card_triple, oddTypeCard,
    show (2 ^ 15 * 3 ^ 4 * 5 * 7 : ℕ) = 2 ^ 15 * (3 ^ 4 * 5 * 7) by ring]
  exact factorization_two_pow_mul_odd (by decide)

theorem s347_factorization_five_A
    (hSLS : SLSStatement d₀) (hTV : TableVIn G)
    (hL : LeechStatement) (hLO : LeechOddPairStatement) (hT4 : TableIVIn G)
    {a z₀ : G} (hG : GMSF1Type d₀ a z₀)
    {w : G} (hw : IsConj z₀ w) {x y : G} (h : IsOddPair a w x y) (hty : LeechOddType w x y 2) :
    (Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y})).factorization 2 =
      14 := by
  rw [s347_factorization hSLS hTV hL hLO hT4 hG hw h (k := 2) (by decide) hty, leechTriple,
    hty.card_triple, oddTypeCard,
    show (2 ^ 14 * 3 ^ 2 * 5 ^ 2 : ℕ) = 2 ^ 14 * (3 ^ 2 * 5 ^ 2) by ring]
  exact factorization_two_pow_mul_odd (by decide)

theorem le_factorization_of_leechOddType_zero {w x y : G} (hty : LeechOddType w x y 0) :
    18 ≤ (Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y})).factorization
      2 := by
  have hd : Nat.card ↥(leechTriple w x y) ∣
      Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y}) :=
    Subgroup.card_dvd_of_le (inf_le_inf_right _ inf_le_right)
  have h18 : 2 ^ 18 ∣ Nat.card ↥(leechTriple w x y) := by
    rw [leechTriple, hty.card_triple, oddTypeCard]
    exact ⟨3 ^ 5 * 5, by ring⟩
  exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp
    (h18.trans hd)

end SylowMain

section Fusion

variable {G : Type} [Group G] [Finite G] {d₀ : B}

theorem s347_not_isConj
    (hSLS : SLSStatement d₀) (hTV : TableVIn G) (hL : LeechStatement)
    (hLO : LeechOddPairStatement) (hT4 : TableIVIn G)
    {a z₀ : G} (hG : GMSF1Type d₀ a z₀) {w w' : G}
    (hw' : IsConj z₀ w') {x y y' : G} (hk : LeechOddType w x y 0) (h' : IsOddPair a w' x y')
    (hk' : LeechOddType w' x y' 1) :
    ¬ ∃ c ∈ Subgroup.centralizer ({x} : Set G), c * y * c⁻¹ = y' := by
  rintro ⟨c, hc, rfl⟩
  have h15 := s347_factorization_three_C hSLS hTV hL hLO hT4 hG hw' h' hk'
  have h18 := le_factorization_of_leechOddType_zero hk
  have hcard := card_centralizer_inf_conj c x y
  rw [conj_eq_self_of_mem_centralizer hc] at hcard
  rw [hcard] at h15
  omega

theorem s347_type_indep
    (hSLS : SLSStatement d₀) (hTV : TableVIn G) (hL : LeechStatement)
    (hLO : LeechOddPairStatement) (hT4 : TableIVIn G)
    {a z₀ : G} (hG : GMSF1Type d₀ a z₀) {w w' : G}
    (hw : IsConj z₀ w) (hw' : IsConj z₀ w') {x y : G} (h : IsOddPair a w x y)
    (h' : IsOddPair a w' x y) {k : Fin 3} (hk : LeechOddType w x y k) :
    LeechOddType w' x y k := by
  obtain ⟨k', hk'⟩ := (s347_type hSLS hTV hL hLO hT4 hG hw' h').exists
  have hne : ∀ {w₁ w₂ : G}, IsConj z₀ w₂ → IsOddPair a w₂ x y → LeechOddType w₁ x y 0 →
      LeechOddType w₂ x y 1 → False := fun hw₂ h₂ h0 h1 =>
    s347_not_isConj hSLS hTV hL hLO hT4 hG hw₂ h0 h₂ h1
      ⟨1, Subgroup.one_mem _, by rw [inv_one, mul_one, one_mul]⟩
  have hkk : k = k' := by
    fin_cases k <;> fin_cases k' <;> first
      | rfl
      | exact absurd (hk.orderOf_mul.symm.trans hk'.orderOf_mul) (by decide)
      | exact (hne hw' h' hk hk').elim
      | exact (hne hw h hk' hk).elim
  exact hkk ▸ hk'

theorem s347_transitive
    (hSLS : SLSStatement d₀) (hTV : TableVIn G) (hL : LeechStatement)
    (hLO : LeechOddPairStatement) (hT4 : TableIVIn G)
    {a z₀ : G} (hG : GMSF1Type d₀ a z₀) {x y : G} (hx : IsConj a x)
    (hy : IsConj a y) (hxy : x ≠ y) (hodd : Odd (orderOf (x * y))) {w w' : G}
    (hw : w ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y})
    (hw' : w' ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y})
    (hwB : IsConj z₀ w) (hwB' : IsConj z₀ w') :
    ∃ g ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y}, g * w * g⁻¹ = w' := by
  have hYw : IsOddPair a w x y := IsOddPair.of_mem_inf hx hy hxy hodd hw
  have hYw' : IsOddPair a w' x y := IsOddPair.of_mem_inf hx hy hxy hodd hw'
  obtain ⟨k, hk⟩ := (s347_type hSLS hTV hL hLO hT4 hG hwB hYw).exists
  have hk' : LeechOddType w' x y k := s347_type_indep hSLS hTV hL hLO hT4 hG hwB hwB' hYw hYw' hk
  obtain ⟨h, hh⟩ := isConj_iff.mp (hwB.symm.trans hwB')
  have hYc : IsOddPair a w' (h * x * h⁻¹) (h * y * h⁻¹) := by
    have := hYw.conj h
    rwa [hh] at this
  have hkc : LeechOddType w' (h * x * h⁻¹) (h * y * h⁻¹) k := by
    have := (LeechOddType.conj_iff h w x y k).mpr hk
    rwa [hh] at this
  obtain ⟨g, hg, hgx, hgy⟩ := s347_orbit hSLS hTV hL hLO hT4 hG hwB' hYw' hYc hk' hkc
  have hgw := conj_eq_self_of_mem_centralizer (Subgroup.inv_mem _ hg)
  refine ⟨g⁻¹ * h, Subgroup.mem_inf.mpr
    ⟨mem_centralizer_of_conj_eq ?_, mem_centralizer_of_conj_eq ?_⟩, ?_⟩
  · calc g⁻¹ * h * x * (g⁻¹ * h)⁻¹ = g⁻¹ * (h * x * h⁻¹) * g := by group
      _ = x := by rw [← hgx]; group
  · calc g⁻¹ * h * y * (g⁻¹ * h)⁻¹ = g⁻¹ * (h * y * h⁻¹) * g := by group
      _ = y := by rw [← hgy]; group
  · calc g⁻¹ * h * w * (g⁻¹ * h)⁻¹ = g⁻¹ * (h * w * h⁻¹) * g := by group
      _ = w' := by rw [hh]; simpa using hgw

end Fusion

section Nbr

variable {G : Type} [Group G] [Finite G] {d₀ : B}

theorem s348_type
    (hSLS : SLSStatement d₀) (hTV : TableVIn G) (hL : LeechStatement)
    (hLO : LeechOddPairStatement) (hT4 : TableIVIn G)
    {a z₀ : G} (hG : GMSF1Type d₀ a z₀) {x y : G} (hx : IsConj a x)
    (hy : y ∈ oddNbr a z₀ x) : ∃! k, OddNbrType z₀ x y k := by
  obtain ⟨w₀, hw₀B, hY₀⟩ := oddNbr.exists_isOddPair hx hy
  obtain ⟨k, hk, huniq⟩ := s347_type hSLS hTV hL hLO hT4 hG hw₀B hY₀
  refine ⟨k, fun w hw hwB => ?_, fun k' hk' => huniq k' (hk' w₀ hY₀.mem_inf hw₀B)⟩
  obtain ⟨hyA, hyx, hodd, -⟩ := hy
  exact s347_type_indep hSLS hTV hL hLO hT4 hG hw₀B hwB hY₀
    (IsOddPair.of_mem_inf hx hyA hyx.symm hodd hw) hk

theorem s348_orbit
    (hSLS : SLSStatement d₀) (hTV : TableVIn G) (hL : LeechStatement)
    (hLO : LeechOddPairStatement) (hT4 : TableIVIn G)
    {a z₀ : G} (hG : GMSF1Type d₀ a z₀) {x y y' : G}
    (hx : IsConj a x) (hy : y ∈ oddNbr a z₀ x) (hy' : y' ∈ oddNbr a z₀ x) {k : Fin 3}
    (hk : OddNbrType z₀ x y k) (hk' : OddNbrType z₀ x y' k) :
    ∃ c ∈ Subgroup.centralizer ({x} : Set G), c * y * c⁻¹ = y' := by
  obtain ⟨w, hwB, hYw⟩ := oddNbr.exists_isOddPair hx hy
  obtain ⟨w', hwB', hYw'⟩ := oddNbr.exists_isOddPair hx hy'
  obtain ⟨h, hh⟩ := isConj_iff.mp (hwB'.symm.trans hwB)
  have hYc : IsOddPair a w (h * x * h⁻¹) (h * y' * h⁻¹) := by
    have := hYw'.conj h
    rwa [hh] at this
  have hkc : LeechOddType w (h * x * h⁻¹) (h * y' * h⁻¹) k := by
    have := (LeechOddType.conj_iff h w' x y' k).mpr (hk' w' hYw'.mem_inf hwB')
    rwa [hh] at this
  obtain ⟨g, -, hgx, hgy⟩ :=
    s347_orbit hSLS hTV hL hLO hT4 hG hwB hYw hYc (hk w hYw.mem_inf hwB) hkc
  refine ⟨h⁻¹ * g, mem_centralizer_of_conj_eq ?_, ?_⟩
  · calc h⁻¹ * g * x * (h⁻¹ * g)⁻¹ = h⁻¹ * (g * x * g⁻¹) * h := by group
      _ = x := by rw [hgx]; group
  · calc h⁻¹ * g * y * (h⁻¹ * g)⁻¹ = h⁻¹ * (g * y * g⁻¹) * h := by group
      _ = y' := by rw [hgy]; group

theorem s348_exists
    (hSLS : SLSStatement d₀) (hTV : TableVIn G) (hL : LeechStatement)
    (hLO : LeechOddPairStatement) (hT4 : TableIVIn G)
    {a z₀ : G} (hG : GMSF1Type d₀ a z₀) {x : G} (hx : IsConj a x)
    (k : Fin 3) : ∃ y ∈ oddNbr a z₀ x, OddNbrType z₀ x y k := by
  obtain ⟨b, z, u, hT⟩ := exists_twoClasses hSLS hTV hL hG
  obtain ⟨c, hc⟩ := isConj_iff.mp hx
  have hwB : IsConj z₀ (c * u * c⁻¹) := hT.isConj_u.trans (isConj_iff.mpr ⟨c, rfl⟩)
  have hxC : x ∈ Subgroup.centralizer ({c * u * c⁻¹} : Set G) := by
    rw [← hc]
    exact (mem_centralizer_singleton_map_iff (MulAut.conj c) u a).mpr
      (mem_centralizer_singleton_comm.mpr hT.tableV.mem_u)
  have hxQ : x ∉ leechQ (c * u * c⁻¹) := by
    intro hQ
    rw [mem_leechQ_conj_iff, ← hc] at hQ
    have e : c⁻¹ * (c * a * c⁻¹) * c = a := by group
    rw [e] at hQ
    exact hT.not_mem_leechQ_u hQ
  obtain ⟨y, hY, hty⟩ := s347_exists hSLS hTV hL hLO hG hwB hxC hx hxQ k
  refine ⟨y, hY.mem_oddNbr hwB, fun w' hw' hw'B => ?_⟩
  exact s347_type_indep hSLS hTV hL hLO hT4 hG hwB hw'B hY
    (IsOddPair.of_mem_inf hx hY.2.2.2.1 hY.2.2.2.2.1 hY.2.2.2.2.2 hw') hty

theorem s348_transitive
    (hSLS : SLSStatement d₀) (hTV : TableVIn G) (hL : LeechStatement)
    (hLO : LeechOddPairStatement) (hT4 : TableIVIn G)
    {a z₀ : G} (hG : GMSF1Type d₀ a z₀) {x y : G} (hx : IsConj a x)
    (hy : y ∈ oddNbr a z₀ x) {w w' : G}
    (hw : w ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y})
    (hw' : w' ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y})
    (hwB : IsConj z₀ w) (hwB' : IsConj z₀ w') :
    ∃ g ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y}, g * w * g⁻¹ = w' := by
  obtain ⟨hyA, hyx, hodd, -⟩ := hy
  exact s347_transitive hSLS hTV hL hLO hT4 hG hx hyA hyx.symm hodd hw hw' hwB hwB'

end Nbr

end CFSG.Monster.GMS
