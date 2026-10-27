module

public import CFSG.Monster.GMS.S31Two
public import CFSG.Monster.GMS.Facts.LeechInvolutions
import CFSG.Monster.GMS.F1Basic
import CFSG.Monster.GMS.NotConj

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G] {d₀ : B}

structure TwoClasses (a z₀ b z u : G) : Prop where
  tableV : TableV a b z u
  orderOf_a : orderOf a = 2
  orderOf_z₀ : orderOf z₀ = 2
  not_isConj : ¬ IsConj a z₀
  isConj_b : IsConj a b
  isConj_z : IsConj z₀ z
  isConj_az : IsConj a (a * z)
  mem_leechQ_z : a ∈ leechQ z
  isConj_u : IsConj z₀ u
  isConj_au : IsConj z₀ (a * u)
  not_mem_leechQ_u : a ∉ leechQ u
  card_u : Nat.card ↥(leechQ u ⊓ Subgroup.centralizer ({a} : Set G)) = 2 ^ 17
  gms : ∀ w, IsConj z₀ w → GMSLeechCentralizer w
  leech : ∀ w, IsConj z₀ w → LeechData w

theorem exists_twoClasses
    [Finite G] (hSLS : SLSStatement d₀) (hTV : TableVIn G)
    (hL : LeechStatement) {a z₀ : G} (hG : GMSF1Type d₀ a z₀) :
    ∃ b z u : G, TwoClasses a z₀ b z u := by
  obtain ⟨b, z, u, hTVz, hab, -, hz₀z, hacz, haQ, hz₀u, hz₀au, hauQ, hcard⟩ :=
    s31_two hSLS hTV hL hG
  exact ⟨b, z, u, hTVz, hG.1.1, hG.2.1, hG.not_isConj, hab, hz₀z, hacz, haQ, hz₀u, hz₀au, hauQ,
    hcard, fun w hw => hG.2.of_isConj hw, fun w hw => hL G w (hG.2.of_isConj hw)⟩

theorem exists_mem_centralizer_conj {p t x y w g₁ g₂ : G} (hx : g₁ * p * g₁⁻¹ = x)
    (hw : g₁ * t * g₁⁻¹ = w) (hy : g₂ * p * g₂⁻¹ = y) (hw' : g₂ * t * g₂⁻¹ = w) :
    ∃ g ∈ Subgroup.centralizer ({w} : Set G), g * x * g⁻¹ = y := by
  subst hx hy hw
  refine ⟨g₂ * g₁⁻¹, ?_, by group⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc g₂ * g₁⁻¹ * (g₁ * t * g₁⁻¹) = (g₂ * t * g₂⁻¹) * g₂ * g₁⁻¹ := by group
    _ = (g₁ * t * g₁⁻¹) * g₂ * g₁⁻¹ := by rw [hw']
    _ = (g₁ * t * g₁⁻¹) * (g₂ * g₁⁻¹) := by group

namespace TwoClasses

variable {a z₀ b z u : G} (h : TwoClasses a z₀ b z u)

include h

theorem orderOf_of_isConj {w : G} (hw : IsConj z₀ w) : orderOf w = 2 :=
  (orderOf_eq_of_isConj hw).symm.trans h.orderOf_z₀

theorem card_centralizer [Finite G] {w : G} (hw : IsConj z₀ w) :
    Nat.card (Subgroup.centralizer ({w} : Set G)) = 2 ^ 46 * 1982582476875 :=
  (h.gms w hw).card_centralizer

theorem isConj_or_isConj_of_mem_centralizer {a' t : G} (ha' : IsConj a a')
    (ht : t ∈ Subgroup.centralizer ({a'} : Set G)) (ht2 : orderOf t = 2) :
    IsConj a t ∨ IsConj z₀ t := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp ha'
  have htt : IsConj t (c⁻¹ * t * c) := isConj_iff.mpr ⟨c⁻¹, by rw [inv_inv]⟩
  have htC : c⁻¹ * t * c ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at ht ⊢
    calc c⁻¹ * t * c * a = c⁻¹ * (t * (c * a * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * a * c⁻¹) * t) * c := by rw [ht]
      _ = a * (c⁻¹ * t * c) := by group
  have ht2' : orderOf (c⁻¹ * t * c) = 2 := by
    rw [← ht2, ← orderOf_conj_eq c⁻¹ t, inv_inv]
  by_cases hta : c⁻¹ * t * c = a
  · left
    have : t = c * a * c⁻¹ := by rw [← hta]; group
    rw [this]
    exact isConj_iff.mpr ⟨c, rfl⟩
  obtain ⟨g, hg, hcase⟩ := h.tableV.cover _ htC ht2' hta
  have hconj : ∀ y, g * (c⁻¹ * t * c) * g⁻¹ = y → IsConj (c⁻¹ * t * c) y := fun y e =>
    isConj_iff.mpr ⟨g, e⟩
  have hA : ∀ y, IsConj a y → g * (c⁻¹ * t * c) * g⁻¹ = y → IsConj a t := fun y hy e =>
    (hy.trans (hconj y e).symm).trans htt.symm
  have hB : ∀ y, IsConj z₀ y → g * (c⁻¹ * t * c) * g⁻¹ = y → IsConj z₀ t := fun y hy e =>
    (hy.trans (hconj y e).symm).trans htt.symm
  rcases hcase with e | e | e | e
  · exact Or.inl (hA _ h.isConj_b e)
  · exact Or.inr (hB _ h.isConj_z e)
  · exact Or.inl (hA _ h.isConj_az e)
  · exact Or.inr (hB _ h.isConj_u e)

theorem exists_conj {w x : G} (hw : IsConj z₀ w) (hx : IsConj a x) (hxw : x * w = w * x) :
    ((∃ g, g * a * g⁻¹ = x ∧ g * z * g⁻¹ = w) ∧ x ∈ leechQ w) ∨
      ((∃ g, g * a * g⁻¹ = x ∧ g * u * g⁻¹ = w) ∧ x ∉ leechQ w) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hx
  have hww : IsConj w (c⁻¹ * w * c) := isConj_iff.mpr ⟨c⁻¹, by rw [inv_inv]⟩
  have hw' : IsConj z₀ (c⁻¹ * w * c) := hw.trans hww
  have hw'C : c⁻¹ * w * c ∈ Subgroup.centralizer ({a} : Set G) := by
    have hxw' : (c * a * c⁻¹) * w = w * (c * a * c⁻¹) := by rw [hc]; exact hxw
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc c⁻¹ * w * c * a = c⁻¹ * (w * (c * a * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * a * c⁻¹) * w) * c := by rw [hxw']
      _ = a * (c⁻¹ * w * c) := by group
  have hw'2 : orderOf (c⁻¹ * w * c) = 2 := by
    rw [← h.orderOf_of_isConj hw, ← orderOf_conj_eq c⁻¹ w, inv_inv]
  have hw'a : c⁻¹ * w * c ≠ a := by
    intro e
    rw [e] at hw'
    exact h.not_isConj hw'.symm
  obtain ⟨g, hg, hcase⟩ := h.tableV.cover _ hw'C hw'2 hw'a
  have hga : g⁻¹ * a * g = a := by
    have hga : g * a = a * g := Subgroup.mem_centralizer_singleton_iff.mp hg
    calc g⁻¹ * a * g = g⁻¹ * (a * g) := by rw [mul_assoc]
      _ = g⁻¹ * (g * a) := by rw [hga]
      _ = a := by rw [inv_mul_cancel_left]
  have hconj : ∀ y, g * (c⁻¹ * w * c) * g⁻¹ = y → IsConj z₀ y := fun y e =>
    hw'.trans (isConj_iff.mpr ⟨g, e⟩)
  have hx1 : (c * g⁻¹) * a * (c * g⁻¹)⁻¹ = x := by
    rw [← hc]
    calc c * g⁻¹ * a * (c * g⁻¹)⁻¹ = c * (g⁻¹ * a * g) * c⁻¹ := by group
      _ = c * a * c⁻¹ := by rw [hga]
  have hx2 : ∀ y, g * (c⁻¹ * w * c) * g⁻¹ = y → (c * g⁻¹) * y * (c * g⁻¹)⁻¹ = w := by
    intro y e
    rw [← e]
    group
  rcases hcase with e | e | e | e
  · exact absurd (h.isConj_b.trans (hconj _ e).symm) h.not_isConj
  · refine Or.inl ⟨⟨c * g⁻¹, hx1, hx2 z e⟩, ?_⟩
    have := conj_mem_leechQ_conj (c := c * g⁻¹) h.mem_leechQ_z
    rwa [hx1, hx2 z e] at this
  · exact absurd (h.isConj_az.trans (hconj _ e).symm) h.not_isConj
  · refine Or.inr ⟨⟨c * g⁻¹, hx1, hx2 u e⟩, fun hQ => h.not_mem_leechQ_u ?_⟩
    rw [← hx2 u e, mem_leechQ_conj_iff] at hQ
    have : (c * g⁻¹)⁻¹ * x * (c * g⁻¹) = a := by rw [← hx1]; group
    rwa [this] at hQ

theorem mem_leechQ_of_isConj_mul {a' t : G} (ha' : IsConj a a') (ht : IsConj z₀ t)
    (hcomm : a' * t = t * a') (hmul : IsConj a (a' * t)) : a' ∈ leechQ t := by
  rcases h.exists_conj ht ha' hcomm with ⟨-, hQ⟩ | ⟨⟨g, hg1, hg2⟩, -⟩
  · exact hQ
  · exfalso
    have e : g * (a * u) * g⁻¹ = a' * t := by rw [← hg1, ← hg2]; group
    exact h.not_isConj (hmul.trans (h.isConj_au.trans (isConj_iff.mpr ⟨g, e⟩)).symm)

theorem not_mem_leechQ_of_isConj_mul {a' t : G} (ha' : IsConj a a') (ht : IsConj z₀ t)
    (hcomm : a' * t = t * a') (hmul : IsConj z₀ (a' * t)) :
    a' ∉ leechQ t ∧ Nat.card ↥(leechQ t ⊓ Subgroup.centralizer ({a'} : Set G)) = 2 ^ 17 := by
  rcases h.exists_conj ht ha' hcomm with ⟨⟨g, hg1, hg2⟩, -⟩ | ⟨⟨g, hg1, hg2⟩, hQ⟩
  · exfalso
    have e : g * (a * z) * g⁻¹ = a' * t := by rw [← hg1, ← hg2]; group
    exact h.not_isConj ((h.isConj_az.trans (isConj_iff.mpr ⟨g, e⟩)).trans hmul.symm)
  · refine ⟨hQ, ?_⟩
    rw [← hg1, ← hg2, card_leechQ_inf_centralizer_conj]
    exact h.card_u

theorem exists_conj_of_mem_leechQ {w x : G} (hw : IsConj z₀ w) (hx : IsConj a x)
    (hxQ : x ∈ leechQ w) : ∃ g, g * a * g⁻¹ = x ∧ g * z * g⁻¹ = w := by
  have hxw : x * w = w * x :=
    Subgroup.mem_centralizer_singleton_iff.mp (leechQ_le_centralizer w hxQ)
  rcases h.exists_conj hw hx hxw with ⟨hg, -⟩ | ⟨-, hnot⟩
  · exact hg
  · exact absurd hxQ hnot

theorem exists_conj_of_not_mem_leechQ {w x : G} (hw : IsConj z₀ w) (hx : IsConj a x)
    (hxC : x ∈ Subgroup.centralizer ({w} : Set G)) (hxQ : x ∉ leechQ w) :
    ∃ g, g * a * g⁻¹ = x ∧ g * u * g⁻¹ = w := by
  rcases h.exists_conj hw hx (Subgroup.mem_centralizer_singleton_iff.mp hxC) with
    ⟨-, hQ⟩ | ⟨hg, -⟩
  · exact absurd hQ hxQ
  · exact hg

theorem exists_conj_mem_two [Finite G] {w : G} (hw : IsConj z₀ w)
    {T₂ T₃ T₄ : Set G}
    (hT : LeechOrbits w T₂ T₃ T₄) : ∃ c : G, c * z * c⁻¹ = w ∧ c * a * c⁻¹ ∈ T₂ := by
  obtain ⟨c, hc⟩ := isConj_iff.mp (h.isConj_z.symm.trans hw)
  refine ⟨c, hc, ?_⟩
  subst hc
  have ha2 : orderOf (c * a * c⁻¹) = 2 := by rw [orderOf_conj_eq]; exact h.orderOf_a
  have hz2 : orderOf (c * z * c⁻¹) = 2 := by rw [orderOf_conj_eq]; exact h.tableV.orderOf_z
  refine hT.mem_two (h.card_centralizer hw) (ne_one_of_orderOf hz2)
    (conj_mem_leechQ_conj h.mem_leechQ_z) (ne_one_of_orderOf ha2)
    (fun e => h.tableV.ne_z (mul_left_cancel (mul_right_cancel e)).symm)
    (mul_self_eq_one_of_orderOf ha2) ?_
  rw [card_centralizer_inf_conj, inf_comm]
  exact h.tableV.card_z

theorem exists_isConj_mem_two [Finite G] {w : G} (hw : IsConj z₀ w)
    {T₂ T₃ T₄ : Set G}
    (hT : LeechOrbits w T₂ T₃ T₄) : ∃ a' : G, IsConj a a' ∧ a' ∈ T₂ := by
  obtain ⟨c, -, haT⟩ := h.exists_conj_mem_two hw hT
  exact ⟨_, isConj_iff.mpr ⟨c, rfl⟩, haT⟩

theorem isConj_of_mem_two [Finite G] {w : G} (hw : IsConj z₀ w)
    {T₂ T₃ T₄ : Set G}
    (hT : LeechOrbits w T₂ T₃ T₄) {q : G} (hq : q ∈ T₂) : IsConj a q := by
  obtain ⟨a', ha', haT⟩ := h.exists_isConj_mem_two hw hT
  obtain ⟨g, -, e⟩ := hT.trans_two _ haT q hq
  exact ha'.trans (isConj_iff.mpr ⟨g, e⟩)

theorem isConj_of_mem_four [Finite G] {w : G} (hw : IsConj z₀ w)
    {T₂ T₃ T₄ : Set G}
    (hT : LeechOrbits w T₂ T₃ T₄) {q : G} (hq : q ∈ T₄) : IsConj z₀ q := by
  obtain ⟨c, hc, haT⟩ := h.exists_conj_mem_two hw hT
  have hTV := h.tableV.conj c
  rw [hc] at hTV
  have ha2 : orderOf (c * a * c⁻¹) = 2 := by rw [orderOf_conj_eq]; exact h.orderOf_a
  have hacz : IsConj (c * a * c⁻¹) (c * a * c⁻¹ * w) := by
    refine (isConj_iff.mpr ⟨c, rfl⟩ : IsConj a (c * a * c⁻¹)).symm.trans
      (h.isConj_az.trans (isConj_iff.mpr ⟨c, ?_⟩))
    rw [← hc]
    group
  exact hw.trans (hT.isConj_of_mem_four hTV ha2 (h.card_centralizer hw) haT hacz q hq)

theorem mem_four_of_isConj [Finite G] {w : G} (hw : IsConj z₀ w)
    {T₂ T₃ T₄ : Set G}
    (hT : LeechOrbits w T₂ T₃ T₄) {x : G} (hx : x ∈ leechQ w) (hxw : x ≠ w)
    (hx2B : IsConj z₀ x) : x ∈ T₄ := by
  have hx2 : orderOf x = 2 := h.orderOf_of_isConj hx2B
  rcases hT.cover x hx (ne_one_of_orderOf hx2) hxw with h2 | h3 | h4
  · exact absurd ((h.isConj_of_mem_two hw hT h2).trans hx2B.symm) h.not_isConj
  · exact absurd ((hT.three x h3).symm.trans (mul_self_eq_one_of_orderOf hx2))
      (ne_one_of_orderOf (h.orderOf_of_isConj hw))
  · exact h4

theorem orderOf_mul_eq_two_pow [Finite G] {w r x : G} (hrA : IsConj a r)
    (hrC : r ∈ Subgroup.centralizer ({w} : Set G))
    (hxC : x ∈ Subgroup.centralizer ({w} : Set G)) (hr2 : orderOf r = 2) (hx2 : orderOf x = 2)
    (hno : ∀ y ∈ Subgroup.centralizer ({w} : Set G), y * x = x * y → ¬ IsConj a y) :
    ∃ k : ℕ, orderOf (r * x) = 2 ^ k := by
  have hrr : r * r = 1 := mul_self_eq_one_of_orderOf hr2
  have hxx : x * x = 1 := mul_self_eq_one_of_orderOf hx2
  have hxA : ¬ IsConj a x := fun hax => hno x hxC rfl hax
  have heven : Even (orderOf (r * x)) := by
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    exact hxA (hrA.trans (isConj_of_involutions_of_odd_orderOf_mul hrr hxx hodd))
  obtain ⟨k, hk⟩ := heven
  have hk' : orderOf (r * x) = 2 * k := by omega
  have hk0 : 0 < k := by
    have := orderOf_pos (r * x)
    omega
  obtain ⟨hz1, hz1ne, hzr, hzx, hconj⟩ := dihedral_central_involution hrr hxx hk' hk0
  have hz₁C : (r * x) ^ k ∈ Subgroup.centralizer ({w} : Set G) :=
    Subgroup.pow_mem _ (Subgroup.mul_mem _ hrC hxC) k
  generalize (r * x) ^ k = z₁ at hz₁C hz1 hz1ne hzr hzx hconj
  have hz₁2 : orderOf z₁ = 2 := orderOf_eq_two_of_mul_self hz1 hz1ne
  have hz₁B : IsConj z₀ z₁ := by
    rcases h.isConj_or_isConj_of_mem_centralizer hrA
      (Subgroup.mem_centralizer_singleton_iff.mpr hzr) hz₁2 with hA | hB
    · exact absurd hA (hno z₁ hz₁C hzx)
    · exact hB
  have hz₁rA : IsConj a (r * z₁) := by
    rcases hconj with hc | hc
    · have : IsConj a (z₁ * r) := hrA.trans hc
      rwa [hzr] at this
    · exfalso
      refine hno (z₁ * x) (Subgroup.mul_mem _ hz₁C hxC) ?_ (hrA.trans hc)
      calc z₁ * x * x = z₁ := by rw [mul_assoc, hxx, mul_one]
        _ = x * (z₁ * x) := by rw [← mul_assoc, ← hzx, mul_assoc, hxx, mul_one]
  have hrQ : r ∈ leechQ z₁ := h.mem_leechQ_of_isConj_mul hrA hz₁B hzr.symm hz₁rA
  have hxz : x ∈ Subgroup.centralizer ({z₁} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hzx.symm
  have hsq : (r * x) ^ 2 ∈ leechQ z₁ := by
    have hmem := (leechQ z₁).mul_mem hrQ (conj_mem_leechQ hxz hrQ)
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
    rw [hxinv] at hmem
    convert hmem using 1
    rw [pow_two]
    group
  obtain ⟨e, he⟩ := exists_orderOf_eq_two_pow_of_mem_leechQ hsq
  have hdvd : orderOf (r * x) ∣ 2 ^ (e + 1) := by
    apply orderOf_dvd_of_pow_eq_one
    rw [show 2 ^ (e + 1) = 2 * 2 ^ e by ring, pow_mul, ← he, pow_orderOf_eq_one]
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  exact ⟨i, hi⟩

end TwoClasses

theorem isConj_or_isConj_of_mem_centralizer
    [Finite G] (hSLS : SLSStatement d₀)
    (hTV : TableVIn G) (hL : LeechStatement) {a z₀ : G} (hG : GMSF1Type d₀ a z₀) {a' t : G}
    (ha' : IsConj a a') (ht : t ∈ Subgroup.centralizer ({a'} : Set G)) (ht2 : orderOf t = 2) :
    IsConj a t ∨ IsConj z₀ t := by
  obtain ⟨b, z, u, h⟩ := exists_twoClasses hSLS hTV hL hG
  exact h.isConj_or_isConj_of_mem_centralizer ha' ht ht2

theorem mem_leechQ_of_isConj_mul
    [Finite G] (hSLS : SLSStatement d₀) (hTV : TableVIn G)
    (hL : LeechStatement) {a z₀ : G} (hG : GMSF1Type d₀ a z₀) {a' t : G} (ha' : IsConj a a')
    (ht : IsConj z₀ t) (hcomm : a' * t = t * a') (hmul : IsConj a (a' * t)) : a' ∈ leechQ t := by
  obtain ⟨b, z, u, h⟩ := exists_twoClasses hSLS hTV hL hG
  exact h.mem_leechQ_of_isConj_mul ha' ht hcomm hmul

theorem not_mem_leechQ_of_isConj_mul
    [Finite G] (hSLS : SLSStatement d₀) (hTV : TableVIn G)
    (hL : LeechStatement) {a z₀ : G} (hG : GMSF1Type d₀ a z₀) {a' t : G} (ha' : IsConj a a')
    (ht : IsConj z₀ t) (hcomm : a' * t = t * a') (hmul : IsConj z₀ (a' * t)) :
    a' ∉ leechQ t ∧ Nat.card ↥(leechQ t ⊓ Subgroup.centralizer ({a'} : Set G)) = 2 ^ 17 := by
  obtain ⟨b, z, u, h⟩ := exists_twoClasses hSLS hTV hL hG
  exact h.not_mem_leechQ_of_isConj_mul ha' ht hcomm hmul

theorem isConj_of_mem_leechQ_two
    [Finite G] (hSLS : SLSStatement d₀) (hTV : TableVIn G)
    (hL : LeechStatement) {a z₀ : G} (hG : GMSF1Type d₀ a z₀) {w x y : G} (hw : IsConj z₀ w)
    (hx : x ∈ leechQ w) (hy : y ∈ leechQ w) (hax : IsConj a x) (hay : IsConj a y) :
    ∃ g ∈ Subgroup.centralizer ({w} : Set G), g * x * g⁻¹ = y := by
  obtain ⟨b, z, u, h⟩ := exists_twoClasses hSLS hTV hL hG
  obtain ⟨g₁, h₁, h₁'⟩ := h.exists_conj_of_mem_leechQ hw hax hx
  obtain ⟨g₂, h₂, h₂'⟩ := h.exists_conj_of_mem_leechQ hw hay hy
  exact exists_mem_centralizer_conj h₁ h₁' h₂ h₂'

theorem isConj_of_mem_leechQ_four
    [Finite G] (hSLS : SLSStatement d₀) (hTV : TableVIn G)
    (hL : LeechStatement) {a z₀ : G} (hG : GMSF1Type d₀ a z₀) {w x y : G} (hw : IsConj z₀ w)
    (hx : x ∈ leechQ w) (hy : y ∈ leechQ w) (hxw : x ≠ w) (hyw : y ≠ w) (hbx : IsConj z₀ x)
    (hby : IsConj z₀ y) : ∃ g ∈ Subgroup.centralizer ({w} : Set G), g * x * g⁻¹ = y := by
  obtain ⟨b, z, u, h⟩ := exists_twoClasses hSLS hTV hL hG
  obtain ⟨T₂, T₃, T₄, hT⟩ := (h.leech w hw).exists_orbits
  exact hT.trans_four x (h.mem_four_of_isConj hw hT hx hxw hbx) y
    (h.mem_four_of_isConj hw hT hy hyw hby)

theorem isConj_of_not_mem_leechQ
    [Finite G] (hSLS : SLSStatement d₀) (hTV : TableVIn G)
    (hL : LeechStatement) {a z₀ : G} (hG : GMSF1Type d₀ a z₀) {w x y : G} (hw : IsConj z₀ w)
    (hx : x ∈ Subgroup.centralizer ({w} : Set G)) (hy : y ∈ Subgroup.centralizer ({w} : Set G))
    (hxQ : x ∉ leechQ w) (hyQ : y ∉ leechQ w) (hax : IsConj a x) (hay : IsConj a y) :
    ∃ g ∈ Subgroup.centralizer ({w} : Set G), g * x * g⁻¹ = y := by
  obtain ⟨b, z, u, h⟩ := exists_twoClasses hSLS hTV hL hG
  obtain ⟨g₁, h₁, h₁'⟩ := h.exists_conj_of_not_mem_leechQ hw hax hx hxQ
  obtain ⟨g₂, h₂, h₂'⟩ := h.exists_conj_of_not_mem_leechQ hw hay hy hyQ
  exact exists_mem_centralizer_conj h₁ h₁' h₂ h₂'

theorem card_centralizer_inf_of_mem_leechQ_two
    [Finite G] (hSLS : SLSStatement d₀)
    (hTV : TableVIn G) (hL : LeechStatement) {a z₀ : G} (hG : GMSF1Type d₀ a z₀) {w x : G}
    (hw : IsConj z₀ w) (hx : x ∈ leechQ w) (hax : IsConj a x) :
    Nat.card ↥(Subgroup.centralizer ({w} : Set G) ⊓ Subgroup.centralizer ({x} : Set G)) =
      tableVOrderZ := by
  obtain ⟨b, z, u, h⟩ := exists_twoClasses hSLS hTV hL hG
  obtain ⟨g, hg1, hg2⟩ := h.exists_conj_of_mem_leechQ hw hax hx
  rw [← hg1, ← hg2, card_centralizer_inf_conj, inf_comm]
  exact h.tableV.card_z

theorem card_centralizer_inf_of_mem_leechQ_four
    [Finite G] (hSLS : SLSStatement d₀)
    (hTV : TableVIn G) (hL : LeechStatement) {a z₀ : G} (hG : GMSF1Type d₀ a z₀) {w x : G}
    (hw : IsConj z₀ w) (hx : x ∈ leechQ w) (hxw : x ≠ w) (hbx : IsConj z₀ x) :
    Nat.card ↥(Subgroup.centralizer ({w} : Set G) ⊓ Subgroup.centralizer ({x} : Set G)) =
      2 ^ 45 * 3 ^ 3 * 5 * 7 * 11 * 23 := by
  obtain ⟨b, z, u, h⟩ := exists_twoClasses hSLS hTV hL hG
  obtain ⟨T₂, T₃, T₄, hT⟩ := (h.leech w hw).exists_orbits
  have h2 := card_inf_centralizer_mul_ncard hT.conj_four hT.trans_four
    (h.mem_four_of_isConj hw hT hx hxw hbx)
  rw [hT.card_four, h.card_centralizer hw] at h2
  norm_num at h2 ⊢
  omega

theorem card_centralizer_inf_of_not_mem_leechQ
    [Finite G] (hSLS : SLSStatement d₀)
    (hTV : TableVIn G) (hL : LeechStatement) {a z₀ : G} (hG : GMSF1Type d₀ a z₀) {w x : G}
    (hw : IsConj z₀ w) (hx : x ∈ Subgroup.centralizer ({w} : Set G)) (hxQ : x ∉ leechQ w)
    (hax : IsConj a x) :
    Nat.card ↥(Subgroup.centralizer ({w} : Set G) ⊓ Subgroup.centralizer ({x} : Set G)) =
      tableVOrderU := by
  obtain ⟨b, z, u, h⟩ := exists_twoClasses hSLS hTV hL hG
  obtain ⟨g, hg1, hg2⟩ := h.exists_conj_of_not_mem_leechQ hw hax hx hxQ
  rw [← hg1, ← hg2, card_centralizer_inf_conj, inf_comm]
  exact h.tableV.card_u

theorem orderOf_eq_two_mem_leechQ
    [Finite G] (hSLS : SLSStatement d₀) (hTV : TableVIn G)
    (hL : LeechStatement) {a z₀ : G} (hG : GMSF1Type d₀ a z₀) {w x : G} (hw : IsConj z₀ w)
    (hx : x ∈ leechQ w) (hx2 : orderOf x = 2) : x = w ∨ IsConj a x ∨ IsConj z₀ x := by
  obtain ⟨b, z, u, h⟩ := exists_twoClasses hSLS hTV hL hG
  by_cases hxw : x = w
  · exact Or.inl hxw
  right
  obtain ⟨T₂, T₃, T₄, hT⟩ := (h.leech w hw).exists_orbits
  rcases hT.cover x hx (ne_one_of_orderOf hx2) hxw with h2 | h3 | h4
  · exact Or.inl (h.isConj_of_mem_two hw hT h2)
  · exact absurd ((hT.three x h3).symm.trans (mul_self_eq_one_of_orderOf hx2))
      (ne_one_of_orderOf (h.orderOf_of_isConj hw))
  · exact Or.inr (h.isConj_of_mem_four hw hT h4)

theorem s31_four
    [Finite G] (hSLS : SLSStatement d₀) (hTV : TableVIn G) (hL : LeechStatement)
    {a z₀ : G} (hG : GMSF1Type d₀ a z₀) (hLI : LeechInvolutionStatement) {w x : G}
    (hw : IsConj z₀ w) (hx : x ∈ Subgroup.centralizer ({w} : Set G)) (hx2 : orderOf x = 2) :
    ∃ y ∈ Subgroup.centralizer ({w} : Set G), y * x = x * y ∧ IsConj a y := by
  obtain ⟨b, z, u, h⟩ := exists_twoClasses hSLS hTV hL hG
  by_contra hno
  push Not at hno
  have hxx : x * x = 1 := mul_self_eq_one_of_orderOf hx2
  have hxA : ¬ IsConj a x := fun hax => hno x hx rfl hax
  obtain ⟨T₂, T₃, T₄, hT⟩ := (h.leech w hw).exists_orbits
  by_cases hxQ : x ∈ leechQ w
  ·
    obtain ⟨a', ha'A, haT⟩ := h.exists_isConj_mem_two hw hT
    have ha'C : a' ∈ Subgroup.centralizer ({w} : Set G) :=
      leechQ_le_centralizer w (hT.two_sub haT)
    by_cases hxw : x = w
    · refine hno a' ha'C ?_ ha'A
      rw [hxw]
      exact Subgroup.mem_centralizer_singleton_iff.mp ha'C
    · rcases hT.cover x hxQ (ne_one_of_orderOf hx2) hxw with h2 | h3 | h4
      · exact hxA (h.isConj_of_mem_two hw hT h2)
      · exact absurd ((hT.three x h3).symm.trans hxx) (ne_one_of_orderOf (h.orderOf_of_isConj hw))
      · obtain ⟨q', hq'4, haq'4⟩ := hT.pair_c a' haT
        obtain ⟨g, hg, hgx⟩ := hT.trans_four q' hq'4 x h4
        have hyT : g * a' * g⁻¹ ∈ T₂ := hT.conj_two g hg a' haT
        refine hno _ (leechQ_le_centralizer w (hT.two_sub hyT)) ?_ (h.isConj_of_mem_two hw hT hyT)
        have haa : a' * a' = 1 := (hT.two a' haT).2.2.1
        have hqq : q' * q' = 1 := (hT.four q' hq'4).2.2.1
        have hcomm : a' * q' = q' * a' :=
          mul_comm_of_mul_self_eq_one haa hqq (hT.four _ haq'4).2.2.1
        rw [← hgx]
        calc g * a' * g⁻¹ * (g * q' * g⁻¹) = g * (a' * q') * g⁻¹ := by group
          _ = g * (q' * a') * g⁻¹ := by rw [hcomm]
          _ = g * q' * g⁻¹ * (g * a' * g⁻¹) := by group
  ·
    obtain ⟨c, hc⟩ := isConj_iff.mp (h.isConj_u.symm.trans hw)
    have hauC : a * u = u * a := (Subgroup.mem_centralizer_singleton_iff.mp h.tableV.mem_u).symm
    have hr₀C : c * a * c⁻¹ ∈ Subgroup.centralizer ({w} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff, ← hc]
      calc c * a * c⁻¹ * (c * u * c⁻¹) = c * (a * u) * c⁻¹ := by group
        _ = c * (u * a) * c⁻¹ := by rw [hauC]
        _ = c * u * c⁻¹ * (c * a * c⁻¹) := by group
    have hr₀2 : orderOf (c * a * c⁻¹) = 2 := by rw [orderOf_conj_eq]; exact h.orderOf_a
    have hr₀Q : c * a * c⁻¹ ∉ leechQ w := by
      intro hQ
      rw [← hc, mem_leechQ_conj_iff] at hQ
      have e : c⁻¹ * (c * a * c⁻¹) * c = a := by group
      rw [e] at hQ
      exact h.not_mem_leechQ_u hQ
    have h35 : Nat.card ↥(Subgroup.centralizer ({w} : Set G) ⊓
        Subgroup.centralizer ({c * a * c⁻¹} : Set G)) = 2 ^ 38 * 3 ^ 5 * 5 ^ 2 * 7 := by
      rw [← hc, card_centralizer_inf_conj, inf_comm, h.tableV.card_u]
      rfl
    obtain ⟨g, hg, hord⟩ := (hLI G w (h.gms w hw)).1 _ hr₀C hr₀2 hr₀Q h35 x hx hx2 hxQ
    have hrC : g * (c * a * c⁻¹) * g⁻¹ ∈ Subgroup.centralizer ({w} : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hr₀C) (Subgroup.inv_mem _ hg)
    have hrA : IsConj a (g * (c * a * c⁻¹) * g⁻¹) :=
      (isConj_iff.mpr ⟨c, rfl⟩).trans (isConj_iff.mpr ⟨g, rfl⟩)
    obtain ⟨k, hk⟩ := h.orderOf_mul_eq_two_pow hrA hrC hx (by rw [orderOf_conj_eq]; exact hr₀2)
      hx2 hno
    exact hord k hk

theorem s31_five
    [Finite G] (hSLS : SLSStatement d₀) (hTV : TableVIn G) (hL : LeechStatement)
    {a z₀ : G} (hG : GMSF1Type d₀ a z₀) (hLI : LeechInvolutionStatement) {x : G}
    (hx : orderOf x = 2) : IsConj a x ∨ IsConj z₀ x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpg : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨g, hg⟩ := hG.2.exists_conj_mem_centralizer hpg
  obtain ⟨y, -, hyx, hya⟩ := s31_four hSLS hTV hL hG hLI (IsConj.refl z₀) hg
    (by rw [orderOf_conj_eq]; exact hx)
  have hxy : g * x * g⁻¹ ∈ Subgroup.centralizer ({y} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hyx.symm
  have hxx : IsConj x (g * x * g⁻¹) := isConj_iff.mpr ⟨g, rfl⟩
  rcases isConj_or_isConj_of_mem_centralizer hSLS hTV hL hG hya hxy
      (by rw [orderOf_conj_eq]; exact hx) with hA | hB
  · exact Or.inl (hA.trans hxx.symm)
  · exact Or.inr (hB.trans hxx.symm)

end CFSG.Monster.GMS
