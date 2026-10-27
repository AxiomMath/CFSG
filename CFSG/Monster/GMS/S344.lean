module

public import CFSG.Monster.GMS.Extraspecial
public import CFSG.Monster.GMS.Facts.LeechCosets
public import CFSG.Monster.GMS.S31Three
public import CFSG.Monster.GMS.S33
import CFSG.Monster.GMS.NotConj

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G] {d₀ : B}

private theorem isConj_mul_of_not_mem_leechQ
    [Finite G] (hSLS : SLSStatement d₀)
    (hTV : TableVIn G) (hL : LeechStatement) {a z₀ : G} (hG : GMSF1Type d₀ a z₀) {w x : G}
    (hw : IsConj z₀ w) (hx : x ∈ Subgroup.centralizer ({w} : Set G)) (hxA : IsConj a x)
    (hxQ : x ∉ leechQ w) : IsConj z₀ (x * w) := by
  have hxw : x * w = w * x := Subgroup.mem_centralizer_singleton_iff.mp hx
  have hx2 : orderOf x = 2 := (orderOf_eq_of_isConj hxA).symm.trans hG.1.1
  have hw2 : orderOf w = 2 := (orderOf_eq_of_isConj hw).symm.trans hG.2.1
  have hxx : x * x = 1 := mul_self_eq_one_of_orderOf hx2
  have hww : w * w = 1 := mul_self_eq_one_of_orderOf hw2
  have hprod : (x * w) * (x * w) = 1 := by
    calc (x * w) * (x * w) = x * (w * x) * w := by group
      _ = x * (x * w) * w := by rw [hxw]
      _ = (x * x) * (w * w) := by group
      _ = 1 := by rw [hxx, hww, one_mul]
  have hne : x * w ≠ 1 := by
    intro h1
    have hxinv : x = w⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [inv_eq_of_mul_eq_one_right hww] at hxinv
    rw [hxinv] at hxA
    exact hG.not_isConj (hxA.trans hw.symm)
  have hC : x * w ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * w * x = x * (w * x) := by rw [mul_assoc]
      _ = x * (x * w) := by rw [hxw]
  rcases isConj_or_isConj_of_mem_centralizer hSLS hTV hL hG hxA hC
      (orderOf_eq_two_of_mul_self hprod hne) with h | h
  · exact absurd (mem_leechQ_of_isConj_mul hSLS hTV hL hG hxA hw hxw h) hxQ
  · exact h

private theorem two_pow_seventeen_le_card
    [Finite G] (hSLS : SLSStatement d₀)
    (hTV : TableVIn G) (hL : LeechStatement) {a z₀ : G} (hG : GMSF1Type d₀ a z₀) {w x : G}
    (hw : IsConj z₀ w) (hx : x ∈ Subgroup.centralizer ({w} : Set G)) (hxA : IsConj a x) :
    2 ^ 17 ≤ Nat.card ↥(leechQ w ⊓ Subgroup.centralizer ({x} : Set G)) := by
  by_cases hxQ : x ∈ leechQ w
  · have hGw := hG.2.of_isConj hw
    have h1 := hGw.extraspecialData.card_le_two_mul_card_inf_centralizer (le_refl (leechQ w)) hxQ
    rw [hGw.card_leechQ] at h1
    omega
  · have hxw : x * w = w * x := Subgroup.mem_centralizer_singleton_iff.mp hx
    have := (not_mem_leechQ_of_isConj_mul hSLS hTV hL hG hxA hw hxw
      (isConj_mul_of_not_mem_leechQ hSLS hTV hL hG hw hx hxA hxQ)).2
    omega

theorem s344_card
    [Finite G] (hSLS : SLSStatement d₀) (hTV : TableVIn G)
    (hL : LeechStatement) {a z₀ : G} (hG : GMSF1Type d₀ a z₀) {w x y : G} (hw : IsConj z₀ w)
    (hx : x ∈ Subgroup.centralizer ({w} : Set G)) (hy : y ∈ Subgroup.centralizer ({w} : Set G))
    (hxA : IsConj a x) (hyA : IsConj a y) :
    2 ^ 9 ≤ Nat.card ↥(leechQ w ⊓ Subgroup.centralizer ({x} : Set G) ⊓
      Subgroup.centralizer ({y} : Set G)) := by
  have hQc : Nat.card (leechQ w) = 2 ^ 25 := (hG.2.of_isConj hw).card_leechQ
  have hX := two_pow_seventeen_le_card hSLS hTV hL hG hw hx hxA
  have hY := two_pow_seventeen_le_card hSLS hTV hL hG hw hy hyA
  set Q := leechQ w with hQ
  set A := Subgroup.centralizer ({x} : Set G) with hA
  set B := Subgroup.centralizer ({y} : Set G) with hB
  have hAr := Subgroup.relIndex_mul_card A Q
  have hBr := Subgroup.relIndex_mul_card B Q
  have hABr := Subgroup.relIndex_mul_card (A ⊓ B) Q
  have hle := Subgroup.relIndex_inf_le (H := A) (K := B) (L := Q)
  rw [inf_comm] at hAr hBr
  have hset : A ⊓ B ⊓ Q = Q ⊓ A ⊓ B := by
    ext g
    simp only [Subgroup.mem_inf]
    tauto
  rw [hset] at hABr
  set N := Nat.card ↥(Q ⊓ A ⊓ B) with hN
  set rA := A.relIndex Q
  set rB := B.relIndex Q
  set rAB := (A ⊓ B).relIndex Q
  have h1 : rA ≤ 2 ^ 8 := by
    refine Nat.le_of_mul_le_mul_right (c := 2 ^ 17) ?_ (by norm_num)
    calc rA * 2 ^ 17 ≤ rA * Nat.card ↥(Q ⊓ A) := Nat.mul_le_mul_left _ hX
      _ = 2 ^ 25 := by rw [hAr, hQc]
      _ = 2 ^ 8 * 2 ^ 17 := by norm_num
  have h2 : rB ≤ 2 ^ 8 := by
    refine Nat.le_of_mul_le_mul_right (c := 2 ^ 17) ?_ (by norm_num)
    calc rB * 2 ^ 17 ≤ rB * Nat.card ↥(Q ⊓ B) := Nat.mul_le_mul_left _ hY
      _ = 2 ^ 25 := by rw [hBr, hQc]
      _ = 2 ^ 8 * 2 ^ 17 := by norm_num
  have h3 : rAB ≤ 2 ^ 16 := by
    calc rAB ≤ rA * rB := hle
      _ ≤ 2 ^ 8 * 2 ^ 8 := Nat.mul_le_mul h1 h2
      _ = 2 ^ 16 := by norm_num
  refine Nat.le_of_mul_le_mul_left (c := 2 ^ 16) ?_ (by norm_num)
  calc 2 ^ 16 * 2 ^ 9 = 2 ^ 25 := by norm_num
    _ = rAB * N := by rw [← hQc, hABr]
    _ ≤ 2 ^ 16 * N := Nat.mul_le_mul_right _ h3

theorem s344_exists
    [Finite G] (hSLS : SLSStatement d₀) (hTV : TableVIn G)
    (hL : LeechStatement) (hT4 : TableIVIn G) {a z₀ : G} (hG : GMSF1Type d₀ a z₀)
    {w x y : G} (hw : IsConj z₀ w) (hx : x ∈ Subgroup.centralizer ({w} : Set G))
    (hy : y ∈ Subgroup.centralizer ({w} : Set G)) (hxA : IsConj a x) (hyA : IsConj a y) :
    ∃ w₀ ∈ leechQ w ⊓ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G),
      w₀ ≠ w ∧ IsConj z₀ w₀ ∧ IsConj z₀ (w * w₀) := by
  have hQ := (hG.2.of_isConj hw).extraspecialData
  have hXQ : leechQ w ⊓ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G) ≤
      leechQ w := inf_le_left.trans inf_le_left
  obtain ⟨E, hEX, hwE, hE8, hE2⟩ :=
    hQ.exists_elementary_card_eight hXQ (s344_card hSLS hTV hL hG hw hx hy hxA hyA)
  obtain ⟨e, heE, he1, heA⟩ := s33 hSLS hTV hL hG hT4 E hE8 hE2
  have heQ : e ∈ leechQ w := hXQ (hEX heE)
  have hew : e ≠ w := fun h => hwE (h ▸ heE)
  have he2 : orderOf e = 2 := orderOf_eq_two_of_mul_self (hE2 e heE) he1
  have heB : IsConj z₀ e := by
    rcases orderOf_eq_two_mem_leechQ hSLS hTV hL hG hw heQ he2 with h | h | h
    · exact absurd h hew
    · exact absurd h heA
    · exact h
  obtain ⟨b, z, u, h⟩ := exists_twoClasses hSLS hTV hL hG
  obtain ⟨T₂, T₃, T₄, hT⟩ := (h.leech w hw).exists_orbits
  have he4 : e ∈ T₄ := h.mem_four_of_isConj hw hT heQ hew heB
  have hewB : IsConj z₀ (e * w) :=
    h.isConj_of_mem_four hw hT (hT.four e he4).2.2.2
  refine ⟨e, hEX heE, hew, heB, ?_⟩
  rwa [← hQ.central e heQ]

theorem s345
    [Finite G] (hSLS : SLSStatement d₀) (hTV : TableVIn G) (hL : LeechStatement)
    (hLC : LeechCosetStatement) {a z₀ : G} (hG : GMSF1Type d₀ a z₀) {w x y : G}
    (hw : IsConj z₀ w) (hx : x ∈ Subgroup.centralizer ({w} : Set G)) (hxA : IsConj a x)
    (hxQ : x ∉ leechQ w) (hyA : IsConj a y) (hxy : x⁻¹ * y ∈ leechQ w) :
    ∃ q ∈ leechQ w, q * x * q⁻¹ = y := by
  have hyC : y ∈ Subgroup.centralizer ({w} : Set G) := by
    have : y = x * (x⁻¹ * y) := by group
    rw [this]
    exact Subgroup.mul_mem _ hx (leechQ_le_centralizer w hxy)
  have hyQ : y ∉ leechQ w := by
    intro hy
    apply hxQ
    have : x = y * (x⁻¹ * y)⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ hy (Subgroup.inv_mem _ hxy)
  obtain ⟨g, hg, hgx⟩ := isConj_of_not_mem_leechQ hSLS hTV hL hG hw hx hyC hxQ hyQ hxA hyA
  have hx2 : orderOf x = 2 := (orderOf_eq_of_isConj hxA).symm.trans hG.1.1
  have h35 : Nat.card ↥(Subgroup.centralizer ({w} : Set G) ⊓
      Subgroup.centralizer ({x} : Set G)) = 2 ^ 38 * 3 ^ 5 * 5 ^ 2 * 7 := by
    rw [card_centralizer_inf_of_not_mem_leechQ hSLS hTV hL hG hw hx hxQ hxA]
    rfl
  obtain ⟨q, hq, hcase⟩ := hLC G w (hG.2.of_isConj hw) x hx hx2 hxQ h35 g hg
    (by rw [hgx]; exact hxy)
  rcases hcase with h1 | h1
  · exact ⟨q, hq, h1.trans hgx⟩
  · exfalso
    have hxwB := isConj_mul_of_not_mem_leechQ hSLS hTV hL hG hw hx hxA hxQ
    have h2 : IsConj (x * w) y := isConj_iff.mpr ⟨q, h1.trans hgx⟩
    exact hG.not_isConj (hyA.trans (hxwB.trans h2).symm)

private theorem eq_one_of_odd_orderOf {w t : G} (ht : t ∈ leechQ w) (hodd : Odd (orderOf t)) :
    t = 1 := by
  obtain ⟨k, hk⟩ := exists_orderOf_eq_two_pow_of_mem_leechQ ht
  rcases k with _ | k
  · rw [pow_zero, orderOf_eq_one_iff] at hk
    exact hk
  · exfalso
    have : Even (orderOf t) := ⟨2 ^ k, by rw [hk, pow_succ]; ring⟩
    exact (Nat.not_even_iff_odd.mpr hodd) this

private theorem pow_eq_self_of_mul_self_eq_one {y : G} (hy : y * y = 1) {m : ℕ} (hm : Odd m) :
    y ^ m = y := by
  obtain ⟨k, rfl⟩ := hm
  rw [pow_succ, pow_mul, pow_two, hy, one_pow, one_mul]

theorem s346
    [Finite G] (hSLS : SLSStatement d₀) (hTV : TableVIn G) (hL : LeechStatement)
    (hLC : LeechCosetStatement) {a z₀ : G} (hG : GMSF1Type d₀ a z₀) {w x y x' y' : G}
    (hw : IsConj z₀ w) (hx : x ∈ Subgroup.centralizer ({w} : Set G))
    (hy : y ∈ Subgroup.centralizer ({w} : Set G)) (hx' : x' ∈ Subgroup.centralizer ({w} : Set G))
    (hy' : y' ∈ Subgroup.centralizer ({w} : Set G)) (hxA : IsConj a x) (hyA : IsConj a y)
    (hx'A : IsConj a x') (hy'A : IsConj a y') (hxy : x ≠ y) (hxx' : x⁻¹ * x' ∈ leechQ w)
    (hyy' : y⁻¹ * y' ∈ leechQ w) (hodd : Odd (orderOf (x * y)))
    (hodd' : Odd (orderOf (x' * y'))) :
    ∃ q ∈ leechQ w, q * x * q⁻¹ = x' ∧ q * y * q⁻¹ = y' := by
  have hQ := (hG.2.of_isConj hw).extraspecialData
  set C := Subgroup.centralizer ({w} : Set G) with hC
  have hMn : ∀ g ∈ C, ∀ q ∈ leechQ w, g * q * g⁻¹ ∈ leechQ w := fun g hg q hq =>
    conj_mem_leechQ hg hq
  have hMw : ∀ g ∈ C, g * w = w * g := fun g hg => Subgroup.mem_centralizer_singleton_iff.mp hg
  have hx2 : x * x = 1 := mul_self_eq_one_of_orderOf ((orderOf_eq_of_isConj hxA).symm.trans hG.1.1)
  have hy2 : y * y = 1 := mul_self_eq_one_of_orderOf ((orderOf_eq_of_isConj hyA).symm.trans hG.1.1)
  have hx'2 : x' * x' = 1 :=
    mul_self_eq_one_of_orderOf ((orderOf_eq_of_isConj hx'A).symm.trans hG.1.1)
  have hy'2 : y' * y' = 1 :=
    mul_self_eq_one_of_orderOf ((orderOf_eq_of_isConj hy'A).symm.trans hG.1.1)
  have hxQ : x ∉ leechQ w := by
    intro hxQ
    have hgh : y⁻¹ * (x * y) ∈ leechQ w := by
      have := hMn y⁻¹ (C.inv_mem hy) x hxQ
      simpa [mul_assoc] using this
    have h1 := inv_pow_mul_pow_mem_of_conj_mem hMn hy hgh (orderOf (x * y))
    rw [pow_orderOf_eq_one, mul_one, pow_eq_self_of_mul_self_eq_one hy2 hodd] at h1
    have hyQ : y ∈ leechQ w := by simpa using Subgroup.inv_mem _ h1
    have hxy1 := eq_one_of_odd_orderOf (Subgroup.mul_mem _ hxQ hyQ) hodd
    exact hxy (inv_eq_of_mul_eq_one_right hxy1 ▸ (inv_eq_of_mul_eq_one_right hx2).symm)
  have hx'Q : x' ∉ leechQ w := by
    intro h
    apply hxQ
    have : x = x' * (x⁻¹ * x')⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ h (Subgroup.inv_mem _ hxx')
  obtain ⟨q₁, hq₁, hq₁x⟩ := s345 hSLS hTV hL hLC hG hw hx hxA hxQ hx'A hxx'
  have hq₁C : q₁ ∈ C := leechQ_le_centralizer w hq₁
  obtain ⟨y₂, hy₂⟩ : ∃ y₂ : G, y₂ = q₁ * y * q₁⁻¹ := ⟨_, rfl⟩
  have hy₂C : y₂ ∈ C := by
    rw [hy₂]
    exact C.mul_mem (C.mul_mem hq₁C hy) (C.inv_mem hq₁C)
  have hy₂2 : y₂ * y₂ = 1 := by
    rw [hy₂]
    calc q₁ * y * q₁⁻¹ * (q₁ * y * q₁⁻¹) = q₁ * (y * y) * q₁⁻¹ := by group
      _ = 1 := by rw [hy2]; group
  have hy₂y' : y₂⁻¹ * y' ∈ leechQ w := by
    have h1 := hMn y⁻¹ (C.inv_mem hy) q₁⁻¹ (Subgroup.inv_mem _ hq₁)
    have h2 := Subgroup.mul_mem _ (Subgroup.mul_mem _ hq₁ h1) hyy'
    convert h2 using 1
    rw [hy₂]
    group
  have hd : x' * y₂ = q₁ * (x * y) * q₁⁻¹ := by
    rw [hy₂, ← hq₁x]
    group
  have hm : Odd (orderOf (x' * y₂)) := by
    rw [hd, orderOf_conj_eq]
    exact hodd
  have hdC : x' * y₂ ∈ C := C.mul_mem hx' hy₂C
  have huC : x' * y' ∈ C := C.mul_mem hx' hy'
  have hdu : (x' * y₂)⁻¹ * (x' * y') ∈ leechQ w := by
    rw [show (x' * y₂)⁻¹ * (x' * y') = y₂⁻¹ * y' by group]
    exact hy₂y'
  have hum : (x' * y') ^ orderOf (x' * y₂) = 1 := by
    have h1 := inv_pow_mul_pow_mem_of_conj_mem hMn hdC hdu (orderOf (x' * y₂))
    rw [pow_orderOf_eq_one, inv_one, one_mul] at h1
    exact eq_one_of_odd_orderOf h1 (hodd'.of_dvd_nat (orderOf_pow_dvd _))
  have hx'inv : x'⁻¹ = x' := inv_eq_of_mul_eq_one_right hx'2
  have hy₂inv : y₂⁻¹ = y₂ := inv_eq_of_mul_eq_one_right hy₂2
  have hy'inv : y'⁻¹ = y' := inv_eq_of_mul_eq_one_right hy'2
  have hxd : x' * (x' * y₂) * x' = (x' * y₂)⁻¹ := by
    calc x' * (x' * y₂) * x' = (x' * x') * y₂ * x' := by group
      _ = (x' * y₂)⁻¹ := by rw [hx'2, one_mul, mul_inv_rev, hx'inv, hy₂inv]
  have hxu : x' * (x' * y') * x' = (x' * y')⁻¹ := by
    calc x' * (x' * y') * x' = (x' * x') * y' * x' := by group
      _ = (x' * y')⁻¹ := by rw [hx'2, one_mul, mul_inv_rev, hx'inv, hy'inv]
  obtain ⟨q, hq, hqd, hqx⟩ := hQ.exists_conj_of_inverting hMn hMw hx' hdC huC hm
    (pow_orderOf_eq_one _) hum hx'2 hxd hxu hdu
  have hqx' : q * x' * q⁻¹ = x' := by
    rcases hqx with h | h
    · exact h
    · exfalso
      have h1 : IsConj a (x' * w) := by
        rw [← h]
        exact hx'A.trans (isConj_iff.mpr ⟨q, rfl⟩)
      exact hG.not_isConj
        (h1.trans (isConj_mul_of_not_mem_leechQ hSLS hTV hL hG hw hx' hx'A hx'Q).symm)
  refine ⟨q * q₁, Subgroup.mul_mem _ hq hq₁, ?_, ?_⟩
  · calc q * q₁ * x * (q * q₁)⁻¹ = q * (q₁ * x * q₁⁻¹) * q⁻¹ := by group
      _ = x' := by rw [hq₁x, hqx']
  · have hy₂' : q * y₂ * q⁻¹ = y' := by
      calc q * y₂ * q⁻¹ = (q * x' * q⁻¹)⁻¹ * (q * (x' * y₂) * q⁻¹) := by group
        _ = y' := by rw [hqx', hqd]; group
    calc q * q₁ * y * (q * q₁)⁻¹ = q * (q₁ * y * q₁⁻¹) * q⁻¹ := by group
      _ = y' := by rw [← hy₂, hy₂']

theorem s346_frattini
    [Finite G] (hSLS : SLSStatement d₀) (hTV : TableVIn G)
    (hL : LeechStatement) (hLC : LeechCosetStatement) {a z₀ : G} (hG : GMSF1Type d₀ a z₀)
    {w x y g : G} (hw : IsConj z₀ w) (hx : x ∈ Subgroup.centralizer ({w} : Set G))
    (hy : y ∈ Subgroup.centralizer ({w} : Set G)) (hxA : IsConj a x) (hyA : IsConj a y)
    (hxy : x ≠ y) (hodd : Odd (orderOf (x * y))) (hg : g ∈ Subgroup.centralizer ({w} : Set G))
    (hgx : x⁻¹ * (g * x * g⁻¹) ∈ leechQ w) (hgy : y⁻¹ * (g * y * g⁻¹) ∈ leechQ w) :
    ∃ q ∈ leechQ w,
      q * g ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G) := by
  have hconj : ∀ t : G, t ∈ Subgroup.centralizer ({w} : Set G) →
      g * t * g⁻¹ ∈ Subgroup.centralizer ({w} : Set G) := fun t ht =>
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hg ht) (Subgroup.inv_mem _ hg)
  obtain ⟨q, hq, hqx, hqy⟩ := s346 hSLS hTV hL hLC hG hw hx hy (hconj x hx) (hconj y hy) hxA hyA
    (hxA.trans (isConj_iff.mpr ⟨g, rfl⟩)) (hyA.trans (isConj_iff.mpr ⟨g, rfl⟩)) hxy hgx hgy hodd
    (by
      rw [show g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ by group, orderOf_conj_eq]
      exact hodd)
  have hcent : ∀ t : G, q * t * q⁻¹ = g * t * g⁻¹ →
      q⁻¹ * g ∈ Subgroup.centralizer ({t} : Set G) := by
    intro t h
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc q⁻¹ * g * t = q⁻¹ * (g * t * g⁻¹) * g := by group
      _ = q⁻¹ * (q * t * q⁻¹) * g := by rw [h]
      _ = t * (q⁻¹ * g) := by group
  exact ⟨q⁻¹, Subgroup.inv_mem _ hq, Subgroup.mem_inf.mpr ⟨hcent x hqx, hcent y hqy⟩⟩

end CFSG.Monster.GMS
