module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.RankThree.PartTwo.Sec13.F135LastR2Plane
public import CFSG.RankThree.PartTwo.Sec13.F135LastR4Cube

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

section Fixed

open CFSG Subgroup

theorem exists_fixed_orderOf_eq_prime {S : Type*} [Group S] [Finite S] {p : ℕ} (hp : p.Prime)
    (hS : p ∣ Nat.card S) (α : MulAut S) (hα : α ^ p = 1) :
    ∃ s : S, orderOf s = p ∧ α s = s := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hA : IsPGroup p (Subgroup.zpowers α) := by
    intro g
    refine ⟨1, ?_⟩
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp g.2
    apply Subtype.ext
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hα, one_zpow]
  let C : Subgroup S :=
    { carrier := {s | α s = s}
      mul_mem' := fun {a b} ha hb => by
        have ha' : α a = a := ha
        have hb' : α b = b := hb
        show α (a * b) = a * b
        rw [map_mul, ha', hb']
      one_mem' := by
        show α 1 = 1
        exact map_one α
      inv_mem' := fun {a} ha => by
        have ha' : α a = a := ha
        show α a⁻¹ = a⁻¹
        rw [map_inv, ha'] }
  have hset : MulAction.fixedPoints (Subgroup.zpowers α) S = (C : Set S) := by
    ext s
    rw [MulAction.mem_fixedPoints]
    constructor
    · intro h
      exact h ⟨α, Subgroup.mem_zpowers α⟩
    · intro h a
      have h' : α s = s := h
      have hs : α ∈ MulAction.stabilizer (MulAut S) s := MulAction.mem_stabilizer_iff.mpr h'
      have hle : Subgroup.zpowers α ≤ MulAction.stabilizer (MulAut S) s :=
        Subgroup.zpowers_le.mpr hs
      exact MulAction.mem_stabilizer_iff.mp (hle a.2)
  have hcard : p ∣ Nat.card C := by
    have h1 : Nat.card S ≡ Nat.card (MulAction.fixedPoints (Subgroup.zpowers α) S) [MOD p] :=
      hA.card_modEq_card_fixedPoints S
    have h0 : Nat.card S ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr hS
    have h2 : Nat.card (MulAction.fixedPoints (Subgroup.zpowers α) S) ≡ 0 [MOD p] :=
      h1.symm.trans h0
    have h3 : Nat.card (MulAction.fixedPoints (Subgroup.zpowers α) S) = Nat.card C := by
      rw [hset]
      rfl
    rw [← h3]
    exact Nat.modEq_zero_iff_dvd.mp h2
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hcard
  refine ⟨(x : S), ?_, ?_⟩
  · rw [Subgroup.orderOf_coe]
    exact hx
  · exact x.2

theorem pow_natCard_center_eq_one_aux {J : Type*} [Group J] {g : J}
    (hg : g ∈ Subgroup.center J) :
    g ^ Nat.card (Subgroup.center J) = 1 := by
  have h : (⟨g, hg⟩ : Subgroup.center J) ^ Nat.card (Subgroup.center J) = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (orderOf_dvd_natCard _)
  exact congrArg Subtype.val h

theorem exists_lift_fixed_orderOf_eq_prime {J : Type*} [Group J] [Finite J] {p : ℕ} (hp : p.Prime)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center J)) (f : MulAut J) (x : J)
    (hxo : orderOf (QuotientGroup.mk x : J ⧸ Subgroup.center J) = p)
    (hfx : (QuotientGroup.mk (f x) : J ⧸ Subgroup.center J) = QuotientGroup.mk x) :
    ∃ w : J, orderOf w = p ∧ f w = w := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hζ : x⁻¹ * f x ∈ Subgroup.center J := by
    have h1 : (f x)⁻¹ * x ∈ Subgroup.center J := QuotientGroup.eq.mp hfx
    have h2 := inv_mem h1
    rwa [mul_inv_rev, inv_inv] at h2
  obtain ⟨ζ, hζZ, hfxζ⟩ : ∃ ζ ∈ Subgroup.center J, f x = x * ζ :=
    ⟨x⁻¹ * f x, hζ, (mul_inv_cancel_left x (f x)).symm⟩
  have hcomm : Commute x ζ := Subgroup.mem_center_iff.mp hζZ x
  have hζpow : ζ ^ Nat.card (Subgroup.center J) = 1 :=
    pow_natCard_center_eq_one_aux hζZ
  have hxp : x ^ p ∈ Subgroup.center J := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    have h := pow_orderOf_eq_one (QuotientGroup.mk x : J ⧸ Subgroup.center J)
    rwa [hxo] at h
  refine ⟨x ^ Nat.card (Subgroup.center J), ?_, ?_⟩
  · apply orderOf_eq_prime
    · rw [pow_right_comm]
      exact pow_natCard_center_eq_one_aux hxp
    · intro h
      have hmk : (QuotientGroup.mk x : J ⧸ Subgroup.center J) ^ Nat.card (Subgroup.center J) = 1 := by
        rw [← QuotientGroup.mk_pow, h, QuotientGroup.mk_one]
      have hdvd : orderOf (QuotientGroup.mk x : J ⧸ Subgroup.center J) ∣
          Nat.card (Subgroup.center J) :=
        orderOf_dvd_of_pow_eq_one hmk
      rw [hxo] at hdvd
      exact hZ hdvd
  · rw [map_pow, hfxζ, hcomm.mul_pow, hζpow, mul_one]

end Fixed

section Cube

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

theorem r3_cube_of_central_commuting {N : Type} [Group N] [Finite N] {p : ℕ} (hp : p.Prime)
    {Y : Subgroup N} (hY : Nat.card Y = p) (hYc : Y ≤ Subgroup.center N)
    {v f : N} (hv : orderOf v = p) (hf : f ^ p = 1) (hvf : v * f = f * v)
    (hYv : Y ⊓ Subgroup.zpowers v = ⊥) (hfA : f ∉ Y ⊔ Subgroup.zpowers v) :
    ∃ F : Subgroup N, CFSG.Open.IsElemAbelian p F ∧ Nat.card F = p ^ 3 ∧
      F = Y ⊔ Subgroup.zpowers v ⊔ Subgroup.zpowers f := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hzp : ∀ w : N, orderOf w = p → ∀ x ∈ Subgroup.zpowers w, x ^ p = 1 := by
    intro w hw x hx
    have h1 := Subgroup.orderOf_dvd_natCard (Subgroup.zpowers w) hx
    rw [Nat.card_zpowers, hw] at h1
    exact orderOf_dvd_iff_pow_eq_one.1 h1
  have hYZ : ∀ y ∈ Y, ∀ k ∈ Subgroup.zpowers v, y * k = k * y :=
    fun y hy k _ => ((Subgroup.mem_center_iff.1 (hYc hy)) k).symm
  have hYel : CFSG.Open.IsElemAbelian p Y := by
    refine ⟨⟨⟨fun a b => Subtype.ext ((Subgroup.mem_center_iff.1 (hYc a.2)) b.1).symm⟩⟩, ?_⟩
    intro x hx
    have h1 := Subgroup.orderOf_dvd_natCard Y hx
    rw [hY] at h1
    exact orderOf_dvd_iff_pow_eq_one.1 h1
  have hVel : CFSG.Open.IsElemAbelian p (Subgroup.zpowers v) := ⟨inferInstance, hzp v hv⟩
  have hAel : CFSG.Open.IsElemAbelian p (Y ⊔ Subgroup.zpowers v) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hYel hVel hYZ
  have hAcard : Nat.card (Y ⊔ Subgroup.zpowers v : Subgroup N) = p * p := by
    rw [r4d_card_sup hYZ hYv, hY, Nat.card_zpowers, hv]
  have hf1 : f ≠ 1 := by
    intro h1
    apply hfA
    rw [h1]
    exact (Y ⊔ Subgroup.zpowers v).one_mem
  have hfo : orderOf f = p := orderOf_eq_prime hf hf1
  have hZel : CFSG.Open.IsElemAbelian p (Subgroup.zpowers f) := ⟨inferInstance, hzp f hfo⟩
  have hfY : ∀ y ∈ Y, f * y = y * f := fun y hy => Subgroup.mem_center_iff.1 (hYc hy) f
  have hfk : ∀ k ∈ Subgroup.zpowers v, f * k = k * f := by
    intro k hk
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    exact Commute.zpow_right (show Commute f v from hvf.symm) n
  have hfA' : ∀ g ∈ Y ⊔ Subgroup.zpowers v, f * g = g * f := by
    intro g hg
    obtain ⟨y, hy, k, hk, rfl⟩ := r2a_mem_sup hYZ hg
    rw [← mul_assoc, hfY y hy, mul_assoc, hfk k hk, ← mul_assoc]
  have hfinf : (Y ⊔ Subgroup.zpowers v) ⊓ Subgroup.zpowers f = ⊥ := by
    have hdvd : Nat.card ↥((Y ⊔ Subgroup.zpowers v) ⊓ Subgroup.zpowers f) ∣ p := by
      have h2 := Subgroup.card_dvd_of_le
        (inf_le_right : (Y ⊔ Subgroup.zpowers v) ⊓ Subgroup.zpowers f ≤ Subgroup.zpowers f)
      rwa [Nat.card_zpowers, hfo] at h2
    rcases (Nat.dvd_prime hp).1 hdvd with h1 | h1
    · exact Subgroup.card_eq_one.1 h1
    · exfalso
      have hKz : (Y ⊔ Subgroup.zpowers v) ⊓ Subgroup.zpowers f = Subgroup.zpowers f :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (le_of_eq (by rw [Nat.card_zpowers, hfo, h1]))
      have hfmem : f ∈ (Y ⊔ Subgroup.zpowers v) ⊓ Subgroup.zpowers f := by
        rw [hKz]
        exact Subgroup.mem_zpowers f
      exact hfA (Subgroup.mem_inf.1 hfmem).1
  have hcAf : ∀ x ∈ Y ⊔ Subgroup.zpowers v, ∀ y ∈ Subgroup.zpowers f, x * y = y * x := by
    intro x hx y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact Commute.zpow_right (show Commute x f from (hfA' x hx).symm) n
  have hcardAF : Nat.card (Y ⊔ Subgroup.zpowers v ⊔ Subgroup.zpowers f : Subgroup N) =
      Nat.card (Y ⊔ Subgroup.zpowers v : Subgroup N) * Nat.card (Subgroup.zpowers f) :=
    r4d_card_sup hcAf hfinf
  have hFel : CFSG.Open.IsElemAbelian p (Y ⊔ Subgroup.zpowers v ⊔ Subgroup.zpowers f) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hAel hZel hcAf
  refine ⟨Y ⊔ Subgroup.zpowers v ⊔ Subgroup.zpowers f, hFel, ?_, rfl⟩
  rw [hcardAF, hAcard, Nat.card_zpowers, hfo]
  ring

theorem r3_wDelta {N : Type} [Group N] [Finite N] {p : ℕ} (hp : p.Prime)
    {J₀ : Subgroup N} (hJ₀ : CFSG.IsComponent J₀) {u : N} (hu2 : u * u = 1)
    (hne : J₀.map (MulAut.conj u).toMonoidHom ≠ J₀)
    (hm : ¬ p ∣ Nat.card (Subgroup.center J₀))
    {Y : Subgroup N} (hY : Nat.card Y = p) (hYc : Y ≤ Subgroup.center N)
    {w : N} (hw : w ∈ J₀) (hwo : orderOf w = p) :
    orderOf (w * (u * w * u⁻¹)) = p ∧ u * (w * (u * w * u⁻¹)) = (w * (u * w * u⁻¹)) * u ∧
      Y ⊓ Subgroup.zpowers (w * (u * w * u⁻¹)) = ⊥ ∧
      ∀ k : ℤ, ∀ j ∈ J₀, (w * (u * w * u⁻¹)) ^ k * j * ((w * (u * w * u⁻¹)) ^ k)⁻¹ =
        w ^ k * j * (w ^ k)⁻¹ := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨J₁, hJ₁def⟩ : ∃ J₁ : Subgroup N, J₁ = J₀.map (MulAut.conj u).toMonoidHom := ⟨_, rfl⟩
  rw [← hJ₁def] at hne
  have hJ₁ : CFSG.IsComponent J₁ := by
    rw [hJ₁def]
    exact CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj u) hJ₀
  have hcomm : ∀ x ∈ J₀, ∀ y ∈ J₁, x * y = y * x := by
    intro x hx y hy
    rcases CFSG.LocalCores.distinct_components_commute hJ₀ hJ₁ with he | hb
    · exact absurd he.symm hne
    · have hxy : ⁅x, y⁆ ∈ ⁅J₀, J₁⁆ := Subgroup.commutator_mem_commutator hx hy
      rw [hb, Subgroup.mem_bot] at hxy
      exact commutatorElement_eq_one_iff_mul_comm.1 hxy
  have hcen : ∀ J : Subgroup N, ¬ p ∣ Nat.card (Subgroup.center J) →
      ∀ x ∈ J, (∀ j ∈ J, x * j = j * x) → x ^ p = 1 → x = 1 := by
    intro J hJ x hxJ hxc hxp
    by_contra hx1
    have hord : orderOf x = p := orderOf_eq_prime hxp hx1
    have hmem : (⟨x, hxJ⟩ : J) ∈ Subgroup.center J := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hxc g.1 g.2).symm
    have hdvd := Subgroup.orderOf_dvd_natCard (Subgroup.center J) hmem
    rw [Subgroup.orderOf_mk, hord] at hdvd
    exact hJ hdvd
  have hzp : ∀ a : N, orderOf a = p → ∀ x ∈ Subgroup.zpowers a, x ^ p = 1 := by
    intro a ha x hx
    have h1 := Subgroup.orderOf_dvd_natCard (Subgroup.zpowers a) hx
    rw [Nat.card_zpowers, ha] at h1
    exact orderOf_dvd_iff_pow_eq_one.1 h1
  have hW0 : Subgroup.zpowers w ≤ J₀ := Subgroup.zpowers_le.2 hw
  obtain ⟨w', hw'⟩ : ∃ w' : N, w' = u * w * u⁻¹ := ⟨_, rfl⟩
  have hw'J : w' ∈ J₁ := by
    rw [hJ₁def, hw']
    exact Subgroup.mem_map.2 ⟨w, hw, rfl⟩
  have hW1 : Subgroup.zpowers w' ≤ J₁ := Subgroup.zpowers_le.2 hw'J
  have hinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hconj_back : u * w' * u⁻¹ = w := by
    rw [hw', hinv]
    calc u * (u * w * u) * u = (u * u) * w * (u * u) := by group
      _ = w := by rw [hu2, one_mul, mul_one]
  have hconjw : (MulAut.conj u).toMonoidHom w = w' := by
    rw [hw']
    rfl
  have hw'o : orderOf w' = p := by
    rw [← hwo, ← hconjw]
    exact orderOf_injective (MulAut.conj u).toMonoidHom (MulEquiv.injective _) w
  have hcW : Commute w w' := hcomm w hw w' hw'J
  have hzinf : Subgroup.zpowers w ⊓ Subgroup.zpowers w' = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hx0, hx1⟩ := Subgroup.mem_inf.1 hx
    exact hcen J₀ hm x (hW0 hx0) (fun j hj => (hcomm j hj x (hW1 hx1)).symm) (hzp w hwo x hx0)
  have hvconj : u * (w * w') * u⁻¹ = w * w' := by
    calc u * (w * w') * u⁻¹ = (u * w * u⁻¹) * (u * w' * u⁻¹) := by group
      _ = w' * w := by rw [hconj_back, ← hw']
      _ = w * w' := hcW.eq.symm
  have hvu : u * (w * w') = (w * w') * u := mul_inv_eq_iff_eq_mul.1 hvconj
  have hpw : w ^ p = 1 := by
    rw [← hwo]
    exact pow_orderOf_eq_one w
  have hpw' : w' ^ p = 1 := by
    rw [← hw'o]
    exact pow_orderOf_eq_one w'
  have hv1 : w * w' ≠ 1 := by
    intro h
    have hweq : w = w'⁻¹ := eq_inv_of_mul_eq_one_left h
    have hmemw : w ∈ Subgroup.zpowers w ⊓ Subgroup.zpowers w' := by
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_zpowers w, ?_⟩
      rw [hweq]
      exact Subgroup.inv_mem _ (Subgroup.mem_zpowers w')
    rw [hzinf, Subgroup.mem_bot] at hmemw
    rw [hmemw, orderOf_one] at hwo
    exact hp.ne_one hwo.symm
  have hvord : orderOf (w * w') = p := by
    refine orderOf_eq_prime ?_ hv1
    rw [hcW.mul_pow, hpw, hpw', one_mul]
  have hYv : Y ⊓ Subgroup.zpowers (w * w') = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro g hg
    obtain ⟨hgY, hgv⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hgv
    have hgc : ∀ j : N, j * (w ^ k * w' ^ k) = (w ^ k * w' ^ k) * j := by
      intro j
      rw [← hcW.mul_zpow k, hk]
      exact Subgroup.mem_center_iff.1 (hYc hgY) j
    have hwk : ∀ j ∈ J₀, j * w ^ k = w ^ k * j := by
      intro j hj
      have hjw : j * w' ^ k = w' ^ k * j := hcomm j hj (w' ^ k) (zpow_mem hw'J k)
      have key : j * w ^ k * w' ^ k = w ^ k * j * w' ^ k := by
        calc j * w ^ k * w' ^ k = j * (w ^ k * w' ^ k) := mul_assoc _ _ _
          _ = (w ^ k * w' ^ k) * j := hgc j
          _ = w ^ k * (w' ^ k * j) := mul_assoc _ _ _
          _ = w ^ k * (j * w' ^ k) := by rw [hjw]
          _ = w ^ k * j * w' ^ k := (mul_assoc _ _ _).symm
      exact mul_right_cancel key
    have hwk1 : w ^ k = 1 :=
      hcen J₀ hm (w ^ k) (zpow_mem hw k) (fun j hj => (hwk j hj).symm)
        (hzp w hwo (w ^ k) (Subgroup.zpow_mem_zpowers w k))
    have hw'k1 : w' ^ k = 1 := by
      have h1 : (orderOf w : ℤ) ∣ k := orderOf_dvd_iff_zpow_eq_one.2 hwk1
      rw [hwo] at h1
      have h2 : (orderOf w' : ℤ) ∣ k := by
        rw [hw'o]
        exact h1
      exact orderOf_dvd_iff_zpow_eq_one.1 h2
    rw [← hk, hcW.mul_zpow k, hwk1, hw'k1, one_mul]
  rw [← hw']
  refine ⟨hvord, hvu, hYv, ?_⟩
  intro k j hj
  have hjw : w' ^ k * j = j * w' ^ k := (hcomm j hj (w' ^ k) (zpow_mem hw'J k)).symm
  have hconjj : w' ^ k * j * (w' ^ k)⁻¹ = j := by
    rw [hjw, mul_inv_cancel_right]
  rw [hcW.mul_zpow k]
  calc w ^ k * w' ^ k * j * (w ^ k * w' ^ k)⁻¹ = w ^ k * (w' ^ k * j * (w' ^ k)⁻¹) * (w ^ k)⁻¹ := by
        group
    _ = w ^ k * j * (w ^ k)⁻¹ := by rw [hconjj]

end Cube

end CFSG.RankThree.PartTwo.Sec13.F135Last
