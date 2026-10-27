module

public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21
open scoped Pointwise

section Elem

variable {G : Type} [Group G]

theorem e34_elem_intro {p : ℕ} {S : Subgroup G} (hc : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    (hp : ∀ x ∈ S, x ^ p = 1) : IsElementaryAbelian p S := by
  refine { is_comm := ⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩, exponent_dvd_p := ?_ }
  exact Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x => Subtype.ext (hp x x.2)

theorem e34_elem_comm {p : ℕ} {S : Subgroup G} (h : IsElementaryAbelian p S) :
    ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := fun x hx y hy =>
  congrArg Subtype.val (h.toIsMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem e34_elemAb_sup [Finite G] {p k l : ℕ} {X Y : Subgroup G} (hX : IsElemAb p k X)
    (hY : IsElemAb p l Y) (hc : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) (hi : X ⊓ Y = ⊥) :
    IsElemAb p (k + l) (X ⊔ Y) := by
  let μ : X × Y →* G := MonoidHom.noncommCoprod X.subtype Y.subtype
    fun a b => show Commute (X.subtype a) (Y.subtype b) from hc a a.2 b b.2
  have hrange : μ.range = X ⊔ Y := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  have hinj : Function.Injective μ := by
    rintro ⟨a1, b1⟩ ⟨a2, b2⟩ h
    have h' : (a1 : G) * b1 = a2 * b2 := h
    have hab : (a2 : G)⁻¹ * a1 = b2 * (b1 : G)⁻¹ := by
      calc (a2 : G)⁻¹ * a1 = (a2 : G)⁻¹ * (a1 * b1) * (b1 : G)⁻¹ := by group
        _ = (a2 : G)⁻¹ * (a2 * b2) * (b1 : G)⁻¹ := by rw [h']
        _ = b2 * (b1 : G)⁻¹ := by group
    have hmem : (a2 : G)⁻¹ * a1 ∈ X ⊓ Y :=
      ⟨X.mul_mem (X.inv_mem a2.2) a1.2, hab ▸ Y.mul_mem b2.2 (Y.inv_mem b1.2)⟩
    rw [hi, Subgroup.mem_bot] at hmem
    have ha : a1 = a2 := Subtype.ext (inv_mul_eq_one.mp hmem |>.symm)
    have hb : b1 = b2 := by
      apply Subtype.ext
      have : (a1 : G) * b1 = a1 * b2 := by rw [h', ← ha]
      exact mul_left_cancel this
    rw [ha, hb]
  have hX1 := hX.1
  have hY1 := hY.1
  have hsup : ∀ x ∈ X ⊔ Y, ∃ a ∈ X, ∃ b ∈ Y, x = a * b := by
    intro x hx
    rw [← hrange] at hx
    obtain ⟨⟨a, b⟩, rfl⟩ := hx
    exact ⟨a, a.2, b, b.2, rfl⟩
  refine ⟨?_, ?_⟩
  · refine e34_elem_intro ?_ ?_
    · intro x hx y hy
      obtain ⟨a, ha, b, hb, rfl⟩ := hsup x hx
      obtain ⟨a', ha', b', hb', rfl⟩ := hsup y hy
      have c1 : Commute a a' := e34_elem_comm hX1 a ha a' ha'
      have c2 : Commute a b' := hc a ha b' hb'
      have c3 : Commute b a' := (hc a' ha' b hb).symm
      have c4 : Commute b b' := e34_elem_comm hY1 b hb b' hb'
      exact ((c1.mul_right c2).mul_left (c3.mul_right c4)).eq
    · intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := hsup x hx
      have c : Commute a b := hc a ha b hb
      rw [c.mul_pow, elemPow_eq_one_of_isElementaryAbelian (A := X) a ha,
        elemPow_eq_one_of_isElementaryAbelian (A := Y) b hb, one_mul]
  · have h1 : Nat.card ↥(X ⊔ Y) = Nat.card (X × Y) := by
      rw [← hrange]
      exact Nat.card_range_of_injective hinj
    rw [h1, Nat.card_prod, hX.2, hY.2, pow_add]

theorem e34_elemAb_zpowers {g : G} (hg : orderOf g = 3) :
    IsElemAb 3 1 (Subgroup.zpowers g) := by
  refine ⟨e34_elem_intro ?_ ?_, ?_⟩
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact (zpow_add g i j).symm.trans ((add_comm i j ▸ (zpow_add g j i)))
  · rintro _ ⟨i, rfl⟩
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hg, pow_orderOf_eq_one,
      one_zpow]
  · rw [Nat.card_zpowers, hg, pow_one]

theorem e34_zpowers_inf_eq_bot {g : G} (hg : orderOf g = 3) {N : Subgroup G} (hgN : g ∉ N) :
    Subgroup.zpowers g ⊓ N = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨⟨i, rfl⟩, hi⟩
  have h3 : g ^ 3 = 1 := hg ▸ pow_orderOf_eq_one g
  have hmod : g ^ i = g ^ (i % 3) := by
    have := zpow_mod_orderOf g i
    rw [hg] at this
    exact this.symm
  have hr : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
  rw [Subgroup.mem_bot]
  beta_reduce at hi ⊢
  rcases hr with h | h | h
  · rw [hmod, h]; simp
  · exfalso; apply hgN; rw [hmod, h] at hi; simpa using hi
  · exfalso; apply hgN
    rw [hmod, h] at hi
    have : g = (g ^ (2 : ℤ)) ^ 2 := by
      rw [← zpow_natCast, ← zpow_mul]
      have : g ^ (4 : ℤ) = g := by
        have : g ^ (4 : ℤ) = g ^ 3 * g := by
          rw [show (4 : ℤ) = 3 + 1 by norm_num, zpow_add, zpow_one]
          norm_cast
        rw [this, h3, one_mul]
      simpa using this.symm
    rw [this]
    exact pow_mem hi 2

theorem e34_fixed_elem {β : MulAut G} (hβ : β ^ 3 = 1) {A : Subgroup G}
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hβA : ∀ a ∈ A, β a ∈ A) {t : G} (ht : t ∈ A)
    (ht1 : t ≠ 1) (ht3 : t ^ 3 = 1) : ∃ y ∈ A, y ≠ 1 ∧ y ^ 3 = 1 ∧ β y = y := by
  have hβ3 : ∀ g, β (β (β g)) = g := fun g => by
    have := congrArg (fun f : MulAut G => f g) hβ
    simpa [pow_succ, MulAut.mul_apply] using this
  have hb : β t ∈ A := hβA _ ht
  have hc : β (β t) ∈ A := hβA _ hb
  have hb3 : (β t) ^ 3 = 1 := by rw [← map_pow, ht3, map_one]
  have hc3 : (β (β t)) ^ 3 = 1 := by rw [← map_pow, hb3, map_one]
  have cab : Commute t (β t) := hA _ ht _ hb
  have cac : Commute t (β (β t)) := hA _ ht _ hc
  have cbc : Commute (β t) (β (β t)) := hA _ hb _ hc
  by_cases h1 : β t = t
  · exact ⟨t, ht, ht1, ht3, h1⟩
  by_cases h2 : t * β t * β (β t) = 1
  · have hc' : β (β t) = (β t)⁻¹ * t⁻¹ := by
      have h := eq_inv_of_mul_eq_one_left h2
      calc β (β t) = ((β (β t))⁻¹)⁻¹ := (inv_inv _).symm
        _ = (t * β t)⁻¹ := by rw [← h]
        _ = (β t)⁻¹ * t⁻¹ := mul_inv_rev _ _
    refine ⟨β t * t⁻¹, A.mul_mem hb (A.inv_mem ht), ?_, ?_, ?_⟩
    · intro h
      exact h1 (mul_inv_eq_one.mp h)
    · rw [cab.symm.inv_right.mul_pow, inv_pow, hb3, ht3]; simp
    · have hbb : (β t)⁻¹ * (β t)⁻¹ = β t := by
        have : β t * β t * β t = 1 := by simpa [pow_succ] using hb3
        calc (β t)⁻¹ * (β t)⁻¹ = (β t)⁻¹ * (β t)⁻¹ * (β t * β t * β t) := by rw [this, mul_one]
          _ = β t := by group
      have hk : t⁻¹ * (β t)⁻¹ = (β t)⁻¹ * t⁻¹ := (cab.inv_inv).eq
      rw [map_mul, map_inv, hc']
      calc (β t)⁻¹ * t⁻¹ * (β t)⁻¹ = (β t)⁻¹ * (t⁻¹ * (β t)⁻¹) := by rw [mul_assoc]
        _ = (β t)⁻¹ * ((β t)⁻¹ * t⁻¹) := by rw [hk]
        _ = ((β t)⁻¹ * (β t)⁻¹) * t⁻¹ := by rw [mul_assoc]
        _ = β t * t⁻¹ := by rw [hbb]
  · refine ⟨t * β t * β (β t), A.mul_mem (A.mul_mem ht hb) hc, h2, ?_, ?_⟩
    · have c1 : Commute (t * β t) (β (β t)) := cac.mul_left cbc
      rw [c1.mul_pow, cab.mul_pow, ht3, hb3, hc3]; simp
    · rw [map_mul, map_mul, hβ3]
      have c1 : Commute t (β t * β (β t)) := cab.mul_right cac
      calc β t * β (β t) * t = t * (β t * β (β t)) := c1.eq.symm
        _ = t * β t * β (β t) := by rw [mul_assoc]

end Elem

section Sylow

variable {G : Type} [Group G] [Finite G]

theorem e34_exists_fixed_sylow {β : MulAut G} (hβ : β ^ 3 = 1) {x : G} (hx : x ^ 3 = 1)
    (hβx : β x = x) :
    ∃ Q : Sylow 3 G, x ∈ (Q : Subgroup G) ∧ ∀ s ∈ (Q : Subgroup G), β s ∈ (Q : Subgroup G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set σ : MulAut G := MulAut.conj x with hσ
  have hσ3 : σ ^ 3 = 1 := by rw [hσ, ← map_pow, hx, map_one]
  have hcomm : Commute σ β := by
    refine MulEquiv.ext fun g => ?_
    show x * β g * x⁻¹ = β (x * g * x⁻¹)
    rw [map_mul, map_mul, map_inv, hβx]
  set Γ : Subgroup (MulAut G) := Subgroup.closure ({σ, β} : Set (MulAut G)) with hΓ
  haveI : IsMulCommutative Γ := Subgroup.isMulCommutative_closure (by
    intro a ha b hb _
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact Commute.refl _
    · exact hcomm
    · exact hcomm.symm
    · exact Commute.refl _)
  have hΓ3 : ∀ g ∈ Γ, g ^ 3 = 1 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem y hy => rcases hy with rfl | rfl <;> assumption
    | one => simp
    | mul y z hy hz ihy ihz =>
      have : Commute y z := congrArg Subtype.val
        (IsMulCommutative.is_comm.comm (⟨y, hy⟩ : Γ) ⟨z, hz⟩)
      rw [this.mul_pow, ihy, ihz, one_mul]
    | inv y hy ihy => rw [inv_pow, ihy, inv_one]
  have hΓp : IsPGroup 3 Γ := by
    rw [isPGroup_iff_orderOf_dvd_pow]
    intro g
    exact ⟨1, by
      rw [pow_one]
      exact orderOf_dvd_of_pow_eq_one (Subtype.ext (hΓ3 g g.2))⟩
  have hnd : ¬ 3 ∣ Nat.card (Sylow 3 G) := by
    intro h
    have := card_sylow_modEq_one 3 G
    have h0 := (Nat.modEq_zero_iff_dvd.mpr h).symm.trans this
    exact absurd h0 (by decide)
  obtain ⟨Q, hQ⟩ := hΓp.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 3 G) hnd
  have hfix : ∀ γ : MulAut G, γ ∈ Γ → γ • Q = Q := fun γ hγ => by
    have := MulAction.mem_fixedPoints.mp hQ ⟨γ, hγ⟩
    exact this
  refine ⟨Q, ?_, ?_⟩
  · have h1 : x • Q = Q := by
      rw [Sylow.smul_def]
      exact hfix _ (Subgroup.subset_closure (Or.inl rfl))
    have h2 := Sylow.smul_eq_iff_mem_normalizer.mp h1
    have h3 := Subgroup.mem_inf.mpr ⟨Subgroup.mem_zpowers x, h2⟩
    have hp : IsPGroup 3 (Subgroup.zpowers x) := by
      rw [isPGroup_iff_orderOf_dvd_pow]
      intro g
      exact ⟨1, by
        rw [pow_one, ← Subgroup.orderOf_coe]
        exact (orderOf_dvd_of_mem_zpowers g.2).trans (orderOf_dvd_of_pow_eq_one hx)⟩
    rw [hp.inf_normalizer_sylow Q] at h3
    exact h3.2
  · intro s hs
    have h1 := hfix β (Subgroup.subset_closure (Or.inr rfl))
    have h2 : β • (Q : Subgroup G) = (Q : Subgroup G) := by
      rw [← Sylow.pointwise_smul_def, h1]
    have h3 : β s ∈ β • (Q : Subgroup G) := Subgroup.smul_mem_pointwise_smul _ _ _ hs
    rwa [h2] at h3

end Sylow

end CFSG.RankThree.PartTwo.Sec21.FF79
