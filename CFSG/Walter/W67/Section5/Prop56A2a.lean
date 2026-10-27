module

public import CFSG.Walter.W67.Section5.P56Ward
public import CFSG.Walter.W67.Section5.Prop56A1

public section

namespace CFSG.Walter.W67

variable {G : Type} [Group G] [Finite G]

namespace Sec56

@[expose] def invSub (J : G) (R : Subgroup G) (hRc : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a) :
    Subgroup G where
  carrier := {y | y ∈ R ∧ J * y * J⁻¹ = y⁻¹}
  mul_mem' := fun {a b} ha hb => ⟨R.mul_mem ha.1 hb.1, by
    calc J * (a * b) * J⁻¹ = (J * a * J⁻¹) * (J * b * J⁻¹) := by group
      _ = a⁻¹ * b⁻¹ := by rw [ha.2, hb.2]
      _ = (a * b)⁻¹ := by rw [mul_inv_rev, hRc _ (R.inv_mem hb.1) _ (R.inv_mem ha.1)]⟩
  one_mem' := ⟨R.one_mem, by group⟩
  inv_mem' := fun {a} ha => ⟨R.inv_mem ha.1, by
    calc J * a⁻¹ * J⁻¹ = (J * a * J⁻¹)⁻¹ := by group
      _ = a⁻¹⁻¹ := by rw [ha.2]⟩

end Sec56

namespace Frame5

variable {s : Std G} {f5 : Frame5 s}

namespace RData

variable {R : Subgroup G} (hR : f5.RData R)
include hR

theorem inf_H
    (h22 : S_lemma_2_2) (h26i : S_lemma_2_6_i) (hp : s.p = 3) :
    R ⊓ s.H = f5.P₁ :=
  f5.inf_H_eq_P₁ hp hR.isPGroup hR.P₁_le hR.B_le
    (f5.fpf_of_isPGroup h22 h26i hp hR.isPGroup hR.B_le hR.E_le)

theorem J_le : s.J ∈ Subgroup.normalizer (R : Set G) :=
  hR.JBE_le (Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)))

variable (hRc : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a)
include hRc

omit hR in
theorem mem_P₂ {y : G} : y ∈ Sec56.invSub s.J R hRc ↔ y ∈ R ∧ s.J * y * s.J⁻¹ = y⁻¹ := Iff.rfl

omit hR in
theorem P₂_le : Sec56.invSub s.J R hRc ≤ R := fun _ hy => hy.1

theorem P₁_inf_P₂ :
    f5.P₁ ⊓ Sec56.invSub s.J R hRc = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨hyP, hyR, hyJ⟩ := Subgroup.mem_inf.mp hy
  rw [Subgroup.mem_bot]
  have hyJ' : s.J * y * s.J⁻¹ = y := by
    rw [show s.J * y * s.J⁻¹ = y by
      rw [(s.commute_J (s.K_le_H (f5.P₁_le hyP))).symm, mul_inv_cancel_right]]
  have hy2 : y * y = 1 := by
    have h1 : y = y⁻¹ := hyJ'.symm.trans hyJ
    calc y * y = y * y⁻¹ := by rw [← h1]
      _ = 1 := mul_inv_cancel y
  have hodd : Odd (orderOf y) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hR.isPGroup
    exact Odd.of_dvd_nat (hk ▸ Odd.pow (by decide)) (Subgroup.orderOf_dvd_natCard R hyR)
  have h2 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, hy2])
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at hodd
    exact absurd hodd (by decide)

omit hR in
theorem mem_normalizer_P₂ {g : G} (hgR : g ∈ Subgroup.normalizer (R : Set G))
    (hgJ : g * s.J = s.J * g) :
    g ∈ Subgroup.normalizer ((Sec56.invSub s.J R hRc : Subgroup G) : Set G) := by
  apply Sec53.mem_normalizer_of_conj_le
  intro y hy
  refine ⟨(Subgroup.mem_normalizer_iff.mp hgR y).mp hy.1, ?_⟩
  have hJg : s.J * g⁻¹ = g⁻¹ * s.J := by
    calc s.J * g⁻¹ = g⁻¹ * (g * s.J) * g⁻¹ := by group
      _ = g⁻¹ * (s.J * g) * g⁻¹ := by rw [hgJ]
      _ = g⁻¹ * s.J := by group
  calc s.J * (g * y * g⁻¹) * s.J⁻¹ = (s.J * g) * y * (s.J * g)⁻¹ := by group
    _ = (g * s.J) * y * (g * s.J)⁻¹ := by rw [hgJ]
    _ = g * (s.J * y * s.J⁻¹) * g⁻¹ := by group
    _ = g * y⁻¹ * g⁻¹ := by rw [hy.2]
    _ = (g * y * g⁻¹)⁻¹ := by group

theorem B_le_P₂ : f5.B ≤ Subgroup.normalizer ((Sec56.invSub s.J R hRc : Subgroup G) : Set G) :=
  fun _ hb =>
  mem_normalizer_P₂ hRc (hR.B_le hb) (s.commute_J (s.K_le_H (f5.B_le hb)))

theorem E_le_P₂ : s.fr.E ≤ Subgroup.normalizer ((Sec56.invSub s.J R hRc : Subgroup G) : Set G) :=
  fun _ he => mem_normalizer_P₂ hRc (hR.E_le he) (s.commute_J (s.fr.E_le_H he))

theorem card_P₂
    (h22 : S_lemma_2_2) (h26i : S_lemma_2_6_i) (hp : s.p = 3)
    (hRq : Nat.card R = s.q ^ 2) :
    Nat.card (Sec56.invSub s.J R hRc) = s.q ∧ f5.P₁ ⊔ Sec56.invSub s.J R hRc = R := by
  have hJR := hR.J_le
  have hinfH := hR.inf_H h22 h26i hp
  have hφmem : ∀ y ∈ R, y⁻¹ * (s.J * y * s.J⁻¹) ∈ R := fun y hy =>
    R.mul_mem (R.inv_mem hy) ((Subgroup.mem_normalizer_iff.mp hJR y).mp hy)
  let φ : R →* R :=
    { toFun := fun y => ⟨(y : G)⁻¹ * (s.J * y * s.J⁻¹), hφmem y y.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        have hJa := (Subgroup.mem_normalizer_iff.mp hJR a).mp a.2
        have hJb := (Subgroup.mem_normalizer_iff.mp hJR b).mp b.2
        simp only [Subgroup.coe_mul]
        calc ((a : G) * b)⁻¹ * (s.J * (a * b) * s.J⁻¹)
            = (b : G)⁻¹ * ((a : G)⁻¹ * (s.J * a * s.J⁻¹)) * (s.J * b * s.J⁻¹) := by group
          _ = (a : G)⁻¹ * (s.J * a * s.J⁻¹) * ((b : G)⁻¹ * (s.J * b * s.J⁻¹)) := by
            rw [hRc _ (R.inv_mem b.2) _ (R.mul_mem (R.inv_mem a.2) hJa)]
            group) }
  have hker : ∀ y : R, φ y = 1 ↔ (y : G) ∈ f5.P₁ := by
    intro y
    constructor
    · intro h
      have h1 : (y : G)⁻¹ * (s.J * y * s.J⁻¹) = 1 := congrArg Subtype.val h
      have h2 : (y : G) ∈ s.H := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have : s.J * y * s.J⁻¹ = y := by
          calc s.J * (y : G) * s.J⁻¹ = y * ((y : G)⁻¹ * (s.J * y * s.J⁻¹)) := by group
            _ = y := by rw [h1, mul_one]
        calc (y : G) * s.J = s.J * y * s.J⁻¹ * s.J := by rw [this]
          _ = s.J * y := by group
      rw [← hinfH]
      exact Subgroup.mem_inf.mpr ⟨y.2, h2⟩
    · intro h
      apply Subtype.ext
      change (y : G)⁻¹ * (s.J * y * s.J⁻¹) = 1
      rw [show s.J * (y : G) * s.J⁻¹ = y by
        rw [(s.commute_J (s.K_le_H (f5.P₁_le h))).symm, mul_inv_cancel_right], inv_mul_cancel]
  have hrange : ∀ y : R, ((φ y : R) : G) ∈ Sec56.invSub s.J R hRc := by
    intro y
    refine ⟨hφmem y y.2, ?_⟩
    change s.J * ((y : G)⁻¹ * (s.J * y * s.J⁻¹)) * s.J⁻¹ = ((y : G)⁻¹ * (s.J * y * s.J⁻¹))⁻¹
    have hJ2 : s.J * s.J = 1 := s.J_mul_J
    have hJi : s.J⁻¹ = s.J := s.J_inv
    have h1 : ((y : G)⁻¹ * (s.J * y * s.J⁻¹))⁻¹ = s.J * (y : G)⁻¹ * s.J * y := by
      calc ((y : G)⁻¹ * (s.J * y * s.J⁻¹))⁻¹ = s.J⁻¹⁻¹ * (y : G)⁻¹ * s.J⁻¹ * y := by group
        _ = s.J * (y : G)⁻¹ * s.J * y := by rw [inv_inv, hJi]
    rw [h1, hJi]
    calc s.J * ((y : G)⁻¹ * (s.J * y * s.J)) * s.J
        = s.J * (y : G)⁻¹ * s.J * y * (s.J * s.J) := by group
      _ = s.J * (y : G)⁻¹ * s.J * y := by rw [hJ2, mul_one]
  have hkerφ : φ.ker = f5.P₁.subgroupOf R := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hker y
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hkerφ,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR.P₁_le).toEquiv] at h1
  have h2 : Nat.card φ.range ≤ Nat.card (Sec56.invSub s.J R hRc) := by
    have : φ.range.map R.subtype ≤ Sec56.invSub s.J R hRc := by
      rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
      exact hrange y
    have h3 := Subgroup.card_le_of_le this
    rwa [Subgroup.card_map_of_injective R.subtype_injective] at h3
  have hP₂N : Sec56.invSub s.J R hRc ≤ Subgroup.normalizer (f5.P₁ : Set G) := fun y hy =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun u hu =>
      (hRc y (P₂_le hRc hy) u (hR.P₁_le hu)).symm)
  have hsup := Sec54.card_sup_eq_mul hP₂N (hR.P₁_inf_P₂ hRc)
  have hsupR : f5.P₁ ⊔ Sec56.invSub s.J R hRc ≤ R := sup_le hR.P₁_le (P₂_le hRc)
  have h4 := Subgroup.card_le_of_le hsupR
  rw [hsup, hRq, f5.card_P₁] at h4
  rw [hRq, f5.card_P₁] at h1
  have hq := s.one_lt_q
  have hP₂card : Nat.card (Sec56.invSub s.J R hRc) = s.q := by
    apply le_antisymm
    · have : s.q * Nat.card (Sec56.invSub s.J R hRc) ≤ s.q * s.q := by nlinarith
      exact Nat.le_of_mul_le_mul_left this (by omega)
    · have : s.q * s.q ≤ s.q * Nat.card (Sec56.invSub s.J R hRc) := by nlinarith
      exact Nat.le_of_mul_le_mul_left this (by omega)
  refine ⟨hP₂card, Subgroup.eq_of_le_of_card_ge hsupR ?_⟩
  rw [hsup, hRq, f5.card_P₁, hP₂card, pow_two]

theorem pow_three_eq_one
    (h22 : S_lemma_2_2) (h26i : S_lemma_2_6_i) (hp : s.p = 3)
    (hRq : Nat.card R = s.q ^ 2) : ∀ y ∈ R, y ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hP₂c, hsup⟩ := hR.card_P₂ hRc h22 h26i hp hRq
  set P₂ := Sec56.invSub s.J R hRc with hP₂def
  have hP₂3 : IsPGroup 3 P₂ := hR.isPGroup.to_le (P₂_le hRc)
  have hP₂c' : ∀ a ∈ P₂, ∀ b ∈ P₂, a * b = b * a := fun a ha b hb =>
    hRc a (P₂_le hRc ha) b (P₂_le hRc hb)
  set K₃ := Subgroup.closure ((fun y : G => y ^ 3) '' (P₂ : Set G)) with hK₃def
  have hK₃le : K₃ ≤ P₂ := (Subgroup.closure_le P₂).mpr (by
    rintro _ ⟨y, hy, rfl⟩
    exact P₂.pow_mem hy 3)
  have hK₃N : ∀ g ∈ Subgroup.normalizer ((P₂ : Subgroup G) : Set G),
      g ∈ Subgroup.normalizer ((K₃ : Subgroup G) : Set G) := by
    intro g hg
    apply Sec56.mem_normalizer_of_map_conj_le
    rw [hK₃def, MonoidHom.map_closure, Set.image_image]
    apply Subgroup.closure_mono
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨g * y * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg y).mp hy, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact conj_pow
  have hK₃lt : K₃ ≠ P₂ := by
    intro h
    obtain ⟨⟨z, hzP⟩, hoz⟩ := exists_prime_orderOf_dvd_card' (G := P₂) 3 (by
      rw [hP₂c, Hyp.q, hp]
      exact dvd_pow_self 3 s.f_pos.ne')
    rw [Subgroup.orderOf_mk] at hoz
    let c : P₂ →* P₂ :=
      { toFun := fun y => y ^ 3
        map_one' := one_pow 3
        map_mul' := fun a b => by
          rw [(Commute.mul_pow (show Commute a b from Subtype.ext (hP₂c' a a.2 b b.2)) 3)] }
    have hcsurj : Function.Surjective c := by
      intro y
      have hy : (y : G) ∈ K₃ := by rw [h]; exact y.2
      have hrange : K₃ ≤ (c.range).map P₂.subtype := by
        rw [hK₃def, Subgroup.closure_le]
        rintro _ ⟨w, hw, rfl⟩
        exact ⟨c ⟨w, hw⟩, ⟨⟨w, hw⟩, rfl⟩, rfl⟩
      obtain ⟨_, ⟨w, rfl⟩, hw⟩ := hrange hy
      exact ⟨w, Subtype.ext hw⟩
    have hcinj := (Finite.injective_iff_surjective.mpr hcsurj)
    have hz1 : (⟨z, hzP⟩ : P₂) ≠ 1 := fun h1 => by
      have := congrArg Subtype.val h1
      simp only [OneMemClass.coe_one] at this
      rw [this, orderOf_one] at hoz
      norm_num at hoz
    apply hz1
    apply hcinj
    rw [map_one]
    apply Subtype.ext
    change z ^ 3 = 1
    rw [← hoz]
    exact pow_orderOf_eq_one z
  have hK₃1 : K₃ = ⊥ := by
    obtain ⟨k, hk⟩ := f5.card_eq_q_pow hp (hP₂3.to_le hK₃le)
      (fun b hb => hK₃N b (hR.B_le_P₂ hRc hb))
      (fun b hb hb1 y hy => f5.fpf_of_isPGroup h22 h26i hp hR.isPGroup hR.B_le hR.E_le b hb hb1
        y (P₂_le hRc (hK₃le hy)))
    have hlt : Nat.card K₃ < Nat.card P₂ := Subgroup.card_lt_of_lt (lt_of_le_of_ne hK₃le hK₃lt)
    rw [hk, hP₂c] at hlt
    have hk0 : k = 0 := by
      by_contra hk0
      have : s.q ^ 1 ≤ s.q ^ k := Nat.pow_le_pow_right (by have := s.one_lt_q; omega)
        (Nat.one_le_iff_ne_zero.mpr hk0)
      rw [pow_one] at this
      omega
    rw [hk0, pow_zero] at hk
    exact Subgroup.eq_bot_of_card_eq _ hk
  intro y hy
  rw [← hsup] at hy
  have hP₂N : P₂ ≤ Subgroup.normalizer (f5.P₁ : Set G) := fun w hw =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun u hu =>
      (hRc w (P₂_le hRc hw) u (hR.P₁_le hu)).symm)
  obtain ⟨u, hu, w, hw, rfl⟩ := (mem_sup_iff_of_le_normalizer hP₂N).mp hy
  have hu3 : u ^ 3 = 1 := by rw [← hp]; exact f5.P₁_pow u hu
  have hw3 : w ^ 3 = 1 := by
    have : w ^ 3 ∈ K₃ := Subgroup.subset_closure ⟨w, hw, rfl⟩
    rwa [hK₃1, Subgroup.mem_bot] at this
  rw [(Commute.mul_pow (show Commute u w from hRc u (hR.P₁_le hu) w (P₂_le hRc hw)) 3),
    hu3, hw3, one_mul]

end RData

end Frame5

end CFSG.Walter.W67
