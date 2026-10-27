module

public import CFSG.Quasithin.Vol2.Ch10SecKL7s
public import CFSG.Quasithin.Vol2.Ch10SecKL7r

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.KL7

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped Pointwise

variable {W : Type} [CommGroup W]

namespace Hyp

variable {Mb L₁ L₂ R : Subgroup (MulAut W)} {W₁ W₂ : Subgroup W} {τ : MulAut W}
variable (h : Hyp Mb L₁ L₂ W₁ W₂ τ) (hR : RHyp Mb L₁ L₂ R)
include h hR

theorem four_mem : 4 ∈ {c : ℕ | ∃ Y B S : Subgroup (MulAut W), Y ≤ B ∧ B ≤ Mb ∧ IsCyclic Y ∧
    Nat.card Y = 2 ^ c - 1 ∧ (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) ∧ Odd (Nat.card B) ∧
    IsSylowIn 2 S Mb ∧ (B : Set (MulAut W)) * (S : Set (MulAut W)) =
      (S : Set (MulAut W)) * (B : Set (MulAut W))} := by
  obtain ⟨c₁⟩ := h.coord
  have : Finite W := h.finite_W
  have := h.finite_aut
  obtain ⟨S, hSyl, hPS, ⟨t, htS, htK⟩, hSK⟩ := h.exists_sylow_data c₁
  have hSM := hSyl.le
  have htM : t ∈ Mb := hSM htS
  have htL : L₁.map (MulAut.conj t).toMonoidHom = L₂ :=
    (h.map_conj_eq htM).resolve_left fun h1 => htK (mem_normalizer_iff_map.2 h1)
  set E₁ := EE.map c₁.phi with hE₁
  set q := c₁.phi gq with hq
  set ct := (MulAut.conj t).toMonoidHom with hct
  set E₂ := E₁.map ct with hE₂
  set q' := t * q * t⁻¹ with hq'
  set E₀ := E₁ ⊔ E₂ with hE₀
  set B := Subgroup.zpowers q ⊔ Subgroup.zpowers q' ⊔ R with hB
  have hEL : E₁ ≤ L₁ := c₁.E_le_P.trans c₁.P_le
  have hqL : q ∈ L₁ := c₁.phi_mem gq
  have hE₂L : E₂ ≤ L₂ := htL ▸ Subgroup.map_mono hEL
  have hq'L : q' ∈ L₂ := htL ▸ Subgroup.mem_map_of_mem ct hqL
  have hRC := fun r (hr : r ∈ R) => Hyp.mem_C_iff.1 (hR.le hr)
  have hBN : B ≤ Subgroup.normalizer (E₀ : Set (MulAut W)) := by
    refine sup_le (sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)) fun r hr => ?_
    · refine mem_normalizer_of_conj_mem fun x hx => conj_mem_sup_of (fun e he =>
        Subgroup.mem_sup_left (c₁.q_conj_E he)) (fun e he => ?_) hx
      rw [h.comm' hqL (hE₂L he), mul_inv_cancel_right]
      exact Subgroup.mem_sup_right he
    · refine mem_normalizer_of_conj_mem fun x hx => conj_mem_sup_of (fun e he => ?_)
        (fun e he => ?_) hx
      · rw [← h.comm' (hEL he) hq'L, mul_inv_cancel_right]
        exact Subgroup.mem_sup_left he
      · obtain ⟨e', he', rfl⟩ := he
        refine Subgroup.mem_sup_right ⟨q * e' * q⁻¹, c₁.q_conj_E he', ?_⟩
        simp only [hct, hq', MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
    · refine mem_normalizer_of_conj_mem fun x hx => ?_
      have hxL : x ∈ L₁ ⊔ L₂ := sup_le (hEL.trans le_sup_left) (hE₂L.trans le_sup_right) hx
      have := Subgroup.mem_centralizer_iff.1 (hR.le hr).2 x hxL
      rw [← this, mul_inv_cancel_right]
      exact hx
  have hE₀S : E₀ ≤ S := sup_le (c₁.E_le_P.trans hPS) (by
    rintro _ ⟨e, he, rfl⟩
    exact mul_mem (mul_mem htS (hPS (c₁.E_le_P he))) (S.inv_mem htS))
  have hDEB' : (E₁ ⊔ Subgroup.zpowers q) ⊔ (E₁ ⊔ Subgroup.zpowers q).map ct ⊔ R ≤ E₀ ⊔ B := by
    refine sup_le (sup_le ?_ ?_) ?_
    · exact sup_le (le_sup_left.trans le_sup_left)
        (Subgroup.zpowers_le.2 (Subgroup.mem_sup_right (Subgroup.mem_sup_left
          (Subgroup.mem_sup_left (Subgroup.mem_zpowers q)))))
    · rw [Subgroup.map_sup, MonoidHom.map_zpowers]
      exact sup_le (le_sup_right.trans le_sup_left)
        (Subgroup.zpowers_le.2 (Subgroup.mem_sup_right (Subgroup.mem_sup_left
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))))
    · exact le_sup_right.trans le_sup_right
  have hDEB : ∀ x ∈ (E₁ ⊔ Subgroup.zpowers q) ⊔ (E₁ ⊔ Subgroup.zpowers q).map ct ⊔ R,
      x ∈ E₀ ⊔ B := fun x hx => hDEB' hx
  have hBD' : B ≤ (E₁ ⊔ Subgroup.zpowers q) ⊔ (E₁ ⊔ Subgroup.zpowers q).map ct ⊔ R := by
    refine sup_le (sup_le ?_ ?_) le_sup_right
    · exact le_sup_right.trans (le_sup_left.trans le_sup_left)
    · refine Subgroup.zpowers_le.2 (Subgroup.mem_sup_left (Subgroup.mem_sup_right ?_))
      exact Subgroup.mem_map_of_mem ct (Subgroup.mem_sup_right (Subgroup.mem_zpowers q))
  have hBD : ∀ b ∈ B, b ∈ (E₁ ⊔ Subgroup.zpowers q) ⊔ (E₁ ⊔ Subgroup.zpowers q).map ct ⊔ R :=
    fun b hb => hBD' hb
  have hD := fun s (hs : s ∈ S) x hx => h.conj_mem_D hR c₁ hSM htS htK hSK (x := x) hs hx
  have hBS : (B : Set (MulAut W)) * (S : Set (MulAut W)) =
      (S : Set (MulAut W)) * (B : Set (MulAut W)) := by
    ext x
    simp only [Set.mem_mul, SetLike.mem_coe]
    constructor
    · rintro ⟨b, hb, s, hs, rfl⟩
      have h1 := hD s⁻¹ (S.inv_mem hs) b (hBD b hb)
      rw [inv_inv] at h1
      have h2 : s⁻¹ * b * s ∈ ((E₀ ⊔ B : Subgroup (MulAut W)) : Set (MulAut W)) := hDEB _ h1
      rw [Subgroup.coe_mul_of_right_le_normalizer_left E₀ B hBN, Set.mem_mul] at h2
      obtain ⟨e, he, b', hb', heb⟩ := h2
      exact ⟨s * e, mul_mem hs (hE₀S he), b', hb', by rw [mul_assoc, heb]; group⟩
    · rintro ⟨s, hs, b, hb, rfl⟩
      have h1 := hD s hs b (hBD b hb)
      have h2 : s * b * s⁻¹ ∈ ((B ⊔ E₀ : Subgroup (MulAut W)) : Set (MulAut W)) := by
        rw [sup_comm]
        exact hDEB _ h1
      rw [Subgroup.coe_mul_of_left_le_normalizer_right B E₀ hBN, Set.mem_mul] at h2
      obtain ⟨b', hb', e, he, hbe⟩ := h2
      exact ⟨b', hb', e * s, mul_mem (hE₀S he) hs, by rw [← mul_assoc, hbe]; group⟩
  obtain ⟨z, hzR, hz1⟩ : ∃ z ∈ R, z ≠ 1 := by
    by_contra hall
    have hbot : R = ⊥ := eq_bot_iff.2 fun y hy => by
      by_contra hy1
      exact hall ⟨y, hy, hy1⟩
    have hc := hR.card
    rw [hbot, Subgroup.card_bot] at hc
    omega
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hz5 : orderOf z = 5 := orderOf_eq_prime (hR.pow5 z hzR) hz1
  have hq3 : orderOf q = 3 := c₁.orderOf_q
  have hqz : Commute q z := (hRC z hzR).2.1 q hqL
  have hord : orderOf (q * z) = 15 := by
    rw [hqz.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hq3, hz5]; norm_num), hq3, hz5]
  have hcommB : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
    refine comm_sup (comm_sup ?_ ?_ ?_) hR.comm ?_
    · rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
      exact (Commute.refl q).zpow_zpow m n
    · rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
      exact (Commute.refl q').zpow_zpow m n
    · rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
      exact Commute.zpow_zpow (h.comm' hqL hq'L) m n
    · intro a ha r hr
      have haL : a ∈ L₁ ⊔ L₂ := sup_le (Subgroup.zpowers_le.2 (Subgroup.mem_sup_left hqL))
        (Subgroup.zpowers_le.2 (Subgroup.mem_sup_right hq'L)) ha
      exact Subgroup.mem_centralizer_iff.1 (hR.le hr).2 a haL
  have hq15 : q ^ 15 = 1 := orderOf_dvd_iff_pow_eq_one.1 (by rw [hq3]; norm_num)
  have hoddB : Odd (Nat.card B) := by
    let B15 : Subgroup (MulAut W) :=
      { carrier := {b | b ∈ B ∧ b ^ 15 = 1}
        one_mem' := ⟨B.one_mem, one_pow _⟩
        mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
          rw [Commute.mul_pow (hcommB a ha.1 b hb.1), ha.2, hb.2, one_mul]⟩
        inv_mem' := fun {a} ha => ⟨B.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
    have hB15 : B ≤ B15 := by
      refine sup_le (sup_le (Subgroup.zpowers_le.2 ⟨Subgroup.mem_sup_left
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers q)), hq15⟩) (Subgroup.zpowers_le.2
          ⟨Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers q')), ?_⟩))
        fun r hr => ⟨Subgroup.mem_sup_right hr, ?_⟩
      · rw [hq', conj_pow, hq15, mul_one, mul_inv_cancel]
      · rw [show 15 = 5 * 3 by norm_num, pow_mul, hR.pow5 r hr, one_pow]
    by_contra heven
    rw [Nat.not_odd_iff_even] at heven
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := ↥B) 2 (even_iff_two_dvd.1 heven)
    have h15 : b ^ 15 = 1 := Subtype.ext (hB15 b.2).2
    have := orderOf_dvd_of_pow_eq_one h15
    rw [hb] at this
    norm_num at this
  refine ⟨Subgroup.zpowers (q * z), B, S, Subgroup.zpowers_le.2 (mul_mem (Subgroup.mem_sup_left
    (Subgroup.mem_sup_left (Subgroup.mem_zpowers q))) (Subgroup.mem_sup_right hzR)), ?_,
    Subgroup.isCyclic_zpowers _, by rw [Nat.card_zpowers, hord]; norm_num, hcommB, hoddB, hSyl,
    hBS⟩
  exact sup_le (sup_le (Subgroup.zpowers_le.2 (h.le₁ hqL)) (Subgroup.zpowers_le.2 (h.le₂ hq'L)))
    (hR.le.trans inf_le_left)

theorem nPrime_eq : E3.nPrime Mb = 4 := by
  have h4 := h.four_mem hR
  have hb : ∀ c ∈ {c : ℕ | ∃ Y B S : Subgroup (MulAut W), Y ≤ B ∧ B ≤ Mb ∧ IsCyclic Y ∧
      Nat.card Y = 2 ^ c - 1 ∧ (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) ∧ Odd (Nat.card B) ∧
      IsSylowIn 2 S Mb ∧ (B : Set (MulAut W)) * (S : Set (MulAut W)) =
        (S : Set (MulAut W)) * (B : Set (MulAut W))}, c ≤ 4 := by
    rintro c ⟨Y, B, S, hYB, hBM, hY, hc, -, hodd, -, -⟩
    exact h.le_four_of_mem hR hYB hBM hY hc hodd
  exact le_antisymm (csSup_le ⟨4, h4⟩ hb) (le_csSup ⟨4, hb⟩ h4)

end Hyp

end CFSG.Quasithin.Vol2.Ch10.SecB.KL7
