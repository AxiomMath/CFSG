module

public import CFSG.Quasithin.H13.NQCatT513PSL2

public section

namespace CFSG.Quasithin.H13.NQCat.T3

open CFSG.Quasithin.H13.NQCat.T513 CFSG.QuasithinUnique CFSG.GorensteinWalter
open scoped commutatorElement

local notation "L24" => Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2)

variable {A : Type} [Group A] {Q R S B D : Subgroup A}
variable {P : Type} [Group P] (e : ↥Q ⧸ Subgroup.center ↥Q ≃* P)

theorem autOf_eq_one_of_mem_centralizer {g : A} (hg : g ∈ Subgroup.normalizer (Q : Set A))
    (hgC : g ∈ Subgroup.centralizer (Q : Set A)) : autOf Q e ⟨g, hg⟩ = 1 := by
  ext y
  obtain ⟨q, rfl⟩ := toP_surjective Q e y
  rw [autOf_toP, MulAut.one_apply]
  congr 1
  apply Subtype.ext
  show g * (q : A) * g⁻¹ = q
  rw [← Subgroup.mem_centralizer_iff.mp hgC q q.2, mul_inv_cancel_right]

theorem mem_centralizer_of_autOf_eq_one (hQ : ⁅Q, Q⁆ = Q) {g : A}
    (hg : g ∈ Subgroup.normalizer (Q : Set A)) (h1 : autOf Q e ⟨g, hg⟩ = 1) :
    g ∈ Subgroup.centralizer (Q : Set A) := by
  have key : ∀ a ∈ Q, ∃ z ∈ Q, (∀ q ∈ Q, z * q = q * z) ∧ g * a * g⁻¹ = a * z := by
    intro a ha
    have h2 := congrArg (fun α : MulAut P => α (toP Q e ⟨a, ha⟩)) h1
    simp only [autOf_toP, MulAut.one_apply] at h2
    have h3 : (⟨a, ha⟩ : ↥Q)⁻¹ * qConj Q ⟨g, hg⟩ ⟨a, ha⟩ ∈ Subgroup.center ↥Q := by
      rw [← ker_toP Q e, MonoidHom.mem_ker, map_mul, map_inv, h2, inv_mul_cancel]
    refine ⟨a⁻¹ * (g * a * g⁻¹), ?_, fun q hq => ?_, by group⟩
    · exact Q.mul_mem (Q.inv_mem ha) (qConj Q ⟨g, hg⟩ ⟨a, ha⟩).2
    · exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp h3 ⟨q, hq⟩)).symm
  let H : Subgroup A := Q ⊓ Subgroup.centralizer ({g} : Set A)
  have hcomm : ⁅Q, Q⁆ ≤ H := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    refine Subgroup.mem_inf.mpr ⟨by rw [← hQ]; exact Subgroup.commutator_mem_commutator ha hb, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨z, hzQ, hz, h1⟩ := key a ha
    obtain ⟨w, hwQ, hw, h2⟩ := key b hb
    have hza : z * a = a * z := hz a ha
    have hzb : z * b = b * z := hz b hb
    have hwa : w * a = a * w := hw a ha
    have hwb : w * b = b * w := hw b hb
    have hzw : z * w = w * z := hz w hwQ
    have e1 : g * ⁅a, b⁆ * g⁻¹ = ⁅g * a * g⁻¹, g * b * g⁻¹⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      group
    have e2 : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      calc a * z * (b * w) * (a * z)⁻¹ * (b * w)⁻¹
          = a * (z * b) * w * z⁻¹ * a⁻¹ * w⁻¹ * b⁻¹ := by group
        _ = a * b * (z * w * z⁻¹) * a⁻¹ * w⁻¹ * b⁻¹ := by rw [hzb]; group
        _ = a * b * w * a⁻¹ * w⁻¹ * b⁻¹ := by rw [hzw]; group
        _ = a * b * (w * a⁻¹) * w⁻¹ * b⁻¹ := by group
        _ = a * b * (a⁻¹ * w) * w⁻¹ * b⁻¹ := by
            rw [show w * a⁻¹ = a⁻¹ * w by
              rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, ← hwa, mul_assoc, mul_inv_cancel, mul_one]]
        _ = a * b * a⁻¹ * b⁻¹ := by group
    calc ⁅a, b⁆ * g = ⁅a * z, b * w⁆ * g := by rw [e2]
      _ = (g * ⁅a, b⁆ * g⁻¹) * g := by rw [e1, h1, h2]
      _ = g * ⁅a, b⁆ := by group
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have : q ∈ H := hcomm (by rw [hQ]; exact hq)
  exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp this).2

variable (hcen : Subgroup.center P = ⊥)
  (hinn : ∀ α : MulAut P, Odd (orderOf α) → ∃ x, α = MulAut.conj x)
include hcen hinn

theorem iPart_eq_zpowers [Finite A] (h : Star513 Q R S B D)
    (hD3 : ∀ d ∈ D, ∃ k : ℕ, d ^ (3 ^ k) ∈ Subgroup.centralizer (Q : Set A)) :
    ∃ x : P, iPart Q e D = Subgroup.zpowers x ∧ ∃ k : ℕ, x ^ (3 ^ k) = 1 := by
  obtain ⟨hc, -⟩ := iPart_D e hinn h hcen
  obtain ⟨⟨x, hx⟩, hg⟩ := hc.exists_generator
  have hxD : iPart Q e D = Subgroup.zpowers x := by
    apply le_antisymm
    · intro y hy
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨y, hy⟩)
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, congrArg Subtype.val hk⟩
    · exact Subgroup.zpowers_le.mpr hx
  refine ⟨x, hxD, ?_⟩
  obtain ⟨d, hdN, hdD, hd⟩ := (mem_aImg Q e).1 (show MulAut.conj x ∈ aImg Q e D from hx)
  obtain ⟨k, hk⟩ := hD3 d hdD
  refine ⟨k, conj_injective_of_center hcen ?_⟩
  rw [map_pow, ← hd, map_one, ← map_pow]
  exact autOf_eq_one_of_mem_centralizer e _ hk

omit hcen in
theorem pow_three_mem_centralizer [Finite A] (h : Star513 Q R S B D) (hQ : ⁅Q, Q⁆ = Q) {x : P}
    (hx : iPart Q e D = Subgroup.zpowers x) (hx3 : x ^ 3 = 1) :
    ∀ d ∈ D, d ^ 3 ∈ Subgroup.centralizer (Q : Set A) := by
  intro d hd
  obtain ⟨y, hy⟩ := aImg_D_inner e hinn h _ (autOf_mem_aImg Q e (h.D_le_Q hd) hd)
  have hyD : y ∈ Subgroup.zpowers x := by
    rw [← hx]
    show MulAut.conj y ∈ aImg Q e D
    rw [← hy]
    exact autOf_mem_aImg Q e _ hd
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hyD
  refine mem_centralizer_of_autOf_eq_one e hQ (pow_mem (h.D_le_Q hd) 3) ?_
  have h1 : (⟨d ^ 3, pow_mem (h.D_le_Q hd) 3⟩ : ↥(Subgroup.normalizer (Q : Set A))) =
      ⟨d, h.D_le_Q hd⟩ ^ 3 := rfl
  rw [h1, map_pow, hy, ← map_pow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
    hx3, one_zpow, map_one]

omit hcen in
theorem conj_mul_mem_centralizer [Finite A] (h : Star513 Q R S B D) (hQ : ⁅Q, Q⁆ = Q) {x : P}
    (hx : iPart Q e D = Subgroup.zpowers x) {t : A} (htQ : t ∈ Q)
    (htx : toP Q e ⟨t, htQ⟩ * x * (toP Q e ⟨t, htQ⟩)⁻¹ = x⁻¹) :
    ∀ d ∈ D, t * d * t⁻¹ * d ∈ Subgroup.centralizer (Q : Set A) := by
  intro d hd
  obtain ⟨y, hy⟩ := aImg_D_inner e hinn h _ (autOf_mem_aImg Q e (h.D_le_Q hd) hd)
  have hyD : y ∈ Subgroup.zpowers x := by
    rw [← hx]
    show MulAut.conj y ∈ aImg Q e D
    rw [← hy]
    exact autOf_mem_aImg Q e _ hd
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hyD
  have htN : t ∈ Subgroup.normalizer (Q : Set A) := Subgroup.le_normalizer htQ
  have hmem : t * d * t⁻¹ * d ∈ Subgroup.normalizer (Q : Set A) :=
    mul_mem (mul_mem (mul_mem htN (h.D_le_Q hd)) (inv_mem htN)) (h.D_le_Q hd)
  refine mem_centralizer_of_autOf_eq_one e hQ hmem ?_
  have h1 : (⟨t * d * t⁻¹ * d, hmem⟩ : ↥(Subgroup.normalizer (Q : Set A))) =
      ⟨t, htN⟩ * ⟨d, h.D_le_Q hd⟩ * ⟨t, htN⟩⁻¹ * ⟨d, h.D_le_Q hd⟩ := rfl
  have hinv : toP Q e ⟨t, htQ⟩ * x ^ k * (toP Q e ⟨t, htQ⟩)⁻¹ = (x ^ k)⁻¹ := by
    rw [← conj_zpow, htx, inv_zpow]
  rw [h1, map_mul, map_mul, map_mul, map_inv, autOf_of_mem Q e htQ, hy, ← map_inv, ← map_mul,
    ← map_mul, ← map_mul, hinv, inv_mul_cancel, map_one]

omit hcen hinn in
theorem exists_b_three [Finite A] (h : Star513 Q R S B D) :
    ∃ (b : A) (hb : b ∈ B), orderOf (toP Q e ⟨b, h.R_le (h.hall_B.1 hb).1⟩) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB3 := card_B h
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := ↥B) 3 (by rw [hB3])
  refine ⟨b, b.2, ?_⟩
  have hbR := (h.hall_B.1 b.2).1
  have hbQ := h.R_le hbR
  have h1 : orderOf (toP Q e ⟨b, hbQ⟩) ∣ 3 := by
    rw [← hb, ← Subgroup.orderOf_coe, ← Subgroup.orderOf_mk (b : A) hbQ]
    exact orderOf_map_dvd _ _
  rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h1 | h1
  · exfalso
    have hz : (⟨b, hbQ⟩ : ↥Q) ∈ Subgroup.center ↥Q := by
      rw [← ker_toP Q e, MonoidHom.mem_ker, ← orderOf_eq_one_iff, h1]
    obtain ⟨e₄⟩ := exists_l24_of_lieModel h.R_type
    let π : ↥R →* ModO2 R := QuotientGroup.mk' _
    have hcen4 : π ⟨b, hbR⟩ ∈ Subgroup.center (ModO2 R) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective _ y
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      have := congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨r, h.R_le r.2⟩)
      exact this
    have hcbot : Subgroup.center (ModO2 R) = ⊥ := by
      have h1 := Subgroup.map_center_eq e₄
      rw [psl2_center_eq_bot (GaloisField 2 2)] at h1
      exact (Subgroup.map_eq_bot_iff_of_injective _ e₄.injective).mp h1
    rw [hcbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hcen4
    obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp (CFSG.pCore_isPGroup (G := ↥R) (p := 2))
      ⟨_, hcen4⟩
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, Subgroup.orderOf_coe, hb] at hn
    rcases n with _ | n
    · norm_num at hn
    · rw [pow_succ] at hn
      omega
  · exact h1

omit hcen in
theorem not_le_normalizer_of_not [Finite A] (h : Star513 Q R S B D)
    (hnot : ¬ D ≤ Subgroup.normalizer (R : Set A)) :
    ¬ iPart Q e D ≤ Subgroup.normalizer (pImg Q e R : Set P) :=
  fun hle => hnot (le_normalizer_of_iPart e hinn h hle)

theorem exists_three_group [Finite A] (h : Star513 Q R S B D)
    (hD3 : ∀ d ∈ D, ∃ k : ℕ, d ^ (3 ^ k) ∈ Subgroup.centralizer (Q : Set A))
    (hnot : ¬ D ≤ Subgroup.normalizer (R : Set A)) {b : A} (hb : b ∈ B)
    (hb3 : orderOf (toP Q e ⟨b, h.R_le (h.hall_B.1 hb).1⟩) = 3) :
    IsPGroup 3 ↥(iPart Q e D ⊔ Subgroup.zpowers (toP Q e ⟨b, h.R_le (h.hall_B.1 hb).1⟩)) ∧
      9 ≤ Nat.card ↥(iPart Q e D ⊔ Subgroup.zpowers (toP Q e ⟨b, h.R_le (h.hall_B.1 hb).1⟩)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite P := Finite.of_surjective _ (toP_surjective Q e)
  set y := toP Q e ⟨b, h.R_le (h.hall_B.1 hb).1⟩ with hy
  obtain ⟨x, hx, k, hxk⟩ := iPart_eq_zpowers e hcen hinn h hD3
  have hD3' : IsPGroup 3 ↥(iPart Q e D) := by
    rw [hx]
    have hdvd : orderOf x ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hxk
    obtain ⟨n, -, hn⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    exact IsPGroup.of_card (n := n) (by rw [Nat.card_zpowers, hn])
  have hy3 : IsPGroup 3 ↥(Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb3, pow_one])
  have hyN : Subgroup.zpowers y ≤ Subgroup.normalizer (iPart Q e D : Set P) :=
    Subgroup.zpowers_le.mpr (toP_mem_normalizer_iPart e h hb)
  have hE := hD3'.to_sup_of_normal_left' hy3 hyN
  refine ⟨hE, ?_⟩
  obtain ⟨m, hm⟩ := hE.exists_card_eq
  have h3 : 3 ∣ Nat.card ↥(iPart Q e D ⊔ Subgroup.zpowers y) := by
    rw [← hb3, ← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le le_sup_right
  rw [hm] at h3 ⊢
  rcases m with _ | _ | m
  · norm_num at h3
  · exfalso
    have heq : Subgroup.zpowers y = iPart Q e D ⊔ Subgroup.zpowers y :=
      Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hm, Nat.card_zpowers, hb3]; norm_num)
    apply not_le_normalizer_of_not e hinn h hnot
    calc iPart Q e D ≤ iPart Q e D ⊔ Subgroup.zpowers y := le_sup_left
      _ = Subgroup.zpowers y := heq.symm
      _ ≤ pImg Q e R := Subgroup.zpowers_le.mpr (toP_mem_pImg Q e _ (h.hall_B.1 hb).1)
      _ ≤ Subgroup.normalizer (pImg Q e R : Set P) := Subgroup.le_normalizer
  · calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ (m + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

end CFSG.Quasithin.H13.NQCat.T3
