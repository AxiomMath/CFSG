module

public import CFSG.Quasithin.H13.J4M22

public noncomputable section

namespace CFSG.Quasithin.H13.J4

theorem ZC_le_center
    : ZC ≤ Subgroup.center CQ := by
  intro c hc
  rw [Subgroup.mem_center_iff]
  intro d
  apply Subtype.ext
  exact (Subgroup.mem_centralizer_iff.1 d.2 c (mem_ZC_iff.1 hc)).symm

theorem commutator_M22
    : commutator ↥CFSG.Blueprint.NativeSporadic.M22 = ⊤ := by
  obtain ⟨-, -, hsimple⟩ := CFSG.Sporadic.Mathieu.fam_m22_simplicity
  rcases hsimple.eq_bot_or_eq_top_of_normal (commutator ↥CFSG.Blueprint.NativeSporadic.M22)
    with h | h
  · exfalso
    have hab := Subgroup.commutator_mem_commutator (Subgroup.mem_top CFSG.Sporadic.Mathieu.m22a)
      (Subgroup.mem_top CFSG.Sporadic.Mathieu.m22b)
    rw [← _root_.commutator_def, h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      at hab
    have := congrArg Subtype.val hab
    revert this
    decide
  · exact h

theorem commutator_CmodZ
    : commutator (CQ ⧸ ZC) = ⊤ := by
  have e1 : (commutator ↥CFSG.Blueprint.NativeSporadic.M22).map m22EquivC.toMonoidHom =
      commutator (CQ ⧸ ZC) := by
    rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective m22EquivC.toMonoidHom m22EquivC.surjective]
  rw [← e1, commutator_M22,
    Subgroup.map_top_of_surjective m22EquivC.toMonoidHom m22EquivC.surjective]

theorem commutator_sup_ZC
    : commutator CQ ⊔ ZC = ⊤ := by
  rw [eq_top_iff]
  intro c _
  have hc : (QuotientGroup.mk' ZC c) ∈ commutator (CQ ⧸ ZC) :=
    commutator_CmodZ ▸ Subgroup.mem_top _
  rw [_root_.commutator_def,
    ← Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective ZC),
    ← Subgroup.map_commutator, ← _root_.commutator_def] at hc
  obtain ⟨d, hd, e⟩ := hc
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at e
  have : c = d * (d⁻¹ * c) := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hd) (Subgroup.mem_sup_right e)

theorem pow_eq_one_of_mem_ZC
    {c : CQ} (hc : c ∈ ZC) {n : ℕ} (hn : c ^ n = 1) (h3 : ¬ 3 ∣ n) :
    c = 1 := by
  have hc' := mem_ZC_iff.1 hc
  have h31 : c ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, OneMemClass.coe_one]
    rcases mem_Zq_iff.1 hc' with h | h | h
    · rw [h, one_pow]
    · rw [h, zq_pow_three]
    · rw [h, ← sq, ← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, zq_pow_three, one_pow])
  have hord : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one h31
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).1 hord with h | h
  · exact orderOf_eq_one_iff.1 h
  · exact absurd (h ▸ orderOf_dvd_of_pow_eq_one hn) h3

theorem mem_commutator_of_pow
    (hD : commutator CQ ⊓ ZC = ⊥) {c : CQ} {n : ℕ}
    (hn : c ^ n = 1) (h3 : ¬ 3 ∣ n) : c ∈ commutator CQ := by
  have hc : c ∈ commutator CQ ⊔ ZC := commutator_sup_ZC ▸ Subgroup.mem_top c
  obtain ⟨d, hd, e, he, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hc
  have hcomm : Commute d e := Subgroup.mem_center_iff.1 (ZC_le_center he) d
  have hpow : e ^ n ∈ commutator CQ := by
    have h1 : d ^ n * e ^ n = 1 := by rw [← hcomm.mul_pow, hn]
    rw [eq_inv_of_mul_eq_one_right h1]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hd n)
  have he1 : e ^ n = 1 := by
    have : e ^ n ∈ commutator CQ ⊓ ZC := ⟨hpow, Subgroup.pow_mem _ he n⟩
    rw [hD, Subgroup.mem_bot] at this
    exact this
  rw [pow_eq_one_of_mem_ZC he he1 h3, mul_one]
  exact hd

@[expose] def zC
    : CQ := ⟨zq, Zq_le_CQ (Subgroup.mem_zpowers zq)⟩

theorem zC_eq
    : (xC * yC) ^ 11 = zC :=
  Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_mul]; exact localChecks_spec.2.2.2.2.2.2.2.2.1)

theorem mem_ZC_iff'
    {c : CQ} : c ∈ ZC ↔ c = 1 ∨ c = zC ∨ c = zC * zC := by
  rw [mem_ZC_iff, mem_Zq_iff]
  constructor
  · rintro (h | h | h)
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr (Subtype.ext h))
  · rintro (rfl | rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

theorem commutator_CQ
    : commutator CQ = ⊤ := by
  by_cases hz : zC ∈ commutator CQ
  · have hZ : ZC ≤ commutator CQ := by
      intro c hc
      rcases mem_ZC_iff'.1 hc with rfl | rfl | rfl
      · exact Subgroup.one_mem _
      · exact hz
      · exact Subgroup.mul_mem _ hz hz
    rw [← commutator_sup_ZC, sup_eq_left.2 hZ]
  · exfalso
    have hD : commutator CQ ⊓ ZC = ⊥ := by
      rw [eq_bot_iff]
      rintro c ⟨hc1, hc2⟩
      rw [Subgroup.mem_bot]
      rcases mem_ZC_iff'.1 hc2 with rfl | rfl | rfl
      · rfl
      · exact absurd hc1 hz
      · exfalso
        apply hz
        have h4 : (zC * zC) * (zC * zC) = zC := Subtype.ext (by
          show zq * zq * (zq * zq) = zq
          rw [show zq * zq * (zq * zq) = zq ^ 3 * zq by
            rw [pow_succ, pow_succ, pow_one]; simp only [mul_assoc], zq_pow_three, one_mul])
        rw [← h4]
        exact Subgroup.mul_mem _ hc1 hc1
    have hx : xC ∈ commutator CQ := mem_commutator_of_pow hD (n := 2)
      (Subtype.ext (by rw [Subgroup.coe_pow]; exact localChecks_spec.2.2.2.2.2.2.1))
      (by norm_num)
    have hy : yC ∈ commutator CQ := mem_commutator_of_pow hD (n := 4)
      (Subtype.ext (by rw [Subgroup.coe_pow]; exact localChecks_spec.2.2.2.2.2.2.2.1))
      (by norm_num)
    apply hz
    rw [← zC_eq]
    exact Subgroup.pow_mem _ (Subgroup.mul_mem _ hx hy) 11

end CFSG.Quasithin.H13.J4
