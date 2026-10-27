module

public import CFSG.Assembly.Defs
public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.Quasithin

namespace B19Aux

section Product

variable {Γ : Type*} [Group Γ]

theorem conj_mem_of_le_normalizer {F A' : Subgroup Γ}
    (hn : A' ≤ Subgroup.normalizer (F : Set Γ)) {a f : Γ} (ha : a ∈ A') (hf : f ∈ F) :
    a * f * a⁻¹ ∈ F :=
  (Subgroup.mem_normalizer_iff.mp (hn ha) f).mp hf

theorem mem_sup_iff_of_le_normalizer {F A' : Subgroup Γ}
    (hn : A' ≤ Subgroup.normalizer (F : Set Γ)) {x : Γ} :
    x ∈ F ⊔ A' ↔ ∃ f ∈ F, ∃ a ∈ A', x = f * a := by
  constructor
  · intro hx
    let S : Subgroup Γ :=
      { carrier := {x | ∃ f ∈ F, ∃ a ∈ A', x = f * a}
        one_mem' := ⟨1, F.one_mem, 1, A'.one_mem, by simp⟩
        mul_mem' := by
          rintro _ _ ⟨f₁, hf₁, a₁, ha₁, rfl⟩ ⟨f₂, hf₂, a₂, ha₂, rfl⟩
          exact ⟨f₁ * (a₁ * f₂ * a₁⁻¹), F.mul_mem hf₁ (conj_mem_of_le_normalizer hn ha₁ hf₂),
            a₁ * a₂, A'.mul_mem ha₁ ha₂, by group⟩
        inv_mem' := by
          rintro _ ⟨f, hf, a, ha, rfl⟩
          refine ⟨a⁻¹ * f⁻¹ * a, ?_, a⁻¹, A'.inv_mem ha, by group⟩
          have := conj_mem_of_le_normalizer hn (A'.inv_mem ha) (F.inv_mem hf)
          simpa using this }
    have hle : F ⊔ A' ≤ S :=
      sup_le (fun f hf => ⟨f, hf, 1, A'.one_mem, by simp⟩)
        (fun a ha => ⟨1, F.one_mem, a, ha, by simp⟩)
    exact hle hx
  · rintro ⟨f, hf, a, ha, rfl⟩
    exact (F ⊔ A').mul_mem (Subgroup.mem_sup_left hf) (Subgroup.mem_sup_right ha)

theorem conj_mem_sup_of_le_normalizer {F A' : Subgroup Γ}
    (hn : A' ≤ Subgroup.normalizer (F : Set Γ)) {h f : Γ} (hh : h ∈ F ⊔ A') (hf : f ∈ F) :
    h * f * h⁻¹ ∈ F := by
  obtain ⟨f', hf', a, ha, rfl⟩ := (mem_sup_iff_of_le_normalizer hn).1 hh
  have e : f' * a * f * (f' * a)⁻¹ = f' * (a * f * a⁻¹) * f'⁻¹ := by group
  rw [e]
  exact F.mul_mem (F.mul_mem hf' (conj_mem_of_le_normalizer hn ha hf)) (F.inv_mem hf')

theorem isSolvable_sup_of_le_normalizer {F A' : Subgroup Γ}
    (hn : A' ≤ Subgroup.normalizer (F : Set Γ)) [Group.IsSolvable ↥F]
    (hA : ∀ a ∈ A', ∀ b ∈ A', a * b = b * a) : Group.IsSolvable ↥(F ⊔ A') := by
  have hN : (F.subgroupOf (F ⊔ A')).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have := conj_mem_sup_of_le_normalizer hn g.2 hx
    simpa using this
  have hsolvN : Group.IsSolvable ↥(F.subgroupOf (F ⊔ A')) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe (le_sup_left : F ≤ F ⊔ A')).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe (le_sup_left : F ≤ F ⊔ A')).injective
  have hcomm : IsMulCommutative ↥(A'.subgroupOf (F ⊔ A')) :=
    ⟨⟨fun a b => Subtype.ext (Subtype.ext (hA a a.2 b b.2))⟩⟩
  have hsolvA : Group.IsSolvable ↥(A'.subgroupOf (F ⊔ A')) := inferInstance
  have hsurj : Function.Surjective
      ((QuotientGroup.mk' (F.subgroupOf (F ⊔ A'))).comp (A'.subgroupOf (F ⊔ A')).subtype) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨f, hf, a, ha, hx⟩ := (mem_sup_iff_of_le_normalizer hn).1 x.2
    refine ⟨⟨⟨a, Subgroup.mem_sup_right ha⟩, ha⟩, ?_⟩
    show (QuotientGroup.mk (⟨a, Subgroup.mem_sup_right ha⟩ : ↥(F ⊔ A')) :
      ↥(F ⊔ A') ⧸ F.subgroupOf (F ⊔ A')) = QuotientGroup.mk x
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h1 : (((⟨a, Subgroup.mem_sup_right ha⟩ : ↥(F ⊔ A'))⁻¹ * x : ↥(F ⊔ A')) : Γ) =
        a⁻¹ * f * a⁻¹⁻¹ := by
      show a⁻¹ * (x : Γ) = _
      rw [hx]
      group
    rw [h1]
    exact conj_mem_of_le_normalizer hn (A'.inv_mem ha) hf
  have hsolvQ : Group.IsSolvable (↥(F ⊔ A') ⧸ F.subgroupOf (F ⊔ A')) :=
    Group.isSolvable_of_surjective hsurj
  exact Group.isSolvable_of_ker_le_range (F.subgroupOf (F ⊔ A')).subtype
    (QuotientGroup.mk' (F.subgroupOf (F ⊔ A')))
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem eq_one_of_odd_orderOf_of_pow {x : Γ} (hx : Odd (orderOf x)) {k : ℕ} (h : x ^ 2 ^ k = 1) :
    x = 1 := by
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h
  have hcop : Nat.Coprime (orderOf x) (2 ^ k) :=
    ((Nat.coprime_two_left.2 hx).symm).pow_right k
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hcop h1)

theorem normal_two_subgroup_le {F A' Q : Subgroup Γ}
    (hn : A' ≤ Subgroup.normalizer (F : Set Γ)) (hF : ∀ x ∈ F, Odd (orderOf x))
    (hA : ∀ a ∈ A', a ^ 2 = 1) (hQ : Q ≤ F ⊔ A') (hQn : (Q.subgroupOf (F ⊔ A')).Normal)
    (hQ2 : ∀ q ∈ Q, ∃ k : ℕ, q ^ 2 ^ k = 1) :
    ∀ q ∈ Q, q ∈ A' ∧ ∀ f ∈ F, q * f = f * q := by
  have hQF : ∀ x ∈ Q, x ∈ F → x = 1 := by
    intro x hxQ hxF
    obtain ⟨k, hk⟩ := hQ2 x hxQ
    exact eq_one_of_odd_orderOf_of_pow (hF x hxF) hk
  have hQconj : ∀ g ∈ F ⊔ A', ∀ x ∈ Q, g * x * g⁻¹ ∈ Q := by
    intro g hg x hx
    have := hQn.conj_mem ⟨x, hQ hx⟩ (by rw [Subgroup.mem_subgroupOf]; exact hx) ⟨g, hg⟩
    simpa [Subgroup.mem_subgroupOf] using this
  have hcomm : ∀ q' ∈ Q, ∀ f' ∈ F, q' * f' = f' * q' := by
    intro q' hq' f' hf'
    have h1 : q' * (f' * q'⁻¹ * f'⁻¹) ∈ Q :=
      Q.mul_mem hq' (hQconj f' (Subgroup.mem_sup_left hf') q'⁻¹ (Q.inv_mem hq'))
    have h2 : q' * f' * q'⁻¹ * f'⁻¹ ∈ F :=
      F.mul_mem (conj_mem_sup_of_le_normalizer hn (hQ hq') hf') (F.inv_mem hf')
    have h3 : q' * f' * q'⁻¹ * f'⁻¹ = 1 := by
      have e : q' * f' * q'⁻¹ * f'⁻¹ = q' * (f' * q'⁻¹ * f'⁻¹) := by group
      exact hQF _ (by rw [e]; exact h1) h2
    have : q' * f' * q'⁻¹ * f'⁻¹ = 1 := h3
    calc q' * f' = (q' * f' * q'⁻¹ * f'⁻¹) * (f' * q') := by group
      _ = f' * q' := by rw [h3, one_mul]
  intro q hq
  obtain ⟨f, hf, a, ha, hqfa⟩ := (mem_sup_iff_of_le_normalizer hn).1 (hQ hq)
  have hcf : q * f = f * q := hcomm q hq f hf
  have hsq : q * q ∈ F := by
    have e : q * q = f * (a * f * a⁻¹) * (a * a) := by rw [hqfa]; group
    have hfa : a * a = 1 := by rw [← pow_two]; exact hA a ha
    rw [e, hfa, mul_one]
    exact F.mul_mem hf (conj_mem_of_le_normalizer hn ha hf)
  have hsq1 : q * q = 1 := hQF _ (Q.mul_mem hq hq) hsq
  have haf : a * f * a⁻¹ = f := by
    have e : f * (a * f) = f * (f * a) := by rw [← mul_assoc, ← hqfa]; exact hcf
    have e2 : a * f = f * a := mul_left_cancel e
    calc a * f * a⁻¹ = f * a * a⁻¹ := by rw [e2]
      _ = f := by group
  have hff : f * f = 1 := by
    have e : q * q = f * (a * f * a⁻¹) * (a * a) := by rw [hqfa]; group
    have hfa : a * a = 1 := by rw [← pow_two]; exact hA a ha
    rw [e, hfa, mul_one, haf] at hsq1
    exact hsq1
  have hf1 : f = 1 := eq_one_of_odd_orderOf_of_pow (hF f hf) (k := 1) (by rw [pow_one, pow_two]; exact hff)
  refine ⟨?_, hcomm q hq⟩
  rw [hqfa, hf1, one_mul]
  exact ha

end Product

end B19Aux

end CFSG.Quasithin
