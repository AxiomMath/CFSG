module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.Quasithin.SzN17

variable {Ω : Type*} [Group Ω]

@[expose] def IsNormalThree (H Q : Subgroup Ω) : Prop :=
  Q ≤ H ∧ (∀ h ∈ H, ∀ q ∈ Q, h * q * h⁻¹ ∈ Q) ∧ Nat.card Q = 3

@[expose] def Fixed3 (H Z : Subgroup Ω) : Prop :=
  ∀ g : Ω, g ^ 3 = 1 → (∀ x, x ∈ H ↔ g * x * g⁻¹ ∈ H) → ∀ z ∈ Z, g * z * g⁻¹ = z

theorem ne_inv_of_orderOf_three {e : Ω} (he : orderOf e = 3) : e ≠ e⁻¹ := by
  intro h
  have h2 : e ^ 2 = 1 := by
    rw [pow_two]
    calc e * e = e * e⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel e
  have := orderOf_dvd_of_pow_eq_one h2
  rw [he] at this
  norm_num at this

theorem zpow_cases_of_orderOf_three {e y : Ω} (he : orderOf e = 3) (hy : y ∈ Subgroup.zpowers e) :
    y = 1 ∨ y = e ∨ y = e⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hmod : e ^ (k % 3) = e ^ k := by simpa [he] using zpow_mod_orderOf e k
  rw [← hmod]
  have hk : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hk with h | h | h <;> rw [h]
  · left; simp
  · right; left; simp
  · right; right
    apply eq_inv_of_mul_eq_one_left
    rw [← zpow_add_one]
    have h3 : e ^ 3 = 1 := he ▸ pow_orderOf_eq_one e
    exact_mod_cast h3

theorem eq_zpowers_of_card_three {Q : Subgroup Ω} (hQ : Nat.card Q = 3) {z : Ω} (hz : z ∈ Q)
    (hz1 : z ≠ 1) : orderOf z = 3 ∧ Q = Subgroup.zpowers z := by
  have hfin : Finite ↥Q := Nat.finite_of_card_ne_zero (by rw [hQ]; norm_num)
  have h1 : orderOf (⟨z, hz⟩ : ↥Q) ∣ Nat.card ↥Q := orderOf_dvd_natCard _
  rw [hQ, Subgroup.orderOf_mk] at h1
  have hz3 : orderOf z = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 h1 with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hz1
    · exact h
  refine ⟨hz3, ?_⟩
  have hle : Subgroup.zpowers z ≤ Q := Subgroup.zpowers_le.2 hz
  have hcard : Nat.card (Subgroup.zpowers z) = 3 := by rw [Nat.card_zpowers, hz3]
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hQ, hcard])).symm

theorem card_three_cases {Q : Subgroup Ω} (hQ : Nat.card Q = 3) {z : Ω} (hz : z ∈ Q) (hz1 : z ≠ 1) :
    orderOf z = 3 ∧ ∀ w ∈ Q, w = 1 ∨ w = z ∨ w = z⁻¹ := by
  obtain ⟨hz3, heq⟩ := eq_zpowers_of_card_three hQ hz hz1
  exact ⟨hz3, fun w hw => zpow_cases_of_orderOf_three hz3 (heq ▸ hw)⟩

theorem exists_ne_one_of_card_three {Q : Subgroup Ω} (hQ : Nat.card Q = 3) : ∃ z ∈ Q, z ≠ 1 := by
  by_contra h
  push Not at h
  have : Q = ⊥ := (Subgroup.eq_bot_iff_forall Q).2 h
  rw [this, Subgroup.card_bot] at hQ
  omega

theorem conj_eq_of_cube {g : Ω} {Q : Subgroup Ω} (hQ : Nat.card Q = 3) (hg3 : g ^ 3 = 1)
    (hgQ : ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) {z : Ω} (hz : z ∈ Q) : g * z * g⁻¹ = z := by
  by_cases hz1 : z = 1
  · subst hz1; simp
  · obtain ⟨hz3, hcases⟩ := card_three_cases hQ hz hz1
    have hw : g * z * g⁻¹ ∈ Q := hgQ z hz
    have hw1 : g * z * g⁻¹ ≠ 1 := by
      intro h
      apply hz1
      have : z = g⁻¹ * (g * z * g⁻¹) * g := by group
      rw [this, h]
      group
    rcases hcases _ hw with h | h | h
    · exact absurd h hw1
    · exact h
    · exfalso
      have h2 : g * z⁻¹ * g⁻¹ = z := by
        have : g * z⁻¹ * g⁻¹ = (g * z * g⁻¹)⁻¹ := by group
        rw [this, h, inv_inv]
      have h3 : g * (g * (g * z * g⁻¹) * g⁻¹) * g⁻¹ = z⁻¹ := by
        rw [h, h2, h]
      have h4 : g * (g * (g * z * g⁻¹) * g⁻¹) * g⁻¹ = z := by
        calc g * (g * (g * z * g⁻¹) * g⁻¹) * g⁻¹ = (g * g * g) * z * (g * g * g)⁻¹ := by group
          _ = z := by rw [← pow_three', hg3]; group
      exact ne_inv_of_orderOf_three hz3 (h4.symm.trans h3)

theorem map_conj_three {K : Subgroup Ω} {g : Ω} (hg3 : g ^ 3 = 1) :
    ((K.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj g).toMonoidHom = K := by
  simp only [Subgroup.map_map]
  have hggg : g * (g * g) = 1 := by rw [← pow_three]; exact hg3
  have : ((MulAut.conj g).toMonoidHom.comp
      ((MulAut.conj g).toMonoidHom.comp (MulAut.conj g).toMonoidHom)) = MonoidHom.id Ω := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.id_apply]
    calc g * (g * (g * x * g⁻¹) * g⁻¹) * g⁻¹ = (g * (g * g)) * x * (g * (g * g))⁻¹ := by group
      _ = x := by rw [hggg]; simp
  rw [this, Subgroup.map_id]

theorem isNormalThree_map_conj {H Q : Subgroup Ω} {g : Ω} (hgH : ∀ x, x ∈ H ↔ g * x * g⁻¹ ∈ H)
    (hQ : IsNormalThree H Q) : IsNormalThree H (Q.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨hQH, hQn, hQc⟩ := hQ
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact (hgH y).1 (hQH hy)
  · rintro h hh _ ⟨y, hy, rfl⟩
    have hh' : g⁻¹ * h * g ∈ H := by
      refine (hgH (g⁻¹ * h * g)).2 ?_
      have e : g * (g⁻¹ * h * g) * g⁻¹ = h := by group
      rw [e]
      exact hh
    refine ⟨(g⁻¹ * h * g) * y * (g⁻¹ * h * g)⁻¹, hQn _ hh' y hy, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hQc

theorem fixed3_of_unique {H Z₁ Z₂ : Subgroup Ω}
    (hΞ : ∀ Q : Subgroup Ω, IsNormalThree H Q → Q = Z₁ ∨ Q = Z₂) {Q : Subgroup Ω}
    (hQ : IsNormalThree H Q) : Fixed3 H Q := by
  intro g hg3 hgH z hz
  set c : Subgroup Ω → Subgroup Ω := fun R => R.map (MulAut.conj g).toMonoidHom with hc
  have hinj : Function.Injective c := Subgroup.map_injective (MulAut.conj g).injective
  have h1 : IsNormalThree H (c Q) := isNormalThree_map_conj hgH hQ
  have h2 : IsNormalThree H (c (c Q)) := isNormalThree_map_conj hgH h1
  have h3 : c (c (c Q)) = Q := map_conj_three hg3
  have key : Q = c Q ∨ Q = c (c Q) ∨ c Q = c (c Q) := by
    rcases hΞ Q hQ with e1 | e1 <;> rcases hΞ (c Q) h1 with e2 | e2 <;>
      rcases hΞ (c (c Q)) h2 with e3 | e3 <;>
      first
        | exact Or.inl (e1.trans e2.symm)
        | exact Or.inr (Or.inl (e1.trans e3.symm))
        | exact Or.inr (Or.inr (e2.trans e3.symm))
  have hcQ : c Q = Q := by
    rcases key with h | h | h
    · exact h.symm
    · have : c Q = c (c (c Q)) := congrArg c h
      rw [h3] at this
      exact this
    · exact (hinj h).symm
  refine conj_eq_of_cube hQ.2.2 hg3 (fun q hq => ?_) hz
  have : g * q * g⁻¹ ∈ c Q := ⟨q, hq, rfl⟩
  rwa [hcQ] at this

theorem perm_center_trivial {α : Type*} [DecidableEq α] [Fintype α] (h3 : 3 ≤ Fintype.card α)
    (z : Equiv.Perm α) (hz : ∀ g : Equiv.Perm α, g * z = z * g) : z = 1 := by
  by_contra hne
  obtain ⟨a, ha⟩ : ∃ a, z a ≠ a := by
    by_contra h
    push Not at h
    exact hne (Equiv.ext h)
  have hc : ∃ c, c ≠ a ∧ c ≠ z a := by
    by_contra h
    push Not at h
    have hsub : (Finset.univ : Finset α) ⊆ {a, z a} := fun x _ => by
      by_cases hx : x = a
      · simp [hx]
      · simp [h x hx]
    have h1 := Finset.card_le_card hsub
    have h2 : ({a, z a} : Finset α).card ≤ 2 := Finset.card_le_two
    simp only [Finset.card_univ] at h1
    omega
  obtain ⟨c, hca, hcz⟩ := hc
  have h : (Equiv.swap a c * z) a = (z * Equiv.swap a c) a := by rw [hz]
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left] at h
  rw [Equiv.swap_apply_of_ne_of_ne ha (Ne.symm hcz)] at h
  exact hca (z.injective h).symm

end CFSG.Quasithin.SzN17
