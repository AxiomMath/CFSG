module

public import CFSG.Quasithin.H13.GoldschmidtQ8SqE9Sub

public section

namespace CFSG.Quasithin.H13.Q8SqE9

open QuaternionGroup Subgroup

variable {G : Type*} [Group G] {A B : Subgroup G}

theorem exists_pow_two_eq_of_odd {g : G} (h : Odd (orderOf g)) : ∃ k : ℕ, (g ^ 2) ^ k = g := by
  obtain ⟨r, hr⟩ := h
  refine ⟨r + 1, ?_⟩
  have h1 : g ^ orderOf g = 1 := pow_orderOf_eq_one g
  rw [← pow_mul, show 2 * (r + 1) = orderOf g + 1 by omega, pow_succ, h1, one_mul]

theorem commute_of_sq_commute {g m : G} (h : Odd (orderOf g)) (hc : (g ^ 2) * m = m * g ^ 2) :
    g * m = m * g := by
  obtain ⟨k, hk⟩ := exists_pow_two_eq_of_odd h
  rw [← hk]
  exact ((Commute.pow_left (show Commute (g ^ 2) m from hc) k).eq)

theorem commute_of_inv_or {g : G} (h : Odd (orderOf g)) {X : Subgroup G}
    (hax : ∀ m ∈ X, g * m * g⁻¹ = m ∨ g * m * g⁻¹ = m⁻¹) : ∀ m ∈ X, g * m = m * g := by
  intro m hm
  rcases hax m hm with h1 | h1
  · rwa [mul_inv_eq_iff_eq_mul] at h1
  · apply commute_of_sq_commute h
    have h2 : g * m = m⁻¹ * g := by rwa [mul_inv_eq_iff_eq_mul] at h1
    have h3 : g * m⁻¹ = m * g := by
      have : g * m⁻¹ * g⁻¹ = m := by
        calc g * m⁻¹ * g⁻¹ = (g * m * g⁻¹)⁻¹ := by group
          _ = m := by rw [h1, inv_inv]
      rwa [mul_inv_eq_iff_eq_mul] at this
    calc g ^ 2 * m = g * (g * m) := by rw [pow_two, mul_assoc]
      _ = g * (m⁻¹ * g) := by rw [h2]
      _ = (g * m⁻¹) * g := by group
      _ = (m * g) * g := by rw [h3]
      _ = m * g ^ 2 := by rw [pow_two, mul_assoc]

theorem mem_normalizer_of_map_eq {g : G} {X : Subgroup G}
    (hX : X.map (MulAut.conj g).toMonoidHom = X) : g ∈ normalizer (X : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have : (MulAut.conj g).toMonoidHom x ∈ X.map (MulAut.conj g).toMonoidHom := ⟨x, hx, rfl⟩
    rw [hX] at this
    simpa using this
  · intro hx
    rw [← hX] at hx
    obtain ⟨a, ha, hax⟩ := hx
    have : a = x := (MulAut.conj g).injective (by simpa using hax)
    exact this ▸ ha

namespace Cfg

theorem map_conj_eq (h : Cfg A B) {g : G} (hg : ∀ q ∈ A ⊔ B, g * q * g⁻¹ ∈ A ⊔ B) :
    A.map (MulAut.conj g).toMonoidHom = A ∨ A.map (MulAut.conj g).toMonoidHom = B := by
  refine h.eq_or_eq ?_ ((A.equivMapOfInjective _ (MulAut.conj g).injective).symm.trans
    h.eA.some)
  rintro _ ⟨a, ha, rfl⟩
  simpa using hg a (Subgroup.mem_sup_left ha)

theorem map_conj_cases (h : Cfg A B) {g : G} (hg : ∀ q ∈ A ⊔ B, g * q * g⁻¹ ∈ A ⊔ B) :
    (A.map (MulAut.conj g).toMonoidHom = A ∧ B.map (MulAut.conj g).toMonoidHom = B) ∨
      (A.map (MulAut.conj g).toMonoidHom = B ∧ B.map (MulAut.conj g).toMonoidHom = A) := by
  have hA := h.map_conj_eq hg
  have hB := h.symm.map_conj_eq (by rwa [sup_comm])
  have hne : A.map (MulAut.conj g).toMonoidHom ≠ B.map (MulAut.conj g).toMonoidHom :=
    fun he => h.ne (Subgroup.map_injective (MulAut.conj g).injective he)
  rcases hA with hA | hA <;> rcases hB with hB | hB
  · exact Or.inl ⟨hA, hB⟩
  · exact absurd (hA.trans hB.symm) hne
  · exact absurd (hA.trans hB.symm) hne
  · exact Or.inr ⟨hA, hB⟩

theorem mem_normalizers_of_odd (h : Cfg A B) {g : G}
    (hg : ∀ q ∈ A ⊔ B, g * q * g⁻¹ ∈ A ⊔ B) (hodd : Odd (orderOf g)) :
    g ∈ normalizer (A : Set G) ∧ g ∈ normalizer (B : Set G) := by
  rcases h.map_conj_cases hg with ⟨hA, hB⟩ | ⟨hA, hB⟩
  · exact ⟨mem_normalizer_of_map_eq hA, mem_normalizer_of_map_eq hB⟩
  · exfalso
    have hg2 : ∀ a ∈ A, g ^ 2 * a * (g ^ 2)⁻¹ ∈ A := by
      intro a ha
      have h1 : g * a * g⁻¹ ∈ B := by
        rw [← hA]; exact ⟨a, ha, by simp⟩
      have h2 : g * (g * a * g⁻¹) * g⁻¹ ∈ A := by
        rw [← hB]; exact ⟨_, h1, by simp⟩
      have : g ^ 2 * a * (g ^ 2)⁻¹ = g * (g * a * g⁻¹) * g⁻¹ := by
        rw [pow_two, mul_inv_rev]; group
      rwa [this]
    have hT : ∀ k : ℕ, ∀ a ∈ A, (g ^ 2) ^ k * a * ((g ^ 2) ^ k)⁻¹ ∈ A := by
      intro k
      induction k with
      | zero => intro a ha; simpa using ha
      | succ k ih =>
        intro a ha
        have : (g ^ 2) ^ (k + 1) * a * ((g ^ 2) ^ (k + 1))⁻¹ =
            (g ^ 2) ^ k * (g ^ 2 * a * (g ^ 2)⁻¹) * ((g ^ 2) ^ k)⁻¹ := by
          rw [pow_succ, mul_inv_rev]; group
        rw [this]
        exact ih _ (hg2 a ha)
    obtain ⟨k, hk⟩ := exists_pow_two_eq_of_odd hodd
    have hgA : ∀ a ∈ A, g * a * g⁻¹ ∈ A := by
      intro a ha
      have := hT k a ha
      rwa [hk] at this
    have hBA : B ≤ A := by
      intro x hx
      rw [← hA] at hx
      obtain ⟨a, ha, rfl⟩ := hx
      simpa using hgA a ha
    have := h.finite_A
    exact h.ne (Subgroup.eq_of_le_of_card_ge hBA (by rw [h.card_A, h.card_B])).symm

theorem inner_axis (h : Cfg A B) {a m : G} (ha : a ∈ A) (hm : m ∈ A) :
    a * m * a⁻¹ = m ∨ a * m * a⁻¹ = m⁻¹ := by
  obtain ⟨u, rfl⟩ := h.exists_phiA ha
  obtain ⟨w, rfl⟩ := h.exists_phiA hm
  have key : ∀ u w : Q8, u * w * u⁻¹ = w ∨ u * w * u⁻¹ = w⁻¹ := by decide +kernel
  rcases key u w with h1 | h1
  · left
    rw [← map_inv, ← map_mul, ← map_mul, h1]
  · right
    rw [← map_inv, ← map_mul, ← map_mul, h1, map_inv]

theorem conj_axis_Q (h : Cfg A B) {q m : G} (hq : q ∈ A ⊔ B) (hm : m ∈ A) :
    q * m * q⁻¹ = m ∨ q * m * q⁻¹ = m⁻¹ := by
  obtain ⟨⟨u, v⟩, rfl⟩ := (h.mem_sup_iff q).mp hq
  rw [pi_apply]
  simp only
  have h1 : h.phiB v * m * (h.phiB v)⁻¹ = m := by
    rw [mul_inv_eq_iff_eq_mul]
    exact Subgroup.mem_centralizer_iff.mp (h.comm hm) _ (h.phiB_mem v)
  have h2 : h.phiA u * h.phiB v * m * (h.phiA u * h.phiB v)⁻¹ =
      h.phiA u * m * (h.phiA u)⁻¹ := by
    calc _ = h.phiA u * (h.phiB v * m * (h.phiB v)⁻¹) * (h.phiA u)⁻¹ := by group
      _ = _ := by rw [h1]
  rw [h2]
  exact h.inner_axis (h.phiA_mem u) hm

end Cfg

end CFSG.Quasithin.H13.Q8SqE9
