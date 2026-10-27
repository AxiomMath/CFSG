module

public import CFSG.Fischer.Aut.Complete

public section

namespace CFSG.Timmesfeld.Bridge.Asc72

theorem subset_inner_of_coset_orders {L : Type*} [Group L] [Finite L]
    (hZ : Subgroup.center L = ⊥) (hnc : ∃ a b : L, a * b ≠ b * a)
    (P : Sylow 2 L) (hP : (P : Subgroup L) ≠ ⊥)
    (htrans : ∀ x ∈ (P : Subgroup L), x ≠ 1 → ∀ y ∈ (P : Subgroup L), y ≠ 1 →
      ∃ g ∈ Subgroup.normalizer ((P : Subgroup L) : Set L), g * x * g⁻¹ = y)
    (C : Set (MulAut L))
    (hinn : ∀ γ ∈ C, ∀ m : L, γ * MulAut.conj m ∈ C)
    (hord : ∀ γ ∈ C, orderOf γ ∣ 2 ∨ Odd (orderOf γ)) :
    ∀ γ ∈ C, γ ∈ (MulAut.conj : L →* MulAut L).range := by
  intro γ hγ
  by_contra hout
  have hinj := CFSG.Fischer.mulAutConj_injective hZ
  obtain ⟨a, haP, ha⟩ : ∃ a ∈ (P : Subgroup L), orderOf a = 2 := by
    have hdvd : 2 ∣ Nat.card (P : Subgroup L) :=
      P.isPGroup'.card_eq_or_dvd.resolve_left fun h => hP (Subgroup.card_eq_one.mp h)
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
    exact ⟨x, x.2, by rw [Subgroup.orderOf_coe, hx]⟩
  have ha1 : a ≠ 1 := by
    rintro rfl
    simp at ha
  obtain ⟨k, hk⟩ : ∃ k : L, k * γ a * k⁻¹ = a := by
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq L (γ • P) P
    have hmem : g * γ a * g⁻¹ ∈ ((g • γ • P : Sylow 2 L) : Subgroup L) := by
      rw [Sylow.smul_def, ← mul_smul, Sylow.pointwise_smul_def]
      convert Subgroup.smul_mem_pointwise_smul a (MulAut.conj g * γ) _ haP using 1
      simp [MulAut.smul_def, MulAut.mul_apply, MulAut.conj_apply]
    rw [hg] at hmem
    have hne : g * γ a * g⁻¹ ≠ 1 := by
      rwa [Ne, conj_eq_one_iff, map_eq_one_iff _ γ.injective]
    obtain ⟨h, -, hh⟩ := htrans _ hmem hne a haP ha1
    refine ⟨h * g, ?_⟩
    calc h * g * γ a * (h * g)⁻¹ = h * (g * γ a * g⁻¹) * h⁻¹ := by group
      _ = a := hh
  set δ : MulAut L := MulAut.conj k * γ with hδdef
  have hδ : δ ∈ C := by
    have h : δ = γ * MulAut.conj (γ⁻¹ k) := by
      ext x
      simp [δ, MulAut.conj_apply, MulAut.mul_apply]
    rw [h]
    exact hinn γ hγ _
  have hδout : δ ∉ (MulAut.conj : L →* MulAut L).range := by
    rintro ⟨j, hj⟩
    exact hout ⟨k⁻¹ * j, by rw [map_mul, hj, map_inv, hδdef, inv_mul_cancel_left]⟩
  have hδa : δ a = a := by
    simp [δ, MulAut.mul_apply, MulAut.conj_apply, hk]
  have hcomm : Commute δ (MulAut.conj a) := by
    ext x
    simp [MulAut.mul_apply, MulAut.conj_apply, hδa]
  have hoa : orderOf (MulAut.conj a) = 2 := by
    rw [orderOf_injective _ hinj, ha]
  rcases hord δ hδ with h2 | hodd
  ·
    have hδδ : ∀ y, δ (δ y) = y := fun y => by
      rw [← MulAut.mul_apply, ← pow_two, orderOf_dvd_iff_pow_eq_one.mp h2, MulAut.one_apply]
    have hinv : ∀ m : L, δ m = m⁻¹ := by
      intro m
      have hε : δ * MulAut.conj m ∈ C := hinn δ hδ m
      have hε2 : (δ * MulAut.conj m) ^ 2 = MulAut.conj (δ m * m) := by
        ext x
        simp [pow_two, MulAut.mul_apply, MulAut.conj_apply, hδδ, mul_assoc]
      rcases hord _ hε with h | h
      · have h1 : MulAut.conj (δ m * m) = MulAut.conj 1 := by
          rw [← hε2, orderOf_dvd_iff_pow_eq_one.mp h, map_one]
        exact eq_inv_of_mul_eq_one_left (hinj h1)
      ·
        exfalso
        obtain ⟨r, hr⟩ := h
        have hεr : δ * MulAut.conj m = ((δ * MulAut.conj m) ^ 2) ^ (r + 1) := by
          rw [← pow_mul, show 2 * (r + 1) = 2 * r + 1 + 1 by ring, pow_succ, ← hr,
            pow_orderOf_eq_one, one_mul]
        have hrange : δ * MulAut.conj m ∈ (MulAut.conj : L →* MulAut L).range := by
          rw [hεr, hε2]
          exact Subgroup.pow_mem _ (MonoidHom.mem_range.mpr ⟨_, rfl⟩) _
        apply hδout
        simpa using Subgroup.mul_mem _ hrange
          (Subgroup.inv_mem _ (MonoidHom.mem_range.mpr ⟨m, rfl⟩))
    obtain ⟨x, y, hxy⟩ := hnc
    have h := map_mul δ x⁻¹ y⁻¹
    simp only [hinv, inv_inv, mul_inv_rev] at h
    exact hxy h.symm
  ·
    have hδ1 : δ ≠ 1 := fun h => hδout ⟨1, by rw [map_one, h]⟩
    have hcop : (orderOf δ).Coprime (orderOf (MulAut.conj a)) := by
      rw [hoa]
      exact hodd.coprime_two_right
    have hprod := hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop
    rw [hoa] at hprod
    rcases hord _ (hinn δ hδ a) with h | h
    · rw [hprod] at h
      have hle := Nat.le_of_dvd two_pos h
      have hpos := hodd.pos
      exact hδ1 (orderOf_eq_one_iff.mp (by omega))
    · rw [hprod] at h
      exact absurd (Nat.odd_mul.mp h).2 (by decide)

end CFSG.Timmesfeld.Bridge.Asc72
