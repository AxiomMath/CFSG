module

public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec4.HeringK419

open CFSG.Open

@[expose] def HasTwoWitness {X : Type*} [Group X] (k : X) : Prop :=
  ∃ T : Subgroup X, IsPGroup 2 T ∧ (∀ t ∈ T, k * t * k⁻¹ ∈ T) ∧ ∃ t ∈ T, k * t * k⁻¹ ≠ t

theorem hasTwoWitness_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {k : X}
    (h : HasTwoWitness (e k)) : HasTwoWitness k := by
  obtain ⟨T, hT, hTn, t, htT, ht⟩ := h
  refine ⟨T.comap e.toMonoidHom, hT.comap_of_injective e.toMonoidHom e.injective, ?_,
    e.symm t, ?_, ?_⟩
  · intro x hx
    change e (k * x * k⁻¹) ∈ T
    rw [map_mul, map_mul, map_inv]
    exact hTn _ hx
  · change e (e.symm t) ∈ T
    rw [MulEquiv.apply_symm_apply]
    exact htT
  · intro h1
    apply ht
    have h2 := congrArg e h1
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply] at h2
    exact h2

theorem hasTwoWitness_of_charTwoLocal {X : Type*} [Group X] [Finite X] (H : Subgroup X)
    (hH : H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set X) ≤ pCoreOf 2 H) {k : X} (hkH : k ∈ H)
    (hk3 : k ^ 3 = 1) (hk1 : k ≠ 1) : HasTwoWitness k := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnorm : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set X) := by
    have : (pCore 2 H).Characteristic := CFSG.LieType.BorelTits.pCore_characteristic 2
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  refine ⟨pCoreOf 2 H, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H, fun t ht => ?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp (hnorm hkH) t).mp ht
  · by_contra hcon
    push Not at hcon
    have hkC : k ∈ Subgroup.centralizer (pCoreOf 2 H : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      have := hcon t ht
      calc t * k = k * t * k⁻¹ * k := by rw [this]
        _ = k * t := by group
    have hk2 : k ∈ pCoreOf 2 H := hH ⟨hkH, hkC⟩
    have hp : IsPGroup 2 (pCoreOf 2 H) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
    obtain ⟨m, hm⟩ := hp ⟨k, hk2⟩
    have hkm : k ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have hord3 : orderOf k = 3 := orderOf_eq_prime hk3 hk1
    have hdvd : orderOf k ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hkm
    rw [hord3] at hdvd
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow hdvd)
    omega

theorem hasTwoWitness_of_conj {X : Type*} [Group X] (g k₀ k : X) (hk : k = g * k₀ * g⁻¹)
    (h : HasTwoWitness k₀) : HasTwoWitness k := by
  subst hk
  refine hasTwoWitness_of_mulEquiv (MulAut.conj g⁻¹) ?_
  change HasTwoWitness (g⁻¹ * (g * k₀ * g⁻¹) * g⁻¹⁻¹)
  have : g⁻¹ * (g * k₀ * g⁻¹) * g⁻¹⁻¹ = k₀ := by group
  rw [this]
  exact h

theorem hasTwoWitness_of_selfCentralizing {X : Type*} [Group X] {C Q : Subgroup X}
    (hQ2 : IsPGroup 2 Q) (hnorm : ∀ g ∈ C, ∀ n ∈ Q, g * n * g⁻¹ ∈ Q)
    (hcen : ∀ g ∈ C, (∀ n ∈ Q, g * n = n * g) → g ∈ Q) {k : X} (hkC : k ∈ C)
    (hk3 : k ^ 3 = 1) (hk1 : k ≠ 1) : HasTwoWitness k := by
  refine ⟨Q, hQ2, fun t ht => hnorm k hkC t ht, ?_⟩
  by_contra hcon
  push Not at hcon
  have hkQ : k ∈ Q := hcen k hkC fun n hn => by
    have := hcon n hn
    calc k * n = k * n * k⁻¹ * k := by group
      _ = n * k := by rw [this]
  obtain ⟨m, hm⟩ := hQ2 ⟨k, hkQ⟩
  have hkm : k ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hord3 : orderOf k = 3 := orderOf_eq_prime hk3 hk1
  have hdvd : orderOf k ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hkm
  rw [hord3] at hdvd
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
    (Nat.prime_three.dvd_of_dvd_pow hdvd)
  omega

@[expose] def HasOuterWitness {X : Type*} [Group X] (β : MulAut X) : Prop :=
  ∃ T : Subgroup X, IsPGroup 2 T ∧ (∀ t ∈ T, β t ∈ T) ∧ ∃ t ∈ T, β t ≠ t

theorem hasOuterWitness_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    {β : MulAut X} (h : HasOuterWitness (MulAut.congr e β)) : HasOuterWitness β := by
  obtain ⟨T, hT, hTn, t, htT, ht⟩ := h
  have hβ : ∀ x, MulAut.congr e β (e x) = e (β x) := fun x => by
    change e (β (e.symm (e x))) = e (β x)
    rw [MulEquiv.symm_apply_apply]
  refine ⟨T.comap e.toMonoidHom, hT.comap_of_injective e.toMonoidHom e.injective, ?_,
    e.symm t, ?_, ?_⟩
  · intro x hx
    change e (β x) ∈ T
    rw [← hβ]
    exact hTn _ hx
  · change e (e.symm t) ∈ T
    rw [MulEquiv.apply_symm_apply]
    exact htT
  · intro h1
    apply ht
    have h2 := congrArg e h1
    rw [← hβ, MulEquiv.apply_symm_apply] at h2
    exact h2

theorem hasOuterWitness_of_conj {X : Type*} [Group X] (c β₀ β : MulAut X) (hβ : β = c * β₀ * c⁻¹)
    (h : HasOuterWitness β₀) : HasOuterWitness β := by
  obtain ⟨T, hT, hTn, t, htT, ht⟩ := h
  refine ⟨T.map c.toMonoidHom, hT.map _, ?_, c t, ⟨t, htT, rfl⟩, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨β₀ x, hTn x hx, ?_⟩
    subst hβ
    simp [MulAut.mul_apply]
  · subst hβ
    intro h1
    apply ht
    have h2 : c (β₀ t) = c t := by
      simpa [MulAut.mul_apply] using h1
    exact c.injective h2

end CFSG.RankThree.PartTwo.Sec4.HeringK419
