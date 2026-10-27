module

public import CFSG.RankThree.GF2n.Stroth80.Sec37Inputs

public section

namespace CFSG.RankThree.GF2n.Stroth80

namespace Mod37

theorem exists_fixed_vector_of_isPGroup {K V : Type*} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [Finite V] (Λ : Subgroup (V ≃ₗ[K] V)) (hΛ : IsPGroup 2 Λ)
    (S : Submodule K V) (hS : ∀ T ∈ Λ, ∀ v ∈ S, T v ∈ S) (hS0 : S ≠ ⊥) :
    ∃ v ∈ S, v ≠ 0 ∧ ∀ T ∈ Λ, T v = v := by
  letI : MulAction Λ S :=
    { smul := fun T v => ⟨T.1 v.1, hS T.1 T.2 v.1 v.2⟩
      one_smul := fun v => Subtype.ext rfl
      mul_smul := fun a b v => Subtype.ext rfl }
  have h2S : 2 ∣ Nat.card S := by
    haveI : Module.Finite K S := Module.Finite.of_finite
    rw [Module.natCard_eq_pow_finrank (K := K) (V := S)]
    have hK : 2 ∣ Nat.card K := by
      haveI := Fintype.ofFinite K
      rw [Nat.card_eq_fintype_card]
      exact (CharP.cast_eq_zero_iff K 2 _).mp (FiniteField.cast_card_eq_zero K)
    exact dvd_pow hK (by rwa [Ne, Submodule.finrank_eq_zero])
  obtain ⟨v, hv, hv0⟩ := hΛ.exists_fixed_point_of_prime_dvd_card_of_fixed_point S h2S
    (a := 0) (MulAction.mem_fixedPoints.mpr fun T => Subtype.ext (map_zero T.1))
  refine ⟨v.1, v.2, fun h => hv0 (Subtype.ext h.symm), fun T hT => ?_⟩
  exact congrArg Subtype.val (MulAction.mem_fixedPoints.mp hv ⟨T, hT⟩)

theorem two_mul_add_three_le_two_pow {m : ℕ} (hm : 4 ≤ m) : 2 * m + 3 ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    rw [pow_succ]
    omega

theorem eq_four_of_two_mul_eq_two_pow {n x : ℕ} (hn : 2 < n) (h : 2 * n = 2 ^ (x * (n - 1))) :
    n = 4 := by
  obtain ⟨m, hm⟩ : ∃ m, m = x * (n - 1) := ⟨_, rfl⟩
  rw [← hm] at h
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · rw [zero_mul] at hm
    rw [hm, pow_zero] at h
    omega
  have hnm : n - 1 ≤ m := hm ▸ Nat.le_mul_of_pos_left (n - 1) hx
  have hm3 : m ≤ 3 := by
    by_contra hm3
    have := two_mul_add_three_le_two_pow (m := m) (by omega)
    omega
  rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3) with rfl | rfl | rfl | rfl <;>
    norm_num at h <;> omega

end Mod37

theorem module37 : Module37Statement := by
  intro hSL2 k n hk hn E _ _ _ hdim L hLiso b hb0 hspan Λ hΛL hΛcard hΛb hfix
  obtain ⟨φ⟩ := hLiso
  haveI : Finite E := Module.finite_of_finite (GaloisField 2 k)
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (k * (n - 1))) →*
      (E ≃ₗ[GaloisField 2 k] E), ∀ ℓ (hℓ : ℓ ∈ L), ρ (φ ⟨ℓ, hℓ⟩) = ℓ :=
    ⟨L.subtype.comp φ.symm.toMonoidHom, fun ℓ hℓ => by simp⟩
  have hΛp : IsPGroup 2 Λ := IsPGroup.of_card hΛcard
  have hirr : ∀ W : Submodule (GaloisField 2 k) E, (∀ g, ∀ v ∈ W, ρ g v ∈ W) →
      W = ⊥ ∨ W = ⊤ := by
    intro W hW
    have hWL : ∀ ℓ ∈ L, ∀ v ∈ W, ℓ v ∈ W := fun ℓ hℓ v hv => by
      simpa only [hρ] using hW (φ ⟨ℓ, hℓ⟩) v hv
    by_cases hW0 : W = ⊥
    · exact Or.inl hW0
    refine Or.inr ?_
    obtain ⟨w, hwW, hw0, hwfix⟩ :=
      Mod37.exists_fixed_vector_of_isPGroup Λ hΛp W (fun t ht => hWL t (hΛL ht)) hW0
    obtain ⟨s, rfl⟩ := hfix w hwfix
    have hs : s ≠ 0 := by
      rintro rfl
      exact hw0 (zero_smul _ _)
    have hbW : b ∈ W := by
      have h1 := W.smul_mem s⁻¹ hwW
      rwa [smul_smul, inv_mul_cancel₀ hs, one_smul] at h1
    rw [eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨ℓ, rfl⟩
    exact hWL ℓ ℓ.2 b hbW
  let P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (k * (n - 1)))) :=
    (Λ.subgroupOf L).map φ.toMonoidHom
  have hPcard : Nat.card P = 2 ^ (k * (n - 1)) := by
    rw [Subgroup.card_map_of_injective φ.injective, ← hΛcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hΛL).toEquiv
  have hPΛ : ∀ g ∈ P, ρ g ∈ Λ := by
    intro g hg
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg
    rw [MulEquiv.coe_toMonoidHom, hρ x.1 x.2]
    exact Subgroup.mem_subgroupOf.mp hx
  have hΛP : ∀ t (ht : t ∈ Λ), φ ⟨t, hΛL ht⟩ ∈ P := fun t ht =>
    Subgroup.mem_map.mpr ⟨⟨t, hΛL ht⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
  obtain ⟨x, hx⟩ := hSL2 k (n - 1) hk (by omega) E ρ hirr P (IsPGroup.of_card hPcard) hPcard
    ⟨b, hb0, fun g hg => hΛb _ (hPΛ g hg), fun v hv => hfix v fun t ht => by
      simpa only [hρ] using hv _ (hΛP t ht)⟩
  rw [hdim] at hx
  exact Mod37.eq_four_of_two_mul_eq_two_pow hn hx

end CFSG.RankThree.GF2n.Stroth80
