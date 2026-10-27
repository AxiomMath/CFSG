module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5110Gen

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13

namespace E2.BorelLift

variable {Γ : Type} [Group Γ] [Finite Γ] {H T M K : Subgroup Γ}

theorem sylow_star (hTH : IsSylowTwoOf T H) (hK : K ∈ cComp H) :
    IsSylowTwoOf (E2.star M H (T ⊓ K)) (E2.star M H K) := by
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hsK : IsSylowTwoOf (T ⊓ K) K :=
    A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hK) hTH
  have h := Setup.Family.isSylowTwoOf_map_range
    ((starPi M H).comp (Subgroup.inclusion hKH)) hsK
  rwa [map_comp_inclusion_eq_star hKH inf_le_right, range_comp_inclusion_eq_star hKH] at h

theorem borel_eq (hTH : IsSylowTwoOf T H) (hTM : T ≤ M) (hK : K ∈ cComp H)
    (hB : E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K))) :
    E2.star M H (M ⊓ K) = E2.star M H K ⊓
      Subgroup.normalizer ((E2.star M H (T ⊓ K) : Subgroup (E2.StarQuot M H)) :
        Set (E2.StarQuot M H)) := by
  obtain ⟨S', hS', hBeq⟩ := hB
  have hTs := sylow_star (M := M) hTH hK
  have hTMs : E2.star M H (T ⊓ K) ≤ E2.star M H (M ⊓ K) :=
    Subgroup.map_mono fun x hx => (inf_le_inf_right K hTM : T ⊓ K ≤ _) hx
  have hTN : E2.star M H (T ⊓ K) ≤ Subgroup.normalizer (S' : Set _) :=
    hTMs.trans (hBeq ▸ inf_le_right)
  have h2 := IsPGroup.to_sup_of_normal_right' hTs.2.1 hS'.2.1 hTN
  have heq := hS'.eq_of_le le_sup_right (sup_le hTs.1 hS'.1) h2
  have hTS : E2.star M H (T ⊓ K) ≤ S' := heq ▸ le_sup_left
  have hS'eq := hTs.eq_of_le hTS hS'.1 hS'.2.1
  rw [hBeq, hS'eq]

theorem mem_normalizer_of_starPi (hTH : IsSylowTwoOf T H) (hK : K ∈ cComp H)
    (hJK : ∀ j ∈ K, j ∈ kerIn M H → ∀ x ∈ T ⊓ K, j * x * j⁻¹ ∈ T ⊓ K)
    {m : Γ} (hmK : m ∈ K)
    (hmN : starPi M H ⟨m, le_of_mem_cComp hK hmK⟩ ∈ Subgroup.normalizer
      ((E2.star M H (T ⊓ K) : Subgroup (E2.StarQuot M H)) : Set (E2.StarQuot M H))) :
    m ∈ Subgroup.normalizer ((T ⊓ K : Subgroup Γ) : Set Γ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hsK : IsSylowTwoOf (T ⊓ K) K :=
    A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hK) hTH
  have hJN : ∀ j ∈ K, j ∈ kerIn M H →
      j ∈ Subgroup.normalizer ((T ⊓ K : Subgroup Γ) : Set Γ) := by
    intro j hjK hjJ
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hJK j hjK hjJ x, fun hx => ?_⟩
    have h1 := hJK j⁻¹ (K.inv_mem hjK) ((kerIn M H).inv_mem hjJ) _ hx
    simpa [mul_assoc] using h1
  have hconj : ∀ x ∈ T ⊓ K, ∃ y ∈ T ⊓ K, y⁻¹ * (m * x * m⁻¹) ∈ kerIn M H := by
    intro x hx
    have hxH : x ∈ H := hKH hx.2
    have hx' : starPi M H ⟨x, hxH⟩ ∈ E2.star M H (T ⊓ K) := starPi_mem_star hx
    have h1 := (Subgroup.mem_normalizer_iff.mp hmN _).mp hx'
    rw [← map_mul, ← map_inv, ← map_mul] at h1
    obtain ⟨y, hy, hyx⟩ := mem_star510_iff.mp h1
    refine ⟨y, hy, ?_⟩
    have h2 := starPi_eq_iff.mp hyx
    simpa using h2
  set P := (T ⊓ K).map (MulAut.conj m).toMonoidHom with hP
  have hPK : P ≤ K := by
    rintro _ ⟨x, hx, rfl⟩
    exact K.mul_mem (K.mul_mem hmK hx.2) (K.inv_mem hmK)
  have hP2 : IsPGroup 2 P := hsK.2.1.map _
  have hPN : P ≤ Subgroup.normalizer ((T ⊓ K : Subgroup Γ) : Set Γ) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyJ⟩ := hconj x hx
    have hc : (MulAut.conj m).toMonoidHom x = m * x * m⁻¹ := rfl
    rw [hc]
    have hyK : y⁻¹ * (m * x * m⁻¹) ∈ K :=
      K.mul_mem (K.inv_mem hy.2) (K.mul_mem (K.mul_mem hmK hx.2) (K.inv_mem hmK))
    have h1 := hJN _ hyK hyJ
    have h2 : y ∈ Subgroup.normalizer ((T ⊓ K : Subgroup Γ) : Set Γ) := Subgroup.le_normalizer hy
    have := Subgroup.mul_mem _ h2 h1
    simpa using this
  have h2 := IsPGroup.to_sup_of_normal_right' hP2 hsK.2.1 hPN
  have heq := hsK.eq_of_le le_sup_right (sup_le hPK hsK.1) h2
  have hPle : P ≤ T ⊓ K := heq ▸ le_sup_left
  have hPeq : P = T ⊓ K := by
    refine Subgroup.eq_of_le_of_card_ge hPle ?_
    rw [hP, Subgroup.card_map_of_injective (MulAut.conj m).injective]
  exact A38.map_conj_eq_iff.mp hPeq

theorem inf_eq_normalizer (hTH : IsSylowTwoOf T H) (hTM : T ≤ M) (hK : K ∈ cComp H)
    (hB : E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K)))
    (hJK : ∀ j ∈ K, j ∈ kerIn M H → ∀ x ∈ T ⊓ K, j * x * j⁻¹ ∈ T ⊓ K) :
    M ⊓ K = K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup Γ) : Set Γ) := by
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hbeq := borel_eq hTH hTM hK hB
  apply le_antisymm
  · intro m hm
    have hm' : starPi M H ⟨m, hKH hm.2⟩ ∈ E2.star M H (M ⊓ K) := starPi_mem_star hm
    rw [hbeq] at hm'
    exact ⟨hm.2, mem_normalizer_of_starPi hTH hK hJK hm.2 hm'.2⟩
  · rintro m ⟨hmK, hmN⟩
    have hmN' := starPi_mem_normalizer (M' := M) (h := ⟨m, hKH hmK⟩) hmN
    have hm' : starPi M H ⟨m, hKH hmK⟩ ∈ E2.star M H (M ⊓ K) := by
      rw [hbeq]
      exact ⟨starPi_mem_star hmK, hmN'⟩
    obtain ⟨x, hx, hxm⟩ := mem_star510_iff.mp hm'
    have h1 := kerIn_le (starPi_eq_iff.mp hxm)
    have h2 : (x : Γ) * ((x : Γ)⁻¹ * m) ∈ M := M.mul_mem hx.1 h1
    refine ⟨?_, hmK⟩
    simpa using h2

end E2.BorelLift

end CFSG.Quasithin
