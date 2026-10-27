module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.Quasithin.SzI47J2C

theorem exists_odd_pow_eq_one_normalizer_not_comm {G : Type*} [Group G] [Finite G]
    {R : Subgroup G} {t : G} (htR : t ∈ R) (ht1 : t ≠ 1) (hcard : Nat.card R = 4)
    (htrans : ∀ r ∈ R, r ≠ 1 → ∃ g ∈ Subgroup.normalizer (R : Set G), g * t * g⁻¹ = r) :
    ∃ y ∈ Subgroup.normalizer (R : Set G), ∃ n : ℕ, Odd n ∧ y ^ n = 1 ∧ y * t * y⁻¹ ≠ t := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set t' : ↥R := ⟨t, htR⟩ with ht'
  have hsmul : ∀ (g : ↥(Subgroup.normalizer (R : Set G))) (x : ↥R),
      (((g • x : ↥R)) : G) = (g : G) * x * (g : G)⁻¹ := fun g x => rfl
  have horbit : MulAction.orbit ↥(Subgroup.normalizer (R : Set G)) t' = ({1} : Set ↥R)ᶜ := by
    ext x
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨g, rfl⟩ h1
      have h2 : (g : G) * t * (g : G)⁻¹ = 1 := by
        have := congrArg Subtype.val (Set.mem_singleton_iff.mp h1)
        rwa [hsmul] at this
      exact ht1 (by
        calc t = (g : G)⁻¹ * ((g : G) * t * (g : G)⁻¹) * g := by group
          _ = 1 := by rw [h2]; group)
    · intro hx
      obtain ⟨g, hg, hgt⟩ := htrans x x.2 (fun h => hx (Subtype.ext h))
      exact ⟨⟨g, hg⟩, Subtype.ext hgt⟩
  have hindex : (MulAction.stabilizer ↥(Subgroup.normalizer (R : Set G)) t').index = 3 := by
    rw [MulAction.index_stabilizer, horbit, Set.ncard_compl, Set.ncard_singleton, hcard]
  obtain ⟨P⟩ : Nonempty (Sylow 3 ↥(Subgroup.normalizer (R : Set G))) := inferInstance
  have hnle : ¬ (P : Subgroup ↥(Subgroup.normalizer (R : Set G))) ≤
      MulAction.stabilizer ↥(Subgroup.normalizer (R : Set G)) t' := by
    intro hle
    have h1 := Subgroup.index_dvd_of_le hle
    rw [hindex] at h1
    exact P.not_dvd_index h1
  obtain ⟨p, hpP, hpS⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp P.isPGroup' ⟨p, hpP⟩
  have hord : orderOf p = 3 ^ k := by
    rw [← hk]
    exact Subgroup.orderOf_coe (⟨p, hpP⟩ : ↥(P : Subgroup _))
  refine ⟨(p : G), p.2, 3 ^ k, Odd.pow (by decide), ?_, ?_⟩
  · have h1 : p ^ (3 ^ k) = 1 := by rw [← hord]; exact pow_orderOf_eq_one p
    have h2 := congrArg Subtype.val h1
    simpa using h2
  · intro h
    apply hpS
    rw [MulAction.mem_stabilizer_iff]
    apply Subtype.ext
    rw [hsmul]
    exact h

end CFSG.Quasithin.SzI47J2C
