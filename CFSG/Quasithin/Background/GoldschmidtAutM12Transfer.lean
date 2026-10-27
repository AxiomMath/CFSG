module

public import CFSG.Quasithin.Background.GoldschmidtAutM12Tab

public section

namespace CFSG.Quasithin.F6

namespace AutM12Recog

namespace Tab

theorem hasTwoE16_of_mulEquiv {A B : Type} [Group A] [Finite A] [Group B]
    (hB : ∀ Q' : Sylow 2 B, HasTwoE16 ↥(Q' : Subgroup B)) (Q : Sylow 2 A) (ψ : A ≃* B) :
    HasTwoE16 ↥(Q : Subgroup A) := by
  obtain ⟨Q', ⟨ι⟩⟩ := exists_sylow_mulEquiv ψ Q
  exact (hB Q').of_mulEquiv ι.symm

theorem hasTwoE16_of_equiv {Q Q' : Type} [Group Q] (h : HasTwoE16 Q) [Group Q'] (e : Q ≃* Q') :
    HasTwoE16 Q' :=
  HasTwoE16.of_mulEquiv e h

theorem hasTwoE16_of_sylow {G : Type} [Group G] [Finite G] (Q₀ : Sylow 2 G)
    (h : HasTwoE16 ↥(Q₀ : Subgroup G)) (Q : Sylow 2 G) : HasTwoE16 ↥(Q : Subgroup G) :=
  hasTwoE16_of_equiv h (Sylow.equiv Q₀ Q)

theorem hasTwoE16_of_surjective {G G' : Type} [Group G] [Finite G] [Group G'] (π : G →* G')
    (hπ : Function.Surjective π) (hker : ∀ z : G, π z = 1 → z ^ 3 = 1)
    (h : ∀ P : Sylow 2 G, HasTwoE16 ↥(P : Subgroup G)) (Q : Sylow 2 G') :
    HasTwoE16 ↥(Q : Subgroup G') := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite G' := Finite.of_surjective π hπ
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 G))
  have hinj : Function.Injective (π.comp (P : Subgroup G).subtype) := by
    rw [injective_iff_map_eq_one]
    intro t ht
    have h3 : (t : G) ^ 3 = 1 := hker _ ht
    obtain ⟨j, hj⟩ := P.isPGroup' t
    have h2 : (t : G) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have h1 : orderOf (t : G) ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one h2
    have h1' : orderOf (t : G) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    have hcop : Nat.Coprime (2 ^ j) 3 := Nat.Coprime.pow_left _ (by norm_num)
    have : orderOf (t : G) = 1 := Nat.eq_one_of_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd h1 h1')
    exact Subtype.ext (orderOf_eq_one_iff.mp this)
  have hrange : (π.comp (P : Subgroup G).subtype).range = (P : Subgroup G).map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let Q₀ : Sylow 2 G' := P.mapSurjective (f := π) hπ
  have hQ₀ : (Q₀ : Subgroup G') = (P : Subgroup G).map π := Sylow.coe_mapSurjective _ _
  let e : ↥(P : Subgroup G) ≃* ↥(Q₀ : Subgroup G') :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr (hrange.trans hQ₀.symm))
  exact hasTwoE16_of_sylow Q₀ (hasTwoE16_of_equiv (h P) e) Q

end Tab

end AutM12Recog

end CFSG.Quasithin.F6
