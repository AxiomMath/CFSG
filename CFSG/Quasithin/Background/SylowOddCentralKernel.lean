module

public import CFSG.Quasithin.Background.Basic
public import CFSG.Quasithin.Background.OddCentralKerSylowTI
public import CFSG.RankThree.OddKernel.OddLift

public section

namespace CFSG.Quasithin

variable {G X : Type*} [Group G] [Finite G] [Group X] [Finite X]

theorem omegaOneOf_map_of_odd_ker (φ : G →* X) (hodd : Odd (Nat.card φ.ker))
    {T : Subgroup G} (hT : IsPGroup 2 T) :
    (omegaOneOf T).map φ = omegaOneOf (T.map φ) := by
  rw [omegaOneOf, omegaOneOf, MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨hxT, hx2⟩, rfl⟩
    exact ⟨⟨x, hxT, rfl⟩, by rw [← map_pow, hx2, map_one]⟩
  · rintro ⟨⟨x, hxT, rfl⟩, hx2⟩
    refine ⟨x, ⟨hxT, ?_⟩, rfl⟩
    have hx2' : φ (x ^ 2) = φ 1 := by
      rw [map_pow, hx2, map_one]
    have h := CFSG.RankThree.OddKernel.injective_restrict_of_odd φ hodd hT
      (a₁ := ⟨x ^ 2, T.pow_mem hxT 2⟩) (a₂ := 1) (by simpa using hx2')
    simpa using congrArg Subtype.val h

theorem sylow_mapSurjective_bijective_of_odd_central_ker (φ : G →* X)
    (hφ : Function.Surjective φ) (hcen : φ.ker ≤ Subgroup.center G)
    (hodd : Odd (Nat.card φ.ker)) :
    Function.Bijective (fun T : Sylow 2 G => Sylow.mapSurjective hφ T) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨?_, Sylow.mapSurjective_surjective hφ 2⟩
  intro T T' hTT'
  have hmap : (T : Subgroup G).map φ = (T' : Subgroup G).map φ := by
    have h := congrArg (fun S : Sylow 2 X => (S : Subgroup X)) hTT'
    rwa [Sylow.coe_mapSurjective (f := φ) hφ T,
      Sylow.coe_mapSurjective (f := φ) hφ T'] at h
  apply Sylow.ext
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · intro x hx
    have hxmap : φ x ∈ (T' : Subgroup G).map φ := hmap ▸ Subgroup.mem_map_of_mem φ hx
    obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp hxmap
    set k : G := y⁻¹ * x with hk
    have hmem : k ∈ φ.ker := by
      rw [MonoidHom.mem_ker, hk, map_mul, map_inv, hxy, inv_mul_cancel]
    have hkcen : k ∈ Subgroup.center G := hcen hmem
    have hkodd : Odd (orderOf k) :=
      Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard φ.ker hmem)
    have hcomm : Commute y k := Subgroup.mem_center_iff.mp hkcen y
    have hx2 : ∃ n, orderOf x = 2 ^ n := by
      simpa [Subgroup.orderOf_mk] using T.isPGroup'.exists_orderOf_eq_pow ⟨x, hx⟩
    have hy2 : ∃ n, orderOf y = 2 ^ n := by
      simpa [Subgroup.orderOf_mk] using T'.isPGroup'.exists_orderOf_eq_pow ⟨y, hy⟩
    have hxeq : x = y * k := by rw [hk]; group
    have hk1 : k = 1 := eq_one_of_mul_eq_of_two_pow_of_odd hcomm hxeq hx2 hy2 hkodd
    have hxy' : x = y := by rw [hxeq, hk1, mul_one]
    rwa [hxy']
  · rw [Sylow.card_eq_multiplicity T', Sylow.card_eq_multiplicity T]

end CFSG.Quasithin

end
