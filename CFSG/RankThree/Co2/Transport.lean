module

public import CFSG.RankThree.Co2.Concrete
public import Certificates.Certificate3054
public import Certificates.Certificate16022
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3055
public import Certificates.Certificate3056
public import Certificates.Certificate3114
public import Certificates.Certificate3115
public import Certificates.Certificate3116
public import Certificates.Certificate3117
public import Certificates.Certificate3138
public import Certificates.Certificate16000

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.Co2

open CFSG.Blueprint CFSG.Monster.B.Co2 CFSG.Monster.B.Short CFSG.Monster.B.TwoA.Co2Inv
  CFSG.Monster.B.Co2Catalog

local notation "Co₂" => NativeSporadic.Co2

@[expose] def centralizerCo2Equiv (z : Co₂) :
    Subgroup.centralizer ({z} : Set Co₂) ≃*
      Subgroup.centralizer ({co2CatalogEquiv.symm z} : Set (Kstab v0)) :=
  @CFSG.Fischer.centralizerEquiv Co₂ (Kstab v0) Units.instGroup (Subgroup.toGroup _)
    co2CatalogEquiv.symm z

@[expose] def comapCo2 (S : Subgroup Co₂) : Subgroup (Kstab v0) where
  carrier := {k | co2CatalogEquiv k ∈ S}
  one_mem' := by
    change co2CatalogEquiv 1 ∈ S
    rw [map_one]
    exact S.one_mem
  mul_mem' := fun {a b} ha hb => by
    change co2CatalogEquiv (a * b) ∈ S
    rw [map_mul]
    exact S.mul_mem ha hb
  inv_mem' := fun {a} ha => by
    change co2CatalogEquiv a⁻¹ ∈ S
    rw [map_inv]
    exact S.inv_mem ha

theorem mem_comapCo2 {S : Subgroup Co₂} {k : Kstab v0} :
    k ∈ comapCo2 S ↔ co2CatalogEquiv k ∈ S := Iff.rfl

theorem card_comapCo2 (S : Subgroup Co₂) : Nat.card (comapCo2 S) = Nat.card S :=
  Nat.card_congr
    { toFun := fun k => ⟨co2CatalogEquiv k, k.2⟩
      invFun := fun s => ⟨co2CatalogEquiv.symm s, by
        rw [mem_comapCo2, MulEquiv.apply_symm_apply]; exact s.2⟩
      left_inv := fun k => Subtype.ext (co2CatalogEquiv.symm_apply_apply k)
      right_inv := fun s => Subtype.ext (co2CatalogEquiv.apply_symm_apply s) }

theorem factorization_card_Co2 : (Nat.card Co₂).factorization 2 = 18 := by
  rw [CFSG.Sporadic.Co2.card_Co2, show (42305421312000 : ℕ) = 2 ^ 18 * 161382375 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

instance finite_Co2 : Finite Co₂ :=
  Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Co2.card_Co2]; norm_num)

theorem nonempty_centralizer_mulEquiv_Cr (z₀ : Co₂) (hz₀1 : z₀ ≠ 1)
    (hcen : ∃ S : Sylow 2 Co₂, z₀ ∈ (S : Subgroup Co₂) ∧
      ∀ s ∈ (S : Subgroup Co₂), z₀ * s = s * z₀) :
    Nonempty (Subgroup.centralizer ({z₀} : Set Co₂) ≃* Cr) := by
  obtain ⟨S, hzS, hzc⟩ := hcen
  have hS' : Nat.card (comapCo2 (S : Subgroup Co₂)) =
      2 ^ (Nat.card (Kstab v0)).factorization 2 := by
    rw [card_comapCo2, Sylow.card_eq_multiplicity, factorization_card_Co2,
      factorization_card_Kstab]
  have hP : ((Sylow.ofCard _ hS' : Sylow 2 (Kstab v0)) : Subgroup (Kstab v0)) =
      comapCo2 (S : Subgroup Co₂) := Sylow.coe_ofCard _ _
  have hk₀ : co2CatalogEquiv.symm z₀ ∈ (Sylow.ofCard _ hS' : Subgroup (Kstab v0)) ∧
      ∀ s ∈ (Sylow.ofCard _ hS' : Subgroup (Kstab v0)),
        co2CatalogEquiv.symm z₀ * s = s * co2CatalogEquiv.symm z₀ := by
    rw [hP]
    refine ⟨?_, fun s hs => ?_⟩
    · rw [mem_comapCo2, MulEquiv.apply_symm_apply]
      exact hzS
    · rw [mem_comapCo2] at hs
      apply co2CatalogEquiv.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hzc _ hs
  have hk₀1 : co2CatalogEquiv.symm z₀ ≠ 1 := by
    intro e
    apply hz₀1
    rw [← co2CatalogEquiv.apply_symm_apply z₀, e, map_one]
  obtain ⟨g, hg⟩ := isConj_iff.1 (isConj_rK_of_central _ _ hk₀ hk₀1)
  exact ⟨((centralizerCo2Equiv z₀).trans (MulEquiv.subgroupCongr (by rw [hg]))).trans
    (centralizerConjEquiv g rK).symm⟩

end CFSG.RankThree.Co2
