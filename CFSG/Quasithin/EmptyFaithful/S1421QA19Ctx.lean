module

public import CFSG.Quasithin.EmptyFaithful.S1421QA15A318
public import CFSG.Quasithin.EmptyFaithful.S1421Q9D

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S1421

variable {G : Type} [Group G] [Finite G] {T M H K1 L M₁ : Subgroup G}

theorem Core3Ctx.exists_involution_data (hF : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (c : Core3Ctx T M H K1 L M₁) (hq : CFSG.IsQuasisimple ↥L)
    (hex : A318Exclusion (↥L ⧸ CFSG.pCore 2 ↥L)) :
    ∃ (z : G) (hz : z ∈ L), orderOf z = 2 ∧ H ≤ Subgroup.centralizer ({z} : Set G) ∧
      orderOf ((QuotientGroup.mk' (CFSG.pCore 2 ↥L) : ↥L →* ↥L ⧸ CFSG.pCore 2 ↥L) ⟨z, hz⟩) = 2 ∧
      ∃ P : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L), IsSylowTwoOf P ⊤ ∧
        P ≤ Subgroup.centralizer
          ({(QuotientGroup.mk' (CFSG.pCore 2 ↥L) : ↥L →* ↥L ⧸ CFSG.pCore 2 ↥L) ⟨z, hz⟩} :
            Set (↥L ⧸ CFSG.pCore 2 ↥L)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL3 := c.eq_oPrimeResidualOf hF h36 h38 hq (MulEquiv.refl _) hex
  obtain ⟨z, hzZ, hz1, hz2, hzT, hZgen⟩ := exists_generator c.st
  have hzL : z ∈ L := c.omegaOneCenter_le_of_eq hL3 hzZ
  have hzo : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  have hHz : H ≤ Subgroup.centralizer ({z} : Set G) :=
    (Q9.H_le_mcOf c.st).trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hzZ))
  set π : ↥L →* ↥L ⧸ CFSG.pCore 2 ↥L := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
  have hzz : (⟨z, hzL⟩ : ↥L) ^ 2 = 1 := Subtype.ext (by simpa using hz2)
  have hne : π ⟨z, hzL⟩ ≠ 1 := by
    intro h1
    have hmem : (⟨z, hzL⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := (QuotientGroup.eq_one_iff _).mp h1
    have hcen := normal_isPGroup_le_center_of_isQuasisimple hq _
      (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) hmem
    apply c.not_le_mc
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [hZgen] at hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hcomm : Commute z l := by
      have := Subgroup.mem_center_iff.mp hcen ⟨l, hl⟩
      exact congrArg Subtype.val this.symm
    exact ((hcomm.zpow_left k).eq)
  have hord : orderOf (π ⟨z, hzL⟩) = 2 := by
    apply orderOf_eq_prime _ hne
    rw [← map_pow, hzz, map_one]
  refine ⟨z, hzL, hzo, hHz, hord, ?_⟩
  have hSyl : IsSylowTwoOf (sOf T K1) (g0Of T M H K1) := isSylowTwoOf_g0 c.inM c.sylow
  have hSL : IsSylowTwoOf (sOf T K1 ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal hSyl c.le_g0Of c.g0Of_le_normalizer
  have hP := isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hSL) π
    (QuotientGroup.mk'_surjective _)
  refine ⟨_, hP, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  have hxS : (x : G) ∈ sOf T K1 ⊓ L := Subgroup.mem_subgroupOf.mp hx
  have hxT : (x : G) ∈ T := hxS.1.1
  exact hzT _ hxT

end S1421

end CFSG.Quasithin
