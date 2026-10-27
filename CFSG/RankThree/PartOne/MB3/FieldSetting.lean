module

public import CFSG.RankThree.PartOne.S11d.Sec109Common

public section

namespace CFSG.RankThree.PartOne.MB3

open Subgroup CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory
open CFSG.Blueprint (EvenLieType)

variable {G : Type} [Group G] [Finite G]

structure FieldSetting (p : ℕ) (A : Subgroup G) (c : G) (L B : Subgroup G) (n : ℕ) (b : G)
    (S K E : Subgroup G) (a d : G) : Prop where
  config : Sec109.Config p A c L B n
  witness : Sec109.Witness A c B b S
  K_mem : K ∈ sectionTenAt p (sectionTenZeroStar p A) b
  S_le : S ≤ K
  K_even : EvenLieType (K ⧸ Subgroup.center K)
  K_center : ¬ p ∣ Nat.card (Subgroup.center K)
  K_qs : CFSG.IsQuasisimple ↥K
  a_mem : a ∈ A
  d_mem : d ∈ A
  d_ne_one : d ≠ 1
  A_eq : A = Subgroup.zpowers a ⊔ Subgroup.zpowers b ⊔ Subgroup.zpowers d
  d_K : Subgroup.zpowers d = A ⊓ K
  a_field : InducesFieldAut p a K
  c_notMem : c ∉ Subgroup.zpowers b ⊔ Subgroup.zpowers d
  c_field : InducesFieldAut p c K
  E_eq : E = inSubgroup perfectResidual (K ⊓ Subgroup.centralizer ({c} : Set G))
  E_qs : CFSG.IsQuasisimple ↥E
  d_mem_E : d ∈ E
  E_le_L : E ≤ L
  E_comp : CFSG.IsComponent (E.subgroupOf (L ⊓ Subgroup.centralizer ({b} : Set G)))

omit [Finite G] in
theorem not_dvd_of_scalar {p : ℕ} {b x : G} {lam : ℤ} (hb1 : b ≠ 1) (hbp : b ^ p = 1)
    (hx : x * b * x⁻¹ = b ^ lam) : ¬ (p : ℤ) ∣ lam := by
  rintro ⟨k, hk⟩
  apply hb1
  have h1 : b ^ lam = 1 := by rw [hk, zpow_mul, zpow_natCast, hbp, one_zpow]
  have h2 : x * b * x⁻¹ = 1 := by rw [hx, h1]
  simpa using h2

namespace FieldSetting

variable {p : ℕ} {A : Subgroup G} {c : G} {L B : Subgroup G} {n : ℕ} {b : G} {S K E : Subgroup G}
  {a d : G} (F : FieldSetting p A c L B n b S K E a d)

include F

theorem b_mem_A : b ∈ A := F.config.B_le_A F.witness.b_mem

theorem b_pow : b ^ p = 1 := F.config.pow_p_eq_one F.b_mem_A

theorem d_mem_K : d ∈ K := (Subgroup.mem_inf.mp (F.d_K ▸ Subgroup.mem_zpowers d)).2

theorem d_mem_B : d ∈ B := by
  rw [F.config.B_eq]
  exact ⟨F.d_mem, F.E_le_L F.d_mem_E⟩

theorem K_le_centralizer : K ≤ Subgroup.centralizer ({b} : Set G) :=
  (mem_thetaComponentsAt_iff.mp F.K_mem.2).1

theorem E_le_K : E ≤ K := by
  rw [F.E_eq]
  exact (Subgroup.map_subtype_le _).trans inf_le_left

end FieldSetting

end CFSG.RankThree.PartOne.MB3
