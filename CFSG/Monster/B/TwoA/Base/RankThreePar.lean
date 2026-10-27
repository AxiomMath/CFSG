
module

public import CFSG.Monster.B.TwoA.Base.RankThreeParBase

public import CFSG.Monster.B.TwoA.Base.RankThree

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.B.Co2

attribute [local instance] sharpAction

theorem exists_K3_conj_xhat
    {a : Dfull} (ha : a ∈ E3) (ha1 : a ≠ 1) :
    ∃ g ∈ K3, g * xhat * g⁻¹ = a := by
  obtain ⟨g, hg, hga⟩ := exists_conj_xhat NU_transitive (E3_eq_EU ▸ ha) ha1
  rw [← KU_eq_closure tauhat_mem_normalizer_EU NU_transitive, ← K3_eq] at hg
  exact ⟨g, hg, hga⟩

theorem pCore_K3_le_C3K :
    CFSG.pCore 2 K3 ≤ C3K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (Esharp E3) = 7 := by rw [natCard_Esharp, natCard_E3]
  obtain ⟨a, ha⟩ :=
    (CFSG.pCore_isPGroup (p := 2) (G := K3)).nonempty_fixed_point_of_prime_not_dvd_card
      (Esharp E3) (by rw [hcard]; decide)
  obtain ⟨ka, hka, hkax⟩ := exists_K3_conj_xhat a.2.1 a.2.2
  intro p hp
  rw [Subgroup.mem_subgroupOf, C3, Subgroup.mem_centralizer_iff]
  intro e he
  by_cases he1 : e = 1
  · rw [he1, one_mul, mul_one]
  obtain ⟨kb, hkb, hkbx⟩ := exists_K3_conj_xhat he he1
  let k : K3 := ⟨kb, hkb⟩ * (⟨ka, hka⟩ : K3)⁻¹
  have hk : (k : Dfull) * a * (k : Dfull)⁻¹ = e := by
    change kb * ka⁻¹ * a * (kb * ka⁻¹)⁻¹ = e
    rw [← hkax, ← hkbx]
    group
  let q : K3 := k⁻¹ * p * k
  have hq : q ∈ CFSG.pCore 2 K3 := by
    have h := (CFSG.pCore_normal (p := 2) (G := K3)).conj_mem p hp k⁻¹
    rwa [inv_inv] at h
  have hqa : (q : Dfull) * a * (q : Dfull)⁻¹ = a := congrArg Subtype.val (ha ⟨q, hq⟩)
  have hpe : (p : Dfull) * e * (p : Dfull)⁻¹ = e := by
    rw [← hk]
    calc (p : Dfull) * ((k : Dfull) * a * (k : Dfull)⁻¹) * (p : Dfull)⁻¹
        = (k : Dfull) * ((q : Dfull) * a * (q : Dfull)⁻¹) * (k : Dfull)⁻¹ := by
          change (p : Dfull) * ((k : Dfull) * a * (k : Dfull)⁻¹) * (p : Dfull)⁻¹ =
            (k : Dfull) * ((k : Dfull)⁻¹ * p * k * a * ((k : Dfull)⁻¹ * p * k)⁻¹) *
              (k : Dfull)⁻¹
          group
      _ = (k : Dfull) * a * (k : Dfull)⁻¹ := by rw [hqa]
  rw [mul_inv_eq_iff_eq_mul] at hpe
  exact hpe.symm

theorem pCore_K3_le_R3K :
    CFSG.pCore 2 K3 ≤ R3K := by
  intro p hp
  have hpC : p ∈ C3K := pCore_K3_le_C3K hp
  have hle : (CFSG.pCore 2 K3).comap C3K.subtype ≤ CFSG.pCore 2 C3K :=
    le_pCore_of_normal (CFSG.pCore_normal.comap _) CFSG.pCore_isPGroup.comap_subtype
  have h1 : (⟨p, hpC⟩ : C3K) ∈ CFSG.pCore 2 C3K := hle hp
  rw [← ker_B3_eq_pCore] at h1
  exact ⟨⟨p, hpC⟩, h1, rfl⟩

theorem pCore_K3_eq :
    CFSG.pCore 2 K3 = R3K :=
  le_antisymm pCore_K3_le_R3K (le_pCore_of_normal R3K_normal (IsPGroup.of_card natCard_R3K))

theorem R3_eq_pCore_K3 :
    R3 = (CFSG.pCore 2 K3).map K3.subtype := by
  rw [pCore_K3_eq, map_R3K]

theorem exists_k3QuotProd :
    ∃ e : K3 ⧸ R3.subgroupOf K3 ≃* GL (Fin 3) (ZMod 2) × Equiv.Perm (Fin 5),
      ∀ g : K3, e (QuotientGroup.mk g) = (actE3 g, sigma3 g) := by
  obtain ⟨e, he⟩ := exists_quotProdEquiv actE3 actE3_surjective ker_actE3 B3 B3_surjective
    ker_B3_characteristic sym5_conj_bijective
  exact ⟨(QuotientGroup.quotientMulEquivOfEq R3_subgroupOf_eq).trans e, fun g => he g⟩

theorem full_short_rank_three_parabolic_structure :
    (∀ g : C3, (g : Dfull) ∈ R3 ↔ c3Proj g ∈ CFSG.pCore 2 CU) ∧
    R3 = (CFSG.pCore 2 C3).map C3.subtype ∧ R3 = (CFSG.pCore 2 K3).map K3.subtype ∧
    Nat.card R3 = 2 ^ 35 ∧ E3 ≤ R3 ∧ (E3.subgroupOf R3).index = 2 ^ 32 ∧
    (∃ e : K3 ⧸ R3.subgroupOf K3 ≃* GL (Fin 3) (ZMod 2) × Equiv.Perm (Fin 5),
      (∀ g : K3, (e (QuotientGroup.mk g)).1 = actE3 g) ∧
      (∀ g : K3, (g : Dfull) ∈ C3 ↔ (e (QuotientGroup.mk g)).1 = 1) ∧
      ∀ g : C3, (e (QuotientGroup.mk (⟨g, C3_le_K3 g.2⟩ : K3))).2 = betaCU (c3Proj g)) ∧
    K3 ≤ Shat ∧ Nat.card K3 = 692692325498880 ∧
    (H3.subgroupOf K3).index = 7 ∧ ((K3 ⊓ Ntwo).subgroupOf K3).index = 7 := by
  obtain ⟨e, he⟩ := exists_k3QuotProd
  refine ⟨mem_R3_iff, R3_eq_pCore_C3, R3_eq_pCore_K3, natCard_R3, E3_le_R3, index_E3_R3,
    ⟨e, fun g => by rw [he], fun g => ?_, fun g => by rw [he, sigma3_coe]⟩, K3_le_Shat,
    natCard_K3, index_H3_K3, index_K3_inf_Ntwo⟩
  rw [he, ← MonoidHom.mem_ker, ker_actE3, Subgroup.mem_subgroupOf]

end CFSG.Monster.B.TwoA
