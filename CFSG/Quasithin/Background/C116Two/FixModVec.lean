module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks
public import CFSG.Quasithin.EmptyFaithful.S14111
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.C116Two

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem two_dvd_index_subgroupOf {U Z : Subgroup G} (hU2 : IsPGroup 2 U) (hZU : Z < U) :
    2 ∣ (Z.subgroupOf U).index := by
  have hne : Z.subgroupOf U ≠ ⊤ := by
    intro h
    have hUZ : U ≤ Z := fun x hx => by
      have hmem : (⟨x, hx⟩ : ↥U) ∈ Z.subgroupOf U := by
        rw [h]
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp hmem
    exact lt_irrefl Z (lt_of_lt_of_le hZU hUZ)
  obtain ⟨n, hn⟩ := hU2.index (Z.subgroupOf U)
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hne (Subgroup.index_eq_one.mp (by rw [hn, pow_zero]))
  rw [hn]
  exact dvd_pow_self 2 hn0

theorem conj_mem_of_mem_normalizer {N : Subgroup G} {j : G}
    (hj : j ∈ Subgroup.normalizer (N : Set G)) {x : G} (hx : x ∈ N) : j * x * j⁻¹ ∈ N :=
  (Subgroup.mem_normalizer_iff.mp hj x).mp hx

theorem exists_fixedCoset_ne {U Z J : Subgroup G} (hU2 : IsPGroup 2 U) (hZU : Z < U)
    (hJ2 : IsPGroup 2 J) (hUn : ∀ j ∈ J, ∀ x ∈ U, j * x * j⁻¹ ∈ U)
    (hZn : ∀ j ∈ J, ∀ x ∈ Z, j * x * j⁻¹ ∈ Z) :
    ∃ u ∈ U, u ∉ Z ∧ ∀ j ∈ J, ⁅u, j⁆ ∈ Z := by
  letI actU : MulAction J U :=
    { smul := fun j x => ⟨(j : G) * x * (j : G)⁻¹, hUn j j.2 x x.2⟩
      one_smul := fun x => Subtype.ext (by
        show ((1 : J) : G) * (x : G) * ((1 : J) : G)⁻¹ = (x : G)
        simp)
      mul_smul := fun j k x => Subtype.ext (by
        show ((j * k : J) : G) * (x : G) * ((j * k : J) : G)⁻¹
          = (j : G) * ((k : G) * (x : G) * (k : G)⁻¹) * (j : G)⁻¹
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group) }
  have hsmul : ∀ (j : J) (a : U), ((j • a : U) : G) = (j : G) * (a : G) * (j : G)⁻¹ :=
    fun _ _ => rfl
  haveI : MulAction.QuotientAction J (Z.subgroupOf U) :=
    ⟨fun j {a a'} h => by
      rw [Subgroup.mem_subgroupOf] at h ⊢
      have h' := hZn (j : G) j.2 _ h
      convert h' using 1
      simp only [hsmul, Subgroup.coe_mul, Subgroup.coe_inv]
      group⟩
  haveI : Finite (↥U ⧸ Z.subgroupOf U) := inferInstance
  have hpα : 2 ∣ Nat.card (↥U ⧸ Z.subgroupOf U) := two_dvd_index_subgroupOf hU2 hZU
  have ha0 : (QuotientGroup.mk (1 : ↥U) : ↥U ⧸ Z.subgroupOf U) ∈
      MulAction.fixedPoints J (↥U ⧸ Z.subgroupOf U) := by
    refine MulAction.mem_fixedPoints.mpr (fun j => ?_)
    rw [MulAction.Quotient.smul_mk,
      show j • (1 : ↥U) = 1 from Subtype.ext (by rw [hsmul]; simp)]
  obtain ⟨b, hbfix, hab⟩ :=
    hJ2.exists_fixed_point_of_prime_dvd_card_of_fixed_point (↥U ⧸ Z.subgroupOf U) hpα ha0
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective b
  have hv_not : v ∉ Z.subgroupOf U := fun h =>
    hab (QuotientGroup.eq.mpr (by simpa using h))
  have hv_notZ : (v : G) ∉ Z := fun h => hv_not (Subgroup.mem_subgroupOf.mpr h)
  refine ⟨(v : G)⁻¹, U.inv_mem v.2, fun h => hv_notZ (by simpa using Z.inv_mem h), fun j hj => ?_⟩
  have hfix := (MulAction.mem_fixedPoints.mp hbfix) ⟨j, hj⟩
  rw [MulAction.Quotient.smul_mk] at hfix
  have hmem := Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp hfix)
  have e : ⁅(v : G)⁻¹, j⁆ = (((j : G) * (v : G) * (j : G)⁻¹)⁻¹ * (v : G))⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [e]
  refine Z.inv_mem ?_
  simpa only [hsmul, Subgroup.coe_mul, Subgroup.coe_inv] using hmem

theorem exists_fixMod_ne {H L J : Subgroup G} (hL : IsChiBlock H L) (hJ2 : IsPGroup 2 J)
    (hJN : J ≤ Subgroup.normalizer (L : Set G)) :
    ∃ u ∈ blockU L, u ∉ blockZ L ∧ ∀ j ∈ J, ⁅u, j⁆ ∈ blockZ L :=
  exists_fixedCoset_ne (CFSG.QuasithinUnique.C1.isPGroup_blockU hL.1.1)
    hL.1.1.2.2.2.2.1 hJ2
    (fun j hj _ hx => conj_mem_of_mem_normalizer
      (CFSG.QuasithinUnique.C1.mem_normalizer_blockU (hJN hj)) hx)
    (fun j hj _ hx => conj_mem_of_mem_normalizer
      (CFSG.QuasithinUnique.C1.mem_normalizer_blockZ (hJN hj)) hx)

end CFSG.Quasithin.C116Two
