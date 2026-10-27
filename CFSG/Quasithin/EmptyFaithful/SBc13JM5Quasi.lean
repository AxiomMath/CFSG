module

public import CFSG.Quasithin.Background.A3Structure36AQuasi
public import CFSG.Quasithin.Background.A3StructureBasic
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3Structure37Base

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

namespace SBc13

theorem card_center_of_quasisimple {X : Type} [Group X] (hq : CFSG.IsQuasisimple X)
    (h : A36Common X) :
    Nat.card (Subgroup.center X) = 1 ∨ Nat.card (Subgroup.center X) = 3 := by
  have hF : CFSG.fittingSubgroup X ≤ Subgroup.center X := A37.fitting_le_center hq h
  obtain ⟨-, -, halt, -, -⟩ := h
  rcases halt with ⟨hgf, -⟩ | ⟨hFZ, -, hcard⟩
  · exact absurd hgf (A36A.generalizedFitting_ne_fittingSubgroup hq hF)
  · rw [← hFZ]
    exact hcard

theorem not_mem_of_commutes {G : Type} [Group G] [Finite G] {X J : Subgroup G}
    (hX : SQTKGroup ↥X) (h36 : A36Statement (↥X ⧸ CFSG.pCore 2 ↥X)) (hJ : J ∈ cComp X)
    (hJq : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J)) {k : G} (hk : orderOf k = 5)
    (hcomm : ∀ x ∈ J, ⁅x, k⁆ ∈ pCoreOf 2 J) : k ∉ J := by
  intro hkJ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hJX : J ≤ X := le_of_mem_cComp hJ
  have hQ : SQTKHyp (↥X ⧸ CFSG.pCore 2 ↥X) := SQTKHyp.of_sqtkGroup ↥X hX
  let π : ↥X →* ↥X ⧸ CFSG.pCore 2 ↥X := QuotientGroup.mk' (CFSG.pCore 2 ↥X)
  have hsolv : Group.IsSolvable ↥(CFSG.pCore 2 ↥X) := by
    have : Group.IsNilpotent ↥(CFSG.pCore 2 ↥X) := IsPGroup.isNilpotent CFSG.pCore_isPGroup
    infer_instance
  set Jt : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X) := (J.subgroupOf X).map π with hJtdef
  have hJt : Jt ∈ cComp (⊤ : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)) :=
    (cComp_quotient_bijOn (CFSG.pCore 2 ↥X) hsolv).mapsTo (subgroupOf_mem_cComp hJ)
  let ι : ↥J →* ↥X := Subgroup.inclusion hJX
  have hmem : ∀ j : ↥J, π (ι j) ∈ Jt := fun j =>
    Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr j.2)
  let ρ : ↥J →* ↥Jt := (π.comp ι).codRestrict Jt hmem
  have hρsurj : Function.Surjective ρ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, Subgroup.mem_subgroupOf.mp hx⟩, Subtype.ext rfl⟩
  have hker_iff : ∀ j : ↥J, ρ j = 1 ↔ ι j ∈ CFSG.pCore 2 ↥X := by
    intro j
    rw [← OneMemClass.coe_eq_one]
    exact QuotientGroup.eq_one_iff _
  have hker_le : ρ.ker ≤ CFSG.pCore 2 ↥J := by
    refine le_sSup ⟨inferInstance, ?_⟩
    intro g
    have hg : ι g.1 ∈ CFSG.pCore 2 ↥X := (hker_iff g.1).mp g.2
    obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥X)) ⟨ι g.1, hg⟩
    refine ⟨n, ?_⟩
    have h1 : (ι g.1) ^ 2 ^ n = 1 := by
      have := congrArg Subtype.val hn
      simpa using this
    have h2 : ι (g.1 ^ 2 ^ n) = ι 1 := by
      rw [map_pow, map_one]
      exact h1
    have h3 : g.1 ^ 2 ^ n = 1 := Subgroup.inclusion_injective hJX h2
    apply Subtype.ext
    simpa using h3
  have hker_ge : CFSG.pCore 2 ↥J ≤ ρ.ker := by
    have hmap : (CFSG.pCore 2 ↥J).map ρ ≤ CFSG.pCore 2 ↥Jt :=
      le_sSup ⟨Subgroup.Normal.map inferInstance ρ hρsurj, IsPGroup.map CFSG.pCore_isPGroup ρ⟩
    have hbot : CFSG.pCore 2 ↥Jt = ⊥ := hQ.pCore_two_of_subnormal (subnormal_of_mem_cComp hJt)
    rw [hbot, le_bot_iff] at hmap
    intro x hx
    have h1 : ρ x ∈ (CFSG.pCore 2 ↥J).map ρ := Subgroup.mem_map_of_mem ρ hx
    rw [hmap] at h1
    exact MonoidHom.mem_ker.mpr (Subgroup.mem_bot.mp h1)
  have hker : ρ.ker = CFSG.pCore 2 ↥J := le_antisymm hker_le hker_ge
  let e : (↥J ⧸ CFSG.pCore 2 ↥J) ≃* ↥Jt :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ρ hρsurj)
  have hqJt : CFSG.IsQuasisimple ↥Jt := CFSG.LocalCores.isQuasisimple_of_mulEquiv e hJq
  have hZ := card_center_of_quasisimple hqJt (h36 Jt hJt).2.1
  let kk : ↥J := ⟨k, hkJ⟩
  have hkk : orderOf kk = 5 := (Subgroup.orderOf_coe kk).symm.trans hk
  have hρk1 : ρ kk ≠ 1 := by
    intro h1
    have hmem2 : kk ∈ CFSG.pCore 2 ↥J := hker ▸ MonoidHom.mem_ker.mpr h1
    obtain ⟨m, hm⟩ := IsPGroup.iff_orderOf.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥J))
      ⟨kk, hmem2⟩
    have h2 : orderOf kk = 2 ^ m :=
      (Subgroup.orderOf_coe (⟨kk, hmem2⟩ : ↥(CFSG.pCore 2 ↥J))).trans hm
    rw [hkk] at h2
    have h3 : 5 ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by norm_num) (dvd_of_eq h2)
    omega
  have hρk5 : orderOf (ρ kk) = 5 := by
    apply orderOf_eq_prime _ hρk1
    rw [← map_pow]
    have h1 : kk ^ 5 = 1 := by
      rw [← hkk]
      exact pow_orderOf_eq_one kk
    rw [h1, map_one]
  have hcent : ρ kk ∈ Subgroup.center ↥Jt := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := hρsurj y
    obtain ⟨w, hw, hwx⟩ := hcomm x x.2
    have hw' : w ∈ CFSG.pCore 2 ↥J := by
      exact hw
    have hwc : w = ⁅x, kk⁆ := Subtype.ext hwx
    have h1 : ρ ⁅x, kk⁆ = 1 := by
      rw [← hwc]
      exact MonoidHom.mem_ker.mp (hker_ge hw')
    rw [map_commutatorElement] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  have hdvd : 5 ∣ Nat.card (Subgroup.center ↥Jt) := by
    have h1 := orderOf_dvd_natCard (⟨ρ kk, hcent⟩ : ↥(Subgroup.center ↥Jt))
    have h2 : orderOf (⟨ρ kk, hcent⟩ : ↥(Subgroup.center ↥Jt)) = 5 :=
      (Subgroup.orderOf_coe _).symm.trans hρk5
    rwa [h2] at h1
  rcases hZ with h | h <;> (rw [h] at hdvd; omega)

end SBc13

end CFSG.Quasithin
