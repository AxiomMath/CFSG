module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseS0Involution
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinConjugation
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.FStarCommute
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Uniformity for all involutions outside the Klein four two-core
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

private theorem hallSubgroup_subgroupPrimeSet_of_isHallIn_local
    {G : Type u} [Group G] [Finite G]
    {K H : Subgroup G} (hHall : IsHallIn K H) :
    IsHallSubgroup (subgroupPrimeSet K) (K.subgroupOf H) := by
  classical
  rcases hHall with ⟨hKH, hcop⟩
  have hcard : Nat.card (K.subgroupOf H) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv
  refine isHallSubgroup_of (G := H) (subgroupPrimeSet K) (K.subgroupOf H) ?_ ?_
  · intro q hq
    simpa [subgroupPrimeSet, hcard] using hq
  · intro q hqK hqIndex
    have hqCard : q.1 ∣ Nat.card K := by
      simpa [subgroupPrimeSet] using hqK
    exact ((q.2.coprime_iff_not_dvd).1
      (hcop.coprime_dvd_left hqCard)) hqIndex

public theorem firstCase_klein_uniform_involution_inverted
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    (r : G) (hr : c.IsReflection r)
    (hrV : r ∉ twoCoreOf c.Hhat) :
    ∃ K : Subgroup G,
      IsInvertedSubgroup K c.U r ∧ IsHallIn K c.FU ∧ K ≠ ⊥ ∧
        ∀ s : G, s ∈ c.Hhat → IsInvolution s →
          s ∉ twoCoreOf c.Hhat → IsInvertedSubgroup K c.U s := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hKr, hKHall, hKne, hKref⟩ :=
    firstCase_klein_uniform_reflection_inverted hmin c hfirst hklein r hr hrV
  have h26 := theorem_2_6 hmin c
  have hUnorm : IsNormalIn c.U c.Hhat := by
    rw [h26.1]
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      exact y.2
    · intro h hh k hk
      rcases Subgroup.mem_map.mp hk with ⟨y, hy, rfl⟩
      refine Subgroup.mem_map.mpr ⟨
        (⟨h, hh⟩ : ↥c.Hhat) * y * (⟨h, hh⟩ : ↥c.Hhat)⁻¹, ?_, ?_⟩
      · exact (pPrimeCore_normal (p := 2) (G := ↥c.Hhat)).conj_mem
          y hy (⟨h, hh⟩ : ↥c.Hhat)
      · simp
  have hFUnorm : IsNormalIn c.FU c.Hhat := by
    have h := fstar_characteristic_subgroupOf_map_normal_in
      (A := c.Hhat) (F := c.U) (K := fittingSubgroup (↥c.U))
      fittingSubgroup_characteristic hUnorm
    change IsNormalIn ((fittingSubgroup (↥c.U)).map c.U.subtype) c.Hhat at h
    exact h
  have hVnormal : IsNormalIn (twoCoreOf c.Hhat) c.Hhat := by
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      exact y.2
    · intro h hh k hk
      rcases Subgroup.mem_map.mp hk with ⟨y, hy, rfl⟩
      refine Subgroup.mem_map.mpr ⟨
        (⟨h, hh⟩ : ↥c.Hhat) * y * (⟨h, hh⟩ : ↥c.Hhat)⁻¹, ?_, ?_⟩
      · exact (pCore_normal (p := 2) (G := ↥c.Hhat)).conj_mem
          y hy (⟨h, hh⟩ : ↥c.Hhat)
      · simp
  have hSleHhat : (c.S : Subgroup G) ≤ c.Hhat :=
    (centralizerSetup_S_le_H c).trans c.H_le_Hhat
  let P : Sylow 2 (↥c.Hhat) := c.S.subtype hSleHhat
  have hVt : c.t ∈ twoCoreOf c.Hhat := by
    rw [← h26.2.1]
    refine ⟨c.S0_le_S c.t_mem_S0, ?_⟩
    have htcent : c.t ∈ Subgroup.centralizer (c.U : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hUleH : c.U ≤ c.H := by
        intro z hz
        change z ∈ oddCoreOf c.H at hz
        rcases Subgroup.mem_map.mp hz with ⟨w, hw, rfl⟩
        exact w.2
      have hxH : x ∈ c.H := hUleH hx
      have hxCent : x ∈ Subgroup.centralizer ({c.t} : Set G) := by
        simpa [c.H_eq_centralizer] using hxH
      have hcomm := (Subgroup.mem_centralizer_iff.mp hxCent) c.t (by simp)
      exact hcomm.symm
    exact htcent
  refine ⟨K, hKr, hKHall, hKne, ?_⟩
  intro s hsH hsInv hsV
  have hsPow : s ^ 2 = 1 := hsInv.2
  have hsord : orderOf s = 2 := by
    exact orderOf_eq_prime hsPow hsInv.1
  have hzpH : Subgroup.zpowers s ≤ c.Hhat :=
    (Subgroup.zpowers_le).2 hsH
  let Q0 : Subgroup (↥c.Hhat) := (Subgroup.zpowers s).subgroupOf c.Hhat
  have hQ0card : Nat.card Q0 = 2 := by
    calc
      Nat.card Q0 = Nat.card (Subgroup.zpowers s) := by
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzpH).toEquiv
      _ = orderOf s := Nat.card_zpowers s
      _ = 2 := hsord
  have hQ0p : IsPGroup 2 Q0 := by
    simpa [hQ0card] using (IsPGroup.of_card (p := 2) (n := 1)
      (show Nat.card Q0 = 2 ^ 1 by simpa using hQ0card))
  obtain ⟨Q, hQ0Q⟩ := IsPGroup.exists_le_sylow hQ0p
  obtain ⟨h, hh⟩ :=
    @MulAction.IsPretransitive.exists_smul_eq c.Hhat (Sylow 2 c.Hhat)
      inferInstance inferInstance Q P
  let yH : c.Hhat := ⟨s, hsH⟩
  have hyQ0 : yH ∈ Q0 := by
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers s)
  have hyQ : yH ∈ Q := hQ0Q hyQ0
  have hyP : h * yH * h⁻¹ ∈ (P : Subgroup c.Hhat) := by
    have hySmul : (MulAut.conj h) yH ∈ ((h • Q : Sylow 2 c.Hhat) : Subgroup c.Hhat) := by
      change (MulAut.conj h) yH ∈ ((h • Q : Sylow 2 c.Hhat) : Subgroup c.Hhat)
      exact Subgroup.mem_map.mpr ⟨yH, hyQ, rfl⟩
    rw [hh] at hySmul
    simpa [MulAut.conj_apply] using hySmul
  let r' : G := (h : G) * s * (h : G)⁻¹
  have hr'S : r' ∈ (c.S : Subgroup G) := by
    have hyP' : (h * yH * h⁻¹ : c.Hhat) ∈
        (c.S : Subgroup G).subgroupOf c.Hhat := by
      simpa [P] using hyP
    exact Subgroup.mem_subgroupOf.mp hyP'
  have hr'Inv : IsInvolution r' := by
    refine ⟨?_, ?_⟩
    · intro h1
      apply hsInv.1
      calc
        s = (h : G)⁻¹ * r' * (h : G) := by simp [r', mul_assoc]
        _ = 1 := by rw [h1]; simp
    · change ((h : G) * s * (h : G)⁻¹) ^ 2 = 1
      rw [pow_two]
      calc
        ((h : G) * s * (h : G)⁻¹) * ((h : G) * s * (h : G)⁻¹) =
            (h : G) * (s * s) * (h : G)⁻¹ := by group
        _ = 1 := by rw [← pow_two, hsPow]; simp
  have hr'V : r' ∉ twoCoreOf c.Hhat := by
    intro hrV'
    have hsV' := hVnormal.2 (h : G) h.property r' hrV'
    have : s ∈ twoCoreOf c.Hhat := by
      have hsV'' := hVnormal.2 (h : G)⁻¹ ((c.Hhat).inv_mem h.property) r' hrV'
      rw [show s = (h : G)⁻¹ * r' * (h : G) by
        simp [r', mul_assoc, inv_inv]]
      rw [inv_inv] at hsV''
      exact hsV''
    exact hsV this
  have hr'Refl : c.IsReflection r' := by
    refine ⟨hr'S, ?_⟩
    intro hrS0
    have hrEqT : r' = c.t := firstCase_S0_involution_eq_t c hrS0 hr'Inv
    exact hr'V (hrEqT ▸ hVt)
  have hhU : (h : G) ∈ Subgroup.normalizer (c.U : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hUnorm.2 (h : G) h.property x hx
    · intro hx
      have hxin := hUnorm.2 (h : G)⁻¹ ((c.Hhat).inv_mem h.property)
        ((h : G) * x * (h : G)⁻¹) hx
      simpa [mul_assoc] using hxin
  have hhr : (h : G) * s * (h : G)⁻¹ = r' := by rfl
  have hKr' : IsInvertedSubgroup K c.U r' := hKref r' hr'Refl hr'V
  have hhUinv : (h : G)⁻¹ ∈ Subgroup.normalizer (c.U : Set G) :=
    (Subgroup.normalizer (c.U : Set G)).inv_mem hhU
  have hKmapInv : IsInvertedSubgroup
      (K.map (MulAut.conj ((h : G)⁻¹)).toMonoidHom) c.U s := by
    apply firstCase_conjugate_invertedSubgroup hr'Inv hhUinv
    · change (h : G)⁻¹ * r' * ((h : G)⁻¹)⁻¹ = s
      rw [inv_inv]
      simp [r', mul_assoc]
    · exact hKr'
  have hmapEq : K.map (MulAut.conj ((h : G)⁻¹)).toMonoidHom = K := by
    let KFU : Subgroup (↥c.FU) := K.subgroupOf c.FU
    have hKFUHall : IsHallSubgroup (subgroupPrimeSet K) KFU :=
      hallSubgroup_subgroupPrimeSet_of_isHallIn_local hKHall
    have hFUnil : Group.IsNilpotent (↥c.FU) :=
      fittingSubgroupOf_isNilpotent c.U
    let α : (↥c.FU) ≃* (↥c.FU) :=
      { toFun := fun y =>
          ⟨(h : G)⁻¹ * (y : G) * (h : G),
            by
              simpa [inv_inv] using
                hFUnorm.2 (h : G)⁻¹ ((c.Hhat).inv_mem h.property)
                  (y : G) y.property⟩
        invFun := fun y =>
          ⟨(h : G) * (y : G) * (h : G)⁻¹,
            hFUnorm.2 (h : G) h.property (y : G) y.property⟩
        left_inv := by intro y; ext; group
        right_inv := by intro y; ext; group
        map_mul' := by
          intro x y
          apply Subtype.ext
          change (h : G)⁻¹ * ((x : G) * (y : G)) * (h : G) =
            ((h : G)⁻¹ * (x : G) * (h : G)) *
              ((h : G)⁻¹ * (y : G) * (h : G))
          group }
    have hαHall : IsHallSubgroup (subgroupPrimeSet K)
        (KFU.map α.toMonoidHom) := hKFUHall.map_mulAut α
    let : KFU.Normal :=
      section15_hall_subgroup_normal_of_nilpotent hFUnil hKFUHall
    have hEqFU : KFU.map α.toMonoidHom = KFU :=
      hKFUHall.eq_of_normal hαHall
    ext x
    constructor
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨z, hz, rfl⟩
      let zFU : ↥c.FU := ⟨z, hKHall.1 hz⟩
      have hzmap : α zFU ∈ KFU.map α.toMonoidHom := by
        exact Subgroup.mem_map.mpr ⟨zFU,
          Subgroup.mem_subgroupOf.mpr hz, rfl⟩
      rw [hEqFU] at hzmap
      have hzmap' : (α zFU : G) ∈ K :=
        Subgroup.mem_subgroupOf.mp hzmap
      simpa [α, KFU, MulAut.conj_apply] using hzmap'
    · intro hx
      let xFU : ↥c.FU := ⟨x, hKHall.1 hx⟩
      have hxmap : xFU ∈ KFU.map α.toMonoidHom := by
        rw [hEqFU]
        exact Subgroup.mem_subgroupOf.mpr hx
      rcases Subgroup.mem_map.mp hxmap with ⟨z, hz, hzx⟩
      apply Subgroup.mem_map.mpr
      refine ⟨(z : G), Subgroup.mem_subgroupOf.mp hz, ?_⟩
      simpa [α, MulAut.conj_apply] using congrArg Subtype.val hzx
  rw [← hmapEq]
  exact hKmapInv

end CFSG.GorensteinWalter
