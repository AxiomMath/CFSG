module

import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Quasithin.Background.A3ComponentsQuotient

public section

namespace CFSG.Quasithin

namespace A37

open CFSG.Open
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem oddCore_eq_pPrimeCore_two (G : Type*) [Group G] :
    CFSG.oddCore G = CFSG.pPrimeCore 2 G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (CFSG.oddCore_eq_piCore G).trans (CFSG.pPrimeCore_eq_piCore G 2).symm

theorem odd_card_oddCore (G : Type*) [Group G] [Finite G] :
    Odd (Nat.card (CFSG.oddCore G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [oddCore_eq_pPrimeCore_two]
  exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card

instance oddCore_characteristic (G : Type*) [Group G] : (CFSG.oddCore G).Characteristic := by
  rw [oddCore_eq_pPrimeCore_two]
  infer_instance

theorem isSolvable_oddCore (G : Type*) [Group G] [Finite G] :
    Group.IsSolvable (CFSG.oddCore G) :=
  CFSG.FeitThompson.isSolvable_of_odd_natCard _ (odd_card_oddCore G)

@[expose] def oddCoreOf (H : Subgroup G) : Subgroup G := (CFSG.oddCore ↥H).map H.subtype

theorem oddCoreOf_le (H : Subgroup G) : oddCoreOf H ≤ H := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

theorem odd_card_oddCoreOf [Finite G] (H : Subgroup G) : Odd (Nat.card (oddCoreOf H)) := by
  unfold oddCoreOf
  rw [Subgroup.card_map_of_injective H.subtype_injective]
  exact odd_card_oddCore _

theorem le_oddCoreOf {N M : Subgroup G} (hNM : N ≤ M) (hN : (N.subgroupOf M).Normal)
    (hodd : Odd (Nat.card N)) : N ≤ oddCoreOf M := by
  have h1 : N.subgroupOf M ≤ CFSG.oddCore ↥M := by
    refine le_sSup ⟨hN, ?_⟩
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv]
    exact hodd
  calc N = (N.subgroupOf M).map M.subtype := (Subgroup.map_subgroupOf_eq_of_le hNM).symm
    _ ≤ oddCoreOf M := Subgroup.map_mono h1

theorem conj_mem_oddCoreOf {H : Subgroup G} {g x : G} (hg : g ∈ Subgroup.normalizer (H : Set G))
    (hx : x ∈ oddCoreOf H) : g * x * g⁻¹ ∈ oddCoreOf H := by
  obtain ⟨y, hy, rfl⟩ := hx
  have h := Subgroup.characteristic_iff_le_comap.mp (oddCore_characteristic ↥H)
    (Subgroup.normalizerMonoidHom H ⟨g, hg⟩) hy
  refine ⟨_, h, ?_⟩
  simp

theorem oddCoreOf_le_of_normal [Finite G] {H M : Subgroup G} (hle : H ≤ M)
    (hN : (H.subgroupOf M).Normal) : oddCoreOf H ≤ oddCoreOf M := by
  have hnorm : M ≤ Subgroup.normalizer (H : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp hN
  refine le_oddCoreOf ((oddCoreOf_le H).trans hle) ?_ (odd_card_oddCoreOf H)
  rw [Subgroup.normal_subgroupOf_iff ((oddCoreOf_le H).trans hle)]
  intro h m hh hm
  exact conj_mem_oddCoreOf (hnorm hm) hh

theorem oddCoreOf_le_of_subnormal [Finite G] {H K : Subgroup G} (h : IsSubnormal H K) :
    oddCoreOf H ≤ oddCoreOf K := by
  induction h with
  | refl => exact le_rfl
  | step hle hN _ ih => exact (oddCoreOf_le_of_normal hle hN).trans ih

theorem oddCoreOf_le_oddCore [Finite G] {L : Subgroup G} (h : IsSubnormal L ⊤) :
    oddCoreOf L ≤ CFSG.oddCore G := by
  refine (oddCoreOf_le_of_subnormal h).trans ?_
  refine le_sSup ⟨?_, ?_⟩
  · have : (⊤ : Subgroup G).subtype.range = ⊤ := by simp
    exact Subgroup.Normal.map (inferInstance : (CFSG.oddCore ↥(⊤ : Subgroup G)).Normal) _
      (MonoidHom.range_eq_top.1 this)
  · exact odd_card_oddCoreOf _

section Quotient

variable [Finite G]

theorem ker_oddCore_comp_subtype {L : Subgroup G} (hL : L ∈ cComp (⊤ : Subgroup G)) :
    ((QuotientGroup.mk' (CFSG.oddCore G)).comp L.subtype).ker = CFSG.oddCore ↥L := by
  ext a
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · intro ha
    have hN : ((CFSG.oddCore G).subgroupOf L).Normal := inferInstance
    have hodd : Odd (Nat.card ((CFSG.oddCore G).subgroupOf L)) := by
      let f : ((CFSG.oddCore G).subgroupOf L) →* CFSG.oddCore G :=
        (L.subtype.comp ((CFSG.oddCore G).subgroupOf L).subtype).codRestrict (CFSG.oddCore G)
          (fun x => x.2)
      have hf : Function.Injective f := by
        intro x y h
        have h' := congrArg (fun z : ↥(CFSG.oddCore G) => (z : G)) h
        exact Subtype.ext (Subtype.ext h')
      exact Odd.of_dvd_nat (odd_card_oddCore G) (Subgroup.card_dvd_of_injective f hf)
    exact (le_sSup ⟨hN, hodd⟩ : (CFSG.oddCore G).subgroupOf L ≤ CFSG.oddCore ↥L) ha
  · intro ha
    exact oddCoreOf_le_oddCore (subnormal_of_mem_cComp hL) ⟨a, ha, rfl⟩

theorem isComponent_map_oddCore {L : Subgroup G} (hL : L ∈ cComp (⊤ : Subgroup G))
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.oddCore ↥L)) :
    CFSG.IsComponent (L.map (QuotientGroup.mk' (CFSG.oddCore G))) := by
  have hsolv : Group.IsSolvable (QuotientGroup.mk' (CFSG.oddCore G)).ker := by
    rw [QuotientGroup.ker_mk']
    exact isSolvable_oddCore G
  have hLπ : L.map (QuotientGroup.mk' (CFSG.oddCore G)) ∈
      cComp (⊤ : Subgroup (G ⧸ CFSG.oddCore G)) :=
    map_mem_cComp_top _ (QuotientGroup.mk'_surjective _) hsolv hL
  refine ⟨?_, A3.subnormal_top_iff.1 (subnormal_of_mem_cComp hLπ)⟩
  let f : ↥L →* G ⧸ CFSG.oddCore G := (QuotientGroup.mk' (CFSG.oddCore G)).comp L.subtype
  have hker : f.ker = CFSG.oddCore ↥L := ker_oddCore_comp_subtype hL
  have hrange : f.range = L.map (QuotientGroup.mk' (CFSG.oddCore G)) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let e : (↥L ⧸ CFSG.oddCore ↥L) ≃* ↥(L.map (QuotientGroup.mk' (CFSG.oddCore G))) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      ((QuotientGroup.quotientKerEquivRange f).trans (MulEquiv.subgroupCongr hrange))
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq

theorem commutator_le_oddCoreOf {A B : Subgroup G} (hA : A ∈ cComp (⊤ : Subgroup G))
    (hB : B ∈ cComp (⊤ : Subgroup G)) (hAB : A ≠ B)
    (hAq : CFSG.IsQuasisimple (↥A ⧸ CFSG.oddCore ↥A))
    (hBq : CFSG.IsQuasisimple (↥B ⧸ CFSG.oddCore ↥B))
    (hnorm : B ≤ Subgroup.normalizer (A : Set G)) : ⁅A, B⁆ ≤ oddCoreOf A := by
  have hsolv : Group.IsSolvable (QuotientGroup.mk' (CFSG.oddCore G)).ker := by
    rw [QuotientGroup.ker_mk']
    exact isSolvable_oddCore G
  have hKA := isComponent_map_oddCore hA hAq
  have hKB := isComponent_map_oddCore hB hBq
  have hne : A.map (QuotientGroup.mk' (CFSG.oddCore G)) ≠
      B.map (QuotientGroup.mk' (CFSG.oddCore G)) := fun h =>
    hAB (map_injOn_cComp_top _ hsolv hA hB h)
  have hcomm : ⁅A.map (QuotientGroup.mk' (CFSG.oddCore G)),
      B.map (QuotientGroup.mk' (CFSG.oddCore G))⁆ = ⊥ := by
    rcases CFSG.LocalCores.distinct_components_commute hKA hKB with h | h
    · exact absurd h hne
    · exact h
  have hker : ⁅A, B⁆ ≤ CFSG.oddCore G := by
    have h : (⁅A, B⁆).map (QuotientGroup.mk' (CFSG.oddCore G)) = ⊥ := by
      rw [Subgroup.map_commutator]
      exact hcomm
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
  have hle : ⁅A, B⁆ ≤ A := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have hn' : b ∈ Subgroup.normalizer (A : Set G) := hnorm hb
    have : b * a⁻¹ * b⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hn' a⁻¹).mp (A.inv_mem ha)
    simpa [commutatorElement_def, mul_assoc] using A.mul_mem ha this
  have hinf : A ⊓ CFSG.oddCore G ≤ oddCoreOf A := by
    refine le_oddCoreOf inf_le_left ?_ ?_
    · rw [Subgroup.normal_subgroupOf_iff inf_le_left]
      intro h m hh hm
      exact ⟨A.mul_mem (A.mul_mem hm hh.1) (A.inv_mem hm),
        (inferInstance : (CFSG.oddCore G).Normal).conj_mem h hh.2 m⟩
    · exact Odd.of_dvd_nat (odd_card_oddCore G) (Subgroup.card_dvd_of_le inf_le_right)
  exact fun x hx => hinf ⟨hle hx, hker hx⟩

end Quotient

end A37

end CFSG.Quasithin
