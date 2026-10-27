module

public import CFSG.RankThree.LocalRank.ThetaPlaneAlpha
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.RankThreeEvenClassification.NormalizedProduct

public section

namespace CFSG.RankThree.Coprime

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.RankThreeEvenClassification.Helpers
open scoped commutatorElement

theorem commutator_inSubgroup_aschbacherSolvableCore_eq_bot {G : Type*} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) {L C : Subgroup G} (hL : IsComponent L) (hLC : L ≤ C) :
    ⁅inSubgroup (aschbacherSolvableCore p) C, L⁆ = ⊥ := by
  have hL' := CFSG.LocalCores.component_overgroup hL hLC
  have hsolv := (solvable_prime_complement_core_characterization (H := C) hp).1
  have hsub : (aschbacherSolvableCore p C).IsSubnormal :=
    (inferInstance : (aschbacherSolvableCore p C).Normal).isSubnormal
  have h := (CFSG.LocalCores.component_solvable_centralizer (G := C) hsolv hsub).1 _ hL'
  have hmap := congrArg (Subgroup.map C.subtype) h
  rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hLC,
    Subgroup.map_bot] at hmap
  rw [Subgroup.commutator_comm]
  exact hmap

theorem conj_mem_centralizer_of_mem_normalizer {G : Type*} [Group G] {L : Subgroup G} {z a : G}
    (hz : z ∈ normalizer (L : Set G)) (ha : a ∈ centralizer (L : Set G)) :
    z * a * z⁻¹ ∈ centralizer (L : Set G) :=
  Subgroup.le_normalizer_iff.mp (normalizes_centralizer_of_normalizes _ L le_rfl) z hz a ha

theorem le_centralizer_singleton_of_mem {G : Type*} [Group G] {L : Subgroup G} {a : G}
    (ha : a ∈ centralizer (L : Set G)) : L ≤ centralizer ({a} : Set G) := by
  intro l hl
  rw [mem_centralizer_iff]
  rintro _ rfl
  exact ((mem_centralizer_iff.mp ha) l hl).symm

theorem nonfaithful_plane_local_core_product_centralizes_component {G : Type*} [Group G]
    [Finite G] {p : ℕ} (hp : p.Prime) {E : Subgroup G} (hE : IsElementaryAbelian p E)
    (hEcard : Nat.card E = p ^ 2) {t : G} (htE : t ∈ E) (ht1 : t ≠ 1) {L : Subgroup G}
    (hL : IsComponent L)
    (hXL : ⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ≤
      normalizer (L : Set G))
    (hCEL : E ⊓ centralizer (L : Set G) ≠ ⊥) :
    ⁅⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆, L⁆ = ⊥ ∧
      ⁅thetaT p E, L⁆ = ⊥ ∧
      ⁅⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ⊔ thetaT p E,
        L⁆ = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have := hE
  have hEexp : ∀ x ∈ E, x ^ p = 1 := fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx
  have hEab : IsMulCommutative E := hE.toIsMulCommutative
  have hEp : IsPGroup p E := IsElementaryAbelian.isPGroup p E
  set S := inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)) with hS
  have hSp : ¬ p ∣ Nat.card S := by
    rw [hS, inSubgroup, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    exact (solvable_prime_complement_core_characterization
      (H := centralizer ({t} : Set G)) hp).2.2.1
  have hSt : S ≤ centralizer ({t} : Set G) := Subgroup.map_subtype_le _
  have hXS : ⁅S, E⁆ ≤ S := by
    rw [hS, inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp]
    exact thetaPlaneCommutator_le_element_theta p hp E hEab t htE
  have hES : E ≤ normalizer (S : Set G) := by
    rw [hS, inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp]
    exact commutative_plane_normalizes_element_theta p hp E hEab t htE
  obtain ⟨⟨a, haE, haL⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hCEL
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hIL : ⁅thetaT p E, L⁆ = ⊥ := by
    have hle : thetaT p E ≤ inSubgroup (aschbacherSolvableCore p) (centralizer ({a} : Set G)) :=
      iInf_le_of_le a (iInf_le_of_le haE (iInf_le_of_le ha1' le_rfl))
    exact le_bot_iff.mp ((Subgroup.commutator_mono hle le_rfl).trans
      (commutator_inSubgroup_aschbacherSolvableCore_eq_bot hp hL
        (le_centralizer_singleton_of_mem haL)).le)
  have hcentL : zpowers a ≤ centralizer (L : Set G) := zpowers_le.mpr haL
  have hXL' : ⁅S, E⁆ ≤ centralizer (L : Set G) := by
    by_cases hat : a ∈ zpowers t
    ·
      have hta : t ∈ zpowers a := by
        have hle : zpowers a ≤ zpowers t := zpowers_le.mpr hat
        have heq : zpowers a = zpowers t := Subgroup.eq_of_le_of_card_ge hle (by
          rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime (hEexp t htE) ht1,
            orderOf_eq_prime (hEexp a haE) ha1'])
        rw [heq]
        exact mem_zpowers t
      have h := commutator_inSubgroup_aschbacherSolvableCore_eq_bot hp hL
        (le_centralizer_singleton_of_mem (hcentL hta))
      exact hXS.trans (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h)
    ·
      have hcomm : zpowers a ≤ normalizer (zpowers t : Set G) := by
        refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
        refine zpowers_le.mpr ?_
        have hEc : E ≤ centralizer (E : Set G) := le_centralizer_iff_isMulCommutative.mpr hEab
        exact Subgroup.centralizer_le (zpowers_le.mpr htE) (hEc haE)
      have hEta : zpowers t ⊔ zpowers a = E := by
        have hle : zpowers t ⊔ zpowers a ≤ E := sup_le (zpowers_le.mpr htE) (zpowers_le.mpr haE)
        refine Subgroup.eq_of_le_of_card_ge hle ?_
        have hlt : zpowers t < zpowers t ⊔ zpowers a :=
          lt_of_le_of_ne le_sup_left fun h => hat (h ▸ mem_sup_right (mem_zpowers a))
        have h1 := Subgroup.card_lt_of_lt hlt
        rw [Nat.card_zpowers, orderOf_eq_prime (hEexp t htE) ht1] at h1
        obtain ⟨j, hj, hjc⟩ := (Nat.dvd_prime_pow hp).mp
          (hEcard ▸ Subgroup.card_dvd_of_le hle)
        rw [hEcard, hjc]
        rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
        · rw [hjc, pow_zero] at h1
          exact absurd h1 (by have := hp.one_lt; omega)
        · rw [hjc, pow_one] at h1
          exact absurd h1 (lt_irrefl p)
        · exact le_rfl
      have htS : zpowers t ≤ centralizer (S : Set G) := by
        refine zpowers_le.mpr ?_
        rw [mem_centralizer_iff]
        intro s hs
        exact ((mem_centralizer_iff.mp (hSt hs)) t rfl).symm
      have hXa : ⁅S, E⁆ = ⁅S, zpowers a⁆ := by
        refine le_antisymm ?_ (Subgroup.commutator_mono le_rfl (zpowers_le.mpr haE))
        refine Subgroup.commutator_le.mpr fun s hs e he => ?_
        rw [← hEta] at he
        obtain ⟨x, hx, y, hy, rfl⟩ := normalized_sup_factorization _ _ hcomm e he
        have hsx : s * x = x * s := (mem_centralizer_iff.mp (htS hx)) s hs
        have hsy : ⁅s, y⁆ ∈ S := by
          rw [commutatorElement_def]
          have := Subgroup.le_normalizer_iff.mp hES y (zpowers_le.mpr haE hy) s⁻¹
            (S.inv_mem hs)
          simpa [mul_assoc] using S.mul_mem hs this
        have hxc : x * ⁅s, y⁆ * x⁻¹ = ⁅s, y⁆ := by
          rw [← (mem_centralizer_iff.mp (htS hx)) _ hsy, mul_inv_cancel_right]
        have h : ⁅s, x * y⁆ = x * ⁅s, y⁆ * x⁻¹ := by
          simp only [commutatorElement_def]
          calc s * (x * y) * s⁻¹ * (x * y)⁻¹ = (s * x) * y * s⁻¹ * y⁻¹ * x⁻¹ := by group
            _ = x * (s * y * s⁻¹ * y⁻¹) * x⁻¹ := by rw [hsx]; group
        rw [h, hxc]
        exact Subgroup.commutator_mem_commutator hs hy
      have hidem := coprime_commutator_idempotent p hp (zpowers a) S
        (hEp.to_le (zpowers_le.mpr haE)) hSp ((zpowers_le.mpr haE).trans hES)
      rw [hXa, ← hidem]
      refine Subgroup.commutator_le.mpr fun z hz g hg => ?_
      have hzN : z ∈ normalizer (L : Set G) := hXL (hXa ▸ hidem ▸ hz)
      rw [commutatorElement_def]
      exact (centralizer (L : Set G)).mul_mem
        (conj_mem_centralizer_of_mem_normalizer hzN (hcentL hg))
        ((centralizer (L : Set G)).inv_mem (hcentL hg))
  exact ⟨Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hXL', hIL,
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (sup_le hXL' (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hIL))⟩

end CFSG.RankThree.Coprime
