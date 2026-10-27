module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeU52TorusPerm
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeU52TorusPattern
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotBlocksBasic

public section

namespace CFSG.GGQ2Prime

open Subgroup CFSG.Open CFSG.Models
open CFSG.RankThree.PartOne.KFU CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.SeitzReduction.UnitaryPilot

private theorem lieModel_PSU_of_mulEquiv_unitarySU {Y : Type} [Group Y] {K : Type} [Field K]
    (hU : UnitaryFieldData 2 1 K) {n : ℕ} (hn : 4 ≤ n) (hgcd : Nat.gcd n 3 = 1)
    (e : unitarySU 2 1 K n ≃* Y) : LieModel Y .PSU n 2 1 := by
  have := hU.finite
  have hK : Nat.card K = (2 ^ 1) ^ 2 := by rw [hU.card]; norm_num
  have hadm : StatedLieAdmissible .PSU n 2 1 :=
    ⟨Nat.prime_two, le_rfl, by omega, fun h => by
      have := congrArg Prod.fst h
      simp only at this
      omega⟩
  refine ⟨hadm, Or.inl ⟨hadm, K, inferInstance, inferInstance, hK, ⟨?_⟩⟩⟩
  exact e.symm.trans (projEquivOfBot (scalars_subgroupOf_eq_bot hK (by omega)
    (by simpa using hgcd))).symm

private theorem unitaryBlock_commute_diagU {K : Type} [Field K] (hU : UnitaryFieldData 2 1 K)
    {I : Finset (Fin 5)} {l : Kˣ} {d : Fin 5 → Kˣ} (hd : ∀ i ∈ I, d i = l)
    {A : unitarySU 2 1 K 5} (hA : A ∈ unitaryBlock hU I) :
    (A : GL (Fin 5) K) * diagU d = diagU d * (A : GL (Fin 5) K) := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, diagU_val]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hij : i ∈ I ∧ j ∈ I
  · rw [hd i hij.1, hd j hij.2, mul_comm]
  · rw [(mem_unitaryBlock hU).1 hA i j (by tauto)]
    by_cases e : i = j
    · subst e
      simp [mul_comm]
    · simp [Matrix.one_apply_ne e]

theorem exists_U42_of_U52_torus {G : Type} [Group G] {X T : Subgroup G}
    (hX : LieModel X .PSU 5 2 1) (hT : IsElemAbelian 3 T) (hTX : T ≤ X)
    (hcard : Nat.card T = 3 ^ 4) {t : G} (ht : t ∈ T) (ht1 : t ≠ 1)
    (h24 : 24 ≤ ((fun y : G => fun b : T => y * (b : G) * y⁻¹) ''
      ((X ⊓ normalizer (T : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G)).ncard) :
    ∃ Y : Subgroup G, LieModel Y .PSU 4 2 1 ∧ Y ≤ X ⊓ centralizer ({t} : Set G) := by
  obtain ⟨K, _, hU, ψ, hψ⟩ := exists_torusFrame_of_U52 hX hT hTX hcard
  have : Finite K := hU.finite
  have hK : Nat.card K = 4 := by rw [hU.card]; norm_num
  set g₀ := ψ.symm ⟨t, hTX ht⟩ with hg₀
  have hg₀t : ((ψ g₀ : X) : G) = t := by simp [hg₀]
  obtain ⟨d, hd3, hprod, hdg⟩ := mem_torusSU_iff.1 ((hψ g₀).1 (by rw [hg₀t]; exact ht))
  have hd1 : d ≠ 1 := by
    rintro rfl
    apply ht1
    have : g₀ = 1 := Subtype.ext (by rw [← hdg, diagU_one]; rfl)
    rw [← hg₀t, this, map_one]
    rfl
  have h24' : 24 ≤ Set.ncard {τ : Equiv.Perm (Fin 5) | d ∘ τ = d} := by
    set Φ : Equiv.Perm (Fin 5) → T → G := fun σ b =>
      U52TorusCarried.torusPermElt hU ψ σ * (b : G) *
        (U52TorusCarried.torusPermElt hU ψ σ)⁻¹ with hΦ
    have hsub : (fun y : G => fun b : T => y * (b : G) * y⁻¹) ''
        ((X ⊓ normalizer (T : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) ⊆
        Φ '' {τ : Equiv.Perm (Fin 5) | d ∘ τ = d} := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨hyXN, hyC⟩ := Subgroup.mem_inf.1 hy
      obtain ⟨σ, hσ⟩ := hψ.exists_torusPermElt_conj_eq hU hTX hyXN
      refine ⟨σ, ?_, funext fun b => (hσ b).symm⟩
      have h1 : y * t * y⁻¹ = t := by
        rw [← Subgroup.mem_centralizer_iff.1 hyC t (Set.mem_singleton t), mul_assoc,
          mul_inv_cancel, mul_one]
      have h2 := hσ ⟨t, ht⟩
      rw [h1] at h2
      set sσ : unitarySU 2 1 K 5 := ⟨permGL σ, permGL_mem_unitarySU hU σ⟩ with hsσ
      have h3 : ψ (sσ * g₀ * sσ⁻¹) = ψ g₀ := by
        apply Subtype.ext
        rw [map_mul, map_mul, map_inv]
        simpa [U52TorusCarried.torusPermElt, hsσ, hg₀t] using h2.symm
      have h5 : permGL σ * diagU d * (permGL σ)⁻¹ = diagU d := by
        rw [hdg]
        exact congrArg Subtype.val (ψ.injective h3)
      rw [permGL_conj_diagU] at h5
      have h6 := diagU_injective h5
      exact funext fun i => by simpa using (congrFun h6 (σ i)).symm
    calc 24 ≤ _ := h24
      _ ≤ _ := Set.ncard_le_ncard hsub ((Set.toFinite _).image _)
      _ ≤ _ := Set.ncard_image_le (Set.toFinite _)
  obtain ⟨I, hI4, l, ν, hlν, hv⟩ := exists_two_valued_of_stabilizer_card hK hd3 hprod hd1 h24'
  have hdI : ∀ i ∈ I, d i = l := fun i hi => by rw [hv i, if_pos hi]
  set ι : unitarySU 2 1 K 5 →* G := X.subtype.comp ψ.toMonoidHom with hι
  have hι_inj : Function.Injective ι := Subtype.val_injective.comp ψ.injective
  refine ⟨(unitaryBlock hU I).map ι, ?_, ?_⟩
  · have e : unitarySU 2 1 K I.card ≃* (unitaryBlock hU I).map ι :=
      (unitaryBlockEquiv hU I).trans ((unitaryBlock hU I).equivMapOfInjective ι hι_inj)
    have := lieModel_PSU_of_mulEquiv_unitarySU hU (by omega) (by rw [hI4]; norm_num) e
    rwa [hI4] at this
  · rintro _ ⟨A, hA, rfl⟩
    refine Subgroup.mem_inf.2 ⟨(ψ A).2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← hg₀t]
    have h1 : A * g₀ = g₀ * A :=
      Subtype.ext (by simpa [← hdg] using unitaryBlock_commute_diagU hU hdI hA)
    have h2 : ((ψ A : X) : G) * ((ψ g₀ : X) : G) = ((ψ g₀ : X) : G) * ((ψ A : X) : G) := by
      simpa using congrArg (fun z => ((ψ z : X) : G)) h1
    exact h2

end CFSG.GGQ2Prime
