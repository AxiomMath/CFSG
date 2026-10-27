module

public import CFSG.Quasithin.H13.U4ParRecog
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSylow
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LinearAlgebra.FinTwoMatrixCharTwo
public import CFSG.Quasithin.MS93.S46TypeLin

public section

namespace CFSG.Quasithin.H13.U4Par

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin CFSG.QuasithinUnique

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

theorem chi_pow {g : hypSU h 2 0} (hg : g ∈ parP h) (n : ℕ) :
    chi h (g ^ n) = chi h g ^ n := by
  induction n with
  | zero => simp [chi_one]
  | succ n ih =>
      rw [pow_succ', chi_mul h ((parP h).pow_mem hg n), ih]
      exact (pow_succ' (chi h g) n).symm

theorem rho_pow {g : hypSU h 2 0} (hg : g ∈ parP h) (n : ℕ) :
    rho h (g ^ n) = rho h g ^ n := by
  induction n with
  | zero => simp [rho_one]
  | succ n ih =>
      rw [pow_succ', rho_mul h hg ((parP h).pow_mem hg n), ih]
      exact (pow_succ' (rho h g) n).symm

theorem rho2_pow {g : hypSU h 2 0} (hg : g ∈ parP2 h) (n : ℕ) :
    rho2 h (g ^ n) = rho2 h g ^ n := by
  induction n with
  | zero => simp [rho2_one]
  | succ n ih =>
      rw [pow_succ', rho2_mul h ((parP2 h).pow_mem hg n), ih]
      exact (pow_succ' (rho2 h g) n).symm

theorem sq_mem_radQ_of_pow_two_pow_eq_one {g : hypSU h 2 0} (hg : g ∈ parP h) {k : ℕ}
    (hk : g ^ 2 ^ k = 1) : g ^ 2 ∈ radQ h := by
  haveI : CharP K 2 := h.charP
  have hchi : chi h g = 1 := by
    have h := chi_pow h hg (2 ^ k)
    rw [hk, chi_one] at h
    exact CFSG.Quasithin.MS93.S46.eq_one_of_pow_two_pow_eq_one h.symm
  have hrho : (rho h g) ^ 2 = 1 := by
    have h := rho_pow h hg (2 ^ k)
    rw [hk, rho_one] at h
    exact CFSG.LinearAlgebra.fin_two_sq_eq_one_of_pow_two_pow_eq_one h.symm
  refine mem_radQ_of_chi_rho h ((parP h).pow_mem hg 2) ?_ ?_
  · rw [chi_pow h hg 2, hchi, one_pow]
  · rw [rho_pow h hg 2, hrho]

theorem sq_mem_radQ2_of_pow_two_pow_eq_one {g : hypSU h 2 0} (hg : g ∈ parP2 h) {k : ℕ}
    (hk : g ^ 2 ^ k = 1) : g ^ 2 ∈ radQ2 h := by
  haveI : CharP K 2 := h.charP
  have hrho : (rho2 h g) ^ 2 = 1 := by
    have h := rho2_pow h hg (2 ^ k)
    rw [hk, rho2_one] at h
    exact CFSG.LinearAlgebra.fin_two_sq_eq_one_of_pow_two_pow_eq_one h.symm
  refine mem_radQ2_of_rho2 h ((parP2 h).pow_mem hg 2) ?_
  rw [rho2_pow h hg 2, hrho]

theorem exists_sq_mem_of_lieModel {X : Type} [Group X] [Finite X] {f : ℕ}
    (hX : CFSG.Blueprint.LieModel X .PSU 4 2 f) (T : Sylow 2 X) {P : Subgroup X} (hP : P ≠ ⊤)
    (hNP : Subgroup.normalizer ((T : Subgroup X) : Set X) ≤ P) :
    ∃ Q : Subgroup X, IsPGroup 2 Q ∧ P ≤ Subgroup.normalizer (Q : Set X) ∧
      ∀ y ∈ P, (∃ k : ℕ, y ^ 2 ^ k = 1) → y ^ 2 ∈ Q := by
  obtain ⟨K, instK, h, ⟨e⟩⟩ := exists_hypSU_equiv_of_lieModel hX
  letI : Field K := instK
  haveI : Finite (hypSU h 2 0) := finite_hypSU h
  let ψ : hypSU h 2 0 →* X := e.toMonoidHom
  have hψ : Function.Injective ψ := e.injective
  have hψrange : ψ.range = ⊤ := MonoidHom.range_eq_top.mpr e.surjective
  have hT : IsSylowTwoOf (T : Subgroup X) ⊤ :=
    CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow T
  obtain ⟨ψ', hψ', hψ'range, hU⟩ :=
    exists_conj_eq_sylow h hT hψ (by rw [hψrange]; infer_instance)
  rw [hψrange, inf_top_eq] at hU
  let A : Subgroup (hypSU h 2 0) := P.comap ψ'
  have hB_le_A : hypBorel h 2 0 ≤ A := by
    intro b hb
    have hbU : b ∈ Subgroup.normalizer (hypUnitriangular h 2 0 : Set (hypSU h 2 0)) := by
      rwa [← UnitaryHigher.normalizer_hypUnitriangular h (r := 2) (ε := 0) (by norm_num)
        (by norm_num)] at hb
    have hψb : ψ' b ∈ Subgroup.normalizer ((T : Subgroup X) : Set X) := by
      have h := Subgroup.le_normalizer_map (H := hypUnitriangular h 2 0) ψ'
        (Subgroup.mem_map_of_mem ψ' hbU)
      rwa [hU] at h
    exact hNP hψb
  have hP_le_range : P ≤ ψ'.range := by rw [hψ'range, hψrange]; exact le_top
  have hA_ne_top : A ≠ ⊤ := by
    intro hAtop
    apply hP
    rw [← Subgroup.map_comap_eq_self hP_le_range]
    change Subgroup.map ψ' A = ⊤
    rw [hAtop, Subgroup.map_top, hψ'range, hψrange]
  obtain ⟨A', hA'coat, hAA'⟩ :=
    (IsCoatomic.eq_top_or_exists_le_coatom A).resolve_left hA_ne_top
  have hBA' : hypBorel h 2 0 ≤ A' := hB_le_A.trans hAA'
  have hPA' : P ≤ A'.map ψ' := by
    rw [← Subgroup.map_comap_eq_self hP_le_range]
    exact Subgroup.map_mono hAA'
  rcases eq_parP_or_eq_parP2 h hA'coat hBA' with hA'P | hA'P2
  · refine ⟨(radQ h).map ψ', IsPGroup.map (radQ_isPGroup h) ψ', ?_, ?_⟩
    · calc P ≤ A'.map ψ' := hPA'
        _ = (parP h).map ψ' := by rw [hA'P]
        _ ≤ (Subgroup.normalizer (radQ h : Set (hypSU h 2 0))).map ψ' :=
            Subgroup.map_mono (parP_le_normalizer_radQ h)
        _ ≤ Subgroup.normalizer (((radQ h).map ψ' : Subgroup X) : Set X) :=
            Subgroup.le_normalizer_map (H := radQ h) ψ'
    · intro y hy hy2
      obtain ⟨k, hk⟩ := hy2
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp (hPA' hy)
      have hxP : x ∈ parP h := by rwa [hA'P] at hx
      have hxk : x ^ 2 ^ k = 1 := hψ' (by rw [map_pow, hk, map_one])
      have hx2 : x ^ 2 ∈ radQ h := sq_mem_radQ_of_pow_two_pow_eq_one h hxP hxk
      rw [← map_pow]
      exact Subgroup.mem_map_of_mem ψ' hx2
  · refine ⟨(radQ2 h).map ψ', IsPGroup.map (radQ2_isPGroup h) ψ', ?_, ?_⟩
    · calc P ≤ A'.map ψ' := hPA'
        _ = (parP2 h).map ψ' := by rw [hA'P2]
        _ ≤ (Subgroup.normalizer (radQ2 h : Set (hypSU h 2 0))).map ψ' :=
            Subgroup.map_mono (parP2_le_normalizer_radQ2 h)
        _ ≤ Subgroup.normalizer (((radQ2 h).map ψ' : Subgroup X) : Set X) :=
            Subgroup.le_normalizer_map (H := radQ2 h) ψ'
    · intro y hy hy2
      obtain ⟨k, hk⟩ := hy2
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp (hPA' hy)
      have hxP : x ∈ parP2 h := by rwa [hA'P2] at hx
      have hxk : x ^ 2 ^ k = 1 := hψ' (by rw [map_pow, hk, map_one])
      have hx2 : x ^ 2 ∈ radQ2 h := sq_mem_radQ2_of_pow_two_pow_eq_one h hxP hxk
      rw [← map_pow]
      exact Subgroup.mem_map_of_mem ψ' hx2

end CFSG.Quasithin.H13.U4Par
