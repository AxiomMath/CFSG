module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K45Setup
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.UC46

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {D : Subgroup G}

private theorem commutator_conjugatesOfSet_le_normalClosure (N : Subgroup G) [N.Normal] :
    ∀ a ∈ N, ∀ y ∈ Group.conjugatesOfSet (D : Set G),
      ⁅a, y⁆ ∈ normalClosure ((⁅N, D⁆ : Subgroup G) : Set G) := by
  intro a ha y hy
  obtain ⟨d, hd, hconj⟩ := Group.mem_conjugatesOfSet_iff.1 hy
  obtain ⟨c, rfl⟩ := isConj_iff.1 hconj
  have hca : c⁻¹ * a * c ∈ N := by
    simpa using (inferInstance : N.Normal).conj_mem a ha c⁻¹
  have hmem : ⁅c⁻¹ * a * c, d⁆ ∈ (⁅N, D⁆ : Subgroup G) :=
    Subgroup.commutator_mem_commutator hca hd
  have hconjmem : c * ⁅c⁻¹ * a * c, d⁆ * c⁻¹ ∈
      normalClosure ((⁅N, D⁆ : Subgroup G) : Set G) :=
    (inferInstance : (normalClosure ((⁅N, D⁆ : Subgroup G) : Set G)).Normal).conj_mem _
      (Subgroup.subset_normalClosure hmem) c
  have harg : c * (c⁻¹ * a * c) * c⁻¹ = a := by group
  have hgoal : c * ⁅c⁻¹ * a * c, d⁆ * c⁻¹ = ⁅a, c * d * c⁻¹⁆ := by
    rw [conjugate_commutatorElement (c⁻¹ * a * c) d c, harg]
  rwa [hgoal] at hconjmem

theorem commutator_top_eq_normalClosure {N : Subgroup G} [N.Normal]
    (hgen : normalClosure (D : Set G) = ⊤) :
    ⁅N, (⊤ : Subgroup G)⁆ = normalClosure ((⁅N, D⁆ : Subgroup G) : Set G) := by
  apply le_antisymm
  · rw [← hgen]
    exact TauCeti.commutator_closure_le_iff.mpr
      (commutator_conjugatesOfSet_le_normalClosure (G := G) (D := D) N)
  · have hle : ((⁅N, D⁆ : Subgroup G) : Set G) ⊆
        ((⁅N, (⊤ : Subgroup G)⁆ : Subgroup G) : Set G) :=
      Subgroup.commutator_mono_right (H := N) (le_top : D ≤ (⊤ : Subgroup G))
    exact Subgroup.normalClosure_le_normal (s := ((⁅N, D⁆ : Subgroup G) : Set G)) hle

private theorem commutator_idem_pPrimeCore_three (hD : Nat.card D = 3) :
    ⁅⁅CFSG.pPrimeCore 3 G, D⁆, D⁆ = ⁅CFSG.pPrimeCore 3 G, D⁆ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : (CFSG.pPrimeCore 3 G).Normal := CFSG.pPrimeCore_normal
  have hD3 : IsPGroup 3 D := IsPGroup.of_card (n := 1) (by rw [hD]; norm_num)
  have hcop : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore 3 G) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (CFSG.pPrimeCore_coprime_card (p := 3) (G := G))
  have hnorm : D ≤ Subgroup.normalizer (CFSG.pPrimeCore 3 G : Set G) := by
    rw [Subgroup.normalizer_eq_top_iff.2 (inferInstance : (CFSG.pPrimeCore 3 G).Normal)]
    exact le_top
  exact CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 3 Nat.prime_three
    D (CFSG.pPrimeCore 3 G) hD3 hcop hnorm

theorem kof_commutator_top (hD : Nat.card D = 3) (hgen : normalClosure (D : Set G) = ⊤) :
    ⁅Kof G, (⊤ : Subgroup G)⁆ = Kof G := by
  have hidem : ⁅⁅CFSG.pPrimeCore 3 G, D⁆, D⁆ = ⁅CFSG.pPrimeCore 3 G, D⁆ :=
    commutator_idem_pPrimeCore_three (G := G) (D := D) hD
  have hK : Kof G = normalClosure ((⁅CFSG.pPrimeCore 3 G, D⁆ : Subgroup G) : Set G) :=
    commutator_top_eq_normalClosure (N := CFSG.pPrimeCore 3 G) (D := D) hgen
  have hAK : (⁅CFSG.pPrimeCore 3 G, D⁆ : Subgroup G) ≤ Kof G := by
    rw [hK]
    exact Subgroup.le_normalClosure
  have hAle : (⁅CFSG.pPrimeCore 3 G, D⁆ : Subgroup G) ≤ ⁅Kof G, (⊤ : Subgroup G)⁆ := by
    calc (⁅CFSG.pPrimeCore 3 G, D⁆ : Subgroup G)
        = ⁅⁅CFSG.pPrimeCore 3 G, D⁆, D⁆ := hidem.symm
      _ ≤ ⁅Kof G, D⁆ := Subgroup.commutator_mono hAK le_rfl
      _ ≤ ⁅Kof G, (⊤ : Subgroup G)⁆ := Subgroup.commutator_mono_right (H := Kof G) le_top
  exact le_antisymm (Subgroup.commutator_le_left (Kof G) (⊤ : Subgroup G))
    (hK.le.trans (Subgroup.normalClosure_le_normal hAle))

theorem uc45_X_gen (hD : Nat.card D = 3) (hgen : normalClosure (D : Set G) = ⊤)
    (hKX : Kof G = Xof G) : normalClosure (Tof G D : Set G) = Xof G := by
  have hK : ⁅Kof G, (⊤ : Subgroup G)⁆ = Kof G := kof_commutator_top hD hgen
  have hX : ⁅Xof G, (⊤ : Subgroup G)⁆ = normalClosure ((⁅Xof G, D⁆ : Subgroup G) : Set G) :=
    commutator_top_eq_normalClosure (N := Xof G) (D := D) hgen
  calc normalClosure (Tof G D : Set G)
      = normalClosure ((⁅Xof G, D⁆ : Subgroup G) : Set G) := rfl
    _ = ⁅Xof G, (⊤ : Subgroup G)⁆ := hX.symm
    _ = ⁅Kof G, (⊤ : Subgroup G)⁆ := by rw [hKX]
    _ = Kof G := hK
    _ = Xof G := hKX

end CFSG.LocalAnalysis.UniquenessCase.UCK.UC46
