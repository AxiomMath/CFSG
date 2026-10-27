module

public import CFSG.LocalAnalysis.StandardType.GGHalfCentAlign
public import CFSG.LocalAnalysis.StandardType.GGHalfCentSupp
public import CFSG.LocalAnalysis.StandardType.GGHalfCentDefs
public import CFSG.LocalAnalysis.StandardType.GGHalfCentStruct
public import CFSG.LocalAnalysis.StandardType.GGHalfCentComp
public import CFSG.LocalAnalysis.StandardType.GGHalfCentCard
public import CFSG.LocalAnalysis.StandardType.GGHalfCentGroup

public section

namespace CFSG.StandardType.GGHalf

open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial Matrix

private theorem disjoint_map_conj {G : Type*} [Group G] {X Y : Subgroup G} (hXY : Disjoint X Y)
    (g : G) : Disjoint (conjSub g X) (conjSub g Y) := by
  rw [Subgroup.disjoint_def]
  rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
  have hba : b = a := (MulAut.conj g).injective hab
  subst hba
  rw [Subgroup.disjoint_def.mp hXY ha hb, map_one]

theorem centralizer_blocks {n : ℕ} {t : SpecialLinearGroup (Fin (n + 1)) F2} (ht3 : t ^ 3 = 1) :
    ∃ Z Λ : Subgroup (SpecialLinearGroup (Fin (n + 1)) F2),
      Nat.card Z = Nat.card (SpecialLinearGroup (Fin (n + 1 - supp t)) F2) ∧
      Nat.card Λ = Nat.card (SpecialLinearGroup (Fin (supp t / 2)) (GaloisField 2 2)) ∧
      Disjoint Z Λ ∧
      (3 ≤ n + 1 - supp t →
        IsComponentOf Z (Subgroup.centralizer ({t} : Set (SpecialLinearGroup (Fin (n + 1)) F2)))) ∧
      (2 ≤ supp t / 2 →
        IsComponentOf Λ (Subgroup.centralizer ({t} : Set (SpecialLinearGroup (Fin (n + 1)) F2)))) ∧
      (∀ J : Subgroup (SpecialLinearGroup (Fin (n + 1)) F2),
        IsComponentOf J (Subgroup.centralizer ({t} : Set (SpecialLinearGroup (Fin (n + 1)) F2))) →
          J = Z ∨ J = Λ) := by
  obtain ⟨s, r, ε, A₀, k, htk⟩ := exists_frame_of_pow_three t ht3
  obtain ⟨M, k', hMk, hk'⟩ := exists_conj_nsSL_binary ε k
  have hbin : ∀ i, k' i = 0 ∨ k' i = 1 := fun i => (hk' i).1
  set Y' := SLNS.nsSL ε det_rootMat_phi3 k' with hY'
  set A : SpecialLinearGroup (Fin (n + 1)) F2 := A₀ * M with hA
  have hY : SLNS.nsSL ε det_rootMat_phi3 k = M * Y' * M⁻¹ := by
    rw [← hMk]
    group
  have htA : t = A * Y' * A⁻¹ := by
    rw [htk, hY, hA]
    group
  have hsupp : supp t = 2 * ones k' := by
    rw [htA, supp_conj, supp_nsSL, ones]
    congr 2
    refine Finset.filter_congr fun i _ => ?_
    rcases hbin i with h | h <;> simp [h]
  have hcent : Subgroup.centralizer ({t} : Set (SpecialLinearGroup (Fin (n + 1)) F2)) =
      conjSub A (Subgroup.centralizer ({Y'} : Set (SpecialLinearGroup (Fin (n + 1)) F2))) := by
    rw [htA]
    exact (map_conj_centralizer_singleton A Y').symm
  refine ⟨conjSub A (zeroBlk ε k'), conjSub A (classBlk ε k'), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [card_conjSub, natCard_zeroBlk ε k' hbin, hsupp]
  · have hsupp2 : supp t / 2 = ones k' := by omega
    rw [card_conjSub, natCard_classBlk ε k' hbin, hsupp2]
  · exact disjoint_map_conj (disjoint_zeroBlk_classBlk ε k') A
  · intro h3
    rw [hcent]
    exact isComponentOf_map_conj (isComponentOf_zeroBlk ε k' hbin (by omega)) A
  · intro h2
    rw [hcent]
    exact isComponentOf_map_conj (isComponentOf_classBlk ε k' hbin (by omega)) A
  · intro J hJ
    have hJ' : IsComponentOf (conjSub A⁻¹ J)
        (Subgroup.centralizer ({Y'} : Set (SpecialLinearGroup (Fin (n + 1)) F2))) := by
      have h := isComponentOf_map_conj hJ A⁻¹
      rw [hcent] at h
      change IsComponentOf (conjSub A⁻¹ J) (conjSub A⁻¹ (conjSub A _)) at h
      rwa [conjSub_inv_conjSub] at h
    have hJJ : J = conjSub A (conjSub A⁻¹ J) := (conjSub_conjSub_inv A J).symm
    rcases comp_eq_zeroBlk_or_classBlk ε k' hbin hJ' with h | h
    · left
      rw [hJJ, h]
    · right
      rw [hJJ, h]

theorem layer_centralizer_not_component {n : ℕ} {t : SpecialLinearGroup (Fin (n + 1)) F2}
    (ht : t ∈ halfTorus n) (hr : 4 ≤ supp t) (hfix : 3 ≤ n + 1 - supp t) :
    ¬ ∃ J : Subgroup (SpecialLinearGroup (Fin (n + 1)) F2),
      J = LargeEvenLayer (Subgroup.centralizer ({t} : Set (SpecialLinearGroup (Fin (n + 1)) F2))) ∧
        IsComponentOf J (Subgroup.centralizer ({t} : Set _)) := by
  obtain ⟨Z, Λ, -, -, hdisj, hZc, hΛc, -⟩ := centralizer_blocks (halfTorus_pow_three ht)
  have hZ := hZc hfix
  have hΛ := hΛc (by omega)
  have hne : Z ≠ Λ := by
    intro h
    subst h
    exact ne_bot_of_isComponentOf hZ (disjoint_self.mp hdisj)
  exact layer_ne_component_of_two_components hZ hΛ hne

theorem card_component_centralizer {n : ℕ} {t : SpecialLinearGroup (Fin (n + 1)) F2}
    (ht : t ∈ halfTorus n) (ht1 : t ≠ 1)
    {J : Subgroup (SpecialLinearGroup (Fin (n + 1)) F2)}
    (hJ : IsComponentOf J (Subgroup.centralizer ({t} : Set (SpecialLinearGroup (Fin (n + 1)) F2)))) :
    Nat.card J = Nat.card (SpecialLinearGroup (Fin (supp t / 2)) (GaloisField 2 2)) ∨
      Nat.card J = Nat.card (SpecialLinearGroup (Fin (n + 1 - supp t)) F2) := by
  obtain ⟨Z, Λ, hZ, hΛ, -, -, -, hcomp⟩ := centralizer_blocks (halfTorus_pow_three ht)
  rcases hcomp J hJ with rfl | rfl
  · right
    exact hZ
  · left
    exact hΛ

end CFSG.StandardType.GGHalf

end
