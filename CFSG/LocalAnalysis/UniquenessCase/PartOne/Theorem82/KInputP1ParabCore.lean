module

public import CFSG.LieType.SteinbergBRTriangularSolvable
public import CFSG.LocalAnalysis.AGLEmbedding.LinearThreeKitParab
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputP1ParabComm
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputP1ParabLevi

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.AGLEmbedding.LinearThreeKit
  CFSG.AGLEmbedding CFSG.QuasithinUnique
open scoped commutatorElement

theorem isSolvable_map {G G' : Type*} [Group G] [Group G'] (f : G →* G') (B : Subgroup G)
    [Group.IsSolvable B] : Group.IsSolvable (B.map f) :=
  Group.isSolvable_of_surjective (f := f.subgroupMap B) (f.subgroupMap_surjective B)

theorem isSolvable_normalizer_sylow {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}
    (hf : Nat.card K = 2 ^ f) (T : Sylow 2 (projectiveSL 3 K)) :
    Group.IsSolvable ↥(Subgroup.normalizer ((T : Subgroup (projectiveSL 3 K)) :
      Set (projectiveSL 3 K))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, -, -, hg, -⟩ := exists_eq_map_conj_flagStabilizer 2 (n := 3) (by norm_num) T ⊤ le_top
  haveI : Group.IsSolvable (upperTriangular 3 K) :=
    CFSG.LieType.SteinbergBR.isSolvable_upperTriangular_of_card Nat.prime_two hf 3
  haveI : Group.IsSolvable ↥(projUpperTriangular 3 K) :=
    isSolvable_map (proj 3 K) (upperTriangular 3 K)
  rw [hg]
  exact isSolvable_map _ _

theorem hasOffender_projectiveSL (hD : DicksonSL2) {K : Type} [Field K] [Finite K] [CharP K 2]
    {f : ℕ} (hf : Nat.card K = 2 ^ f) (hodd : Odd f) {J H : Subgroup (projectiveSL 3 K)}
    (hJ : J ≠ ⊤) (hpar : IsParabolicTwo ⊤ J) (hHJ : H ≤ J) (hH : ⁅H, H⁆ = H) (hne : H ≠ ⊥) :
    HasOffender J H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, T, hT, hNT⟩ := hpar
  have hNJ : Subgroup.normalizer (T : Set (projectiveSL 3 K)) ≤ J := by
    rwa [top_inf_eq] at hNT
  by_cases heq : J = Subgroup.normalizer (T : Set (projectiveSL 3 K))
  · have hsolv := isSolvable_normalizer_sylow hf (sylowOfTopTwo hT)
    rw [coe_sylowOfTopTwo hT, ← heq] at hsolv
    haveI := hsolv
    exact absurd (eq_bot_of_perfect_of_le_solvable hHJ hH) hne
  · obtain ⟨g, d, hd, hJg⟩ :=
      eq_map_conj_projStabilizer_of_sylow 2 (sylowOfTopTwo hT) J hNJ heq hJ
    set e : projectiveSL 3 K ≃* projectiveSL 3 K := (MulAut.conj g).symm with he
    have hJe : J.map e.toMonoidHom = projStabilizer (flagSpace 3 K d) := by
      rw [hJg, Subgroup.map_map]
      convert Subgroup.map_id (projStabilizer (flagSpace 3 K d))
      ext x
      simp [he]
    have hHe : H.map e.toMonoidHom ≤ projStabilizer (flagSpace 3 K d) :=
      hJe ▸ Subgroup.map_mono hHJ
    have hHperf : ⁅H.map e.toMonoidHom, H.map e.toMonoidHom⁆ = H.map e.toMonoidHom := by
      rw [← Subgroup.map_commutator, hH]
    have hHne : H.map e.toMonoidHom ≠ ⊥ := fun h =>
      hne ((Subgroup.map_eq_bot_iff_of_injective H e.injective).mp h)
    obtain ⟨r, hr, h5, hrH, hrK⟩ :=
      exists_prime_of_perfect_parabolic hD hf hodd hd hHe hHperf hHne
    obtain ⟨g₀, hg₀, hord, hcomm⟩ := exists_levi_central hd hr h5 hrK
    refine HasOffender.of_map_mulEquiv e ?_
    rw [hJe]
    exact ⟨g₀, hg₀, r, hr, h5, hord, hrH, fun k hk => hcomm k (hHe hk)⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
