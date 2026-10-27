module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5ClassAb
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5ClassFrame

public section

namespace CFSG.StandardType.Line63.H5

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.Assembly

variable {K : Type} [Field K] {n : ℕ} {G : Type} [Group G]

theorem exists_noncomm_pair [Finite K] [Finite G] (hKd : UnitaryFieldData 2 n K)
    (hpq : 3 ∣ 2 ^ n + 1) (φ : ↥(unitarySU 2 n K 6) →* G) (hφ : Function.Injective φ)
    {B : Subgroup G} (hB : CFSG.Open.IsElemAbelian 3 B) (hBcard : Nat.card B = 3 ^ 4)
    (hSC : ∀ g ∈ Subgroup.centralizer (B : Set G), g ^ 3 = 1 → g ∈ B)
    (hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer ((φ.range : Subgroup G) : Set G) →
      IsPGroup 3 S → IsCyclic S)
    {x : G} (hxB : x ∈ B) (hx1 : x ≠ 1) (hxC : ∀ s, x * φ s = φ s * x)
    (hact : ∀ b ∈ B, ∃ M, M ∈ LargeEvenGUSet (Fin 6) K (2 ^ n) ∧ ActsAs φ b M) :
    ∃ a ∈ B, ∃ b₀ ∈ B, ∃ Ma Mb : GL (Fin 6) K, ActsAs φ a Ma ∧ ActsAs φ b₀ Mb ∧
      IsInner n Mb ∧ Ma * Mb ≠ Mb * Ma := by
  classical
  obtain ⟨MB, hMB1, hMB2, hMB⟩ := exists_actGroup hKd hpq φ hφ hB hBcard hcyc hxB hx1 hxC hact
  by_cases hfr : ∃ P ∈ primeFormUnitary hKd (idGram K 6), ∀ M ∈ MB,
      ((P⁻¹ * M * P : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).IsDiag
  · exfalso
    obtain ⟨P, hP, hPd⟩ := hfr
    exact false_of_frame hKd hpq φ hφ hBcard hSC
      (fun b hb => (hact b hb).imp fun _ h => h.2) hP
      (fun b hb M hM => hPd M (hMB1 b hb M hM))
  · obtain ⟨M₁, h₁, M₂, h₂, hne⟩ := exists_noncomm_of_noFrame hKd hpq hMB hfr
    obtain ⟨P, hP, Q, hQ, hQi, hPQ⟩ := exists_inner_noncomm hKd hpq hMB.mem_gu h₁ h₂ hne
    obtain ⟨a, haB, haP⟩ := hMB2 P hP
    obtain ⟨b₀, hbB, hbQ⟩ := hMB2 Q hQ
    exact ⟨a, haB, b₀, hbB, P, Q, haP, hbQ, hQi, hPQ⟩

theorem false_of_injective_cover_class [Finite K] [Finite G] (hKd : UnitaryFieldData 2 n K)
    (hpq : 3 ∣ 2 ^ n + 1) (φ : ↥(unitarySU 2 n K 6) →* G) (hφ : Function.Injective φ)
    {B : Subgroup G} (hB : CFSG.Open.IsElemAbelian 3 B) (hBcard : Nat.card B = 3 ^ 4)
    (hrank : LargeEvenTwoLocalRank 3 G ≤ 4)
    (hSC : ∀ g ∈ Subgroup.centralizer (B : Set G), g ^ 3 = 1 → g ∈ B)
    (hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer ((φ.range : Subgroup G) : Set G) →
      IsPGroup 3 S → IsCyclic S)
    {x : G} (hxB : x ∈ B) (hx1 : x ≠ 1) (hxC : ∀ s, x * φ s = φ s * x)
    (hact : ∀ b ∈ B, ∃ M, M ∈ LargeEvenGUSet (Fin 6) K (2 ^ n) ∧ ActsAs φ b M) : False := by
  obtain ⟨a, haB, b₀, hbB, Ma, Mb, ha, hb, hin, hne⟩ :=
    exists_noncomm_pair hKd hpq φ hφ hB hBcard hSC hcyc hxB hx1 hxC hact
  exact false_of_injective_cover hKd hpq φ hφ hB hrank hcyc hxB hx1 hxC haB hbB ha hb hin hne

end CFSG.StandardType.Line63.H5

end
