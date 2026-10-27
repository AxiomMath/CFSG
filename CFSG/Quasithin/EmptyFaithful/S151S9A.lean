module

public import CFSG.Quasithin.EmptyFaithful.SBd7Ms

public section

namespace CFSG.Quasithin.S151S9

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped Pointwise

variable {G : Type} [Group G]

theorem le_normalizer_of_char {S C T : Subgroup G} (hCS : C ≤ S)
    (hchar : (C.subgroupOf S).Characteristic) (hT : T ≤ Subgroup.normalizer (S : Set G)) :
    T ≤ Subgroup.normalizer (C : Set G) := by
  have := hchar
  have h1 := normalizer_le_normalizer_map_of_characteristic (H := S) (C.subgroupOf S)
  rw [Subgroup.map_subgroupOf_eq_of_le hCS] at h1
  exact hT.trans h1

theorem isMSPair_of_noChar [Finite G] {G₀ S K : Subgroup G} (hsqtk : IsSQTKIn G₀)
    (hchar : CharTwo G₀) (hcomp : K ∈ cComp G₀)
    (hset : (G₀ : Set G) = (K : Set G) * (S : Set G))
    (hLie : IsRankTwoLie2Derived
      ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)))
    (hsyl : IsSylowTwoOf S G₀) (hS0 : S ≠ ⊥)
    (hno : ∀ C : Subgroup G, C ≤ S → C ≠ ⊥ → (C.subgroupOf S).Characteristic →
      ¬ (G₀ ≤ Subgroup.normalizer (C : Set G))) : IsMSPair G₀ S := by
  classical
  have hSp : IsPGroup 2 ↥S := hsyl.2.1
  have hH'le : G₀ ⊓ Subgroup.normalizer (S : Set G) ≤ G₀ := inf_le_left
  have hSH' : S ≤ G₀ ⊓ Subgroup.normalizer (S : Set G) :=
    le_inf hsyl.1 Subgroup.le_normalizer
  have hchS : (S.subgroupOf S).Characteristic :=
    ⟨fun φ => by rw [Subgroup.subgroupOf_self]; exact Subgroup.comap_top _⟩
  have hlt : G₀ ⊓ Subgroup.normalizer (S : Set G) < G₀ := by
    refine lt_of_le_of_ne hH'le fun h => hno _ le_rfl hS0 hchS ?_
    calc G₀ = G₀ ⊓ Subgroup.normalizer (S : Set G) := h.symm
      _ ≤ Subgroup.normalizer (S : Set G) := inf_le_right
  have hodd : ¬ 2 ∣ (G₀ ⊓ Subgroup.normalizer (S : Set G)).relIndex G₀ := by
    intro hdvd
    apply hsyl.2.2
    have h1 := Subgroup.relIndex_mul_relIndex S (G₀ ⊓ Subgroup.normalizer (S : Set G)) G₀ hSH'
      hH'le
    have h2 : 2 ∣ S.relIndex G₀ := by
      rw [← h1]; exact Dvd.dvd.mul_left hdvd _
    exact h2
  have hcore : S = pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (S : Set G)) := by
    apply le_antisymm
    · exact le_pCoreOf_of_le_normalizer 2 hSH' (fun g hg => hg.2) hSp
    · exact pCoreOf_le_of_isSylowTwoOf (SBd7.isSylowTwoOf_of_le_of_le' hsyl hSH' hH'le)
  exact ⟨⟨hsqtk, hchar, K, hcomp, hset, hLie⟩, Or.inl ⟨_, hlt, hodd, hcore⟩, hno⟩

end CFSG.Quasithin.S151S9
