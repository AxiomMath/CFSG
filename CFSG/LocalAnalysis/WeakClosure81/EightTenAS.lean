module

public import CFSG.LocalAnalysis.WeakClosure81.EightTenPrimeAS
public import CFSG.Adapters.LieModelSimple
public import CFSG.LocalAnalysis.WeakClosure81.EightTenAux

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
  (IsL2 IsSz IsL3 IsU3 IsSp4 IsU4 IsU5 IsOmega8m Is3D4 IsAlt IsSL3 Bar2 OInf Opp)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)

variable {G : Type} [Group G] [Finite G]

private theorem HasQuotShape.mono' {K : Subgroup G} {N : Set G}
    {P Q : ∀ (X : Type) [Group X], Prop} (h : HasQuotShape K N P)
    (hPQ : ∀ (X : Type) [Group X], P X → Q X) : HasQuotShape K N Q := by
  obtain ⟨X, hX, φ, hφ, hker, hP⟩ := h
  exact ⟨X, hX, φ, hφ, hker, hPQ X hP⟩

theorem MinCex88.eight_ten_AS {V H T : Subgroup G} {i : ℕ}
    (h5_11 : Asch5_11AS) (h5_13 : Asch5_13AS) (h : MinCex88 V H T i) :
    InFSqAS 1 H ∨
      ((CFSG.Open.pRank 3 H ≤ 3 ∧ ∀ p : ℕ, p.Prime → p ≠ 2 → 3 < CFSG.Open.pRank p H →
          CFSG.Open.pRank p (H ⊓ normalizer (V : Set G)) ≤ 1) ∧
        InFSqAS 2 H ∧ ∃ L : Subgroup G, IsComponentModN (kerMV V H) H L ∧
          HasQuotShape L (kerMV V H : Set G) (fun X _ => IsSimpleGroup X) ∧ L ⊔ T = H ∧
          (HasQuotShape L (kerMV V H : Set G) (fun X _ => IsL2 X 2) ∨
            HasQuotShape L (kerMV V H : Set G) (fun X _ => IsU3 X 2) ∨
            ((HasQuotShape L (kerMV V H : Set G) (fun X _ => IsL3 X 2) ∨
                HasQuotShape L (kerMV V H : Set G) (fun X _ => IsSp4 X 2)) ∧
              ∃ t ∈ T ⊓ normalizer (L : Set G), ActsOnDynkinMod (kerMV V H) L t))) := by
  by_cases h1 : Concl881 V H
  · have h2 : ¬ Concl882 V H := fun h2 => h.fail ⟨h1, h2⟩
    obtain ⟨hK, hT, hTlt, hno, hne, hp⟩ := h.hyps_5_11 h2
    obtain ⟨-, hcase⟩ := h5_11 G H T hK hT hTlt hno hne hp
    rcases hcase with h11 | ⟨h22, L, hL, hLT, hshape⟩
    · exact Or.inl h11
    · right
      obtain ⟨h3, hpp, -⟩ := not_concl882_iff.mp h2
      have hKer : OInf H = kerMV V H :=
        oInf_eq_kerMV hT (MinCex88.calNIn_eq_AS h5_11 h5_13 h) ⟨L, hL, hLT⟩
      rw [hKer] at hL hshape
      refine ⟨⟨h3, hpp⟩, h22, L, hL, ?_, hLT, ?_⟩
      · rcases hshape with hs | hs | ⟨hs | hs, -⟩
        · exact hs.mono' fun X _ hX => CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags
            (by decide) hX
        · exact hs.mono' fun X _ hX => CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags
            (by decide) hX
        · exact hs.mono' fun X _ hX => CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags
            (by decide) hX
        · exact hs.mono' fun X _ hX => CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags
            (by decide) hX
      · rcases hshape with hs | hs | ⟨hs, t, ht, hact⟩
        · exact Or.inl hs
        · exact Or.inr (Or.inl hs)
        · exact Or.inr (Or.inr ⟨hs, t, Subgroup.mem_inf.mpr ⟨ht, hact.1⟩, hact⟩)
  · left
    obtain ⟨hK, hT, hTlt, h3, hno, hne⟩ := h.hyps_5_13 h1
    obtain ⟨-, hcase⟩ := h5_13 G H T hK hT hTlt h3 hno hne
    rcases hcase with h11 | ⟨n, hn, hshape⟩
    · exact h11
    · exact absurd hshape (h.not_fStar_shape_AS h5_11 h5_13 h1 n hn)

end CFSG.LocalAnalysis.WeakClosure81

end
