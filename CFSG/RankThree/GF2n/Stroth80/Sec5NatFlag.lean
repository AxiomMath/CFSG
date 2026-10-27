module

public import CFSG.RankThree.GF2n.Stroth80.Sec5NatBridge
public import CFSG.ClassicalGroups.Symplectic.PointRadicalFlag

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.ClassicalGroups.Symplectic CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.F2Fixed
  CFSG.Open
open CFSG.ClassicalGroups.Alternating (Lsp)
open QuadraticMap
open Matrix

variable {G : Type} [Group G]

section Sp

variable {m : ℕ} {K : Type} [Field K] {R N L : Subgroup G}

theorem map_subgroupOf_eq_LspGL_of_flag (φ : ↥R →* GL (Fin m ⊕ Fin m) K)
    (hφ : φ.range = StatedSp m K) (hNφ : φ.ker = N.subgroupOf R) (hN : N ≤ R) (hL : L ≤ R)
    {u : Fin m ⊕ Fin m → K} (hu : u ≠ 0)
    (h : ∀ r : ↥R, (r : G) ∈ L ⊔ N ↔
      (φ r).val *ᵥ u = u ∧ (∀ x, spForm m K x u = 0 → ∃ c : K, (φ r).val *ᵥ x - x = c • u) ∧
        ∀ x, spForm m K ((φ r).val *ᵥ x - x) u = 0) :
    (L.subgroupOf R).map φ = LspGL m K u := by
  have hle : LspGL m K u ≤ φ.range := by
    rw [hφ]
    exact LspGL_le_statedSp u
  refine map_subgroupOf_eq_of_mem_sup_iff φ hNφ hN hL hle (fun r => ?_)
  rw [h r, mem_LspGL_iff_flag hu]
  have hr : φ r ∈ StatedSp m K := hφ ▸ MonoidHom.mem_range.mpr ⟨r, rfl⟩
  exact ⟨fun hh => ⟨hr, hh⟩, fun hh => hh.2⟩

end Sp

section Omega

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
  {Q : QuadraticForm K (ι → K)} {X : Subgroup (GL ι K)} {R N L : Subgroup G}

theorem map_subgroupOf_eq_LomGL_of_flag (E : ElemMatrixIso Q X)
    (hQ : (polarBilin Q).Nondegenerate) (φ : ↥R →* GL ι K) (hφ : φ.range = X)
    (hNφ : φ.ker = N.subgroupOf R) (hN : N ≤ R) (hL : L ≤ R) {u : ι → K} (hu : Q u = 0)
    (hu0 : u ≠ 0)
    (h : ∀ r : ↥R, (r : G) ∈ L ⊔ N ↔
      (φ r : Matrix ι ι K) *ᵥ u = u ∧
        (∀ x, polar Q u x = 0 → ∃ c : K, (φ r : Matrix ι ι K) *ᵥ x - x = c • u) ∧
          ∀ x, polar Q u ((φ r : Matrix ι ι K) *ᵥ x - x) = 0) :
    (L.subgroupOf R).map φ = E.LomGL u := by
  have hle : E.LomGL u ≤ φ.range := by
    rw [hφ]
    intro A hA
    exact ((E.mem_LomGL_iff_flag hQ hu hu0).mp hA).1
  refine map_subgroupOf_eq_of_mem_sup_iff φ hNφ hN hL hle (fun r => ?_)
  rw [h r, E.mem_LomGL_iff_flag hQ hu hu0]
  have hr : φ r ∈ X := hφ ▸ MonoidHom.mem_range.mpr ⟨r, rfl⟩
  exact ⟨fun hh => ⟨hr, hh⟩, fun hh => hh.2⟩

end Omega

end CFSG.RankThree.GF2n.Stroth80
