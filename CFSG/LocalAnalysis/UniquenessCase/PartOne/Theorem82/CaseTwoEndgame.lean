module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoPairs
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoNormalizerA
import CFSG.LocalAnalysis.StronglyEmbedded.OfCentralizers

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

variable {G : Type} [Group G] [Finite G]

namespace CaseTwoTransitive

variable {c : Ctx812E G} (t : CaseTwoTransitive c)

theorem false_of_centralizer_le {p : ℕ} (hp : p ∈ c.sig) (hN : t.PairNormalizerLe p)
    (hA : ∀ x ∈ t.d.AA, x ≠ 1 → Subgroup.centralizer ({x} : Set G) ≤ c.S.M)
    (hy : Subgroup.centralizer ({t.y} : Set G) ≤ c.S.M) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSP : t.d.S ≤ t.P := by
    rw [t.hdS]
    exact inf_le_left
  have hP1 : t.P ≠ ⊥ := by
    intro hbot
    have hy1 : t.y = 1 := by simpa [hbot] using t.hyP
    have h3 := t.orderOf_y
    rw [hy1, orderOf_one] at h3
    omega
  refine c.not_strong
    (CFSG.RankThree.PartOne.isStronglyPEmbedded_of_normalizer_sylow_le c.M_ne_top t.hP hP1
      (t.normalizer_P_le hp hN) fun x hxP hx => ?_)
  have hx3 : x ^ 3 = 1 := by
    rw [← hx]
    exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    omega
  rcases t.mem_AA_or_exists_conj_eq hxP hx3 with hxA | ⟨s, hsS, hs⟩
  · exact hA x hxA hx1
  ·
    have hsM : s ∈ c.S.M := t.hP.le (hSP hsS)
    have hys : Subgroup.centralizer ({s * x * s⁻¹} : Set G) ≤ c.S.M := by
      rcases hs with hs | hs <;> rw [hs]
      · exact hy
      · intro g hg
        refine hy (Subgroup.mem_centralizer_singleton_iff.mpr ?_)
        have hg' : g * t.y⁻¹ = t.y⁻¹ * g := Subgroup.mem_centralizer_singleton_iff.mp hg
        calc g * t.y = t.y * (t.y⁻¹ * g) * t.y := by group
          _ = t.y * (g * t.y⁻¹) * t.y := by rw [← hg']
          _ = t.y * g := by group
    intro g hg
    have hconj : s * g * s⁻¹ ∈ Subgroup.centralizer ({s * x * s⁻¹} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
      calc s * g * s⁻¹ * (s * x * s⁻¹) = s * (g * x) * s⁻¹ := by group
        _ = s * (x * g) * s⁻¹ := by rw [hg]
        _ = s * x * s⁻¹ * (s * g * s⁻¹) := by group
    have hgM := c.S.M.mul_mem (c.S.M.mul_mem (c.S.M.inv_mem hsM) (hys hconj)) hsM
    have heq : s⁻¹ * (s * g * s⁻¹) * s = g := by group
    rwa [heq] at hgM

end CaseTwoTransitive

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
