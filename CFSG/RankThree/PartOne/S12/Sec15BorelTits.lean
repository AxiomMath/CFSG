module

public import CFSG.Milestones.CL_LIT_Borel_Tits_local_parabolic
import CFSG.RankThree.PartOne.S12.Sec12FusSyl
import CFSG.RankThree.PartOne.S10.AmbientTheta

public section

namespace CFSG.RankThree.PartOne

open CFSG

theorem borelTits_normalizer_parabolic
    {X : Type} [Group X] [Finite X] {t : Assembly.LowTwoRank.StatedLieTag} {n r f : ℕ}
    (hr : r.Prime) (hmodel : Blueprint.LieModel X t n r f) {S : Subgroup X} (hS : S ≠ ⊥)
    (hSr : IsPGroup r S) (hcore : Open.pCoreOf r (Subgroup.normalizer (S : Set X)) = S) :
    Subgroup.normalizer (S : Set X) ≠ ⊤ ∧ ∃ S₀ : Sylow r X,
      (t ≠ .Tits →
        Subgroup.normalizer ((S₀ : Subgroup X) : Set X) ≤ Subgroup.normalizer (S : Set X)) ∧
      (t = .Tits → (S₀ : Subgroup X) ≤ Subgroup.normalizer (S : Set X)) := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨S₀, P, hP, hNP, -, hSP, hS1, hS2⟩ :=
    Milestones.cl_lit_borel_tits_local_parabolic_all_models X t n r f hmodel S hS hSr
  have hRp : IsPGroup r (Open.pCoreOf r P) := LieType.BorelTits.pCoreOf_isPGroup r P
  have hRP : P ≤ Subgroup.normalizer ((Open.pCoreOf r P : Subgroup X) : Set X) :=
    LieType.BorelTits.le_normalizer_pCoreOf r P
  have hRN : Open.pCoreOf r P ⊓ Subgroup.normalizer (S : Set X) ≤ S := by
    have h := LieType.BorelTits.le_pCoreOf_of_le_normalizer r (inf_le_right :
        Open.pCoreOf r P ⊓ Subgroup.normalizer (S : Set X) ≤ Subgroup.normalizer (S : Set X))
      (le_normalizer_inf_of_le_normalizer (hNP.trans hRP) Subgroup.le_normalizer)
      (hRp.to_le inf_le_left)
    rwa [hcore] at h
  have hSR : S ≤ Open.pCoreOf r P := hSP
  have hSReq : S = Open.pCoreOf r P := by
    by_contra hne
    obtain ⟨y, hyR, hyS, hyN⟩ := Sec12Fus.exists_mem_normalizer_sdiff hSR hRp hne
    exact hyS (hRN ⟨hyR, hyN⟩)
  have hPN : P ≤ Subgroup.normalizer (S : Set X) := by
    rw [hSReq]
    exact hRP
  have hNPeq : Subgroup.normalizer (S : Set X) = P := le_antisymm hNP hPN
  refine ⟨by rw [hNPeq]; exact hP, S₀, fun ht => hNPeq ▸ hS1 ht, fun ht => hNPeq ▸ hS2 ht⟩

end CFSG.RankThree.PartOne
