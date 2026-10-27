module

public import CFSG.LocalAnalysis.WeakClosure81.W183TwoCtx
public import CFSG.LocalAnalysis.WeakClosure81.W183TwoSec
public import CFSG.LocalAnalysis.WeakClosure81.W183TwoKStar

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}

theorem tail1812Two_kstar (hB : ListBNonabelian) {g : G} (cx : Tail1812TwoCtx G D V₀ V H i g)
    (hM : OddMultiplier186Triv) {L : Subgroup G} (hL : IsComponentModN (kerMV V H) H L)
    {X : Type} [Group X] [IsSimpleGroup X] (hnc : ∃ u v : X, u * v ≠ v * u)
    (hS : Shape186OddTriv X) (φ : ↥L →* X) (hφs : Function.Surjective φ)
    (hφk : ∀ k : ↥L, φ k = 1 ↔ (k : G) ∈ kerMV V H) :
    kerMV V H ≤ Subgroup.centralizer (eOmegaZ H D.T : Set G) := by
  classical
  obtain ⟨Y, _, _, π, a₁, Kk, P, hset⟩ := tail1812Two_exists_setting hB cx
  obtain ⟨φ', hφ's, hφ'k, hLc⟩ :=
    tail1812Two_exists_section hL hset.surj hset.ker_le hset.mem_kk φ hφs hφk
  have hKk : Kk = ⊥ :=
    kk_eq_bot_of_component hM hset.kk_normal hset.p_normal hset.kk_le_p hset.kk_central
      hset.kk_odd hset.two_quot hset.le_of_not_le hLc hnc hS φ' hφ's hφ'k
  intro k hk
  have hkH : k ∈ H := kerMV_le_self V H hk
  have hkK : π ⟨k, hkH⟩ ∈ Kk := (hset.mem_kk ⟨k, hkH⟩).2 hk
  have hk1 : π ⟨k, hkH⟩ = 1 := by
    rw [hKk] at hkK
    simpa using hkK
  exact (hset.ker_iff ⟨k, hkH⟩).1 hk1

end CFSG.LocalAnalysis.WeakClosure81

end
