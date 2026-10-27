module

public import CFSG.RankThree.GF2n.Stroth80.Sec37Action

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace Ab38

section Model

variable {K : Type} [Field K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

theorem LB_fix_b (hc : Ctx M Q Z B) {b : M₀.E}
    (hB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b)
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (t : H0 M Z) (ht : (t : G) ∈ LB M Q B) : φ t b = b := by
  obtain ⟨u, huB, huQ, hu⟩ : b ∈ M₀.img B := (hB b).mpr ⟨1, (one_smul _ b).symm⟩
  rw [← hu, ← hφπ t u huQ]
  exact (Tim79.QuadModel.comm_mem_iff (M₀ := M₀) huQ
    ((Gl37.conj_mem_Q hc (hc.LB_le_M ht)).1 u huQ)).mp (hc.comm_B_mem_Z ht huB)

end Model

end Ab38

end CFSG.RankThree.GF2n.Stroth80
