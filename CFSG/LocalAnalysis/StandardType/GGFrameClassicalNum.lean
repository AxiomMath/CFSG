module

public import CFSG.LocalAnalysis.StandardType.GGFrameModelNumSigned
public import CFSG.LocalAnalysis.StandardType.GGFrameModelNumPerm
public import CFSG.LocalAnalysis.StandardType.GGFrameModelNumSumZero

public section

namespace CFSG.StandardType.FrameRoute

open CFSG SpCoord UCoord Multiplicative

variable {G : Type} [Group G] {A : Subgroup G}

theorem frameNumIs_frameConn_of_signedPerm {k : ℕ} (hk : 3 ≤ k)
    (Θ : (Fin k → Multiplicative (ZMod 3)) ≃* ↥A) {𝒜 : Subgroup (MulAut ↥A)}
    (h𝒜 : ∀ φ : MulAut ↥A, φ ∈ 𝒜 ↔ IsSignedPerm ⇑((MulAut.congr Θ).symm φ)) :
    FrameNumIs 𝒜 (k ^ 2) none ∧ FrameConn 𝒜 :=
  frameNumIs_frameConn_of_model Θ (S := signedPermSet k) h𝒜 (modelNumIs_signedPermSet hk)
    modelConn_signedPermSet

theorem frameNumIs_frameConn_of_evenSignedPerm {k : ℕ} (hk : 3 ≤ k)
    (Θ : (Fin k → Multiplicative (ZMod 3)) ≃* ↥A) {𝒜 : Subgroup (MulAut ↥A)}
    (h𝒜 : ∀ φ : MulAut ↥A, φ ∈ 𝒜 ↔ (MulAut.congr Θ).symm φ ∈ evenSignedPermSet k) :
    FrameNumIs 𝒜 (k * (k - 1)) (some (4 * (k - 2))) ∧ FrameConn 𝒜 :=
  frameNumIs_frameConn_of_model Θ (S := evenSignedPermSet k) h𝒜
    (modelNumIs_evenSignedPermSet hk) (modelConn_evenSignedPermSet hk)

theorem frameNumIs_frameConn_of_sumZeroPerm {d : ℕ} (hd : 3 ≤ d) (Θ : ↥(sumZero d 3) ≃* ↥A)
    {𝒜 : Subgroup (MulAut ↥A)}
    (h𝒜 : ∀ φ : MulAut ↥A, φ ∈ 𝒜 ↔ ∃ π : Equiv.Perm (Fin d), (MulAut.congr Θ).symm φ = permAutV π) :
    FrameNumIs 𝒜 (d * (d - 1) / 2) (some (2 * (d - 2))) ∧ FrameConn 𝒜 := by
  have h := modelNumIs_modelConn_of_perm hd (permAutVHom d 3)
    (permAutV_injective Nat.prime_three (by decide)) mem_modelReflSet_sumZeroPermSet_iff
  refine frameNumIs_frameConn_of_model Θ (S := sumZeroPermSet d) (fun φ => ?_) h.1 h.2
  rw [h𝒜 φ, sumZeroPermSet, Set.mem_range]
  exact exists_congr fun _ => eq_comm

end CFSG.StandardType.FrameRoute

end
