module

public import CFSG.LocalAnalysis.StandardType.GGStdPosLocalDefs
public import CFSG.LocalAnalysis.StandardType.GGStdPosRankModel
public import CFSG.LocalAnalysis.StandardType.GGStdPosRankTypeA

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

theorem ggKGPos_three_le_bnRank
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {Bs X : Subgroup G} {t : StatedLieTag} {n f : ℕ} {ψ : (ggU t n f).K →* G}
    (hadm : StatedLieAdmissible t n 2 f) (hker : ψ.ker ≤ Subgroup.center (ggU t n f).K)
    (hrange : ψ.range = X)
    (ht : t = .PSL ∨ t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8) (hpf : p ∣ 2 ^ f - 1)
    (hBs : IsElemAbelian p Bs) (hInn : GGInnerDiagOn Bs X)
    (hcard : p ^ 3 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≤ Nat.card ↥Bs) :
    3 ≤ bnRank t n := by
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · by_contra hlt
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hadm.2.2.1; omega⟩
    have hm : m ≤ 2 := by simp only [bnRank] at hlt; omega
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hf : f ≠ 0 := by have := hadm.2.1; omega
    have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f hf
    subst hrange
    have hmod := ggKGPos_statedModel_psl (F := GaloisField 2 f) hF hadm ψ hker
    have hle := ggKGPos_card_le_of_typeA hRig hp hBs hInn hmod hpf
    have hc : 0 < Nat.card ↥(Bs ⊓ Subgroup.centralizer (ψ.range : Set G)) := Nat.card_pos
    have h3 : p ^ 3 ≤ p ^ m := Nat.le_of_mul_le_mul_right (hcard.trans hle) hc
    have := (Nat.pow_le_pow_iff_right hp.one_lt).mp h3
    omega
  · simp only [bnRank]
    have := hadm.2.2
    omega
  · simp [bnRank]
  · simp [bnRank]
  · simp [bnRank]

end CFSG.StandardType

end
