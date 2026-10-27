module

public import Certificates.Certificate9566
public import CFSG.RankThree.PartTwo.KFacts.ONanKS152J2Bridge

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.ComponentClassification.J2Cover

theorem ks152J2Gen :
    ∀ (Γ : Type) [Group Γ] [Finite Γ], Nonempty (Γ ≃* CFSG.Blueprint.NativeSporadic.J2) →
      ∀ z : Γ, z ≠ 1 →
        (∃ S : Sylow 3 Γ, z ∈ (S : Subgroup Γ) ∧
          (S : Subgroup Γ) ≤ Subgroup.centralizer ({z} : Set Γ)) →
        ∀ Q F : Subgroup Γ, IsPGroup 2 Q → 64 ∣ Nat.card Q →
          F ≤ Subgroup.centralizer ({z} : Set Γ) → Group.IsPerfect F → Nat.card F = 60 →
            Q ⊔ F = ⊤ := by
  intro Γ _ _ hΓ
  obtain ⟨e⟩ := hΓ
  have hP : KS152J2.GenStmt (↥P) := by
    obtain ⟨Tp, Wp, Sp, z0, y0, hT, hTc, hW, hWT, hS, hSc, hz1, hzS, hSz, hy, hy5, hy1, hzy,
      hcore⟩ := Certificates.certificate9566
    have hX : Nat.card (↥P) = 604800 := KS152J2.card_of_j2 ⟨nativeEquivP.symm⟩
    obtain ⟨T, W, S₀, z₀, y₀, hWT', hz₀, hz₀S, hS₀, hy₀, hzy₀, hcore'⟩ :=
      KS152J2.core_of_perm (X := P) hX hT hTc hW hWT hS hSc hz1 hzS hSz hy hy5 hy1 hzy hcore
    exact KS152J2.genStmt_of_core ⟨nativeEquivP.symm⟩ T W hWT' S₀ hz₀ hz₀S hS₀ hy₀ hzy₀ hcore'
  exact KS152J2.genStmt_of_equiv (e.trans nativeEquivP) hP

end CFSG.RankThree.PartTwo.KFacts
