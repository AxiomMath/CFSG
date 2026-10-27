module

public import CFSG.RankThree.PartTwo.Sec21.FF81FS79R38Ctl
public import CFSG.RankThree.PartTwo.Sec21.FF81FS79R38Main

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79 Equiv
open CFSG.Assembly (InCatalog)

namespace R38K

variable {H : Type} [Group H] [Finite H]
variable {b t b₁ b₂ : H} {J : Subgroup H}

theorem r38V (hR1K : KF_FS79Prop2OneK) (h34 : FS79R34K) (hD2 : FS79D2K)
    (hK : KCore.KGroupNonab InCatalog H) (S : Std b t b₁ b₂ J) :
    R38Stmt b (J6.V1.map S.ι) := by
  have h := S.hyp
  have hR34 : CtlEq b (b₁ * b₂) := h34 H hK b t b₁ b₂ J h
  have hD : CtlEq b (b * (b₁ * b₂)) := hD2 H hK b t b₁ b₂ J h
  have hB₁ : b₁ ∈ Subgroup.closure ({b, b₁, b₂} : Set H) :=
    FS79Hyp.B₁_le_B b b₁ b₂ (Subgroup.subset_closure (by simp))
  have hB₂ : b₂ ∈ Subgroup.closure ({b, b₁, b₂} : Set H) :=
    FS79Hyp.B₁_le_B b b₁ b₂ (Subgroup.subset_closure (by simp))
  have hd : b₁ * b₂ ∈ Subgroup.closure ({b, b₁, b₂} : Set H) := Subgroup.mul_mem _ hB₁ hB₂
  have hbd : b * (b₁ * b₂) ∈ Subgroup.closure ({b, b₁, b₂} : Set H) := mul_mem_B hd
  obtain ⟨γ, hγ⟩ := J6.conj_c0_d
  have hσ₁ : γ⁻¹ * J6.d * γ⁻¹⁻¹ = J6.c0 := by
    have : J6.d = J6.c₁ * J6.c₂ := rfl
    rw [this, ← hγ]
    group
  have hσ₃ : (γ⁻¹ * J6.ainv) * J6.d * (γ⁻¹ * J6.ainv)⁻¹ = J6.c0⁻¹ := by
    have e : (γ⁻¹ * J6.ainv) * J6.d * (γ⁻¹ * J6.ainv)⁻¹ =
        γ⁻¹ * (J6.ainv * J6.d * J6.ainv⁻¹) * γ := by group
    rw [e, J6.ainv_d_conj, ← hσ₁]
    group
  have hι₁ : S.ι γ⁻¹ * (b₁ * b₂) * (S.ι γ⁻¹)⁻¹ = S.ι J6.c0 := by
    have := S.ι_conj γ⁻¹ J6.d
    rw [hσ₁, S.ι_dd] at this
    exact this.symm
  have hι₃ : S.ι (γ⁻¹ * J6.ainv) * (b₁ * b₂) * (S.ι (γ⁻¹ * J6.ainv))⁻¹ = (S.ι J6.c0)⁻¹ := by
    have := S.ι_conj (γ⁻¹ * J6.ainv) J6.d
    rw [hσ₃, S.ι_dd, map_inv] at this
    exact this.symm
  obtain ⟨hC₁, hO₁⟩ := ctl_odd_of_conj (S.ι_comm_b γ⁻¹) hR34 (odd_Opp_of_mem_B h hd) hι₁
  have e₂ : S.ι γ⁻¹ * (b * (b₁ * b₂)) * (S.ι γ⁻¹)⁻¹ = b * S.ι J6.c0 := by
    rw [conj_mul_of_comm (S.ι_comm_b γ⁻¹), hι₁]
  obtain ⟨hC₂, hO₂⟩ := ctl_odd_of_conj (S.ι_comm_b γ⁻¹) hD (odd_Opp_of_mem_B h hbd) e₂
  have e₃ : S.ι (γ⁻¹ * J6.ainv) * (b * (b₁ * b₂)) * (S.ι (γ⁻¹ * J6.ainv))⁻¹ =
      b * (S.ι J6.c0)⁻¹ := by
    rw [conj_mul_of_comm (S.ι_comm_b _), hι₃]
  obtain ⟨hC₃, hO₃⟩ := ctl_odd_of_conj (S.ι_comm_b _) hD (odd_Opp_of_mem_B h hbd) e₃
  exact frame_r38 hR1K hK S frameV hC₁ hC₂ hC₃ hO₁ hO₂ hO₃

end R38K

theorem fs79R38'K_of (hR1K : KF_FS79Prop2OneK) (h34 : FS79R34K) (hD2 : FS79D2K) : FS79R38'K := by
  intro H _ _ hK b t b₁ b₂ J S
  exact R38K.r38V hR1K h34 hD2 hK S

end CFSG.RankThree.PartTwo.Sec21.FF81
