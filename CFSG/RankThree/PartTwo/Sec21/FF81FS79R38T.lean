module

public import CFSG.RankThree.PartTwo.Sec21.FF81FS79R38Ctl
public import CFSG.RankThree.PartTwo.Sec21.FF81FS79R38Main

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79 Equiv
open CFSG.Assembly (InCatalog)

namespace R38K

theorem sg3_swap45_c₁ :
    (swap (4 : Fin 6) 5 * J6.sg3) * J6.c₁ * (swap (4 : Fin 6) 5 * J6.sg3)⁻¹ = J6.c₂⁻¹ := by
  decide +kernel

variable {H : Type} [Group H] [Finite H]
variable {b t b₁ b₂ : H} {J : Subgroup H}

theorem r38T (hR1K : KF_FS79Prop2OneK) (hD1 : FS79D1K) (hK : KCore.KGroupNonab InCatalog H)
    (S : Std b t b₁ b₂ J) : R38Stmt b (J6.T1.map S.ι) := by
  have h := S.hyp
  have hD : CtlEq b (b * b₁) := hD1 H hK b t b₁ b₂ J h
  have hB₁ : b₁ ∈ Subgroup.closure ({b, b₁, b₂} : Set H) :=
    FS79Hyp.B₁_le_B b b₁ b₂ (Subgroup.subset_closure (by simp))
  have hB₂ : b₂ ∈ Subgroup.closure ({b, b₁, b₂} : Set H) :=
    FS79Hyp.B₁_le_B b b₁ b₂ (Subgroup.subset_closure (by simp))
  have hbb₁ : b * b₁ ∈ Subgroup.closure ({b, b₁, b₂} : Set H) := mul_mem_B hB₁
  have hC₁ : CtlEq b (S.ι J6.c₂) := by
    rw [S.ι_c₂]
    exact h.N_bi b₂ (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hO₁ : Odd (Nat.card (Opp 3 (Nor (Subgroup.zpowers (S.ι J6.c₂))))) := by
    rw [S.ι_c₂]
    exact odd_Opp_of_mem_B h hB₂
  have e₂ : S.ι J6.sg3 * (b * b₁) * (S.ι J6.sg3)⁻¹ = b * S.ι J6.c₂ := by
    rw [conj_mul_of_comm (S.ι_comm_b J6.sg3), S.tau_b₁, S.ι_c₂]
  obtain ⟨hC₂, hO₂⟩ := ctl_odd_of_conj (S.ι_comm_b J6.sg3) hD (odd_Opp_of_mem_B h hbb₁) e₂
  have hσb₁ : S.ι (swap (4 : Fin 6) 5 * J6.sg3) * b₁ * (S.ι (swap (4 : Fin 6) 5 * J6.sg3))⁻¹ =
      (S.ι J6.c₂)⁻¹ := by
    have := S.ι_conj (swap (4 : Fin 6) 5 * J6.sg3) J6.c₁
    rw [S.ι_c₁, sg3_swap45_c₁, map_inv] at this
    exact this.symm
  have e₃ : S.ι (swap (4 : Fin 6) 5 * J6.sg3) * (b * b₁) * (S.ι (swap (4 : Fin 6) 5 * J6.sg3))⁻¹ =
      b * (S.ι J6.c₂)⁻¹ := by
    rw [conj_mul_of_comm (S.ι_comm_b _), hσb₁]
  obtain ⟨hC₃, hO₃⟩ := ctl_odd_of_conj (S.ι_comm_b _) hD (odd_Opp_of_mem_B h hbb₁) e₃
  exact frame_r38 hR1K hK S frameT hC₁ hC₂ hC₃ hO₁ hO₂ hO₃

end R38K

theorem fs79R38K_of (hR1K : KF_FS79Prop2OneK) (hD1 : FS79D1K) : FS79R38K := by
  intro H _ _ hK b t b₁ b₂ J S
  exact R38K.r38T hR1K hD1 hK S

end CFSG.RankThree.PartTwo.Sec21.FF81
