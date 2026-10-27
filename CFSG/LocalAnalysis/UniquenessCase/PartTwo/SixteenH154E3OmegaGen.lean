module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3OmegaB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsHyp
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ui
public import CFSG.Quasithin.Background.B2FactorizationResidual

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)

variable {G : Type} [Group G] [Finite G]

@[expose] def s16h_e3_omega_cfg_gen (D : Data G) {V L : Subgroup G}
    (hV : IsElemAbelian 2 V) : Prop :=
  D.sig = {3} ∧ ∃ L₀ D₃ A : Subgroup G,
    L₀ ∈ calC D.M ∧ L₀ ≤ D.M ∧ IsL2 (Bar2 L₀) 3 ∧ pCoreOf 2 L₀ ≠ ⊥ ∧
    D₃ ≤ L₀ ∧ Nat.card D₃ = 3 ∧ D₃ ∈ uniqueSet D.M ∧
    A ≤ L₀ ∧ Nat.card A = 7 ∧ A ∈ uniqueSet D.M ∧
    L₀ ≤ centralizer ((wSub ⊥ V hV L ⊔ v1Sub D.M ⊥ V hV L : Subgroup G) : Set G)

theorem s16h_e3_omega_unique_gen (D : Data G) (h920 : s16h_e3_R920L28 D) {V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hΩ : s16h_e3_omega_cfg_gen D (V := V) (L := L) hV) :
    ∀ w ∈ wSub ⊥ V hV L ⊔ v1Sub D.M ⊥ V hV L, w ≠ 1 →
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  obtain ⟨hsig, L₀, D₃, A, hL, hLM, hL2, hO, hD₃, hD₃c, hD₃u, hA, hAc, hAu, hcent⟩ := hΩ
  have hU := h920 (by rw [hsig]; exact Set.mem_singleton 3) L₀ D₃ A hL hLM hL2 hO hD₃ hD₃c hD₃u
    hA hAc hAu
  intro w hw _
  refine uc22p22u_uniqueMax_mono D (le_inf hLM fun l hl => ?_) inf_le_left hU
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff.1 hy]
  exact (Subgroup.mem_centralizer_iff.1 (hcent hl)) w hw

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
