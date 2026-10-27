module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporK105In
import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraBasic
import CFSG.Quasithin.Background.A4V
import CFSG.Quasithin.Background.B2Thompson

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

open CFSG Subgroup

variable {X : Type} [Group X] [Finite X]

theorem mem_omegaOneCenterOf_thompsonJ {T : Subgroup X} {z : X} (hzT : z ∈ T)
    (hz : ∀ t ∈ T, t * z = z * t) (hz2 : z ^ 2 = 1) :
    z ∈ CFSG.Quasithin.omegaOneCenterOf (CFSG.Quasithin.thompsonJ T) := by
  have hzJ : z ∈ CFSG.Quasithin.thompsonJ T :=
    CFSG.QuasithinUnique.GammaExtra.mem_thompsonJ_of_central_involution hzT hz hz2
  have hJle : CFSG.Quasithin.thompsonJ T ≤ T :=
    CFSG.QuasithinUnique.GammaExtra.thompsonJ_le_self T
  have hzC : z ∈ CFSG.Quasithin.centerOf (CFSG.Quasithin.thompsonJ T) :=
    ⟨hzJ, Subgroup.mem_centralizer_iff.2 fun y hy => hz y (hJle hy)⟩
  change z ∈ CFSG.Quasithin.omegaOneOf
    (CFSG.Quasithin.centerOf (CFSG.Quasithin.thompsonJ T))
  exact Subgroup.subset_closure ⟨hzC, hz2⟩

theorem omegaOneCenterOf_thompsonJ_le {T A : Subgroup X}
    (hA : CFSG.Quasithin.IsMaxElemAbelian T A) :
    CFSG.Quasithin.omegaOneCenterOf (CFSG.Quasithin.thompsonJ T) ≤ A := by
  rw [(CFSG.Quasithin.omegaOne_centralizer_thompsonJ T).2]
  exact iInf₂_le A hA

theorem omegaOneCenterOf_thompsonJ_le_iInf {T : Subgroup X} {ι : Type*} (A : ι → Subgroup X)
    (hA : ∀ i, CFSG.Quasithin.IsMaxElemAbelian T (A i)) :
    CFSG.Quasithin.omegaOneCenterOf (CFSG.Quasithin.thompsonJ T) ≤ ⨅ i, A i :=
  le_iInf fun i => omegaOneCenterOf_thompsonJ_le (hA i)

theorem k105In_normalizer_thompsonJ_of_card_le_four {T : Subgroup X} {z : X}
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤) (hzT : z ∈ T)
    (hz : ∀ t ∈ T, t * z = z * t) (hz2 : z ^ 2 = 1) (hC : K105In (centralizer {z}) T)
    (hV : Nat.card (CFSG.Quasithin.omegaOneCenterOf (CFSG.Quasithin.thompsonJ T)) ≤ 4) :
    K105In (normalizer (CFSG.Quasithin.thompsonJ T : Set X)) T := by
  have hzW : z ∈ CFSG.Quasithin.omegaOneCenterOf (CFSG.Quasithin.thompsonJ T) :=
    mem_omegaOneCenterOf_thompsonJ hzT hz hz2
  have hTz : T ≤ centralizer {z} := by
    intro t ht
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hz t ht
  have hK := k105In_normalizer_of_card_le_four
    (V := CFSG.Quasithin.omegaOneCenterOf (CFSG.Quasithin.thompsonJ T))
    hT hTz hzW hV hC
  exact K105In.mono hK
    (CFSG.Quasithin.A4.normalizer_le_normalizer_omegaOneCenterOf (CFSG.Quasithin.thompsonJ T))

theorem k105In_normalizer_thompsonJ_of_iInf {T : Subgroup X} {z : X} {ι : Type*}
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤) (hzT : z ∈ T)
    (hz : ∀ t ∈ T, t * z = z * t) (hz2 : z ^ 2 = 1) (hC : K105In (centralizer {z}) T)
    (A : ι → Subgroup X) (hA : ∀ i, CFSG.Quasithin.IsMaxElemAbelian T (A i))
    (hAc : Nat.card (⨅ i, A i : Subgroup X) ≤ 4) :
    K105In (normalizer (CFSG.Quasithin.thompsonJ T : Set X)) T := by
  have hVle : CFSG.Quasithin.omegaOneCenterOf (CFSG.Quasithin.thompsonJ T) ≤ ⨅ i, A i :=
    omegaOneCenterOf_thompsonJ_le_iInf A hA
  have hV : Nat.card (CFSG.Quasithin.omegaOneCenterOf (CFSG.Quasithin.thompsonJ T)) ≤ 4 :=
    (Subgroup.card_le_of_le hVle).trans hAc
  exact k105In_normalizer_thompsonJ_of_card_le_four hT hzT hz hz2 hC hV

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
