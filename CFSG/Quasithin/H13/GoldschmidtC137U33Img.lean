module

public import CFSG.Quasithin.H13.GoldschmidtC137U33Cfg
public import CFSG.Quasithin.H13.GoldschmidtC137Off
public import CFSG.Quasithin.EmptyFaithful.A38c5Aut

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
  CFSG.LieType.BorelTits

variable {G : Type} [Group G]

namespace U33Cfg

variable [Finite G] {X T V L P M : Subgroup G} (h : U33Cfg X T V L P M)
include h

theorem hCP : X ⊓ centralizer (V : Set G) ≤ P := h.C_le_R.trans (pCoreOf_le 2 P)

theorem sylow_T : IsSylowTwoOf (autI h.hVe T) (autI h.hVe X) :=
  B2F.isSylowTwoOf_autI h.hVe h.hXN h.hT

theorem T_le_P : autI h.hVe T ≤ autI h.hVe P := autI_mono h.hVe h.hTP

theorem P_le_X : autI h.hVe P ≤ autI h.hVe X := autI_mono h.hVe h.hPX.le

theorem P_ne_X : autI h.hVe P ≠ autI h.hVe X := by
  intro heq
  apply h.hPX.not_ge
  exact le_of_autI_le h.hVe h.hXN h.hPX.le h.hCP le_rfl heq.ge

theorem P_max : ∀ H₀ : Subgroup (MulAut (IntMod V h.hVe)), autI h.hVe P ≤ H₀ →
    H₀ ≤ autI h.hVe X → H₀ = autI h.hVe P ∨ H₀ = autI h.hVe X := by
  intro H₀ h1 h2
  have hHX : starPreIn h.hVe X H₀ ≤ X := starPreIn_le h.hVe
  have hPH : P ≤ starPreIn h.hVe X H₀ := fun p hp =>
    mem_starPreIn.2 ⟨h.hPX.le hp, h.hXN (h.hPX.le hp), h1 (convI_mem_autI h.hVe hp _)⟩
  have hau : autI h.hVe (starPreIn h.hVe X H₀) = H₀ := autI_starPreIn h.hVe h.hXN h2
  rcases h.hmax _ (h.hPeq ▸ hPH) hHX with h3 | h3
  · left
    rw [← hau, h3]
    exact congrArg (autI h.hVe) h.hPeq.symm
  · right
    rw [← hau, h3]

theorem autI_R : autI h.hVe (pCoreOf 2 P) = pCoreOf 2 (autI h.hVe P) :=
  A38c5.autI_pCoreOf h.hVe (h.hPX.le.trans h.hXN) (h.isPGroup_C.to_le (inf_le_inf_right _ h.hPX.le))

end U33Cfg

end CFSG.Quasithin.H13.U3.GC137
