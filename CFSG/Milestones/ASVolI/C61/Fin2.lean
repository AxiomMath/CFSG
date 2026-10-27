module

public import CFSG.Milestones.ASVolI.C61.Fin
public import CFSG.Milestones.ASVolI.C61.Tr3

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
open scoped Pointwise

variable {G G' : Type} [Group G] [Group G'] {H Λ : Subgroup G} {ι : ↥H →* G'} {κ : ↥Λ →* G'}

section HSide

variable (hι : Function.Injective ι)
include hι

theorem burnsideC56_finH_pCoreOf (p : ℕ) :
    pCoreOf p ((⊤ : Subgroup ↥H).map ι) = (pCoreOf p (⊤ : Subgroup ↥H)).map ι :=
  burnsideC56_tr_pCoreOf hι p ⊤

omit hι in
theorem burnsideC56_finH_pCoreOf' (p : ℕ) :
    pCoreOf p H = (pCoreOf p (⊤ : Subgroup ↥H)).map H.subtype := by
  have := burnsideC56_tr_pCoreOf H.subtype_injective p (⊤ : Subgroup ↥H)
  rwa [burnsideC56_fin_top] at this

omit hι in
theorem burnsideC56_finH_oTwoUpper' :
    oTwoUpper H = (oTwoUpper (⊤ : Subgroup ↥H)).map H.subtype := by
  have := burnsideC56_tr_oTwoUpper H.subtype_injective (⊤ : Subgroup ↥H)
  rwa [burnsideC56_fin_top] at this

theorem burnsideC56_finH_oTwoUpper :
    oTwoUpper ((⊤ : Subgroup ↥H).map ι) = (oTwoUpper (⊤ : Subgroup ↥H)).map ι :=
  burnsideC56_tr_oTwoUpper hι ⊤

theorem burnsideC56_finH_charTwo : CharTwo H ↔ CharTwo ((⊤ : Subgroup ↥H).map ι) := by
  rw [burnsideC56_tr_charTwo hι, ← burnsideC56_tr_charTwo H.subtype_injective, burnsideC56_fin_top]

theorem burnsideC56_finH_quotHas_L (P : ∀ (Y : Type) [Group Y], Prop) :
    QuotHas (oTwoUpper H) (pCoreOf 2 H) P ↔
      QuotHas (oTwoUpper ((⊤ : Subgroup ↥H).map ι)) (pCoreOf 2 ((⊤ : Subgroup ↥H).map ι)) P := by
  rw [burnsideC56_finH_oTwoUpper hι, burnsideC56_finH_pCoreOf hι, burnsideC56_tr_quotHas hι,
    burnsideC56_finH_oTwoUpper', burnsideC56_finH_pCoreOf', burnsideC56_tr_quotHas H.subtype_injective]

theorem burnsideC56_finH_quotHas_H (P : ∀ (Y : Type) [Group Y], Prop) :
    QuotHas H (pCoreOf 2 H) P ↔
      QuotHas ((⊤ : Subgroup ↥H).map ι) (pCoreOf 2 ((⊤ : Subgroup ↥H).map ι)) P := by
  rw [burnsideC56_finH_pCoreOf hι, burnsideC56_tr_quotHas hι, burnsideC56_finH_pCoreOf',
    ← burnsideC56_tr_quotHas H.subtype_injective, burnsideC56_fin_top]

theorem burnsideC56_finH_isBlock2 :
    IsBlock2 H (oTwoUpper H) ↔
      IsBlock2 ((⊤ : Subgroup ↥H).map ι) (oTwoUpper ((⊤ : Subgroup ↥H).map ι)) := by
  rw [burnsideC56_finH_oTwoUpper hι, burnsideC56_tr_isBlock2 hι, burnsideC56_finH_oTwoUpper',
    ← burnsideC56_tr_isBlock2 H.subtype_injective, burnsideC56_fin_top]

theorem burnsideC56_finH_isLin2Type (n : ℕ) :
    IsLin2Type (oTwoUpper H) n ↔ IsLin2Type (oTwoUpper ((⊤ : Subgroup ↥H).map ι)) n := by
  rw [burnsideC56_finH_oTwoUpper hι, burnsideC56_tr_isLin2Type hι, burnsideC56_finH_oTwoUpper',
    burnsideC56_tr_isLin2Type H.subtype_injective]

theorem burnsideC56_finH_isAltType (m : ℕ) :
    IsAltType (oTwoUpper H) m ↔ IsAltType (oTwoUpper ((⊤ : Subgroup ↥H).map ι)) m := by
  rw [burnsideC56_finH_oTwoUpper hι, burnsideC56_tr_isAltType hι, burnsideC56_finH_oTwoUpper',
    burnsideC56_tr_isAltType H.subtype_injective]

theorem burnsideC56_finH_isA3Product (s : ℕ) :
    IsA3Product H (oTwoUpper H) s ↔
      IsA3Product ((⊤ : Subgroup ↥H).map ι) (oTwoUpper ((⊤ : Subgroup ↥H).map ι)) s := by
  rw [burnsideC56_finH_oTwoUpper hι, burnsideC56_tr_isA3Product hι, burnsideC56_finH_oTwoUpper',
    ← burnsideC56_tr_isA3Product H.subtype_injective, burnsideC56_fin_top]

theorem burnsideC56_finH_mulEquiv (W : Type*) [Group W] :
    Nonempty (↥H ≃* W) ↔ Nonempty (↥((⊤ : Subgroup ↥H).map ι) ≃* W) := by
  rw [burnsideC56_tr_nonempty_mulEquiv hι]
  exact ⟨fun ⟨e⟩ => ⟨Subgroup.topEquiv.trans e⟩, fun ⟨e⟩ => ⟨Subgroup.topEquiv.symm.trans e⟩⟩

end HSide

end CFSG.ASVolI
