module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPShape
public import CFSG.LocalAnalysis.WeakClosure81.EightNVDerived
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenAMain

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def W3Claim820' (G : Type) [Group G] [Finite G] : Prop :=
  ∀ {V H T A L K : Subgroup G} {i : ℕ}, Sit813 V H T i A L K →
    Case813UC (cGrp H T) H T A L →
    A ≤ (H ⊓ normalizer (V : Set G) ⊓ centralizer (V : Set G)) ⊔ cGrp H T

theorem Sit813.false_of_claim820' (hin : W3In814 G) {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K)
    (hA : A ≤ (H ⊓ normalizer (V : Set G) ⊓ centralizer (V : Set G)) ⊔ cGrp H T) : False := by
  have hC : cGrp H T ≤ centralizer (V : Set G) :=
    h.cGrp_le_oTwoMod.trans (h.oTwoMod_le_centralizer_V hin)
  have hAV : A ≤ centralizer (V : Set G) := hA.trans (sup_le inf_le_right hC)
  obtain ⟨a, ha, w, hw, hne⟩ := h.commutator_A_ne
  exact hne ((Subgroup.mem_centralizer_iff.mp (hAV ha) w hw).symm)

theorem Sit813.eight_twenty' (hin : W3In814 G) (hc : W3Claim820' G) {V H T A L K : Subgroup G}
    {i : ℕ} (h : Sit813 V H T i A L K) (hUC : Case813UC (cGrp H T) H T A L) : False :=
  h.false_of_claim820' hin (hc h hUC)

end CFSG.LocalAnalysis.WeakClosure81

end
