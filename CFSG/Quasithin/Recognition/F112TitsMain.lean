module

public import CFSG.Quasithin.Recognition.F112RDefs
public import CFSG.Quasithin.EmptyFaithful.S1421L2Two

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

@[expose] def HayashiFiveThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L₁ L₂ S : Subgroup G),
    Hyp111 L₁ L₂ S → IsQuasithinSub (L₁ ⊔ L₂ ⊔ S) → S ≤ L₁ → S ≤ L₂ → L₁ ⊓ L₂ = S →
    L₁ ⊓ Subgroup.normalizer (S : Set G) = S → L₂ ⊓ Subgroup.normalizer (S : Set G) = S →
    (Nonempty (oTwoQuot ↥L₁ ≃* DihedralGroup 5) ∨ Nonempty (oTwoQuot ↥L₁ ≃* ↥(Sz 0))) →
    IsL2Quot 1 (oTwoQuot ↥L₂) → CaseTits L₁ L₂ ∨ Case2F4 L₁ L₂

theorem f112R2b_of_hayashi (hSz : Nat.card ↥(Sz 0) = 20) (hHay : HayashiFiveThree) :
    F112R2bStatement := by
  intro G _ _ T M Y H S hsmall
  have hq : IsL2Quot 1 (oTwoQuot ↥(Y ⊔ T)) := by
    obtain ⟨e⟩ := S.data.quot
    exact isL2Quot_one_iff_perm3.mpr ⟨e⟩
  exact hHay G H (Y ⊔ T) T (S.hyp111 hSz) (isQuasithinSub_of_qtke S.hyp.qtke _) S.T_le_H
    Setting1422.T_le_YT (S.H_inf_YT hSz) (S.inf_normalizer_H hSz) S.inf_normalizer_YT hsmall hq

end CFSG.Quasithin
