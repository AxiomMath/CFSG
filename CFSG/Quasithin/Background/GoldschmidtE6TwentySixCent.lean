module

public import CFSG.Quasithin.Background.E6TwentySix
public import CFSG.Quasithin.Background.GoldschmidtE5TwoCent

public section

namespace CFSG.Quasithin
namespace E6

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem e6_26_ofC {T V M H S : Subgroup G} {j : ℕ} (hT : IsPGroup 2 T) (hV1 : V ≠ ⊥)
    (hV : IsElemAbelian 2 V) (hVT : V ≤ T) (hNM : Subgroup.normalizer (V : Set G) ≤ M)
    (hM : IsUniqueM (Subgroup.normalizer ((T ⊓ Subgroup.centralizer (V : Set G) :
      Subgroup G) : Set G)) M)
    (hG : E5.CentGen j H S)
    (hQS : T ⊓ Subgroup.centralizer (V : Set G) ≤ S) (hST : S ≤ T)
    (hr : (j : ℕ∞) < E3.rParam V)
    (hJ : H13.thompsonJk j S ≤ S ⊓ Subgroup.centralizer (V : Set G)) :
    H ≤ M ∧ Subgroup.normalizer (S : Set G) ≤ M := by
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQdef
  have hVQ : V ≤ Q := fun v hv =>
    ⟨hVT hv, Subgroup.mem_centralizer_iff.2 fun w hw =>
      congrArg Subtype.val (hV.1.is_comm.comm ⟨w, hw⟩ ⟨v, hv⟩)⟩
  have hVS : V ≤ S := hVQ.trans hQS
  have hJC : H13.thompsonJk j S ≤ Subgroup.centralizer (V : Set G) := hJ.trans inf_le_right
  have hVD : V ≤ omegaOneCenterOf (H13.thompsonJk j S) :=
    E5.le_omegaOneCenterOf_of_le_centralizer hVS hV hJC
  have hJQ : thompsonJ S ≤ Q :=
    (thompsonJ_le_thompsonJk j S).trans (hJ.trans (inf_le_inf_right _ hST))
  have hJeq : thompsonJ S = thompsonJ Q := thompsonJ_eq_of_le hJQ hQS
  have hNJ : Subgroup.normalizer (thompsonJ S : Set G) ≤ M := by
    have hNQ : Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (thompsonJ S : Set G) := by
      intro g hg
      rw [hJeq]
      exact E5.mem_normalizer_of_cjSub_eq (cjSub_thompsonJ hg)
    have h2 : IsPGroup 2 (thompsonJ S) := (hT.to_le hST).to_le (thompsonJ_le_self S)
    obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge
      (⟨thompsonJ S, thompsonJ_ne_bot hVS hV hV1, h2, rfl⟩ :
        IsTwoLocal (Subgroup.normalizer (thompsonJ S : Set G)))
    have hM'eq : M' = M := hM.2 M' ⟨hM', hNQ.trans hle⟩
    rw [← hM'eq]
    exact hle
  refine ⟨?_, fun g hg => hNJ (E5.mem_normalizer_of_cjSub_eq (cjSub_thompsonJ hg))⟩
  rw [← hG]
  refine sup_le (inf_le_right.trans hNJ) (iSup₂_le fun D₁ hD₁ => ?_)
  set D := omegaOneCenterOf (H13.thompsonJk j S) with hDdef
  have hrelD : D₁.relIndex D ≤ 2 ^ j := by
    have h1 := Subgroup.relIndex_mul_card D₁ D
    rw [inf_eq_left.2 hD₁.1] at h1
    have h2 : D₁.relIndex D * Nat.card ↥D₁ ≤ 2 ^ j * Nat.card ↥D₁ := by rw [h1]; exact hD₁.2
    exact Nat.le_of_mul_le_mul_right h2 Nat.card_pos
  have hrelV : (V ⊓ D₁).relIndex V ≤ 2 ^ j := by
    rw [Subgroup.inf_relIndex_left]
    exact (Subgroup.relIndex_le_of_le_right hVD (E3.relIndex_ne_zero' _ _)).trans hrelD
  have hm : E3.mQuot V (V ⊓ D₁) ≤ j := by
    unfold E3.mQuot
    calc padicValNat 2 ((V ⊓ D₁).relIndex V) ≤ Nat.log 2 ((V ⊓ D₁).relIndex V) :=
          padicValNat_le_nat_log _
      _ ≤ Nat.log 2 (2 ^ j) := Nat.log_mono_right hrelV
      _ = j := Nat.log_pow (by norm_num) j
  have hCN : Subgroup.centralizer ((V ⊓ D₁ : Subgroup G) : Set G) ≤
      Subgroup.normalizer (V : Set G) := by
    by_contra hne
    have h1 := E3.rParam_le_mQuot (inf_le_left : V ⊓ D₁ ≤ V) hne
    have h2 : (E3.mQuot V (V ⊓ D₁) : ℕ∞) ≤ j := by exact_mod_cast hm
    exact absurd (h1.trans h2) (not_le.2 hr)
  exact (inf_le_right.trans (Subgroup.centralizer_le fun x hx => hx.2)).trans (hCN.trans hNM)

end E6

namespace H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3

theorem ch6InE626_ofC :
    ∀ (G : Type) [Group G] [Finite G] (T V M H S : Subgroup G) (j : ℕ),
      quasithinIsSylowTwo T → V ≠ ⊥ → IsElemAbelian 2 V → V ≤ T →
      T ≤ Subgroup.normalizer (V : Set G) →
      Subgroup.normalizer (V : Set G) ≤ M → IsUniqueM (Subgroup.normalizer (ch6Q T V : Set G)) M →
      0 < j → E5.CentGen j H S → ch6Q T V ≤ S → S ≤ T →
      (j : ℕ∞) < rParam V → thompsonJk j S ≤ S ⊓ Subgroup.centralizer (V : Set G) →
        H ≤ M ∧ Subgroup.normalizer (S : Set G) ≤ M := by
  intro G _ _ T V M H S j hT hV1 hV hVT _ hNM hM _ hG hQS hST hr hJ
  exact E6.e6_26_ofC hT.1 hV1 hV hVT hNM hM hG hQS hST hr hJ

end H13

end CFSG.Quasithin
