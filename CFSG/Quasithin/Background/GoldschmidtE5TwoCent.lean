module

public import CFSG.Quasithin.Background.GoldschmidtE5TwoNormal

public section

namespace CFSG.Quasithin
namespace E5

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
@[expose] def CentGen (j : ℕ) (H P : Subgroup G) : Prop :=
  (H ⊓ Subgroup.normalizer (thompsonJ P : Set G)) ⊔
    (⨆ D₁ ∈ dFam j P, H ⊓ Subgroup.centralizer (D₁ : Set G)) = H

theorem inf_eq_of_isSylowIn {T Y S : Subgroup G} (hT : IsPGroup 2 T) (hS : IsSylowIn 2 S Y)
    (hST : S ≤ T) : T ⊓ Y = S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : S ≤ T ⊓ Y := le_inf hST hS.le
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  obtain ⟨m, hm⟩ := (hT.to_le (inf_le_left : T ⊓ Y ≤ T)).exists_card_eq
  have hdvd : 2 ^ m ∣ Nat.card Y := hm ▸ Subgroup.card_dvd_of_le (inf_le_right : T ⊓ Y ≤ Y)
  have hm' : m ≤ (Nat.card Y).factorization 2 :=
    (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 hdvd
  rw [hm, hS.card_eq]
  exact Nat.pow_le_pow_right Nat.two_pos hm'

omit [Finite G] in
theorem isInvColl_maxElemAbelian_of_normal {H Y : Subgroup G} (hYH : Y ≤ H)
    (hHY : H ≤ Subgroup.normalizer (Y : Set G)) :
    E1.IsInvColl H {A | IsMaxElemAbelian Y A} where
  le A hA := hA.1.trans hYH
  isElemAbelian A hA := hA.2.1
  conj A hA h hh := by
    refine ⟨cjSub_le (hHY hh) hA.1, isElemAbelian_cjSub hA.2.1, fun B hBY hB => ?_⟩
    show Nat.card B ≤ Nat.card (cjSub h A)
    rw [card_cjSub]
    exact hA.2.2 B hBY hB

theorem weakClosure_maxElemAbelian_of_inf {Y T S : Subgroup G} (hS : IsSylowIn 2 S Y)
    (hSTY : T ⊓ Y = S) : E1.weakClosure T {A | IsMaxElemAbelian Y A} = thompsonJ S := by
  rw [← weakClosure_maxElemAbelian hS]
  unfold E1.weakClosure
  refine le_antisymm (iSup₂_le fun A hA => iSup_le fun hAT => ?_)
    (iSup₂_le fun A hA => iSup_le fun hAS => ?_)
  · exact le_iSup₂_of_le A hA (le_iSup_of_le (hSTY ▸ le_inf hAT hA.1) le_rfl)
  · exact le_iSup₂_of_le A hA (le_iSup_of_le (hAS.trans (hSTY ▸ inf_le_left)) le_rfl)

theorem genCent_of_inE {j : ℕ} {H Y T S : Subgroup G} (hT : IsSylowIn 2 T H) (hYH : Y ≤ H)
    (hHY : H ≤ Subgroup.normalizer (Y : Set G)) (h2 : ∀ x ∈ H, ∃ k : ℕ, x ^ 2 ^ k ∈ Y)
    (hS : IsSylowIn 2 S Y) (hSTY : T ⊓ Y = S) (hH : E1.InE j H) : CentGen j Y S := by
  refine le_antisymm (sup_le inf_le_left (iSup₂_le fun _ _ => inf_le_left)) ?_
  have hΩ := isInvColl_maxElemAbelian_of_normal hYH hHY
  have hEF := (E1.inE_iff_inEFor hT).1 hH _ hΩ
  have hres := E1.eGenRes_sup_normalizer_eq hT hYH hHY h2 hΩ.conj hEF
  rw [weakClosure_maxElemAbelian_of_inf hS hSTY] at hres
  calc Y = E1.eGenRes j H T {A | IsMaxElemAbelian Y A} ⊔
        (Y ⊓ Subgroup.normalizer (thompsonJ S : Set G)) := hres.symm
    _ ≤ _ := by
      refine sup_le ?_ le_sup_left
      refine iSup₂_le fun A hA => iSup_le fun hAT => iSup₂_le fun K hK => ?_
      exact (twoResidual_le_iSup_of_normal hT hHY h2 hSTY hA (hSTY ▸ le_inf hAT hA.1)
        hK).trans le_sup_right

end E5
end CFSG.Quasithin
