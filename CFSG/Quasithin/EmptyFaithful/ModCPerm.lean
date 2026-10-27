module

public import CFSG.Quasithin.EmptyFaithful.ModCGlue
public import CFSG.Quasithin.EmptyFaithful.ModCModel6
public import CFSG.Quasithin.EmptyFaithful.ModCModel7

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

theorem input14610PermTuOutS_holds :
    ∀ (G : Type) [Group G] [Finite G] (T M H : Subgroup G) (u : G) (I I₂ K : Subgroup G),
      Facts14610 T M H u I I₂ → IsSylowTwoOf (T ⊓ I) I →
      yOfL22 T M ⊔ T = i1Of1469 T M I ⊔ pCoreOf 2 (yOfL22 T M ⊔ T) →
      Concl14610List T M I I₂ K →
      ((IsAlt 6 (OTwoQuot K) ∧ Nat.card (wOf1469 K) = 2 ^ 5) ∨
        (IsAlt 7 (OTwoQuot K) ∧ Nat.card (wOf1469 K) = 2 ^ 6)) →
      T ⊓ I = tU T u → Nat.card (conjClosure (VZ T M) I₂) ≠ 2 ^ 3 → u ∉ wOf1469 K → False := by
  intro G _ _ T M H u I I₂ K c hsyl hLT hK hperm hTu hne huW
  rcases hperm with ⟨hA, hW⟩ | ⟨hA, hW⟩
  · have hshort : IsShort2 K := ModB.isShort_of_alt hK (Or.inl hA)
    have hWU := ModB.wOf1469_eq_blockU_of_short hshort
    rw [hWU] at hW huW
    obtain ⟨Φ, hΦ⟩ := ModC.exists_core_equiv_six hshort hA hW
    have hcardA : Nat.card (alternatingGroup (Fin 6)) = 8 * 45 := by
      rw [nat_card_alternatingGroup]
      simp [Nat.factorial]
    exact ModC.out_of_module (n := 6) (by norm_num) ModC.modelOut6 (o := 45) ⟨22, by norm_num⟩ hcardA c hK
      hsyl hLT hshort Φ hΦ hTu hne huW
  · have hshort : IsShort2 K := ModB.isShort_of_alt hK (Or.inr hA)
    have hWU := ModB.wOf1469_eq_blockU_of_short hshort
    rw [hWU] at hW huW
    obtain ⟨Φ, hΦ⟩ := ModC.exists_core_equiv_seven hshort hA hW
    have hcardA : Nat.card (alternatingGroup (Fin 7)) = 8 * 315 := by
      rw [nat_card_alternatingGroup]
      simp [Nat.factorial]
    exact ModC.out_of_module (n := 7) (by norm_num) ModC.modelOut7 (o := 315) ⟨157, by norm_num⟩ hcardA c hK
      hsyl hLT hshort Φ hΦ hTu hne huW

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

end CFSG.Quasithin
