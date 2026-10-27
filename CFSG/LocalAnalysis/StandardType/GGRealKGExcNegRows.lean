module

public import CFSG.LocalAnalysis.StandardType.GGRealKGExcNegC
public import CFSG.LocalAnalysis.StandardType.GGRealKGFiveRows
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcE7Nons
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcE8Nons
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcF4Nons
public import CFSG.LocalAnalysis.StandardType.GGRealKGThree
import CFSG.LocalAnalysis.StandardType.GGKGForkExcNonsLang

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley

theorem ggRealKGNeg_rootDatum {τ : Tag} (hτ' : τ = .E7 ∨ τ = .E8 ∨ τ = .F4)
    {K : Type} [Field K] [Finite K] [CharP K 2] {p r₀ : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hpq : p ∣ Nat.card K + 1) (hq : 4 ≤ Nat.card K) (h : ExcSCTorusInput τ K p r₀) :
    GGKGRootDatum p r₀ (adjointGroup τ K) := by
  intro E hE h3 hr hsc
  obtain ⟨F, -, h2⟩ := h E hE h3 hr hsc
  exact ggRealKGNeg_rootDatumAt hτ' hp hp3 hpq hq F (h2 hpq)

private theorem ggRKR_recipe {τ : Tag} (hτ' : τ = .E7 ∨ τ = .E8 ∨ τ = .F4)
    {p n r₀ : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hpn : p ∣ 2 ^ n + 1) (hn : 2 ≤ n)
    (hin : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ n →
      ExcSCTorusInput τ K p r₀)
    (hlift : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ n →
      GGTorusLift p r₀ (TableBExc.RecipeGroup τ K))
    (hIp : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ n →
      GGOutdiagPrime p (TableBExc.RecipeGroup τ K) (TableBExc.RecipeID τ K))
    (hcp : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ n →
      GGCenterPrime p (TableBExc.RecipeGroup τ K))
    {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeChevalley τ.cartan (2 ^ n) false Q) :
    LargeEvenRecipeChevalley τ.cartan (2 ^ n) false
      (fun R _ I F => Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGTorusRootSL2 p r R I) := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  haveI : CharP K 2 := charP_two_of_card hK
  have hpq : p ∣ Nat.card K + 1 := by rw [hK]; exact hpn
  have hq : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hroot : GGKGRootDatum p r₀ (TableBExc.RecipeGroup τ K) :=
    ggKGRootDatum_of_mulEquiv (TableBExc.recipeEquiv τ K)
      (ggRealKGNeg_rootDatum hτ' hp hp3 hpq hq (hin K hK))
  refine ⟨K, inferInstance, inferInstance, hK, hQ, r₀, hlift K hK, ?_⟩
  exact ggTorusRootSL2_of_rootDatum hp (hIp K hK)
    (TableBExc.center_recipeGroup_eq_bot τ K) (hcp K hK) hroot

private theorem ggRKR_outdiagPrime_of_subset {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (h : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) : GGOutdiagPrime p R I :=
  fun _ hφ _ => h hφ

theorem ggRealRootSL2On_e7Nonsplit :
    GGRealRootSL2On fun p lab => 5 ≤ p ∧ GGKGRowLabel .e7Nonsplit p lab := by
  intro p lab hp hlab hR hs
  obtain ⟨hp5, htag, hpn⟩ := hs
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hpn hR
  subst htag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  exact ggRKR_recipe (τ := .E7) (Or.inl rfl) hp (by omega) hpn hR.2.1
    (fun K _ _ _ hK => ggKGExcInputNonsplit_E7 K p hp hp5 (by rw [hK]; exact hpn))
    (fun K _ _ _ hK => ggTorusLift_E7Plus hp (by omega) (by rw [hK]; exact hpn))
    (fun K _ _ _ _ => ggRKR_outdiagPrime_of_subset (TableBExc.idImage_subset_inn_E7 K))
    (fun K _ _ _ hK => ExcSplitL.ggCenterPrime_recipe_E7 hlab.1 hK hp (by omega)) hQ

theorem ggRealRootSL2On_e8Nonsplit :
    GGRealRootSL2On fun p lab => 5 ≤ p ∧ GGKGRowLabel .e8Nonsplit p lab := by
  intro p lab hp hlab hR hs
  obtain ⟨hp5, htag, hpn⟩ := hs
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hpn hR
  subst htag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  exact ggRKR_recipe (τ := .E8) (Or.inr (Or.inl rfl)) hp (by omega) hpn hR.2.1
    (fun K _ _ _ hK => ggKGExcInputNonsplit_E8 K p hp hp5 (by rw [hK]; exact hpn))
    (fun K _ _ _ hK => ggTorusLift_E8Plus hp (by omega) (by rw [hK]; exact hpn))
    (fun K _ _ _ _ => ggRKR_outdiagPrime_of_subset (TableBExc.idImage_subset_inn_E8 K))
    (fun K _ _ _ _ => ExcSplitL.ggCenterPrime_recipe_E8 hp (by omega)) hQ

theorem ggRealRootSL2On_f4Nonsplit :
    GGRealRootSL2On fun p lab => 5 ≤ p ∧ GGKGRowLabel .f4Nonsplit p lab := by
  intro p lab hp hlab hR hs
  obtain ⟨hp5, htag, hpn⟩ := hs
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hpn hR
  subst htag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  exact ggRKR_recipe (τ := .F4) (Or.inr (Or.inr rfl)) hp (by omega) hpn hR.2.1
    (fun K _ _ _ hK => ggKGExcInputNonsplit_F4 K p hp hp5 (by rw [hK]; exact hpn))
    (fun K _ _ _ hK => ggTorusLift_F4Plus hp (by omega) (by rw [hK]; exact hpn))
    (fun K _ _ _ _ => ggRKR_outdiagPrime_of_subset (TableBF4.idImage_subset_inn K))
    (fun K _ _ _ _ => ExcSplitL.ggCenterPrime_recipe_F4 hp (by omega)) hQ

theorem ggRealKGThreeRow_e7Nonsplit : GGRealKGThreeRow .e7Nonsplit := by
  intro p lab hp hlab hR hs
  obtain ⟨rfl, ⟨htag, hpn⟩, -⟩ := hs
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hpn hR
  subst htag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  exact ggRKR_recipe (τ := .E7) (Or.inl rfl) hp le_rfl hpn hR.2.1
    (fun K _ _ _ hK => excSCTorusInput_nonsplit_three_five (τ := .E7) (Or.inl rfl) (Or.inl rfl)
      (by rw [hK]; exact hpn))
    (fun K _ _ _ hK => ggTorusLift_E7Plus hp (by decide) (by rw [hK]; exact hpn))
    (fun K _ _ _ _ => ggRKR_outdiagPrime_of_subset (TableBExc.idImage_subset_inn_E7 K))
    (fun K _ _ _ hK => ExcSplitL.ggCenterPrime_recipe_E7 hlab.1 hK hp (by decide)) hQ

theorem ggRealKGThreeRow_e8Nonsplit : GGRealKGThreeRow .e8Nonsplit := by
  intro p lab hp hlab hR hs
  obtain ⟨rfl, ⟨htag, hpn⟩, -⟩ := hs
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hpn hR
  subst htag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  exact ggRKR_recipe (τ := .E8) (Or.inr (Or.inl rfl)) hp le_rfl hpn hR.2.1
    (fun K _ _ _ hK => excSCTorusInput_nonsplit_three_five (τ := .E8) (Or.inr rfl) (Or.inl rfl)
      (by rw [hK]; exact hpn))
    (fun K _ _ _ hK => ggTorusLift_E8Plus hp (by decide) (by rw [hK]; exact hpn))
    (fun K _ _ _ _ => ggRKR_outdiagPrime_of_subset (TableBExc.idImage_subset_inn_E8 K))
    (fun K _ _ _ _ => ExcSplitL.ggCenterPrime_recipe_E8 hp (by decide)) hQ

end CFSG.StandardType
