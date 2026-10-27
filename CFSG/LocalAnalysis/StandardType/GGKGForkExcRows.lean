module

public import CFSG.LocalAnalysis.StandardType.GGKGForkRows
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcAssembly
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwE6Frame
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLineE6
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLineE7
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLine
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Aut
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlusLift
public import CFSG.LocalAnalysis.StandardType.GGKGForkE6PlusLift

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley

@[expose] def GGKGExcInputSplit
    (τ : Tag) (r₀ : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (p : ℕ), p.Prime → 5 ≤ p →
    p ∣ Nat.card K - 1 → ExcSCTorusInput τ K p r₀

@[expose] def GGKGExcInputNonsplit
    (τ : Tag) (r₀ : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (p : ℕ), p.Prime → 5 ≤ p →
    p ∣ Nat.card K + 1 → ExcSCTorusInput τ K p r₀

@[expose] def GGKGTwE6InputSplit
    (r₀ : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (n p : ℕ), p.Prime → 5 ≤ p →
    Nat.card K = (2 ^ n) ^ 2 → (∀ c, σ c = c ^ (2 ^ n)) → p ∣ 2 ^ n - 1 →
      TwE6SCTorusInput K σ n p r₀

@[expose] def GGKGTwE6InputNonsplit
    (r₀ : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (n p : ℕ), p.Prime → 5 ≤ p →
    Nat.card K = (2 ^ n) ^ 2 → (∀ c, σ c = c ^ (2 ^ n)) → p ∣ 2 ^ n + 1 →
      TwE6SCTorusInput K σ n p r₀

private theorem ggKGRg_outdiagPrime_of_subset {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (h : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) : GGOutdiagPrime p R I :=
  fun _ hφ _ => h hφ

private theorem ggKGRg_recipe_two
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4)
    {p n r₀ : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpn : p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1)
    (hin : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ n →
      (p ∣ Nat.card K - 1 ∨ p ∣ Nat.card K + 1) → ExcSCTorusInput τ K p r₀)
    (hlift : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ n →
      (p ∣ Nat.card K - 1 ∨ p ∣ Nat.card K + 1) → GGTorusLift p r₀ (TableBExc.RecipeGroup τ K))
    (hIp : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ n →
      GGOutdiagPrime p (TableBExc.RecipeGroup τ K) (TableBExc.RecipeID τ K))
    (hcp : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ n →
      GGCenterPrime p (TableBExc.RecipeGroup τ K))
    {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeChevalley τ.cartan (2 ^ n) false Q) :
    LargeEvenRecipeChevalley τ.cartan (2 ^ n) false
      (fun R _ I F => Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGTorusLattice p r R I) := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  haveI : CharP K 2 := charP_two_of_card hK
  have hpq : p ∣ Nat.card K - 1 ∨ p ∣ Nat.card K + 1 := by rw [hK]; exact hpn
  have hlat : GGKGLatticeElt p r₀ (TableBExc.RecipeGroup τ K) :=
    ggKGLatticeElt_of_mulEquiv (TableBExc.recipeEquiv τ K)
      (ggKGExc_latticeElt hτ hp hp5 hpq (hin K hK hpq))
  refine ⟨K, inferInstance, inferInstance, hK, hQ, r₀, hlift K hK hpq, ?_⟩
  exact ggTorusLattice_of_latticeElt hp (hIp K hK)
    (TableBExc.center_recipeGroup_eq_bot τ K) (hcp K hK) hlat

theorem ggKGRg_recipe_one
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4)
    {p n r₀ : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hτ6 : τ = .E6 → 5 ≤ p) (hpn : p ∣ 2 ^ n - 1)
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
  have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
  have hroot : GGKGRootDatum p r₀ (TableBExc.RecipeGroup τ K) :=
    ggKGRootDatum_of_mulEquiv (TableBExc.recipeEquiv τ K)
      (ggKGExc_rootDatum hτ hp hp3 hτ6 hpq (hin K hK))
  refine ⟨K, inferInstance, inferInstance, hK, hQ, r₀, hlift K hK, ?_⟩
  exact ggTorusRootSL2_of_rootDatum hp (hIp K hK)
    (TableBExc.center_recipeGroup_eq_bot τ K) (hcp K hK) hroot

theorem ggKGTwoOn_excSplit
    (h6 : GGKGExcInputSplit .E6 6) (h7 : GGKGExcInputSplit .E7 7) (h8 : GGKGExcInputSplit .E8 8)
    (hF : GGKGExcInputSplit .F4 4) :
    GGKGTwoOn fun p lab =>
      (lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .F4) ∧ p ∣ 2 ^ lab.n - 1 := by
  intro p lab hp hlab hl hs Q hQ
  have hp5 : 5 ≤ p := hl.1
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hpn⟩ := hs
  rcases htag with rfl | rfl | rfl | rfl
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    exact ggKGRg_recipe_two (τ := .E6) (Or.inl rfl) hp hp5 (Or.inl hpn)
      (fun K _ _ _ hK _ => h6 K p hp hp5 (by rw [hK]; exact hpn))
      (fun K _ _ _ hK _ =>
        TableBExc.ggTorusLift_E6 hp (by omega) (by omega) (by rw [hK]; exact hpn))
      (fun K _ _ _ _ => TableBExc.ggOutdiagPrime_E6 hp (by omega))
      (fun K _ _ _ _ => ExcSplitL.ggCenterPrime_recipe_E6 hp (by omega) (by omega)) hQ
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    exact ggKGRg_recipe_two (τ := .E7) (Or.inr (Or.inl rfl)) hp hp5 (Or.inl hpn)
      (fun K _ _ _ hK _ => h7 K p hp hp5 (by rw [hK]; exact hpn))
      (fun K _ _ _ hK _ =>
        TableBExc.ggTorusLift_E7 hp (by omega) (by rw [hK]; exact hpn))
      (fun K _ _ _ _ => ggKGRg_outdiagPrime_of_subset (TableBExc.idImage_subset_inn_E7 K))
      (fun K _ _ _ hK => ExcSplitL.ggCenterPrime_recipe_E7 hlab.1 hK hp (by omega)) hQ
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    exact ggKGRg_recipe_two (τ := .E8) (Or.inr (Or.inr (Or.inl rfl))) hp hp5 (Or.inl hpn)
      (fun K _ _ _ hK _ => h8 K p hp hp5 (by rw [hK]; exact hpn))
      (fun K _ _ _ hK _ =>
        TableBExc.ggTorusLift_E8 hp (by omega) (by rw [hK]; exact hpn))
      (fun K _ _ _ _ => ggKGRg_outdiagPrime_of_subset (TableBExc.idImage_subset_inn_E8 K))
      (fun K _ _ _ _ => ExcSplitL.ggCenterPrime_recipe_E8 hp (by omega)) hQ
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    exact ggKGRg_recipe_two (τ := .F4) (Or.inr (Or.inr (Or.inr rfl))) hp hp5 (Or.inl hpn)
      (fun K _ _ _ hK _ => hF K p hp hp5 (by rw [hK]; exact hpn))
      (fun K _ _ _ hK _ =>
        TableBF4.ggTorusLift_F4 hp (by omega) (by rw [hK]; exact hpn))
      (fun K _ _ _ _ => ggKGRg_outdiagPrime_of_subset (TableBF4.idImage_subset_inn K))
      (fun K _ _ _ _ => ExcSplitL.ggCenterPrime_recipe_F4 hp (by omega)) hQ

theorem ggKGTwoOn_excNonsplit
    (h6 : GGKGExcInputNonsplit .E6 4) (h7 : GGKGExcInputNonsplit .E7 6)
    (h8 : GGKGExcInputNonsplit .E8 7) (hF : GGKGExcInputNonsplit .F4 3) :
    GGKGTwoOn fun p lab =>
      (lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .F4) ∧ p ∣ 2 ^ lab.n + 1 := by
  intro p lab hp hlab hl hs Q hQ
  have hp5 : 5 ≤ p := hl.1
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hpn⟩ := hs
  rcases htag with rfl | rfl | rfl | rfl
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    exact ggKGRg_recipe_two (τ := .E6) (Or.inl rfl) hp hp5 (Or.inr hpn)
      (fun K _ _ _ hK _ => h6 K p hp hp5 (by rw [hK]; exact hpn))
      (fun K _ _ _ hK _ =>
        ggTorusLift_E6Plus hp hp5 (by rw [hK]; exact hpn))
      (fun K _ _ _ _ => TableBExc.ggOutdiagPrime_E6 hp (by omega))
      (fun K _ _ _ _ => ExcSplitL.ggCenterPrime_recipe_E6 hp (by omega) (by omega)) hQ
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    exact ggKGRg_recipe_two (τ := .E7) (Or.inr (Or.inl rfl)) hp hp5 (Or.inr hpn)
      (fun K _ _ _ hK _ => h7 K p hp hp5 (by rw [hK]; exact hpn))
      (fun K _ _ _ hK _ => ggTorusLift_E7Plus hp (by omega) (by rw [hK]; exact hpn))
      (fun K _ _ _ _ => ggKGRg_outdiagPrime_of_subset (TableBExc.idImage_subset_inn_E7 K))
      (fun K _ _ _ hK => ExcSplitL.ggCenterPrime_recipe_E7 hlab.1 hK hp (by omega)) hQ
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    exact ggKGRg_recipe_two (τ := .E8) (Or.inr (Or.inr (Or.inl rfl))) hp hp5 (Or.inr hpn)
      (fun K _ _ _ hK _ => h8 K p hp hp5 (by rw [hK]; exact hpn))
      (fun K _ _ _ hK _ => ggTorusLift_E8Plus hp (by omega) (by rw [hK]; exact hpn))
      (fun K _ _ _ _ => ggKGRg_outdiagPrime_of_subset (TableBExc.idImage_subset_inn_E8 K))
      (fun K _ _ _ _ => ExcSplitL.ggCenterPrime_recipe_E8 hp (by omega)) hQ
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    exact ggKGRg_recipe_two (τ := .F4) (Or.inr (Or.inr (Or.inr rfl))) hp hp5 (Or.inr hpn)
      (fun K _ _ _ hK _ => hF K p hp hp5 (by rw [hK]; exact hpn))
      (fun K _ _ _ hK _ => ggTorusLift_F4Plus hp (by omega) (by rw [hK]; exact hpn))
      (fun K _ _ _ _ => ggKGRg_outdiagPrime_of_subset (TableBF4.idImage_subset_inn K))
      (fun K _ _ _ _ => ExcSplitL.ggCenterPrime_recipe_F4 hp (by omega)) hQ

theorem ggKGOneOn_excSplit
    (h6 : GGKGExcInputSplit .E6 6) (h7 : GGKGExcInputSplit .E7 7) (h8 : GGKGExcInputSplit .E8 8)
    (hF : GGKGExcInputSplit .F4 4) :
    GGKGOneOn fun p lab =>
      (lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .F4) ∧ p ∣ 2 ^ lab.n - 1 := by
  intro p lab hp hlab hl hs Q hQ
  have hp5 : 5 ≤ p := hl.1
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hpn⟩ := hs
  rcases htag with rfl | rfl | rfl | rfl
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    exact ggKGRg_recipe_one (τ := .E6) (Or.inl rfl) hp (by omega) (fun _ => hp5) hpn
      (fun K _ _ _ hK => h6 K p hp hp5 (by rw [hK]; exact hpn))
      (fun K _ _ _ hK => TableBExc.ggTorusLift_E6 hp (by omega) (by omega) (by rw [hK]; exact hpn))
      (fun K _ _ _ _ => TableBExc.ggOutdiagPrime_E6 hp (by omega))
      (fun K _ _ _ _ => ExcSplitL.ggCenterPrime_recipe_E6 hp (by omega) (by omega)) hQ
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    exact ggKGRg_recipe_one (τ := .E7) (Or.inr (Or.inl rfl)) hp (by omega) (fun _ => hp5) hpn
      (fun K _ _ _ hK => h7 K p hp hp5 (by rw [hK]; exact hpn))
      (fun K _ _ _ hK => TableBExc.ggTorusLift_E7 hp (by omega) (by rw [hK]; exact hpn))
      (fun K _ _ _ _ => ggKGRg_outdiagPrime_of_subset (TableBExc.idImage_subset_inn_E7 K))
      (fun K _ _ _ hK => ExcSplitL.ggCenterPrime_recipe_E7 hlab.1 hK hp (by omega)) hQ
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    exact ggKGRg_recipe_one (τ := .E8) (Or.inr (Or.inr (Or.inl rfl))) hp (by omega) (fun _ => hp5)
      hpn
      (fun K _ _ _ hK => h8 K p hp hp5 (by rw [hK]; exact hpn))
      (fun K _ _ _ hK => TableBExc.ggTorusLift_E8 hp (by omega) (by rw [hK]; exact hpn))
      (fun K _ _ _ _ => ggKGRg_outdiagPrime_of_subset (TableBExc.idImage_subset_inn_E8 K))
      (fun K _ _ _ _ => ExcSplitL.ggCenterPrime_recipe_E8 hp (by omega)) hQ
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    exact ggKGRg_recipe_one (τ := .F4) (Or.inr (Or.inr (Or.inr rfl))) hp (by omega) (fun _ => hp5)
      hpn
      (fun K _ _ _ hK => hF K p hp hp5 (by rw [hK]; exact hpn))
      (fun K _ _ _ hK => TableBF4.ggTorusLift_F4 hp (by omega) (by rw [hK]; exact hpn))
      (fun K _ _ _ _ => ggKGRg_outdiagPrime_of_subset (TableBF4.idImage_subset_inn K))
      (fun K _ _ _ _ => ExcSplitL.ggCenterPrime_recipe_F4 hp (by omega)) hQ

end CFSG.StandardType

end
