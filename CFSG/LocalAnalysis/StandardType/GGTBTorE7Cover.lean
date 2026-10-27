module

public import CFSG.LocalAnalysis.StandardType.GGTBTorTransport
public import CFSG.LocalAnalysis.StandardType.GGTableBExcBasic
public import CFSG.LieType.Steinberg.CentralExt.FieldTwoMultiplier
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerF4Toral
public import CFSG.LieType.Steinberg.CentralExt.F4E8Multiplier

public noncomputable section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.CentralExt CFSG.HardMathSupport.Timmesfeld.CrossChar


theorem e7_even_bijective_of_perfect {K : Type} [Field K] [Finite K] [CharP K 2]
    {L : Type} [Group L] [Finite L] (hperf : commutator L = ⊤)
    (π : L →* adjointGroup .E7 K) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center L) : Function.Bijective π := by
  have : Group.IsPerfect L := ⟨hperf⟩
  have hEven : Even (Nat.card K) := by
    let : Fintype K := Fintype.ofFinite K
    apply (Nat.even_iff).mpr
    simpa only [Nat.card_eq_fintype_card] using
      FiniteField.even_card_of_char_two (ringChar.eq K 2)
  have hOdd : Odd (Nat.card K - 1) := by
    obtain ⟨n, hn⟩ := hEven
    have hpos : 1 < Nat.card K := Finite.one_lt_card
    exact ⟨n - 1, by omega⟩
  have hZ : Subgroup.center (e7Data_valid.minGroup K) = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    rw [(MinusculeClosed.card_center_e7 K).1]
    exact Nat.coprime_two_left.mpr hOdd |>.gcd_eq_one
  have hIso : Function.Injective (e7Isogeny K) := by
    rw [← MonoidHom.ker_eq_bot_iff, FieldFour.e7Isogeny_ker_eq_center, hZ]
  let eIso : e7Data_valid.minGroup K ≃* adjointGroup .E7 K :=
    MulEquiv.ofBijective (e7Isogeny K) ⟨hIso, e7Isogeny_surjective K⟩
  let η : L →* e7Data_valid.minGroup K := eIso.symm.toMonoidHom.comp π
  have hη : Function.Surjective η := eIso.symm.surjective.comp hπ
  have hηker : η.ker ≤ Subgroup.center L := by
    rw [MonoidHom.ker_comp_of_injective π eIso.symm.toMonoidHom eIso.symm.injective]
    exact hker
  have hsec : ∃ s : e7Data_valid.minGroup K →* L, ∀ g, η (s g) = g := by
    by_cases hK2 : Nat.card K = 2
    · exact FieldTwo.e7_two_exists_section hK2 L η hη hηker
    · by_cases hK4 : Nat.card K = 4
      · exact FieldFour.e7_four_exists_section (by simpa using hK4) L η hη hηker
      · have hK5 : 5 ≤ Nat.card K := by
          obtain ⟨n, hn⟩ := hEven
          have hpos : 1 < Nat.card K := Finite.one_lt_card
          omega
        exact MinusculeClosed.e7_exists_section_of_central hK5 hη hηker
  obtain ⟨s, hs⟩ := hsec
  have hη0 := SL2Closed.ker_eq_bot_of_section η hηker s hs
  have hηinj : Function.Injective η := (MonoidHom.ker_eq_bot_iff η).mp hη0
  exact ⟨fun a b hab => hηinj (congrArg eIso.symm hab), hπ⟩

theorem exists_e7_model_of_tbGroup {K : Type} [Field K] [Finite K] [CharP K 2]
    {p r : ℕ} {L : Type} [Group L] [Finite L]
    (ψ : L →* TableBExc.RecipeGroup .E7 K) (A : Subgroup (MulAut L))
    (hTB : GGTorusTBGroup p r (TableBExc.RecipeGroup .E7 K)
      (TableBExc.RecipeID .E7 K) L ψ A) :
    ∃ e : L ≃* adjointGroup .E7 K,
      (∀ l, e l = TableBExc.recipeEquiv .E7 K (ψ l)) ∧
      ∃ E : Subgroup (adjointGroup .E7 K), IsElemAbelian p E ∧ Nat.card E = Nat.card A ∧
        (∀ g : adjointGroup .E7 K, (∀ x ∈ E, g * x = x * g) → g ^ p = 1 → g ∈ E) ∧
        A.map (MulAut.congr e).toMonoidHom =
          E.map (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K)) := by
  obtain ⟨hψ, hker, hperf, hA, hAI, _, _, hSC⟩ := hTB
  let π : L →* adjointGroup .E7 K := (TableBExc.recipeEquiv .E7 K).toMonoidHom.comp ψ
  have hπ : Function.Surjective π := (TableBExc.recipeEquiv .E7 K).surjective.comp hψ
  have hπker : π.ker ≤ Subgroup.center L := by
    simpa only [π, MonoidHom.ker_comp_of_injective ψ
      (TableBExc.recipeEquiv .E7 K).toMonoidHom (TableBExc.recipeEquiv .E7 K).injective]
      using hker
  let e : L ≃* adjointGroup .E7 K :=
    MulEquiv.ofBijective π (e7_even_bijective_of_perfect hperf π hπ hπker)
  have he : ∀ l, e l = TableBExc.recipeEquiv .E7 K (ψ l) := fun _ => rfl
  obtain ⟨E, hE, hcard, hESC, hmodel⟩ := exists_inner_model_of_cover e
    (TableBExc.recipeEquiv .E7 K) ψ he mulAut_conj_injective_adjointGroup A hA
    (TableBExc.idImage_subset_inn_E7 K) hAI hSC
  exact ⟨e, he, E, hE, hcard, hESC, hmodel⟩

end CFSG.StandardType
