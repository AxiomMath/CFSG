module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLine
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLBstar

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover
  TableB TableBSymp NbrInnerRest CFSG.LieType.Steinberg.Minuscule

namespace ExcSplitL

section E7

variable
  {K : Type} [Field K] [Finite K] [CharP K 2]

theorem ggCenterPrime_recipe_E7 {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : GGCenterPrime p (TableBExc.RecipeGroup .E7 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker := CFSG.LieType.Steinberg.CentralExt.FieldFour.e7Isogeny_ker_eq_center (K := K)
  obtain ⟨hcard, -⟩ := CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e7 K
  have hodd : Nat.Coprime 2 (Nat.card K - 1) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
    fun h => ne_two_of_dvd_two_pow_sub_one hf (hK ▸ h) rfl
  have hZ : Subgroup.center (e7Data_valid.minGroup K) = ⊥ :=
    Subgroup.eq_bot_of_card_eq _ (by rw [hcard]; exact hodd)
  have hinj : Function.Injective (CFSG.LieType.Steinberg.Isogeny.e7Isogeny K) := by
    rw [← MonoidHom.ker_eq_bot_iff, hker, hZ]
  set e := MulEquiv.ofBijective (CFSG.LieType.Steinberg.Isogeny.e7Isogeny K)
    ⟨hinj, CFSG.LieType.Steinberg.Isogeny.e7Isogeny_surjective K⟩
  have := CFSG.LieType.Steinberg.CentralExt.FieldFour.finite_minGroup' (K := K) e7Data_valid
  obtain ⟨-, ⟨O⟩, -, -⟩ := CFSG.LieType.Steinberg.e7_conclusionB K
  obtain ⟨C, -, hC⟩ := e7Datum_commutatorFormula K _ (roots_eq isFiniteType_cartan_E7) O
  exact (OrthRest.center_data (e.trans (TableBExc.recipeEquiv .E7 K).symm) hZ
    (fun E _ _ π hπ hcen hc =>
      CFSG.LieType.Steinberg.CentralExt.FieldFour.exists_section_of_coprime
        (e7Datum_isCTGroupDatum K) (e7Datum_steinbergExtras K) (e7_chevalleyExtras K O C hC)
        E π hπ hcen hc) hp hp2).2

theorem ggNoInvariantLineTorus_E7 {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) :
    GGNoInvariantLineTorus p 7 (TableBExc.RecipeGroup .E7 K) (TableBExc.RecipeID .E7 K) := by
  have := TableBExc.finite_recipeGroup .E7 K
  exact ggNoInvariantLineTorus_of_reflElt hp (TableBExc.idImage_subset_inn_E7 K)
    (TableBExc.center_recipeGroup_eq_bot .E7 K)
    (CorFourTwoOpen.ggCenterCoprime_of_centerPrime (ggCenterPrime_recipe_E7 hf hK hp hp2))
    (CorFourTwoMore.ggTorusReflElt_of_mulEquiv (TableBExc.recipeEquiv .E7 K)
      (ggTorusReflElt_adjoint (τ := .E7) hp hpq
        (TableBExc.isUnit_det_cartan_of_eq hp CFSG.LieType.Chevalley.det_cartan_E7
          ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)))
        (cartanE_connected (by decide)) (fun i j h => cartanE_entry_ne_zero hp hp2 i j h)
        (TableBExc.card_torusPow_E7 hp hpq)
        (IOneRest.ggExcToralRankInput_E7E8 (Or.inl rfl) hp hp2 hpq)))

end E7

end ExcSplitL

open ExcSplitL

section Labels

theorem largeEvenLabelAll_noInvariantLine_excLSplit {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGExcLSplitLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGNoInvariantLineTorus p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hpn⟩ := h
  have hn : 1 ≤ n := hlab.1
  dsimp only at htag hpn hn
  have hp2 : p ≠ 2 := ne_two_of_dvd_two_pow_sub_one hn hpn
  rcases htag with rfl | h8 | h4
  · intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    refine recipeChevalley_and (fun K _ _ hK => ?_) hQ
    have : CharP K 2 := charP_two_of_card hK
    have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
    exact ⟨7, TableBExc.ggTorusLift_E7 hp hp2 hpq, ggNoInvariantLineTorus_E7 hn hK hp hp2 hpq⟩
  · exact largeEvenLabelAll_noInvariantLine_excLLine hp hlab ⟨Or.inl h8, hpn⟩
  · exact largeEvenLabelAll_noInvariantLine_excLLine hp hlab ⟨Or.inr h4, hpn⟩

theorem ggLNoInvariantLineInputOn_excLSplit : GGLNoInvariantLineInputOn GGExcLSplitLabel :=
  ggLNoInvariantLineInputOn_of_labels fun _ _ hp hlab h =>
    largeEvenLabelAll_noInvariantLine_excLSplit hp hlab h

end Labels

end CFSG.StandardType

end
