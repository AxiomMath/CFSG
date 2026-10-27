module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.BorelTorusAbelianRootDatum
public import CFSG.LieType.HighestRoot.CentIsogenyE6E7
public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2OddSplit

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.Blueprint (LieModel AdjointQuotient)
open CFSG.Blueprint.Chevalley (adjointGroup)
open CFSG.LieType.Steinberg.Minuscule
open CFSG.LieType.Steinberg.Isogeny


theorem coprime_card_e6Torus {k : Type} [Field k] [Finite k] {p : ℕ} [Fact p.Prime]
    [CharP k p] :
    p.Coprime (Nat.card (⨆ i, e6Data_valid.torus k i :
      Subgroup ↥(e6Data_valid.minGroup k))) := by
  have : Finite ↥(e6Data_valid.minGroup k) :=
    CFSG.ClassicalInvolution.ModelFacts.ChevAut.finite_minGroup e6Data_valid k
  rw [Nat.Prime.coprime_iff_not_dvd Fact.out]
  refine CFSG.ClassicalInvolution.ModelFacts.ChevAut.not_dvd_card_of_forall_pow_card_sub_one
    (F := k) fun z hz => ?_
  exact CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed.pow_eq_one_of_mem_iSup
    (fun i _ hh =>
      CFSG.ClassicalInvolution.ModelFacts.ChevAut.torus_pow_card_sub_one e6Data_valid k i hh)
    (fun i j _ hh _ hh' => e6Data_valid.torus_commute k i j hh hh') hz


theorem oddCentralSplit_e6 {F : Type} [Field F] [Finite F] [CharP F 2] :
    CFSG.SeitzReduction.UnitaryPilot.OddCentralSplit ↥(e6Data_valid.minGroup F) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro E _ _ π hπ hcen hodd
  obtain ⟨O⟩ := CFSG.LieType.Steinberg.nonempty_commOrder_ofCartan
    (e6Datum F).isFiniteType (Dv := (e6Datum F).divisible) rfl
  have hE := e6_chevalleyExtras F O _
    (e6Data_valid.commutatorFormula_commC F posDef_cartan_E6 _
      (roots_eq isFiniteType_cartan_E6) O)
  exact CFSG.LieType.Steinberg.CentralExt.FieldFour.exists_section_of_coprime
    (e6Datum_isCTGroupDatum F) (e6Datum_steinbergExtras F) hE E π hπ hcen
    (Nat.coprime_two_left.2 hodd)

theorem exists_odd_cover_e6 {K : Type} [Group K] [Finite K] {m f : ℕ}
    (hL : LieModel (K ⧸ Subgroup.center K) .E6 m 2 f)
    (hq : CFSG.Open.IsQuasisimple K) (hodd : Odd (Nat.card (Subgroup.center K))) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (α : ↥(e6Data_valid.minGroup F) →* K),
      Function.Surjective α ∧ Odd (Nat.card α.ker) := by
  obtain ⟨-, F, hField, hFinite, hCard, ⟨φ⟩⟩ :=
    hL.chevalleyExceptionalModel
      (by decide : StatedLieTag.E6 ∈ CFSG.Blueprint.chevalleyExceptionalTags)
  let : Field F := hField
  let : Finite F := hFinite
  have hf1 : 1 ≤ f := hL.admissible.2.1
  have : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hf1 hCard
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite ↥(e6Data_valid.minGroup F) :=
    CFSG.ClassicalInvolution.ModelFacts.ChevAut.finite_minGroup e6Data_valid F
  let χ : AdjointQuotient .E6 F ≃* adjointGroup .E6 F :=
    (QuotientGroup.quotientMulEquivOfEq
      (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .E6) (K := F))).trans
      QuotientGroup.quotientBot
  let θ : K ⧸ Subgroup.center K ≃* adjointGroup .E6 F := φ.trans χ
  let η : K →* adjointGroup .E6 F :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hη : Function.Surjective η := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hηker : η.ker = Subgroup.center K := by
    rw [show η = θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K)) from rfl,
      MonoidHom.ker_comp_of_injective (QuotientGroup.mk' (Subgroup.center K))
        θ.toMonoidHom θ.injective,
      QuotientGroup.ker_mk']
  have : Group.IsPerfect K := ⟨hq.1⟩
  obtain ⟨α, hηα, hα, -⟩ :=
    CFSG.SeitzReduction.SeitzQ2.exists_surjective_of_oddCentralSplit
      (S := ↥(e6Data_valid.minGroup F)) (P := K) (Q := ↥(adjointGroup .E6 F))
      (β := e6Isogeny F) (η := η) (oddCentralSplit_e6 (F := F))
      (e6Isogeny_surjective F) hη (le_of_eq hηker) (by rw [hηker]; exact hodd)
  refine ⟨F, hField, hFinite, inferInstance, α, hα, ?_⟩
  have hker_le : α.ker ≤ (e6Isogeny F).ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    rw [← hηα x, hx, map_one]
  have h2 : ¬ 2 ∣ Nat.card (e6Isogeny F).ker :=
    CFSG.ClassicalInvolution.ModelFacts.ChevAut.e6Isogeny_not_dvd_card_ker F
  exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 fun h =>
    h2 (h.trans (Subgroup.card_dvd_of_le hker_le)))

theorem k_BorelTorusAbelian_E6 : K_BorelTorusAbelian_E6 := by
  refine k_BorelFamily_of_odd_card_center .E6 ?_
  intro K _ _ m f _ hL hq hoddZ S hS
  obtain ⟨F, hField, hFinite, hChar, α, hα, hαodd⟩ := exists_odd_cover_e6 hL hq hoddZ
  let : Field F := hField
  let : Finite F := hFinite
  let : CharP F 2 := hChar
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite ↥(e6Data_valid.minGroup F) :=
    CFSG.ClassicalInvolution.ModelFacts.ChevAut.finite_minGroup e6Data_valid F
  exact k_BorelFamily_of_odd_cover_rootDatum
    (D := e6Datum F) (n := e6Data_valid.nm F) (H := e6Data_valid.torus F)
    (e6Datum_isCTGroupDatum F) (e6Datum_steinbergExtras F) (e6Datum_bruhatExtras F)
    (fun γ _ => CFSG.LieType.HighestRoot.isPGroup_minRootGroup e6Data_valid F γ)
    (coprime_card_e6Torus (k := F) (p := 2)) α hα hαodd S hS

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
