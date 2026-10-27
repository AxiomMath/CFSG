module

public import CFSG.LocalAnalysis.StandardType.GGRootGenAvoidReflModel
public import CFSG.LocalAnalysis.StandardType.GGExcSplitRootGenRoot
public import CFSG.LocalAnalysis.StandardType.GGExcSplitRootGenModel
public import CFSG.LocalAnalysis.StandardType.GGExcSplitRootGenComp
public import CFSG.LocalAnalysis.StandardType.GGExcSplitRootGenGen
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerF4
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerRestExc
public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperRestExc
public import CFSG.LocalAnalysis.StandardType.GGTableBF4

public section

namespace CFSG.StandardType

namespace ExcSplitRootGen

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {τ : Tag} {K : Type} [Field K]

private theorem congr_image_inner {R G : Type} [Group R] [Group G] (e : R ≃* G) {p : ℕ}
    {I : Set (MulAut R)} (hI : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R)) :
    ∀ φ ∈ (MulAut.congr e) '' I, φ ^ p = 1 →
      φ ∈ Set.range (MulAut.conj : G →* MulAut G) := by
  rintro _ ⟨φ, hφ, rfl⟩ hpw
  have hφp : φ ^ p = 1 := (MulAut.congr e).injective (by rw [map_pow, hpw, map_one])
  obtain ⟨g, rfl⟩ := hI φ hφ hφp
  refine ⟨e g, ?_⟩
  ext x
  simp [MulAut.congr_apply, MulAut.conj_apply]

private theorem exists_mulEquiv_of_conj_eq {p : ℕ}
    [NeZero p]
    (hfullp : ∀ a : Fin τ.rank → Kˣ, (∀ i, a i ^ p = 1) → rootDiagUnit τ a ∈ torusGroup τ K)
    {ζ : Kˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) {E : Subgroup (adjointGroup τ K)}
    {g : adjointGroup τ K} (hg : E.map (MulAut.conj g).toMonoidHom = TableBExc.torusPow τ K p) :
    ∃ α : adjointGroup τ K ≃* adjointGroup τ K,
      E = (excTorusHom hfullp hζ).range.map α.toMonoidHom := by
  refine ⟨MulAut.conj g⁻¹, ?_⟩
  rw [range_excTorusHom hfullp hζo hζ, ← hg, Subgroup.map_map]
  ext x
  rw [Subgroup.mem_map]
  constructor
  · intro hx
    exact ⟨x, hx, by simp [MulAut.conj_apply, mul_assoc]⟩
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy

end ExcSplitRootGen

open CFSG.Assembly CFSG.Blueprint.Chevalley

theorem ggTorusRootGenAvoidKG_excSplit
    {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hτ : (τ = .E6 ∧ p ≠ 3) ∨ τ = .E7 ∨ τ = .E8) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) :
    GGTorusRootGenAvoidKG p τ.rank (TableBExc.RecipeGroup τ K) (TableBExc.RecipeID τ K) := by
  open CFSG.LieType.Chevalley TableB Multiplicative
    CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley ExcSplitRootGen in
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := K) hpq
  have hζ : ζ ^ p = 1 := hζo ▸ pow_orderOf_eq_one ζ
  have hτ' : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4 := by
    rcases hτ with ⟨h, -⟩ | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  have hfullp : ∀ a : Fin τ.rank → Kˣ, (∀ i, a i ^ p = 1) → rootDiagUnit τ a ∈ torusGroup τ K := by
    rcases hτ with ⟨rfl, hp3⟩ | h | h
    · exact TableBExc.fullp_E6 hp.one_lt ((Nat.coprime_primes Nat.prime_three hp).2 (Ne.symm hp3))
    · exact fun a _ => TableBExc.full_of_E7_E8 (Or.inl h) a
    · exact fun a _ => TableBExc.full_of_E7_E8 (Or.inr h) a
  have hT : GGExcToralRankInput τ K p := by
    rcases hτ with ⟨rfl, hp3⟩ | h | h
    · exact TableBExc.ggExcToralRankInput_E6_of_ne_three hp hp2 hp3 hpq
    · exact IOneRest.ggExcToralRankInput_E7E8 (Or.inl h) hp hp2 hpq
    · exact IOneRest.ggExcToralRankInput_E7E8 (Or.inr h) hp hp2 hpq
  have hrefl : GGTorusReflElt p τ.rank (adjointGroup τ K) := by
    rcases hτ with ⟨rfl, hp3⟩ | rfl | rfl
    · exact NbrInnerRest.ggTorusReflElt_adjoint (τ := .E6) hp hpq
        (TableBExc.isUnit_det_cartan_of_eq hp CFSG.LieType.Chevalley.det_cartan_E6
          ((Nat.coprime_primes Nat.prime_three hp).2 (Ne.symm hp3)))
        (NbrInnerRest.cartanE_connected (by decide))
        (fun i j h => NbrInnerRest.cartanE_entry_ne_zero hp hp2 i j h)
        (TableBExc.card_torusPow_E6 hp hp3 hpq) hT
    · exact NbrInnerRest.ggTorusReflElt_adjoint (τ := .E7) hp hpq
        (TableBExc.isUnit_det_cartan_of_eq hp CFSG.LieType.Chevalley.det_cartan_E7
          ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)))
        (NbrInnerRest.cartanE_connected (by decide))
        (fun i j h => NbrInnerRest.cartanE_entry_ne_zero hp hp2 i j h)
        (TableBExc.card_torusPow_E7 hp hpq) hT
    · exact NbrInnerRest.ggTorusReflElt_adjoint (τ := .E8) hp hpq
        (TableBExc.isUnit_det_cartan_of_eq hp CFSG.LieType.Chevalley.det_cartan_E8
          (Nat.coprime_one_left p))
        (NbrInnerRest.cartanE_connected (by decide))
        (fun i j h => NbrInnerRest.cartanE_entry_ne_zero hp hp2 i j h)
        (TableBExc.card_torusPow_E8 hp hpq) hT
  have hinn : ∀ φ ∈ TableBExc.RecipeID τ K, φ ^ p = 1 →
      φ ∈ Set.range (MulAut.conj : TableBExc.RecipeGroup τ K →* MulAut _) := by
    rcases hτ with ⟨rfl, hp3⟩ | rfl | rfl
    · exact fun φ hφ hφp => mem_range_conj_of_mem_recipeID_E6 hp hp3 hφ hφp
    · exact fun φ hφ _ => TableBExc.idImage_subset_inn_E7 K hφ
    · exact fun φ hφ _ => TableBExc.idImage_subset_inn_E8 K hφ
  let e := TableBExc.recipeEquiv τ K
  refine ggTorusRootGenAvoidKG_of_mulEquiv e (I' := (MulAut.congr e) '' TableBExc.RecipeID τ K)
    (fun φ hφ => ⟨φ, hφ, rfl⟩) ?_
  have hroot : ∀ α β : Fin τ.rank → ℤ, IsRoot τ α → IsRoot τ β → (∀ t : Fin τ.rank → ZMod p,
      ∑ j, (α j : ZMod p) * t j = 0 → ∑ j, (β j : ZMod p) * t j = 0) → β = α ∨ β = -α :=
    fun α β hα hβ h => eq_or_eq_neg_of_forall_sum_eq_zero hτ' hp2 hα hβ h
  haveI : Nonempty {α : Fin τ.rank → ℤ // IsRoot τ α} :=
    ⟨⟨Pi.single ⟨0, τ.rank_pos⟩ 1, isRoot_single τ _⟩⟩
  refine ggTorusRootGenAvoidKG_of_reflTorusModel hp hp2
    (by rw [← Subgroup.map_center_eq e, TableBExc.center_recipeGroup_eq_bot τ K, Subgroup.map_bot])
    (congr_image_inner e hinn) hrefl (excTorusHom hfullp hζ)
    (excTorusHom_injective hfullp hζo hζ)
    (fun E hE hr _ => by
      obtain ⟨g, hg⟩ := hT E hE hr
      exact exists_mulEquiv_of_conj_eq hfullp hζo hζ hg)
    (ι := {α : Fin τ.rank → ℤ // IsRoot τ α}) excWeyl (fun i => excRefl i.1)
    (fun i => excComp i.1) (fun i t => excWeyl_conj_excTorusHom hfullp hζ i t)
    (fun i t => excRefl_excRefl i.2 t) (fun i => card_fix_excRefl hp2 i.2) excWeyl_mem_excComp
    (fun i => isComponentOf_excComp hp2 hfullp hζo hζ i.2 (excRefl_eq_self_iff hp2 i.2)
      (fun β hβ h => hroot i.1 β i.2 hβ h))
    (fun i => dvd_card_excComp hp2 hζo i.2 (fun β hβ h => hroot i.1 β i.2 hβ h))
    (fun j => iSup_excComp_ne hτ' (fun α hα => excRefl_eq_self_iff hp2 hα) hroot j)

theorem ggTorusRootGenAvoidKG_F4Split
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) :
    GGTorusRootGenAvoidKG p 4 (TableBF4.RecipeGroup K) (TableBF4.RecipeID K) := by
  open CFSG.LieType.Chevalley TableB Multiplicative
    CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley ExcSplitRootGen in
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := K) hpq
  have hζ : ζ ^ p = 1 := hζo ▸ pow_orderOf_eq_one ζ
  have hτ' : Tag.F4 = .E6 ∨ Tag.F4 = .E7 ∨ Tag.F4 = .E8 ∨ Tag.F4 = .F4 :=
    Or.inr (Or.inr (Or.inr rfl))
  have hfullp : ∀ a : Fin Tag.F4.rank → Kˣ, (∀ i, a i ^ p = 1) →
      rootDiagUnit .F4 a ∈ torusGroup .F4 K := fun a _ =>
    (even_power_two_Cartan_root_diagonals_inner .F4 (Or.inr (Or.inl rfl)) K
      (ringChar.eq K 2)).1 a
  have hT : GGF4ToralRankInput K p :=
    ggF4ToralRankInput_of_three hp hp2 hpq fun _ => ggF4ThreeRankInput_holds
  have hpow : TableBF4.torusPow K p = TableBExc.torusPow .F4 K p := Subgroup.ext fun _ => Iff.rfl
  let e := TableBF4.recipeEquiv K
  refine ggTorusRootGenAvoidKG_of_mulEquiv e (I' := (MulAut.congr e) '' TableBF4.RecipeID K)
    (fun φ hφ => ⟨φ, hφ, rfl⟩) ?_
  have hroot : ∀ α β : Fin Tag.F4.rank → ℤ, IsRoot .F4 α → IsRoot .F4 β →
      (∀ t : Fin Tag.F4.rank → ZMod p, ∑ j, (α j : ZMod p) * t j = 0 →
        ∑ j, (β j : ZMod p) * t j = 0) → β = α ∨ β = -α :=
    fun α β hα hβ h => eq_or_eq_neg_of_forall_sum_eq_zero hτ' hp2 hα hβ h
  haveI : Nonempty {α : Fin Tag.F4.rank → ℤ // IsRoot .F4 α} :=
    ⟨⟨Pi.single ⟨0, Tag.F4.rank_pos⟩ 1, isRoot_single .F4 _⟩⟩
  refine ggTorusRootGenAvoidKG_of_reflTorusModel hp hp2
    (by rw [← Subgroup.map_center_eq e, TableBF4.center_recipeGroup_eq_bot K, Subgroup.map_bot])
    (congr_image_inner e fun φ hφ _ => TableBF4.idImage_subset_inn K hφ)
    (ggTorusReflElt_adjointF4 hp hp2 hpq hT) (excTorusHom hfullp hζ)
    (excTorusHom_injective hfullp hζo hζ)
    (fun E hE hr _ => by
      obtain ⟨g, hg⟩ := hT E hE hr
      exact exists_mulEquiv_of_conj_eq hfullp hζo hζ (hg.trans hpow))
    (ι := {α : Fin Tag.F4.rank → ℤ // IsRoot .F4 α}) excWeyl (fun i => excRefl i.1)
    (fun i => excComp i.1) (fun i t => excWeyl_conj_excTorusHom hfullp hζ i t)
    (fun i t => excRefl_excRefl i.2 t) (fun i => card_fix_excRefl hp2 i.2) excWeyl_mem_excComp
    (fun i => isComponentOf_excComp hp2 hfullp hζo hζ i.2 (excRefl_eq_self_iff hp2 i.2)
      (fun β hβ h => hroot i.1 β i.2 hβ h))
    (fun i => dvd_card_excComp hp2 hζo i.2 (fun β hβ h => hroot i.1 β i.2 hβ h))
    (fun j => iSup_excComp_ne hτ' (fun α hα => excRefl_eq_self_iff hp2 hα) hroot j)

end CFSG.StandardType

end
