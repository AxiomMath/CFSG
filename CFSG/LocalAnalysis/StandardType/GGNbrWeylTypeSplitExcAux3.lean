module

public import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeSplitExcAux

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.RootSystem CFSG.RankThree.CentralCover Multiplicative

theorem ggWTSX_card_map_eq {G H : Type} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) (E : Subgroup G) :
    Nat.card E = Nat.card (E.map f) :=
  (Subgroup.card_map_of_injective (K := E) hf).symm

theorem ggWTSX_conj_inv_comp {G : Type} [Group G] (g : G) :
    (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id G := by
  ext x
  simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  group

theorem ggWTSX_weylFrameW_of_pow {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    {ι : Type} {M : CoxeterMatrix ι}
    (h : GGTorusWeylFrameW p r R {φ | φ ∈ I ∧ φ ^ p = 1} M) :
    GGTorusWeylFrameW p r R I M := by
  intro L' _ _ ψ A hA
  exact h L' ψ A (NbrTableBExc.ggTorusTBGroup_pow hA)

theorem ggWTSX_coordFrameElt_adjoint
    {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1)
    (hdet : IsUnit ((τ.cartan.det : ℤ) : ZMod p))
    (hV : Nat.card (TableBExc.torusPow τ K p) = p ^ τ.rank)
    (hT : GGExcToralRankInput τ K p)
    (hsymm : ∀ i j, τ.cartan i j = τ.cartan j i) :
    GGTorusCoordFrameElt p τ.rank (adjointGroup τ K) (coxeterMatrix (isFiniteType_cartan τ)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  intro E hE hr h3 k τ' hτ' hτ'E
  have hcardE : Nat.card E = p ^ τ.rank := by
    obtain ⟨g, hg⟩ := hT E hE hr
    rw [ggWTSX_card_map_eq (MulAut.conj g).toMonoidHom (MulAut.conj g).injective E, hg, hV]
  have hcardτ : Nat.card (Multiplicative (Fin k → ZMod p)) = Nat.card E :=
    Nat.card_congr ((MonoidHom.ofInjective hτ').trans (MulEquiv.subgroupCongr hτ'E))
  have hk : k = τ.rank := Nat.pow_right_injective hp.two_le (by
    show p ^ k = p ^ τ.rank
    rw [← card_multiplicative_fin_zmod k, hcardτ, hcardE])
  subst hk
  obtain ⟨ζ, hζo⟩ := @TableBSymp.exists_orderOf_eq_of_dvd K _ _ p ⟨hp⟩ hpq
  have hζ : ζ ^ p = 1 := by rw [← hζo]; exact pow_orderOf_eq_one ζ
  have hχinj : Function.Injective (chevTorus τ ζ hζ) := chevTorus_injective hζo hζ hdet
  have hχr : (chevTorus τ ζ hζ).range = TableBExc.torusPow τ K p :=
    TableBExc.range_chevTorus_eq_torusPow hζo hζ hdet hV
  have hbase := ggWTSX_frame_base (τ := τ) hp2 hsymm ζ hζ hχr hχinj
  obtain ⟨g, hg⟩ := hT E hE hr
  obtain ⟨τ'', hτ''⟩ : ∃ τ'' : Multiplicative (Fin τ.rank → ZMod p) →* adjointGroup τ K,
      τ'' = (MulAut.conj g).toMonoidHom.comp τ' := ⟨_, rfl⟩
  have hτ''inj : Function.Injective τ'' := by
    rw [hτ'']
    exact (MulAut.conj g).injective.comp hτ'
  have hτ''range : τ''.range = (chevTorus τ ζ hζ).range := by
    rw [hτ'', MonoidHom.range_comp, hτ'E, hg]
    exact hχr.symm
  obtain ⟨γ, hγ⟩ := ExcWeylOuter.exists_mulEquiv_comp_eq hτ''inj hχinj hτ''range
  have hτ'eq : (MulAut.conj g⁻¹).toMonoidHom.comp
      ((chevTorus τ ζ hζ).comp γ.toMonoidHom) = τ' := by
    rw [hγ, hτ'', ← MonoidHom.comp_assoc,
      ggWTSX_conj_inv_comp (G := adjointGroup τ K) g, MonoidHom.id_comp]
  have hframe := ggTorusCoordFrame_post (MulAut.conj g⁻¹)
    ((chevTorus τ ζ hζ).comp γ.toMonoidHom)
    (ggTorusCoordFrame_comp (chevTorus τ ζ hζ) γ hbase)
  rwa [hτ'eq] at hframe

theorem ggWTSX_weylTypeW_split
    {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1)
    (hdet : IsUnit ((τ.cartan.det : ℤ) : ZMod p))
    (hV : Nat.card (TableBExc.torusPow τ K p) = p ^ τ.rank)
    (hT : GGExcToralRankInput τ K p)
    (hsymm : ∀ i j, τ.cartan i j = τ.cartan j i)
    (hI : {φ : MulAut (TableBExc.RecipeGroup τ K) |
        φ ∈ TableBExc.RecipeID τ K ∧ φ ^ p = 1} ⊆
      Set.range (MulAut.conj : TableBExc.RecipeGroup τ K →* MulAut (TableBExc.RecipeGroup τ K)))
    (hZ : Subgroup.center (TableBExc.RecipeGroup τ K) = ⊥)
    (hM : GGIsWeylMatrix (coxeterMatrix (isFiniteType_cartan τ)))
    (hcard : Nat.card (coxeterMatrix (isFiniteType_cartan τ)).Group ≠ 12) :
    GGTorusWeylTypeW p τ.rank (TableBExc.RecipeGroup τ K) (TableBExc.RecipeID τ K) := by
  have hG : GGTorusWeylGenElt p τ.rank (TableBExc.RecipeGroup τ K) :=
    ggTorusWeylGenElt_of_mulEquiv (TableBExc.recipeEquiv τ K)
      (ExcWeylGen.ggTorusWeylGenElt_adjoint (τ := τ) hp hp2 hpq hdet hV hT)
  have hF' : GGTorusWeylFrameW p τ.rank (TableBExc.RecipeGroup τ K)
      {φ | φ ∈ TableBExc.RecipeID τ K ∧ φ ^ p = 1}
      (coxeterMatrix (isFiniteType_cartan τ)) :=
    ggTorusWeylFrameW_of_coordFrameElt hp hp2 hI hZ hG
      (ggTorusCoordFrameElt_of_mulEquiv (TableBExc.recipeEquiv τ K)
        (ggWTSX_coordFrameElt_adjoint (τ := τ) hp hp2 hpq hdet hV hT hsymm))
  exact ggWTF4_weylTypeW_of_frame hM hcard (ggWTSX_weylFrameW_of_pow hF')

theorem ggWTSX_coxeterE6_eq : CoxeterMatrix.E₆ = coxeterMatrix (isFiniteType_cartan .E6) := by
  have hc : CFSG.Blueprint.Chevalley.Tag.cartan .E6 = CartanMatrix.E 6 := cartanE_eq 6
  exact (coxeterMatrix_eq_of_ggIntCartan (C := CFSG.Blueprint.Chevalley.Tag.cartan .E6)
    (M := CoxeterMatrix.E₆) (isFiniteType_cartan .E6) (hc.symm ▸ ggIntCartan_E₆)).symm

theorem ggWTSX_isWeylMatrix_E6 :
    GGIsWeylMatrix (coxeterMatrix (isFiniteType_cartan .E6)) := by
  rw [← ggWTSX_coxeterE6_eq]
  exact Or.inr (Or.inl ⟨Equiv.refl _, rfl⟩)

theorem ggWTSX_card_E6 :
    Nat.card (coxeterMatrix (isFiniteType_cartan .E6)).Group ≠ 12 := by
  rw [NoOffExc.card_weyl_E6]
  norm_num

theorem ggWTSX_cartan_symm_E {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    ∀ i j : Fin τ.rank, τ.cartan i j = τ.cartan j i := by
  rcases hτ with rfl | rfl | rfl <;> intro i j <;> fin_cases i <;> fin_cases j <;> decide

theorem ggWTSX_weylTypeW_E8
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) :
    GGTorusWeylTypeW p 8 (TableBExc.RecipeGroup .E8 K) (TableBExc.RecipeID .E8 K) := by
  have hdet := TableBExc.isUnit_det_cartan_of_eq hp det_cartan_E8 (Nat.coprime_one_left p)
  have hV := TableBExc.card_torusPow_E8 (K := K) hp hpq
  have hT := IOneRest.ggExcToralRankInput_E7E8 (τ := .E8) (K := K) (Or.inr rfl) hp hp2 hpq
  exact ggWTSX_weylTypeW_split (τ := .E8) hp hp2 hpq hdet hV hT
    (ggWTSX_cartan_symm_E (Or.inr (Or.inr rfl)))
    (fun φ hφ => TableBExc.idImage_subset_inn_E8 K hφ.1)
    (TableBExc.center_recipeGroup_eq_bot .E8 K) ggWTEx1_isWeylMatrix_E8 ggWTEx1_card_E8

theorem ggWTSX_weylTypeW_E7
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) :
    GGTorusWeylTypeW p 7 (TableBExc.RecipeGroup .E7 K) (TableBExc.RecipeID .E7 K) := by
  have hdet := TableBExc.isUnit_det_cartan_of_eq hp det_cartan_E7
    ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  have hV := TableBExc.card_torusPow_E7 (K := K) hp hpq
  have hT := IOneRest.ggExcToralRankInput_E7E8 (τ := .E7) (K := K) (Or.inl rfl) hp hp2 hpq
  exact ggWTSX_weylTypeW_split (τ := .E7) hp hp2 hpq hdet hV hT
    (ggWTSX_cartan_symm_E (Or.inr (Or.inl rfl)))
    (fun φ hφ => TableBExc.idImage_subset_inn_E7 K hφ.1)
    (TableBExc.center_recipeGroup_eq_bot .E7 K) ggWTEx1_isWeylMatrix_E7 ggWTEx1_card_E7

theorem ggWTSX_weylTypeW_E6
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hpq : p ∣ Nat.card K - 1) :
    GGTorusWeylTypeW p 6 (TableBExc.RecipeGroup .E6 K) (TableBExc.RecipeID .E6 K) := by
  have hdet := TableBExc.isUnit_det_cartan_of_eq hp det_cartan_E6
    ((Nat.coprime_primes Nat.prime_three hp).2 (Ne.symm hp3))
  have hV := TableBExc.card_torusPow_E6 (K := K) hp hp3 hpq
  have hT := TableBExc.ggExcToralRankInput_E6_of_ne_three (K := K) hp hp2 hp3 hpq
  exact ggWTSX_weylTypeW_split (τ := .E6) hp hp2 hpq hdet hV hT
    (ggWTSX_cartan_symm_E (Or.inl rfl))
    (fun φ hφ => mem_range_conj_of_mem_recipeID_E6 hp hp3 hφ.1 hφ.2)
    (TableBExc.center_recipeGroup_eq_bot .E6 K) ggWTSX_isWeylMatrix_E6 ggWTSX_card_E6

end CFSG.StandardType

end
