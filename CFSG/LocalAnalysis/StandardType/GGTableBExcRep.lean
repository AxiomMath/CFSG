module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcCoverRows
public import CFSG.LocalAnalysis.StandardType.GGTableBRepAbstract
public import CFSG.LocalAnalysis.StandardType.GGTableBMarkedTransfer
public import CFSG.LocalAnalysis.StandardType.GGTableBTorusFix
public import CFSG.LocalAnalysis.StandardType.GGTableBPositionToralExc
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangModel
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExc

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley RecipeExcLang

private noncomputable def modelRepresentativeAt (τ : Tag) (K : Type) [Field K]
    (S : (Fin τ.rank → ℤ) → Prop) (p : ℕ) : Prop :=
  ∀ f : MulAut (LargeEvenCenterQuot (MarkChev.chevH τ.cartan S K false)),
    GGTableBFieldSylowMark p
        (RecipeFieldExcInn.markFieldImage S K (MarkChev.chevH τ.cartan S K false)) f →
      GGTableBFieldRepresentativeAt p
        (RecipeExcLang.markIDImage S K (MarkChev.chevH τ.cartan S K false)) f

private theorem mulAut_mul_conj {R : Type} [Group R] (f : MulAut R) (y : R) :
    f * MulAut.conj y = MulAut.conj (f y) * f := by
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]

private theorem dvd_two_pow_sub_one_ne_two {n p : ℕ} (hn : 1 ≤ n) (hp : p ∣ 2 ^ n - 1) :
    p ≠ 2 := by
  rintro rfl
  have h1 : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h2 : 0 < 2 ^ (n - 1) := by positivity
  omega

private theorem modelRepresentativeAt_isRoot
    {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1)
    (hcase : τ = .E7 ∨ τ = .E8 ∨ τ = .F4 ∨ (τ = .E6 ∧ p ≠ 3)) :
    modelRepresentativeAt τ K (IsRoot τ) p := by
  unfold modelRepresentativeAt
  suffices key : ∀ H : Subgroup (MarkChev.GLS (IsRoot τ) K),
      H = adjointGroup τ K →
      ∀ f : MulAut (LargeEvenCenterQuot H),
        GGTableBFieldSylowMark p (RecipeFieldExcInn.markFieldImage (IsRoot τ) K H) f →
        GGTableBFieldRepresentativeAt p (markIDImage (IsRoot τ) K H) f from
    key _ (chevH_false_eq_adjointGroup K τ)
  intro H hH
  subst hH
  intro f hf
  obtain ⟨hfmem, ⟨c, hford⟩, -⟩ := hf
  obtain ⟨σ, hσ⟩ := RecipeExcLang.exists_eq_entrywise_of_mem_closure_markField hfmem
  have hfpow : f ^ p ^ c = 1 := hford ▸ pow_orderOf_eq_one f
  have hσpow : (entrywiseAdjointAut τ σ) ^ p ^ c = 1 := by
    rw [← hσ, ← map_pow, hfpow, map_one]
  have hmodel : GGTableBFieldRepresentativeAt p (Set.range (inndiagConj τ K))
      (entrywiseAdjointAut τ σ) := by
    intro M _ _ L' E θ hE hP
    have hg : ∃ g : adjointGroup τ K, ∀ e : E, ∃ v ∈ TableBExc.torusPow τ K p,
        ggLAut L' θ ⟨e, hE e.2⟩ = MulAut.conj (g⁻¹ * v * g) := by
      rcases hcase with h7 | h8 | h4 | ⟨h6, hp3⟩
      · subst h7
        exact exists_position_conj_torusPow (Or.inl rfl) hp hp2 hpq hP
      · subst h8
        exact exists_position_conj_torusPow (Or.inr (Or.inl rfl)) hp hp2 hpq hP
      · subst h4
        exact exists_position_conj_torusPow (Or.inr (Or.inr rfl)) hp hp2 hpq hP
      · subst h6
        exact exists_position_conj_torusPow_E6 hp hp2 hp3 hpq hP
    obtain ⟨g, hg⟩ := hg
    have hfix : ∀ s ∈ Set.range (fun e : E => ggLAut L' θ ⟨e, hE e.2⟩),
        entrywiseAdjointAut τ σ * (MulAut.conj g * s * (MulAut.conj g)⁻¹) =
          (MulAut.conj g * s * (MulAut.conj g)⁻¹) * entrywiseAdjointAut τ σ := by
      rintro s ⟨e, rfl⟩
      obtain ⟨v, hv, hve⟩ := hg e
      change entrywiseAdjointAut τ σ *
          (MulAut.conj g * ggLAut L' θ ⟨e, hE e.2⟩ * (MulAut.conj g)⁻¹) =
        (MulAut.conj g * ggLAut L' θ ⟨e, hE e.2⟩ * (MulAut.conj g)⁻¹) *
          entrywiseAdjointAut τ σ
      rw [hve]
      have hcs : MulAut.conj g * MulAut.conj (g⁻¹ * v * g) * (MulAut.conj g)⁻¹ =
          MulAut.conj v := by
        rw [← map_inv, ← map_mul, ← map_mul]
        congr 1
        group
      rw [hcs, mulAut_mul_conj, entrywiseAdjointAut_apply_of_mem_torusPow hp hσpow hv]
    obtain ⟨u, hu, hcomm⟩ := ggTableB_representative_of_conj_fixed (R := adjointGroup τ K)
      (I := Set.range (inndiagConj τ K))
      (fun ρ : adjointGroup τ K => ⟨⟨ρ, adjointGroup_le_inndiagGroup ρ.2⟩,
        RecipeExcLang.inndiagConj_of_mem ρ⟩)
      (entrywiseAdjointAut τ σ) (Set.range fun e : E => ggLAut L' θ ⟨e, hE e.2⟩)
      (MulAut.conj g) ⟨g, rfl⟩ hfix
    exact ⟨u, hu, fun e => hcomm _ ⟨e, rfl⟩⟩
  refine ggTableBFieldRepresentativeAt_of_mulEquiv
    (I' := Set.range (inndiagConj τ K))
    (centerQuotEquivOfBot center_adjointGroup_eq_bot) ?_ ?_ ?_
  · intro φ hφ
    obtain ⟨w, hw⟩ := RecipeExcLang.exists_inndiagConj_of_mem_markID hφ
    exact ⟨w, hw.symm⟩
  · rintro φ' ⟨w, rfl⟩
    exact RecipeExcLang.inndiagConj_mem_markID w
  · show GGTableBFieldRepresentativeAt p (Set.range (inndiagConj τ K))
      (MulAut.congr (centerQuotEquivOfBot center_adjointGroup_eq_bot) f)
    rw [show MulAut.congr (centerQuotEquivOfBot center_adjointGroup_eq_bot) f =
        entrywiseAdjointAut τ σ from hσ]
    exact hmodel

private theorem fieldRepresentative_chev
    {τ : Tag} {K : Type} [Field K] [Finite K] {n p : ℕ}
    (hp : p.Prime) (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) (hpq : p ∣ 2 ^ n - 1)
    (hcase : τ = .E7 ∨ τ = .E8 ∨ τ = .F4 ∨ (τ = .E6 ∧ p ≠ 3)) :
    ∀ f : MulAut (LargeEvenCenterQuot (LargeEvenChevH τ.cartan K false)),
      GGTableBFieldSylowMark p
          (LargeEvenChevFieldImage τ.cartan K (LargeEvenChevH τ.cartan K false)) f →
        GGTableBFieldRepresentativeAt p
          (LargeEvenChevIDImage τ.cartan K (LargeEvenChevH τ.cartan K false)) f := by
  have : CharP K 2 := CFSG.StandardType.charP_two_of_card hK
  have hp2 : p ≠ 2 := dvd_two_pow_sub_one_ne_two hn hpq
  have hpq' : p ∣ Nat.card K - 1 := by rw [hK]; exact hpq
  have hroot := modelRepresentativeAt_isRoot (τ := τ) (K := K) hp hp2 hpq' hcase
  have h : modelRepresentativeAt τ K (LargeEvenIsRoot τ.cartan) p :=
    (largeEvenIsRoot_eq_isRoot τ).symm ▸ hroot
  suffices key : ∀ H : Subgroup (LargeEvenChevGL τ.cartan K),
      H = MarkChev.chevH τ.cartan (LargeEvenIsRoot τ.cartan) K false →
      ∀ f : MulAut (LargeEvenCenterQuot H),
        GGTableBFieldSylowMark p (LargeEvenChevFieldImage τ.cartan K H) f →
        GGTableBFieldRepresentativeAt p (LargeEvenChevIDImage τ.cartan K H) f from
    key _ (largeEvenChevH_eq τ.cartan K false)
  intro H hH
  subst hH
  rw [largeEvenChevIDImage_eq]
  exact h

private theorem fieldRepresentative_card_two {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ}
    {K : Type} [Field K] {p : ℕ} (hK : Nat.card K = 2) :
    ∀ f : MulAut (LargeEvenCenterQuot (LargeEvenChevH A K false)),
      GGTableBFieldSylowMark p
          (LargeEvenChevFieldImage A K (LargeEvenChevH A K false)) f →
        GGTableBFieldRepresentativeAt p
          (LargeEvenChevIDImage A K (LargeEvenChevH A K false)) f := by
  intro f hf
  have hf1 : f = 1 := by
    have hle : Subgroup.closure (LargeEvenChevFieldImage A K (LargeEvenChevH A K false)) ≤ ⊥ := by
      rw [Subgroup.closure_le]
      intro x hx
      rw [chevFieldImage_eq_one_of_card_two hK _ hx]
      exact Subgroup.mem_bot.mpr rfl
    exact Subgroup.mem_bot.mp (hle hf.1)
  subst hf1
  intro M _ _ L' E θ hE hP
  refine ⟨1, ?_, ?_⟩
  · have hmem : MulAut.conj (1 : LargeEvenCenterQuot (LargeEvenChevH A K false)) ∈
        LargeEvenChevIDImage A K (LargeEvenChevH A K false) :=
      Subgroup.subset_closure (Or.inl ⟨1, rfl⟩)
    simpa using hmem
  · intro e
    simp

theorem fieldRepresentative_exc
    {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hrow : GGL48TBExcInnRow p lab ∨ GGL48TBExcTwoRow p lab ∨ (GGL48TBE6Row p lab ∧ 5 ≤ p)) :
    LargeEvenLabelAll lab fun R _ I F =>
      ∀ f : MulAut R, GGTableBFieldSylowMark p F f → GGTableBFieldRepresentativeAt p I f := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, -⟩ := hlab
  intro Q hQ
  rcases hrow with ⟨ht, hpq⟩ | ⟨ht, hn1, -⟩ | ⟨⟨ht, hpq⟩, hp5⟩
  · rcases ht with ht | ht | ht <;> dsimp only at ht <;> subst ht
    · exact recipeChevalley_and (P := fun R _ I F =>
          ∀ f : MulAut R, GGTableBFieldSylowMark p F f → GGTableBFieldRepresentativeAt p I f)
        (fun K _ _ hK => fieldRepresentative_chev (τ := .E7) hp hn hK hpq (Or.inl rfl)) hQ
    · exact recipeChevalley_and (P := fun R _ I F =>
          ∀ f : MulAut R, GGTableBFieldSylowMark p F f → GGTableBFieldRepresentativeAt p I f)
        (fun K _ _ hK =>
          fieldRepresentative_chev (τ := .E8) hp hn hK hpq (Or.inr (Or.inl rfl))) hQ
    · exact recipeChevalley_and (P := fun R _ I F =>
          ∀ f : MulAut R, GGTableBFieldSylowMark p F f → GGTableBFieldRepresentativeAt p I f)
        (fun K _ _ hK =>
          fieldRepresentative_chev (τ := .F4) hp hn hK hpq (Or.inr (Or.inr (Or.inl rfl)))) hQ
  · rcases ht with ht | ht | ht | ht <;> subst ht <;> subst hn1
    · exact recipeChevalley_and (P := fun R _ I F =>
          ∀ f : MulAut R, GGTableBFieldSylowMark p F f → GGTableBFieldRepresentativeAt p I f)
        (fun K _ _ hK => fieldRepresentative_card_two (by simpa using hK)) hQ
    · exact recipeChevalley_and (P := fun R _ I F =>
          ∀ f : MulAut R, GGTableBFieldSylowMark p F f → GGTableBFieldRepresentativeAt p I f)
        (fun K _ _ hK => fieldRepresentative_card_two (by simpa using hK)) hQ
    · exact recipeChevalley_and (P := fun R _ I F =>
          ∀ f : MulAut R, GGTableBFieldSylowMark p F f → GGTableBFieldRepresentativeAt p I f)
        (fun K _ _ hK => fieldRepresentative_card_two (by simpa using hK)) hQ
    · exact recipeChevalley_and (P := fun R _ I F =>
          ∀ f : MulAut R, GGTableBFieldSylowMark p F f → GGTableBFieldRepresentativeAt p I f)
        (fun K _ _ hK => fieldRepresentative_card_two (by simpa using hK)) hQ
  · subst ht
    exact recipeChevalley_and (P := fun R _ I F =>
        ∀ f : MulAut R, GGTableBFieldSylowMark p F f → GGTableBFieldRepresentativeAt p I f)
      (fun K _ _ hK => fieldRepresentative_chev (τ := .E6) hp hn hK hpq
        (Or.inr (Or.inr (Or.inr ⟨rfl, by omega⟩)))) hQ

end CFSG.StandardType
