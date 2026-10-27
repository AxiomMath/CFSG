module

public import CFSG.Timmesfeld.RankTwo.Presentation
public import CFSG.LieType.Steinberg.PartBHalfSpace
public import CFSG.LieType.TitsSimplicity

public section

namespace CFSG.Timmesfeld

open CFSG.LieType CFSG.LieType.Steinberg

universe u v

section HalfSpace

variable {ι : Type u} [Fintype ι] [DecidableEq ι] (Φ : Steinberg.RootSystem ι)

theorem addHom_apply_eq_sum (f : (ι → ℤ) →+ ℤ) (v : ι → ℤ) :
    f v = ∑ j, v j * f (Pi.single j 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : (Pi.single j (v j) : ι → ℤ) = v j • Pi.single j 1 := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [this, map_zsmul, smul_eq_mul]

theorem mem_pos_of_nonneg {γ : ι → ℤ} (hγ : γ ∈ Φ.roots) (h0 : ∀ j, 0 ≤ γ j) : γ ∈ Φ.pos := by
  obtain ⟨j, hj⟩ := exists_apply_ne_zero (Φ.ne_zero_of_mem hγ)
  exact Φ.mem_pos_of_pos hγ (lt_of_le_of_ne (h0 j) hj.symm)

private def negSet (f : (ι → ℤ) →+ ℤ) : Set (ι → ℤ) :=
  {δ | δ ∈ Φ.roots ∧ (∀ j, 0 ≤ δ j) ∧ f δ < 0}

private theorem ncard_negSet_comp_lt (f : (ι → ℤ) →+ ℤ) {i : ι} (hi : f (Pi.single i 1) < 0) :
    (negSet Φ (f.comp (Φ.refl i))).ncard < (negSet Φ f).ncard := by
  have hinj : Function.Injective (Φ.refl i) := fun a b h => by
    rw [← Φ.refl_refl i a, h, Φ.refl_refl]
  rw [← Set.ncard_image_of_injective _ hinj]
  have hsub : Φ.refl i '' negSet Φ (f.comp (Φ.refl i)) ⊆ negSet Φ f := by
    rintro _ ⟨δ, ⟨hδ, hδ0, hfδ⟩, rfl⟩
    refine ⟨Φ.refl_mem i δ hδ, ?_, hfδ⟩
    by_cases hsupp : ∃ j, j ≠ i ∧ δ j ≠ 0
    · obtain ⟨j, hji, hj⟩ := hsupp
      have hpos : 0 < Φ.refl i δ j := by
        rw [Φ.refl_apply_of_ne i δ j hji]
        exact lt_of_le_of_ne (hδ0 j) hj.symm
      rcases Φ.sign _ (Φ.refl_mem i δ hδ) with h | h
      · exact h
      · exact absurd (h j) (not_le.mpr hpos)
    · push Not at hsupp
      have hδi : δ = δ i • Pi.single i 1 := by
        funext j
        by_cases hji : j = i
        · subst hji
          simp
        · simp [hji, hsupp j hji]
      exfalso
      have : f (Φ.refl i δ) = -(δ i * f (Pi.single i 1)) := by
        conv_lhs => rw [hδi]
        rw [map_zsmul, Φ.refl_single, map_zsmul, map_neg, smul_eq_mul, mul_neg]
      simp only [AddMonoidHom.coe_comp, Function.comp_apply] at hfδ
      rw [this] at hfδ
      nlinarith [hδ0 i]
  refine Set.ncard_lt_ncard ((Set.ssubset_iff_of_subset hsub).mpr ⟨Pi.single i 1,
    ⟨Φ.single_mem i, fun j => ?_, hi⟩, ?_⟩) (Φ.finite_roots.subset fun δ hδ => hδ.1)
  · by_cases hji : j = i
    · subst hji
      simp
    · simp [hji]
  · rintro ⟨δ, ⟨-, hδ0, -⟩, hδ⟩
    have : δ = -Pi.single i 1 := by
      rw [← Φ.refl_refl i δ, hδ, Φ.refl_single]
    have := hδ0 i
    simp_all

private theorem exists_word_nonneg_comp (f : (ι → ℤ) →+ ℤ) :
    ∃ u : List ι, ∀ δ ∈ Φ.roots, (∀ j, 0 ≤ δ j) → 0 ≤ f (wordAct Φ.refl u δ) := by
  suffices h : ∀ N (f : (ι → ℤ) →+ ℤ), (negSet Φ f).ncard = N →
      ∃ u : List ι, ∀ δ ∈ Φ.roots, (∀ j, 0 ≤ δ j) → 0 ≤ f (wordAct Φ.refl u δ) from
    h _ f rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro f hN
    by_cases hneg : ∃ i, f (Pi.single i 1) < 0
    · obtain ⟨i, hi⟩ := hneg
      obtain ⟨u, hu⟩ := ih _ (hN ▸ ncard_negSet_comp_lt Φ f hi) (f.comp (Φ.refl i)) rfl
      exact ⟨i :: u, fun δ hδ hδ0 => hu δ hδ hδ0⟩
    · push Not at hneg
      refine ⟨[], fun δ _ hδ0 => ?_⟩
      change 0 ≤ f δ
      rw [addHom_apply_eq_sum f δ]
      exact Finset.sum_nonneg fun j _ => mul_nonneg (hδ0 j) (hneg j)

theorem exists_word_nonneg_of_pos (f : (ι → ℤ) →+ ℤ) :
    ∃ w : List ι, ∀ γ ∈ Φ.roots, 0 < f γ → ∀ j, 0 ≤ wordAct Φ.refl w γ j := by
  obtain ⟨u, hu⟩ := exists_word_nonneg_comp Φ f
  refine ⟨u.reverse, fun γ hγ hfγ => ?_⟩
  have hδ : wordAct Φ.refl u.reverse γ ∈ Φ.roots := Φ.wordAct_mem _ hγ
  rcases Φ.sign _ hδ with h | h
  · exact h
  · exfalso
    have h1 := hu _ (Φ.neg_mem _ hδ) fun j => by simpa using h j
    have hinv := Φ.wordAct_reverse u.reverse γ
    rw [List.reverse_reverse] at hinv
    rw [Steinberg.wordAct_neg, hinv, map_neg] at h1
    linarith

theorem exists_addHom_pos_on_cone {α β : ι → ℤ} (hα : α ∈ Φ.roots) (hβ : β ∈ Φ.roots)
    (h : ¬ Steinberg.IsNegMultiple α β) :
    ∃ f : (ι → ℤ) →+ ℤ, ∀ γ ∈ Steinberg.cone Φ.roots α β, 0 < f γ := by
  obtain ⟨f, hfα, hfβ⟩ : ∃ f : (ι → ℤ) →+ ℤ, 0 < f α ∧ 0 < f β := by
    by_cases hli : LinIndepPair α β
    · exact exists_addHom_pos_pos hli
    rcases Φ.proportional α hα β hβ hli with e | e | e | e | e | e
    · obtain ⟨f, hf⟩ := Φ.exists_addHom_pos hα
      exact ⟨f, hf, e ▸ hf⟩
    · exact absurd ⟨-1, by norm_num, fun j => by rw [e]; simp⟩ h
    · obtain ⟨f, hf⟩ := Φ.exists_addHom_pos hβ
      refine ⟨f, ?_, hf⟩
      rw [e, map_nsmul]
      positivity
    · exact absurd ⟨-1 / 2, by norm_num, fun j => by rw [e]; simp; ring⟩ h
    · obtain ⟨f, hf⟩ := Φ.exists_addHom_pos hα
      refine ⟨f, hf, ?_⟩
      rw [e, map_nsmul]
      positivity
    · exact absurd ⟨-2, by norm_num, fun j => by rw [e]; simp⟩ h
  refine ⟨f, fun γ ⟨hγ, a, b, hab⟩ => ?_⟩
  rw [hab]
  refine pos_apply_nsmul_add_nsmul hfα hfβ (Nat.pos_of_ne_zero fun h0 => ?_)
  obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := by omega
  exact Φ.zero_notMem (by simpa [hab] using hγ)

end HalfSpace

section Weyl

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {Φ : Steinberg.RootSystem ι} {K : Type v}
  [Group K] {X : (ι → ℤ) → Subgroup K} {G : Type*} [Group G]

theorem conj_mem_wordAct (n : ι → K)
    (hn : ∀ i, ∀ γ ∈ Φ.roots, ∀ x ∈ X γ, n i * x * (n i)⁻¹ ∈ X (Φ.refl i γ)) (w : List ι)
    {γ : ι → ℤ} (hγ : γ ∈ Φ.roots) {x : K} (hx : x ∈ X γ) :
    (w.map n).prod * x * ((w.map n).prod)⁻¹ ∈ X (wordAct Φ.refl w γ) := by
  induction w with
  | nil => simpa using hx
  | cons i w ih =>
    have h := hn i _ (Φ.wordAct_mem w hγ) _ ih
    have e : (List.map n (i :: w)).prod * x * ((List.map n (i :: w)).prod)⁻¹ =
        n i * ((w.map n).prod * x * ((w.map n).prod)⁻¹) * (n i)⁻¹ := by
      simp only [List.map_cons, List.prod_cons]
      group
    rw [e]
    exact h

theorem conj_map_wordAct (n : ι → K)
    (hn : ∀ i, ∀ γ ∈ Φ.roots, ∀ x ∈ X γ, n i * x * (n i)⁻¹ ∈ X (Φ.refl i γ)) (ñ : ι → G)
    {φ : ∀ γ, X γ → G}
    (hñ : ∀ i, ∀ γ ∈ Φ.roots, ∀ (x : X γ) (y : X (Φ.refl i γ)), (y : K) = n i * x * (n i)⁻¹ →
      ñ i * φ γ x * (ñ i)⁻¹ = φ (Φ.refl i γ) y)
    (w : List ι) {γ : ι → ℤ} (hγ : γ ∈ Φ.roots) (x : X γ) (y : X (wordAct Φ.refl w γ))
    (hy : (y : K) = (w.map n).prod * x * ((w.map n).prod)⁻¹) :
    (w.map ñ).prod * φ γ x * ((w.map ñ).prod)⁻¹ = φ (wordAct Φ.refl w γ) y := by
  induction w with
  | nil =>
    have hyx : y = x := Subtype.ext (by simpa using hy)
    simp only [List.map_nil, List.prod_nil, one_mul, inv_one, mul_one]
    exact congrArg (φ γ) hyx.symm
  | cons i w ih =>
    let z : X (wordAct Φ.refl w γ) := ⟨_, conj_mem_wordAct n hn w hγ x.2⟩
    have h1 := ih z rfl
    have h2 := hñ i _ (Φ.wordAct_mem w hγ) z y (by
      rw [hy]
      simp only [List.map_cons, List.prod_cons, z]
      group)
    calc (List.map ñ (i :: w)).prod * φ γ x * ((List.map ñ (i :: w)).prod)⁻¹ =
        ñ i * ((w.map ñ).prod * φ γ x * ((w.map ñ).prod)⁻¹) * (ñ i)⁻¹ := by
          simp only [List.map_cons, List.prod_cons]
          group
      _ = φ (wordAct Φ.refl (i :: w) γ) y := by rw [h1, h2]; rfl

theorem coneCompatible_of_pos (n : ι → K)
    (hn : ∀ i, ∀ γ ∈ Φ.roots, ∀ x ∈ X γ, n i * x * (n i)⁻¹ ∈ X (Φ.refl i γ)) (ñ : ι → G)
    {φ : ∀ γ, X γ → G}
    (hñ : ∀ i, ∀ γ ∈ Φ.roots, ∀ (x : X γ) (y : X (Φ.refl i γ)), (y : K) = n i * x * (n i)⁻¹ →
      ñ i * φ γ x * (ñ i)⁻¹ = φ (Φ.refl i γ) y)
    (hpos : ExtendsToHom X Φ.pos φ)
    (hrank : ∀ i, ExtendsToHom X {Pi.single i 1, -Pi.single i 1} φ) :
    ConeCompatible Φ X φ := by
  refine ⟨fun α hα β hβ hneg => ?_, hrank⟩
  obtain ⟨f, hf⟩ := exists_addHom_pos_on_cone Φ hα hβ hneg
  obtain ⟨w, hw⟩ := exists_word_nonneg_of_pos Φ f
  obtain ⟨S, θ, hθ⟩ := hpos
  let c : K →* K := (MulAut.conj (w.map n).prod).toMonoidHom
  refine ⟨S.comap c, (MulAut.conj ((w.map ñ).prod)⁻¹).toMonoidHom.comp
    (θ.comp (c.subgroupComap S)), fun γ hγ x => ?_⟩
  have hγr : γ ∈ Φ.roots := hγ.1
  have hwγ : wordAct Φ.refl w γ ∈ Φ.pos :=
    mem_pos_of_nonneg Φ (Φ.wordAct_mem w hγr) (hw γ hγr (hf γ hγ))
  have hmem := conj_mem_wordAct n hn w hγr x.2
  obtain ⟨hS, hθx⟩ := hθ _ hwγ ⟨_, hmem⟩
  have heq := conj_map_wordAct n hn ñ hñ w hγr x ⟨_, hmem⟩ rfl
  refine ⟨hS, ?_⟩
  change ((w.map ñ).prod)⁻¹ * θ ⟨_, hS⟩ * ((w.map ñ).prod)⁻¹⁻¹ = φ γ x
  rw [hθx, ← heq]
  group

end Weyl

section Datum

variable {K : Type v} [Group K] {D : Universal.UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem conj_mem_refl_of_isCTGroupDatum
    (hct : CurtisTits.IsCTGroupDatum (RootSystem.coxeterMatrix D.isFiniteType).toCoxeterSystem
      (RootSystem.weylAction D.isFiniteType) D.roots D.rootGroup n H) (i : Fin D.rank)
    {γ : Fin D.rank → ℤ} (hγ : γ ∈ (Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible).roots)
    {x : K} (hx : x ∈ D.rootGroup γ) :
    n i * x * (n i)⁻¹ ∈
      D.rootGroup ((Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible).refl i γ) := by
  have h := hct.conj_mem i γ hγ x hx
  rwa [RootSystem.weylAction_simple] at h

end Datum

end CFSG.Timmesfeld
