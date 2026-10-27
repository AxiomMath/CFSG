module

public import CFSG.LocalAnalysis.StandardType.GGSixFieldFiveProof
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGSLTag

public section

namespace CFSG.StandardType

namespace FieldFiveSL

open CFSG.Assembly CFSG.RankThree.PartOne.KCLinComm Matrix LayerFacts LinNonsplit

section Two

theorem eq_one_of_ne_zero_of_card_two {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 2)
    {c : K} (hc : c ≠ 0) : c = 1 := by
  have h1 : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK]
  have : Subsingleton Kˣ := (Nat.card_eq_one_iff_unique.mp h1).1
  exact congrArg Units.val (Subsingleton.elim (Units.mk0 c hc) 1)

theorem scalar_eq_one_of_card_two {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 2)
    {n : Type*} [Fintype n] [DecidableEq n] (u : Kˣ) : GeneralLinearGroup.scalar n u = 1 := by
  have h1 : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK]
  have : Subsingleton Kˣ := (Nat.card_eq_one_iff_unique.mp h1).1
  rw [Subsingleton.elim u 1, map_one]

theorem center_SL_eq_bot_of_card_two {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 2)
    {m : ℕ} : Subgroup.center (SpecialLinearGroup (Fin (m + 1)) K) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hr
  have hr1 : r = 1 := eq_one_of_ne_zero_of_card_two hK hr0
  rw [Subgroup.mem_bot]
  ext i j
  rw [← hrA, hr1]
  simp

end Two

section Single

variable {r₀ : ℕ} {E : Fin r₀ → Type} {e : Fin r₀ → ℕ} [∀ i, Field (E i)]

theorem piSingle_mul_eq (w : PiGL E e) (i₀ : Fin r₀) (hw : w i₀ = 1) :
    (Pi.single i₀ 1 : Π i, Matrix (Fin (e i)) (Fin (e i)) (E i)) *
        (fun i => ((w i : GL (Fin (e i)) (E i)) : Matrix (Fin (e i)) (Fin (e i)) (E i))) =
      Pi.single i₀ 1 ∧
    (fun i => ((w i : GL (Fin (e i)) (E i)) : Matrix (Fin (e i)) (Fin (e i)) (E i))) *
        (Pi.single i₀ 1 : Π i, Matrix (Fin (e i)) (Fin (e i)) (E i)) = Pi.single i₀ 1 := by
  classical
  constructor
  · funext i
    by_cases hi : i = i₀
    · subst hi
      simp [hw]
    · simp [hi]
  · funext i
    by_cases hi : i = i₀
    · subst hi
      simp [hw]
    · simp [hi]

end Single

section Block

variable {m : ℕ} {F : Type} [Field F]
  {r' : ℕ} {D' : Fin r' → Type} {d' : Fin r' → ℕ} [∀ i, Field (D' i)] [∀ i, Algebra F (D' i)]

theorem exists_goodBlock_ge_of_fix [∀ i, Finite (D' i)] [∀ i, CharP (D' i) 2]
    (hd' : ∀ i, NeZero (d' i))
    {Φ' : (Π i, Matrix (Fin (d' i)) (Fin (d' i)) (D' i)) →ₐ[F]
      Matrix (Fin (m + 1)) (Fin (m + 1)) F} (hΦ'inj : Function.Injective Φ')
    {θ' : PiGL D' d' →* GL (Fin (m + 1)) F} (hθ'inj : Function.Injective θ')
    (hθ'Φ' : ∀ w, ((θ' w : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      Φ' (fun i => ((w i : GL (Fin (d' i)) (D' i)) : Matrix (Fin (d' i)) (Fin (d' i)) (D' i))))
    {Bh : Subgroup (GL (Fin (m + 1)) F)}
    (hΦ'range : ∀ X : Matrix (Fin (m + 1)) (Fin (m + 1)) F, X ∈ Set.range Φ' ↔
      ∀ g ∈ Bh, X * (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
        (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * X)
    (hθ'range : θ'.range = Subgroup.centralizer (Bh : Set (GL (Fin (m + 1)) F)))
    {B : GL (Fin (m + 1)) F} (hBmem : B ∈ Bh)
    (hBgen : ∀ M : Matrix (Fin (m + 1)) (Fin (m + 1)) F,
      Commute M (B : Matrix (Fin (m + 1)) (Fin (m + 1)) F) →
        ∀ g ∈ Bh, Commute M (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F))
    {T : Subgroup (SpecialLinearGroup (Fin (m + 1)) F)} (hTq : CFSG.IsQuasisimple T)
    (hTB : ∀ s ∈ T, Commute ((SpecialLinearGroup.toGL s : GL (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F) (B : Matrix (Fin (m + 1)) (Fin (m + 1)) F))
    (hTfix : ∀ s ∈ T, ((SpecialLinearGroup.toGL s : GL (Fin (m + 1)) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
        ((B : Matrix (Fin (m + 1)) (Fin (m + 1)) F) - 1) =
      (B : Matrix (Fin (m + 1)) (Fin (m + 1)) F) - 1) :
    ∃ j, GoodBlock D' d' j ∧ (∀ v, θ' v = B → v j = 1) ∧
      T ≤ ((blockSL D' d' j).map θ').comap SpecialLinearGroup.toGL := by
  classical
  set ι : SpecialLinearGroup (Fin (m + 1)) F →* GL (Fin (m + 1)) F :=
    SpecialLinearGroup.toGL with hιdef
  have hBc : B ∈ Subgroup.centralizer (Bh : Set (GL (Fin (m + 1)) F)) :=
    Subgroup.mem_centralizer_iff.mpr fun g hg => Units.ext (by
      rw [Units.val_mul, Units.val_mul]
      exact (hBgen _ (Commute.refl _) g hg).eq.symm)
  obtain ⟨v, hv⟩ : B ∈ θ'.range := hθ'range ▸ hBc
  have hvc : ∀ u, v * u = u * v := by
    intro u
    apply hθ'inj
    have hu : θ' u ∈ Subgroup.centralizer (Bh : Set (GL (Fin (m + 1)) F)) :=
      hθ'range ▸ ⟨u, rfl⟩
    rw [map_mul, map_mul, hv]
    exact Subgroup.mem_centralizer_iff.mp hu B hBmem
  choose c hc using exists_scalar_of_forall_commute hvc
  have key : ∀ s ∈ T, ∃ γ : PiGL D' d', θ' γ = ι s ∧ ∀ j, v j ≠ 1 → γ j = 1 := by
    intro s hs
    have hcomm := hTB s hs
    have hfix := hTfix s hs
    have hsθ' : ι s ∈ θ'.range := by
      rw [hθ'range]
      exact Subgroup.mem_centralizer_iff.mpr fun g hg => Units.ext (by
        rw [Units.val_mul, Units.val_mul]
        exact (hBgen _ hcomm g hg).eq.symm)
    obtain ⟨γ, hγ⟩ := hsθ'
    refine ⟨γ, hγ, fun j hj => ?_⟩
    have h1 : Φ' ((fun i => ((γ i : GL (Fin (d' i)) (D' i)) :
          Matrix (Fin (d' i)) (Fin (d' i)) (D' i))) *
        ((fun i => ((v i : GL (Fin (d' i)) (D' i)) : Matrix (Fin (d' i)) (Fin (d' i)) (D' i))) -
          1)) =
        Φ' ((fun i => ((v i : GL (Fin (d' i)) (D' i)) :
          Matrix (Fin (d' i)) (Fin (d' i)) (D' i))) - 1) := by
      simp only [map_mul, map_sub, map_one]
      rw [← hθ'Φ', ← hθ'Φ', hγ, hv]
      exact hfix
    have h2 := congrFun (hΦ'inj h1) j
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.one_apply] at h2
    rw [hc j] at h2
    have hcj : c j ≠ 1 := by
      intro h
      apply hj
      apply Units.ext
      rw [hc j, h, map_one, Units.val_one]
    exact eq_one_of_mul_scalar_sub_one hcj h2
  have huniq : ∀ j₁ j₂, v j₁ = 1 → v j₂ = 1 → j₁ = j₂ := by
    intro j₁ j₂ h₁ h₂
    refine eq_of_coord_eq_one hd' Φ' hΦ'inj (B := (B : Matrix (Fin (m + 1)) (Fin (m + 1)) F))
      (fun X hX => (hΦ'range X).mpr fun g hg => (hBgen X hX g hg).eq)
      (w := fun i => ((v i : GL (Fin (d' i)) (D' i)) : Matrix (Fin (d' i)) (Fin (d' i)) (D' i)))
      (by rw [← hθ'Φ', hv]) ?_ ?_
    · show ((v j₁ : GL (Fin (d' j₁)) (D' j₁)) : Matrix (Fin (d' j₁)) (Fin (d' j₁)) (D' j₁)) = 1
      rw [h₁, Units.val_one]
    · show ((v j₂ : GL (Fin (d' j₂)) (D' j₂)) : Matrix (Fin (d' j₂)) (Fin (d' j₂)) (D' j₂)) = 1
      rw [h₂, Units.val_one]
  obtain ⟨s₀, hs₀⟩ : ∃ s : T, s ≠ 1 := by
    obtain ⟨a, a', haa⟩ := LayerFacts.exists_mul_ne_of_isQuasisimple hTq
    refine ⟨a, fun h => haa ?_⟩
    rw [h, one_mul, mul_one]
  obtain ⟨γ₀, hγ₀, hγ₀1⟩ := key s₀ s₀.2
  obtain ⟨j₀, hj₀⟩ : ∃ j, γ₀ j ≠ 1 := by
    by_contra hall
    push Not at hall
    apply hs₀
    have h1 : γ₀ = 1 := funext hall
    rw [h1, map_one] at hγ₀
    exact Subtype.ext (SpecialLinearGroup.toGL_injective (by
      rw [← hιdef, ← hγ₀, Subgroup.coe_one, map_one]))
  have hvj₀ : v j₀ = 1 := by
    by_contra h
    exact hj₀ (hγ₀1 j₀ h)
  set R := (MonoidHom.mulSingle (fun c => GL (Fin (d' c)) (D' c)) j₀).range with hR
  have hsupp : ∀ s ∈ T, ι s ∈ R.map θ' := by
    intro s hs
    obtain ⟨γ, hγ, hγ1⟩ := key s hs
    refine ⟨γ, ⟨γ j₀, ?_⟩, hγ⟩
    funext i
    by_cases hi : i = j₀
    · subst hi
      simp
    · rw [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne hi]
      exact (hγ1 i fun h => hi (huniq i j₀ h hvj₀)).symm
  have hperf : ⁅T, T⁆ = T := ggCommutator_eq_of_isQuasisimple hTq
  have hle : T.map ι ≤ R.map θ' := Subgroup.map_le_iff_le_comap.mpr fun s hs => hsupp s hs
  have hder : ∀ k, T.map ι ≤ (ggDer R k).map θ' := by
    intro k
    calc T.map ι = (ggDer T k).map ι := by rw [ggDer_of_perfect hperf]
      _ = ggDer (T.map ι) k := map_ggDer ι T k
      _ ≤ ggDer (R.map θ') k := ggDer_mono hle k
      _ = (ggDer R k).map θ' := (map_ggDer θ' R k).symm
  have hj₀good : GoodBlock D' d' j₀ := by
    by_contra hng
    obtain ⟨k, hk⟩ := (isSolvable_of_not_goodBlock hng).solvable
    have h1 : ggDer R k = ⊥ := by
      rw [hR, MonoidHom.range_eq_map, ← map_ggDer, ggDer_top, hk, Subgroup.map_bot]
    have h2 := hder k
    rw [h1, Subgroup.map_bot, le_bot_iff,
      Subgroup.map_eq_bot_iff_of_injective T (f := ι) SpecialLinearGroup.toGL_injective] at h2
    apply hs₀
    have h3 : (s₀ : SpecialLinearGroup (Fin (m + 1)) F) ∈ (⊥ : Subgroup _) := h2 ▸ s₀.2
    exact Subtype.ext (Subgroup.mem_bot.mp h3)
  refine ⟨j₀, hj₀good, fun v' hv' => ?_, fun s hs => ?_⟩
  · rw [hθ'inj (hv'.trans hv.symm)]
    exact hvj₀
  obtain ⟨t, ht, hts⟩ := hder 1 (Subgroup.mem_map_of_mem ι hs)
  exact ⟨t, commutator_range_mulSingle_le j₀ ht, hts⟩

omit [∀ i, Algebra F (D' i)] in
theorem exists_blockHom [∀ i, Finite (D' i)] [∀ i, CharP (D' i) 2]
    {θ' : PiGL D' d' →* GL (Fin (m + 1)) F} (hθ'inj : Function.Injective θ') {j : Fin r'}
    (hj : GoodBlock D' d' j) :
    ∃ β : SpecialLinearGroup (Fin (d' j)) (D' j) →* SpecialLinearGroup (Fin (m + 1)) F,
      Function.Injective β ∧
      β.range = ((blockSL D' d' j).map θ').comap SpecialLinearGroup.toGL ∧
      ∀ s, SpecialLinearGroup.toGL (β s) = θ' (blockEmbed D' d' j s) := by
  set ι : SpecialLinearGroup (Fin (m + 1)) F →* GL (Fin (m + 1)) F :=
    SpecialLinearGroup.toGL with hιdef
  have hιinj : Function.Injective ι := SpecialLinearGroup.toGL_injective
  have hlift : ∀ s, θ' (blockEmbed D' d' j s) ∈ ι.range := fun s =>
    map_blockSL_le_range θ' hj ⟨blockEmbed D' d' j s, ⟨s, rfl⟩, rfl⟩
  set β : SpecialLinearGroup (Fin (d' j)) (D' j) →* SpecialLinearGroup (Fin (m + 1)) F :=
    (MonoidHom.ofInjective hιinj).symm.toMonoidHom.comp
      ((θ'.comp (blockEmbed D' d' j)).codRestrict ι.range hlift) with hβdef
  have hβ : ∀ s, ι (β s) = θ' (blockEmbed D' d' j s) := fun s =>
    MonoidHom.apply_ofInjective_symm hιinj _
  refine ⟨β, fun s t h => blockEmbed_injective j (hθ'inj (by rw [← hβ, ← hβ, h])), ?_, hβ⟩
  ext s
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨blockEmbed D' d' j t, ⟨t, rfl⟩, (hβ t).symm⟩
  · rintro ⟨w, ⟨t, rfl⟩, hw⟩
    exact ⟨t, hιinj ((hβ t).trans hw)⟩

omit [∀ i, Algebra F (D' i)] in
theorem toGL_blockHom_conj {θ' : PiGL D' d' →* GL (Fin (m + 1)) F} {j : Fin r'}
    {β : SpecialLinearGroup (Fin (d' j)) (D' j) →* SpecialLinearGroup (Fin (m + 1)) F}
    (hβ : ∀ s, SpecialLinearGroup.toGL (β s) = θ' (blockEmbed D' d' j s)) {a' : PiGL D' d'}
    {M : GL (Fin (m + 1)) F} (ha' : θ' a' = M) :
    ∀ s t : SpecialLinearGroup (Fin (d' j)) (D' j),
      (t : Matrix (Fin (d' j)) (Fin (d' j)) (D' j)) =
        (a' j : Matrix (Fin (d' j)) (Fin (d' j)) (D' j)) *
          (s : Matrix (Fin (d' j)) (Fin (d' j)) (D' j)) *
            (((a' j)⁻¹ : GL (Fin (d' j)) (D' j)) : Matrix (Fin (d' j)) (Fin (d' j)) (D' j)) →
      SpecialLinearGroup.toGL (β t) = M * SpecialLinearGroup.toGL (β s) * M⁻¹ := by
  classical
  intro s t hst
  rw [hβ, hβ, ← ha', ← map_inv, ← map_mul, ← map_mul]
  congr 1
  funext i
  by_cases hi : i = j
  · subst hi
    apply Units.ext
    simp only [blockEmbed_apply_self, Pi.mul_apply, Pi.inv_apply, Units.val_mul,
      SpecialLinearGroup.coe_GL_coe_matrix]
    exact hst
  · simp [blockEmbed_apply_of_ne hi]

end Block

section FixedBlock

variable {m : ℕ} {F : Type} [Field F]

theorem exists_fixedBlock_component {G : Type} [Group G] [Finite G] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2) {ψ : SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F))
    {z : G} (hz : z ^ 5 = 1) {C : GL (Fin (m + 1)) F}
    (hC : (z, C) ∈ LinFusion.ggInducedPairs ψ)
    {T : Subgroup (SpecialLinearGroup (Fin (m + 1)) F)} (hTq : CFSG.IsQuasisimple T)
    (hTC : ∀ s ∈ T, Commute ((SpecialLinearGroup.toGL s : GL (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F) (C : Matrix (Fin (m + 1)) (Fin (m + 1)) F))
    (hTfix : ∀ s ∈ T, ((SpecialLinearGroup.toGL s : GL (Fin (m + 1)) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
        ((C : Matrix (Fin (m + 1)) (Fin (m + 1)) F) - 1) =
      (C : Matrix (Fin (m + 1)) (Fin (m + 1)) F) - 1) :
    ∃ K : Subgroup G, IsComponentOf K (ψ.range ⊓ Subgroup.centralizer {z}) ∧ T.map ψ ≤ K ∧
      ∀ (w : G) (M : GL (Fin (m + 1)) F), (w, M) ∈ LinFusion.ggInducedPairs ψ →
        Commute (M : Matrix (Fin (m + 1)) (Fin (m + 1)) F)
          (C : Matrix (Fin (m + 1)) (Fin (m + 1)) F) →
        ¬ GGNbrClauseFiveMarking 5 w K ∧
          (w ∈ Subgroup.centralizer (K : Set G) → ∀ s ∈ T,
            ((SpecialLinearGroup.toGL s : GL (Fin (m + 1)) F) :
              Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
              ((M : Matrix (Fin (m + 1)) (Fin (m + 1)) F) - 1) =
            (M : Matrix (Fin (m + 1)) (Fin (m + 1)) F) - 1) := by
  classical
  have hp : (5 : ℕ).Prime := by norm_num
  obtain ⟨r, D, d, _, _, _, Φ, θ, hd, hΦinj, hΦrange, hθinj, hθrange, hθΦ⟩ :=
    exists_piMat_commutant (LinTorus.inducedMatrices ψ (Subgroup.zpowers z))
      (natCast_card_inducedMatrices_ne_zero hker hp (by norm_num)
        (ggIsPGroup_zpowers_of_pow_eq_one hz))
  have : ∀ i, CharP (D i) 2 := fun i =>
    charP_of_injective_algebraMap (algebraMap F (D i)).injective 2
  have hCmem : C ∈ LinTorus.inducedMatrices ψ (Subgroup.zpowers z) :=
    LinTorus.mem_inducedMatrices.mpr ⟨z, Subgroup.mem_zpowers z, hC⟩
  have hgen : ∀ M : Matrix (Fin (m + 1)) (Fin (m + 1)) F,
      Commute M (C : Matrix (Fin (m + 1)) (Fin (m + 1)) F) →
        ∀ g ∈ LinTorus.inducedMatrices ψ (Subgroup.zpowers z),
          Commute M (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) :=
    fun M hM g hg => commute_of_mem_inducedMatrices hker hC hM hg
  obtain ⟨j, hj, hvj, hTle⟩ := exists_goodBlock_ge_of_fix hd hΦinj hθinj hθΦ hΦrange hθrange
    hCmem hgen hTq hTC hTfix
  obtain ⟨β, hβinj, hβrange, hβ⟩ := exists_blockHom hθinj hj
  have hC₀θ : ggCentSL ψ (Subgroup.zpowers z) =
      θ.range.comap (SpecialLinearGroup.toGL :
        SpecialLinearGroup (Fin (m + 1)) F →* GL (Fin (m + 1)) F) := by
    rw [hθrange]
    rfl
  have hcz : Subgroup.centralizer (Subgroup.zpowers z : Set G) = Subgroup.centralizer {z} := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hKcomp : IsComponentOf (β.range.map ψ) (ψ.range ⊓ Subgroup.centralizer {z}) := by
    rw [← hcz, hβrange]
    refine isComponentOf_map_of_le ψ hker (map_ggCentSL_le (forall_mem_zpowers_exists hC))
      (normal_map_ggCentSL hker) ?_ ?_ (isQuasisimple_comap_blockSL hθinj hj)
    · rw [hC₀θ]
      exact Subgroup.comap_mono (Subgroup.map_le_range θ _)
    · intro c hc s hs
      rw [hC₀θ] at hc
      exact conj_mem_comap_blockSL hc hs
  have hθM : ∀ M : GL (Fin (m + 1)) F, Commute (M : Matrix (Fin (m + 1)) (Fin (m + 1)) F)
      (C : Matrix (Fin (m + 1)) (Fin (m + 1)) F) → M ∈ θ.range := by
    intro M hM
    rw [hθrange]
    exact Subgroup.mem_centralizer_iff.mpr fun g hg => Units.ext (by
      rw [Units.val_mul, Units.val_mul]
      exact (hgen _ hM g hg).eq.symm)
  obtain ⟨v, hv⟩ := hθM C (Commute.refl _)
  have hDj : Nat.card (D j) = Nat.card F := by
    have hs := piSingle_mul_eq v j (hvj v hv)
    refine card_eq_of_corner Φ hΦinj (A := (C : Matrix (Fin (m + 1)) (Fin (m + 1)) F))
      (fun X hX => (hΦrange X).mpr fun g hg => (hgen X hX g hg).eq) (hd j) ?_ ?_
    · rw [← hv, hθΦ, ← map_mul, hs.1]
    · rw [← hv, hθΦ, ← map_mul, hs.2]
  have hDj2 : Nat.card (D j) = 2 := hDj.trans hF
  have hdj3 : 3 ≤ d j := by
    rcases hj.2 with h | ⟨s, hs⟩
    · exact h
    · exfalso
      have := Fintype.ofFinite (D j)
      have h4 := Finset.card_le_univ s
      rw [hs, ← Nat.card_eq_fintype_card, hDj2] at h4
      omega
  refine ⟨β.range.map ψ, hKcomp, ?_, fun w M hM hMC => ⟨?_, ?_⟩⟩
  · rw [hβrange]
    exact Subgroup.map_mono hTle
  · obtain ⟨a', ha'⟩ := hθM M hMC
    exact not_ggNbrClauseFiveMarking_block (f := 1) le_rfl (by rw [hF, pow_one]) hker
      (by omega) hDj (Or.inl hdj3) hβinj hM (toGL_blockHom_conj hβ ha') hp (by norm_num)
      (by norm_num) (by norm_num) (fun _ => by norm_num) (fun h => absurd h (by omega))
  · intro hwK s hs
    obtain ⟨a', ha'⟩ := hθM M hMC
    have hcenter := center_SL_eq_bot_of_card_two hF (m := m)
    have hcomm : ∀ g : SpecialLinearGroup (Fin (d j)) (D j),
        Commute (g : Matrix (Fin (d j)) (Fin (d j)) (D j))
          ((a' j : GL (Fin (d j)) (D j)) : Matrix (Fin (d j)) (Fin (d j)) (D j)) := by
      intro g
      have hmem : ψ (β g) ∈ β.range.map ψ := ⟨β g, ⟨g, rfl⟩, rfl⟩
      have h1 : w * ψ (β g) * w⁻¹ = ψ (β g) := by
        rw [(Subgroup.mem_centralizer_iff.mp hwK _ hmem).symm, mul_inv_cancel_right]
      rw [LinFusion.mem_ggInducedPairs.mp hM (β g)] at h1
      have h2 : InnerDiagA.conjSL M (β g) = β g := by
        have hk : InnerDiagA.conjSL M (β g) * (β g)⁻¹ ∈ ψ.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, h1, mul_inv_cancel]
        have hk1 := hker hk
        rw [hcenter, Subgroup.mem_bot] at hk1
        exact mul_inv_eq_one.mp hk1
      have h3 := (LayerFacts.conjSL_eq_iff_commute M (β g)).mp h2
      rw [hβ g, ← ha', ← map_mul, ← map_mul] at h3
      have h4 := congrFun (hθinj h3) j
      simp only [Pi.mul_apply, blockEmbed_apply_self] at h4
      have h5 := congrArg (fun u : GL (Fin (d j)) (D j) =>
        (u : Matrix (Fin (d j)) (Fin (d j)) (D j))) h4
      simp only [Units.val_mul, SpecialLinearGroup.coe_GL_coe_matrix] at h5
      exact h5.symm
    obtain ⟨c, hc⟩ : ((a' j : GL (Fin (d j)) (D j)) : Matrix (Fin (d j)) (Fin (d j)) (D j)) ∈
        Set.range (Matrix.scalar (Fin (d j))) :=
      Matrix.mem_range_scalar_of_commute_transvectionStruct fun t => hcomm ⟨t.toMatrix, t.det⟩
    have : Nonempty (Fin (d j)) := ⟨⟨0, by omega⟩⟩
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact (a' j).ne_zero (hc.symm.trans (map_zero _))
    have ha'j : a' j = 1 := Units.ext (by
      rw [← hc, eq_one_of_ne_zero_of_card_two hDj2 hc0, map_one, Units.val_one])
    obtain ⟨_, ⟨g, rfl⟩, hg⟩ := hTle hs
    rw [← hg, ← ha', hθΦ, hθΦ, ← map_one Φ, ← map_sub, ← map_mul,
      blockEmbed_mul_sub_one ha'j g]

end FixedBlock

section Main

variable {m : ℕ} {F : Type} [Field F]

theorem fieldFive_sl {G : Type} [Group G] [Finite G] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2) {ψ : SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F))
    {D : Subgroup G} (hDel : IsElemAbelian 5 D) (hDcard : Nat.card D = 5 ^ 2)
    (hDA : ∀ d ∈ D, ∃ A, (d, A) ∈ LinFusion.ggInducedPairs ψ)
    {x : G} (hxD : x ∈ D) {L : Subgroup G}
    (hL : IsComponentOf L (ψ.range ⊓ Subgroup.centralizer {x}))
    (hLmark : GGNbrClauseFiveMarking 5 x L)
    {J : Subgroup G} (hJ : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G))) :
    ∃ y ∈ D, y ≠ 1 ∧ ∃ K : Subgroup G,
      IsComponentOf K (ψ.range ⊓ Subgroup.centralizer {y}) ∧ J ≤ K ∧ 5 ∣ Nat.card K ∧
      x ∉ Subgroup.centralizer (K : Set G) ∧ ¬ GGNbrClauseFiveMarking 5 x K := by
  classical
  have hp : (5 : ℕ).Prime := by norm_num
  have : Fact (5 : ℕ).Prime := ⟨hp⟩
  have hproj := LinTorus.isProjElem_inducedMatrices hker hDel
  have hDcomm : ∀ g ∈ LinTorus.inducedMatrices ψ D, ∀ h ∈ LinTorus.inducedMatrices ψ D,
      g * h = h * g := fun g hg h hh => by
    obtain ⟨u, hu⟩ := hproj.comm_scalar g hg h hh
    rw [hu, scalar_eq_one_of_card_two hF, one_mul]
  have hDpow : ∀ g ∈ LinTorus.inducedMatrices ψ D, g ^ 5 = 1 := fun g hg => by
    obtain ⟨u, hu⟩ := hproj.pow_scalar g hg
    rw [hu, scalar_eq_one_of_card_two hF]
  have hDp : IsPGroup 5 D := fun g => ⟨1, Subtype.ext (by simpa using hDel.2 g g.2)⟩
  have hJG : IsComponentOf J (ψ.range ⊓ Subgroup.centralizer (D : Set G)) := by
    have h1 := CFSG.LocalAnalysis.ComponentInitial.assembly_isSubnormal_inf hL.2.1
      (Subgroup.centralizer (D : Set G))
    have h2 : ψ.range ⊓ Subgroup.centralizer {x} ⊓ Subgroup.centralizer (D : Set G) =
        ψ.range ⊓ Subgroup.centralizer (D : Set G) := by
      rw [inf_assoc, inf_eq_right.mpr
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hxD))]
    rw [h2] at h1
    exact isComponentOf_of_isSubnormal_of_isComponentOf hJ h1
  obtain ⟨r, E, e, _, _, _, Φ, θ, he, hΦinj, hΦrange, hθinj, hθrange, hθΦ⟩ :=
    exists_piMat_commutant (LinTorus.inducedMatrices ψ D)
      (natCast_card_inducedMatrices_ne_zero hker hp (by norm_num) hDp)
  have : ∀ i, CharP (E i) 2 := fun i =>
    charP_of_injective_algebraMap (algebraMap F (E i)).injective 2
  set ι : SpecialLinearGroup (Fin (m + 1)) F →* GL (Fin (m + 1)) F :=
    SpecialLinearGroup.toGL with hιdef
  have hιinj : Function.Injective ι := SpecialLinearGroup.toGL_injective
  have hC₀θ : ggCentSL ψ D = θ.range.comap ι := by rw [hθrange]; rfl
  set S : {b : Fin r // GoodBlock E e b} → Subgroup (SpecialLinearGroup (Fin (m + 1)) F) :=
    fun b => ((blockSL E e b.1).map θ).comap ι with hSdef
  have hSmap : ∀ b, (S b).map ι = (blockSL E e b.1).map θ := fun b =>
    Subgroup.map_comap_eq_self (map_blockSL_le_range θ b.2)
  have hÑmap : (⨆ b, S b).map ι = (goodSL E e).map θ := by
    rw [Subgroup.map_iSup, goodSL, Subgroup.map_iSup]
    exact iSup_congr hSmap
  have hSC : ∀ b, S b ≤ ggCentSL ψ D := fun b => by
    rw [hC₀θ]
    exact Subgroup.comap_mono (Subgroup.map_le_range θ _)
  have hSn : ∀ b, ∀ c ∈ ggCentSL ψ D, ∀ s ∈ S b, c * s * c⁻¹ ∈ S b := by
    intro b c hc s hs
    rw [hC₀θ] at hc
    exact conj_mem_comap_blockSL hc hs
  have hSq : ∀ b, CFSG.IsQuasisimple (S b) := fun b => isQuasisimple_comap_blockSL hθinj b.2
  have hder : ∃ k, ggDer (ggCentSL ψ D) k ≤ ⨆ b, S b := by
    obtain ⟨k, hk⟩ := exists_derivedSeries_le_goodSL (E := E) (m := e)
    refine ⟨k, ?_⟩
    rw [← Subgroup.map_le_map_iff_of_injective hιinj, map_ggDer, hÑmap]
    calc ggDer ((ggCentSL ψ D).map ι) k ≤ ggDer θ.range k :=
          ggDer_mono (by rw [hC₀θ]; exact Subgroup.map_comap_le _ _) k
      _ = (ggDer ⊤ k).map θ := by rw [map_ggDer, ← MonoidHom.range_eq_map]
      _ = (derivedSeries _ k).map θ := by rw [ggDer_top]
      _ ≤ (goodSL E e).map θ := Subgroup.map_mono hk
  obtain ⟨i, rfl⟩ := LayerPDiv.exists_eq_map_of_isComponentOf ψ hker (map_ggCentSL_le hDA)
    (normal_map_ggCentSL hker) (commutator_le_map_ggCentSL hker) S hSC hSn hSq hder hJG
  have hTq : CFSG.IsQuasisimple (S i) := hSq i
  have hTsupp : ∀ w : PiGL E e, w i.1 = 1 → ∀ s ∈ S i,
      Commute ((ι s : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F)
        ((θ w : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) ∧
      ((ι s : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
          (((θ w : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) - 1) =
        ((θ w : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) - 1 := by
    intro w hw s hs
    obtain ⟨_, ⟨g, rfl⟩, hg⟩ := hs
    refine ⟨?_, ?_⟩
    · rw [← hg]
      exact ((show Commute (blockEmbed E e i.1 g) w from blockEmbed_mul_comm hw g).map θ).units_val
    · rw [← hg, hθΦ, hθΦ, ← map_one Φ, ← map_sub, ← map_mul, blockEmbed_mul_sub_one hw g]
  obtain ⟨A, hA⟩ := hDA x hxD
  have hAmem : A ∈ LinTorus.inducedMatrices ψ D :=
    LinTorus.mem_inducedMatrices.mpr ⟨x, hxD, hA⟩
  obtain ⟨y₀, hy₀D, hy₀x⟩ : ∃ y₀ ∈ D, y₀ ∉ Subgroup.zpowers x := by
    by_contra hall
    push Not at hall
    have h1 := Subgroup.card_le_of_le (show D ≤ Subgroup.zpowers x from fun d hd => hall d hd)
    rw [Nat.card_zpowers, hDcard] at h1
    have h2 : orderOf x ≤ 5 := orderOf_le_of_pow_eq_one (by norm_num) (hDel.2 x hxD)
    omega
  obtain ⟨B₀, hB₀⟩ := hDA y₀ hy₀D
  have hB₀mem : B₀ ∈ LinTorus.inducedMatrices ψ D :=
    LinTorus.mem_inducedMatrices.mpr ⟨y₀, hy₀D, hB₀⟩
  have hcent : ∀ M ∈ LinTorus.inducedMatrices ψ D,
      ∃ a : PiGL E e, θ a = M ∧ ∀ u, a * u = u * a := by
    intro M hM
    obtain ⟨a, ha⟩ : M ∈ θ.range := by
      rw [hθrange]
      exact Subgroup.mem_centralizer_iff.mpr fun g hg => hDcomm g hg M hM
    refine ⟨a, ha, fun u => hθinj ?_⟩
    have hu : θ u ∈ Subgroup.centralizer
        (LinTorus.inducedMatrices ψ D : Set (GL (Fin (m + 1)) F)) := hθrange ▸ ⟨u, rfl⟩
    rw [map_mul, map_mul, ha]
    exact Subgroup.mem_centralizer_iff.mp hu M hM
  obtain ⟨a, ha, hac⟩ := hcent A hAmem
  obtain ⟨w₀, hw₀, hw₀c⟩ := hcent B₀ hB₀mem
  obtain ⟨α, hα⟩ := exists_scalar_of_forall_commute hac i.1
  obtain ⟨β, hβ⟩ := exists_scalar_of_forall_commute hw₀c i.1
  have hscalar_pow : ∀ (w : PiGL E e) (c : E i.1),
      ((w i.1 : GL (Fin (e i.1)) (E i.1)) : Matrix (Fin (e i.1)) (Fin (e i.1)) (E i.1)) =
        Matrix.scalar (Fin (e i.1)) c → θ w ^ 5 = 1 → c ^ 5 = 1 := by
    intro w c hc h5
    have hw5 : w ^ 5 = 1 := hθinj (by rw [map_pow, h5, map_one])
    have h1 := congrArg (fun u : PiGL E e =>
      ((u i.1 : GL (Fin (e i.1)) (E i.1)) : Matrix (Fin (e i.1)) (Fin (e i.1)) (E i.1))) hw5
    simp only [Pi.pow_apply, Units.val_pow_eq_pow_val, Pi.one_apply, Units.val_one] at h1
    rw [hc, ← map_pow] at h1
    have i₀ : Fin (e i.1) := ⟨0, Nat.pos_of_ne_zero (he i.1).ne⟩
    have h2 := congrFun (congrFun h1 i₀) i₀
    simpa using h2
  have hα5 : α ^ 5 = 1 := hscalar_pow a α hα (by rw [ha]; exact hDpow A hAmem)
  have hβ5 : β ^ 5 = 1 := hscalar_pow w₀ β hβ (by rw [hw₀]; exact hDpow B₀ hB₀mem)
  have hα1 : α ≠ 1 := by
    intro hα1
    have hai : a i.1 = 1 := Units.ext (by rw [hα, hα1, map_one, Units.val_one])
    have hsupp := hTsupp a hai
    rw [ha] at hsupp
    obtain ⟨Kx, hKx, hTKx, hKxw⟩ := exists_fixedBlock_component hF hker (hDel.2 x hxD) hA hTq
      (fun s hs => (hsupp s hs).1) (fun s hs => (hsupp s hs).2)
    have hLK : L = Kx := by
      rcases CFSG.LocalAnalysis.ComponentInitial.isComponentOf_eq_or_commute hL hKx with h | h
      · exact h
      · exfalso
        apply CFSG.LocalAnalysis.ComponentInitial.not_le_centralizer_self_of_isQuasisimple hJ.2.2
        have hc : L ≤ Subgroup.centralizer (Kx : Set G) :=
          Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
        exact ((hJ.1.trans inf_le_left).trans hc).trans (Subgroup.centralizer_le hTKx)
    exact (hKxw x A hA (Commute.refl _)).1 (hLK ▸ hLmark)
  have hαo : orderOf α = 5 := orderOf_eq_prime hα5 hα1
  have hprim : IsPrimitiveRoot α 5 := hαo ▸ IsPrimitiveRoot.orderOf α
  obtain ⟨j, -, hj⟩ := hprim.eq_pow_of_pow_eq_one hβ5
  have hyC : (y₀ * (x ^ j)⁻¹, B₀ * (A ^ j)⁻¹) ∈ LinFusion.ggInducedPairs ψ := by
    have h := (LinFusion.ggInducedPairs ψ).mul_mem hB₀
      ((LinFusion.ggInducedPairs ψ).inv_mem ((LinFusion.ggInducedPairs ψ).pow_mem hA j))
    rwa [Prod.pow_mk, Prod.inv_mk, Prod.mk_mul_mk] at h
  have hyD : y₀ * (x ^ j)⁻¹ ∈ D := D.mul_mem hy₀D (D.inv_mem (D.pow_mem hxD j))
  have hy1 : y₀ * (x ^ j)⁻¹ ≠ 1 := by
    intro h
    apply hy₀x
    rw [mul_inv_eq_one.mp h]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers x) j
  have hCmem : B₀ * (A ^ j)⁻¹ ∈ LinTorus.inducedMatrices ψ D :=
    LinTorus.mem_inducedMatrices.mpr ⟨_, hyD, hyC⟩
  have hwi : (w₀ * (a ^ j)⁻¹) i.1 = 1 := by
    have h1 : (a i.1) ^ j = w₀ i.1 := Units.ext (by
      rw [Units.val_pow_eq_pow_val, hα, hβ, ← map_pow, hj])
    rw [Pi.mul_apply, Pi.inv_apply, Pi.pow_apply, h1, mul_inv_cancel]
  have hθC : θ (w₀ * (a ^ j)⁻¹) = B₀ * (A ^ j)⁻¹ := by rw [map_mul, map_inv, map_pow, ha, hw₀]
  have hsupp := hTsupp _ hwi
  rw [hθC] at hsupp
  obtain ⟨K, hK, hTK, hKw⟩ := exists_fixedBlock_component hF hker (hDel.2 _ hyD) hyC hTq
    (fun s hs => (hsupp s hs).1) (fun s hs => (hsupp s hs).2)
  have hAC : Commute (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F)
      ((B₀ * (A ^ j)⁻¹ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) :=
    (show Commute A (B₀ * (A ^ j)⁻¹) from hDcomm A hAmem _ hCmem).units_val
  obtain ⟨hnm, hcentK⟩ := hKw x A hA hAC
  have hxK : x ∉ Subgroup.centralizer (K : Set G) := by
    intro hxK
    have hfix := hcentK hxK
    have hT1 : ∀ s ∈ S i, s = 1 := by
      intro s hs
      have hf := hfix s hs
      obtain ⟨_, ⟨g, rfl⟩, hg⟩ := hs
      rw [← hg, ← ha, hθΦ, hθΦ, ← map_one Φ, ← map_sub, ← map_mul] at hf
      have h2 := congrFun (hΦinj hf) i.1
      simp only [Pi.mul_apply, Pi.sub_apply, Pi.one_apply, blockEmbed_apply_self] at h2
      rw [hα] at h2
      have hg1 : (SpecialLinearGroup.toGL g : GL (Fin (e i.1)) (E i.1)) = 1 :=
        eq_one_of_mul_scalar_sub_one hα1 h2
      have hg' : g = 1 := SpecialLinearGroup.toGL_injective (by rw [hg1, map_one])
      apply hιinj
      rw [← hg, hg', map_one, map_one, map_one]
    obtain ⟨a₁, a₂, haa⟩ := LayerFacts.exists_mul_ne_of_isQuasisimple hTq
    have h1 : a₁ = 1 := Subtype.ext (hT1 _ a₁.2)
    exact haa (by rw [h1, one_mul, mul_one])
  have h5J : 5 ∣ Nat.card ((S i).map ψ) := by
    have hcardT : Nat.card (S i) = Nat.card (SpecialLinearGroup (Fin (e i.1)) (E i.1)) := by
      rw [← Subgroup.card_map_of_injective hιinj, hSmap, Subgroup.card_map_of_injective hθinj]
      exact (Nat.card_congr (MonoidHom.ofInjective (blockEmbed_injective (E := E) (m := e)
        i.1)).toEquiv).symm
    have hα0 : α ≠ 0 := by
      rintro rfl
      simp at hα5
    have h5E : 5 ∣ Nat.card (E i.1) - 1 := by
      have h1 : orderOf (Units.mk0 α hα0) = 5 := by rw [← orderOf_units, Units.val_mk0, hαo]
      rw [← Nat.card_units, ← h1]
      exact orderOf_dvd_natCard _
    have h5S : 5 ∣ Nat.card (SpecialLinearGroup (Fin (e i.1)) (E i.1)) :=
      (h5E.trans (Nat.sub_one_dvd_pow_sub_one _ 2)).trans (LayerPDiv.sq_sub_one_dvd_card_SL i.2.1)
    exact LayerPDiv.dvd_card_map_of_perfect ψ hker (ggCommutator_eq_of_isQuasisimple hTq) hp
      (hcardT ▸ h5S)
  exact ⟨_, hyD, hy1, K, hK, hTK, h5J.trans (Subgroup.card_dvd_of_le hTK), hxK, hnm⟩

end Main

end FieldFiveSL

section Tag

open CFSG.Assembly

theorem ggFieldFiveNbrTag_PSL : GGFieldFiveNbrTag .PSL := by
  intro G _ _ n ψ G₀ hpres D hDel hDcard _ hDdiag x hxD L hL hLmark J hJ
  obtain ⟨⟨hadm, hrk⟩, ⟨hrange, hker⟩, -, -⟩ := hpres
  obtain ⟨-, -, hn, -⟩ := hadm
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [← hrange] at hL ⊢
  have hpair : ∀ z : G, GGPsiInnerDiag (ggU .PSL (m + 1) 1).D ψ z →
      ∃ A : GL (Fin (m + 1)) (GaloisField 2 1), (z, A) ∈ LinFusion.ggInducedPairs ψ := by
    intro z hz
    obtain ⟨A, hA⟩ : ∃ A : GL (Fin (m + 1)) (GaloisField 2 1),
        (z⁻¹, A) ∈ LinFusion.ggInducedPairs ψ :=
      LinFusion.exists_mem_ggInducedPairs (y := z⁻¹) hrk ψ hker (by rwa [inv_inv])
    refine ⟨A⁻¹, ?_⟩
    have h := (LinFusion.ggInducedPairs ψ).inv_mem hA
    rwa [Prod.inv_mk, inv_inv] at h
  have hF : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 one_ne_zero, pow_one]
  exact FieldFiveSL.fieldFive_sl hF hker hDel hDcard (fun d hd => hpair d (hDdiag d hd)) hxD hL
    hLmark hJ

theorem ggSixFieldFiveInput_of_genuine_PSL (hPSU : GGFieldFiveNbrTag .PSU)
    (hPSp : GGFieldFiveNbrTag .PSp) (hPlus : GGFieldFiveNbrTag .POmegaPlus)
    (hMinus : GGFieldFiveNbrTag .POmegaMinus) (hF4 : GGFieldFiveNbrTag .F4)
    (hE6 : GGFieldFiveNbrTag .E6) (hE7 : GGFieldFiveNbrTag .E7) (hE8 : GGFieldFiveNbrTag .E8)
    (hTwE6 : GGFieldFiveNbrTag .twistedE6) : GGSixFieldFiveInput :=
  ggSixFieldFiveInput_of_genuine ggFieldFiveNbrTag_PSL hPSU hPSp hPlus hMinus hF4 hE6 hE7 hE8
    hTwE6

end Tag

end CFSG.StandardType
