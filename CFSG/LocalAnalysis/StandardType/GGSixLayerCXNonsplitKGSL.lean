module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGSLBasic
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplit
public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDiv

public section

namespace CFSG.StandardType

namespace LinNonsplit

open CFSG.Assembly CFSG.RankThree.PartOne.KCLinComm Matrix LayerFacts

section Scalar

theorem exists_scalar_of_forall_commute {r : ℕ} {D : Fin r → Type} {d : Fin r → ℕ}
    [∀ i, Field (D i)] {v : PiGL D d} (hv : ∀ u : PiGL D d, v * u = u * v) (j : Fin r) :
    ∃ c : D j, ((v j : GL (Fin (d j)) (D j)) : Matrix (Fin (d j)) (Fin (d j)) (D j)) =
      Matrix.scalar (Fin (d j)) c := by
  classical
  have hc : v j ∈ Subgroup.center (GL (Fin (d j)) (D j)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h := congrFun (hv (Pi.mulSingle j g)) j
    simp only [Pi.mul_apply, Pi.mulSingle_eq_same] at h
    exact h.symm
  obtain ⟨c, hc⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp hc
  exact ⟨c, hc.symm⟩

theorem eq_one_of_mul_scalar_sub_one {k : ℕ} {E : Type*} [Field E] {g : GL (Fin k) E} {c : E}
    (hc : c ≠ 1)
    (h : (g : Matrix (Fin k) (Fin k) E) * (Matrix.scalar (Fin k) c - 1) =
      Matrix.scalar (Fin k) c - 1) : g = 1 := by
  have hc' : c - 1 ≠ 0 := sub_ne_zero.mpr hc
  have e : Matrix.scalar (Fin k) c - 1 = (c - 1) • (1 : Matrix (Fin k) (Fin k) E) := by
    rw [sub_smul, one_smul, Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]
  rw [e, Matrix.mul_smul, mul_one] at h
  exact Units.ext ((smul_right_injective _ hc') h)

end Scalar

section Block

variable {m : ℕ} {F : Type} [Field F]
  {r : ℕ} {D : Fin r → Type} {d : Fin r → ℕ} [∀ i, Field (D i)] [∀ i, Algebra F (D i)]
  {r' : ℕ} {D' : Fin r' → Type} {d' : Fin r' → ℕ} [∀ i, Field (D' i)] [∀ i, Algebra F (D' i)]

theorem exists_goodBlock_le [∀ i, Finite (D i)] [∀ i, CharP (D i) 2] [∀ i, Finite (D' i)]
    [∀ i, CharP (D' i) 2]
    {Φ : (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) →ₐ[F] Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    {θ : PiGL D d →* GL (Fin (m + 1)) F} (hθinj : Function.Injective θ)
    (hθΦ : ∀ w, ((θ w : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      Φ (fun i => ((w i : GL (Fin (d i)) (D i)) : Matrix (Fin (d i)) (Fin (d i)) (D i))))
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
    {p : ℕ} (hp : p.Prime) (hBp : B ^ p = 1) (hBθ : B ∈ θ.range)
    {b : Fin r} (hb : GoodBlock D d b)
    (hpS : ¬ p ∣ Nat.card (SpecialLinearGroup (Fin (d b)) (D b))) :
    ∃ j, GoodBlock D' d' j ∧ (∀ v, θ' v = B → v j = 1) ∧
      ((blockSL D d b).map θ).comap
          (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin (m + 1)) F →* GL (Fin (m + 1)) F) ≤
        ((blockSL D' d' j).map θ').comap SpecialLinearGroup.toGL := by
  classical
  set ι : SpecialLinearGroup (Fin (m + 1)) F →* GL (Fin (m + 1)) F :=
    SpecialLinearGroup.toGL with hιdef
  set Sb := ((blockSL D d b).map θ).comap ι with hSb
  obtain ⟨w, hw⟩ := hBθ
  have hwp : w ^ p = 1 := hθinj (by rw [map_pow, hw, hBp, map_one])
  have hwb : w b = 1 := eq_one_of_pow_eq_one_of_not_dvd hb.1 hp hpS (by
    rw [← Pi.pow_apply, hwp, Pi.one_apply])
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
  have key : ∀ s ∈ Sb, ∃ γ : PiGL D' d', θ' γ = ι s ∧ ∀ j, v j ≠ 1 → γ j = 1 := by
    intro s hs
    obtain ⟨t, ⟨g, rfl⟩, hts⟩ := hs
    have hcomm : Commute ((ι s : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F)
        (B : Matrix (Fin (m + 1)) (Fin (m + 1)) F) := by
      rw [← hts, ← hw]
      have h0 : Commute (blockEmbed D d b g) w := blockEmbed_mul_comm hwb g
      exact (h0.map θ).units_val
    have hfix : ((ι s : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
        ((B : Matrix (Fin (m + 1)) (Fin (m + 1)) F) - 1) =
          (B : Matrix (Fin (m + 1)) (Fin (m + 1)) F) - 1 := by
      rw [← hts, ← hw, hθΦ, hθΦ, ← map_one Φ, ← map_sub, ← map_mul,
        blockEmbed_mul_sub_one hwb g]
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
  have hSq : CFSG.IsQuasisimple Sb := isQuasisimple_comap_blockSL hθinj hb
  obtain ⟨s₀, hs₀⟩ : ∃ s : Sb, s ≠ 1 := by
    obtain ⟨a, a', haa⟩ := LayerFacts.exists_mul_ne_of_isQuasisimple hSq
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
  have hsupp : ∀ s ∈ Sb, ι s ∈ R.map θ' := by
    intro s hs
    obtain ⟨γ, hγ, hγ1⟩ := key s hs
    refine ⟨γ, ⟨γ j₀, ?_⟩, hγ⟩
    funext i
    by_cases hi : i = j₀
    · subst hi
      simp
    · rw [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne hi]
      exact (hγ1 i fun h => hi (huniq i j₀ h hvj₀)).symm
  have hperf : ⁅Sb, Sb⁆ = Sb := ggCommutator_eq_of_isQuasisimple hSq
  have hle : Sb.map ι ≤ R.map θ' := Subgroup.map_le_iff_le_comap.mpr fun s hs => hsupp s hs
  have hder : ∀ k, Sb.map ι ≤ (ggDer R k).map θ' := by
    intro k
    calc Sb.map ι = (ggDer Sb k).map ι := by rw [ggDer_of_perfect hperf]
      _ = ggDer (Sb.map ι) k := map_ggDer ι Sb k
      _ ≤ ggDer (R.map θ') k := ggDer_mono hle k
      _ = (ggDer R k).map θ' := (map_ggDer θ' R k).symm
  have hj₀good : GoodBlock D' d' j₀ := by
    by_contra hng
    obtain ⟨k, hk⟩ := (isSolvable_of_not_goodBlock hng).solvable
    have h1 : ggDer R k = ⊥ := by
      rw [hR, MonoidHom.range_eq_map, ← map_ggDer, ggDer_top, hk, Subgroup.map_bot]
    have h2 := hder k
    rw [h1, Subgroup.map_bot, le_bot_iff,
      Subgroup.map_eq_bot_iff_of_injective Sb (f := ι) SpecialLinearGroup.toGL_injective] at h2
    apply hs₀
    have h3 : (s₀ : SpecialLinearGroup (Fin (m + 1)) F) ∈ (⊥ : Subgroup _) := h2 ▸ s₀.2
    exact Subtype.ext (Subgroup.mem_bot.mp h3)
  refine ⟨j₀, hj₀good, fun v' hv' => ?_, fun s hs => ?_⟩
  · rw [hθ'inj (hv'.trans hv.symm)]
    exact hvj₀
  obtain ⟨t, ht, hts⟩ := hder 1 (Subgroup.mem_map_of_mem ι hs)
  exact ⟨t, commutator_range_mulSingle_le j₀ ht, hts⟩

end Block

section Main

variable {m : ℕ} {F : Type} [Field F] {G : Type*} [Group G]

theorem exists_isComponentOf_le [Finite G] [Finite F] [CharP F 2]
    {ψ : SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpF : ¬ p ∣ Nat.card F - 1) {x y : G}
    (hx : x ^ p = 1) (hy : y ^ p = 1) (hxy : x * y = y * x)
    {A₀ B₀ : GL (Fin (m + 1)) F} (hA₀ : (x, A₀) ∈ LinFusion.ggInducedPairs ψ)
    (hB₀ : (y, B₀) ∈ LinFusion.ggInducedPairs ψ)
    {K : Subgroup G} (hK : IsComponentOf K (ψ.range ⊓ Subgroup.centralizer {x}))
    (hpK : ¬ p ∣ Nat.card K) :
    ∃ K' : Subgroup G, IsComponentOf K' (ψ.range ⊓ Subgroup.centralizer {y}) ∧ K ≤ K' := by
  classical
  obtain ⟨A, hA, hAp⟩ := exists_mem_ggInducedPairs_pow_eq_one hker hp hpF hx hA₀
  obtain ⟨B, hB, hBp⟩ := exists_mem_ggInducedPairs_pow_eq_one hker hp hpF hy hB₀
  have hAB : A * B = B * A := mul_comm_of_mem_ggInducedPairs hker hp hpF hxy hA hB hAp
  have hcz : ∀ z : G, Subgroup.centralizer (Subgroup.zpowers z : Set G) =
      Subgroup.centralizer {z} := fun z => by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [← hcz] at hK ⊢
  set ι : SpecialLinearGroup (Fin (m + 1)) F →* GL (Fin (m + 1)) F :=
    SpecialLinearGroup.toGL with hιdef
  have hιinj : Function.Injective ι := SpecialLinearGroup.toGL_injective
  obtain ⟨r, D, d, _, _, _, Φ, θ, -, -, -, hθinj, hθrange, hθΦ⟩ :=
    exists_piMat_commutant (LinTorus.inducedMatrices ψ (Subgroup.zpowers x))
      (natCast_card_inducedMatrices_ne_zero hker hp hp2 (ggIsPGroup_zpowers_of_pow_eq_one hx))
  have : ∀ i, CharP (D i) 2 := fun i =>
    charP_of_injective_algebraMap (algebraMap F (D i)).injective 2
  have hC₀θ : ggCentSL ψ (Subgroup.zpowers x) = θ.range.comap ι := by rw [hθrange]; rfl
  set S : {b : Fin r // GoodBlock D d b} → Subgroup (SpecialLinearGroup (Fin (m + 1)) F) :=
    fun b => ((blockSL D d b.1).map θ).comap ι with hSdef
  have hSmap : ∀ b, (S b).map ι = (blockSL D d b.1).map θ := fun b =>
    Subgroup.map_comap_eq_self (map_blockSL_le_range θ b.2)
  have hÑmap : (⨆ b, S b).map ι = (goodSL D d).map θ := by
    rw [Subgroup.map_iSup, goodSL, Subgroup.map_iSup]
    exact iSup_congr hSmap
  have hSC : ∀ b, S b ≤ ggCentSL ψ (Subgroup.zpowers x) := fun b => by
    rw [hC₀θ]
    exact Subgroup.comap_mono (Subgroup.map_le_range θ _)
  have hSn : ∀ b, ∀ c ∈ ggCentSL ψ (Subgroup.zpowers x), ∀ s ∈ S b, c * s * c⁻¹ ∈ S b := by
    intro b c hc s hs
    rw [hC₀θ] at hc
    exact conj_mem_comap_blockSL hc hs
  have hSq : ∀ b, CFSG.IsQuasisimple (S b) := fun b => isQuasisimple_comap_blockSL hθinj b.2
  have hder : ∃ k, ggDer (ggCentSL ψ (Subgroup.zpowers x)) k ≤ ⨆ b, S b := by
    obtain ⟨k, hk⟩ := exists_derivedSeries_le_goodSL (E := D) (m := d)
    refine ⟨k, ?_⟩
    rw [← Subgroup.map_le_map_iff_of_injective hιinj, map_ggDer, hÑmap]
    calc ggDer ((ggCentSL ψ (Subgroup.zpowers x)).map ι) k ≤ ggDer θ.range k :=
          ggDer_mono (by rw [hC₀θ]; exact Subgroup.map_comap_le _ _) k
      _ = (ggDer ⊤ k).map θ := by rw [map_ggDer, ← MonoidHom.range_eq_map]
      _ = (derivedSeries _ k).map θ := by rw [ggDer_top]
      _ ≤ (goodSL D d).map θ := Subgroup.map_mono hk
  obtain ⟨b, rfl⟩ := LayerPDiv.exists_eq_map_of_isComponentOf ψ hker
    (map_ggCentSL_le (forall_mem_zpowers_exists hA)) (normal_map_ggCentSL hker)
    (commutator_le_map_ggCentSL hker) S hSC hSn hSq hder hK
  have hcardS : Nat.card (S b) = Nat.card (SpecialLinearGroup (Fin (d b.1)) (D b.1)) := by
    rw [← Subgroup.card_map_of_injective hιinj, hSmap, Subgroup.card_map_of_injective hθinj]
    exact (Nat.card_congr (MonoidHom.ofInjective (blockEmbed_injective (E := D) (m := d)
      b.1)).toEquiv).symm
  have hpS : ¬ p ∣ Nat.card (SpecialLinearGroup (Fin (d b.1)) (D b.1)) := fun h =>
    hpK (LayerPDiv.dvd_card_map_of_perfect ψ hker (ggCommutator_eq_of_isQuasisimple (hSq b)) hp
      (hcardS ▸ h))
  obtain ⟨r', D', d', _, _, _, Φ', θ', hd', hΦ'inj, hΦ'range, hθ'inj, hθ'range, hθ'Φ'⟩ :=
    exists_piMat_commutant (LinTorus.inducedMatrices ψ (Subgroup.zpowers y))
      (natCast_card_inducedMatrices_ne_zero hker hp hp2 (ggIsPGroup_zpowers_of_pow_eq_one hy))
  have : ∀ i, CharP (D' i) 2 := fun i =>
    charP_of_injective_algebraMap (algebraMap F (D' i)).injective 2
  have hBmem : B ∈ LinTorus.inducedMatrices ψ (Subgroup.zpowers y) :=
    LinTorus.mem_inducedMatrices.mpr ⟨y, Subgroup.mem_zpowers y, hB⟩
  have hBA : Commute (B : Matrix (Fin (m + 1)) (Fin (m + 1)) F)
      (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) := by
    have h := congrArg Units.val hAB
    rw [Units.val_mul, Units.val_mul] at h
    exact h.symm
  have hBθ : B ∈ θ.range := by
    rw [hθrange]
    exact Subgroup.mem_centralizer_iff.mpr fun g hg => Units.ext (by
      rw [Units.val_mul, Units.val_mul]
      exact (commute_of_mem_inducedMatrices hker hA hBA hg).eq.symm)
  obtain ⟨j, hj, -, hle⟩ := exists_goodBlock_le hθinj hθΦ hd' hΦ'inj hθ'inj hθ'Φ' hΦ'range
    hθ'range hBmem (fun M hM g hg => commute_of_mem_inducedMatrices hker hB hM hg) hp hBp hBθ
    b.2 hpS
  have hC₀θ' : ggCentSL ψ (Subgroup.zpowers y) = θ'.range.comap ι := by rw [hθ'range]; rfl
  refine ⟨(((blockSL D' d' j).map θ').comap ι).map ψ, ?_, Subgroup.map_mono hle⟩
  refine isComponentOf_map_of_le ψ hker (map_ggCentSL_le (forall_mem_zpowers_exists hB))
    (normal_map_ggCentSL hker) ?_ ?_ (isQuasisimple_comap_blockSL hθ'inj hj)
  · rw [hC₀θ']
    exact Subgroup.comap_mono (Subgroup.map_le_range θ' _)
  · intro c hc s hs
    rw [hC₀θ'] at hc
    exact conj_mem_comap_blockSL hc hs

end Main

end LinNonsplit

section Tag

theorem ggNonsplitCompLiftTag_PSL : GGNonsplitCompLiftTag .PSL := by
  intro G _ _ n f ψ G₀ hpres p hp hp2 hq1 _ x y hx hy hxy _ _ hxD hyD K hK hpK
  obtain ⟨⟨hadm, hrk⟩, ⟨hrange, hker⟩, -, -⟩ := hpres
  obtain ⟨-, hf, hn, -⟩ := hadm
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [← hrange] at hK ⊢
  have hpair : ∀ z : G, GGPsiInnerDiag (ggU .PSL (m + 1) f).D ψ z →
      ∃ A : GL (Fin (m + 1)) (GaloisField 2 f), (z, A) ∈ LinFusion.ggInducedPairs ψ := by
    intro z hz
    obtain ⟨A, hA⟩ : ∃ A : GL (Fin (m + 1)) (GaloisField 2 f),
        (z⁻¹, A) ∈ LinFusion.ggInducedPairs ψ :=
      LinFusion.exists_mem_ggInducedPairs (y := z⁻¹) hrk ψ hker (by rwa [inv_inv])
    refine ⟨A⁻¹, ?_⟩
    have h := (LinFusion.ggInducedPairs ψ).inv_mem hA
    rwa [Prod.inv_mk, inv_inv] at h
  obtain ⟨A, hA⟩ := hpair x hxD
  obtain ⟨B, hB⟩ := hpair y hyD
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  exact LinNonsplit.exists_isComponentOf_le hker hp hp2 (by rwa [hF]) hx hy hxy hA hB hK hpK

end Tag

end CFSG.StandardType
