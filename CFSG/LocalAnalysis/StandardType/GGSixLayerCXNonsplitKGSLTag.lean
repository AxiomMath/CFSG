module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGSLNbr

public section

namespace CFSG.StandardType

namespace LinNonsplit

open CFSG.Assembly CFSG.RankThree.PartOne.KCLinComm Matrix LayerFacts

section Main

variable {m : ℕ} {F : Type} [Field F]

theorem not_ggNbrClauseFiveMarking_of_sl {G : Type} [Group G] [Finite G] [Finite F] [CharP F 2]
    {f : ℕ} (hf : 1 ≤ f) (hF : Nat.card F = 2 ^ f)
    {ψ : SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hq1 : ¬ p ∣ 2 ^ f - 1) (hq2 : ¬ p ∣ 2 ^ f + 1) {x y : G}
    (hx : x ^ p = 1) (hy : y ^ p = 1) (hxy : x * y = y * x)
    {A₀ B₀ : GL (Fin (m + 1)) F} (hA₀ : (x, A₀) ∈ LinFusion.ggInducedPairs ψ)
    (hB₀ : (y, B₀) ∈ LinFusion.ggInducedPairs ψ)
    {K K' : Subgroup G} (hK : IsComponentOf K (ψ.range ⊓ Subgroup.centralizer {x}))
    (hpK : ¬ p ∣ Nat.card K) (hK' : IsComponentOf K' (ψ.range ⊓ Subgroup.centralizer {y}))
    (hKK' : K ≤ K') : ¬ GGNbrClauseFiveMarking p x K' := by
  classical
  have hpF : ¬ p ∣ Nat.card F - 1 := by rwa [hF]
  obtain ⟨A, hA, hAp⟩ := exists_mem_ggInducedPairs_pow_eq_one hker hp hpF hx hA₀
  obtain ⟨B, hB, hBp⟩ := exists_mem_ggInducedPairs_pow_eq_one hker hp hpF hy hB₀
  have hAB : A * B = B * A := mul_comm_of_mem_ggInducedPairs hker hp hpF hxy hA hB hAp
  have hcz : ∀ z : G, Subgroup.centralizer (Subgroup.zpowers z : Set G) =
      Subgroup.centralizer {z} := fun z => by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [← hcz] at hK hK'
  set ι : SpecialLinearGroup (Fin (m + 1)) F →* GL (Fin (m + 1)) F :=
    SpecialLinearGroup.toGL with hιdef
  have hιinj : Function.Injective ι := SpecialLinearGroup.toGL_injective
  obtain ⟨r, D, d, _, _, _, Φ, θ, hd, hΦinj, hΦrange, hθinj, hθrange, hθΦ⟩ :=
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
  have hAB' : Commute (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F)
      (B : Matrix (Fin (m + 1)) (Fin (m + 1)) F) := by
    have h := congrArg Units.val hAB
    rw [Units.val_mul, Units.val_mul] at h
    exact h
  have hBθ : B ∈ θ.range := by
    rw [hθrange]
    exact Subgroup.mem_centralizer_iff.mpr fun g hg => Units.ext (by
      rw [Units.val_mul, Units.val_mul]
      exact (commute_of_mem_inducedMatrices hker hA hAB'.symm hg).eq.symm)
  obtain ⟨j, hj, hvj, hle⟩ := exists_goodBlock_le hθinj hθΦ hd' hΦ'inj hθ'inj hθ'Φ' hΦ'range
    hθ'range hBmem (fun M hM g hg => commute_of_mem_inducedMatrices hker hB hM hg) hp hBp hBθ
    b.2 hpS
  set S' := ((blockSL D' d' j).map θ').comap ι with hS'def
  have hC₀θ' : ggCentSL ψ (Subgroup.zpowers y) = θ'.range.comap ι := by rw [hθ'range]; rfl
  have hS'comp : IsComponentOf (S'.map ψ)
      (ψ.range ⊓ Subgroup.centralizer (Subgroup.zpowers y : Set G)) := by
    refine isComponentOf_map_of_le ψ hker (map_ggCentSL_le (forall_mem_zpowers_exists hB))
      (normal_map_ggCentSL hker) ?_ ?_ (isQuasisimple_comap_blockSL hθ'inj hj)
    · rw [hC₀θ']
      exact Subgroup.comap_mono (Subgroup.map_le_range θ' _)
    · intro c hc s hs
      rw [hC₀θ'] at hc
      exact conj_mem_comap_blockSL hc hs
  have hK'eq : K' = S'.map ψ := by
    rcases CFSG.LocalAnalysis.ComponentInitial.isComponentOf_eq_or_commute hK' hS'comp with h | h
    · exact h
    · exfalso
      have hc : K' ≤ Subgroup.centralizer ((S'.map ψ : Subgroup G) : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
      have hKc : (S b).map ψ ≤ Subgroup.centralizer (((S b).map ψ : Subgroup G) : Set G) :=
        (hKK'.trans hc).trans (Subgroup.centralizer_le (Subgroup.map_mono hle))
      obtain ⟨a₁, b₁, hab₁⟩ := LayerFacts.exists_mul_ne_of_isQuasisimple
        ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp hK.2.2)
      exact hab₁ (Subtype.ext (Subgroup.mem_centralizer_iff.mp (hKc b₁.2) a₁ a₁.2))
  obtain ⟨a, ha⟩ : A ∈ θ.range := by
    rw [hθrange]
    exact Subgroup.mem_centralizer_iff.mpr fun g hg => Units.ext (by
      rw [Units.val_mul, Units.val_mul]
      exact (commute_of_mem_inducedMatrices hker hA (Commute.refl _) hg).eq.symm)
  have hap : a ^ p = 1 := hθinj (by rw [map_pow, ha, hAp, map_one])
  have hab : a b.1 = 1 := eq_one_of_pow_eq_one_of_not_dvd b.2.1 hp hpS (by
    rw [← Pi.pow_apply, hap, Pi.one_apply])
  have hsingle : ∀ {r₀ : ℕ} {E : Fin r₀ → Type} {e : Fin r₀ → ℕ} [∀ i, Field (E i)]
      (w : PiGL E e) (i₀ : Fin r₀), w i₀ = 1 →
      (Pi.single i₀ 1 : Π i, Matrix (Fin (e i)) (Fin (e i)) (E i)) *
          (fun i => ((w i : GL (Fin (e i)) (E i)) : Matrix (Fin (e i)) (Fin (e i)) (E i))) =
        Pi.single i₀ 1 ∧
      (fun i => ((w i : GL (Fin (e i)) (E i)) : Matrix (Fin (e i)) (Fin (e i)) (E i))) *
          (Pi.single i₀ 1 : Π i, Matrix (Fin (e i)) (Fin (e i)) (E i)) = Pi.single i₀ 1 := by
    intro r₀ E e _ w i₀ hw
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
  have hDb : Nat.card (D b.1) = Nat.card F := by
    have hs := hsingle a b.1 hab
    refine card_eq_of_corner Φ hΦinj (A := (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F))
      (fun X hX => (hΦrange X).mpr fun g hg => (commute_of_mem_inducedMatrices hker hA hX hg).eq)
      (hd b.1) ?_ ?_
    · rw [← ha, hθΦ, ← map_mul, hs.1]
    · rw [← ha, hθΦ, ← map_mul, hs.2]
  obtain ⟨v, hv⟩ : B ∈ θ'.range := by
    rw [hθ'range]
    exact Subgroup.mem_centralizer_iff.mpr fun g hg => Units.ext (by
      rw [Units.val_mul, Units.val_mul]
      exact (commute_of_mem_inducedMatrices hker hB (Commute.refl _) hg).eq.symm)
  have hD'j : Nat.card (D' j) = Nat.card F := by
    have hs := hsingle v j (hvj v hv)
    refine card_eq_of_corner Φ' hΦ'inj (A := (B : Matrix (Fin (m + 1)) (Fin (m + 1)) F))
      (fun X hX => (hΦ'range X).mpr fun g hg => (commute_of_mem_inducedMatrices hker hB hX hg).eq)
      (hd' j) ?_ ?_
    · rw [← hv, hθ'Φ', ← map_mul, hs.1]
    · rw [← hv, hθ'Φ', ← map_mul, hs.2]
  have hlift : ∀ s, θ' (blockEmbed D' d' j s) ∈ ι.range := fun s =>
    map_blockSL_le_range θ' hj ⟨blockEmbed D' d' j s, ⟨s, rfl⟩, rfl⟩
  set β : SpecialLinearGroup (Fin (d' j)) (D' j) →* SpecialLinearGroup (Fin (m + 1)) F :=
    (MonoidHom.ofInjective hιinj).symm.toMonoidHom.comp
      ((θ'.comp (blockEmbed D' d' j)).codRestrict ι.range hlift) with hβdef
  have hβ : ∀ s, ι (β s) = θ' (blockEmbed D' d' j s) := fun s =>
    MonoidHom.apply_ofInjective_symm hιinj _
  have hβinj : Function.Injective β := fun s t h =>
    blockEmbed_injective j (hθ'inj (by rw [← hβ, ← hβ, h]))
  have hβrange : β.range = S' := by
    ext s
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨blockEmbed D' d' j t, ⟨t, rfl⟩, (hβ t).symm⟩
    · rintro ⟨w, ⟨t, rfl⟩, hw⟩
      exact ⟨t, hιinj ((hβ t).trans hw)⟩
  obtain ⟨a', ha'⟩ : A ∈ θ'.range := by
    rw [hθ'range]
    exact Subgroup.mem_centralizer_iff.mpr fun g hg => Units.ext (by
      rw [Units.val_mul, Units.val_mul]
      exact (commute_of_mem_inducedMatrices hker hB hAB' hg).eq.symm)
  have hconj : ∀ s t : SpecialLinearGroup (Fin (d' j)) (D' j),
      (t : Matrix (Fin (d' j)) (Fin (d' j)) (D' j)) =
        (a' j : Matrix (Fin (d' j)) (Fin (d' j)) (D' j)) *
          (s : Matrix (Fin (d' j)) (Fin (d' j)) (D' j)) *
            (((a' j)⁻¹ : GL (Fin (d' j)) (D' j)) : Matrix (Fin (d' j)) (Fin (d' j)) (D' j)) →
      ι (β t) = A * ι (β s) * A⁻¹ := by
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
  have hcent : d' j = 2 → x ∈ Subgroup.centralizer ((β.range.map ψ : Subgroup G) : Set G) := by
    intro h2
    have hcardS' : Nat.card S' = Nat.card (SpecialLinearGroup (Fin (d' j)) (D' j)) := by
      rw [← Subgroup.card_map_of_injective hιinj, Subgroup.map_comap_eq_self
        (map_blockSL_le_range θ' hj), Subgroup.card_map_of_injective hθ'inj]
      exact (Nat.card_congr (MonoidHom.ofInjective (blockEmbed_injective (E := D') (m := d')
        j)).toEquiv).symm
    have hSS : S b = S' := Subgroup.eq_of_le_of_card_ge hle (by
      rw [hcardS', hcardS]
      exact card_SL_le_of_eq_two (hD'j.trans hDb.symm) h2 b.2.1)
    rw [hβrange, ← hSS]
    refine Subgroup.mem_centralizer_iff.mpr fun g hg => ?_
    have hgx := Subgroup.mem_centralizer_iff.mp (hK.1 hg).2 x (Subgroup.mem_zpowers x)
    exact hgx.symm
  have h7 : f = 1 → p ≠ 7 := by
    rintro rfl rfl
    have hDb2 : Nat.card (D b.1) = 2 := by rw [hDb, hF, pow_one]
    have hdb3 : 3 ≤ d b.1 := by
      rcases b.2.2 with h | ⟨s, hs⟩
      · exact h
      · exfalso
        have := Fintype.ofFinite (D b.1)
        have h4 := Finset.card_le_univ s
        rw [hs, ← Nat.card_eq_fintype_card, hDb2] at h4
        omega
    exact hpS (seven_dvd_card_SL hDb2 hdb3)
  rw [hK'eq, ← hβrange]
  exact not_ggNbrClauseFiveMarking_block hf hF hker hj.1 (hD'j) hj.2 hβinj hA hconj hp hp2 hq1
    hq2 h7 hcent

end Main

end LinNonsplit

section Tag

theorem ggNonsplitNbrMarkingTag_PSL : GGNonsplitNbrMarkingTag .PSL := by
  intro G _ _ n f ψ G₀ hpres p hp hp2 hq1 hq2 x y hx hy hxy _ _ hxD hyD K K' hK hpK hK' hKK' _
  obtain ⟨⟨hadm, hrk⟩, ⟨hrange, hker⟩, -, -⟩ := hpres
  obtain ⟨-, hf, hn, -⟩ := hadm
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [← hrange] at hK hK'
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
  exact LinNonsplit.not_ggNbrClauseFiveMarking_of_sl hf hF hker hp hp2 hq1 hq2 hx hy hxy hA hB
    hK hpK hK' hKK'

theorem ggNonsplitTag_PSL : GGNonsplitTag .PSL :=
  ⟨ggNonsplitCompLiftTag_PSL, ggNonsplitNbrMarkingTag_PSL⟩

theorem ggSixLayerCXNonsplitInput_of_tags_PSL (hPSU : GGNonsplitTag .PSU)
    (hPSp : GGNonsplitTag .PSp) (hPlus : GGNonsplitTag .POmegaPlus)
    (hMinus : GGNonsplitTag .POmegaMinus) (hF4 : GGNonsplitTag .F4) (hE6 : GGNonsplitTag .E6)
    (hE7 : GGNonsplitTag .E7) (hE8 : GGNonsplitTag .E8) (hTwE6 : GGNonsplitTag .twistedE6) :
    GGSixLayerCXNonsplitInput :=
  ggSixLayerCXNonsplitInput_of_tags ggNonsplitTag_PSL hPSU hPSp hPlus hMinus
    hF4 hE6 hE7 hE8 hTwE6

end Tag

end CFSG.StandardType
