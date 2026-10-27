module

public import CFSG.LocalAnalysis.StandardType.GGUSixTwoSetup
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallUnitDvd63Norm

public section

namespace CFSG.StandardType.USixTwo

open Matrix CFSG.Assembly CFSG.StandardType CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.SectionRank.OddCover CFSG.StandardType.TableBUE
  CFSG.StandardType.SmallU CFSG.StandardType.UnitTB CFSG.StandardType.Line63.H5
  CFSG.StandardType.LineU
open scoped commutatorElement

theorem concl_downstairs {Lb : Type} [Group Lb] [Finite Lb] {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ 1) ^ 2) {φ : ↥(unitarySU 2 1 K 6) →* Lb} (hM : Model φ)
    {Ab : Subgroup (MulAut Lb)}
    (hdiag : ∀ a ∈ Ab, ∃ t : Fin 6 → K, ActsDiagU φ a t) {s t : Fin 6} (hst : s ≠ t)
    (hpair : ∀ a ∈ Ab, ∀ σ : Fin 6 → Kˣ, ActsU φ a σ → σ s = σ t) {ab : MulAut Lb}
    (hab : ab ∈ Ab) (hab1 : ab ≠ 1)
    (hEcomp : IsComponentOf (LargeEvenLayer (ggFix ab)) (ggFix ab))
    (hsmall : GGStdSubSmallHyp 3 Ab ab) : GGStdSubTwoTorusConcl 3 Ab ab := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  have hpq : 3 ∣ 2 ^ 1 + 1 := by norm_num
  have hd3 : 3 ≤ 6 := by norm_num
  have hn : 1 ≤ 1 := le_rfl
  obtain ⟨Usw, hUsw1, hUsw2, hUswA, hUswN, hUswS⟩ := exists_swap_group hM hst hd3 hdiag hpair
  obtain ⟨t₀, ht₀⟩ := hdiag ab hab
  obtain ⟨σ, -, hσ⟩ := ActsU.of_actsDiagU ht₀
  have hts : σ t = σ s := (hpair ab hab σ hσ).symm
  have hsS : s ∈ cls σ s := mem_cls.mpr rfl
  have htS : t ∈ cls σ s := mem_cls.mpr hts
  obtain ⟨i₀, hbig'⟩ := exists_bigOK_cls hM (by norm_num) le_rfl hσ hEcomp
  have hS4' : 4 ≤ (cls σ i₀).card := by
    rcases hbig' with h | ⟨h2, -⟩
    · exact h
    · omega
  have hlayer' : LargeEvenLayer (ggFix ab) = (blockSU (cls σ i₀)).map φ :=
    layer_eq_block hM hσ (cls_isCls σ i₀) (isQuasisimple_block hM hbig') hEcomp
  have hSS' : cls σ i₀ = cls σ s := by
    by_contra hne
    have hsS' : s ∉ cls σ i₀ := fun hs => hne (by
      ext k
      rw [mem_cls, mem_cls, mem_cls.mp hs])
    have htS' : t ∉ cls σ i₀ := fun ht => hsS' (by
      rw [mem_cls] at ht ⊢
      rw [← hts]
      exact ht)
    obtain ⟨E, hEcard, hEdesc⟩ :=
      exists_torus hM hK hp hpq hsS' id (fun k hk => hk)
    rw [Finset.image_id] at hEcard
    have hEab : CFSG.Open.IsElemAbelian 3 E := isElemAbelian_torus fun e he => by
      obtain ⟨g, τ, h1, h2, h3, -⟩ := hEdesc e he
      exact ⟨g, τ, h1, h2, h3⟩
    have hElayer : E ≤ LargeEvenLayer (ggFix ab) := by
      rw [hlayer']
      exact torus_le_block fun e he => by
        obtain ⟨g, τ, h1, h2, -, h4, -⟩ := hEdesc e he
        exact ⟨g, τ, h1, h2, h4⟩
    have hEfix : ∀ a' ∈ Ab, ∀ e ∈ E, a' e = e := by
      intro a' ha'
      obtain ⟨t', ht'⟩ := hdiag a' ha'
      obtain ⟨σ', -, hσ'⟩ := ActsU.of_actsDiagU ht'
      exact fix_of_torus hσ' fun e he => by
        obtain ⟨g, τ, h1, h2, -⟩ := hEdesc e he
        exact ⟨g, τ, h1, h2⟩
    have hEnorm : E ≤ Subgroup.normalizer (Usw : Set Lb) := by
      intro e he
      obtain ⟨g, τ, h1, h2, -, h4, -⟩ := hEdesc e he
      exact hUswN e ⟨g, τ, h1, h2, by rw [h4 s hsS', h4 t htS']⟩
    have hEsmall : Nat.card E < 3 ^ 3 :=
      hsmall E hEab hElayer hEfix (Or.inr ⟨Usw, hUsw1, hUsw2, hUswA, hEnorm⟩)
    have h1 : 3 ^ 3 ≤ 3 ^ ((cls σ i₀).card - 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  set S := cls σ s with hSdef
  have hS := cls_isCls σ s
  have hbigS : BigOK 1 S := hSS' ▸ hbig'
  have hSd : ∃ k₀, k₀ ∉ S := by
    by_contra hall
    push Not at hall
    exact hab1 (hσ.eq_one_of_const hM s fun i j => by
      rw [mem_cls.mp (hall i), mem_cls.mp (hall j)])
  obtain ⟨k₀, hk₀⟩ := hSd
  have hSc : 2 ≤ S.card := by
    have h1 := Finset.card_le_card (show ({s, t} : Finset (Fin 6)) ⊆ S from fun k hk => by
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact hsS
      · rw [Finset.mem_singleton.mp hk]
        exact htS)
    rwa [Finset.card_pair hst] at h1
  have hlayer : LargeEvenLayer (ggFix ab) = (blockSU S).map φ := hSS' ▸ hlayer'
  set r : Fin 6 → Fin 6 := fun k => if k = t then s else k with hrdef
  have hrS : ∀ k ∈ S, r k ∈ S := fun k hk => by
    by_cases h : k = t
    · simp [hrdef, h, hsS]
    · simp [hrdef, h, hk]
  obtain ⟨E, hEcard, hEdesc⟩ := exists_torus hM hK hp hpq hk₀ r hrS
  have himg : S.card - 1 ≤ (S.image r).card := by
    have hsub : S.erase t ⊆ S.image r := fun k hk => by
      obtain ⟨hkt, hkS⟩ := Finset.mem_erase.mp hk
      exact Finset.mem_image.mpr ⟨k, hkS, by simp [hrdef, hkt]⟩
    have := Finset.card_le_card hsub
    rwa [Finset.card_erase_of_mem htS] at this
  have hEab : CFSG.Open.IsElemAbelian 3 E := isElemAbelian_torus fun e he => by
    obtain ⟨g, τ, h1, h2, h3, -⟩ := hEdesc e he
    exact ⟨g, τ, h1, h2, h3⟩
  have hElayer : E ≤ LargeEvenLayer (ggFix ab) := by
    rw [hlayer]
    exact torus_le_block fun e he => by
      obtain ⟨g, τ, h1, h2, -, h4, -⟩ := hEdesc e he
      exact ⟨g, τ, h1, h2, h4⟩
  have hEfix : ∀ a' ∈ Ab, ∀ e ∈ E, a' e = e := by
    intro a' ha'
    obtain ⟨t', ht'⟩ := hdiag a' ha'
    obtain ⟨σ', -, hσ'⟩ := ActsU.of_actsDiagU ht'
    exact fix_of_torus hσ' fun e he => by
      obtain ⟨g, τ, h1, h2, -⟩ := hEdesc e he
      exact ⟨g, τ, h1, h2⟩
  have hEnorm : E ≤ Subgroup.normalizer (Usw : Set Lb) := by
    intro e he
    obtain ⟨g, τ, h1, h2, -, -, h5⟩ := hEdesc e he
    refine hUswN e ⟨g, τ, h1, h2, h5 s hsS t htS ?_⟩
    simp [hrdef, hst]
  have hEsmall : Nat.card E < 3 ^ 3 :=
    hsmall E hEab hElayer hEfix (Or.inr ⟨Usw, hUsw1, hUsw2, hUswA, hEnorm⟩)
  have hSle : S.card ≤ 4 := by
    by_contra hc
    push Not at hc
    have h1 : 3 ^ 3 ≤ 3 ^ ((S.image r).card - 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hSge : 4 ≤ S.card := by
    rcases hbigS with h | ⟨h2, -⟩
    · exact h
    · omega
  have hS4 : S.card = 4 := le_antisymm hSle hSge
  have hT'card : ((S.erase s).erase t).card = 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hst.symm, htS⟩),
      Finset.card_erase_of_mem hsS, hS4]
  obtain ⟨c, e, hce, hT'⟩ := Finset.card_eq_two.mp hT'card
  have hcT : c ∈ (S.erase s).erase t := by rw [hT']; simp
  have heT : e ∈ (S.erase s).erase t := by rw [hT']; simp
  have hcS : c ∈ S := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hcT)
  have heS : e ∈ S := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase heT)
  have htc : t ≠ c := (Finset.ne_of_mem_erase hcT).symm
  have hte : t ≠ e := (Finset.ne_of_mem_erase heT).symm
  have hsc : s ≠ c := (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hcT)).symm
  have hse : s ≠ e := (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase heT)).symm
  obtain ⟨g, τ, hg, hτp, hτoff, hτst, hncomm⟩ :=
    exists_witness (φ := φ) hM hp hpq hn hst hsc hse htc hte hce
  have hgS : g ∈ blockSU S := by
    change IsBlockOn S ((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)
    rw [hg]
    refine StdSubRestU.isBlockOn_diagHom fun k hk => hτoff k ?_ ?_ ?_
    · exact fun h => hk (h ▸ hsS)
    · exact fun h => hk (h ▸ htS)
    · exact fun h => hk (h ▸ hcS)
  refine ⟨Usw, hUsw1, hUsw2, hlayer ▸ hUswS S hsS htS, hUswA, φ g, ?_, ?_, ?_, ?_,
    φ (IOneU.swapSU hM.field c e), ?_, fun hcomm => hncomm hcomm.symm⟩
  · rw [hlayer]
    exact ⟨g, hgS, rfl⟩
  · have h1 : g ^ 3 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, hg, ← map_pow]
      have : τ ^ 3 = 1 := funext fun k => by simpa using hτp k
      rw [this, map_one]
      rfl
    rw [← map_pow, h1, map_one]
  · intro a' ha'
    obtain ⟨t', ht'⟩ := hdiag a' ha'
    exact ht'.fix_of_diagonal g (v := fun k => ((τ k : Kˣ) : K))
      (by rw [hg, coe_diagHom])
  · exact hUswN (φ g) ⟨g, τ, rfl, hg, hτst⟩
  · rw [hlayer]
    exact ⟨IOneU.swapSU hM.field c e, isBlockOn_permGL_swap hcS heS, rfl⟩

theorem ggStdSubTwoTorusNormSmallR_sixTwo
    {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ 1) ^ 2) :
    GGStdSubTwoTorusNormSmallR 3 3 (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
        (LargeEvenGUSet (Fin 6) K (2 ^ 1))) := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hα a ha ha1 hEcomp hcentA hsmall _hrule
  classical
  obtain ⟨ψb, hψbmk, hψbs, hkerb, hperfb, hoddb, hAb, hcardAb, hAIb⟩ :=
    six_package hK hψ hker hperf hA hAI
  set Ab := A.map (qAutHom L') with hAbdef
  obtain ⟨φ, hM, hdiag⟩ := exists_diagModel_frame_odd hK hψbs hkerb hperfb hoddb hAb hAIb
    (by rw [hcardAb]; simpa using h3) (normTwoR_down hψbmk hα)
  have hc := qAutHom_compat a
  have hZR : Subgroup.center (UnitaryR K 1 6) = ⊥ := six_center_eq_bot hK
  have hAp : ∀ g ∈ Ab, g ^ 3 = 1 := hAb.2
  obtain ⟨U₀, hU1, hU2, hAU⟩ := normTwoR_down hψbmk hα
  obtain ⟨s, t, hst, hpair⟩ := exists_pair hM hK (by norm_num) Nat.prime_three (by norm_num)
    hψbs hkerb hZR hAp hdiag hU1 hU2 hAU
  have hab : qAutHom L' a ∈ Ab := ⟨a, ha, rfl⟩
  have hab1 : qAutHom L' a ≠ 1 := fun h => ha1 (qAutHom_injective hperf (by rw [h, map_one]))
  have hEcompb := isComponentOf_layer_down qmk_surjective qmk_ker_le_center hc hEcomp
  exact concl_up hperf hA ha
    (concl_downstairs hK hM hdiag hst hpair hab hab1 hEcompb (smallHyp_down hperf hA ha hsmall))

end CFSG.StandardType.USixTwo

end
