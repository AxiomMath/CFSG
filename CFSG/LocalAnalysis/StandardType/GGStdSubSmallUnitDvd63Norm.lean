module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallUnitDvdNorm
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRule
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallUnitDvd63Model

public section

namespace CFSG.StandardType.SmallU

open scoped commutatorElement

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.SectionRank.OddCover CFSG.StandardType.LineU CFSG.StandardType.UnitTB CFSG.Assembly
  CFSG.RankThree.Classical CFSG.RankThree.Classical2 CFSG.StandardType.TableBUE

theorem ggStdSubTwoTorusNormSmallR_unitDvd63
    {K : Type} [Field K] [Finite K]
    {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) (hn2 : 2 ≤ n) (hpq : 3 ∣ 2 ^ n + 1) :
    GGStdSubTwoTorusNormSmallR 3 3 (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ n)))
        (LargeEvenGUSet (Fin 6) K (2 ^ n))) := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hα a ha ha1 hEcomp hcentA hsmall _
  obtain ⟨φ, hM', hdiag⟩ := Line63.exists_diagModel_frame hK hn2 hpq hψ hker hperf hA hAI hr hα
  have hM : Model φ := hM'
  have hn : 1 ≤ n := by omega
  have hp : Nat.Prime 3 := Nat.prime_three
  have hpK := dvd_card_sub_one hK hpq
  have hAp : ∀ g ∈ A, g ^ 3 = 1 := hA.2
  have hdq : ((6 : ℕ), 2 ^ n) ≠ (3, 2) := fun he => by
    have := congrArg Prod.fst he
    simp only at this
    omega
  have hd3 : 3 ≤ 6 := by norm_num
  have hZR : Subgroup.center (LargeEvenProj (unitarySU 2 n K 6)) = ⊥ :=
    center_proj_eq_bot hK hd3 hdq
  obtain ⟨U₀, hU1, hU2, hAU⟩ := hα
  obtain ⟨s, t, hst, hpair⟩ := exists_pair hM hK (by norm_num) hp hpq hψ hker hZR hAp hdiag
    hU1 hU2 hAU
  obtain ⟨Usw, hUsw1, hUsw2, hUswA, hUswN, hUswS⟩ := exists_swap_group hM hst hd3 hdiag hpair
  obtain ⟨t₀, ht₀⟩ := hdiag a ha
  obtain ⟨σ, -, hσ⟩ := ActsU.of_actsDiagU ht₀
  have hts : σ t = σ s := (hpair a ha σ hσ).symm
  have hS := cls_isCls σ s
  have hsS : s ∈ cls σ s := mem_cls.mpr rfl
  have htS : t ∈ cls σ s := mem_cls.mpr hts
  set S := cls σ s with hSdef
  have hSd : ∃ k₀, k₀ ∉ S := by
    by_contra hall
    push Not at hall
    exact ha1 (hσ.eq_one_of_const hM s fun i j => by
      rw [mem_cls.mp (hall i), mem_cls.mp (hall j)])
  obtain ⟨k₀, hk₀⟩ := hSd
  have hSc : 2 ≤ S.card := by
    have h1 := Finset.card_le_card (show ({s, t} : Finset (Fin 6)) ⊆ S from fun k hk => by
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact hsS
      · rw [Finset.mem_singleton.mp hk]
        exact htS)
    rwa [Finset.card_pair hst] at h1
  have hbigS : BigOK n S := Or.inr ⟨hn2, hSc⟩
  have hlayer : LargeEvenLayer (ggFix a) = (blockSU S).map φ :=
    layer_eq_block hM hσ hS (isQuasisimple_block hM hbigS) hEcomp
  have hcardA := card_A_le_of_class (T := {s, t}) hM hd3 hp hpK hA hdiag ha hσ hS hbigS hEcomp
    hcentA (s₀ := s)
    (fun k hk => by
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact hsS
      · rw [Finset.mem_singleton.mp hk]
        exact htS)
    (fun a' ha' τ hτ k hk => by
      rcases Finset.mem_insert.mp hk with rfl | hk
      · rfl
      · rw [Finset.mem_singleton.mp hk]
        exact (hpair a' ha' τ hτ).symm)
  rw [Finset.card_pair hst] at hcardA
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
  have hElayer : E ≤ LargeEvenLayer (ggFix a) := by
    rw [hlayer]
    exact torus_le_block fun e he => by
      obtain ⟨g, τ, h1, h2, -, h4, -⟩ := hEdesc e he
      exact ⟨g, τ, h1, h2, h4⟩
  have hEfix : ∀ a' ∈ A, ∀ e ∈ E, a' e = e := by
    intro a' ha'
    obtain ⟨t', ht'⟩ := hdiag a' ha'
    obtain ⟨σ', -, hσ'⟩ := ActsU.of_actsDiagU ht'
    exact fix_of_torus hσ' fun e he => by
      obtain ⟨g, τ, h1, h2, -⟩ := hEdesc e he
      exact ⟨g, τ, h1, h2⟩
  have hEnorm : E ≤ Subgroup.normalizer (Usw : Set L') := by
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
    by_contra hc
    push Not at hc
    have h1 : 3 ^ (S.card - 2) ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : Nat.card A ≤ 3 * 3 := by
      calc Nat.card A ≤ 3 * 3 ^ (S.card - 2) := hcardA
        _ ≤ 3 * 3 ^ 1 := Nat.mul_le_mul_left 3 h1
        _ = 3 * 3 := by norm_num
    have h3' : 27 ≤ Nat.card A := by simpa using h3
    omega
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
  refine ⟨Usw, hUsw1, hUsw2, hlayer ▸ hUswS S hsS htS, hUswA, φ g, ?_, ?_, ?_, ?_, φ
    (IOneU.swapSU hM.field c e), ?_, fun hcomm => hncomm hcomm.symm⟩
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

end CFSG.StandardType.SmallU

end
