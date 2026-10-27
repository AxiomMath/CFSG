module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallUnitDvdSwap

public section

namespace CFSG.StandardType.SmallU

open scoped commutatorElement

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.SectionRank.OddCover CFSG.StandardType.LineU CFSG.StandardType.UnitTB CFSG.Assembly
  CFSG.RankThree.Classical CFSG.RankThree.Classical2 CFSG.StandardType.TableBUE

variable {K : Type} [Field K] [Finite K] {n d p : ℕ}

theorem ggStdSubTwoTorusNormSmall_unitDvd
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 5 ≤ d) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hpd : p ∣ d) (hnd : ¬ (d = 6 ∧ p = 3)) :
    GGStdSubTwoTorusNormSmall p (d - 3) (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hα a ha ha1 hEcomp hcentA hsmall
  obtain ⟨φ, hM, hdiag⟩ := exists_model hK hn hd hp hpq hpd hnd hψ hker hperf hA hAI hr h3
  have hpK := dvd_card_sub_one hK hpq
  have hd3 : 3 ≤ d := by omega
  have hAp : ∀ g ∈ A, g ^ p = 1 := hA.2
  have hdq : (d, 2 ^ n) ≠ (3, 2) := fun he => by
    have := congrArg Prod.fst he
    simp only at this
    omega
  have hZR : Subgroup.center (LargeEvenProj (unitarySU 2 n K d)) = ⊥ :=
    center_proj_eq_bot hK hd3 hdq
  obtain ⟨U₀, hU1, hU2, hAU⟩ := hα
  obtain ⟨s, t, hst, hpair⟩ :=
    exists_pair hM hK (by omega) hp hpq hψ hker hZR hAp hdiag hU1 hU2 hAU
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
    have h1 := Finset.card_le_card (show ({s, t} : Finset (Fin d)) ⊆ S from fun k hk => by
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact hsS
      · rw [Finset.mem_singleton.mp hk]
        exact htS)
    rwa [Finset.card_pair hst] at h1
  by_cases hbigS : BigOK n S
  ·
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
    set r : Fin d → Fin d := fun k => if k = t then s else k with hrdef
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
    have hEab : CFSG.Open.IsElemAbelian p E := isElemAbelian_torus fun e he => by
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
    have hEsmall : Nat.card E < p ^ 3 :=
      hsmall E hEab hElayer hEfix (Or.inr ⟨Usw, hUsw1, hUsw2, hUswA, hEnorm⟩)
    have hSle : S.card ≤ 4 := by
      by_contra hc
      push Not at hc
      have := Nat.pow_le_pow_right hp.pos (show 3 ≤ (S.image r).card - 1 by omega)
      omega
    have hSge : 4 ≤ S.card := by
      by_contra hc
      push Not at hc
      have h1 : p * p ^ (S.card - 2) ≤ p * p := by
        have := Nat.pow_le_pow_right hp.pos (show S.card - 2 ≤ 1 by omega)
        simpa using Nat.mul_le_mul_left p this
      have h2 : p * p < p ^ 3 := by
        have := Nat.pow_lt_pow_right hp.one_lt (show 2 < 3 by norm_num)
        simpa [sq] using this
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
      change IsBlockOn S ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
      rw [hg]
      refine StdSubRestU.isBlockOn_diagHom fun k hk => hτoff k ?_ ?_ ?_
      · exact fun h => hk (h ▸ hsS)
      · exact fun h => hk (h ▸ htS)
      · exact fun h => hk (h ▸ hcS)
    refine ⟨Usw, hUsw1, hUsw2, hlayer ▸ hUswS S hsS htS, hUswA, φ g, ?_, ?_, ?_, ?_, φ
      (IOneU.swapSU hM.field c e), ?_, fun hcomm => hncomm hcomm.symm⟩
    · rw [hlayer]
      exact ⟨g, hgS, rfl⟩
    · have h1 : g ^ p = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, hg, ← map_pow]
        have : τ ^ p = 1 := funext fun k => by simpa using hτp k
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
  ·
    exfalso
    have hn1 : n = 1 := by
      by_contra hn1
      exact hbigS (Or.inr ⟨by omega, hSc⟩)
    have hS3 : S.card ≤ 3 := by
      by_contra hc
      exact hbigS (Or.inl (by omega))
    obtain ⟨i₁, hbig₁⟩ := exists_bigOK_cls hM (by omega) hn hσ hEcomp
    have hS'4 : 4 ≤ (cls σ i₁).card := by
      rcases hbig₁ with h | ⟨h, -⟩
      · exact h
      · omega
    have hS' := cls_isCls σ i₁
    set S' := cls σ i₁ with hS'def
    have hdisj : ∀ x ∈ S, x ∉ S' := by
      intro x hx hx'
      have h1 : σ x = σ s := mem_cls.mp hx
      have h2 : σ x = σ i₁ := mem_cls.mp hx'
      have hEq : S = S' := by
        ext k
        rw [hSdef, hS'def, mem_cls, mem_cls, ← h2, h1]
      rw [← hEq] at hS'4
      omega
    obtain ⟨E, hEcard, hEdesc⟩ := exists_torus hM hK hp hpq (hdisj s hsS) id (fun k hk => hk)
    rw [Finset.image_id] at hEcard
    have hEab : CFSG.Open.IsElemAbelian p E := isElemAbelian_torus fun e he => by
      obtain ⟨g, τ, h1, h2, h3, -⟩ := hEdesc e he
      exact ⟨g, τ, h1, h2, h3⟩
    have hKc := isComponentOf_block hM hσ hS' (isQuasisimple_block hM (Or.inl hS'4))
    have hKE : (blockSU S').map φ ≤ LargeEvenLayer (ggFix a) := le_sSup hKc
    have hElayer : E ≤ LargeEvenLayer (ggFix a) := by
      refine le_trans ?_ hKE
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
      obtain ⟨g, τ, h1, h2, -, h4, -⟩ := hEdesc e he
      refine hUswN e ⟨g, τ, h1, h2, ?_⟩
      rw [h4 s (hdisj s hsS), h4 t (hdisj t htS)]
    have hEsmall : Nat.card E < p ^ 3 :=
      hsmall E hEab hElayer hEfix (Or.inr ⟨Usw, hUsw1, hUsw2, hUswA, hEnorm⟩)
    have := Nat.pow_le_pow_right hp.pos (show 3 ≤ S'.card - 1 by omega)
    omega

end CFSG.StandardType.SmallU

end
