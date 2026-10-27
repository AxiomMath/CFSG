module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFactsNineteenTwenty
public import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Adapters.StatedPSLTwoSeven
public import CFSG.Quasithin.Background.F420Orders
public import CFSG.Quasithin.H13.GoldschmidtC137SQSimp
public import CFSG.LocalAnalysis.AGLEmbedding.BlockAltSevenPLAux
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NormalizedBySimple
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113CentInner

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
open CFSG.ComponentClassification.OuterAutomorphisms

private theorem factorization_168_two : (168 : ℕ).factorization 2 = 3 := by
  rw [show (168 : ℕ) = 2 ^ 3 * 21 by norm_num]
  rw [Nat.factorization_mul (by norm_num) (by norm_num)]
  rw [Nat.factorization_pow]
  simp [Nat.prime_two.factorization_self]
  exact Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ (21 : ℕ))

theorem k_19_20_oddAut_holds : K_19_20_oddAut := by
  intro X _ _ Y hY α hodd hαY
  rcases hY with ⟨hLie, hPar⟩ | ⟨hAlt, hIndex⟩
  ·
    have hX : CFSG.Open.StatedClassicalModel X .PSL 3 2 1 :=
      hLie.statedClassicalModel (by decide)
    have hcardX : Nat.card X = 168 :=
      CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_two hX
    have hsimple : IsSimpleGroup X :=
      (CFSG.LieType.Simplicity.fam_PSL_simplicity X 3 2 1 hX).2
    have : IsSimpleGroup X := hsimple
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨hparab, hne, S₀, hS₀⟩ := hPar
    obtain ⟨S, hS⟩ := hparab
    have hS8 : Nat.card (S : Subgroup X) = 8 := by
      rw [Sylow.card_eq_multiplicity, hcardX, factorization_168_two]
      norm_num
    have hSleY : (S : Subgroup X) ≤ Y := Subgroup.le_normalizer.trans hS
    have h8dvd : 8 ∣ Nat.card Y := by
      rw [← hS8]
      exact Subgroup.card_dvd_of_le hSleY
    have hgt8 : 8 < Nat.card Y := by
      have hNle : (S₀ : Subgroup X) ≤ Subgroup.normalizer (S₀ : Set X) :=
        Subgroup.le_normalizer
      have hlt : Nat.card (Subgroup.normalizer (S₀ : Set X)) < Nat.card Y :=
        Subgroup.card_lt_of_lt hS₀
      have h8N : 8 ≤ Nat.card (Subgroup.normalizer (S₀ : Set X)) := by
        have hS₀8 : Nat.card (S₀ : Subgroup X) = 8 := by
          rw [Sylow.card_eq_multiplicity, hcardX, factorization_168_two]
          norm_num
        rw [← hS₀8]
        exact Subgroup.card_le_of_le hNle
      omega
    have hYdvd : Nat.card Y ∣ 168 := by
      rw [← hcardX]
      exact Subgroup.card_subgroup_dvd_card Y
    have hYcard : Nat.card Y = 24 := by
      obtain ⟨c, hc⟩ := h8dvd
      have hc21 : c ∣ 21 := by
        have h : 8 * c ∣ 8 * 21 := by
          rw [← hc]
          simpa [show (168 : ℕ) = 8 * 21 by norm_num] using hYdvd
        exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h
      have hmem : c ∈ Nat.divisors 21 := Nat.mem_divisors.mpr ⟨hc21, by norm_num⟩
      have hdiv : Nat.divisors 21 = {1, 3, 7, 21} := by decide
      rw [hdiv] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h1 | h3 | h7 | h21
      · rw [h1, mul_one] at hc
        omega
      · rw [h3] at hc
        omega
      · exfalso
        rw [h7] at hc
        norm_num at hc
        have hidx : Y.index = 3 := by
          have hmul := Subgroup.index_mul_card Y
          rw [hcardX, hc] at hmul
          omega
        have hdvd : Nat.card X ∣ (Y.index).factorial :=
          CFSG.Quasithin.H13.U3.GC137.SQ.card_dvd_factorial_index hne
        rw [hcardX, hidx] at hdvd
        norm_num at hdvd
      · exfalso
        rw [h21] at hc
        norm_num at hc
        have htop : Y = ⊤ :=
          Subgroup.eq_top_of_le_card (H := Y) (by rw [hcardX, hc])
        exact hne htop
    have hNcard : Nat.card (Subgroup.normalizer (Y : Set X)) = 24 := by
      have hNmul : Nat.card (Subgroup.normalizer (Y : Set X)) ∣ 168 := by
        rw [← hcardX]
        exact Subgroup.card_subgroup_dvd_card _
      have h24N : 24 ∣ Nat.card (Subgroup.normalizer (Y : Set X)) := by
        rw [← hYcard]
        exact Subgroup.card_dvd_of_le (Subgroup.le_normalizer)
      obtain ⟨d, hd⟩ := h24N
      have hd7 : d ∣ 7 := by
        have h : 24 * d ∣ 24 * 7 := by
          rw [← hd]
          simpa [show (168 : ℕ) = 24 * 7 by norm_num] using hNmul
        exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h
      have hmem : d ∈ Nat.divisors 7 := Nat.mem_divisors.mpr ⟨hd7, by norm_num⟩
      have hdiv : Nat.divisors 7 = {1, 7} := by decide
      rw [hdiv] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h1 | h7
      · rw [h1, mul_one] at hd
        exact hd
      · exfalso
        rw [h7] at hd
        norm_num at hd
        have htop : Subgroup.normalizer (Y : Set X) = ⊤ :=
          Subgroup.eq_top_of_le_card (H := Subgroup.normalizer (Y : Set X))
            (by rw [hcardX, hd])
        have hYnorm : Y.Normal := Subgroup.normalizer_eq_top_iff.mp htop
        have : Y.Normal := hYnorm
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Y with hb | ht
        · rw [hb, Subgroup.card_bot] at hYcard
          omega
        · exact hne ht
    have hNY : Subgroup.normalizer (Y : Set X) = Y :=
      (Subgroup.eq_of_le_of_card_ge (H := Y) (K := Subgroup.normalizer (Y : Set X))
        (Subgroup.le_normalizer) (by rw [hNcard, hYcard])).symm
    have hOut : Nat.card (Outer X) ∣ 2 := by
      have h27 : CFSG.Open.StatedClassicalModel X .PSL 2 7 1 :=
        CFSG.Open.StatedAPI.statedClassicalModel_psl_two_seven_of_psl_three_two hX
      obtain ⟨-, K, hField, hFinite, hK, ⟨eK⟩⟩ := h27
      have hK' : Nat.card K = 7 ^ 1 := hK
      have hiso : Nonempty (X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :=
        ⟨eK.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj
          2 K).symm⟩
      have h := (CFSG.LocalAnalysis.ComponentInitial.linear_two_outer_order_divisor
        (p := 7) (f := 1) Nat.prime_seven K hK').2 X hiso
      norm_num at h
      exact h
    have hInner : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner X := by
      have hoddq : Odd (orderOf (QuotientGroup.mk α : Outer X)) := by
        exact Odd.of_dvd_nat hodd
          (orderOf_map_dvd
            (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner X)) α)
      have hdvd : orderOf (QuotientGroup.mk α : Outer X) ∣ 2 :=
        (orderOf_dvd_natCard (QuotientGroup.mk α : Outer X)).trans hOut
      have hone : orderOf (QuotientGroup.mk α : Outer X) = 1 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
        · exact h1
        · exfalso
          rw [h2] at hoddq
          exact (by norm_num : ¬ Odd 2) hoddq
      exact (QuotientGroup.eq_one_iff α).mp (orderOf_eq_one_iff.mp hone)
    obtain ⟨g, hg⟩ := hInner
    have hgN : g ∈ Subgroup.normalizer (Y : Set X) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      rw [hg]
      exact hαY
    have hgY : g ∈ Y := hNY ▸ hgN
    have hZ : Subgroup.center X = ⊥ := CFSG.Quasithin.F420.center_eq_bot_of_statedPSL hX
    have hconj_inj : Function.Injective (MulAut.conj : X →* MulAut X) :=
      CFSG.QuasithinUnique.Bridge.conj_injective_of_center_eq_bot hZ
    have hoddg : Odd (orderOf g) := by
      have h1 : orderOf (MulAut.conj g) = orderOf g := orderOf_injective _ hconj_inj g
      rw [← h1, hg]
      exact hodd
    have hgdvd : orderOf g ∣ 24 := by
      have h1 : orderOf (⟨g, hgY⟩ : ↥Y) ∣ Nat.card ↥Y := orderOf_dvd_natCard _
      have h2 : orderOf (⟨g, hgY⟩ : ↥Y) = orderOf g := (Subgroup.orderOf_coe _).symm
      rw [h2, hYcard] at h1
      exact h1
    have h3dvd : orderOf g ∣ 3 := by
      have hcop : Nat.Coprime (orderOf g) 8 := by
        simpa using hoddg.coprime_two_right.pow_right 3
      have hdvd : orderOf g ∣ 8 * 3 := by
        simpa [show (24 : ℕ) = 8 * 3 by norm_num] using hgdvd
      exact hcop.dvd_of_dvd_mul_left hdvd
    have hg3 : g ^ 3 = 1 := (orderOf_dvd_iff_pow_eq_one).mp h3dvd
    have hconj3 : (MulAut.conj g) ^ 3 = 1 := by
      rw [← map_pow (MulAut.conj : X →* MulAut X) g 3, hg3, map_one]
    rw [← hg]
    exact hconj3
  ·
    obtain ⟨e⟩ := hAlt
    set Y' : Subgroup (alternatingGroup (Fin 7)) := Y.map e.toMonoidHom with hY'def
    have hcardA7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
      rw [nat_card_alternatingGroup, Nat.card_fin]
      decide
    have hcardY' : Nat.card Y' = Nat.card Y := Subgroup.card_map_of_injective e.injective
    have hcardX : Nat.card X = 2520 := (Nat.card_congr e.toEquiv).trans hcardA7
    have hYcard : Nat.card Y = 72 := by
      have hmul := Subgroup.index_mul_card Y
      rw [hIndex, hcardX] at hmul
      omega
    have hY'card : Nat.card Y' = 72 := by rw [hcardY', hYcard]
    have hY'index : Y'.index = 35 := by
      have hmul := Subgroup.index_mul_card Y'
      rw [hY'card, hcardA7] at hmul
      omega
    let β : MulAut (alternatingGroup (Fin 7)) := MulAut.congr e α
    have hβodd : Odd (orderOf β) := by
      have h := (MulAut.congr e).orderOf_eq α
      exact (show Odd (orderOf β) from h ▸ hodd)
    have hβY : Y'.map β.toMonoidHom = Y' := by
      have hcomp : β.toMonoidHom.comp e.toMonoidHom = e.toMonoidHom.comp α.toMonoidHom := by
        ext x
        simp [β, MulAut.congr_apply]
      rw [hY'def, Subgroup.map_map, hcomp, ← Subgroup.map_map, hαY]
    obtain ⟨g, hg⟩ :=
      CFSG.GorensteinWalter.gw_lemma_3_2_ix_a7_no_outer_automorphisms_odd_order β hβodd
    have hgN : g ∈ Subgroup.normalizer (Y' : Set (alternatingGroup (Fin 7))) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      rw [← hg]
      exact hβY
    have hNoOdd : ∀ p : ℕ, p.Prime → (p = 5 ∨ p = 7) →
        ¬ p ∣ Nat.card (Subgroup.normalizer (Y' : Set (alternatingGroup (Fin 7)))) := by
      intro p hp hp57 hpdvd
      have : Fact p.Prime := ⟨hp⟩
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' p hpdvd
      have hxord' : orderOf (x : alternatingGroup (Fin 7)) = p :=
        (Subgroup.orderOf_coe x).trans hxord
      let G : Subgroup (alternatingGroup (Fin 7)) :=
        Subgroup.zpowers (x : alternatingGroup (Fin 7))
      have hGN : G ≤ Subgroup.normalizer (Y' : Set (alternatingGroup (Fin 7))) :=
        Subgroup.zpowers_le.mpr x.2
      let _ : MulDistribMulAction ↥G ↥Y' :=
        MulDistribMulAction.compHom ↥Y'
          (Y'.normalizerMonoidHom.comp (Subgroup.inclusion hGN))
      have hGp : IsPGroup p ↥G :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxord', pow_one])
      have hnotp : ¬ p ∣ Nat.card (Sylow 2 ↥Y') := by
        intro h
        have h1 : Nat.card (Sylow 2 ↥Y') ∣ (default : Sylow 2 ↥Y').index :=
          Sylow.card_dvd_index default
        have h2 : (default : Sylow 2 ↥Y').index ∣ Nat.card ↥Y' := Subgroup.index_dvd_card _
        rw [hY'card] at h2
        rcases hp57 with rfl | rfl
        · exact absurd (h.trans (h1.trans h2)) (by norm_num)
        · exact absurd (h.trans (h1.trans h2)) (by norm_num)
      obtain ⟨P, hP⟩ := hGp.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 2 ↥Y') hnotp
      have hPx : ∀ q ∈ (P : Subgroup ↥Y'),
          (x : alternatingGroup (Fin 7)) * (q : alternatingGroup (Fin 7)) *
            (x : alternatingGroup (Fin 7))⁻¹ ∈ (P : Subgroup ↥Y').map Y'.subtype := by
        intro q hq
        have h1 := Subgroup.smul_mem_pointwise_smul q
          (⟨(x : alternatingGroup (Fin 7)), Subgroup.mem_zpowers _⟩ : ↥G)
          (P : Subgroup ↥Y') hq
        rw [← Sylow.pointwise_smul_def,
          hP ⟨(x : alternatingGroup (Fin 7)), Subgroup.mem_zpowers _⟩] at h1
        exact ⟨_, h1, rfl⟩
      set T : Subgroup (alternatingGroup (Fin 7)) :=
        (P : Subgroup ↥Y').map Y'.subtype with hTdef
      have hT2 : IsPGroup 2 T := (P.isPGroup').map Y'.subtype
      have hmap_le : T.map (MulAut.conj (x : alternatingGroup (Fin 7))).toMonoidHom ≤ T := by
        rintro _ ⟨y, hy, rfl⟩
        obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hy
        simpa [MulAut.conj_apply] using hPx q hq
      have hcardmap :
          Nat.card (T.map (MulAut.conj (x : alternatingGroup (Fin 7))).toMonoidHom) =
            Nat.card T := Subgroup.card_map_of_injective (MulAut.conj _).injective
      have hmap : T.map (MulAut.conj (x : alternatingGroup (Fin 7))).toMonoidHom = T :=
        Subgroup.eq_of_le_of_card_ge hmap_le (by rw [hcardmap])
      have hxT : (x : alternatingGroup (Fin 7)) ∈
          Subgroup.normalizer (T : Set (alternatingGroup (Fin 7))) :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap
      have hTne : T ≠ ⊥ := by
        have hPne : (P : Subgroup ↥Y') ≠ ⊥ :=
          Sylow.ne_bot_of_dvd_card P (by rw [hY'card]; norm_num)
        have hcardT : Nat.card T = Nat.card (P : Subgroup ↥Y') :=
          Subgroup.card_map_of_injective Y'.subtype_injective
        intro hbot
        apply hPne
        apply (Subgroup.eq_bot_iff_card _).mpr
        rw [← hcardT, hbot, Subgroup.card_bot]
      have hTbot : T = ⊥ := by
        rcases hp57 with rfl | rfl
        · exact CFSG.AGLEmbedding.BlockAltSevenPL.eq_bot_of_orderOf_eq_five hT2 hxord' hxT
        · exact CFSG.AGLEmbedding.BlockAltSevenPL.eq_bot_of_orderOf_eq_seven hT2 hxord' hxT
      exact hTne hTbot
    have hNo5 : ¬ 5 ∣ Nat.card (Subgroup.normalizer (Y' : Set (alternatingGroup (Fin 7)))) :=
      hNoOdd 5 Nat.prime_five (Or.inl rfl)
    have hNo7 : ¬ 7 ∣ Nat.card (Subgroup.normalizer (Y' : Set (alternatingGroup (Fin 7)))) :=
      hNoOdd 7 Nat.prime_seven (Or.inr rfl)
    have hNY : Subgroup.normalizer (Y' : Set (alternatingGroup (Fin 7))) = Y' := by
      have hNdiv : Nat.card (Subgroup.normalizer (Y' : Set (alternatingGroup (Fin 7)))) ∣ 2520 := by
        rw [← hcardA7]
        exact Subgroup.card_subgroup_dvd_card _
      have h72N : 72 ∣ Nat.card
          (Subgroup.normalizer (Y' : Set (alternatingGroup (Fin 7)))) := by
        rw [← hY'card]
        exact Subgroup.card_dvd_of_le (Subgroup.le_normalizer)
      have hN72 : Nat.card (Subgroup.normalizer (Y' : Set (alternatingGroup (Fin 7)))) ∣ 72 := by
        have hcop5 : Nat.Coprime
            (Nat.card (Subgroup.normalizer (Y' : Set (alternatingGroup (Fin 7))))) 5 :=
          ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mpr hNo5).symm
        have hcop7 : Nat.Coprime
            (Nat.card (Subgroup.normalizer (Y' : Set (alternatingGroup (Fin 7))))) 7 :=
          ((Nat.Prime.coprime_iff_not_dvd Nat.prime_seven).mpr hNo7).symm
        have hcop35 : Nat.Coprime
            (Nat.card (Subgroup.normalizer (Y' : Set (alternatingGroup (Fin 7))))) 35 := by
          rw [show (35 : ℕ) = 5 * 7 by norm_num]
          exact hcop5.mul_right hcop7
        have hdvd : Nat.card (Subgroup.normalizer (Y' : Set (alternatingGroup (Fin 7)))) ∣
            72 * 35 := by
          rw [show (72 * 35 : ℕ) = 2520 by norm_num]
          exact hNdiv
        exact hcop35.dvd_of_dvd_mul_right hdvd
      have hcardN : Nat.card
          (Subgroup.normalizer (Y' : Set (alternatingGroup (Fin 7)))) = 72 := by
        exact (Nat.dvd_antisymm h72N hN72).symm
      exact (Subgroup.eq_of_le_of_card_ge (H := Y')
        (K := Subgroup.normalizer (Y' : Set (alternatingGroup (Fin 7))))
        (Subgroup.le_normalizer) (by rw [hcardN, hY'card])).symm
    have hgY' : g ∈ Y' := hNY ▸ hgN
    have hZ : Subgroup.center (alternatingGroup (Fin 7)) = ⊥ :=
      alternatingGroup.center_eq_bot (by norm_num)
    have hconj_inj :
        Function.Injective (MulAut.conj :
          alternatingGroup (Fin 7) →* MulAut (alternatingGroup (Fin 7))) :=
      CFSG.QuasithinUnique.Bridge.conj_injective_of_center_eq_bot hZ
    have hoddg : Odd (orderOf g) := by
      have h1 : orderOf (MulAut.conj g) = orderOf g := orderOf_injective _ hconj_inj g
      rw [← hg] at h1
      rw [← h1]
      exact hβodd
    have hgdvd : orderOf g ∣ 72 := by
      have h1 : orderOf (⟨g, hgY'⟩ : ↥Y') ∣ Nat.card ↥Y' := orderOf_dvd_natCard _
      have h2 : orderOf (⟨g, hgY'⟩ : ↥Y') = orderOf g := (Subgroup.orderOf_coe _).symm
      rw [h2, hY'card] at h1
      exact h1
    have hg9 : orderOf g ∣ 9 := by
      have hcop : Nat.Coprime (orderOf g) 8 := by
        simpa using hoddg.coprime_two_right.pow_right 3
      have hdvd : orderOf g ∣ 8 * 9 := by
        simpa [show (72 : ℕ) = 8 * 9 by norm_num] using hgdvd
      exact hcop.dvd_of_dvd_mul_left hdvd
    have hne9 : orderOf g ≠ 9 := by
      intro h9
      have hcard7 : Nat.card (Fin 7) ≤ 7 := by simp
      have hcoe : orderOf (g : Equiv.Perm (Fin 7)) = orderOf g := Subgroup.orderOf_coe g
      have hperm : orderOf (g : Equiv.Perm (Fin 7)) = 9 := by rw [hcoe, h9]
      exact CFSG.SignalizerFunctorTheorem.CatalogBridge.not_orderOf_eq_nine hcard7
        (g : Equiv.Perm (Fin 7)) hperm
    have h3dvd : orderOf g ∣ 3 := by
      have hmem : orderOf g ∈ Nat.divisors 9 := Nat.mem_divisors.mpr ⟨hg9, by norm_num⟩
      have hdiv : Nat.divisors 9 = {1, 3, 9} := by decide
      rw [hdiv] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h1 | h3 | h9'
      · rw [h1]
        norm_num
      · rw [h3]
      · exact absurd h9' hne9
    have hg3 : g ^ 3 = 1 := (orderOf_dvd_iff_pow_eq_one).mp h3dvd
    have hβ3 : β ^ 3 = 1 := by
      rw [hg]
      rw [← map_pow (MulAut.conj :
        alternatingGroup (Fin 7) →* MulAut (alternatingGroup (Fin 7))) g 3, hg3, map_one]
    have hα3 : α ^ 3 = 1 := by
      apply (MulAut.congr e).injective
      rw [map_pow, map_one]
      exact hβ3
    exact hα3

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
