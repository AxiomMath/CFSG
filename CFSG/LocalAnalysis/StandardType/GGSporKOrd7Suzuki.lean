module

public import CFSG.LocalAnalysis.StandardType.GGSporKOrd7Defs
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldSuzuki

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.Open

open CFSG.ComponentClassification.OuterAutomorphisms in
private theorem lr2osz_outer_card_dvd_of_inner_sup_eq_top
    {S Q : Type} [Group S] [Group Q] (φ : Q →* MulAut S)
    (hsup : inner S ⊔ φ.range = ⊤) :
    Nat.card (Outer S) ∣ Nat.card Q := by
  rw [← Subgroup.index_eq_card (inner S)]
  calc (inner S).index = (inner S).relIndex (inner S ⊔ φ.range) := by
        rw [hsup, Subgroup.relIndex_top_right]
    _ = (inner S).relIndex φ.range := Subgroup.relIndex_sup_left φ.range (inner S)
    _ ∣ Nat.card φ.range := Subgroup.relIndex_dvd_card (inner S) φ.range
    _ ∣ Nat.card Q := Subgroup.card_range_dvd φ

open CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.SignalizerFunctorTheorem.NearModels.Suzuki
  CFSG.SignalizerFunctorTheorem.CatalogBridge in
private theorem lr2osz_outer_card_dvd_ringAut
    {a : ℕ} {K : Type} [Field K] [Finite K]
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Nat.card (Outer (suzukiGroup a K)) ∣ Nat.card (RingAut K) := by
  refine lr2osz_outer_card_dvd_of_inner_sup_eq_top (φ := szFieldAut a K) ?_
  rw [eq_top_iff]
  intro g _
  obtain ⟨x, τ, rfl⟩ := exists_eq_conj_mul_szFieldAut ha hK g
  exact Subgroup.mul_mem_sup ⟨x, rfl⟩ ⟨τ, rfl⟩

theorem ord7_card_mulAut_dvd_twistedB2
    {f : ℕ} {R : Type} [Group R] (hm : LieModel R .twistedB2 0 2 f) :
    Nat.card (MulAut R) ∣ f * Nat.card R := by
  have hsz : SuzukiModel R 2 f := by
    rcases hm with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, hsz⟩
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact hsz
  obtain ⟨-, a, ha, K, hKfld, hKfin, hf, hKcard, ⟨e⟩⟩ := hsz
  letI : Field K := hKfld
  letI : Finite K := hKfin
  have hK : Nat.card K = 2 ^ (2 * a + 1) := hf ▸ hKcard
  have hOut_dvd : Nat.card
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer (suzukiGroup a K)) ∣
      Nat.card (RingAut K) := lr2osz_outer_card_dvd_ringAut ha hK
  have hcardRing : Nat.card (RingAut K) = f :=
    ((CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic
      Nat.prime_two K hK).1).trans hf.symm
  have hOut_dvd_f : Nat.card
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer (suzukiGroup a K)) ∣ f := by
    rw [← hcardRing]
    exact hOut_dvd
  have hInn_dvd : Nat.card
      (CFSG.ComponentClassification.OuterAutomorphisms.inner (suzukiGroup a K)) ∣
      Nat.card (suzukiGroup a K) :=
    Subgroup.card_range_dvd (MulAut.conj : suzukiGroup a K →* MulAut (suzukiGroup a K))
  have hcardAut : Nat.card (MulAut (suzukiGroup a K)) = Nat.card
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer (suzukiGroup a K)) *
      Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner (suzukiGroup a K)) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup
      (CFSG.ComponentClassification.OuterAutomorphisms.inner (suzukiGroup a K))
  have hS_result : Nat.card (MulAut (suzukiGroup a K)) ∣ f * Nat.card (suzukiGroup a K) := by
    rw [hcardAut]
    exact mul_dvd_mul hOut_dvd_f hInn_dvd
  have hcardAutR : Nat.card (MulAut R) = Nat.card (MulAut (suzukiGroup a K)) :=
    Nat.card_congr (MulAut.congr e).toEquiv
  have hcardR : Nat.card R = Nat.card (suzukiGroup a K) := Nat.card_congr e.toEquiv
  rw [hcardAutR, hcardR]
  exact hS_result

theorem ord7Param_twistedB2 {f : ℕ} (h7 : ¬ 7 ∣ f) :
    Ord7Param .twistedB2 0 2 f := by
  intro R _ _ _ hmodel
  have hsz : SuzukiModel R 2 f := by
    rcases hmodel with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, hsz⟩
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact hsz
  obtain ⟨-, a, ha, K, hKfld, hKfin, hf, hKcard, ⟨e⟩⟩ := hsz
  letI : Field K := hKfld
  letI : Finite K := hKfin
  have hK : Nat.card K = 2 ^ (2 * a + 1) := hf ▸ hKcard
  haveI : Finite (MulAut (suzukiGroup a K)) :=
    Finite.of_injective
      (fun φ : MulAut (suzukiGroup a K) => (φ : suzukiGroup a K → suzukiGroup a K))
      DFunLike.coe_injective
  have hOut_dvd : Nat.card
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer (suzukiGroup a K)) ∣
      Nat.card (RingAut K) := lr2osz_outer_card_dvd_ringAut ha hK
  have hcardRing : Nat.card (RingAut K) = f :=
    ((CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic
      Nat.prime_two K hK).1).trans hf.symm
  have h7Out : ¬ 7 ∣ Nat.card
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer (suzukiGroup a K)) :=
    fun hd => h7 (hcardRing ▸ (hd.trans hOut_dvd))
  have hInn_dvd : Nat.card
      (CFSG.ComponentClassification.OuterAutomorphisms.inner (suzukiGroup a K)) ∣
      Nat.card (suzukiGroup a K) :=
    Subgroup.card_range_dvd (MulAut.conj : suzukiGroup a K →* MulAut (suzukiGroup a K))
  have hInnerFac : (Nat.card
      (CFSG.ComponentClassification.OuterAutomorphisms.inner (suzukiGroup a K))).factorization 7 ≤
      (Nat.card (suzukiGroup a K)).factorization 7 :=
    (Nat.factorization_le_iff_dvd (Nat.card_pos.ne') (Nat.card_pos.ne')).mpr hInn_dvd 7
  have hcardAut : Nat.card (MulAut (suzukiGroup a K)) = Nat.card
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer (suzukiGroup a K)) *
      Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner (suzukiGroup a K)) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup
      (CFSG.ComponentClassification.OuterAutomorphisms.inner (suzukiGroup a K))
  have hfac : (Nat.card (MulAut (suzukiGroup a K))).factorization 7 = (Nat.card
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer (suzukiGroup a K))).factorization 7 +
      (Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner (suzukiGroup a K))).factorization 7 := by
    rw [hcardAut, Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne'), Finsupp.add_apply]
  have hOutFac : (Nat.card
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer (suzukiGroup a K))).factorization 7 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd h7Out
  have hS_result : (Nat.card (MulAut (suzukiGroup a K))).factorization 7 ≤
      (Nat.card (suzukiGroup a K)).factorization 7 := by
    rw [hfac, hOutFac, zero_add]
    exact hInnerFac
  have hcardAutR : Nat.card (MulAut R) = Nat.card (MulAut (suzukiGroup a K)) :=
    Nat.card_congr (MulAut.congr e).toEquiv
  have hcardR : Nat.card R = Nat.card (suzukiGroup a K) := Nat.card_congr e.toEquiv
  rw [hcardAutR, hcardR]
  exact hS_result

end CFSG.StandardType.SporadicShape
