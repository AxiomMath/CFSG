module

public import CFSG.LocalAnalysis.StandardType.GGSporKOrdBMLift
public import CFSG.LieType.ChevTwo.OppCl.AutLifts
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.Open
  CFSG.EvenSmallLie.CatalogOrders
  CFSG.LieType.ChevTwo.OppCl

theorem ordBMBound_PSp_two {f : ℕ} (hf : 2 ≤ f) :
    OrdBMBound .PSp 2 2 f (bmGlOrd 4 (2 ^ f) * f) := by
  unfold OrdBMBound
  intro R _ _ _ hmodel ℓ hℓ hℓ2
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hclass : StatedClassicalModel R .PSp 2 2 f :=
    LieModel.statedClassicalModel_of_ne_zero (by norm_num : (2 : ℕ) ≠ 0) hmodel
  rw [StatedClassicalModel] at hclass
  obtain ⟨_, K, hKfield, hKfin, hKcard, ⟨e⟩⟩ := hclass
  letI : Field K := hKfield
  letI : Finite K := hKfin
  haveI : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hKcard
  have hcard : Nat.card (MulAut R) = Nat.card (MulAut (StatedProj (StatedSp 2 K))) :=
    Nat.card_congr (MulAut.congr e).toEquiv
  let V := Fin 2 ⊕ Fin 2 → K
  haveI : Nontrivial V :=
    ⟨fun _ => 1, fun _ => 0, fun h => one_ne_zero (congr_fun h (Sum.inl 0))⟩
  let N : Subgroup (StatedSp 2 K) :=
    (StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf (StatedSp 2 K)
  let π : ↥(StatedSp 2 K) →* StatedProj (StatedSp 2 K) := QuotientGroup.mk' N
  let ρ : ↥(StatedSp 2 K) →* Module.End K V :=
    CFSG.LieType.BorelTits.natRep (StatedSp 2 K)
  let P : Equiv.Perm V → Prop := SemiIso (CFSG.LieType.BorelTits.spForm 2 K)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hρ : Function.Injective ρ := CFSG.LieType.BorelTits.natRep_injective _
  have hP1 : P 1 := semiIso_one (CFSG.LieType.BorelTits.spForm 2 K)
  have hPm : ∀ r s, P r → P s → P (r * s) :=
    fun r s => semiIso_mul (CFSG.LieType.BorelTits.spForm 2 K)
  have hPi : ∀ r, P r → P r⁻¹ :=
    fun r hr => semiIso_inv (CFSG.LieType.BorelTits.spForm 2 K) hr
  have h4 : 4 ≤ Nat.card K := by
    rw [hKcard]
    exact pow_right_monotone (a := 2) (by norm_num : 1 ≤ (2 : ℕ)) hf
  have hind : ∀ R' : Subgroup (MulAut (StatedProj (StatedSp 2 K))), IsPGroup ℓ R' →
      ∀ α ∈ R', ∃ r : Equiv.Perm V, r ∈ semilinGroup K V ∧ P r ∧ Induces π ρ r α := by
    intro R' hR' α hα
    exact induced_PSp_two (F := K) (p := ℓ) (hp2 := hℓ2) (hF := h4)
      (R := R') (hR := hR') α hα
  have hlift := lre6b_factorization_le_of_lift (F := K) (V := V)
      (H := ↥(StatedSp 2 K)) (K := StatedProj (StatedSp 2 K))
      (π := π) (hπ := hπ) (ρ := ρ) (hρ := hρ)
      (P := P) (hP1 := hP1) (hPm := hPm) (hPi := hPi) (ℓ := ℓ) (hind := hind)
  have hdvd0 : Nat.card (semilinGroup K V) ∣
      Nat.card (V ≃ₗ[K] V) * Nat.card (K ≃+* K) := lre6b_card_semilin_dvd
  have hgl : Nat.card (V ≃ₗ[K] V) = bmGlOrd 4 (2 ^ f) := by
    have h := lre6b_card_linearEquiv (F := K) (ι := Fin 2 ⊕ Fin 2) (N := 4) (by simp)
    rw [hKcard] at h
    exact h
  have haut : Nat.card (K ≃+* K) = f :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic
      (p := 2) (n := f) Nat.prime_two K hKcard).1
  have hdvd : Nat.card (semilinGroup K V) ∣ bmGlOrd 4 (2 ^ f) * f := by
    rw [hgl, haut] at hdvd0
    exact hdvd0
  have hB : bmGlOrd 4 (2 ^ f) * f ≠ 0 := by
    apply mul_ne_zero
    · have hpos : 0 < bmGlOrd 4 (2 ^ f) := by
        rw [← hgl]
        haveI : Finite (V ≃ₗ[K] V) :=
          Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V)) LinearEquiv.coe_injective
        haveI : Nonempty (V ≃ₗ[K] V) := ⟨LinearEquiv.refl K V⟩
        exact Nat.card_pos
      exact ne_of_gt hpos
    · omega
  have hd0 : Nat.card (semilinGroup K V) ≠ 0 := by
    rintro h0
    obtain ⟨c, hc⟩ := hdvd
    rw [h0, zero_mul] at hc
    exact hB hc
  have hfin : (Nat.card (semilinGroup K V)).factorization ℓ ≤
      (bmGlOrd 4 (2 ^ f) * f).factorization ℓ :=
    (Nat.factorization_le_iff_dvd hd0 hB).2 hdvd ℓ
  rw [hcard]
  exact le_trans hlift hfin

private theorem lre6br2_bmGlOrd_ne_zero {N q : ℕ} (hq : 2 ≤ q) : bmGlOrd N q ≠ 0 := by
  unfold bmGlOrd
  apply mul_ne_zero
  · exact (pow_pos (by omega : 0 < q) _).ne'
  · suffices h : ∀ (l : List ℕ) (a : ℕ), 0 < a →
        0 < l.foldl (fun a i => a * (q ^ (i + 1) - 1)) a by
      exact (h (List.range N) 1 (by norm_num)).ne'
    intro l
    induction l with
    | nil => intro a ha; simpa using ha
    | cons i l ih =>
        intro a ha
        rw [List.foldl_cons]
        apply ih
        apply Nat.mul_pos ha
        have h1 : 1 < q ^ (i + 1) := Nat.one_lt_pow (by omega) (by omega)
        omega

theorem ordBMBound_POmegaPlus {n f : ℕ} (hn : 5 ≤ n) (hf : 1 ≤ f) :
    OrdBMBound .POmegaPlus n 2 f (bmGlOrd (2 * n) (2 ^ f) * f) := by
  intro R _ _ _ hmodel ℓ hℓ hℓ2
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hclass : StatedClassicalModel R .POmegaPlus n 2 f :=
    hmodel.statedClassicalModel (by decide)
  obtain ⟨-, K, hKfield, hKfin, hKcard, ⟨e⟩⟩ := hclass
  letI : Field K := hKfield
  letI : Finite K := hKfin
  haveI : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hKcard
  have hcardAut : Nat.card (MulAut R) =
      Nat.card (MulAut (StatedProj (StatedOmega (StatedQuadPlus n K)))) :=
    Nat.card_congr (MulAut.congr e).toEquiv
  haveI : Nontrivial (Fin n ⊕ Fin n → K) := by
    haveI : NeZero n := ⟨by omega⟩
    infer_instance
  have hN : Fintype.card (Fin n ⊕ Fin n) = 2 * n := by
    simp [Fintype.card_sum, two_mul]
  have hlift := lre6b_factorization_le_of_lift
    (F := K) (V := Fin n ⊕ Fin n → K)
    (H := ↥(StatedOmega (StatedQuadPlus n K)))
    (K := StatedProj (StatedOmega (StatedQuadPlus n K)))
    (QuotientGroup.mk'
      ((StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedOmega (StatedQuadPlus n K))))
    (QuotientGroup.mk'_surjective _)
    (CFSG.LieType.BorelTits.natRep (StatedOmega (StatedQuadPlus n K)))
    (CFSG.LieType.BorelTits.natRep_injective _)
    (SemiIsoQ (CFSG.LieType.BorelTits.quadPlusForm n K))
    (semiIsoQ_one _)
    (fun r s hr hs => semiIsoQ_mul _ hr hs)
    (fun r hr => semiIsoQ_inv _ hr)
    ℓ
    (fun R' hR' α hα => induced_POmegaPlus K ℓ hℓ2 n hn R' hR' α hα)
  have hdvd : Nat.card (semilinGroup K (Fin n ⊕ Fin n → K)) ∣
      Nat.card ((Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)) * Nat.card (K ≃+* K) :=
    lre6b_card_semilin_dvd
  have hdvd' : Nat.card (semilinGroup K (Fin n ⊕ Fin n → K)) ∣
      bmGlOrd (2 * n) (2 ^ f) * f := by
    rw [lre6b_card_linearEquiv (F := K) (ι := Fin n ⊕ Fin n) (N := 2 * n) hN,
        (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic
          Nat.prime_two K hKcard).1, hKcard] at hdvd
    exact hdvd
  have hbmGl_ne : bmGlOrd (2 * n) (2 ^ f) ≠ 0 := by
    have h2f : 2 ≤ 2 ^ f := by
      have h := Nat.one_lt_pow (n := f) (by omega) (by norm_num : 1 < 2)
      omega
    exact lre6br2_bmGlOrd_ne_zero (N := 2 * n) (q := 2 ^ f) h2f
  have hBne : bmGlOrd (2 * n) (2 ^ f) * f ≠ 0 :=
    mul_ne_zero hbmGl_ne (by omega)
  have hsne : Nat.card (semilinGroup K (Fin n ⊕ Fin n → K)) ≠ 0 :=
    Nat.card_ne_zero.mpr ⟨⟨1, Subgroup.one_mem _⟩, inferInstance⟩
  have hfac : (Nat.card (semilinGroup K (Fin n ⊕ Fin n → K))).factorization ℓ ≤
      (bmGlOrd (2 * n) (2 ^ f) * f).factorization ℓ :=
    (Nat.factorization_le_iff_dvd hsne hBne).2 hdvd' ℓ
  rw [hcardAut]
  exact le_trans hlift hfac

theorem ordBMBound_POmegaMinus {n f : ℕ} (hn : 4 ≤ n) (hf : 1 ≤ f) :
    OrdBMBound .POmegaMinus n 2 f (bmGlOrd (2 * n) (2 ^ f) * f) := by
  intro R _ _ _ hmodel ℓ hℓ hℓ2
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hn0 : n ≠ 0 := by omega
  have hclassic : StatedClassicalModel R .POmegaMinus n 2 f :=
    CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero hn0 hmodel
  unfold StatedClassicalModel at hclassic
  obtain ⟨-, K, hField, hFinite, hcard, b, c, hirr, ⟨e⟩⟩ := hclassic
  letI : Field K := hField
  letI : Finite K := hFinite
  haveI : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hf hcard
  let V := Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K
  haveI : Nonempty (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
  haveI : Nontrivial V := inferInstance
  have hVcard : Fintype.card (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) = 2 * n := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have hcardAut : Nat.card (MulAut R) =
      Nat.card (MulAut (StatedProj (StatedOmega (StatedQuadMinus n K b c)))) :=
    Nat.card_congr (MulAut.congr e).toEquiv
  have hbound :
      (Nat.card (MulAut (StatedProj (StatedOmega (StatedQuadMinus n K b c))))).factorization ℓ ≤
      (Nat.card (semilinGroup K V)).factorization ℓ := by
    refine lre6b_factorization_le_of_lift (F := K) (V := V)
      (H := ↥(StatedOmega (StatedQuadMinus n K b c)))
      (K := StatedProj (StatedOmega (StatedQuadMinus n K b c)))
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ℓ ?_
    · exact QuotientGroup.mk' ((StatedScalars
        (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K).subgroupOf
          (StatedOmega (StatedQuadMinus n K b c)))
    · exact QuotientGroup.mk'_surjective _
    · exact CFSG.LieType.BorelTits.natRep (StatedOmega (StatedQuadMinus n K b c))
    · exact CFSG.LieType.BorelTits.natRep_injective _
    · exact SemiIsoQ (CFSG.LieType.BorelTits.quadMinusForm n K b c hirr)
    · exact semiIsoQ_one (CFSG.LieType.BorelTits.quadMinusForm n K b c hirr)
    · intro r s hr hs
      exact semiIsoQ_mul (CFSG.LieType.BorelTits.quadMinusForm n K b c hirr) hr hs
    · intro r hr
      exact semiIsoQ_inv (CFSG.LieType.BorelTits.quadMinusForm n K b c hirr) hr
    · intro S hS α hα
      exact induced_POmegaMinus (F := K) (p := ℓ) (hp2 := hℓ2) (n := n) (hn := hn)
        (b := b) (c := c) (hirr := hirr) (R := S) (hR := hS) α hα
  have hdvd : Nat.card (semilinGroup K V) ∣
      Nat.card (V ≃ₗ[K] V) * Nat.card (K ≃+* K) :=
    lre6b_card_semilin_dvd (F := K) (V := V)
  have hlin : Nat.card (V ≃ₗ[K] V) = bmGlOrd (2 * n) (Nat.card K) := by
    change Nat.card ((Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) ≃ₗ[K]
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K)) = bmGlOrd (2 * n) (Nat.card K)
    exact lre6b_card_linearEquiv (F := K)
      (ι := Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (N := 2 * n) hVcard
  have haut : Nat.card (K ≃+* K) = f :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic
      Nat.prime_two K hcard).1
  have hbm : Nat.card (V ≃ₗ[K] V) * Nat.card (K ≃+* K) =
      bmGlOrd (2 * n) (2 ^ f) * f := by
    rw [hlin, haut, hcard]
  have hdvd' : Nat.card (semilinGroup K V) ∣ bmGlOrd (2 * n) (2 ^ f) * f := by
    simpa only [hbm] using hdvd
  have hbmGl_ne : bmGlOrd (2 * n) (2 ^ f) ≠ 0 := by
    haveI : Finite (V ≃ₗ[K] V) :=
      Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
        (fun e₁ e₂ h => LinearEquiv.ext (congrFun h))
    have hne_lin : Nat.card (V ≃ₗ[K] V) ≠ 0 :=
      Nat.card_ne_zero.mpr ⟨⟨LinearEquiv.refl K V⟩, inferInstance⟩
    rw [← hcard, ← hlin]
    exact hne_lin
  have hne : bmGlOrd (2 * n) (2 ^ f) * f ≠ 0 :=
    mul_ne_zero hbmGl_ne (by omega)
  have hd0 : Nat.card (semilinGroup K V) ≠ 0 := by
    rintro h
    rw [h] at hdvd'
    exact hne (zero_dvd_iff.mp hdvd')
  have hfac : (Nat.card (semilinGroup K V)).factorization ℓ ≤
      (bmGlOrd (2 * n) (2 ^ f) * f).factorization ℓ :=
    (Nat.factorization_le_iff_dvd hd0 hne).2 hdvd' ℓ
  rw [hcardAut]
  exact le_trans hbound hfac

end CFSG.StandardType.SporadicShape
