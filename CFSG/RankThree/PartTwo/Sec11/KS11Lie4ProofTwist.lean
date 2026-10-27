module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofG2Minus
public import CFSG.LieType.Chevalley.OddDiagramFrobeniusFixedDerived

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.HighestRoot

namespace KS11Lie4Proof

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Chevalley CFSG.ComponentClassification.UnbalancedCatalog

theorem exists_quadratic_ext' (K : Type) [Field K] [Finite K] :
    ∃ (K₂ : Type) (_ : Field K₂) (_ : Finite K₂) (_ : Algebra K K₂) (σ : K₂ ≃+* K₂),
      Module.finrank K K₂ = 2 ∧ ∀ c, σ c = c ^ Nat.card K := by
  have : CharP K (ringChar K) := ringChar.charP K
  have : Fact (ringChar K).Prime :=
    ⟨(CharP.char_is_prime_or_zero K (ringChar K)).resolve_right
      (CharP.ringChar_ne_zero_of_finite K)⟩
  exact ⟨FiniteField.Extension K (ringChar K) 2, inferInstance, inferInstance, inferInstance,
    (FiniteField.Extension.frob K (ringChar K) 2).toRingEquiv,
    FiniteField.finrank_extension K (ringChar K) 2, fun c => by simp⟩

theorem natCard_quadratic {K K₂ : Type} [Field K] [Finite K] [Field K₂] [Algebra K K₂]
    (hdeg : Module.finrank K K₂ = 2) : Nat.card K₂ = Nat.card K ^ 2 := by
  have : Module.Finite K K₂ := Module.finite_of_finrank_pos (by omega)
  rw [Module.natCard_eq_pow_finrank (K := K), hdeg]

theorem exists_sl2_eq_map_of_fixed {K K₂ : Type} [Field K] [Field K₂] [Algebra K K₂]
    (σ : K₂ ≃+* K₂) (hfix : ∀ c, σ c = c ↔ c ∈ Set.range (algebraMap K K₂)) (B : SL2 K₂)
    (hB : Matrix.SpecialLinearGroup.map (σ : K₂ →+* K₂) B = B) :
    ∃ B' : SL2 K, Matrix.SpecialLinearGroup.map (algebraMap K K₂) B' = B := by
  have h : ∀ i j, ∃ c : K, algebraMap K K₂ c = (B : Matrix (Fin 2) (Fin 2) K₂) i j := by
    intro i j
    refine (hfix _).mp ?_
    have h1 := congrArg (fun A : SL2 K₂ => (A : Matrix (Fin 2) (Fin 2) K₂) i j) hB
    simpa using h1
  choose c hc using h
  set N : Matrix (Fin 2) (Fin 2) K := Matrix.of c with hN
  have hNB : (algebraMap K K₂).mapMatrix N = (B : Matrix (Fin 2) (Fin 2) K₂) := by
    ext i j
    simp [hN, hc]
  have hdet : N.det = 1 := by
    apply (algebraMap K K₂).injective
    rw [RingHom.map_det, hNB, B.2, map_one]
  exact ⟨⟨N, hdet⟩, Subtype.ext hNB⟩

section Base

variable {K K₂ : Type} [Field K] [Field K₂] [Algebra K K₂]

@[expose] noncomputable def bcG2 (K K₂ : Type) [Field K] [Field K₂] [Algebra K K₂] :
    adjointGroup .G2 K →* adjointGroup .G2 K₂ :=
  ((baseChangeGL (algebraMap K K₂)).comp (adjointGroup .G2 K).subtype).codRestrict _
    fun x => baseChangeGL_mem_adjointGroup _ x.2

theorem coe_bcG2 (x : adjointGroup .G2 K) :
    (bcG2 K K₂ x : ModGL .G2 K₂) = baseChangeGL (algebraMap K K₂) (x : ModGL .G2 K) :=
  rfl

theorem bcG2_injective : Function.Injective (bcG2 K K₂) := fun _ _ h =>
  Subtype.ext (baseChangeGL_injective (τ := .G2) (algebraMap K K₂) (congrArg Subtype.val h))

theorem baseChangeGL_rhoV {L : Type} [Field L] (f : K →+* L) (A : SL2 K) :
    baseChangeGL f (rhoV K A) = rhoV L (Matrix.SpecialLinearGroup.map f A) := by
  rw [rhoV_apply, rhoV_apply, map_mul, map_mul, map_inv, baseChangeGL_canonicalRep,
    baseChangeGL_simpleRootSL2_of_field]

theorem bcG2_mem_g2ShortSL2 {x : adjointGroup .G2 K} (hx : x ∈ g2ShortSL2 K) :
    bcG2 K K₂ x ∈ g2ShortSL2 K₂ := by
  obtain ⟨A, hA⟩ := mem_g2ShortSL2_iff.mp hx
  rw [mem_g2ShortSL2_iff]
  exact ⟨Matrix.SpecialLinearGroup.map (algebraMap K K₂) A, by
    rw [← baseChangeGL_rhoV, hA, coe_bcG2]⟩

theorem bcG2_mem_g2LongSL2 {x : adjointGroup .G2 K} (hx : x ∈ g2LongSL2 K) :
    bcG2 K K₂ x ∈ g2LongSL2 K₂ := by
  obtain ⟨A, hA⟩ := mem_g2LongSL2_iff.mp hx
  rw [mem_g2LongSL2_iff]
  exact ⟨Matrix.SpecialLinearGroup.map (algebraMap K K₂) A, by
    rw [← baseChangeGL_simpleRootSL2_of_field, hA, coe_bcG2]⟩

theorem baseChangeGL_bcG2 (σ : K₂ →+* K₂) (hσ : σ.comp (algebraMap K K₂) = algebraMap K K₂)
    (x : adjointGroup .G2 K) :
    baseChangeGL σ (bcG2 K K₂ x : ModGL .G2 K₂) = bcG2 K K₂ x := by
  rw [coe_bcG2, baseChangeGL_baseChangeGL, hσ]

theorem mem_g2ShortSL2_of_bcG2 (σ : K₂ ≃+* K₂)
    (hfix : ∀ c, σ c = c ↔ c ∈ Set.range (algebraMap K K₂)) {x : adjointGroup .G2 K}
    (hx : bcG2 K K₂ x ∈ g2ShortSL2 K₂) : x ∈ g2ShortSL2 K := by
  have hσ : (σ : K₂ →+* K₂).comp (algebraMap K K₂) = algebraMap K K₂ := by
    ext c
    exact (hfix _).mpr ⟨c, rfl⟩
  obtain ⟨B, hB⟩ := mem_g2ShortSL2_iff.mp hx
  have h1 : rhoV K₂ (Matrix.SpecialLinearGroup.map (σ : K₂ →+* K₂) B) = rhoV K₂ B := by
    rw [← baseChangeGL_rhoV, hB, baseChangeGL_bcG2 _ hσ]
  obtain ⟨B', hB'⟩ := exists_sl2_eq_map_of_fixed σ hfix B (rhoV_injective h1)
  rw [mem_g2ShortSL2_iff]
  refine ⟨B', baseChangeGL_injective (τ := .G2) (algebraMap K K₂) ?_⟩
  rw [baseChangeGL_rhoV, hB', hB, coe_bcG2]

theorem mem_g2LongSL2_of_bcG2 (σ : K₂ ≃+* K₂)
    (hfix : ∀ c, σ c = c ↔ c ∈ Set.range (algebraMap K K₂)) {x : adjointGroup .G2 K}
    (hx : bcG2 K K₂ x ∈ g2LongSL2 K₂) : x ∈ g2LongSL2 K := by
  have hσ : (σ : K₂ →+* K₂).comp (algebraMap K K₂) = algebraMap K K₂ := by
    ext c
    exact (hfix _).mpr ⟨c, rfl⟩
  obtain ⟨B, hB⟩ := mem_g2LongSL2_iff.mp hx
  have h1 : simpleRootSL2 .G2 K₂ g2ia (Matrix.SpecialLinearGroup.map (σ : K₂ →+* K₂) B) =
      simpleRootSL2 .G2 K₂ g2ia B := by
    rw [← baseChangeGL_simpleRootSL2_of_field, hB, baseChangeGL_bcG2 _ hσ]
  obtain ⟨B', hB'⟩ := exists_sl2_eq_map_of_fixed σ hfix B (simpleRootSL2_injective_g2 _ h1)
  rw [mem_g2LongSL2_iff]
  refine ⟨B', baseChangeGL_injective (τ := .G2) (algebraMap K K₂) ?_⟩
  rw [baseChangeGL_simpleRootSL2_of_field, hB', hB, coe_bcG2]

theorem map_mem_centralizer {G H : Type*} [Group G] [Group H] (f : G →* H) {z x : G}
    (hx : x ∈ Subgroup.centralizer ({z} : Set G)) :
    f x ∈ Subgroup.centralizer ({f z} : Set H) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
  rw [← map_mul, ← map_mul, hx]

end Base

section Cent

variable {K : Type} [Field K]

theorem mem_g2LongSL2_of_mem_sup {x : adjointGroup .G2 K}
    (hx : (x : ModGL .G2 K) ∈
      torusGroup .G2 K ⊔ (rootSubgroup .G2 K g2e0 ⊔ rootSubgroup .G2 K (-g2e0)))
    (hxS : x ∈ Subgroup.centralizer (g2ShortSL2 K : Set (adjointGroup .G2 K))) :
    x ∈ g2LongSL2 K := by
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right _ _
    (torusGroup_le_normalizer_rootPair (K := K) (isRoot_single .G2 g2l))
  have hx' : (x : ModGL .G2 K) ∈
      ((torusGroup .G2 K ⊔ (rootSubgroup .G2 K g2e0 ⊔ rootSubgroup .G2 K (-g2e0)) :
        Subgroup (ModGL .G2 K)) : Set (ModGL .G2 K)) := hx
  rw [hset] at hx'
  obtain ⟨t', ht', u, hu, htu⟩ := hx'
  have hv1 : pinnedX .G2 K g2δ 1 ∈ rootSubgroup .G2 K g2δ ⊔ rootSubgroup .G2 K (-g2δ) :=
    Subgroup.mem_sup_left (mem_rootSubgroup.mpr ⟨1, rfl⟩)
  have hv1C : pinnedX .G2 K g2δ 1 ∈ adjointGroup .G2 K := pinnedX_mem_adjointGroup _ _
  have hc1 : (x : ModGL .G2 K) * pinnedX .G2 K g2δ 1 = pinnedX .G2 K g2δ 1 * x :=
    (congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hxS ⟨_, hv1C⟩ hv1)).symm
  have hc2 : u * pinnedX .G2 K g2δ 1 = pinnedX .G2 K g2δ 1 * u :=
    (KS11Lie2Proof.g2_commute' hu hv1).eq
  have htc : t' * pinnedX .G2 K g2δ 1 = pinnedX .G2 K g2δ 1 * t' := by
    have e : t' = (x : ModGL .G2 K) * u⁻¹ := by
      rw [← htu]
      group
    rw [e]
    calc (x : ModGL .G2 K) * u⁻¹ * pinnedX .G2 K g2δ 1 =
        (x : ModGL .G2 K) * (u⁻¹ * pinnedX .G2 K g2δ 1) := by group
      _ = (x : ModGL .G2 K) * (pinnedX .G2 K g2δ 1 * u⁻¹) := by
          rw [(Commute.inv_left hc2).eq]
      _ = pinnedX .G2 K g2δ 1 * ((x : ModGL .G2 K) * u⁻¹) := by
          rw [← mul_assoc, hc1, mul_assoc]
  have ht'M := mem_range_rhoA_of_torus ht' htc
  rw [← range_simpleRootSL2_g2] at hu
  rw [mem_g2LongSL2_iff, ← htu]
  exact mul_mem ht'M hu

theorem mem_g2LongSL2_of_mem_centralizer [Finite K] (hK5 : 5 ≤ Nat.card K)
    {x : adjointGroup .G2 K}
    (hxS : x ∈ Subgroup.centralizer (g2ShortSL2 K : Set (adjointGroup .G2 K))) :
    x ∈ g2LongSL2 K := by
  obtain ⟨μ, hμ⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hμo : orderOf μ = Nat.card K - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hμ, Nat.card_units]
  have hμ4 : 4 ≤ orderOf μ := by omega
  set y : adjointGroup .G2 K := ⟨rhoV K (HSL μ), by
    rw [rhoV_apply]
    exact mul_mem (mul_mem (canonicalRep_mem_adjointGroup _ K _)
      (simpleRootSL2_mem_adjointGroup _ _)) (inv_mem (canonicalRep_mem_adjointGroup _ K _))⟩
  have hyS : y ∈ g2ShortSL2 K := mem_g2ShortSL2_iff.mpr ⟨HSL μ, rfl⟩
  have hy : (y : ModGL .G2 K) = rootDiagUnit .G2 (Pi.mulSingle g2ir μ) := rhoV_HSL μ
  have hxy : x ∈ Subgroup.centralizer ({y} : Set (adjointGroup .G2 K)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hxS y hyS).symm
  have hx : (x : ModGL .G2 K) ∈
      torusGroup .G2 K ⊔ (rootSubgroup .G2 K g2e0 ⊔ rootSubgroup .G2 K (-g2e0)) := by
    rw [← toralCentralizer_shortNine hμ4, ← mem_centralizer_iff_toral hy]
    exact hxy
  exact mem_g2LongSL2_of_mem_sup hx hxS

theorem eq_HSL_of_commute_HSL {L : Type} [Field L] {t : Lˣ} (ht : t ^ 2 ≠ 1) {C : SL2 L}
    (hC : HSL t * C = C * HSL t) : ∃ s : Lˣ, C = HSL s := by
  have htt : (t : L) ≠ ((t⁻¹ : Lˣ) : L) := by
    intro h
    apply ht
    have h1 : t = t⁻¹ := Units.ext h
    rw [sq]
    nth_rewrite 2 [h1]
    exact mul_inv_cancel t
  have hm := congrArg (fun A : SL2 L => (A : Matrix (Fin 2) (Fin 2) L)) hC
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_HSL] at hm
  have h01 := congrFun (congrFun hm 0) 1
  have h10 := congrFun (congrFun hm 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h01 h10
  have hc01 : (C : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 := by
    have : ((t : L) - ((t⁻¹ : Lˣ) : L)) * (C : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 := by
      simp only [Units.val_inv_eq_inv_val] at h01 ⊢
      linear_combination h01
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h) htt
    · exact h
  have hc10 : (C : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by
    have : ((t : L) - ((t⁻¹ : Lˣ) : L)) * (C : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by
      simp only [Units.val_inv_eq_inv_val] at h10 ⊢
      linear_combination -h10
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h) htt
    · exact h
  have hdet : (C : Matrix (Fin 2) (Fin 2) L) 0 0 * (C : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 := by
    have h := C.2
    rw [Matrix.det_fin_two, hc01, hc10] at h
    simpa using h
  refine ⟨Units.mkOfMulEqOne _ _ hdet, Subtype.ext ?_⟩
  rw [coe_HSL]
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · exact hc01
  · exact hc10
  · simp only [Units.val_inv_eq_inv_val, Units.val_mkOfMulEqOne]
    exact (eq_inv_of_mul_eq_one_right hdet).trans rfl

theorem pow_card_sq_sub_one_of_commute [Finite K] (h3 : 3 ∣ Nat.card K ^ 2 - 1) {A B : SL2 K}
    (hA3 : A ^ 3 = 1) (hA1 : A ≠ 1) (hAB : A * B = B * A) : B ^ (Nat.card K ^ 2 - 1) = 1 := by
  obtain ⟨K₂, _, _, _, σ, hdeg, -⟩ := exists_quadratic_ext' K
  have hcard := natCard_quadratic (K := K) (K₂ := K₂) hdeg
  set ι := Matrix.SpecialLinearGroup.map (n := Fin 2) (algebraMap K K₂) with hι
  have hιinj : Function.Injective ι := by
    intro X Y h
    apply Subtype.ext
    ext i j
    have h1 := congrArg (fun A : SL2 K₂ => (A : Matrix (Fin 2) (Fin 2) K₂) i j) h
    simpa [hι] using h1
  have h3' : 3 ∣ Nat.card K₂ - 1 := by rw [hcard]; exact h3
  obtain ⟨P, t, hPt⟩ := exists_conj_HSL_of_three h3' (ι A) ⟨1, by rw [pow_one, ← map_pow, hA3,
    map_one]⟩
  have hconj : ∀ n : ℕ, HSL t ^ n = P * ι A ^ n * P⁻¹ := fun n => by rw [← hPt, conj_pow]
  have ht3 : t ^ 3 = 1 := by
    apply HSLHom_injective (K := K₂)
    rw [map_pow, map_one, HSLHom_apply, hconj, ← map_pow, hA3, map_one, mul_one, mul_inv_cancel]
  have ht1 : t ≠ 1 := by
    rintro rfl
    apply hA1
    apply hιinj
    have h1 : P * ι A * P⁻¹ = 1 := by rw [hPt]; exact map_one (HSLHom K₂)
    rw [map_one]
    calc ι A = P⁻¹ * (P * ι A * P⁻¹) * P := by group
      _ = 1 := by rw [h1]; group
  have ht2 : t ^ 2 ≠ 1 := by
    intro h
    apply ht1
    calc t = t ^ 3 * (t ^ 2)⁻¹ := by group
      _ = 1 := by rw [ht3, h, inv_one, one_mul]
  have hcomm : HSL t * (P * ι B * P⁻¹) = (P * ι B * P⁻¹) * HSL t := by
    rw [← hPt]
    calc P * ι A * P⁻¹ * (P * ι B * P⁻¹) = P * ι (A * B) * P⁻¹ := by
          rw [map_mul]; group
      _ = P * ι (B * A) * P⁻¹ := by rw [hAB]
      _ = P * ι B * P⁻¹ * (P * ι A * P⁻¹) := by rw [map_mul]; group
  obtain ⟨s, hs⟩ := eq_HSL_of_commute_HSL ht2 hcomm
  have hs1 : s ^ (Nat.card K ^ 2 - 1) = 1 := by
    rw [← hcard, ← Nat.card_units]
    exact pow_card_eq_one'
  apply hιinj
  rw [map_pow, map_one]
  have h1 : (P * ι B * P⁻¹) ^ (Nat.card K ^ 2 - 1) = 1 := by
    rw [hs, ← HSLHom_apply, ← map_pow, hs1, map_one]
  rw [conj_pow, mul_inv_eq_one, mul_eq_left] at h1
  exact h1

end Cent

section Holds

theorem three_dvd_sq_sub_one {q : ℕ} (h : 3 ∣ q + 1) : 3 ∣ q ^ 2 - 1 := by
  have e : q ^ 2 - 1 = (q + 1) * (q - 1) := by rw [← Nat.sq_sub_sq, one_pow]
  rw [e]
  exact Dvd.dvd.mul_right h _

theorem g2ThreeBCentMinus_holds : G2ThreeBCentMinus := by
  intro K _ _ h3 hK4 z hzM hz3 hz1
  have hK5 : 5 ≤ Nat.card K := by omega
  obtain ⟨K₂, _, _, _, σ, hdeg, hσ⟩ := exists_quadratic_ext' K
  obtain ⟨-, -, hfix⟩ := CFSG.RankThree.QuadraticSL2.quadratic_frobenius hdeg σ hσ
  have hcard := natCard_quadratic (K := K) (K₂ := K₂) hdeg
  have h31 : 3 ∣ Nat.card K₂ - 1 := by rw [hcard]; exact three_dvd_sq_sub_one h3
  set ι := bcG2 K K₂
  have hιz3 : ι z ^ 3 = 1 := by rw [← map_pow, hz3, map_one]
  have hιz1 : ι z ≠ 1 := fun h => hz1 (bcG2_injective (h.trans (map_one ι).symm))
  have hsplit := g2ThreeBCent_split h31 (bcG2_mem_g2LongSL2 hzM) hιz3 hιz1
  refine ⟨fun x hx y hy => ?_, fun b hb hbS => ?_⟩
  · refine mem_g2ShortSL2_of_bcG2 σ hfix ?_
    have := hsplit.1 _ (map_mem_centralizer ι hx) _ (map_mem_centralizer ι hy)
    simpa only [map_mul, map_inv] using this
  · have hbM := mem_g2LongSL2_of_mem_centralizer hK5 hbS
    obtain ⟨B, hB⟩ := mem_g2LongSL2_iff.mp hbM
    obtain ⟨A, hA⟩ := mem_g2LongSL2_iff.mp hzM
    have hinj := simpleRootSL2_injective_g2 (K := K) g2ia
    have hA3 : A ^ 3 = 1 := hinj (by
      rw [map_pow, hA, map_one]
      exact congrArg Subtype.val hz3)
    have hA1 : A ≠ 1 := by
      rintro rfl
      apply hz1
      apply Subtype.ext
      rw [← hA, map_one]
      rfl
    have hAB : A * B = B * A := hinj (by
      rw [map_mul, map_mul, hA, hB]
      exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hb).symm)
    have h1 := pow_card_sq_sub_one_of_commute (three_dvd_sq_sub_one h3) hA3 hA1 hAB
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hB, ← map_pow, h1, map_one]
    rfl

theorem g2ShortNineCentMinus_holds : G2ShortNineCentMinus := by
  intro K _ _ h3 hK4 y hyS hy hy3
  have hK5 : 5 ≤ Nat.card K := by omega
  obtain ⟨K₂, _, _, _, σ, hdeg, hσ⟩ := exists_quadratic_ext' K
  obtain ⟨-, -, hfix⟩ := CFSG.RankThree.QuadraticSL2.quadratic_frobenius hdeg σ hσ
  have hcard := natCard_quadratic (K := K) (K₂ := K₂) hdeg
  have h31 : 3 ∣ Nat.card K₂ - 1 := by rw [hcard]; exact three_dvd_sq_sub_one h3
  set ι := bcG2 K K₂
  have hιy : ∃ k : ℕ, ι y ^ 3 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hy
    exact ⟨k, by rw [← map_pow, hk, map_one]⟩
  have hιy3 : ι y ^ 3 ≠ 1 := fun h => hy3 (bcG2_injective (K₂ := K₂) (by
    show ι (y ^ 3) = ι 1
    rw [map_pow, h, map_one]))
  have hsplit := g2ShortNineCent_split h31 (bcG2_mem_g2ShortSL2 hyS) hιy hιy3
  refine ⟨fun x hx w hw => ?_, fun x _ hxS => mem_g2LongSL2_of_mem_centralizer hK5 hxS⟩
  refine mem_g2LongSL2_of_bcG2 σ hfix ?_
  have := hsplit.1 _ (map_mem_centralizer ι hx) _ (map_mem_centralizer ι hw)
  simpa only [map_mul, map_inv] using this

end Holds

section Provers

theorem g2ThreeBCent_holds : G2ThreeBCent :=
  g2ThreeBCent_of_minus g2ThreeBCentMinus_holds

theorem thetaCentral119G2Ss_of_twisted (hC : G2ThreeConjSL2Minus) (hA : G2ThreeACentMinus) :
    ThetaCentral119G2Ss :=
  thetaCentral119G2Ss_of_minus hC hA g2ThreeBCentMinus_holds

theorem centJ119G2Inn_of_twisted (hC : G2ThreeConjSL2Minus) (hA : G2ThreeACentMinus) :
    CentJ119G2Inn :=
  centJ119G2Inn_of_minus hC hA g2ThreeBCentMinus_holds

theorem centJ119G2Out_of_twisted (hC : G2ThreeConjSL2Minus) (hA : G2ThreeACentMinus) :
    CentJ119G2Out :=
  centJ119G2Out_of_minus hC hA g2ThreeBCentMinus_holds

theorem normCentJ1117G2Ss_of_twisted (hC : G2ThreeConjSL2Minus) (hA : G2ThreeACentMinus) :
    NormCentJ1117G2Ss :=
  normCentJ1117G2Ss_of_minus hC hA g2ThreeBCentMinus_holds g2ShortNineCentMinus_holds

end Provers

end KS11Lie4Proof

end CFSG.RankThree.PartTwo.Sec11
