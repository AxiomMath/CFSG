module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TS3Core

public section

namespace CFSG.Quasithin.H13.F431.Lift

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin.H13.F431.F45
  CFSG.Quasithin.H13.F431.NF CFSG.Quasithin.Loc442Q
open scoped commutatorElement

universe u

section Datum

variable {D : Type} [Group D]

structure OrientD3 (P P' : Subgroup D) (z0 t0 : D) : Prop where
  cz : Subgroup.centralizer ({z0} : Set D) ≤ P
  ct : Subgroup.centralizer ({t0} : Set D) ≤ P'
  nz : ¬ Subgroup.centralizer ({z0} : Set D) ≤ P'
  nt : ¬ Subgroup.centralizer ({t0} : Set D) ≤ P
  Zperf : z0 ∈ centerOf (perfectCore P)
  F1 : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer ({z0} : Set D))
  F2 : 3 ∣ Nat.card ↥⁅Subgroup.centralizer ({t0} : Set D), Subgroup.centralizer ({t0} : Set D)⁆

end Datum

section Transfer

variable {D : Type} [Group D] (A : LieAmalgamExt D)
  (hgen : (MulAut.conj : D →* MulAut D).range ≤ A.K)

theorem commutator_cent_iK_le (hcen : Subgroup.center D = ⊥)
    (hF3 : ∀ x y : MulAut D, ⁅x, y⁆ ∈ (MulAut.conj : D →* MulAut D).range) (w : D) :
    ⁅Subgroup.centralizer ({iK A hgen w} : Set ↥A.K),
      Subgroup.centralizer ({iK A hgen w} : Set ↥A.K)⁆ ≤
      (Subgroup.centralizer ({w} : Set D)).map (iK A hgen) := by
  rw [Subgroup.commutator_le]
  intro k₁ hk₁ k₂ hk₂
  obtain ⟨d, hd⟩ := hF3 (k₁ : MulAut D) (k₂ : MulAut D)
  have hκ : (⁅k₁, k₂⁆ : ↥A.K) = iK A hgen d := by
    apply Subtype.ext
    rw [iK_coe, hd]
    exact map_commutatorElement A.K.subtype k₁ k₂
  have hmem : (⁅k₁, k₂⁆ : ↥A.K) ∈ Subgroup.centralizer ({iK A hgen w} : Set ↥A.K) := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hk₁ hk₂) (inv_mem hk₁)) (inv_mem hk₂)
  rw [hκ] at hmem ⊢
  exact ⟨d, (iK_mem_centralizer_iff A hgen hcen w d).mp hmem, rfl⟩

theorem not_three_dvd_commutator_cent_iK (hcen : Subgroup.center D = ⊥)
    (hF3 : ∀ x y : MulAut D, ⁅x, y⁆ ∈ (MulAut.conj : D →* MulAut D).range) {z0 : D}
    (hF1 : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer ({z0} : Set D))) :
    ¬ 3 ∣ Nat.card ↥⁅Subgroup.centralizer ({iK A hgen z0} : Set ↥A.K),
      Subgroup.centralizer ({iK A hgen z0} : Set ↥A.K)⁆ := fun h3 =>
  hF1 (by
    have h := dvd_trans h3 (Subgroup.card_dvd_of_le (commutator_cent_iK_le A hgen hcen hF3 z0))
    rwa [Subgroup.card_map_of_injective (iK_injective A hgen hcen)] at h)

theorem three_dvd_commutator_cent_iK (hcen : Subgroup.center D = ⊥) {t0 : D}
    (hF2 : 3 ∣ Nat.card ↥⁅Subgroup.centralizer ({t0} : Set D),
      Subgroup.centralizer ({t0} : Set D)⁆) :
    3 ∣ Nat.card ↥⁅Subgroup.centralizer ({iK A hgen t0} : Set ↥A.K),
      Subgroup.centralizer ({iK A hgen t0} : Set ↥A.K)⁆ := by
  have hle : (Subgroup.centralizer ({t0} : Set D)).map (iK A hgen) ≤
      Subgroup.centralizer ({iK A hgen t0} : Set ↥A.K) := by
    rintro _ ⟨d, hd, rfl⟩
    exact (iK_mem_centralizer_iff A hgen hcen t0 d).mpr hd
  have h2 : Nat.card ↥⁅(Subgroup.centralizer ({t0} : Set D)).map (iK A hgen),
      (Subgroup.centralizer ({t0} : Set D)).map (iK A hgen)⁆ =
      Nat.card ↥⁅Subgroup.centralizer ({t0} : Set D), Subgroup.centralizer ({t0} : Set D)⁆ := by
    rw [← Subgroup.map_commutator, Subgroup.card_map_of_injective (iK_injective A hgen hcen)]
  exact dvd_trans (h2 ▸ hF2) (Subgroup.card_dvd_of_le (Subgroup.commutator_mono hle hle))

end Transfer

section Final

variable {D : Type} [Group D] [Finite D] {G : Type} [Group G] [Finite G] {M1 M2 : Subgroup G}
  (E : LieExt D M1 M2)

open scoped Classical in
theorem f431Local_of_dlevel3 (hcen : Subgroup.center D = ⊥)
    (hgen : (MulAut.conj : D →* MulAut D).range ≤ E.K)
    (hodd : ¬ 2 ∣ (iK E.toLieAmalgamExt hgen).range.index) {z0 t0 : D} {V L : Subgroup D}
    (H : TwoClassD E.toLieAmalgamExt z0 t0) (HL : LocD E.toLieAmalgamExt z0 t0 V L)
    (hF3 : ∀ x y : MulAut D, ⁅x, y⁆ ∈ (MulAut.conj : D →* MulAut D).range)
    (hag : ∀ E' : Subgroup ↥E.K, IsAGMember (E.TD.map (iK E.toLieAmalgamExt hgen)) E' →
      Subgroup.normalizer (E' : Set ↥E.K) ≤ E.Mb1 ∨ Subgroup.normalizer (E' : Set ↥E.K) ≤ E.Mb2)
    (hyp1 : ∀ w ∈ centerOf (perfectCore M1), orderOf w = 2 →
      Subgroup.centralizer ({w} : Set G) ≤ M1)
    (hyp2 : ∀ w ∈ centerOf (perfectCore M2), orderOf w = 2 →
      Subgroup.centralizer ({w} : Set G) ≤ M2)
    (hor : OrientD3 E.P1 E.P2 z0 t0 ∨ OrientD3 E.P2 E.P1 z0 t0) :
    ∃ (T : Subgroup ↥E.K) (I : Finset ↥E.K) (z : ↥E.K), F431LieK T E.Mb1 E.Mb2 I z ∧
      (∀ i ∈ I, ∀ j ∈ I, i ≠ j →
        ¬ IsConj (amalgamMap E.b1 E.b2 i) (amalgamMap E.b1 E.b2 j)) ∧
      (∀ i ∈ I, Subgroup.centralizer ({i} : Set ↥E.K) ≤ E.Mb1 →
        Subgroup.centralizer ({amalgamMap E.b1 E.b2 i} : Set G) ≤ M1) ∧
      (∀ i ∈ I, Subgroup.centralizer ({i} : Set ↥E.K) ≤ E.Mb2 →
        Subgroup.centralizer ({amalgamMap E.b1 E.b2 i} : Set G) ≤ M2) := by
  set A := E.toLieAmalgamExt with hA
  have LK := f431LieK_of_twoClassD A hgen hcen hodd H hag
  have LKloc := locK_of_dlevel A hgen hcen hodd HL
  refine ⟨A.TD.map (iK A hgen), {iK A hgen z0, iK A hgen t0}, iK A hgen z0, LK, ?_⟩
  have hI : ({iK A hgen z0, iK A hgen t0} : Finset ↥A.K) = {iK A hgen z0, iK A hgen t0} := rfl
  have hmemI : ∀ i ∈ ({iK A hgen z0, iK A hgen t0} : Finset ↥A.K),
      i = iK A hgen z0 ∨ i = iK A hgen t0 := by
    intro i hi
    rwa [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hor with HO | HO
  · have hz3 := not_three_dvd_commutator_cent_iK A hgen hcen hF3 HO.F1
    have ht3 := three_dvd_commutator_cent_iK A hgen hcen HO.F2
    obtain ⟨hnf, hb1, hbt⟩ := local_core3 LK E.comp hI E.range_b1 E.range_b2 hyp1
      (cent_le_Mb1 A hgen hcen HO.cz H.aut_z) (cent_le_Mb2 A hgen hcen HO.ct H.aut_t)
      (iK_mem_centerOf_perfectCore_Mb1 A hgen hcen hodd HO.Zperf) hz3 ht3 LKloc
    refine ⟨hnfI_of_hnf hnf, ?_, ?_⟩
    · intro i hi hc
      rcases hmemI i hi with rfl | rfl
      · exact hb1
      · exact absurd (cent_le_P1_of_Mb1 A hgen hc) HO.nt
    · intro i hi hc
      rcases hmemI i hi with rfl | rfl
      · exact absurd (cent_le_P2_of_Mb2 A hgen hc) HO.nz
      · exact hbt
  · have hz3 := not_three_dvd_commutator_cent_iK A hgen hcen hF3 HO.F1
    have ht3 := three_dvd_commutator_cent_iK A hgen hcen HO.F2
    obtain ⟨hnf, hb1, hbt⟩ := local_core3 (swapLieK LK) (swapComp E.comp) hI E.range_b2
      E.range_b1 hyp2 (cent_le_Mb2 A hgen hcen HO.cz H.aut_z)
      (cent_le_Mb1 A hgen hcen HO.ct H.aut_t)
      (iK_mem_centerOf_perfectCore_Mb2 A hgen hcen hodd HO.Zperf) hz3 ht3 LKloc
    rw [amalgamMap_swap E.comp] at hnf hb1 hbt
    refine ⟨hnfI_of_hnf hnf, ?_, ?_⟩
    · intro i hi hc
      rcases hmemI i hi with rfl | rfl
      · exact absurd (cent_le_P1_of_Mb1 A hgen hc) HO.nz
      · exact hbt
    · intro i hi hc
      rcases hmemI i hi with rfl | rfl
      · exact hb1
      · exact absurd (cent_le_P2_of_Mb2 A hgen hc) HO.nt

end Final

end CFSG.Quasithin.H13.F431.Lift
