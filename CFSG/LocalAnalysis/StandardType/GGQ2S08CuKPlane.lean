module

public import CFSG.LocalAnalysis.StandardType.GGQ2PlaneRaw
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CuKE6
public import CFSG.LocalAnalysis.StandardType.GGQTwoK1OfI1

public section

namespace CFSG.StandardType.GGQ2S08Split

open CFSG CFSG.Assembly CFSG.StandardType.GGQ2Frame.PlaneRaw

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

theorem scalarLine_inside {t : ℕ} {e v : V t} (he : e ≠ 0) (hv : v ∈ centExt e)
    (h3 : 3 ∣ (Code.extSupport e).card)
    (hline : ∀ w ∈ centExt e, ∃ c : F, w = c • v) : v ∈ insideExt e := by
  have hsq : ∀ a : F, a ≠ 0 → a * a = 1 := by decide
  have he_mem : e ∈ centExt e := by
    rw [mem_centExt]
    intro p hp q hq
    rw [hsq (e p) (by simpa using hp), hsq (e q) (by simpa using hq)]
  obtain ⟨i, hi⟩ : ∃ i : Fin t, e i ≠ 0 := by
    by_contra h
    exact he (funext fun i => by
      by_contra hne
      exact h ⟨i, hne⟩)
  have hi_mem : i ∈ Code.extSupport e := by simpa using hi
  obtain ⟨a, ha⟩ := hline e he_mem
  have hvi : v i ≠ 0 := by
    intro hvi0
    apply hi
    calc e i = (a • v) i := by rw [ha]
      _ = a * v i := by rw [Pi.smul_apply, smul_eq_mul]
      _ = 0 := by rw [hvi0, mul_zero]
  have hv' : ∀ p ∈ Code.extSupport e, ∀ q ∈ Code.extSupport e, e p * v p = e q * v q :=
    (mem_centExt e v).mp hv
  have hne : ∀ j : Fin t, e j ≠ 0 := by
    intro j hj_eq
    have hij : i ≠ j := by
      intro h
      rw [h] at hi
      exact hi hj_eq
    have hw_mem : (Pi.single j (1 : F) : V t) ∈ centExt e := by
      rw [mem_centExt]
      intro p hp q hq
      have hpj : p ≠ j := by
        intro h
        rw [h] at hp
        exact (by simpa using hp : e j ≠ 0) hj_eq
      have hqj : q ≠ j := by
        intro h
        rw [h] at hq
        exact (by simpa using hq : e j ≠ 0) hj_eq
      have hp0 : (Pi.single j (1 : F) : V t) p = 0 :=
        Pi.single_eq_of_ne (M := fun _ => F) (i := j) (i' := p) hpj 1
      have hq0 : (Pi.single j (1 : F) : V t) q = 0 :=
        Pi.single_eq_of_ne (M := fun _ => F) (i := j) (i' := q) hqj 1
      rw [hp0, hq0]
      simp
    obtain ⟨b, hb⟩ := hline (Pi.single j (1 : F)) hw_mem
    have hwi : (Pi.single j (1 : F) : V t) i = 0 :=
      Pi.single_eq_of_ne (M := fun _ => F) (i := j) (i' := i) hij 1
    have hbi : b * v i = 0 := by
      have h1 : (Pi.single j (1 : F) : V t) i = (b • v) i := congrFun hb i
      rw [hwi] at h1
      simpa [Pi.smul_apply, smul_eq_mul] using h1.symm
    have hb0 : b = 0 := by
      rcases mul_eq_zero.mp hbi with h | h
      · exact h
      · exact absurd h hvi
    have hwj : (Pi.single j (1 : F) : V t) j = 1 :=
      Pi.single_eq_same (M := fun _ => F) j 1
    have h10 : (1 : F) = 0 := by
      have h1 : (Pi.single j (1 : F) : V t) j = (b • v) j := congrFun hb j
      rw [hwj, hb0] at h1
      simpa using h1
    exact one_ne_zero h10
  have hsupp_univ : Code.extSupport e = Finset.univ := by
    ext j
    simp only [Finset.mem_univ, iff_true]
    exact (mem_extSupport e j).mpr (hne j)
  have hcard : (Code.extSupport e).card = t := by
    rw [hsupp_univ, Finset.card_univ, Fintype.card_fin]
  have htF : (t : F) = 0 := by
    have h3' : 3 ∣ t := by rw [← hcard]; exact h3
    exact (CharP.cast_eq_zero_iff F 3 t).mpr h3'
  have hsum0 : ∑ j, e j * v j = 0 := by
    have h1 : ∑ j, e j * v j = ∑ j ∈ Code.extSupport e, e j * v j := by
      rw [hsupp_univ]
    rw [h1]
    calc ∑ j ∈ Code.extSupport e, e j * v j
        = ∑ _j ∈ Code.extSupport e, e i * v i :=
          Finset.sum_congr rfl (fun j hj => (hv' i hi_mem j hj).symm)
      _ = (Code.extSupport e).card • (e i * v i) := Finset.sum_const _
      _ = t • (e i * v i) := by rw [hcard]
      _ = (t : F) * (e i * v i) := by rw [nsmul_eq_mul]
      _ = 0 := by rw [htF, zero_mul]
  rw [mem_insideExt]
  exact ⟨fun j hj => (hne j hj).elim, hsum0⟩

structure SplitPlaneRealization {G : Type} [Group G] (E K : Subgroup G) (N t : ℕ) where
  coord : Additive E ≃+ V t
  e : V t
  nonzero : e ≠ 0
  support_card : (Code.extSupport e).card = N
  cent_eq : ∀ b : E, (b : G) ∈ Subgroup.centralizer (K : Set G) ↔
    coord (Additive.ofMul b) ∈ centExt e
  inside_eq : ∀ b : E, (b : G) ∈ K ↔ coord (Additive.ofMul b) ∈ insideExt e

@[expose] def SplitAPlaneInput : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {B E : Subgroup G} {x : G} {L D J : Subgroup G}
    {N : ℕ} {y : G} {K : Subgroup G},
    GGQTwoSetting 3 B E x L D J → GGQTwoI1 E D J → GGNbr 3 B x D J y K →
      GGQ2S08RowA 3 N K J → (N = 6 ∨ N = 9) →
        ∃ t, Nonempty (SplitPlaneRealization E K N t)

theorem SplitPlaneRealization.mem_of_centralizes_of_K1
    {G : Type} [Group G] {E K : Subgroup G} {N t : ℕ}
    (d : SplitPlaneRealization E K N t) (h3 : 3 ∣ N) (y : E)
    (hcent : (y : G) ∈ Subgroup.centralizer (K : Set G))
    (hK1 : ∀ b : E, (b : G) ∈ Subgroup.centralizer (K : Set G) →
      (b : G) ∈ Subgroup.zpowers (y : G)) :
    (y : G) ∈ K := by
  rw [d.inside_eq y]
  refine scalarLine_inside d.nonzero ?_ ?_ ?_
  · exact (d.cent_eq y).mp hcent
  · rw [d.support_card]; exact h3
  · intro w hw
    set b : E := Additive.toMul (d.coord.symm w) with hb
    have hcoord : d.coord (Additive.ofMul b) = w := by simp [hb]
    have hbcent : (b : G) ∈ Subgroup.centralizer (K : Set G) :=
      (d.cent_eq b).mpr (by rw [hcoord]; exact hw)
    obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp (hK1 b hbcent)
    refine ⟨(z : F), ?_⟩
    have hb_eq : y ^ z = b := by
      apply Subtype.ext
      simpa using hz
    calc w = d.coord (Additive.ofMul b) := hcoord.symm
      _ = d.coord (Additive.ofMul (y ^ z)) := by rw [hb_eq]
      _ = d.coord (z • Additive.ofMul y) := by rw [ofMul_zpow]
      _ = z • d.coord (Additive.ofMul y) := map_zsmul d.coord z _
      _ = (z : F) • d.coord (Additive.ofMul y) :=
            (Int.cast_smul_eq_zsmul (R := F) z _).symm

theorem ggQ2s08_normalizer_le_of_splitAPlaneInput
    (hSplit : SplitAPlaneInput) (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {B E : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B E x L D J) (hI1 : GGQTwoI1 E D J)
    {N : ℕ} {y : G} {K : Subgroup G} (hnbr : GGNbr 3 B x D J y K)
    (hrow : GGQ2S08RowA 3 N K J) (hN : N = 6 ∨ N = 9) (hyK : y ∉ K) :
    Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (ggG0 3 B x L D J : Set G) := by
  have hK1 := ggQ2_K1_of_I1 hLB hP hS.1 hI1
  obtain ⟨t, ⟨d⟩⟩ := hSplit hS hI1 hnbr hrow hN
  have h3 : 3 ∣ N := by rcases hN with rfl | rfl <;> decide
  have hyE : y ∈ E := hS.1.1.2.1.1 hnbr.1.2.1
  have hcent : (y : G) ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact ((Subgroup.mem_centralizer_iff.mp (hnbr.1.2.2.2.1 hk)) y
      (Set.mem_singleton y)).symm
  have hK1' : ∀ b : E, (b : G) ∈ Subgroup.centralizer (K : Set G) →
      (b : G) ∈ Subgroup.zpowers (y : G) := by
    intro b hb
    refine hK1 y K hnbr b b.2 ?_
    have hbot : ⁅K, Subgroup.zpowers (b : G)⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.zpowers_le.mpr hb)
    rw [hbot]; exact bot_le
  exact (hyK (d.mem_of_centralizes_of_K1 h3 ⟨y, hyE⟩ hcent hK1')).elim

theorem ggQ2s08_rowA_three_false {G : Type} [Group G] {p : ℕ} {X J : Subgroup G}
    (hr : GGQ2S08RowA p 3 X J) : False := by
  obtain ⟨labX, labJ, -, hmJ, htJ, -, -, -, -, -, hN⟩ := hr
  have hrank : labJ.rank = 0 := by omega
  obtain ⟨lab, hlab, hlabJ, -⟩ := FrameRoute.ggFrameQTwo_exists_hasLabel hmJ
  rw [hlabJ] at hlab
  have h1 : 1 ≤ labJ.rank := by
    unfold LargeEvenInLambda2 at hlab
    rw [htJ] at hlab
    exact hlab.2.1
  omega

theorem ggQ2s08_cuKA_of_splitAPlaneInput
    (hSplit : SplitAPlaneInput) (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput) :
    GGQ2S08TNCellK GGQ2S08PosASmall := by
  intro G _ _ p _ hp B E x L D J hS hI1 y K hnbr hrow hyK
  subst hp
  obtain ⟨N, hN12, hrowA⟩ := hrow
  have hrowA' := hrowA
  obtain ⟨-, labJ, -, -, -, -, -, -, hpd, -, hNeq⟩ := hrowA'
  have h3N : 3 ∣ N := by rw [← hNeq]; exact hpd
  have hcases : N = 3 ∨ N = 6 ∨ N = 9 := by omega
  rcases hcases with h3 | h6 | h9
  · subst h3
    exact (ggQ2s08_rowA_three_false hrowA).elim
  · subst h6
    exact ggQ2s08_normalizer_le_of_splitAPlaneInput hSplit hLB hP hS hI1 hnbr hrowA
      (Or.inl rfl) hyK
  · subst h9
    exact ggQ2s08_normalizer_le_of_splitAPlaneInput hSplit hLB hP hS hI1 hnbr hrowA
      (Or.inr rfl) hyK

end

end CFSG.StandardType.GGQ2S08Split
