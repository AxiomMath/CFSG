module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.StatementsNineFifteen
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20d
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214c
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22l
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846g
public import CFSG.Adapters.LieModelOrders
public import CFSG.Adapters.StatedPSLTwo
public import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
public import CFSG.Blueprint.LieModelAPI
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21k

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem not_dvd_center_and_dvd_of_mem_conjSetOf {M L : Subgroup G} (hL : L ∈ calC M)
    {r : ℕ} (hZ : ¬ r ∣ Nat.card (center (Bar2 L))) (hrL : r ∣ Nat.card (Bar2 L))
    {K : Subgroup G} (hK : K ∈ conjSetOf M L) :
    (¬ r ∣ Nat.card (center (Bar2 K))) ∧ r ∣ Nat.card (Bar2 K) := by
  obtain ⟨g, -, hKg⟩ := hK
  constructor
  · rw [hKg, CFSG.LocalAnalysis.UniquenessCase.UC6S846.card_center_bar2_map]
    exact hZ
  · rw [hKg]
    have hcard : Nat.card (Bar2 (L.map (MulAut.conj g).toMonoidHom)) =
        Nat.card (Bar2 L) :=
      (Nat.card_congr (CFSG.LocalAnalysis.UniquenessCase.UC6S846.bar2Equiv
        (Subgroup.equivMapOfInjective L (MulAut.conj g).toMonoidHom
          (MulAut.conj g).injective)).toEquiv).symm
    rw [hcard]
    exact hrL

private theorem exists_barImage_pow_eq_one_not_center {M L : Subgroup G} (hL : L ∈ calC M)
    {r : ℕ} (hr : r.Prime) (hZ : ¬ r ∣ Nat.card (center (Bar2 L)))
    (hrL : r ∣ Nat.card (Bar2 L)) {K : Subgroup G} (hK : K ∈ conjSetOf M L) :
    ∃ z ∈ barImage M K, z ^ r = 1 ∧ ∃ a ∈ barImage M K, a * z ≠ z * a := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨hZK, hrK⟩ := not_dvd_center_and_dvd_of_mem_conjSetOf hL hZ hrL hK
  obtain ⟨y, hyord⟩ := exists_prime_orderOf_dvd_card' (G := Bar2 K) r hrK
  have hyZ : y ∉ Subgroup.center (Bar2 K) := by
    intro hyZ
    apply hZK
    have hle : Subgroup.zpowers y ≤ Subgroup.center (Bar2 K) := Subgroup.zpowers_le.mpr hyZ
    have hdvd := Subgroup.card_dvd_of_le hle
    rwa [Nat.card_zpowers, hyord] at hdvd
  obtain ⟨c, hc⟩ := QuotientGroup.mk_surjective y
  have hcp : (QuotientGroup.mk c : Bar2 K) ^ r = 1 := by
    rw [hc, ← hyord]
    exact pow_orderOf_eq_one _
  have hcz : (QuotientGroup.mk c : Bar2 K) ∉ Subgroup.center (Bar2 K) := by
    rw [hc]
    exact hyZ
  have hKC : K ∈ calC M := uc22p2214_calC_of_mem_conjSetOf hL hK
  let z : Bar2 M := QuotientGroup.mk (Subgroup.inclusion hKC.1.le c)
  have hzmem : z ∈ barImage M K :=
    Subgroup.mem_map.2 ⟨Subgroup.inclusion hKC.1.le c,
      Subgroup.mem_subgroupOf.2 c.2, rfl⟩
  exact ⟨z, hzmem, uc22p20d_image_props hKC.1.le hKC.1 c hcp hcz⟩

private theorem exists_elemAbelian_card_pow_ncard {M L : Subgroup G} (hL : L ∈ calC M)
    {r : ℕ} (hr : r.Prime) (hZ : ¬ r ∣ Nat.card (center (Bar2 L)))
    (hrL : r ∣ Nat.card (Bar2 L)) :
    ∃ E : Subgroup (Bar2 M), IsElemAbelian r E ∧
      Nat.card E = r ^ (conjSetOf M L).ncard := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  letI : Fintype (conjSetOf M L) := Fintype.ofFinite _
  let e : Fin (Fintype.card (conjSetOf M L)) ≃ conjSetOf M L :=
    (Fintype.equivFin (conjSetOf M L)).symm
  let A : Fin (Fintype.card (conjSetOf M L)) → Subgroup (Bar2 M) :=
    fun i => barImage M (e i : Subgroup G)
  have hKC : ∀ K : conjSetOf M L, (K : Subgroup G) ∈ calC M :=
    fun K => uc22p2214_calC_of_mem_conjSetOf hL K.2
  choose z hzmem hzprops using fun K : conjSetOf M L =>
    exists_barImage_pow_eq_one_not_center hL hr hZ hrL K.2
  let x : Fin (Fintype.card (conjSetOf M L)) → Bar2 M := fun i => z (e i)
  have hcomm : ∀ i j : Fin (Fintype.card (conjSetOf M L)), i ≠ j →
      ∀ a ∈ A i, ∀ b ∈ A j, a * b = b * a := by
    intro i j hij a ha b hb
    have hne : (e i : Subgroup G) ≠ (e j : Subgroup G) := by
      intro h
      exact hij (e.injective (Subtype.ext h))
    exact uc22p22l_barImage_commute (hKC (e i)) (hKC (e j)) hne a ha b hb
  obtain ⟨E, -, hEea, hEcard⟩ :=
    uc22p20d_elemAbelian_of_commuting (X := Bar2 M) r (Fintype.card (conjSetOf M L)) hr A x
      hcomm (fun i => hzmem (e i)) (fun i => (hzprops (e i)).1)
      (fun i => (hzprops (e i)).2)
  have hcard : Fintype.card (conjSetOf M L) = (conjSetOf M L).ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  rw [hcard] at hEcard
  exact ⟨E, hEea, hEcard⟩

theorem ncard_conjSetOf_le_pRank {M L : Subgroup G} (hL : L ∈ calC M) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hZ : ¬ r ∣ Nat.card (center (Bar2 L)))
    (hrL : r ∣ Nat.card (Bar2 L)) :
    (conjSetOf M L).ncard ≤ CFSG.Open.pRank r M := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨E₀, hE₀ea, hE₀card⟩ := exists_elemAbelian_card_pow_ncard hL hr hZ hrL
  obtain ⟨E, -, hEea, hEcard⟩ :=
    uc22p20d_lift_elemAbelian (A := ↥M) (CFSG.pCore 2 ↥M) CFSG.pCore_isPGroup hr hr2
      (⊤ : Subgroup ↥M) E₀ hE₀ea hE₀card (by
        rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
        exact le_top)
  exact CFSG.SectionRank.le_pRank hr.one_lt (Subgroup.map_subtype_le E) (hEea.map M.subtype) (by
    rw [Subgroup.card_map_of_injective M.subtype_injective, hEcard])

private theorem sub_one_dvd_ordA_one_two_pow {n : ℕ} (hn : 1 ≤ n) :
    2 ^ n - 1 ∣ CFSG.Open.ordA 1 (2 ^ n) := by
  have hodd : Odd (2 ^ n - 1) :=
    Nat.Even.sub_odd (m := 2 ^ n) (n := 1) Nat.one_le_two_pow
      (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
  have hg : Nat.gcd 2 (2 ^ n - 1) = 1 := Nat.coprime_two_left.mpr hodd
  unfold CFSG.Open.ordA
  rw [show 1 * (1 + 1) / 2 = 1 by rfl, pow_one,
    show Finset.Icc 2 (1 + 1) = {2} by rfl, Finset.prod_singleton,
    show (1 + 1 : ℕ) = 2 by rfl, hg, Nat.div_one]
  exact dvd_mul_of_dvd_right (by simpa using Nat.sub_dvd_pow_sub_pow (2 ^ n) 1 2) _

theorem s21_15Rank_of (D : Data G) (Ch : Choice2011 G) : S21_15Rank D Ch := by
  intro h1930 c L hL n hshape r hr hr2 hrdvd
  haveI : Fact r.Prime := ⟨hr⟩
  have hZ : ¬ r ∣ Nat.card (center (Bar2 L)) := by
    haveI : IsSimpleGroup (Bar2 L) := by
      rcases hshape with hL2 | hSz
      · exact CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hL2
      · exact CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 hSz
    rw [uc22p21k_center_eq_bot hL.2.2, Subgroup.card_bot]
    exact hr.not_dvd_one
  have hrL : r ∣ Nat.card (Bar2 L) := by
    rcases hshape with hL2 | hSz
    · have hn1 : 1 ≤ n := hL2.admissible.2.1
      have hcard : Nat.card (Bar2 L) = CFSG.Open.ordA 1 (2 ^ n) := by
        simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using
          CFSG.Blueprint.LieModel.card_eq_lieOrd (X := Bar2 L) (n := 2) (p := 2) (f := n)
            (by norm_num) hL2
      rw [hcard]
      exact hrdvd.trans (sub_one_dvd_ordA_one_two_pow hn1)
    · have hSz' : CFSG.Blueprint.SuzukiModel (Bar2 L) 2 n :=
        (CFSG.Blueprint.LieModel.suzukiModel hSz).2
      unfold CFSG.Blueprint.SuzukiModel at hSz'
      obtain ⟨-, a, ha, K, hKfield, hKfinite, hn, hKcard, ⟨eK⟩⟩ := hSz'
      letI := hKfield
      letI := hKfinite
      have eSM : Bar2 L ≃* CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup a :=
        eK.trans (CFSG.ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup
          (a := a) (K := K) (by rw [hKcard, hn]))
      have hcard : Nat.card (Bar2 L) =
          ((2 ^ (2 * a + 1)) ^ 2 + 1) * (2 ^ (2 * a + 1)) ^ 2 *
            (2 ^ (2 * a + 1) - 1) := by
        rw [Nat.card_congr eSM.toEquiv]
        exact CFSG.SectionRank.card_suzukiMatrixGroup (m := a) (by omega)
      have hfac : 2 ^ n - 1 ∣ Nat.card (Bar2 L) := by
        rw [hcard, hn]
        refine ⟨((2 ^ (2 * a + 1)) ^ 2 + 1) * (2 ^ (2 * a + 1)) ^ 2, ?_⟩
        ring
      exact hrdvd.trans hfac
  exact ncard_conjSetOf_le_pRank hL hr hr2 hZ hrL

end CFSG.LocalAnalysis.UniquenessCase.UC22
