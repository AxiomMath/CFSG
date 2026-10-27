module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenGlueB
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KBlkStep
public import CFSG.RankThree.PartTwo.Sec10.Sec10XProofTen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtyOne

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

@[expose] def K_3D4CartanRank : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (n : ℕ), Is3D4 Y n →
    ∀ T : Subgroup Y, CFSG.QuasithinUnique.IsSylowTwoOf T ⊤ →
      IsMulCommutative (TauCeti.Subgroup.normalizerQuotient T) ∧
      ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ 2 ^ n - 1 →
        2 ≤ CFSG.pRank r (TauCeti.Subgroup.normalizerQuotient T)

private abbrev borelS (D : Data G) (L : Subgroup G) : Subgroup G := D.T ⊓ L

private abbrev borelB (D : Data G) (L : Subgroup G) : Subgroup G :=
  Subgroup.normalizer (borelS D L : Set G) ⊓ L

private theorem commutator_and_rank_borel_of_is3D4 (D : Data G) (hK : K_3D4CartanRank)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hN : (L.subgroupOf D.M).Normal) {n r : ℕ}
    (h3D4 : Is3D4 (Bar2 L) n) (hr : r.Prime) (hr2 : r ≠ 2) (hrd : r ∣ 2 ^ n - 1) :
    (∀ x y : ↥(borelB D L),
      ((x * y)⁻¹ * (y * x) : ↥(borelB D L)) ∈
        (borelS D L).subgroupOf (borelB D L)) ∧
    2 ≤ CFSG.Open.pRank r (borelB D L) := by
  classical
  have hLN : D.M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL.1.le).1 hN
  let S : Subgroup G := D.T ⊓ L
  have hSylS : CFSG.ABGLocalTools.IsSylowOf 2 S L :=
    CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer D.sylowM hL.1.le hLN
  let Q : Subgroup ↥L := CFSG.pCore 2 ↥L
  let Tbar : Subgroup (Bar2 L) := TwelveThirteen.barOf L S
  have hTbarsyl : CFSG.QuasithinUnique.IsSylowTwoOf Tbar ⊤ :=
    CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.mpr
      (TwelveThirteen.isSylowOf_barOf hSylS)
  obtain ⟨habK0, hrankK⟩ := hK (Bar2 L) n h3D4 Tbar hTbarsyl
  have habK : ∀ a b : TauCeti.Subgroup.normalizerQuotient Tbar, a * b = b * a :=
    fun a b => habK0.is_comm.comm a b
  have hrankK' : 2 ≤ CFSG.pRank r (TauCeti.Subgroup.normalizerQuotient Tbar) :=
    hrankK r hr hr2 hrd
  have hQsyl : CFSG.QuasithinUnique.IsSylowTwoOf D.T D.M :=
    CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.mpr D.sylowM
  have hQleS : Q ≤ S.subgroupOf L := by
    intro x hx
    have hxL : (x : G) ∈ pCoreOf 2 L := by
      have h1 : x ∈ (pCoreOf 2 L).subgroupOf L := by
        rwa [show Q = (pCoreOf 2 L).subgroupOf L from
          (CFSG.openPCoreOf_subgroupOf 2 L).symm] at hx
      exact Subgroup.mem_subgroupOf.mp h1
    rw [pCoreOf_eq_inf_of_mem_calC hL] at hxL
    rw [Subgroup.mem_subgroupOf]
    exact ⟨CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.pCoreOf_le_of_isSylowTwoOf hQsyl hxL.1,
      hxL.2⟩
  let B : Subgroup G := Subgroup.normalizer (S : Set G) ⊓ L
  have hSB : S ≤ B := le_inf Subgroup.le_normalizer inf_le_right
  have hS2 : IsPGroup 2 S := D.sylowM.isPGroup.to_le inf_le_left
  have hST : S ≤ D.T := inf_le_left
  have hTS : D.T ≤ Subgroup.normalizer (S : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxT, hxL⟩
      refine ⟨D.T.mul_mem (D.T.mul_mem ht hxT) (D.T.inv_mem ht), ?_⟩
      exact (Subgroup.mem_normalizer_iff.mp (hLN (D.sylowM.le ht)) x).mp hxL
    · rintro ⟨hxT, hxL⟩
      refine ⟨?_, (Subgroup.mem_normalizer_iff.mp (hLN (D.sylowM.le ht)) x).mpr hxL⟩
      have heq : x = t⁻¹ * (t * x * t⁻¹) * t := by group
      rw [heq]
      exact D.T.mul_mem (D.T.mul_mem (D.T.inv_mem ht) hxT) ht
  have hTB : D.T ≤ Subgroup.normalizer (B : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxN, hxL⟩
      exact ⟨(Subgroup.normalizer (S : Set G)).mul_mem
          ((Subgroup.normalizer (S : Set G)).mul_mem (hTS ht) hxN)
          ((Subgroup.normalizer (S : Set G)).inv_mem (hTS ht)),
        (Subgroup.mem_normalizer_iff.mp (hLN (D.sylowM.le ht)) x).mp hxL⟩
    · rintro ⟨hxN, hxL⟩
      refine ⟨?_, (Subgroup.mem_normalizer_iff.mp (hLN (D.sylowM.le ht)) x).mpr hxL⟩
      have heq : x = t⁻¹ * (t * x * t⁻¹) * t := by group
      rw [heq]
      exact (Subgroup.normalizer (S : Set G)).mul_mem
        ((Subgroup.normalizer (S : Set G)).mul_mem
          ((Subgroup.normalizer (S : Set G)).inv_mem (hTS ht)) hxN) (hTS ht)
  have : (S.subgroupOf B).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (H := B) (N := S) inf_le_left
  have hTbar_eq : Tbar = (S.subgroupOf L).map (QuotientGroup.mk' Q) := rfl
  have hpre : Tbar.comap (QuotientGroup.mk' Q) = S.subgroupOf L := by
    rw [hTbar_eq]
    exact Subgroup.comap_map_eq_self (f := QuotientGroup.mk' Q) (H := S.subgroupOf L) (by
      rw [QuotientGroup.ker_mk']
      exact hQleS)
  have hBnorm : ∀ b : ↥B, QuotientGroup.mk' Q ⟨b.1, (Subgroup.mem_inf.mp b.2).2⟩ ∈
      Subgroup.normalizer (Tbar : Set (Bar2 L)) := by
    intro b
    have hbN : (⟨b.1, (Subgroup.mem_inf.mp b.2).2⟩ : ↥L) ∈
        Subgroup.normalizer ((S.subgroupOf L : Subgroup ↥L) : Set ↥L) :=
      CFSG.RankThree.PartTwo.Sec10.Sec10XProof.mem_normalizer_subgroupOf_of_mem_normalizer
        (K := S) (H := L) (Subgroup.mem_inf.mp b.2).1
    have h := Subgroup.le_normalizer_map (QuotientGroup.mk' Q)
      (Subgroup.mem_map.mpr ⟨⟨b.1, (Subgroup.mem_inf.mp b.2).2⟩, hbN, rfl⟩)
    simpa [hTbar_eq] using h
  let toN : ↥B →* ↥(Subgroup.normalizer (Tbar : Set (Bar2 L))) :=
  { toFun := fun b => ⟨QuotientGroup.mk' Q ⟨b.1, (Subgroup.mem_inf.mp b.2).2⟩, hBnorm b⟩
    map_one' := Subtype.ext (map_one (QuotientGroup.mk' Q))
    map_mul' := fun a b => Subtype.ext
      (map_mul (QuotientGroup.mk' Q) ⟨a.1, (Subgroup.mem_inf.mp a.2).2⟩
        ⟨b.1, (Subgroup.mem_inf.mp b.2).2⟩) }
  let φ : ↥B →* TauCeti.Subgroup.normalizerQuotient Tbar :=
    (TauCeti.Subgroup.normalizerQuotientMk Tbar).comp toN
  have hφker : φ.ker = S.subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hb
      have hb' : QuotientGroup.mk' Q ⟨b.1, (Subgroup.mem_inf.mp b.2).2⟩ ∈ Tbar := by
        have h1 := (TauCeti.Subgroup.normalizerQuotientMk_eq_one_iff Tbar (toN b)).mp hb
        simpa [toN] using h1
      rw [hTbar_eq] at hb'
      obtain ⟨s, hs, hsm⟩ := Subgroup.mem_map.mp hb'
      have hdiv : (⟨b.1, (Subgroup.mem_inf.mp b.2).2⟩ / s : ↥L) ∈ Q := by
        have h1 : (QuotientGroup.mk' Q) (⟨b.1, (Subgroup.mem_inf.mp b.2).2⟩ / s) = 1 := by
          rw [map_div, div_eq_mul_inv]
          rw [← hsm]
          simp
        exact (QuotientGroup.eq_one_iff _).1 h1
      have hdivS : ((⟨b.1, (Subgroup.mem_inf.mp b.2).2⟩ / s : ↥L) : G) ∈ S :=
        Subgroup.mem_subgroupOf.mp (hQleS hdiv)
      have hsS : (s : G) ∈ S := Subgroup.mem_subgroupOf.mp hs
      have heq : (b.1 : G) = ((⟨b.1, (Subgroup.mem_inf.mp b.2).2⟩ / s : ↥L) : G) * (s : G) := by
        have h2 : (⟨b.1, (Subgroup.mem_inf.mp b.2).2⟩ : ↥L) =
            (⟨b.1, (Subgroup.mem_inf.mp b.2).2⟩ / s) * s := by
          apply Subtype.ext
          exact (div_mul_cancel (b.1 : G) (s : G)).symm
        exact congrArg Subtype.val h2
      rw [heq]
      exact S.mul_mem hdivS hsS
    · intro hb
      have hbT : QuotientGroup.mk' Q ⟨b.1, (Subgroup.mem_inf.mp b.2).2⟩ ∈ Tbar := by
        rw [hTbar_eq]
        exact Subgroup.mem_map.mpr ⟨⟨b.1, (Subgroup.mem_inf.mp b.2).2⟩, hb, rfl⟩
      have h1 : TauCeti.Subgroup.normalizerQuotientMk Tbar (toN b) = 1 :=
        (TauCeti.Subgroup.normalizerQuotientMk_eq_one_iff Tbar (toN b)).mpr (by
          simpa [toN] using hbT)
      simpa [φ] using h1
  have hφsurj : Function.Surjective φ := by
    intro y
    obtain ⟨n, rfl⟩ := TauCeti.Subgroup.normalizerQuotientMk_surjective Tbar y
    obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective Q (n : Bar2 L)
    have hlN : l ∈ Subgroup.normalizer ((S.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      refine Subgroup.eq_of_le_of_card_ge ?_ ?_
      · rintro _ ⟨x, hx, rfl⟩
        have hxT : (QuotientGroup.mk' Q) x ∈ Tbar := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
        have hnmem : (n : Bar2 L) ∈ Subgroup.normalizer (Tbar : Set (Bar2 L)) := n.2
        have h1 := (Subgroup.mem_normalizer_iff.mp hnmem ((QuotientGroup.mk' Q) x)).mp hxT
        rw [← hl] at h1
        rw [← hpre]
        simpa [MulAut.conj_apply, map_mul, map_inv] using h1
      · rw [Subgroup.card_map_of_injective (MulAut.conj l).injective]
    let b : ↥B := ⟨(l : G), Subgroup.mem_inf.mpr ⟨
      CFSG.RankThree.PartTwo.Sec10.Sec10XProof.mem_normalizer_of_mem_normalizer_subgroupOf
        (K := S) (H := L) inf_le_right hlN, l.2⟩⟩
    refine ⟨b, ?_⟩
    have htoN : toN b = n := by
      apply Subtype.ext
      exact hl
    simp only [φ, MonoidHom.comp_apply]
    rw [htoN]
  let e : (↥B ⧸ S.subgroupOf B) ≃* TauCeti.Subgroup.normalizerQuotient Tbar :=
    (QuotientGroup.quotientMulEquivOfEq hφker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφsurj)
  have hab : ∀ a b : ↥B ⧸ S.subgroupOf B, a * b = b * a := by
    intro a b
    apply e.injective
    rw [map_mul, map_mul, habK]
  have hrS : ¬ r ∣ Nat.card ↥(S.subgroupOf B) := by
    have hcard : Nat.card ↥(S.subgroupOf B) = Nat.card S :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSB).toEquiv
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hS2
    intro h
    have hr2k : r ∣ 2 ^ k := by rwa [hcard, hk] at h
    have hr2' : r ∣ 2 := hr.dvd_of_dvd_pow hr2k
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 hr2')
  have : Fact r.Prime := ⟨hr⟩
  have hrankB : 2 ≤ CFSG.Open.pRank r B := by
    have h1 : CFSG.Open.pRank r B = CFSG.Open.pRank r (⊤ : Subgroup B) :=
      CFSG.SectionRank.pRank_eq_pRank_top_subgroup B
    have h2 : CFSG.Open.pRank r (⊤ : Subgroup B) =
        CFSG.Open.pRank r (⊤ : Subgroup (↥B ⧸ S.subgroupOf B)) :=
      (CFSG.SectionRank.pRank_quotient_eq (S.subgroupOf B) hrS).symm
    have h3 : CFSG.Open.pRank r (⊤ : Subgroup (↥B ⧸ S.subgroupOf B)) =
        CFSG.Open.pRank r (⊤ : Subgroup (TauCeti.Subgroup.normalizerQuotient Tbar)) :=
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt e
    have h4 : CFSG.Open.pRank r
        (⊤ : Subgroup (TauCeti.Subgroup.normalizerQuotient Tbar)) =
        CFSG.pRank r (TauCeti.Subgroup.normalizerQuotient Tbar) :=
      (CFSG.SectionRank.pRank_eq_open_pRank_top r _).symm
    rw [h1, h2, h3, h4]
    exact hrankK'
  refine ⟨?_, hrankB⟩
  intro x y
  have hq : QuotientGroup.mk' (S.subgroupOf B) (x * y) =
      QuotientGroup.mk' (S.subgroupOf B) (y * x) := by
    rw [map_mul, map_mul]
    exact hab _ _
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hq
  simpa only [S, B, borelS, borelB] using (QuotientGroup.eq.mp hq)

theorem two_le_pRank_borel_of_is3D4 (D : Data G) (hK : K_3D4CartanRank) {L : Subgroup G}
    (hL : L ∈ calC D.M) (hN : (L.subgroupOf D.M).Normal) {n r : ℕ} (h3D4 : Is3D4 (Bar2 L) n)
    (hr : r.Prime) (hr2 : r ≠ 2) (hrd : r ∣ 2 ^ n - 1) :
    2 ≤ CFSG.Open.pRank r (Subgroup.normalizer ((D.T ⊓ L : Subgroup G) : Set G) ⊓ L) := by
  simpa only [borelB, borelS] using
    (commutator_and_rank_borel_of_is3D4 D hK hL hN h3D4 hr hr2 hrd).2

theorem seventeen_thirtytwo_n_even (D : Data G) {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    (h1 : R17_1At D V₀ V hV) (h891 : F08.R891 D) (hK : K_3D4CartanRank)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hN : (L.subgroupOf D.M).Normal)
    {n : ℕ} (h3D4 : Is3D4 (Bar2 L) n) (hnodd : ¬ Odd n) : False := by
  classical
  have heven : Even n := by
    rcases Nat.even_or_odd n with h | h
    · exact h
    · exact absurd h hnodd
  have h3dvd : 3 ∣ 2 ^ n - 1 := by
    obtain ⟨k, rfl⟩ := heven
    rw [← two_mul, pow_mul]
    simpa using Nat.sub_one_dvd_pow_sub_one 4 k
  have hk : D.k = 1 :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Data.k_eq_one_of_isStronglyPEmbedded D
      (h891 L hL n h3D4)
  have hLN : D.M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL.1.le).1 hN
  let S : Subgroup G := D.T ⊓ L
  let B : Subgroup G := Subgroup.normalizer (S : Set G) ⊓ L
  have hSB : S ≤ B := le_inf Subgroup.le_normalizer inf_le_right
  have hS2 : IsPGroup 2 S := D.sylowM.isPGroup.to_le inf_le_left
  have hST : S ≤ D.T := inf_le_left
  have hTS : D.T ≤ Subgroup.normalizer (S : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxT, hxL⟩
      refine ⟨D.T.mul_mem (D.T.mul_mem ht hxT) (D.T.inv_mem ht), ?_⟩
      exact (Subgroup.mem_normalizer_iff.mp (hLN (D.sylowM.le ht)) x).mp hxL
    · rintro ⟨hxT, hxL⟩
      refine ⟨?_, (Subgroup.mem_normalizer_iff.mp (hLN (D.sylowM.le ht)) x).mpr hxL⟩
      have heq : x = t⁻¹ * (t * x * t⁻¹) * t := by group
      rw [heq]
      exact D.T.mul_mem (D.T.mul_mem (D.T.inv_mem ht) hxT) ht
  have hTB : D.T ≤ Subgroup.normalizer (B : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxN, hxL⟩
      exact ⟨(Subgroup.normalizer (S : Set G)).mul_mem
          ((Subgroup.normalizer (S : Set G)).mul_mem (hTS ht) hxN)
          ((Subgroup.normalizer (S : Set G)).inv_mem (hTS ht)),
        (Subgroup.mem_normalizer_iff.mp (hLN (D.sylowM.le ht)) x).mp hxL⟩
    · rintro ⟨hxN, hxL⟩
      refine ⟨?_, (Subgroup.mem_normalizer_iff.mp (hLN (D.sylowM.le ht)) x).mpr hxL⟩
      have heq : x = t⁻¹ * (t * x * t⁻¹) * t := by group
      rw [heq]
      exact (Subgroup.normalizer (S : Set G)).mul_mem
        ((Subgroup.normalizer (S : Set G)).mul_mem
          ((Subgroup.normalizer (S : Set G)).inv_mem (hTS ht)) hxN) (hTS ht)
  have : (S.subgroupOf B).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (H := B) (N := S) inf_le_left
  have hcomm := (commutator_and_rank_borel_of_is3D4 D hK hL hN h3D4
    Nat.prime_three (by norm_num) h3dvd).1
  have hab : ∀ a b : ↥B ⧸ S.subgroupOf B, a * b = b * a := by
    intro a b
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (S.subgroupOf B) a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (S.subgroupOf B) b
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    simpa only [S, B, borelS, borelB] using hcomm x y
  have hrankB : 2 ≤ CFSG.Open.pRank 3 B := by
    have h := two_le_pRank_borel_of_is3D4 D hK hL hN h3D4
      Nat.prime_three (by norm_num) h3dvd
    simpa only [S, B] using h
  obtain ⟨E, hEB, hEel, hEcard, hEperm⟩ :=
    CFSG.GroupTheory.exists_elemAbelian_permutes_of_abelian_quotient
      (B := B) (S := S) (T := D.T) hab hSB hST hTB hTS
      Nat.prime_three (by norm_num) hS2
  have hErank : 2 ≤ CFSG.Open.pRank 3 E := by
    have h := CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian Nat.prime_three hEel
    rw [hEcard] at h
    have hEq : CFSG.Open.pRank 3 B = CFSG.Open.pRank 3 E :=
      Nat.pow_right_injective (by norm_num : 2 ≤ 3) h
    omega
  exact false_of_permuting_elemAbelian_rank_two_of_k_one h1 hk
    (hEB.trans (inf_le_right.trans hL.1.le)) hEel hEperm hErank

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
