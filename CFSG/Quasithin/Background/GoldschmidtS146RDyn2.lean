module

public import CFSG.Quasithin.Background.GoldschmidtS146RDyn
public import CFSG.Quasithin.Background.GoldschmidtS146RA6
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinRed
public import CFSG.Quasithin.Background.A1cTransferVariants
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.G10Four
public import CFSG.Quasithin.Background.G10Three
public import CFSG.Quasithin.Background.G2Relaxed
public import CFSG.Quasithin.Background.G9Stmts
public import CFSG.Quasithin.Background.GoldschmidtS146RArithDefs
public import CFSG.Quasithin.Background.GoldschmidtS146RCases
public import CFSG.Quasithin.Background.GoldschmidtS146RIdent
public import CFSG.Quasithin.Background.GoldschmidtS146RProper
public import CFSG.Quasithin.EmptyFaithful.S143EB
public import CFSG.Quasithin.EmptyFaithful.S143VFin
public import CFSG.Quasithin.EmptyFaithful.S143VG94
public import CFSG.Quasithin.EmptyFaithful.S143VQG
public import CFSG.Quasithin.EmptyFaithful.S143VTwo
public import CFSG.Quasithin.EmptyFaithful.S143VZU
public import CFSG.Quasithin.EmptyFaithful.S143WAL
public import CFSG.Quasithin.EmptyFaithful.S143WCl
public import CFSG.Quasithin.EmptyFaithful.S143WE
public import CFSG.Quasithin.EmptyFaithful.S143WFin
public import CFSG.Quasithin.EmptyFaithful.S143WNo
public import CFSG.Quasithin.EmptyFaithful.S143WT
public import CFSG.Quasithin.EmptyFaithful.S146F4
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabInputs
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.Timmesfeld.Orders.Classical
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.Quasithin.GoldS146R

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

section A6

variable {G : Type} [Group G] [Finite G] {H J K T : Subgroup G} [(J.subgroupOf H).Normal]

theorem kbarFusesThrees_of_not_normalizer {P : Subgroup (↥H ⧸ J.subgroupOf H)} (hKH : K ≤ H)
    (hTH : T ≤ H) (hTK : T ≤ Subgroup.normalizer (K : Set G)) (hOJ : pCoreOf 2 K ≤ J)
    (hKJ : K ⊓ J = pCoreOf 2 K) (hsyl : IsSylowTwoOf (imgJ H J (T ⊓ K)) (imgJ H J K))
    (hA6 : IsAlt 6 ↥(imgJ H J K))
    (hPB : imgJ H J K ⊓ Subgroup.normalizer ((imgJ H J (T ⊓ K) : Subgroup (↥H ⧸ J.subgroupOf H)) :
      Set (↥H ⧸ J.subgroupOf H)) ≤ P) (hPK : P ≤ imgJ H J K) (hPne : P ≠ imgJ H J K)
    (hPmax : ∀ Q : Subgroup (↥H ⧸ J.subgroupOf H), Q ≤ imgJ H J K → Q ≠ imgJ H J K → P ≤ Q →
      Q = P)
    {t : G} (ht : t ∈ T) (hnot : ((⟨t, hTH ht⟩ : ↥H) : ↥H ⧸ J.subgroupOf H) ∉
      Subgroup.normalizer (P : Set (↥H ⧸ J.subgroupOf H))) : KbarFusesThrees K t := by
  have : Finite (↥H ⧸ J.subgroupOf H) := inferInstance
  set tb : ↥H ⧸ J.subgroupOf H := ((⟨t, hTH ht⟩ : ↥H) : ↥H ⧸ J.subgroupOf H) with htb
  have htN : (⟨t, hTH ht⟩ : ↥H).1 ∈ Subgroup.normalizer (K : Set G) := hTK ht
  have htN' : (⟨t, hTH ht⟩ : ↥H).1 ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ht, hTK ht⟩
  have hnormiff : ∀ {X : Subgroup G}, (⟨t, hTH ht⟩ : ↥H).1 ∈ Subgroup.normalizer (X : Set G) →
      X ≤ H → tb ∈ Subgroup.normalizer ((imgJ H J X : Subgroup (↥H ⧸ J.subgroupOf H)) :
        Set (↥H ⧸ J.subgroupOf H)) := by
    intro X hX hXH
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · intro hq
      exact conj_mem_imgJ (J := J) (g := ⟨t, hTH ht⟩) hX hq
    · intro hq
      have hinv : ((⟨t, hTH ht⟩ : ↥H)⁻¹ : ↥H).1 ∈ Subgroup.normalizer (X : Set G) := by
        simpa using (Subgroup.normalizer (X : Set G)).inv_mem hX
      have h1 := conj_mem_imgJ (J := J) (g := (⟨t, hTH ht⟩ : ↥H)⁻¹) hinv hq
      have h2 : tb⁻¹ * (tb * q * tb⁻¹) * tb = q := by group
      have h1' : tb⁻¹ * (tb * q * tb⁻¹) * tb ∈ imgJ H J X := by
        simpa [htb, QuotientGroup.mk_inv] using h1
      rwa [h2] at h1'
  obtain ⟨x, hxK, hx3, hx1, hxk⟩ := a6_swap (X := imgJ H J K) (U := imgJ H J (T ⊓ K)) (P := P)
    hA6 hsyl hPK hPne hPmax
    (fun u hu => hPB ⟨imgJ_mono inf_le_right hu, Subgroup.le_normalizer hu⟩)
    (hnormiff htN hKH) (hnormiff htN' (inf_le_right.trans hKH)) hnot
  obtain ⟨h, hhK, rfl⟩ := mem_imgJ.mp hxK
  refine ⟨(h : G), hhK, ?_, ?_, ?_⟩
  · have h1 : (((h : ↥H) ^ 3 : ↥H) : ↥H ⧸ J.subgroupOf H) = 1 := by
      rw [QuotientGroup.mk_pow]
      exact hx3
    have h2 := (QuotientGroup.eq_one_iff _).mp h1
    have h3 : (h : G) ^ 3 ∈ J := by simpa [Subgroup.mem_subgroupOf] using h2
    have h4 : (h : G) ^ 3 ∈ K := pow_mem hhK 3
    rw [← hKJ]
    exact ⟨h4, h3⟩
  · intro hmem
    have hJ : (h : G) ∈ J := hOJ hmem
    have h1 : ((h : ↥H) : ↥H ⧸ J.subgroupOf H) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hJ)
    exact hx1 h1
  · intro k hk hmem
    have hJ : (k * (h : G) * k⁻¹)⁻¹ * (t * (h : G) * t⁻¹) ∈ J := hOJ hmem
    have hkH : k ∈ H := hKH hk
    let kH : ↥H := ⟨k, hkH⟩
    let tH : ↥H := ⟨t, hTH ht⟩
    let w : ↥H := (kH * h * kH⁻¹)⁻¹ * (tH * h * tH⁻¹)
    have hw : (w : G) = (k * (h : G) * k⁻¹)⁻¹ * (t * (h : G) * t⁻¹) := by simp [w, kH, tH]
    have h1 : (w : ↥H ⧸ J.subgroupOf H) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr (hw ▸ hJ))
    have h2 : (w : ↥H ⧸ J.subgroupOf H) =
        (((kH : ↥H) : ↥H ⧸ J.subgroupOf H) * ((h : ↥H) : ↥H ⧸ J.subgroupOf H) *
          ((kH : ↥H) : ↥H ⧸ J.subgroupOf H)⁻¹)⁻¹ *
          (((tH : ↥H) : ↥H ⧸ J.subgroupOf H) * ((h : ↥H) : ↥H ⧸ J.subgroupOf H) *
          ((tH : ↥H) : ↥H ⧸ J.subgroupOf H)⁻¹) := by
      simp only [w, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [h2] at h1
    exact hxk ((kH : ↥H) : ↥H ⧸ J.subgroupOf H) (mem_imgJ.mpr ⟨kH, hk, rfl⟩)
      (inv_mul_eq_one.mp h1)

end A6

section Glue

variable {G : Type} [Group G] [Finite G] {T M K : Subgroup G}

theorem Ctx146.inf_kerIn (c : Ctx146 T M K) :
    K ⊓ kerIn ((K ⊔ T) ⊓ M) (K ⊔ T) = pCoreOf 2 K := by
  have hJH : kerIn ((K ⊔ T) ⊓ M) (K ⊔ T) ≤ K ⊔ T := kerIn_le.trans inf_le_left
  have hOJ : pCoreOf 2 K ≤ kerIn ((K ⊔ T) ⊓ M) (K ⊔ T) :=
    (A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp c.comp)).trans
      (pCoreOf_le_kerIn c c.sylow)
  have hKJ : ¬ K ≤ kerIn ((K ⊔ T) ⊓ M) (K ⊔ T) := by
    intro h
    apply c.htm.2
    exact sup_le (h.trans (kerIn_le.trans inf_le_right)) c.le_M
  exact inf_eq_pCoreOf_of_simple c.le_H hJH hOJ hKJ c.simple

theorem not_two_pow_of_dvd_three {k c : ℕ} (hc : 3 ∣ c) (h : 2 ^ k = c) : False := by
  have h3 : 3 ∣ 2 ^ k := h ▸ hc
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

local notation "Jk" => kerIn ((K ⊔ T) ⊓ M) (K ⊔ T)

theorem dynkin_of_diag (c : Ctx146 T M K)
    (hKs : IsPSL 3 2 1 ↥(E2.star ((K ⊔ T) ⊓ M) (K ⊔ T) K) ∨
      IsAlt 6 ↥(E2.star ((K ⊔ T) ⊓ M) (K ⊔ T) K))
    (hdiag : E2.IsDiagramNontrivial (E2.star ((K ⊔ T) ⊓ M) (K ⊔ T) T)
      (E2.star ((K ⊔ T) ⊓ M) (K ⊔ T) K) (E2.star ((K ⊔ T) ⊓ M) (K ⊔ T) (T ⊓ K))) :
    (KbarIsL3Two K ∨ KbarIsA6 K) ∧
      ∃ s ∈ T ⊓ Subgroup.normalizer (K : Set G), KbarNontrivialOnDynkin K s := by
  have hKJ := c.inf_kerIn
  have hOJ : pCoreOf 2 K ≤ Jk := by
    rw [← hKJ]
    exact inf_le_right
  obtain ⟨e⟩ := nonempty_kbar_equiv_imgJ (J := Jk) c.le_H hKJ
  have hsyl : IsSylowTwoOf (imgJ (K ⊔ T) Jk (T ⊓ K)) (imgJ (K ⊔ T) Jk K) :=
    isSylowTwoOf_imgJ_sub c.le_H c.sylow_inf (by rw [hKJ]; exact c.pCore_le)
  have hsimpKs : IsSimpleGroup ↥(imgJ (K ⊔ T) Jk K) := by
    have := c.simple
    exact e.symm.isSimpleGroup
  have hcard : Nat.card ↥(imgJ (K ⊔ T) Jk K) = 168 ∨ Nat.card ↥(imgJ (K ⊔ T) Jk K) = 360 := by
    rcases hKs with h | h
    · exact Or.inl (card_of_isPSL_three_two h)
    · exact Or.inr (card_of_isAlt_six h)
  have hTKsK : imgJ (K ⊔ T) Jk (T ⊓ K) ≤ imgJ (K ⊔ T) Jk K := imgJ_mono inf_le_right
  have hne : ¬ imgJ (K ⊔ T) Jk K ≤ Subgroup.normalizer ((imgJ (K ⊔ T) Jk (T ⊓ K) :
      Subgroup (↥(K ⊔ T) ⧸ (Jk).subgroupOf (K ⊔ T))) :
      Set (↥(K ⊔ T) ⧸ (Jk).subgroupOf (K ⊔ T))) := by
    intro h
    have hnorm := (Subgroup.normal_subgroupOf_iff_le_normalizer hTKsK).mpr h
    rcases hsimpKs.eq_bot_or_eq_top_of_normal
      ((imgJ (K ⊔ T) Jk (T ⊓ K)).subgroupOf (imgJ (K ⊔ T) Jk K)) with h0 | h1
    · have h2 : ¬ 2 ∣ ((imgJ (K ⊔ T) Jk (T ⊓ K)).subgroupOf (imgJ (K ⊔ T) Jk K)).index :=
        hsyl.2.2
      rw [h0, Subgroup.index_bot] at h2
      omega
    · have h2 := Subgroup.subgroupOf_eq_top.mp h1
      have h3 : imgJ (K ⊔ T) Jk (T ⊓ K) = imgJ (K ⊔ T) Jk K := le_antisymm hTKsK h2
      obtain ⟨k, hk⟩ := (hsyl.2.1.of_equiv (MulEquiv.subgroupCongr h3)).exists_card_eq
      rcases hcard with h4 | h4
      · exact not_two_pow_of_dvd_three (by omega) (hk.symm.trans h4)
      · exact not_two_pow_of_dvd_three (by omega) (hk.symm.trans h4)
  obtain ⟨P, hPmax, hPB, hPK, hPmax'⟩ := exists_isMaxParabolic2 hsyl hne
  have hnot := hdiag P hPmax hPB
  obtain ⟨x, hxTs, hxN⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  obtain ⟨hx, hxT, rfl⟩ := mem_imgJ.mp hxTs
  have hTH : T ≤ K ⊔ T := le_sup_right
  rcases hKs with hKs | hKs
  · have hL3 : KbarIsL3Two K :=
      isPSL_three_two_iff.mp (CFSG.SectionRank.statedClassicalModel_of_mulEquiv e hKs)
    have hOuter := inducesOuter_of_not_normalizer c.le_H hTH c.norm hOJ hPB hPK hxT hxN
    exact ⟨Or.inl hL3, hx, ⟨hxT, c.norm hxT⟩, Or.inl ⟨hL3, hOuter⟩⟩
  · have hA6 : KbarIsA6 K := by
      obtain ⟨e'⟩ := hKs
      exact ⟨e.trans e'⟩
    have hF := kbarFusesThrees_of_not_normalizer c.le_H hTH c.norm hOJ hKJ hsyl hKs hPB hPK
      hPmax.2.1 hPmax' hxT hxN
    exact ⟨Or.inr hA6, hx, ⟨hxT, c.norm hxT⟩, Or.inr ⟨hA6, hF⟩⟩

end Glue

end CFSG.Quasithin.GoldS146R
