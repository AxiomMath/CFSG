module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight63General
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight63J2Tits
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.SylowInfCenter
public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersRee

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSpor Bar2)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Blueprint (LieModel)

private theorem card_bar2_of_isSpor_bar2_J2
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (h : IsSpor (Bar2 L) .J2) :
    Nat.card (Bar2 L) = 604800 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.Sporadic.J2.card_J2

private theorem factorization_five_card_bar2_of_isSpor_bar2_J2
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (h : IsSpor (Bar2 L) .J2) :
    (Nat.card (Bar2 L)).factorization 5 = 2 := by
  rw [card_bar2_of_isSpor_bar2_J2 h]
  have hb5a : 5 ^ 2 ∣ (604800 : ℕ) := by norm_num
  have hb5b : ¬ 5 ^ 3 ∣ (604800 : ℕ) := by norm_num
  have hn0 : (604800 : ℕ) ≠ 0 := by norm_num
  have hle : 2 ≤ (604800 : ℕ).factorization 5 :=
    (Nat.prime_five.pow_dvd_iff_le_factorization (k := 2) hn0).mp hb5a
  have hlt : (604800 : ℕ).factorization 5 < 3 := by
    by_contra hge
    exact hb5b ((Nat.prime_five.pow_dvd_iff_le_factorization (k := 3) hn0).mpr (by omega))
  omega

theorem factorization_five_card_of_isSpor_bar2_J2
    {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (h : IsSpor (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 L) .J2) :
    (Nat.card ↥L).factorization 5 = 2 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let O : Subgroup ↥L := CFSG.pCore 2 ↥L
  have hπ : Function.Surjective (QuotientGroup.mk' O) := QuotientGroup.mk'_surjective O
  have hcardmul : Nat.card O * Nat.card (Bar2 L) = Nat.card ↥L := by
    have hh := Subgroup.card_ker_mul_card_of_surjective (f := QuotientGroup.mk' O) hπ
    simpa [O, Bar2, QuotientGroup.ker_mk'] using hh
  have hO2 : IsPGroup 2 O := CFSG.pCore_isPGroup
  obtain ⟨n, hn⟩ := hO2.exists_card_eq
  have h5O : ¬ 5 ∣ Nat.card O := by
    rw [hn]
    intro h5
    have h52 : (5 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_five h5
    norm_num at h52
  have hfacO : (Nat.card O).factorization 5 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd h5O
  have hfacB : (Nat.card (Bar2 L)).factorization 5 = 2 :=
    factorization_five_card_bar2_of_isSpor_bar2_J2 h
  have hO0 : Nat.card O ≠ 0 := Nat.card_pos.ne'
  have hB0 : Nat.card (Bar2 L) ≠ 0 := Nat.card_pos.ne'
  rw [← hcardmul, Nat.factorization_mul hO0 hB0, Finsupp.add_apply, hfacO, hfacB, zero_add]

private theorem isElemAbelian_five_sylow_of_isSpor_bar2_J2
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (h : IsSpor (Bar2 L) .J2)
    (Q : Sylow 5 ↥L) :
    CFSG.Open.IsElemAbelian 5 (Q : Subgroup ↥L) ∧ Nat.card Q = 25 := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let O : Subgroup ↥L := CFSG.pCore 2 ↥L
  let π : ↥L →* Bar2 L := QuotientGroup.mk' O
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective O
  have hfacL : (Nat.card ↥L).factorization 5 = 2 :=
    factorization_five_card_of_isSpor_bar2_J2 h
  have hQcard : Nat.card Q = 25 := by
    rw [Sylow.card_eq_multiplicity, hfacL]
    norm_num
  have hO2 : IsPGroup 2 π.ker := by
    rw [show π.ker = O from QuotientGroup.ker_mk' O]
    exact CFSG.pCore_isPGroup
  have hQdisj : (Q : Subgroup ↥L) ⊓ π.ker = ⊥ :=
    disjoint_iff.mp (IsPGroup.disjoint_of_ne 5 2 (by norm_num)
      (Q : Subgroup ↥L) π.ker Q.isPGroup' hO2)
  have hinj : Function.Injective (π.subgroupMap (Q : Subgroup ↥L)) := by
    intro x y hxy
    have hxy' : π (x : ↥L) = π (y : ↥L) := by
      simpa using congrArg (fun z : ↥((Q : Subgroup ↥L).map π) => (z : Bar2 L)) hxy
    apply Subtype.ext
    have hmem : ((x : ↥L)⁻¹ * (y : ↥L)) ∈ (Q : Subgroup ↥L) ⊓ π.ker := by
      refine ⟨(Q : Subgroup ↥L).mul_mem ((Q : Subgroup ↥L).inv_mem x.2) y.2, ?_⟩
      show π ((x : ↥L)⁻¹ * (y : ↥L)) = 1
      rw [map_mul, map_inv, hxy', inv_mul_cancel]
    rw [hQdisj] at hmem
    exact eq_of_inv_mul_eq_one (Subgroup.mem_bot.mp hmem)
  let e : ↥Q ≃* ↥((Q : Subgroup ↥L).map π) :=
    MulEquiv.ofBijective (π.subgroupMap (Q : Subgroup ↥L))
      ⟨hinj, π.subgroupMap_surjective (Q : Subgroup ↥L)⟩
  have hQmap_card : Nat.card ((Q : Subgroup ↥L).map π) = 25 := by
    rw [← Nat.card_congr e.toEquiv]
    exact hQcard
  have hfacB : (Nat.card (Bar2 L)).factorization 5 = 2 :=
    factorization_five_card_bar2_of_isSpor_bar2_J2 h
  have hQmap_sylow : Nat.card ((Q : Subgroup ↥L).map π) =
      5 ^ (Nat.card (Bar2 L)).factorization 5 := by
    rw [hQmap_card, hfacB]
    norm_num
  obtain ⟨E, hEel, hEcard⟩ := exists_elemAbelian_five_two_of_isSpor_J2 h
  have hE_sylow : Nat.card E = 5 ^ (Nat.card (Bar2 L)).factorization 5 := by
    rw [hEcard, hfacB]
    norm_num
  let PE : Sylow 5 (Bar2 L) := Sylow.ofCard E hE_sylow
  let PQ : Sylow 5 (Bar2 L) := Sylow.ofCard ((Q : Subgroup ↥L).map π) hQmap_sylow
  haveI : Finite (Sylow 5 (Bar2 L)) :=
    Finite.of_injective (fun S : Sylow 5 (Bar2 L) => (S : Set (Bar2 L)))
      (fun S T h' => Sylow.ext (by
        ext x
        exact Set.ext_iff.mp h' x))
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Bar2 L) PE PQ
  have hsub : (PE : Subgroup (Bar2 L)).map (MulAut.conj g).toMonoidHom =
      (PQ : Subgroup (Bar2 L)) := by
    have h' := congrArg (fun S : Sylow 5 (Bar2 L) => (S : Subgroup (Bar2 L))) hg
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h'
    convert h' using 2
    ext x
    rfl
  have hsub' : E.map (MulAut.conj g).toMonoidHom = (Q : Subgroup ↥L).map π := by
    simpa [PE, PQ] using hsub
  have hQmap_el : CFSG.Open.IsElemAbelian 5 ((Q : Subgroup ↥L).map π) := by
    rw [← hsub']
    exact CFSG.SectionRank.isElemAbelian_map hEel (MulAut.conj g).toMonoidHom
  have hQel : CFSG.Open.IsElemAbelian 5 (Q : Subgroup ↥L) := by
    haveI : CFSG.IsElementaryAbelian 5 ↥(Q : Subgroup ↥L) :=
      CFSG.IsElementaryAbelian.of_mulEquiv e.symm hQmap_el.isElementaryAbelian
    exact CFSG.Open.isElemAbelian_of_isElementaryAbelian
  exact ⟨hQel, hQcard⟩

theorem not_five_dvd_card_outer_bar2_J2
    {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (h : IsSpor (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 L) .J2) :
    ¬ 5 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 L)) := by
  haveI : Finite (Bar2 L) :=
    Finite.of_surjective (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
      (QuotientGroup.mk'_surjective _)
  exact not_five_dvd_card_outer_of_isSpor_J2 h

theorem isElemAbelian_five_inf_sylow_of_isSpor_bar2_J2
    {G : Type} [Group G] [Finite G] {M L S : Subgroup G} (hLM : L ≤ M)
    (hLnorm : (L.subgroupOf M).Normal)
    (hS : CFSG.ABGLocalTools.IsSylowOf 5 S M)
    (hJ2 : IsSpor (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 L) .J2) :
    CFSG.Open.IsElemAbelian 5 (S ⊓ L) ∧ Nat.card ↥(S ⊓ L) = 25 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hMnormL : M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp hLnorm
  have hA : CFSG.ABGLocalTools.IsSylowOf 5 (S ⊓ L) L :=
    CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer hS hLM hMnormL
  obtain ⟨Q, hQ⟩ := hA.exists_sylow_eq_subgroupOf
  obtain ⟨hQel, hQcard⟩ := isElemAbelian_five_sylow_of_isSpor_bar2_J2 hJ2 Q
  have hmap : (Q : Subgroup ↥L).map L.subtype = S ⊓ L := by
    rw [hQ, Subgroup.map_subgroupOf_eq_of_le hA.le]
  refine ⟨?_, ?_⟩
  · rw [← hmap]
    exact CFSG.SectionRank.isElemAbelian_map hQel L.subtype
  · rw [← hmap, Subgroup.card_map_of_injective L.subtype_injective]
    exact hQcard

theorem false_of_isSpor_bar2_J2_of_bar
    {G : Type} [Group G] [Finite G] {M L S : Subgroup G}
    (h614 : CFSG.Yardstones.Mf4cdcdf2e013.Theorem614At M)
    (hsub : CFSG.Open.uniqueFourSigma M ⊆ CFSG.Yardstones.Mf4cdcdf2e013.SigmaOne4 G)
    (h5sig : 5 ∉ CFSG.Open.uniqueFourSigma M)
    (hnot : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 5 M)
    (hLM : L ≤ M) (hLnorm : (L.subgroupOf M).Normal)
    (hS : CFSG.ABGLocalTools.IsSylowOf 5 S M)
    (hJ2 : IsSpor (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 L) .J2)
    (hΓ : CFSG.Open.rankThreeGamma 1 5 (S ⊓ L) ≤ M) :
    False := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOut : ¬ 5 ∣ Nat.card
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer (Bar2 L)) :=
    not_five_dvd_card_outer_bar2_J2 hJ2
  have hA := isElemAbelian_five_inf_sylow_of_isSpor_bar2_J2 hLM hLnorm hS hJ2
  have hP5 : IsPGroup 5 ↥(S ⊓ L) :=
    IsPGroup.of_card (p := 5) (n := 2) (by rw [hA.2]; norm_num)
  have hO2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 L) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  have hSL : S ⊓ L ⊓ CFSG.Open.pCoreOf 2 L = ⊥ :=
    disjoint_iff.mp (IsPGroup.disjoint_of_ne 5 2 (by norm_num)
      (S ⊓ L) (CFSG.Open.pCoreOf 2 L) hP5 hO2)
  have hcomm : ∀ a b : ↥(S ⊓ L), a * b = b * a :=
    isMulCommutative_iff.mp hA.1.1
  have hSLab : ∀ x ∈ S ⊓ L, ∀ y ∈ S ⊓ L, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hcomm ⟨x, hx⟩ ⟨y, hy⟩)
  have hMnormL : M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp hLnorm
  have hSNL : S ≤ Subgroup.normalizer (L : Set G) := hS.le.trans hMnormL
  have hQnormP : ((S ⊓ L).subgroupOf S).Normal := by
    have h := normal_subgroupOf_inf_of_normal (P := S) hLM hLnorm hS.le
    rwa [inf_comm] at h
  have hQ : CFSG.ABGLocalTools.IsSylowOf 5 (S ⊓ L) L :=
    CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer hS hLM hMnormL
  have hInner : ∀ x ∈ S, ∃ l ∈ L, ∀ y ∈ L,
      (x * y * x⁻¹) * (l * y * l⁻¹)⁻¹ ∈ CFSG.Open.pCoreOf 2 L := by
    intro x hx
    exact exists_conj_of_not_dvd_outer x (hSNL hx)
      (hS.isPGroup.to_le (Subgroup.zpowers_le.mpr hx)) hOut
  have hdecomp : S ≤ (S ⊓ L) ⊔ centralizerBar S L :=
    le_sup_centralizerBar_of_inner_prime (P := S) (Q := S ⊓ L) (X := S)
      inf_le_left inf_le_right rfl hQnormP hQ hS.isPGroup hSNL le_rfl hInner
  exact false_of_abelian_sylow_of_bar (r := 5) (E := S ⊓ L)
    h614 hsub (by norm_num) (by norm_num) h5sig hnot hLM hLnorm hS hdecomp
    hSLab hSL le_rfl hA.1 (by rw [hA.2]; norm_num) hΓ

private theorem card_bar2_dvd_of_lieModel_bar2_tits
    {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (h : CFSG.Blueprint.LieModel (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 L) .Tits 0 2 1) :
    Nat.card (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 L) ∣ 35942400 := by
  have hree : CFSG.Blueprint.ReeTitsModel
      (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 L) .Tits 2 1 :=
    (CFSG.Blueprint.LieModel.reeTitsModel h (by decide)).2
  obtain ⟨⟨-, -, -, -, -⟩, a, hf, hmodel⟩ := hree
  obtain rfl : a = 0 := by omega
  obtain ⟨K, hKfield, hKfin, hKchar, hKcard, ⟨e⟩⟩ :=
    CFSG.EvenSmallLie.CatalogOrders.exists_mulEquiv_of_reeTitsRelationModel_F4 hmodel
  letI := hKfield
  letI := hKfin
  haveI := hKchar
  rw [pow_one] at hKcard
  rw [Nat.card_congr e.toEquiv]
  exact (Subgroup.card_quotient_dvd_card _).trans
    (CFSG.SectionRank.TitsOrder.Tits_commutator_card_dvd hKcard)

private theorem factorization_five_card_bar2_of_lieModel_bar2_tits
    {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (h : CFSG.Blueprint.LieModel (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 L) .Tits 0 2 1) :
    (Nat.card (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 L)).factorization 5 = 2 := by
  have hree : CFSG.Blueprint.ReeTitsModel
      (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 L) .Tits 2 1 :=
    (CFSG.Blueprint.LieModel.reeTitsModel h (by decide)).2
  have h25' : 25 ∣ Nat.card (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 L) :=
    CFSG.EvenSmallLie.CatalogOrders.twenty_five_dvd_card_of_reeTitsModel_Tits hree
  have h25 : 5 ^ 2 ∣ Nat.card (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 L) := by
    rw [show (5 : ℕ) ^ 2 = 25 by norm_num]
    exact h25' 
  have hdvd : Nat.card (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 L) ∣ 35942400 :=
    card_bar2_dvd_of_lieModel_bar2_tits h
  have hN0 : Nat.card (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 L) ≠ 0 := Nat.card_pos.ne'
  have hle : 2 ≤ (Nat.card (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 L)).factorization 5 :=
    (Nat.prime_five.pow_dvd_iff_le_factorization (k := 2) hN0).mp h25
  have hlt : (Nat.card (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 L)).factorization 5 < 3 := by
    by_contra hge
    have h125 : 5 ^ 3 ∣ Nat.card (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 L) :=
      (Nat.prime_five.pow_dvd_iff_le_factorization (k := 3) hN0).mpr (by omega)
    exact (by norm_num : ¬ 5 ^ 3 ∣ 35942400) (h125.trans hdvd)
  omega

theorem factorization_five_card_of_lieModel_bar2_tits
    {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (h : CFSG.Blueprint.LieModel (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 L) .Tits 0 2 1) :
    (Nat.card ↥L).factorization 5 = 2 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let O : Subgroup ↥L := CFSG.pCore 2 ↥L
  have hπ : Function.Surjective (QuotientGroup.mk' O) := QuotientGroup.mk'_surjective O
  have hcardmul : Nat.card O * Nat.card (Bar2 L) = Nat.card ↥L := by
    have hh := Subgroup.card_ker_mul_card_of_surjective (f := QuotientGroup.mk' O) hπ
    simpa [O, Bar2, QuotientGroup.ker_mk'] using hh
  have hO2 : IsPGroup 2 O := CFSG.pCore_isPGroup
  obtain ⟨n, hn⟩ := hO2.exists_card_eq
  have h5O : ¬ 5 ∣ Nat.card O := by
    rw [hn]
    intro h5
    have h52 : (5 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_five h5
    norm_num at h52
  have hfacO : (Nat.card O).factorization 5 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd h5O
  have hfacB : (Nat.card (Bar2 L)).factorization 5 = 2 :=
    factorization_five_card_bar2_of_lieModel_bar2_tits h
  have hO0 : Nat.card O ≠ 0 := Nat.card_pos.ne'
  have hB0 : Nat.card (Bar2 L) ≠ 0 := Nat.card_pos.ne'
  rw [← hcardmul, Nat.factorization_mul hO0 hB0, Finsupp.add_apply, hfacO, hfacB, zero_add]

private theorem isElemAbelian_five_sylow_of_lieModel_bar2_tits
    {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (h : CFSG.Blueprint.LieModel (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 L) .Tits 0 2 1)
    (Q : Sylow 5 ↥L) :
    CFSG.Open.IsElemAbelian 5 (Q : Subgroup ↥L) ∧ Nat.card Q = 25 := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let O : Subgroup ↥L := CFSG.pCore 2 ↥L
  let π : ↥L →* Bar2 L := QuotientGroup.mk' O
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective O
  have hfacL : (Nat.card ↥L).factorization 5 = 2 :=
    factorization_five_card_of_lieModel_bar2_tits h
  have hQcard : Nat.card Q = 25 := by
    rw [Sylow.card_eq_multiplicity, hfacL]
    norm_num
  have hO2 : IsPGroup 2 π.ker := by
    rw [show π.ker = O from QuotientGroup.ker_mk' O]
    exact CFSG.pCore_isPGroup
  have hQdisj : (Q : Subgroup ↥L) ⊓ π.ker = ⊥ :=
    disjoint_iff.mp (IsPGroup.disjoint_of_ne 5 2 (by norm_num)
      (Q : Subgroup ↥L) π.ker Q.isPGroup' hO2)
  have hinj : Function.Injective (π.subgroupMap (Q : Subgroup ↥L)) := by
    intro x y hxy
    have hxy' : π (x : ↥L) = π (y : ↥L) := by
      simpa using congrArg (fun z : ↥((Q : Subgroup ↥L).map π) => (z : Bar2 L)) hxy
    apply Subtype.ext
    have hmem : ((x : ↥L)⁻¹ * (y : ↥L)) ∈ (Q : Subgroup ↥L) ⊓ π.ker := by
      refine ⟨(Q : Subgroup ↥L).mul_mem ((Q : Subgroup ↥L).inv_mem x.2) y.2, ?_⟩
      show π ((x : ↥L)⁻¹ * (y : ↥L)) = 1
      rw [map_mul, map_inv, hxy', inv_mul_cancel]
    rw [hQdisj] at hmem
    exact eq_of_inv_mul_eq_one (Subgroup.mem_bot.mp hmem)
  let e : ↥Q ≃* ↥((Q : Subgroup ↥L).map π) :=
    MulEquiv.ofBijective (π.subgroupMap (Q : Subgroup ↥L))
      ⟨hinj, π.subgroupMap_surjective (Q : Subgroup ↥L)⟩
  have hQmap_card : Nat.card ((Q : Subgroup ↥L).map π) = 25 := by
    rw [← Nat.card_congr e.toEquiv]
    exact hQcard
  have hfacB : (Nat.card (Bar2 L)).factorization 5 = 2 :=
    factorization_five_card_bar2_of_lieModel_bar2_tits h
  have hQmap_sylow : Nat.card ((Q : Subgroup ↥L).map π) =
      5 ^ (Nat.card (Bar2 L)).factorization 5 := by
    rw [hQmap_card, hfacB]
    norm_num
  obtain ⟨E, hEel, hEcard⟩ := exists_elemAbelian_five_two_of_lieModel_tits h
  have hE_sylow : Nat.card E = 5 ^ (Nat.card (Bar2 L)).factorization 5 := by
    rw [hEcard, hfacB]
    norm_num
  let PE : Sylow 5 (Bar2 L) := Sylow.ofCard E hE_sylow
  let PQ : Sylow 5 (Bar2 L) := Sylow.ofCard ((Q : Subgroup ↥L).map π) hQmap_sylow
  haveI : Finite (Sylow 5 (Bar2 L)) :=
    Finite.of_injective (fun S : Sylow 5 (Bar2 L) => (S : Set (Bar2 L)))
      (fun S T h' => Sylow.ext (by
        ext x
        exact Set.ext_iff.mp h' x))
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Bar2 L) PE PQ
  have hsub : (PE : Subgroup (Bar2 L)).map (MulAut.conj g).toMonoidHom =
      (PQ : Subgroup (Bar2 L)) := by
    have h' := congrArg (fun S : Sylow 5 (Bar2 L) => (S : Subgroup (Bar2 L))) hg
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h'
    convert h' using 2
    ext x
    rfl
  have hsub' : E.map (MulAut.conj g).toMonoidHom = (Q : Subgroup ↥L).map π := by
    simpa [PE, PQ] using hsub
  have hQmap_el : CFSG.Open.IsElemAbelian 5 ((Q : Subgroup ↥L).map π) := by
    rw [← hsub']
    exact CFSG.SectionRank.isElemAbelian_map hEel (MulAut.conj g).toMonoidHom
  have hQel : CFSG.Open.IsElemAbelian 5 (Q : Subgroup ↥L) := by
    haveI : CFSG.IsElementaryAbelian 5 ↥(Q : Subgroup ↥L) :=
      CFSG.IsElementaryAbelian.of_mulEquiv e.symm hQmap_el.isElementaryAbelian
    exact CFSG.Open.isElemAbelian_of_isElementaryAbelian
  exact ⟨hQel, hQcard⟩

theorem not_five_dvd_card_outer_bar2_tits
    {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (h : CFSG.Blueprint.LieModel (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 L) .Tits 0 2 1) :
    ¬ 5 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 L)) := by
  haveI : Finite (Bar2 L) :=
    Finite.of_surjective (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
      (QuotientGroup.mk'_surjective _)
  exact not_five_dvd_card_outer_of_lieModel_tits h

theorem isElemAbelian_five_inf_sylow_of_lieModel_bar2_tits
    {G : Type} [Group G] [Finite G] {M L S : Subgroup G} (hLM : L ≤ M)
    (hLnorm : (L.subgroupOf M).Normal)
    (hS : CFSG.ABGLocalTools.IsSylowOf 5 S M)
    (hT : CFSG.Blueprint.LieModel (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 L) .Tits 0 2 1) :
    CFSG.Open.IsElemAbelian 5 (S ⊓ L) ∧ Nat.card ↥(S ⊓ L) = 25 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hMnormL : M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp hLnorm
  have hA : CFSG.ABGLocalTools.IsSylowOf 5 (S ⊓ L) L :=
    CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer hS hLM hMnormL
  obtain ⟨Q, hQ⟩ := hA.exists_sylow_eq_subgroupOf
  obtain ⟨hQel, hQcard⟩ := isElemAbelian_five_sylow_of_lieModel_bar2_tits hT Q
  have hmap : (Q : Subgroup ↥L).map L.subtype = S ⊓ L := by
    rw [hQ, Subgroup.map_subgroupOf_eq_of_le hA.le]
  refine ⟨?_, ?_⟩
  · rw [← hmap]
    exact CFSG.SectionRank.isElemAbelian_map hQel L.subtype
  · rw [← hmap, Subgroup.card_map_of_injective L.subtype_injective]
    exact hQcard

theorem false_of_lieModel_bar2_tits_of_bar
    {G : Type} [Group G] [Finite G] {M L S : Subgroup G}
    (h614 : CFSG.Yardstones.Mf4cdcdf2e013.Theorem614At M)
    (hsub : CFSG.Open.uniqueFourSigma M ⊆ CFSG.Yardstones.Mf4cdcdf2e013.SigmaOne4 G)
    (h5sig : 5 ∉ CFSG.Open.uniqueFourSigma M)
    (hnot : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 5 M)
    (hLM : L ≤ M) (hLnorm : (L.subgroupOf M).Normal)
    (hS : CFSG.ABGLocalTools.IsSylowOf 5 S M)
    (hT : CFSG.Blueprint.LieModel (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 L) .Tits 0 2 1)
    (hΓ : CFSG.Open.rankThreeGamma 1 5 (S ⊓ L) ≤ M) :
    False := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOut : ¬ 5 ∣ Nat.card
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer (Bar2 L)) :=
    not_five_dvd_card_outer_bar2_tits hT
  have hA := isElemAbelian_five_inf_sylow_of_lieModel_bar2_tits hLM hLnorm hS hT
  have hP5 : IsPGroup 5 ↥(S ⊓ L) :=
    IsPGroup.of_card (p := 5) (n := 2) (by rw [hA.2]; norm_num)
  have hO2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 L) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  have hSL : S ⊓ L ⊓ CFSG.Open.pCoreOf 2 L = ⊥ :=
    disjoint_iff.mp (IsPGroup.disjoint_of_ne 5 2 (by norm_num)
      (S ⊓ L) (CFSG.Open.pCoreOf 2 L) hP5 hO2)
  have hcomm : ∀ a b : ↥(S ⊓ L), a * b = b * a :=
    isMulCommutative_iff.mp hA.1.1
  have hSLab : ∀ x ∈ S ⊓ L, ∀ y ∈ S ⊓ L, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hcomm ⟨x, hx⟩ ⟨y, hy⟩)
  have hMnormL : M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp hLnorm
  have hSNL : S ≤ Subgroup.normalizer (L : Set G) := hS.le.trans hMnormL
  have hQnormP : ((S ⊓ L).subgroupOf S).Normal := by
    have h := normal_subgroupOf_inf_of_normal (P := S) hLM hLnorm hS.le
    rwa [inf_comm] at h
  have hQ : CFSG.ABGLocalTools.IsSylowOf 5 (S ⊓ L) L :=
    CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer hS hLM hMnormL
  have hInner : ∀ x ∈ S, ∃ l ∈ L, ∀ y ∈ L,
      (x * y * x⁻¹) * (l * y * l⁻¹)⁻¹ ∈ CFSG.Open.pCoreOf 2 L := by
    intro x hx
    exact exists_conj_of_not_dvd_outer x (hSNL hx)
      (hS.isPGroup.to_le (Subgroup.zpowers_le.mpr hx)) hOut
  have hdecomp : S ≤ (S ⊓ L) ⊔ centralizerBar S L :=
    le_sup_centralizerBar_of_inner_prime (P := S) (Q := S ⊓ L) (X := S)
      inf_le_left inf_le_right rfl hQnormP hQ hS.isPGroup hSNL le_rfl hInner
  exact false_of_abelian_sylow_of_bar (r := 5) (E := S ⊓ L)
    h614 hsub (by norm_num) (by norm_num) h5sig hnot hLM hLnorm hS hdecomp
    hSLab hSL le_rfl hA.1 (by rw [hA.2]; norm_num) hΓ

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
