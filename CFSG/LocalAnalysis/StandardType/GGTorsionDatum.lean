module

public import CFSG.LocalAnalysis.StandardType.GGTorsionDefs
import CFSG.LocalAnalysis.StandardType.GGD4OddCentVocab
import CFSG.LocalAnalysis.StandardType.GGD4OddCentJLevel
import CFSG.LocalAnalysis.StandardType.GGTableBTransport
import CFSG.LocalAnalysis.StandardType.GGNbrBalance
import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
import CFSG.LocalAnalysis.ComponentInitial.DerivedFixedLayer

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section TorsionDatum

private theorem td1_exists_closure_pair {G : Type} [Group G] [Finite G] {p : ℕ} {B : Subgroup G}
    {x : G} {L D J : Subgroup G} (hp : p.Prime) (hS : LargeEvenSStar p B x L)
    (hpre : LargeEvenStdSubPre p B x L D J) :
    ∃ y ∈ B, D = Subgroup.closure {x, y} := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hxB : x ∈ B := hS.2.1
  have hxD : x ∈ D := hpre.2.2.2.1
  have hzxcard : Nat.card (Subgroup.zpowers x) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hS.1.1.2 x hxB) hS.2.2.1]
  have hzxD : Subgroup.zpowers x ≤ D := Subgroup.zpowers_le.mpr hxD
  have hpgt : p < p ^ 2 := by
    have h1 : p * 1 < p * p := Nat.mul_lt_mul_of_pos_left hp.one_lt hp.pos
    simpa [pow_two] using h1
  have hp2le : 2 ≤ p := hp.two_le
  have hne : Subgroup.zpowers x ≠ D := by
    intro h
    rw [h, hpre.2.2.1] at hzxcard
    exact absurd hpgt (not_lt.mpr (le_of_eq hzxcard))
  obtain ⟨y, hyD, hyz⟩ : ∃ y ∈ D, y ∉ Subgroup.zpowers x := by
    by_contra h
    simp only [not_exists, not_and] at h
    exact hne (le_antisymm hzxD fun z hz => Classical.not_not.mp (h z hz))
  refine ⟨y, hpre.1 hyD, ?_⟩
  have hclD : Subgroup.closure ({x, y} : Set G) ≤ D := by
    rw [Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hxD
    · exact hyD
  have hzxcl : Subgroup.zpowers x ≤ Subgroup.closure ({x, y} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
  have hnecl : Subgroup.zpowers x ≠ Subgroup.closure ({x, y} : Set G) := by
    intro h
    exact hyz (h ▸ Subgroup.subset_closure (by simp))
  have hcardlt : Nat.card (Subgroup.zpowers x) <
      Nat.card (Subgroup.closure ({x, y} : Set G)) :=
    Subgroup.card_lt_of_lt (lt_of_le_of_ne hzxcl hnecl)
  have hdvd : Nat.card (Subgroup.closure ({x, y} : Set G)) ∣ p ^ 2 := by
    have h := Subgroup.card_dvd_of_le hclD
    rwa [hpre.2.2.1] at h
  have hcardp2 : Nat.card (Subgroup.closure ({x, y} : Set G)) = p ^ 2 := by
    obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    have hk21 : k = 2 := by
      have hk012 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      rcases hk012 with rfl | rfl | rfl
      · rw [pow_zero] at hk
        rw [hk, hzxcard] at hcardlt
        omega
      · rw [pow_one] at hk
        rw [hk, hzxcard] at hcardlt
        omega
      · rfl
    rw [hk21] at hk
    exact hk
  exact (Subgroup.eq_of_le_of_card_ge hclD (by rw [hcardp2, hpre.2.2.1])).symm

theorem ggTorsion_component_eq_of_stdSub
    {G : Type} [Group G] [Finite G] {p : ℕ} {B : Subgroup G} {x y : G} {L D J : Subgroup G}
    (hI : GGThmIHyp p B x L) (hDJ : LargeEvenStdSub p B x L D J)
    (hD : D = Subgroup.closure {x, y}) (hyB : y ∈ B)
    (hNL : B ≤ Subgroup.normalizer (L : Set G)) :
    ∀ Q : Subgroup ↥L,
      IsComponentOf Q (ggAutFixedSubgroup (L.normalizerMonoidHom ⟨y, hNL hyB⟩)) →
        Q = J.subgroupOf L := by
  have hS : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
  have hpre : LargeEvenStdSubPre p B x L D J := hDJ.1
  have hyN : y ∈ Subgroup.normalizer (L : Set G) := hNL hyB
  have hCD : Subgroup.centralizer (D : Set G) =
      Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G) := by
    rw [hD, Subgroup.centralizer_closure]
    ext g
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  have hLD : L ⊓ Subgroup.centralizer (D : Set G) =
      L ⊓ Subgroup.centralizer ({y} : Set G) := by
    rw [hCD, ← inf_assoc, inf_eq_left.mpr hS.2.2.2.1.1]
  intro Q hQ
  have hfixeq := ggAutFixedSubgroup_normalizerMonoidHom hyN
  have hQ' : IsComponentOf (Subgroup.map L.subtype Q)
      (Subgroup.map L.subtype
        (ggAutFixedSubgroup (L.normalizerMonoidHom ⟨y, hyN⟩))) :=
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff L.subtype_injective).2 hQ
  rw [hfixeq, Subgroup.map_subgroupOf_eq_of_le
    (inf_le_left : L ⊓ Subgroup.centralizer ({y} : Set G) ≤ L), ← hLD] at hQ'
  have hle : Subgroup.map L.subtype Q ≤ J := by
    rw [hpre.2.2.2.2.1]
    exact le_largeEvenLayer hQ'
  have hJeq : Subgroup.map L.subtype Q = J :=
    (CFSG.LocalAnalysis.ComponentInitial.eq_of_isComponentOf_of_le hQ'.2.2
      hpre.2.2.2.2.2.1 hQ' hle le_rfl).symm
  have hQcomap : Q = (Subgroup.map L.subtype Q).comap L.subtype :=
    (Subgroup.comap_map_eq_self_of_injective L.subtype_injective Q).symm
  rw [hQcomap, hJeq]
  exact Subgroup.comap_subtype J L

private theorem td1_exists_unique_of_marking
    {G : Type} [Group G] [Finite G] {p : ℕ} {B : Subgroup G} {x : G}
    {L D J : Subgroup G} (P : LargeEvenLabel → Prop)
    (hI : GGThmIHyp p B x L) (hDJ : LargeEvenStdSub p B x L D J)
    (hmark : ∀ (y : G), y ∈ B → ∀ hyN : y ∈ Subgroup.normalizer (L : Set G),
      LargeEvenMarking ↥L fun lab _ _ I _ θ =>
        P lab ∧ ggInducedAut θ (L.normalizerMonoidHom ⟨y, hyN⟩) ∈ I) :
    ∃ δ : MulAut ↥L, GGTorsionDatum P p δ (J.subgroupOf L) ∧
      ∀ Q : Subgroup ↥L, IsComponentOf Q (ggAutFixedSubgroup δ) → Q = J.subgroupOf L := by
  have hp : p.Prime := hI.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hI.2.2.2.2.2.1.2.1
  have hS : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
  have hst : LargeEvenStandardType p B x L := hI.2.2.2.2.2.2.2
  have hpre : LargeEvenStdSubPre p B x L D J := hDJ.1
  have hNL : B ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_largeEvenStandardType hst
  obtain ⟨y, hyB, hD⟩ := td1_exists_closure_pair hp hS hpre
  have hyN : y ∈ Subgroup.normalizer (L : Set G) := hNL hyB
  have hxB : x ∈ B := hS.2.1
  have hJL : J ≤ L := hpre.2.2.2.2.2.1.1.trans inf_le_left
  refine ⟨L.normalizerMonoidHom ⟨y, hyN⟩, ?_⟩
  have hpow : (⟨y, hyN⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ p = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    simpa using hS.1.1.2 y hyB
  have hδp : (L.normalizerMonoidHom ⟨y, hyN⟩) ^ p = 1 := by
    rw [← map_pow, hpow, map_one]
  have hδ1 : L.normalizerMonoidHom ⟨y, hyN⟩ ≠ 1 := by
    intro hδ
    have hycent : y ∈ Subgroup.centralizer (L : Set G) :=
      (normalizerMonoidHom_eq_one_iff hyN).1 hδ
    have hyinf : y ∈ B ⊓ Subgroup.centralizer (L : Set G) := ⟨hyB, hycent⟩
    have hzpx : B ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x :=
      inf_centralizer_eq_zpowers_of_sstar hp hS
    have hyzx : y ∈ Subgroup.zpowers x := by
      rw [← hzpx]; exact hyinf
    have hcl_le : Subgroup.closure ({x, y} : Set G) ≤ Subgroup.zpowers x := by
      rw [Subgroup.closure_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hzx | hzy
      · rw [hzx]; exact Subgroup.mem_zpowers x
      · rw [hzy]; exact hyzx
    have hDle : D ≤ Subgroup.zpowers x := by rw [hD]; exact hcl_le
    have hzxcard : Nat.card (Subgroup.zpowers x) = p := by
      haveI : Fact p.Prime := ⟨hp⟩
      rw [Nat.card_zpowers, orderOf_eq_prime (hS.1.1.2 x hxB) hS.2.2.1]
    have hdvd : p ^ 2 ∣ p := by
      have h := Subgroup.card_dvd_of_le hDle
      rwa [hpre.2.2.1, hzxcard] at h
    have hpgt : p < p ^ 2 := by
      have h1 : p * 1 < p * p := Nat.mul_lt_mul_of_pos_left hp.one_lt hp.pos
      simpa [pow_two] using h1
    exact absurd hpgt (not_lt.mpr (Nat.le_of_dvd hp.pos hdvd))
  have hCD : Subgroup.centralizer (D : Set G) =
      Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G) := by
    rw [hD, Subgroup.centralizer_closure]
    ext g
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  have hLD : L ⊓ Subgroup.centralizer (D : Set G) =
      L ⊓ Subgroup.centralizer ({y} : Set G) := by
    rw [hCD, ← inf_assoc, inf_eq_left.mpr hS.2.2.2.1.1]
  have hJcomp : IsComponentOf J (L ⊓ Subgroup.centralizer ({y} : Set G)) := by
    rw [← hLD]; exact hpre.2.2.2.2.2.1
  have hcomp : IsComponentOf (J.subgroupOf L)
      (ggAutFixedSubgroup (L.normalizerMonoidHom ⟨y, hyN⟩)) :=
    isComponentOf_subgroupOf_ggAutFixed hyN hJL hJcomp
  refine ⟨?_, ggTorsion_component_eq_of_stdSub hI hDJ hD hyB hNL⟩
  exact ⟨hp, hp2, hδp, hδ1, hcomp, hmark y hyB hyN⟩

theorem exists_ggTorsionDatum {G : Type} [Group G] [Finite G] {p : ℕ} {B : Subgroup G} {x : G}
    {L D J : Subgroup G} (hI : GGThmIHyp p B x L) (hDJ : LargeEvenStdSub p B x L D J) :
    ∃ δ : MulAut ↥L, GGTorsionDatum (fun _ => True) p δ (J.subgroupOf L) := by
  obtain ⟨δ, hδ, -⟩ := td1_exists_unique_of_marking (fun _ => True) hI hDJ (by
    intro y hyB hyN
    have hst : LargeEvenStandardType p B x L := hI.2.2.2.2.2.2.2
    have hNL : B ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_largeEvenStandardType hst
    refine largeEvenMarking_mono ?_ hst.1
    rintro lab R _ I F θ ⟨hsp, -, h3⟩
    have hinn : GGInducedInn (ggAutsOf L B hNL) θ I := ggInducedInn_of_clause3 hNL θ h3
    exact ⟨trivial, hinn _ ((mem_ggAutsOf hNL).2 ⟨y, hyB, rfl⟩)⟩)
  exact ⟨δ, hδ⟩

theorem exists_ggTorsionDatum_unique_of_innerDiagOnLabel
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (P : LargeEvenLabel → Prop)
    (hI : GGThmIHyp p B x L) (hDJ : LargeEvenStdSub p B x L D J) (hBBs : B ≤ Bs)
    (hMark : GGInnerDiagOnLabel (fun _ lab => P lab) p Bs L) :
    ∃ δ : MulAut ↥L, GGTorsionDatum P p δ (J.subgroupOf L) ∧
      ∀ Q : Subgroup ↥L, IsComponentOf Q (ggAutFixedSubgroup δ) → Q = J.subgroupOf L := by
  apply td1_exists_unique_of_marking P hI hDJ
  intro y hyB hyN
  refine largeEvenMarking_mono ?_ hMark
  rintro lab R _ I F θ ⟨hP, -, hind⟩
  refine ⟨hP, ?_⟩
  obtain ⟨φ, hφI, hφ⟩ := hind y⁻¹ (hBBs (Subgroup.inv_mem B hyB))
  have hφeq : φ = ggInducedAut θ (L.normalizerMonoidHom ⟨y, hyN⟩) := by
    ext r
    obtain ⟨z, rfl⟩ := θ.surjective r
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective z
    rw [hφ l (L.normalizerMonoidHom ⟨y, hyN⟩ l) ?_, ggInducedAut_apply]
    change ((L.normalizerMonoidHom ⟨y, hyN⟩ l : ↥L) : G) = y⁻¹⁻¹ * (l : G) * y⁻¹
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    simp
  rw [hφeq] at hφI
  exact hφI

end TorsionDatum

end CFSG.StandardType
