module

public import CFSG.RankThree.PartTwo.Sec17.Item1723ProofHJ
public import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
import CFSG.RankThree.PartTwo.Sec14.Concl142HJ
import CFSG.RankThree.PartTwo.Sec12.Gap128OTwoHJ
import CFSG.RankThree.PartTwo.Sec6.Item612Core
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAut

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
open CFSG.ABGLocalTools (IsSylowOf)

@[expose] def KS17J2CentralizerNine : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ E : Subgroup X, Nat.card E = 9 → Subgroup.centralizer (E : Set X) ≤ E

open CFSG.ComponentClassification.OuterAutomorphisms in
theorem j2_mem_range_conj_of_pow_eq_one
    {X : Type} [Group X]
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2)) {σ : MulAut X} {k : ℕ}
    (hσ : σ ^ (3 ^ k) = 1) : σ ∈ (MulAut.conj : X →* MulAut X).range := by
  obtain ⟨e⟩ := hX
  obtain ⟨f⟩ :=
    CFSG.ComponentClassification.J2Cover.ctuc_j2_full_automorphism_permutation_model.2.2.2.2.2
  set φ : Outer X ≃* Multiplicative (ZMod 2) := (equivalence e).trans f
  have hsq : ∀ y : Multiplicative (ZMod 2), y ^ 2 = 1 := by decide
  have h1 : φ (σ : Outer X) = 1 := by
    have h3 : φ (σ : Outer X) ^ (3 ^ k) = 1 := by
      rw [← map_pow, ← QuotientGroup.mk_pow, hσ, QuotientGroup.mk_one, map_one]
    have hcop : Nat.Coprime (3 ^ k) 2 := Nat.Coprime.pow_left k (by norm_num)
    have h := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one (hsq _))
    rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h
    exact h
  have h2 : (σ : Outer X) = 1 := φ.injective (h1.trans (map_one φ).symm)
  have h4 : σ ∈ inner X := (QuotientGroup.eq_one_iff σ).mp h2
  exact h4

namespace TailProof

variable {G : Type} [Group G]

theorem map_subgroupOf_map_normalizer {L U : Subgroup G} (M : Subgroup ↥L) [M.Characteristic]
    (hUL : U ≤ L) {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    ((U.map (MulAut.conj g).toMonoidHom).subgroupOf L).map (QuotientGroup.mk' M) =
      ((U.subgroupOf L).map (QuotientGroup.mk' M)).map
        (mulAutQuotientHom M (L.normalizerMonoidHom ⟨g, hg⟩)).toMonoidHom := by
  rw [Subgroup.map_map]
  ext z
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, MonoidHom.coe_comp, Function.comp_apply]
  constructor
  · rintro ⟨x, ⟨u, hu, hux⟩, rfl⟩
    refine ⟨⟨u, hUL hu⟩, hu, ?_⟩
    change (mulAutQuotientHom M (L.normalizerMonoidHom ⟨g, hg⟩))
      ((⟨u, hUL hu⟩ : ↥L) : ↥L ⧸ M) = ((x : ↥L) : ↥L ⧸ M)
    rw [mulAutQuotientHom_mk]
    congr 1
    exact Subtype.ext (by rw [Subgroup.normalizerMonoidHom_apply_apply_coe]; exact hux)
  · rintro ⟨u, hu, rfl⟩
    refine ⟨⟨g * u * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg u).mp u.2⟩, ⟨u, hu, rfl⟩, ?_⟩
    change ((⟨g * u * g⁻¹, _⟩ : ↥L) : ↥L ⧸ M) =
      (mulAutQuotientHom M (L.normalizerMonoidHom ⟨g, hg⟩)) ((u : ↥L) : ↥L ⧸ M)
    rw [mulAutQuotientHom_mk]
    rfl

theorem card_map_of_isPGroup_three [Finite G] {X : Type} [Group X] (π : G →* X)
    (hker : IsPGroup 2 π.ker) {K : Subgroup G} (hK : IsPGroup 3 K) :
    Nat.card (K.map π) = Nat.card K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine Nat.card_congr (Equiv.ofBijective (π.subgroupMap K)
    ⟨fun x y hxy => ?_, π.subgroupMap_surjective _⟩).symm
  have hdisj : Disjoint K π.ker := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hK
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hker
    exact Subgroup.disjoint_of_coprime_natCard (by
      rw [hk, hm]
      exact Nat.Coprime.pow k m (by norm_num))
  have hmem : (x : G)⁻¹ * (y : G) ∈ K ⊓ π.ker := by
    refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem x.2) y.2, MonoidHom.mem_ker.mpr ?_⟩
    rw [map_mul, map_inv, inv_mul_eq_one]
    exact congrArg Subtype.val hxy
  rw [hdisj.eq_bot, Subgroup.mem_bot] at hmem
  exact Subtype.ext (eq_of_inv_mul_eq_one hmem)

end TailProof

section Local


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ Y₁ S : Subgroup G}
  {p : ℕ} {P : Subgroup G}

theorem Sec17Std.j2_local (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) ∧
      Nat.card (A ⊓ L : Subgroup G) = 9 ∧ A = Subgroup.zpowers c ⊔ (A ⊓ L) ∧
      Nat.card ((A.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) = 9 ∧
      scriptQPiStar A (lB A) L (piOf 2) = maxInvariantPiSubgroups L A (piOf 2) ∧
      ∀ V : Subgroup G, V ≤ L → A ⊓ L ≤ Subgroup.normalizer (V : Set G) →
        A ≤ Subgroup.normalizer (V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD : Sec13Data G A c L := h.toSec13Data
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hD.mem_partTwoE
  have hLc : L ≤ Subgroup.centralizer {c} := hD.le_centralizer
  have hLtop : L ≠ ⊤ := fun htop =>
    Sec6.centralizer_ne_top_of_ne_one h.toTheoremFourHyp hD.ne_one (top_le_iff.mp (htop ▸ hLc))
  have hJ2 : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) :=
    Sec12.gap128OTwoHJ ↥L (h.toTheoremFourHyp.sectionFourHyp hLtop)
      (Sec6.isPerfect_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt) hJ
  obtain ⟨-, h9, hAc⟩ := j2_point_facts hD hJ
  have hker : IsPGroup 2 (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).ker := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup
  have hT3 : IsPGroup 3 (A.subgroupOf L) :=
    hA.isPGroup.comap_of_ker_isPGroup L.subtype
      (IsPGroup.ker_isPGroup_of_injective L.subtype_injective)
  have hTcard : Nat.card (A.subgroupOf L) = 9 := by
    rw [← Subgroup.inf_subgroupOf_right, ← h9]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : A ⊓ L ≤ L)).toEquiv
  refine ⟨hJ2, h9, hAc, by rw [TailProof.card_map_of_isPGroup_three _ hker hT3, hTcard], ?_, ?_⟩
  · exact scriptQPiStar_two_eq fun U hU => (mem_scriptQ_of_hj_point h.toSec14Std hJ
      ⟨hU.1.trans (hLc.trans (centralizer_singleton_le_normalizer_zpowers c)),
        isPiSubgroup_piCompl_three_of_piOf_two hU.2.1, hU.2.2⟩).1
  · intro V hVL hV
    rw [hAc]
    refine sup_le (Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer (V : Set G) ?_)) hV
    exact Subgroup.mem_centralizer_iff.mpr fun v hv =>
      Subgroup.mem_centralizer_singleton_iff.mp (hLc (hVL hv))

theorem Sec17Y1.mem_normalizer_inf_L_of_j2 (hK : KS17J2CentralizerNine)
    (h : Sec17Y1 G A c L Y₀ Y₁ S p P)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {t : G} (htC : t ∈ Subgroup.centralizer (A : Set G)) {k : ℕ} (htk : t ^ (3 ^ k) = 1) :
    t ∈ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hs := h.toSec17Std
  obtain ⟨hJ2, h9, -, hB9, hstar, hAinv⟩ := hs.j2_local hJ
  have htA : t ∈ Subgroup.normalizer (A : Set G) := Subgroup.centralizer_le_normalizer _ htC
  have h3L : 3 ∣ Nat.card L := by
    have h9L := Subgroup.card_dvd_of_le (inf_le_right : A ⊓ L ≤ L)
    rw [h9] at h9L
    exact (show 3 ∣ 9 by norm_num).trans h9L
  have htc : t ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    centralizer_singleton_le_normalizer_zpowers c (Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp htC c hs.toSec13Data.mem_A).symm)
  have htL : t ∈ Subgroup.normalizer (L : Set G) :=
    Sec15R.normalizer_zpowers_le_normalizer_L hs.toSec15R h3L htc
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : IsPGroup 2 π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup
  have hSL : S ⊓ L ∈ maxInvariantPiSubgroups L A (piOf 2) := hstar ▸ h.inf_L_mem_qStar_two
  obtain ⟨hf, -⟩ := maxInvariant_two_transport π hπs hker hAinv
  set B := (A.subgroupOf L).map π with hBdef
  set Sb := ((S ⊓ L).subgroupOf L).map π with hSbdef
  have hBSb : B ≤ Subgroup.normalizer (Sb : Set _) := (hf _ hSL).1.prop.2.2
  set σ : MulAut (↥L ⧸ CFSG.pCore 2 ↥L) :=
    mulAutQuotientHom (CFSG.pCore 2 ↥L) (L.normalizerMonoidHom ⟨t, htL⟩) with hσ
  have hσk : σ ^ (3 ^ k) = 1 := by
    have e : σ = ((mulAutQuotientHom (CFSG.pCore 2 ↥L)).comp L.normalizerMonoidHom)
        ⟨t, htL⟩ := rfl
    have ht' : (⟨t, htL⟩ : Subgroup.normalizer (L : Set G)) ^ (3 ^ k) = 1 :=
      Subtype.ext (by simpa using htk)
    rw [e, ← map_pow, ht', map_one]
  obtain ⟨y, hy⟩ := j2_mem_range_conj_of_pow_eq_one hJ2 hσk
  have hyC : y ∈ Subgroup.centralizer (B : Set (↥L ⧸ CFSG.pCore 2 ↥L)) := by
    rw [Subgroup.mem_centralizer_iff, hBdef]
    rintro _ ⟨x, hx, rfl⟩
    have h1 : σ (π x) = π x := by
      rw [hσ]
      change mulAutQuotientHom (CFSG.pCore 2 ↥L) (L.normalizerMonoidHom ⟨t, htL⟩)
        ((x : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) = ((x : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L)
      rw [mulAutQuotientHom_mk]
      congr 1
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      have hxt := Subgroup.mem_centralizer_iff.mp htC (x : G) (Subgroup.mem_subgroupOf.mp hx)
      change t * (x : G) * t⁻¹ = (x : G)
      rw [← hxt, mul_inv_cancel_right]
    rw [← hy, MulAut.conj_apply] at h1
    calc π x * y = (y * π x * y⁻¹) * y := by rw [h1]
      _ = y * π x := by group
  have hyB : y ∈ B := hK (↥L ⧸ CFSG.pCore 2 ↥L) hJ2 B hB9 hyC
  have hσSb : Sb.map σ.toMonoidHom = Sb := by
    rw [← hy]
    exact Late.map_conj_eq_of_mem_normalizer (hBSb hyB)
  have himg : (((S ⊓ L).map (MulAut.conj t).toMonoidHom).subgroupOf L).map π = Sb := by
    rw [hπ, TailProof.map_subgroupOf_map_normalizer (CFSG.pCore 2 ↥L) inf_le_right htL]
    exact hσSb
  have hU := TailProof.map_conj_mem_maxInvariant htA htL hSL
  have e1 := (hf _ hU).2
  rw [himg] at e1
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (e1.symm.trans (hf _ hSL).2)

theorem Sec17Y1.le_normalizer_x1720_of_j2 (hK : KS17J2CentralizerNine)
    (h : Sec17Y1 G A c L Y₀ Y₁ S p P)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {T : Subgroup G} (hT : IsSylowOf 3 T (Subgroup.centralizer (A : Set G))) :
    T ≤ Subgroup.normalizer ((x1720 A Y₀ S L : Subgroup G) : Set G) := by
  intro t ht
  have htC : t ∈ Subgroup.centralizer (A : Set G) := hT.le ht
  obtain ⟨k, hk⟩ := hT.isPGroup ⟨t, ht⟩
  have htk : t ^ (3 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    (HeadProof.map_conj_x1720 h.toSec17Std (Subgroup.centralizer_le_normalizer _ htC)
      (h.mem_normalizer_inf_L_of_j2 hK hJ htC htk))

theorem claim1722T_of (hK : KS17J2CentralizerNine) (h1721 : Item1721) : Claim1722T :=
  fun G _ _ A c L Y₀ Y₁ S p P h _ hT =>
    h.le_normalizer_x1720_of_j2 hK (h1721 G A c L Y₀ Y₁ S p P h) hT

end Local

end CFSG.RankThree.PartTwo.Sec17
