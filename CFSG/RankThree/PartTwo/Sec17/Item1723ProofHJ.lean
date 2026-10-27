module

public import CFSG.RankThree.PartTwo.Sec17.Item1723Proof
public import CFSG.RankThree.PartTwo.Sec17.Item17ParaS
public import CFSG.RankThree.PartTwo.Sec17.Item1727Tools
import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
import CFSG.RankThree.PartTwo.Sec14.Concl142HJ
import CFSG.RankThree.PartTwo.KFacts.KS14HJLocal
import CFSG.RankThree.PartTwo.Sec12.Gap128OTwoHJ
import CFSG.RankThree.PartTwo.Sec6.Item612Core
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.RankThree.PartTwo.Sec15.Item15Steps
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
open CFSG.ABGLocalTools (IsSylowOf)
open scoped Pointwise

namespace TailProof

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem subgroupOf_map_conj {L U : Subgroup G} (hUL : U ≤ L) {y : G} (hy : y ∈ L) :
    (U.map (MulAut.conj y).toMonoidHom).subgroupOf L =
      (U.subgroupOf L).map (MulAut.conj (⟨y, hy⟩ : ↥L)).toMonoidHom := by
  ext z
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · rintro ⟨u, hu, hz⟩
    refine ⟨⟨u, hUL hu⟩, hu, Subtype.ext ?_⟩
    simpa using hz
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, by simp⟩

omit [Finite G] in
theorem map_subgroupOf_map_conj {L U : Subgroup G} {X : Type} [Group X] (π : ↥L →* X)
    (hUL : U ≤ L) {y : G} (hy : y ∈ L) :
    ((U.map (MulAut.conj y).toMonoidHom).subgroupOf L).map π =
      ((U.subgroupOf L).map π).map (MulAut.conj (π ⟨y, hy⟩)).toMonoidHom := by
  rw [subgroupOf_map_conj hUL hy, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext z
  simp [map_mul, map_inv]

omit [Finite G] in
theorem map_conj_mem_maxInvariant {A L U : Subgroup G} {g : G}
    (hgA : g ∈ Subgroup.normalizer (A : Set G)) (hgL : g ∈ Subgroup.normalizer (L : Set G))
    (hU : U ∈ maxInvariantPiSubgroups L A (piOf 2)) :
    U.map (MulAut.conj g).toMonoidHom ∈ maxInvariantPiSubgroups L A (piOf 2) := by
  refine Late.maximal_map_conj (W := Subgroup.normalizer (A : Set G) ⊓
    Subgroup.normalizer (L : Set G)) (fun V hV y hy => ?_) hU ⟨hgA, hgL⟩
  obtain ⟨hyA, hyL⟩ := Subgroup.mem_inf.mp hy
  refine ⟨?_, ?_, ?_⟩
  · rw [← Late.map_conj_eq_of_mem_normalizer hyL]
    exact Subgroup.map_mono hV.1
  · intro q hq
    refine hV.2.1 q ?_
    rwa [Subgroup.card_map_of_injective (MulAut.conj y).injective] at hq
  · calc A = A.map (MulAut.conj y).toMonoidHom := (Late.map_conj_eq_of_mem_normalizer hyA).symm
      _ ≤ (Subgroup.normalizer (V : Set G)).map (MulAut.conj y).toMonoidHom :=
          Subgroup.map_mono hV.2.2
      _ = _ := Subgroup.map_equiv_normalizer_eq V (MulAut.conj y)

end TailProof

section Orbit


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ Y₁ S : Subgroup G}
  {p : ℕ} {P : Subgroup G}

theorem Sec17Y1.orbit_of_j2 (h : Sec17Y1 G A c L Y₀ Y₁ S p P)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {w : G} (hwA : w ∈ Subgroup.normalizer (A : Set G)) (hwL : w ∈ L) (hwnA : w ∉ A)
    (hw3 : orderOf w = 3) :
    (∀ g ∈ Subgroup.normalizer (A : Set G), g ∈ Subgroup.normalizer (L : Set G) →
      ∃ i : ℕ, (S ⊓ L).map (MulAut.conj g).toMonoidHom =
        (S ⊓ L).map (MulAut.conj (w ^ i)).toMonoidHom) ∧
      (S ⊓ L).map (MulAut.conj w).toMonoidHom ≠ S ⊓ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have hs := h.toSec17Std
  have hD : Sec13Data G A c L := hs.toSec13Data
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hD.mem_partTwoE
  have hLc : L ≤ Subgroup.centralizer {c} := hD.le_centralizer
  have hLtop : L ≠ ⊤ := fun htop =>
    Sec6.centralizer_ne_top_of_ne_one hs.toTheoremFourHyp hD.ne_one (top_le_iff.mp (htop ▸ hLc))
  have hJ2 : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) :=
    Sec12.gap128OTwoHJ ↥L (hs.toTheoremFourHyp.sectionFourHyp hLtop)
      (Sec6.isPerfect_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt) hJ
  obtain ⟨-, h9, hAc⟩ := j2_point_facts hD hJ
  have hAinv : ∀ V : Subgroup G, V ≤ L → A ⊓ L ≤ Subgroup.normalizer (V : Set G) →
      A ≤ Subgroup.normalizer (V : Set G) := by
    intro V hVL hV
    rw [hAc]
    refine sup_le (Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer (V : Set G) ?_)) hV
    exact Subgroup.mem_centralizer_iff.mpr fun v hv =>
      Subgroup.mem_centralizer_singleton_iff.mp (hLc (hVL hv))
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : IsPGroup 2 π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup
  have hinj3 : ∀ {K : Subgroup ↥L}, IsPGroup 3 K → Nat.card (K.map π) = Nat.card K := by
    intro K hK
    refine Nat.card_congr (Equiv.ofBijective (π.subgroupMap K)
      ⟨fun x y hxy => ?_, π.subgroupMap_surjective _⟩).symm
    have hdisj : Disjoint K π.ker := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hK
      obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hker
      exact Subgroup.disjoint_of_coprime_natCard (by
        rw [hk, hm]
        exact Nat.Coprime.pow k m (by norm_num))
    have hmem : (x : ↥L)⁻¹ * (y : ↥L) ∈ K ⊓ π.ker := by
      refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem x.2) y.2, MonoidHom.mem_ker.mpr ?_⟩
      rw [map_mul, map_inv, inv_mul_eq_one]
      exact congrArg Subtype.val hxy
    rw [hdisj.eq_bot, Subgroup.mem_bot] at hmem
    exact Subtype.ext (eq_of_inv_mul_eq_one hmem)
  have hT3 : IsPGroup 3 (A.subgroupOf L) :=
    hA.isPGroup.comap_of_ker_isPGroup L.subtype
      (IsPGroup.ker_isPGroup_of_injective L.subtype_injective)
  have hTcard : Nat.card (A.subgroupOf L) = 9 := by
    rw [← Subgroup.inf_subgroupOf_right, ← h9]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : A ⊓ L ≤ L)).toEquiv
  set B := (A.subgroupOf L).map π with hBdef
  have hB9 : Nat.card B = 9 := by rw [hBdef, hinj3 hT3, hTcard]
  obtain ⟨hTsyl, hwN⟩ := isSylowOf_inf_sup_zpowers h415 hJ hA h9 hwA hwL hwnA hw3
  set T := (A ⊓ L) ⊔ Subgroup.zpowers w with hTdef
  have hTL : T ≤ L := hTsyl.le
  have hT27 : Nat.card T = 27 := by
    obtain ⟨S₀, hS₀⟩ := hTsyl
    rw [← hS₀, Subgroup.card_map_of_injective L.subtype_injective]
    exact card_sylow_eq_27 h415 hJ S₀
  have hT'3 : IsPGroup 3 (T.subgroupOf L) :=
    hTsyl.isPGroup.comap_of_ker_isPGroup L.subtype
      (IsPGroup.ker_isPGroup_of_injective L.subtype_injective)
  have hT'card : Nat.card (T.subgroupOf L) = 27 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTL).toEquiv, hT27]
  obtain ⟨P₀, hP₀⟩ := (hT'3.map π).exists_le_sylow
  have hP₀27 : Nat.card (P₀ : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) = 27 :=
    (h415 _ hJ2 P₀ _ rfl _ rfl).1.1.2.1
  have hP₀eq : (P₀ : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) = (T.subgroupOf L).map π :=
    (Subgroup.eq_of_le_of_card_ge hP₀ (by rw [hP₀27, hinj3 hT'3, hT'card])).symm
  have hBP₀ : B ≤ P₀ := by
    rw [hP₀eq]
    refine Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr ?_
    exact (le_sup_left : A ⊓ L ≤ T) ⟨Subgroup.mem_subgroupOf.mp hx, x.2⟩
  have hstar : scriptQPiStar A (lB A) L (piOf 2) = maxInvariantPiSubgroups L A (piOf 2) :=
    scriptQPiStar_two_eq fun U hU => (mem_scriptQ_of_hj_point hs.toSec14Std hJ
      ⟨hU.1.trans (hLc.trans (centralizer_singleton_le_normalizer_zpowers c)),
        isPiSubgroup_piCompl_three_of_piOf_two hU.2.1, hU.2.2⟩).1
  have hSL : S ⊓ L ∈ maxInvariantPiSubgroups L A (piOf 2) := hstar ▸ h.inf_L_mem_qStar_two
  obtain ⟨hf, -⟩ := maxInvariant_two_transport π hπs hker hAinv
  set Sb := ((S ⊓ L).subgroupOf L).map π with hSbdef
  have hSb := (hf _ hSL).1
  have hBSb : B ≤ Subgroup.normalizer (Sb : Set _) := hSb.prop.2.2
  have hTmul : ∀ t ∈ T, ∃ a ∈ A ⊓ L, ∃ k : ℤ, t = a * w ^ k := by
    intro t ht
    rw [← SetLike.mem_coe, hTdef,
      Subgroup.coe_mul_of_right_le_normalizer_left _ _ hwN] at ht
    obtain ⟨a, ha, z, hz, rfl⟩ := ht
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact ⟨a, ha, k, rfl⟩
  have hwL' : ∀ k : ℤ, w ^ k ∈ L := fun k => zpow_mem hwL k
  have hSba : ∀ (a : G) (ha : a ∈ A ⊓ L),
      Sb.map (MulAut.conj (π ⟨a, (Subgroup.mem_inf.mp ha).2⟩)).toMonoidHom = Sb := fun a ha =>
    Late.map_conj_eq_of_mem_normalizer (hBSb ⟨⟨a, (Subgroup.mem_inf.mp ha).2⟩,
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mp ha).1, rfl⟩)
  refine ⟨fun g hgA hgL => ?_, fun heq => ?_⟩
  ·
    have hU := TailProof.map_conj_mem_maxInvariant hgA hgL hSL
    obtain ⟨x, hxP, -, hxeq⟩ := KFacts.KS14.j2_maxInvariant_two_transitive h415 hJ2 P₀ hBP₀
      hB9 hSb (hf _ hU).1
    rw [hP₀eq] at hxP
    obtain ⟨t', ht', rfl⟩ := hxP
    obtain ⟨a, ha, k, htk⟩ := hTmul t' (Subgroup.mem_subgroupOf.mp ht')
    obtain ⟨haA, haL⟩ := Subgroup.mem_inf.mp ha
    have ht'eq : t' = ⟨a, haL⟩ * ⟨w ^ k, hwL' k⟩ := Subtype.ext htk
    have hainv : a⁻¹ ∈ A ⊓ L := Subgroup.mem_inf.mpr ⟨inv_mem haA, inv_mem haL⟩
    have hinv : (π t')⁻¹ = π ⟨w ^ (-k), hwL' (-k)⟩ * π ⟨a⁻¹, hainv.2⟩ := by
      rw [ht'eq, map_mul, mul_inv_rev, ← map_inv, ← map_inv]
      congr 2
      exact Subtype.ext (by simp)
    have hconj : CFSG.conjugate Sb (π t') =
        Sb.map (MulAut.conj (π ⟨w ^ (-k), hwL' (-k)⟩)).toMonoidHom := by
      rw [CFSG.conjugate, hinv, map_conj_mul, hSba a⁻¹ hainv]
    set i : ℕ := ((-k) % 3).toNat with hi
    have hwi : w ^ (-k) = w ^ i := by
      have hw3' : w ^ 3 = 1 := by rw [← hw3]; exact pow_orderOf_eq_one w
      rw [zpow_eq_zpow_emod_three hw3' (-k), hi, ← zpow_natCast,
        Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]
    refine ⟨i, ?_⟩
    have hwi' : (S ⊓ L).map (MulAut.conj (w ^ i)).toMonoidHom ∈
        maxInvariantPiSubgroups L A (piOf 2) :=
      TailProof.map_conj_mem_maxInvariant (pow_mem hwA i)
        (Subgroup.le_normalizer (pow_mem hwL i)) hSL
    have e : (⟨w ^ (-k), hwL' (-k)⟩ : ↥L) = ⟨w ^ i, pow_mem hwL i⟩ := Subtype.ext hwi
    rw [← (hf _ hU).2, ← (hf _ hwi').2, hxeq, hconj,
      TailProof.map_subgroupOf_map_conj π inf_le_right (pow_mem hwL i), e]
  ·
    have hwSb : π ⟨w, hwL⟩ ∈ Subgroup.normalizer (Sb : Set _) := by
      refine mem_normalizer_of_map_conj_eq' ?_
      rw [hSbdef, ← TailProof.map_subgroupOf_map_conj π inf_le_right hwL, heq]
    have hPN : (P₀ : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) ≤ Subgroup.normalizer (Sb : Set _) := by
      rw [hP₀eq]
      rintro _ ⟨t', ht', rfl⟩
      obtain ⟨a, ha, k, htk⟩ := hTmul t' (Subgroup.mem_subgroupOf.mp ht')
      obtain ⟨haA, haL⟩ := Subgroup.mem_inf.mp ha
      have ht'eq : t' = ⟨a, haL⟩ * (⟨w, hwL⟩ : ↥L) ^ k := Subtype.ext (by simp [htk])
      rw [ht'eq, map_mul, map_zpow]
      exact mul_mem (hBSb ⟨⟨a, haL⟩, Subgroup.mem_subgroupOf.mpr haA, rfl⟩) (zpow_mem hwSb k)
    have hsub : maxInvariantPiSubgroups ⊤ B (piOf 2) ⊆ {Sb} := by
      intro V hV
      obtain ⟨x, hxP, -, hxeq⟩ :=
        KFacts.KS14.j2_maxInvariant_two_transitive h415 hJ2 P₀ hBP₀ hB9 hSb hV
      rw [Set.mem_singleton_iff, hxeq, CFSG.conjugate]
      exact Late.map_conj_eq_of_mem_normalizer (hPN (inv_mem hxP))
    have h3 := KFacts.KS14.j2_maxInvariant_two_ncard h415 hJ2 P₀ hBP₀ hB9
    have hle := Set.ncard_le_ncard hsub (Set.finite_singleton Sb)
    rw [h3, Set.ncard_singleton] at hle
    omega

theorem claim1723Orbit_of (h1715 : Item1715) (h1721 : Item1721) : Claim1723Orbit := by
  intro G _ _ A c L Y₀ Y₁ S p P w Q h
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have hJ := h1721 G A c L Y₀ Y₁ S p P h.toSec17Y1
  obtain ⟨hΩ, -, -, -⟩ := h.toSec17Std.hj_facts h1715 h415 hJ
  have hwA : w ∈ Subgroup.normalizer (A : Set G) := (Subgroup.mem_inf.mp h.w_mem).1
  have hwL : w ∈ L := (Subgroup.mem_inf.mp h.w_mem).2
  obtain ⟨h1, h2⟩ := h.toSec17Y1.orbit_of_j2 hJ hwA hwL h.w_not_mem h.orderOf_w
  refine ⟨fun g hg => h1 g hg ?_, h2⟩
  have h3L : 3 ∣ Nat.card L := three_dvd_card_of_mem hwL h.orderOf_w
  exact Sec15R.normalizer_zpowers_le_normalizer_L h.toSec15R h3L
    (normalizer_le_of_omegaA_eq hΩ hg)

end Orbit

end CFSG.RankThree.PartTwo.Sec17
