module

public import CFSG.RankThree.PartTwo.Sec15.Item1511ProofTools
public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.RankThree.PartTwo.Sec13.Item13Prod
import CFSG.RankThree.PartTwo.Sec13.Item13Theta
import CFSG.RankThree.PartTwo.Sec13.Item13Plane
import CFSG.RankThree.PartTwo.Sec13.Item133
import CFSG.RankThree.PartTwo.Sec13.OmegaNonempty
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore
import CFSG.RankThree.Theta.PartTwoLocalQuotientAlphaNormalizer
import CFSG.RankThree.PartTwo.Sec6.Item612Basic
import CFSG.LieType.BorelTits.Basic
import CFSG.RankThree.PartTwo.Sec6.Item612Core

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof1510

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL projSU aschCore)

variable {G : Type} [Group G] [Finite G]

theorem facts_of_quot {A L : Subgroup G} {c : G} (hD : Sec13Data G A c L) {S : Type*} [Group S]
    [hSp : Group.IsPerfect S] [hSs : IsSimpleGroup S]
    (hq : letI := kerAO2_normal hD.le_normalizer
      Nonempty (↥(A ⊔ L) ⧸ kerAO2 A L ≃* Multiplicative (ZMod 3) × S)) :
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* S) ∧ Nat.card (A ⊓ L : Subgroup G) = 9 := by
  have hAL : A ≤ Subgroup.normalizer (L : Set G) := hD.le_normalizer
  let _ := kerAO2_normal hAL
  obtain ⟨φ⟩ := hq
  set N := A ⊔ L with hNdef
  set K := kerAO2 A L with hKdef
  set π := QuotientGroup.mk' K with hπdef
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective K
  have hLN : L ≤ N := le_sup_right
  have hAN : A ≤ N := le_sup_left
  set LN := L.subgroupOf N with hLNdef
  set Λ := LN.map π with hΛdef
  have hLNn : LN.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLN).mpr (sup_le hAL Subgroup.le_normalizer)
  have hΛn : Λ.Normal := hLNn.map π hπs
  have hself : (A ⊔ L).subgroupOf N = ⊤ := Subgroup.subgroupOf_self _
  have hsup : Λ ⊔ (A.subgroupOf N).map π = ⊤ := by
    rw [hΛdef, ← Subgroup.map_sup, hLNdef, ← Subgroup.subgroupOf_sup hLN hAN, sup_comm L A,
      hself, Subgroup.map_top_of_surjective π hπs]
  have hAc : IsMulCommutative ((A.subgroupOf N).map π) := by
    refine ⟨⟨?_⟩⟩
    rintro ⟨_, ⟨x, hx, rfl⟩⟩ ⟨_, ⟨y, hy, rfl⟩⟩
    apply Subtype.ext
    show π x * π y = π y * π x
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hD.commute (Subgroup.mem_subgroupOf.mp hx) (Subgroup.mem_subgroupOf.mp hy))
  have hcomm_le : commutator (↥N ⧸ K) ≤ Λ :=
    Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup hAc
  have hLperf : Group.IsPerfect L :=
    Sec6.isPerfect_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt
  have hLNperf : Group.IsPerfect LN :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hLN).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hLN).symm.surjective
  have hΛperf : Group.IsPerfect Λ :=
    Group.IsPerfect.ofSurjective (f := π.subgroupMap LN) (π.subgroupMap_surjective LN)
  have hle_comm : Λ ≤ commutator (↥N ⧸ K) := by
    have h1 : (⊤ : Subgroup Λ).map Λ.subtype = Λ := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    calc Λ = (commutator Λ).map Λ.subtype := by rw [hΛperf.commutator_eq_top, h1]
      _ = ⁅Λ, Λ⁆ := by rw [commutator_def, Subgroup.map_commutator, h1]
      _ ≤ commutator (↥N ⧸ K) := Subgroup.commutator_mono le_top le_top
  have hΛeq : Λ = commutator (↥N ⧸ K) := le_antisymm hle_comm hcomm_le
  have hφΛ : Λ.map φ.toMonoidHom = (⊥ : Subgroup (Multiplicative (ZMod 3))).prod ⊤ := by
    rw [hΛeq, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ φ.surjective, ← commutator_def, commutator_zthree_prod,
      hSp.commutator_eq_top]
  have eΛ : Λ ≃* S :=
    (Λ.equivMapOfInjective _ φ.injective).trans ((MulEquiv.subgroupCongr hφΛ).trans
      ((Subgroup.prodEquiv _ _).trans (MulEquiv.uniqueProd.trans Subgroup.topEquiv)))
  set f : ↥L →* ↥N ⧸ K := π.comp (Subgroup.inclusion hLN) with hfdef
  have hfr : f.range = Λ := by
    ext y
    constructor
    · rintro ⟨l, rfl⟩
      exact ⟨Subgroup.inclusion hLN l, Subgroup.mem_subgroupOf.mpr l.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩, ?_⟩
      rfl
  have hPn : (CFSG.Open.pCore 2 ↥L).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hfk : f.ker = CFSG.Open.pCore 2 ↥L := by
    ext l
    rw [MonoidHom.mem_ker, hfdef, MonoidHom.comp_apply, hπdef, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, hKdef, kerAO2, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_map_iff_mem L.subtype_injective
  have eL : (↥L ⧸ CFSG.Open.pCore 2 ↥L) ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq hfk.symm).trans
      ((QuotientGroup.quotientKerEquivRange f).trans ((MulEquiv.subgroupCongr hfr).trans eΛ))
  have hθ : aschbacherSolvableCore 3 ↥L = CFSG.Open.pCore 2 ↥L := by
    obtain ⟨hθs, -, -, hmax, -⟩ :=
      solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hP2 : IsPGroup 2 (CFSG.Open.pCore 2 ↥L) := CFSG.LieType.BorelTits.pCore_isPGroup 2
    have hP3 : ¬ 3 ∣ Nat.card (CFSG.Open.pCore 2 ↥L) := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP2
      rw [hn]
      intro h3
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.prime_three.dvd_of_dvd_pow h3)
      omega
    have : Group.IsNilpotent (CFSG.Open.pCore 2 ↥L) := hP2.isNilpotent
    refine le_antisymm ?_ (hmax _ hPn inferInstance hP3)
    set M := (aschbacherSolvableCore 3 ↥L).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥L)) with hM
    have hMn : M.Normal := (inferInstance : (aschbacherSolvableCore 3 ↥L).Normal).map _
      (QuotientGroup.mk'_surjective _)
    have hMs : Group.IsSolvable M :=
      Group.isSolvable_of_surjective (f := (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥L)).subgroupMap
        (aschbacherSolvableCore 3 ↥L)) (MonoidHom.subgroupMap_surjective _ _)
    have hMe : (M.map eL.toMonoidHom).Normal := hMn.map _ eL.surjective
    have hbot : M.map eL.toMonoidHom = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.map eL.toMonoidHom) with h | h
      · exact h
      · exfalso
        have hs : Group.IsSolvable (M.map eL.toMonoidHom) :=
          Group.isSolvable_of_surjective (f := eL.toMonoidHom.subgroupMap M)
            (MonoidHom.subgroupMap_surjective _ _)
        rw [h] at hs
        have hS : Group.IsSolvable S :=
          Group.isSolvable_of_surjective
            (f := (Subgroup.topEquiv : (⊤ : Subgroup S) ≃* S).toMonoidHom)
            Subgroup.topEquiv.surjective
        exact Group.IsPerfect.not_isSolvable S hS
    have hM1 : M = ⊥ := (Subgroup.map_eq_bot_iff_of_injective M eL.injective).mp hbot
    intro x hx
    have hxM : QuotientGroup.mk' (CFSG.Open.pCore 2 ↥L) x ∈ M := Subgroup.mem_map_of_mem _ hx
    rw [hM1, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hxM
    exact hxM
  refine ⟨⟨(QuotientGroup.quotientMulEquivOfEq hθ).trans eL⟩, ?_⟩
  have hidx : Λ.index = 3 := by
    rw [← Subgroup.index_map_equiv Λ φ]
    change (Λ.map φ.toMonoidHom).index = 3
    rw [hφΛ, Subgroup.index_prod, Subgroup.index_bot, Subgroup.index_top, mul_one,
      Nat.card_congr (Multiplicative.toAdd (α := ZMod 3)), Nat.card_zmod]
  have hKLN : π.ker ≤ LN := by
    rw [hπdef, QuotientGroup.ker_mk']
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 L
      (Subgroup.mem_subgroupOf.mp hx))
  have hidx2 : LN.index = 3 := by
    rw [← Subgroup.index_map_eq LN hπs hKLN]
    exact hidx
  have hcardN : Nat.card N = 3 * Nat.card L := by
    have h1 := Subgroup.card_mul_index LN
    rw [hidx2, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLN).toEquiv] at h1
    rw [← h1, mul_comm]
  have h1 := Sec6.card_sup_mul_card_inf hAL
  rw [← hNdef, hcardN, hD.card_eq] at h1
  have hLpos : 0 < Nat.card L := Nat.card_pos
  have h2 : Nat.card L * (3 * Nat.card (A ⊓ L : Subgroup G)) = Nat.card L * 27 := by
    linarith [h1]
  have h3 := Nat.eq_of_mul_eq_mul_left hLpos h2
  omega

theorem zpowers_eq_of_le_normalizer {A L : Subgroup G} {c : G} (hD : Sec13Data G A c L)
    (hcL : c ∉ L) (h9 : Nat.card (A ⊓ L : Subgroup G) = 9)
    (hirr : Sec21.IsIrreducibleOn (Sec4.autIn (L ⊓ Subgroup.normalizer (A : Set G)) (A ⊓ L)))
    {d : G} (hdA : d ∈ A) (hd3 : Nat.card (Subgroup.zpowers d) = 3)
    (hN : L ⊓ Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers d : Set G)) :
    Subgroup.zpowers d = Subgroup.zpowers c := by
  have hcB : c ∉ A ⊓ L := fun h => hcL h.2
  have hAa := eq_sup_of_card_nine hD h9 hcB
  have hKa : ∀ k ∈ L ⊓ Subgroup.normalizer (A : Set G), k * c = c * k := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer hk.1)
  have hKB : L ⊓ Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) := fun k hk =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hk.2, Subgroup.le_normalizer hk.1⟩
  rcases eq_of_le_of_le_normalizer hD.isElemAbelian hD.card_eq hD.mem_A hAa hcB h9 hKa hirr
      (Subgroup.zpowers_le.mpr hdA) hN hKB with h | h | h | h
  · rw [h, Subgroup.card_bot] at hd3
    norm_num at hd3
  · exact h
  · rw [h, h9] at hd3
    norm_num at hd3
  · rw [h, hD.card_eq] at hd3
    norm_num at hd3

omit [Finite G] in
theorem eq_of_eq_map_conj {F F' : Subgroup G} {w : G}
    (hF : F' = F.map (MulAut.conj w).toMonoidHom)
    (hw : w ∈ Subgroup.normalizer (F' : Set G)) : F = F' := by
  have h1 : F'.map (MulAut.conj w⁻¹).toMonoidHom = F := by
    rw [hF, Late.map_conj_map_conj, inv_mul_cancel, Late.map_conj_one]
  have h2 : F'.map (MulAut.conj w⁻¹).toMonoidHom = F' :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (inv_mem hw)
  rw [← h1, h2]

theorem normalizer_le_sup_of_isSylowOf {B P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P (Subgroup.centralizer (B : Set G))) :
    Subgroup.normalizer (B : Set G) ≤ Subgroup.centralizer (B : Set G) ⊔
      (Subgroup.normalizer (B : Set G) ⊓ Subgroup.normalizer (P : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro x hx
  set CB := Subgroup.centralizer (B : Set G) with hCB
  have hxCB : CB.map (MulAut.conj x).toMonoidHom = CB := by
    rw [hCB, map_conj_centralizer]
    congr 2
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hx
  have hPx : CFSG.ABGLocalTools.IsSylowOf 3 (P.map (MulAut.conj x).toMonoidHom) CB := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card ?_ ?_
    · rw [← hxCB]
      exact Subgroup.map_mono hP.le
    · rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]
      exact hP.card_eq
  obtain ⟨z, hzCB, hzP⟩ := hP.exists_mem_conj hPx
  have hle : P.map (MulAut.conj (z⁻¹ * x)).toMonoidHom ≤ P := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 : x * y * x⁻¹ ∈ P.map (MulAut.conj x).toMonoidHom := ⟨y, hy, rfl⟩
    have h2 := (hzP _).mp h1
    have h3 : (MulAut.conj (z⁻¹ * x)).toMonoidHom y = z⁻¹ * (x * y * x⁻¹) * z := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [h3]
    exact h2
  have hw : z⁻¹ * x ∈ Subgroup.normalizer (P : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj _).injective]))
  have hwB : z⁻¹ * x ∈ Subgroup.normalizer (B : Set G) :=
    mul_mem (inv_mem (Subgroup.centralizer_le_normalizer _ hzCB)) hx
  have hxz : x = z * (z⁻¹ * x) := by group
  rw [hxz]
  exact Subgroup.mul_mem_sup hzCB ⟨hwB, hw⟩

omit [Finite G] in
theorem map_conj_omegaOneThree (P : Subgroup G) (y : G) :
    (omegaOneThree P).map (MulAut.conj y).toMonoidHom =
      omegaOneThree (P.map (MulAut.conj y).toMonoidHom) := by
  unfold omegaOneThree
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨z, ⟨hzP, hz3⟩, rfl⟩
    exact ⟨⟨z, hzP, rfl⟩, by rw [← map_pow, hz3, map_one]⟩
  · rintro ⟨⟨z, hzP, rfl⟩, hz3⟩
    refine ⟨z, ⟨hzP, ?_⟩, rfl⟩
    rw [← map_pow] at hz3
    exact (MulAut.conj y).injective (by simpa using hz3)

omit [Finite G] in
theorem normalizer_le_of_eq_omegaOneThree {A P : Subgroup G} (hA : A = omegaOneThree P) :
    Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (A : Set G) := by
  intro y hy
  have hPy : P.map (MulAut.conj y).toMonoidHom = P := Subgroup.mem_normalizer_iff_map_conj_eq.mp hy
  have h : A.map (MulAut.conj y).toMonoidHom = A := by
    rw [hA, map_conj_omegaOneThree, hPy]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h

theorem normalizer_le_normalizer_thetaAlpha (B : Subgroup G) :
    Subgroup.normalizer (B : Set G) ≤ Subgroup.normalizer (thetaAlpha 3 B : Set G) := by
  intro y hy
  have hBy : B.map (MulAut.conj y).toMonoidHom = B := Subgroup.mem_normalizer_iff_map_conj_eq.mp hy
  have h : (thetaAlpha 3 B).map (MulAut.conj y).toMonoidHom = thetaAlpha 3 B := by
    rw [thetaAlpha_map_equiv Nat.prime_three (MulAut.conj y) B, hBy]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h

theorem commutator_pCoreOf_inf_le_thetaAlpha {A L B : Subgroup G} {c : G} (hcB : c ∈ B)
    (hLN : Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (L : Set G))
    (hPC : ∀ e ∈ B, e ≠ 1 →
      ⁅inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer (B : Set G)), A⁆ ≤
        inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({e} : Set G))) :
    ⁅CFSG.Open.pCoreOf 2 L ⊓ Subgroup.centralizer (B : Set G), A⁆ ≤ thetaAlpha 3 B := by
  set X := Subgroup.centralizer (B : Set G) with hXdef
  set N := CFSG.Open.pCoreOf 2 L ⊓ X with hNdef
  have hNX : N ≤ X := inf_le_right
  have hXc : X ≤ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hcB)
  have hXN : X ≤ Subgroup.normalizer (N : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L (hLN (hXc hx)),
        Subgroup.le_normalizer hx⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN2 : IsPGroup 2 N := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le inf_le_left
  have hNs : Group.IsSolvable N := by
    have : Group.IsNilpotent N := hN2.isNilpotent
    infer_instance
  have hN3 : ¬ 3 ∣ Nat.card N := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hN2
    rw [hn]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hθ := Sec6.le_theta_of_normal hNX hXN hNs hN3
  have hT : ⁅inSubgroup (aschbacherSolvableCore 3) X, A⁆ ≤ thetaT 3 B :=
    le_iInf fun e => le_iInf fun he => le_iInf fun he1 => hPC e he he1
  exact (Subgroup.commutator_mono hθ le_rfl).trans (hT.trans le_sup_right)

theorem aschCore_le_normalizer_of {A X : Subgroup G} (h27 : Nat.card A = 27)
    (hB : ∀ B : Subgroup G, B ≤ A → Nat.card B = 9 →
      Subgroup.normalizer (B : Set G) ≤ Subgroup.normalizer (X : Set G))
    (hW : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (X : Set G)) :
    aschCore 2 3 A ≤ Subgroup.normalizer (X : Set G) := by
  refine sSup_le ?_
  rintro _ ⟨U, hUA, hU2, -, rfl⟩
  rcases CFSG.RankThree.Theta.card_eq_or_eq_of_two_le_pRank Nat.prime_three
      (by rw [h27]; norm_num) hUA hU2 with hU | hU
  · exact hB U hUA (by rw [hU]; norm_num)
  · rw [hU]
    exact hW

theorem mem_partTwoS_of_thetaAlpha_eq_bot {A : Subgroup G} (hAF : A ∈ partTwoF G)
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (h27 : Nat.card A = 27)
    (hα : ∀ D : Subgroup G, D ≤ A → Nat.card D = 9 → thetaAlpha 3 D = ⊥) : A ∈ partTwoS G := by
  refine ⟨hAF, fun a ha ha1 => ?_, fun D hDA hD9 => ?_⟩
  · rw [commutator_theta_eq_bot hA h27 ha ha1 hα, Subgroup.card_bot]
    exact odd_one
  · have hT : thetaT 3 D = ⊥ := eq_bot_iff.mpr
      ((le_sup_right : thetaT 3 D ≤ thetaJ 3 D ⊔ thetaT 3 D).trans (hα D hDA hD9).le)
    rw [hT, Subgroup.card_bot]
    exact odd_one

end CFSG.RankThree.PartTwo.Sec15.Proof1510
