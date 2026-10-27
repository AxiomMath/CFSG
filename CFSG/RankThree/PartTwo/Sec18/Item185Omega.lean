module

public import CFSG.RankThree.PartTwo.Sec18.Item185Leaves
public import CFSG.RankThree.PartTwo.Sec19.SimsC198Transport
import CFSG.RankThree.PartTwo.Sec18.Item185O23
import CFSG.RankThree.PartTwo.Sec20.SimsFinalL2Lc
import CFSG.RankThree.PartTwo.Sec18.Item183OneProofRemTools
import CFSG.RankThree.PartTwo.Sec18.Item181b
import CFSG.GF2Type.Smith1980Orth.S4Fixed
public import CFSG.RankThree.PartTwo.Sec18.SylowPlane

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item185Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Assembly (IsElemAbelian)

variable {G : Type} [Group G] [Finite G]

private theorem omega_conj_mem_sup {L B : Subgroup G} (hBL : B ≤ L) {y : G} (hy : y ∈ L)
    (hyN : QuotientGroup.mk' (CFSG.pCore 2 ↥L) (⟨y, hy⟩ : ↥L) ∈ Subgroup.normalizer
      (((B.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) : Subgroup _) : Set _))
    {b : G} (hb : b ∈ B) : y * b * y⁻¹ ∈ B ⊔ CFSG.Open.pCoreOf 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbL : (⟨b, hBL hb⟩ : ↥L) ∈ B.subgroupOf L := Subgroup.mem_subgroupOf.mpr hb
  have hmem := (Subgroup.mem_normalizer_iff.mp hyN _).mp
    (Subgroup.mem_map_of_mem (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) hbL)
  rw [← map_inv, ← map_mul, ← map_mul] at hmem
  obtain ⟨w, hw, hwe⟩ := Subgroup.mem_map.mp hmem
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hwe
  have hq : w⁻¹ * ((⟨y, hy⟩ : ↥L) * ⟨b, hBL hb⟩ * (⟨y, hy⟩ : ↥L)⁻¹) ∈ CFSG.pCore 2 ↥L :=
    QuotientGroup.eq.mp hwe
  have hpc : (w : G)⁻¹ * (y * b * y⁻¹) ∈ CFSG.Open.pCoreOf 2 L := by
    have h := (Sec18.mem_pCore_iff_mem_pCoreOf _).mp hq
    simpa using h
  have hw' : (w : G) ∈ B := Subgroup.mem_subgroupOf.mp hw
  have key := Subgroup.mul_mem_sup hw' hpc
  rwa [mul_inv_cancel_left] at key

private theorem omega_le_normalizer_sup {L B Y : Subgroup G} (hBL : B ≤ L) (hYL : Y ≤ L)
    (hY : ∀ y (hy : y ∈ Y), QuotientGroup.mk' (CFSG.pCore 2 ↥L) (⟨y, hYL hy⟩ : ↥L) ∈
      Subgroup.normalizer (((B.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) :
        Subgroup _) : Set _)) :
    Y ≤ Subgroup.normalizer ((B ⊔ CFSG.Open.pCoreOf 2 L : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro y hy
  have hyL : y ∈ L := hYL hy
  apply Sec20.mem_normalizer_of_map_conj_le
  rw [Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rintro _ ⟨b, hb, rfl⟩
    exact omega_conj_mem_sup hBL hyL (hY y hy) hb
  · refine le_trans ?_ le_sup_right
    rintro _ ⟨n, hn, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L hyL) n).mp hn

section Certified


theorem le_oTwoP_centralizer
    (h1812 : Item181_2) (h184 : Item184_1) (h1842 : Item184_2)
    {A M H : Subgroup G} {c : G} (hH : Sec18H G A M H c) :
    A ⊓ inSubgroup perfectResidual H ≤
      (Sec4.oTwoP 3 ↥(M ⊓ Subgroup.centralizer ({c} : Set G))).map
        (M ⊓ Subgroup.centralizer ({c} : Set G)).subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAM : A ≤ M := sec18Std_le hH.toSec18Std
  have hAH : A ≤ H := le_of_mem_scriptH₀ (mem_scriptH_iff_mem_scriptH₀.mp hH.mem_scriptH).1
  have hA : CFSG.Assembly.IsElemAbelian 3 A := (isE27_of_mem_partTwoE hH.mem_partTwoE).1
  have hBE : CFSG.Assembly.IsElemAbelian 3 (A ⊓ inSubgroup perfectResidual H : Subgroup G) :=
    isElemAbelian_of_le hA inf_le_left
  have hB9 : 9 ≤ Nat.card (A ⊓ inSubgroup perfectResidual H : Subgroup G) :=
    (card_inf_of_sec18H h1812 h184 hH).ge
  have hNB : Subgroup.normalizer ((A ⊓ inSubgroup perfectResidual H : Subgroup G) : Set G) ≤ M :=
    (normalizer_le_gamma inf_le_left (two_le_pRank_of_elemAbelian hBE hB9)).trans
      hH.mem_scriptM.2
  have hLM : ¬ inSubgroup perfectResidual H ≤ M :=
    perfectResidual_not_le_of_mem_scriptH hH.toSec18Std hH.mem_scriptH
  have hO2H : CFSG.Open.pCoreOf 2 H ≤ M :=
    le_of_le_normalizer_of_isPGroup_two hH.toSec18Std
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)
      (hAH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
  have hO2L : CFSG.Open.pCoreOf 2 (inSubgroup perfectResidual H) ≤ M :=
    (Rem187QProof.pCoreOf_perfectResidual_le H).trans hO2H
  have hMap := Sec20.SimsFinalL2.map_inf_lc_eq h1812 h184 h1842 hH hAM hNB hLM hO2L
  have hB3 : IsPGroup 3 (A ⊓ inSubgroup perfectResidual H : Subgroup G) :=
    (Sec18.SylowFusion.isSylowOf_lc h1812 h184 hH).isPGroup
  have hBLc : A ⊓ inSubgroup perfectResidual H ≤ Sec18.lc H c :=
    Sec20.SimsFinalL2.inf_le_lc hH
  have hYLc : Sec18.lc H c ⊓ M ≤ Sec18.lc H c := inf_le_left
  have hcond : ∀ y (hy : y ∈ Sec18.lc H c ⊓ M),
      QuotientGroup.mk' (CFSG.pCore 2 ↥(Sec18.lc H c)) (⟨y, hYLc hy⟩ : ↥(Sec18.lc H c)) ∈
        Subgroup.normalizer ((((A ⊓ inSubgroup perfectResidual H).subgroupOf (Sec18.lc H c)).map
          (QuotientGroup.mk' (CFSG.pCore 2 ↥(Sec18.lc H c))) : Subgroup _) : Set _) := by
    intro y hy
    have h1 := Subgroup.mem_map_of_mem (QuotientGroup.mk' (CFSG.pCore 2 ↥(Sec18.lc H c)))
      (Subgroup.mem_subgroupOf.mpr hy :
        (⟨y, hYLc hy⟩ : ↥(Sec18.lc H c)) ∈ (Sec18.lc H c ⊓ M).subgroupOf (Sec18.lc H c))
    rw [hMap] at h1
    exact h1
  have hBY : A ⊓ inSubgroup perfectResidual H ≤ Sec18.lc H c ⊓ M :=
    le_inf hBLc (inf_le_left.trans hAM)
  have hNY : CFSG.Open.pCoreOf 2 (Sec18.lc H c) ≤ Sec18.lc H c ⊓ M :=
    le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 _) (Sec20.SimsFinalL2.pCoreOf_lc_le h1842 hH)
  have hYnorm : Sec18.lc H c ⊓ M ≤ Subgroup.normalizer
      ((A ⊓ inSubgroup perfectResidual H ⊔ CFSG.Open.pCoreOf 2 (Sec18.lc H c) : Subgroup G) :
        Set G) :=
    omega_le_normalizer_sup hBLc hYLc hcond
  have hBNY : A ⊓ inSubgroup perfectResidual H ⊔ CFSG.Open.pCoreOf 2 (Sec18.lc H c) ≤
      Sec18.lc H c ⊓ M := sup_le hBY hNY
  have hBNn : ((A ⊓ inSubgroup perfectResidual H ⊔ CFSG.Open.pCoreOf 2 (Sec18.lc H c)).subgroupOf
      (Sec18.lc H c ⊓ M)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBNY).mpr hYnorm
  have hNn : ((CFSG.Open.pCoreOf 2 (Sec18.lc H c)).subgroupOf (Sec18.lc H c ⊓ M)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNY).mpr
      (fun y hy => CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Sec18.lc H c) (hYLc hy))
  have hYX : Sec18.lc H c ⊓ M ≤ M ⊓ Subgroup.centralizer ({c} : Set G) :=
    le_inf inf_le_right (inf_le_left.trans (Sec18.SylowFusion.lc_le_centralizer H c))
  have hXN : M ⊓ Subgroup.centralizer ({c} : Set G) ≤
      Subgroup.normalizer ((Sec18.lc H c ⊓ M : Subgroup G) : Set G) := by
    intro x hx
    exact Sec20.mem_normalizer_inf_of_mem
      (Sec20.SimsFinalL2.centralizer_le_normalizer_lc h1842 hH hx.2) (Subgroup.le_normalizer hx.1)
  exact (le_oTwoP_of_normal_closure hBY hNY (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) hNn
      hB3 hBNn).trans
    (oTwoP_le_of_normal hYX ((Subgroup.normal_subgroupOf_iff_le_normalizer hYX).mpr hXN))

end Certified

theorem omega_quot {M K B : Subgroup G} {c : G} (hK : K ∈ oTwoComponentsIn M)
    (hBK : B ≤ K) (hcN : c ∈ Subgroup.normalizer (K : Set G)) (hc3 : c ^ 3 = 1)
    (hΩ : B ≤ (Sec4.oTwoP 3 ↥(M ⊓ Subgroup.centralizer ({c} : Set G))).map
      (M ⊓ Subgroup.centralizer ({c} : Set G)).subtype) :
    Sec19.SimsC198.actImage K B ≤
      ((oTwoThreeFixed (Sec19.SimsC198.quotAct K ⟨c, hcN⟩)).map
        (MulAut.conj : (K ⧸ CFSG.pCore 2 K) →* MulAut (K ⧸ CFSG.pCore 2 K))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKM : K ≤ M := by
    obtain ⟨L, -, hL⟩ := hK
    rw [← hL]
    exact Subgroup.map_subtype_le L
  have hYX : K ⊓ Subgroup.centralizer ({c} : Set G) ≤ M ⊓ Subgroup.centralizer ({c} : Set G) :=
    le_inf (inf_le_left.trans hKM) inf_le_right
  have hBC : B ≤ Subgroup.centralizer ({c} : Set G) := fun b hb => by
    obtain ⟨t, -, rfl⟩ := Subgroup.mem_map.mp (hΩ hb)
    exact t.2.2
  have hBY : B ≤ K ⊓ Subgroup.centralizer ({c} : Set G) := fun b hb => ⟨hBK hb, hBC hb⟩
  have hΩ' : B ≤ (Sec4.oTwoP 3 ↥(K ⊓ Subgroup.centralizer ({c} : Set G))).map
      (K ⊓ Subgroup.centralizer ({c} : Set G)).subtype := fun b hb =>
    inf_oTwoP_le hYX ⟨hΩ hb, hBY hb⟩
  set σ := Sec19.SimsC198.quotAct K ⟨c, hcN⟩ with hσ
  have hYK : K ⊓ Subgroup.centralizer ({c} : Set G) ≤ K := inf_le_left
  let g : ↥(K ⊓ Subgroup.centralizer ({c} : Set G)) →* K ⧸ CFSG.pCore 2 K :=
    (QuotientGroup.mk' (CFSG.pCore 2 K)).comp (Subgroup.inclusion hYK)
  have hpO : IsPGroup 2 (CFSG.Open.pCoreOf 2 K) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K
  have hcnorm : ∀ h ∈ CFSG.Open.pCoreOf 2 K, c * h * c⁻¹ ∈ CFSG.Open.pCoreOf 2 K := fun h hh =>
    (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K hcN) h).mp hh
  have hgg : ∀ y : ↥(K ⊓ Subgroup.centralizer ({c} : Set G)), σ (g y) = g y := by
    rintro ⟨y, hy⟩
    have hyK : y ∈ K := hy.1
    have hyc : y * c = c * y := Subgroup.mem_centralizer_singleton_iff.mp hy.2
    have hc' : c * y * c⁻¹ = y := by rw [← hyc, mul_inv_cancel_right]
    have hk : c * y * c⁻¹ ∈ K := by rw [hc']; exact hyK
    show Sec19.SimsC198.quotAct K ⟨c, hcN⟩ ((⟨y, hyK⟩ : K) : K ⧸ CFSG.pCore 2 K) =
      ((⟨y, hyK⟩ : K) : K ⧸ CFSG.pCore 2 K)
    rw [Sec19.SimsC198.quotAct_mk K ⟨c, hcN⟩ ⟨y, hyK⟩ hk]
    congr 1
    exact Subtype.ext hc'
  have hgfix : ∀ y : ↥(K ⊓ Subgroup.centralizer ({c} : Set G)),
      g y ∈ fixedSubgroup σ := fun y => hgg y
  have hgsurj : Function.Surjective (g.codRestrict (fixedSubgroup σ) hgfix) := by
    rintro ⟨z, hz⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 K) z
    have hk' : c * (x : G) * c⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hcN x).mp x.2
    have e := Sec19.SimsC198.quotAct_mk K ⟨c, hcN⟩ x hk'
    have hx' : ((⟨c * (x : G) * c⁻¹, hk'⟩ : K) : K ⧸ CFSG.pCore 2 K) =
        ((x : K) : K ⧸ CFSG.pCore 2 K) := by
      rw [← e]
      exact hz
    have hxc : (x : G)⁻¹ * (c * (x : G) * c⁻¹) ∈ CFSG.Open.pCoreOf 2 K :=
      (Sec19.SimsC198.Transport.mem_pCore_iff_mem_pCoreOf K _).mp (QuotientGroup.eq.mp hx'.symm)
    obtain ⟨h, hh, hfix⟩ :=
      CFSG.GF2Type.Smith1980Orth.exists_fixed_mem_coset hpO hc3 hcnorm hxc
    have hyK : (x : G) * h ∈ K := K.mul_mem x.2 (CFSG.LieType.BorelTits.pCoreOf_le 2 K hh)
    have hyc : c * ((x : G) * h) = ((x : G) * h) * c := by
      calc c * ((x : G) * h) = c * ((x : G) * h) * c⁻¹ * c := by group
        _ = ((x : G) * h) * c := by rw [hfix]
    refine ⟨⟨(x : G) * h, ⟨hyK, Subgroup.mem_centralizer_singleton_iff.mpr hyc.symm⟩⟩, ?_⟩
    apply Subtype.ext
    show QuotientGroup.mk' (CFSG.pCore 2 K) (⟨(x : G) * h, hyK⟩ : K) =
      QuotientGroup.mk' (CFSG.pCore 2 K) x
    symm
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply]
    apply QuotientGroup.eq.mpr
    exact (Sec19.SimsC198.Transport.mem_pCore_iff_mem_pCoreOf K _).mpr (by simpa using hh)
  have hP := oTwoP_map_le_of_surjective (g.codRestrict (fixedSubgroup σ) hgfix) hgsurj
  have hmemOTF : ∀ (d : G) (hdK : d ∈ K), d ∈ B →
      (QuotientGroup.mk' (CFSG.pCore 2 K) (⟨d, hdK⟩ : K)) ∈ oTwoThreeFixed σ := by
    intro d hdK hdB
    obtain ⟨z, hz, hzd⟩ := Subgroup.mem_map.mp (hΩ' hdB)
    refine Subgroup.mem_map.mpr ⟨g.codRestrict (fixedSubgroup σ) hgfix z,
      hP (Subgroup.mem_map_of_mem _ hz), ?_⟩
    show QuotientGroup.mk' (CFSG.pCore 2 K) (Subgroup.inclusion hYK z) = _
    congr 1
    exact Subtype.ext hzd
  intro φ hφ
  obtain ⟨d, hdN, hdB, rfl⟩ := Sec19.SimsC198.mem_actImage hφ
  rw [Sec19.SimsC198.quotAct_conj K (hBK hdB) hdN]
  exact Subgroup.mem_map.mpr ⟨_, hmemOTF d (hBK hdB) hdB, rfl⟩

end CFSG.RankThree.PartTwo.Sec18.Item185Proof
