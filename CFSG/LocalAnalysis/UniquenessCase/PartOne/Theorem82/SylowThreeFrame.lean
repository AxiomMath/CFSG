module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoSylow
import CFSG.GroupTheory.CyclicAutOmega
import CFSG.GroupTheory.PGroup.CardCoprime
import CFSG.LocalAnalysis.SectionRank.AmbientRank
import CFSG.LocalAnalysis.UniquenessCase.UC6S846g
import CFSG.RankThree.PartOne.S11d.OutCentral
import CFSG.Sporadic.Schreier.J4SSylowBase
import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace SylowThreeData

variable (d : SylowThreeData G)

private theorem A_le_AA (i : Fin 3) : d.A i ≤ d.AA := by
  rw [d.AA_def]
  fin_cases i
  · exact le_sup_left.trans le_sup_left
  · exact le_sup_right.trans le_sup_left
  · exact le_sup_right

private theorem L_le_M : d.L ≤ d.M := by
  rw [d.hL]
  exact sup_le (sup_le (d.hLM 0) (d.hLM 1)) (d.hLM 2)

theorem A_eq_AA_inf_Lf (i : Fin 3) : d.A i = d.AA ⊓ d.Lf i := by
  refine le_antisymm (le_inf (SylowThreeData.A_le_AA d i) ?_) ?_
  · exact (d.A_le_H i).trans (d.H_le_Lf i)
  · intro x hx
    rw [d.mem_A_iff]
    exact ⟨⟨d.AA_le_S hx.1, hx.2⟩, d.isElemAbelian_AA.2 x hx.1⟩

theorem exists_mem_Lf_inv_A (i : Fin 3) :
    ∃ n ∈ d.Lf i, ∀ a ∈ d.A i, n * a * n⁻¹ = a⁻¹ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let X := ↥(d.Lf i)
  have : Group.IsPerfect X := Subgroup.isPerfect_iff.mpr (d.hperf i)
  let S : Subgroup X := (d.H i).subgroupOf (d.Lf i)
  have hS3 : IsPGroup 3 S := (d.isSylowOf_H i).isPGroup.comap_subtype
  have hST : CFSG.ABGLocalTools.IsSylowOf 3 S ⊤ := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (K := d.Lf i)]
    simpa [S, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (d.H_le_Lf i),
      Subgroup.map_top, Subgroup.range_subtype] using d.isSylowOf_H i
  have hSindex : ¬ 3 ∣ S.index := by
    simpa [Subgroup.relIndex_top_right] using (CFSG.ABGLocalTools.isSylowOf_iff.mp hST).2.2
  let Q : Sylow 3 X := hS3.toSylow hSindex
  have hSne : S ≠ ⊥ := by
    intro hbot
    have hHbot : d.H i = ⊥ := by
      have hsub : (d.H i).subgroupOf (d.Lf i) = ⊥ := by rw [← hbot]
      have hdisj : Disjoint (d.H i) (d.Lf i) := Subgroup.subgroupOf_eq_bot.mp hsub
      have hinf : d.H i ⊓ d.Lf i = ⊥ := hdisj.eq_bot
      have hle : d.H i ⊓ d.Lf i = d.H i := inf_eq_left.mpr (d.H_le_Lf i)
      rwa [hle] at hinf
    exact d.H_ne_bot i hHbot
  have hQne : (Q : Subgroup X) ≠ ⊥ := by
    simpa [Q] using hSne
  have hrankX : CFSG.pRank 3 (⊤ : Subgroup X) ≤ 1 := by
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank,
      ← CFSG.SectionRank.pRank_eq_open_pRank_top 3 ↥(d.Lf i),
      CFSG.SectionRank.pRank_coe_eq_openPRank, d.hrank i]
  have : IsCyclic ↥S :=
    CFSG.RankThree.PartOne.isCyclic_of_pRank_le_one Nat.prime_three (by norm_num)
      le_top hS3 hrankX
  have : IsCyclic ↥Q := (show IsCyclic ↥S from inferInstance)
  obtain ⟨n, hnN, hnInv⟩ :=
    CFSG.GroupTheory.exists_mem_normalizer_conj_eq_inv_of_perfect Q hQne
  refine ⟨(d.Lf i).subtype n, n.2, ?_⟩
  intro a haA
  obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp haA
  let e : ↥S ≃* ↥(d.H i) := Subgroup.subgroupOfEquivOfLe (d.H_le_Lf i)
  let b : ↥S := e.symm a'
  have hbOmega : b ∈ CFSG.omega₁ ↥S (p := 3) := by
    have hmap : (CFSG.omega₁ ↥S (p := 3)).map e.toMonoidHom =
        CFSG.omega₁ ↥(d.H i) (p := 3) :=
      CFSG.GroupTheory.omega_map_mulEquiv e 3 1
    rw [← hmap] at ha'
    obtain ⟨c, hc, hce⟩ := Subgroup.mem_map.mp ha'
    have hcb : c = b := e.injective (by simpa [b] using hce)
    rwa [hcb] at hc
  have hbval : (b : X) = (Subgroup.inclusion (d.H_le_Lf i) a' : d.Lf i) := rfl
  have hb : (b : X) ∈ (CFSG.omega₁ ↥Q (p := 3)).map (Q : Subgroup X).subtype := by
    change (b : X) ∈ (CFSG.omega₁ ↥S (p := 3)).map S.subtype
    simpa using Subgroup.mem_map_of_mem S.subtype hbOmega
  have hinv := hnInv (b : X) hb
  have hinv' : (d.Lf i).subtype (n * (b : X) * n⁻¹) =
      (d.Lf i).subtype ((b : X)⁻¹) := congrArg (d.Lf i).subtype hinv
  have hinv'' : (d.Lf i).subtype n * (d.Lf i).subtype (b : X) *
      ((d.Lf i).subtype n)⁻¹ = ((d.Lf i).subtype (b : X))⁻¹ := by
    simpa only [map_mul, map_inv] using hinv'
  simpa [hbval, Subgroup.inclusion] using hinv''

theorem exists_sign_in_product (i : Fin 3) :
    ∃ l ∈ d.L, l ∈ Subgroup.normalizer (d.AA : Set G) ∧
      ∀ j, ∀ a ∈ d.A j, l * a * l⁻¹ = if j = i then a⁻¹ else a := by
  classical
  obtain ⟨n, hnLf, hnInv⟩ := d.exists_mem_Lf_inv_A i
  let Y : Subgroup G := d.L
  let Nbar : Subgroup ↥Y := (CFSG.Open.pCoreOf 2 d.M).subgroupOf Y
  have hY_le_M : Y ≤ d.M := d.L_le_M
  have hNbar_normal : Nbar.Normal := by
    change ((CFSG.Open.pCoreOf 2 d.M).subgroupOf Y).Normal
    rw [← Subgroup.inf_subgroupOf_right (CFSG.Open.pCoreOf 2 d.M) Y]
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer
      (inf_le_right : CFSG.Open.pCoreOf 2 d.M ⊓ Y ≤ Y)).mpr ?_
    have hYnormN : Y ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 d.M : Set G) :=
      hY_le_M.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 d.M)
    exact (le_inf hYnormN Subgroup.le_normalizer).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  let : Nbar.Normal := hNbar_normal
  have hNbar_p : IsPGroup 2 ↥Nbar := by
    change IsPGroup 2 ↥((CFSG.Open.pCoreOf 2 d.M).subgroupOf Y)
    rw [← Subgroup.comap_subtype]
    exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 d.M).comap_subtype
  have hNbar_three : ¬ 3 ∣ Nat.card ↥Nbar :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup hNbar_p Nat.prime_three (by norm_num)
  have hcop : Nat.Coprime 3 (Nat.card ↥Nbar) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hNbar_three
  let q : ↥Y →* ↥Y ⧸ Nbar := QuotientGroup.mk' Nbar
  let AY : Subgroup ↥Y := d.AA.subgroupOf Y
  have hAY_p : IsPGroup 3 ↥AY := by
    change IsPGroup 3 ↥(d.AA.subgroupOf Y)
    rw [← Subgroup.comap_subtype]
    exact (d.isElemAbelian_AA.isPGroup).comap_subtype
  have : Fact (IsPGroup 3 ↥AY) := ⟨hAY_p⟩
  let nY : ↥Y := ⟨n, d.Lf_le_L i hnLf⟩
  let AYl : Fin 3 → Subgroup ↥Y := fun l => (d.A l).subgroupOf Y
  have hAY_eq : AY = AYl 0 ⊔ AYl 1 ⊔ AYl 2 := by
    show d.AA.subgroupOf Y = _
    rw [show d.AA = d.A 0 ⊔ d.A 1 ⊔ d.A 2 from rfl,
      Subgroup.subgroupOf_sup (sup_le (d.A_le_L 0) (d.A_le_L 1)) (d.A_le_L 2),
      Subgroup.subgroupOf_sup (d.A_le_L 0) (d.A_le_L 1)]
  have hAx_fix (l : Fin 3) :
      ((AYl l).map q).map (MulAut.conj (q nY)).toMonoidHom = (AYl l).map q := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro z ⟨y, hy, rfl⟩
      obtain ⟨aY, haY, rfl⟩ := Subgroup.mem_map.mp hy
      have ha : (aY : G) ∈ d.A l := Subgroup.mem_subgroupOf.mp haY
      by_cases hli : l = i
      · have ha_i : (aY : G) ∈ d.A i := hli ▸ ha
        have hconj : n * (aY : G) * n⁻¹ = (aY : G)⁻¹ := hnInv _ ha_i
        have hsub : nY * aY * nY⁻¹ = aY⁻¹ := by
          ext
          simpa [nY] using hconj
        have haYinv : aY⁻¹ ∈ AYl i :=
          Subgroup.mem_subgroupOf.mpr ((d.A i).inv_mem ha_i)
        have hqeq : q nY * q aY * (q nY)⁻¹ = q aY⁻¹ := by
          calc q nY * q aY * (q nY)⁻¹ = q (nY * aY * nY⁻¹) := by simp
            _ = q aY⁻¹ := by rw [hsub]
        rw [show AYl l = AYl i by rw [hli]]
        change q nY * q aY * (q nY)⁻¹ ∈ (AYl i).map q
        rw [hqeq]
        exact Subgroup.mem_map_of_mem q haYinv
      · have hil : i ≠ l := fun h => hli h.symm
        have hnY : n ∈ Y := d.Lf_le_L i hnLf
        have haY' : (aY : G) ∈ Y := d.A_le_L l ha
        have hcommN : ⁅n, (aY : G)⁆ ∈ CFSG.Open.pCoreOf 2 d.M :=
          d.hcomm i l hil (Subgroup.commutator_mem_commutator hnLf
            ((d.A_le_H l).trans (d.H_le_Lf l) ha))
        have hconj : n * (aY : G) * n⁻¹ = ⁅n, (aY : G)⁆ * (aY : G) := by
          rw [commutatorElement_def]
          group
        have hmemY : ⁅n, (aY : G)⁆ ∈ Y := by
          rw [commutatorElement_def]
          exact Y.mul_mem (Y.mul_mem (Y.mul_mem hnY haY') (Y.inv_mem hnY)) (Y.inv_mem haY')
        have hcy : (⟨⁅n, (aY : G)⁆, hmemY⟩ : ↥Y) ∈ Nbar :=
          Subgroup.mem_subgroupOf.mpr hcommN
        have hqcy : q ⟨⁅n, (aY : G)⁆, hmemY⟩ = 1 := by
          change (QuotientGroup.mk' Nbar ⟨⁅n, (aY : G)⁆, hmemY⟩ : ↥Y ⧸ Nbar) = 1
          rw [QuotientGroup.mk'_apply]
          exact (QuotientGroup.eq_one_iff _).mpr hcy
        have hsub : nY * aY * nY⁻¹ =
            (⟨⁅n, (aY : G)⁆, hmemY⟩ : ↥Y) * aY := by
          ext
          simpa [nY] using hconj
        have hqeq : q nY * q aY * (q nY)⁻¹ = q aY := by
          calc q nY * q aY * (q nY)⁻¹ = q (nY * aY * nY⁻¹) := by simp
            _ = q ((⟨⁅n, (aY : G)⁆, hmemY⟩ : ↥Y) * aY) := by rw [hsub]
            _ = q ⟨⁅n, (aY : G)⁆, hmemY⟩ * q aY := map_mul q _ _
            _ = 1 * q aY := by rw [hqcy]
            _ = q aY := one_mul _
        change q nY * q aY * (q nY)⁻¹ ∈ (AYl l).map q
        rw [hqeq]
        exact Subgroup.mem_map_of_mem q haY
    · exact le_of_eq (Subgroup.card_map_of_injective
        (K := (AYl l).map q)
        (f := (MulAut.conj (q nY)).toMonoidHom)
        (MulAut.conj (q nY)).injective).symm
  have hqn_norm : q nY ∈ Subgroup.normalizer ((AY.map q : Subgroup (↥Y ⧸ Nbar)) : Set _) := by
    rw [CFSG.LocalAnalysis.UniquenessCase.UC6S846.mem_normalizer_iff_map_conj]
    simp only [hAY_eq, Subgroup.map_sup, hAx_fix]
  have hnormalizer_map :=
    CFSG.normalizer_map_quotient_eq_map_normalizer 3 AY Nbar hNbar_normal hcop
  have hqn_mem : q nY ∈ (Subgroup.normalizer AY).map q := by
    rw [← hnormalizer_map]
    exact hqn_norm
  obtain ⟨lY, hlY_norm, hlY_eq⟩ := Subgroup.mem_map.mp hqn_mem
  let l : G := (lY : G)
  have hlL : l ∈ d.L := lY.2
  have hlNormAA : l ∈ Subgroup.normalizer (d.AA : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hxY : (⟨x, d.AA_le_L hx⟩ : ↥Y) ∈ AY := Subgroup.mem_subgroupOf.mpr hx
      have hmem := (Subgroup.mem_normalizer_iff.mp hlY_norm (⟨x, d.AA_le_L hx⟩ : ↥Y)).mp hxY
      simpa [l] using Subgroup.mem_subgroupOf.mp hmem
    · intro hx
      have hxY : (⟨l * x * l⁻¹, d.AA_le_L hx⟩ : ↥Y) ∈ AY :=
        Subgroup.mem_subgroupOf.mpr hx
      have hmem := (Subgroup.mem_normalizer_iff.mp
        (Subgroup.inv_mem (Subgroup.normalizer (AY : Set ↥Y)) hlY_norm)
        (⟨l * x * l⁻¹, d.AA_le_L hx⟩ : ↥Y)).mp hxY
      simpa [l, mul_assoc] using Subgroup.mem_subgroupOf.mp hmem
  have hdisj : Disjoint d.AA (CFSG.Open.pCoreOf 2 d.M) :=
    IsPGroup.disjoint_of_ne 3 2 (by norm_num) d.AA (CFSG.Open.pCoreOf 2 d.M)
      d.isElemAbelian_AA.isPGroup (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 d.M)
  have hq_inj : ∀ (x y : G) (hx : x ∈ d.AA) (hy : y ∈ d.AA),
      q ⟨x, d.AA_le_L hx⟩ = q ⟨y, d.AA_le_L hy⟩ → x = y := by
    intro x y hx hy hxy
    have hmemNbar : (⟨x, d.AA_le_L hx⟩ : ↥Y)⁻¹ * ⟨y, d.AA_le_L hy⟩ ∈ Nbar := by
      have hxy' : (↑(⟨x, d.AA_le_L hx⟩ : ↥Y) : ↥Y ⧸ Nbar) =
          ↑(⟨y, d.AA_le_L hy⟩ : ↥Y) := hxy
      exact (QuotientGroup.eq.mp hxy')
    have hmemN : x⁻¹ * y ∈ CFSG.Open.pCoreOf 2 d.M := by
      have h := Subgroup.mem_subgroupOf.mp hmemNbar
      simpa using h
    have hmemAA : x⁻¹ * y ∈ d.AA := d.AA.mul_mem (d.AA.inv_mem hx) hy
    have hbot : x⁻¹ * y ∈ (⊥ : Subgroup G) := by
      rw [← hdisj.eq_bot]
      exact Subgroup.mem_inf.mpr ⟨hmemAA, hmemN⟩
    have hz : x⁻¹ * y = 1 := Subgroup.mem_bot.mp hbot
    exact inv_mul_eq_one.mp hz
  refine ⟨l, hlL, hlNormAA, ?_⟩
  intro j a ha
  have haAA : a ∈ d.AA := SylowThreeData.A_le_AA d j ha
  have hleftAA : l * a * l⁻¹ ∈ d.AA := (hlNormAA a).mp haAA
  let aY : ↥Y := ⟨a, d.A_le_L j ha⟩
  have hleft_eq : (⟨l * a * l⁻¹, d.AA_le_L hleftAA⟩ : ↥Y) = lY * aY * lY⁻¹ := by
    ext
    simp [l, aY]
  by_cases hji : j = i
  · have ha_i : a ∈ d.A i := hji ▸ ha
    have hrightAA : a⁻¹ ∈ d.AA := d.AA.inv_mem haAA
    let ainvY : ↥Y := ⟨a⁻¹, d.A_le_L j ((d.A j).inv_mem ha)⟩
    have hq_eq : q ⟨l * a * l⁻¹, d.AA_le_L hleftAA⟩ = q ainvY := by
      have hconj : n * a * n⁻¹ = a⁻¹ := hnInv a ha_i
      have hsub : nY * aY * nY⁻¹ = ainvY := by
        ext
        simpa [nY, aY, ainvY] using hconj
      calc q ⟨l * a * l⁻¹, d.AA_le_L hleftAA⟩ = q (lY * aY * lY⁻¹) := by rw [hleft_eq]
        _ = q lY * q aY * (q lY)⁻¹ := by simp
        _ = q nY * q aY * (q nY)⁻¹ := by rw [hlY_eq]
        _ = q (nY * aY * nY⁻¹) := by simp
        _ = q ainvY := by rw [hsub]
    rw [if_pos hji]
    exact hq_inj _ _ hleftAA hrightAA hq_eq
  · have hij : i ≠ j := fun h => hji h.symm
    have hrightAA : a ∈ d.AA := haAA
    have hcommN : ⁅n, a⁆ ∈ CFSG.Open.pCoreOf 2 d.M :=
      d.hcomm i j hij (Subgroup.commutator_mem_commutator hnLf
        ((d.A_le_H j).trans (d.H_le_Lf j) ha))
    have hconj : n * a * n⁻¹ = ⁅n, a⁆ * a := by
      rw [commutatorElement_def]
      group
    have hnY : n ∈ Y := d.Lf_le_L i hnLf
    have haY' : a ∈ Y := d.A_le_L j ha
    have hmemY : ⁅n, a⁆ ∈ Y := by
      rw [commutatorElement_def]
      exact Y.mul_mem (Y.mul_mem (Y.mul_mem hnY haY') (Y.inv_mem hnY)) (Y.inv_mem haY')
    have hcy : (⟨⁅n, a⁆, hmemY⟩ : ↥Y) ∈ Nbar := Subgroup.mem_subgroupOf.mpr hcommN
    have hqcy : q ⟨⁅n, a⁆, hmemY⟩ = 1 := by
      change (QuotientGroup.mk' Nbar ⟨⁅n, a⁆, hmemY⟩ : ↥Y ⧸ Nbar) = 1
      rw [QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff _).mpr hcy
    have hsub : nY * aY * nY⁻¹ = (⟨⁅n, a⁆, hmemY⟩ : ↥Y) * aY := by
      ext
      simpa [nY, aY] using hconj
    have hq_eq : q ⟨l * a * l⁻¹, d.AA_le_L hleftAA⟩ = q aY := by
      calc q ⟨l * a * l⁻¹, d.AA_le_L hleftAA⟩ = q (lY * aY * lY⁻¹) := by rw [hleft_eq]
        _ = q lY * q aY * (q lY)⁻¹ := by simp
        _ = q nY * q aY * (q nY)⁻¹ := by rw [hlY_eq]
        _ = q (nY * aY * nY⁻¹) := by simp
        _ = q ((⟨⁅n, a⁆, hmemY⟩ : ↥Y) * aY) := by rw [hsub]
        _ = q ⟨⁅n, a⁆, hmemY⟩ * q aY := map_mul q _ _
        _ = 1 * q aY := by rw [hqcy]
        _ = q aY := one_mul _
    rw [if_neg hji]
    exact hq_inj _ _ hleftAA hrightAA hq_eq

end SylowThreeData

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
