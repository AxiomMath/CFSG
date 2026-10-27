module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoPlane
public import CFSG.LocalAnalysis.UniquenessCase.UC1K326S
import CFSG.GroupTheory.WreathThreeIso
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoCentralizerY
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoK326
import CFSG.GroupTheory.SolvableHallNodes
import CFSG.Timmesfeld.RankOne.Quotient
import CFSG.GroupTheory.SteinbergBSQuotientLifting
import CFSG.SignalizerFunctorTheorem.Inheritance.Diagonal
import CFSG.GroupTheory.ABGLocalTools.ZJFactorization
import CFSG.LocalAnalysis.UniquenessCase.UC1K327Core
import CFSG.LocalAnalysis.GLTheoremA.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Subgroup

namespace CaseTwoTransitive

variable {G : Type} [Group G] [Finite G] {c : Ctx812E G} (t : CaseTwoTransitive c)

private theorem Z_ne_bot : t.Z ≠ ⊥ := by
  intro hbot
  have hcard : Nat.card t.Z = 1 := by rw [hbot, Subgroup.card_bot]
  rw [t.card_Z] at hcard
  omega

theorem mem_Z_of_forall_commute {x : G} (hxP : x ∈ t.P) (hxc : ∀ g ∈ t.P, g * x = x * g)
    (hx3 : x ^ 3 = 1) : x ∈ t.Z := by
  have hP : CFSG.GroupTheory.WreathThree.base (t.d.H 0) t.y ⊔ Subgroup.zpowers t.y = t.P := by
    rw [t.base_eq, t.hPy]
  have hxcenter : x ∈ (CFSG.GroupTheory.WreathThree.base (t.d.H 0) t.y ⊔
      Subgroup.zpowers t.y : Subgroup G) ⊓ Subgroup.centralizer
      ((CFSG.GroupTheory.WreathThree.base (t.d.H 0) t.y ⊔
        Subgroup.zpowers t.y : Subgroup G) : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨hP ▸ hxP, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact hxc g (hP ▸ hg)
  rw [CFSG.GroupTheory.WreathThree.center_eq t.isWreathThree t.hy3] at hxcenter
  obtain ⟨hxS, hxy⟩ := Subgroup.mem_inf.mp hxcenter
  rw [t.base_eq] at hxS
  exact Subgroup.mem_inf.mpr ⟨t.d.mem_AA_of_pow_eq_one hxS hx3, hxy⟩

theorem centralizer_Z_ne_top : Subgroup.centralizer (t.Z : Set G) ≠ ⊤ := by
  intro htop
  have hcenter : t.Z ≤ Subgroup.center G := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.centralizer (t.Z : Set G) := by rw [htop]; trivial
    exact (Subgroup.mem_centralizer_iff.mp hg z hz).symm
  haveI : IsSimpleGroup G := c.standing.simple
  have hcentbot : Subgroup.center G = ⊥ :=
    CFSG.SignalizerFunctorTheorem.Diagonal.center_eq_bot (T := G) c.standing.nonab
  exact t.Z_ne_bot (le_bot_iff.mp (hcenter.trans (le_of_eq hcentbot)))

theorem exists_mulEquiv_zwr : ∃ n : ℕ, 1 ≤ n ∧ Nat.card (t.d.H 0) = 3 ^ n ∧
    Nonempty (↥t.P ≃* CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326.ZWr n) := by
  obtain ⟨n, hn, hcard, ⟨e⟩⟩ :=
    CFSG.GroupTheory.WreathThree.exists_mulEquiv_regularWreathProduct t.isWreathThree t.hy3
  refine ⟨n, hn, hcard, ⟨(MulEquiv.subgroupCongr ?_).trans e⟩⟩
  rw [t.base_eq, t.hPy]

theorem centralizer_Z_le_of_not_dvd {p : ℕ} (hp : p ∈ c.sig)
    (h76 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 c.S.M p)
    (hpL : ¬ p ∣ Nat.card c.L) : Subgroup.centralizer (t.Z : Set G) ≤ c.S.M :=
  (Subgroup.centralizer_le_normalizer (t.Z : Set G)).trans
    (normalizer_le_of_le_AA_of_not_dvd t hp h76 hpL t.Z_le_AA t.Z_ne_bot)

theorem centralizer_Z_le_of_map_eq_top {p : ℕ} (hN : t.PairNormalizerLe p)
    (hmap : ((Subgroup.centralizer (t.Z : Set G) ⊓ c.S.M).subgroupOf
        (Subgroup.centralizer (t.Z : Set G))).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Subgroup.centralizer (t.Z : Set G)))) = ⊤) :
    Subgroup.centralizer (t.Z : Set G) ≤ c.S.M := by
  let H : Subgroup G := Subgroup.centralizer (t.Z : Set G)
  let O : Subgroup ↥H := CFSG.pPrimeCore 3 ↥H
  let K : Subgroup ↥H := (H ⊓ c.S.M).subgroupOf H
  have hAAleH : t.d.AA ≤ H := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (congrArg Subtype.val (t.d.isElemAbelian_AA.1.is_comm.comm
      ⟨a, ha⟩ ⟨z, t.Z_le_AA hz⟩)).symm
  have hA : t.d.A 0 ⊔ t.d.A 1 ≤ H :=
    sup_le ((show t.d.A 0 ≤ t.d.AA from le_sup_left.trans le_sup_left).trans hAAleH)
      ((show t.d.A 1 ≤ t.d.AA from le_sup_right.trans le_sup_left).trans hAAleH)
  have hOle : O.map H.subtype ≤ c.S.M := pPrimeCore_le t hN hA
  have hNK : O ≤ K := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact ⟨x.2, hOle (Subgroup.mem_map_of_mem H.subtype hx)⟩
  have hKtop : K = ⊤ := by
    have h := congrArg (Subgroup.comap (QuotientGroup.mk' O))
      (show K.map (QuotientGroup.mk' O) = ⊤ by simpa [K, O, H] using hmap)
    rwa [Subgroup.comap_map_eq, Subgroup.comap_top, QuotientGroup.ker_mk',
      sup_eq_left.mpr hNK] at h
  intro x hxH
  have hxK : (⟨x, hxH⟩ : ↥H) ∈ K := by rw [hKtop]; trivial
  exact (Subgroup.mem_subgroupOf.mp hxK).2

private theorem S_le_P : t.d.S ≤ t.P := by
  rw [t.hdS]
  exact inf_le_left

private theorem AA_le_P : t.d.AA ≤ t.P := t.d.AA_le_S.trans t.S_le_P

private theorem AA_le_normalizer_P : t.P ≤ Subgroup.normalizer (t.d.AA : Set G) := by
  intro p hp
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine t.eq_AA_of_isElemAbelian ?_ ?_ ?_
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    exact t.P.mul_mem (t.P.mul_mem hp (t.AA_le_P ha)) (t.P.inv_mem hp)
  · exact t.d.isElemAbelian_AA.map (MulAut.conj p).toMonoidHom
  · rw [Subgroup.card_map_of_injective (MulAut.conj p).injective, t.d.card_AA]

private theorem normalizer_subgroupOf_map_le {K A : Subgroup G} (hAK : A ≤ K)
    (hN : Subgroup.normalizer (A : Set G) ≤ c.S.M) :
    (Subgroup.normalizer ((A.subgroupOf K) : Set ↥K)).map K.subtype ≤ c.S.M := by
  intro n hn
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hn
  apply hN
  have hAeq : (A.subgroupOf K).map K.subtype = A := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAK]
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hm ⊢
  have hcomp : K.subtype.comp (MulAut.conj m).toMonoidHom =
      (MulAut.conj (m : G)).toMonoidHom.comp K.subtype := by
    ext y
    simp [MulAut.conj_apply, mul_assoc]
  calc A.map (MulAut.conj (m : G)).toMonoidHom
      = ((A.subgroupOf K).map K.subtype).map
          (MulAut.conj (m : G)).toMonoidHom := by rw [hAeq]
    _ = (A.subgroupOf K).map ((MulAut.conj (m : G)).toMonoidHom.comp K.subtype) := by
          rw [Subgroup.map_map]
    _ = (A.subgroupOf K).map (K.subtype.comp (MulAut.conj m).toMonoidHom) := by rw [hcomp]
    _ = ((A.subgroupOf K).map (MulAut.conj m).toMonoidHom).map K.subtype := by
          rw [Subgroup.map_map]
    _ = (A.subgroupOf K).map K.subtype :=
          congrArg (fun S : Subgroup ↥K => S.map K.subtype) hm
    _ = A := hAeq

private theorem le_of_normalizer_map_eq_top {p : ℕ}
    (hN : t.PairNormalizerLe p)
    {H : Subgroup G} (hA : t.d.A 0 ⊔ t.d.A 1 ≤ H) {A_H : Subgroup ↥H}
    (hNle : (Subgroup.normalizer (A_H : Set ↥H)).map H.subtype ≤ c.S.M)
    (hNtop : (Subgroup.normalizer (A_H : Set ↥H)).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H)) = ⊤) :
    H ≤ c.S.M := by
  let O : Subgroup ↥H := CFSG.pPrimeCore 3 ↥H
  let π : ↥H →* (↥H ⧸ O) := QuotientGroup.mk' O
  have hOle : O.map H.subtype ≤ c.S.M := pPrimeCore_le t hN hA
  intro x hxH
  let xH : ↥H := ⟨x, hxH⟩
  have hx : π xH ∈ (Subgroup.normalizer (A_H : Set ↥H)).map π := by
    rw [hNtop]
    trivial
  obtain ⟨n, hnN, hnx⟩ := Subgroup.mem_map.mp hx
  have hmemO : n⁻¹ * xH ∈ O := by
    have h1 : π (n⁻¹ * xH) = 1 := by
      rw [map_mul, map_inv, hnx, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff (N := O) (n⁻¹ * xH)).1 h1
  have hx_eq : xH = n * (n⁻¹ * xH) := (mul_inv_cancel_left n xH).symm
  have hxG : x = (n : G) * ((n⁻¹ * xH : ↥H) : G) := by
    simpa [xH] using congrArg Subtype.val hx_eq
  rw [hxG]
  exact c.S.M.mul_mem (hNle (Subgroup.mem_map_of_mem H.subtype hnN))
    (hOle (Subgroup.mem_map_of_mem H.subtype hmemO))

private theorem nine_le_card_inf_AA (hP : Nat.card t.P = 81) {D : Subgroup G}
    (hDP : D ≤ t.P) (hD27 : Nat.card D = 27) :
    9 ≤ Nat.card ↥(t.d.AA ⊓ D) := by
  have hA : t.d.AA ≤ t.P := t.AA_le_P
  have hcomm : D ≤ Subgroup.normalizer (t.d.AA : Set G) :=
    hDP.trans (AA_le_normalizer_P t)
  have hprod := CFSG.LocalAnalysis.GLTheoremA.card_sup_mul_card_inf_of_le_normalizer
    (A := t.d.AA) (B := D) hcomm
  have hsup_le : Nat.card ↥(t.d.AA ⊔ D) ≤ 81 := by
    calc Nat.card ↥(t.d.AA ⊔ D) ≤ Nat.card t.P := Subgroup.card_le_of_le (sup_le hA hDP)
      _ = 81 := hP
  have hprod' : Nat.card ↥(t.d.AA ⊔ D) * Nat.card ↥(t.d.AA ⊓ D) = 27 * 27 := by
    rw [hprod, t.d.card_AA, hD27]
  by_contra h
  have hle8 : Nat.card ↥(t.d.AA ⊓ D) ≤ 8 := by omega
  have hterm : Nat.card ↥(t.d.AA ⊔ D) * Nat.card ↥(t.d.AA ⊓ D) ≤ 81 * 8 :=
    Nat.mul_le_mul hsup_le hle8
  omega

private abbrev CH (t : CaseTwoTransitive c) : Subgroup G := Subgroup.centralizer (t.Z : Set G)
private abbrev CO (t : CaseTwoTransitive c) : Subgroup ↥(CH t) := CFSG.pPrimeCore 3 ↥(CH t)
private instance CO_normal (t : CaseTwoTransitive c) : (CO t).Normal := CFSG.pPrimeCore_normal
private abbrev CX (t : CaseTwoTransitive c) : Type := ↥(CH t) ⧸ CO t
private abbrev Cpi (t : CaseTwoTransitive c) : ↥(CH t) →* CX t := QuotientGroup.mk' (CO t)
private abbrev CPX (t : CaseTwoTransitive c) : Subgroup (CX t) :=
  (t.P.subgroupOf (CH t)).map (Cpi t)
private abbrev CDhat (t : CaseTwoTransitive c) : Subgroup (CX t) := CFSG.pCore 3 (CX t)
private abbrev CfP (t : CaseTwoTransitive c) : ↥t.P →* CX t :=
  (Cpi t).comp (Subgroup.inclusion t.le_centralizer_Z)
private abbrev CD0P (t : CaseTwoTransitive c) : Subgroup ↥t.P := (CDhat t).comap (CfP t)
private abbrev CD0H (t : CaseTwoTransitive c) : Subgroup ↥(CH t) :=
  (CD0P t).map (Subgroup.inclusion t.le_centralizer_Z)
private abbrev CD0G (t : CaseTwoTransitive c) : Subgroup G := (CD0P t).map t.P.subtype
private abbrev CDpre (t : CaseTwoTransitive c) : Subgroup ↥(CH t) := (CDhat t).comap (Cpi t)
private noncomputable abbrev CB (t : CaseTwoTransitive c) : Subgroup G := t.d.AA ⊓ CD0G t
private noncomputable abbrev CBhat (t : CaseTwoTransitive c) : Subgroup (CX t) :=
  (CB t).subgroupOf (CH t) |>.map (Cpi t)


private theorem not_dvd_card_CO : ¬ 3 ∣ Nat.card (CO t) :=
  (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (CFSG.pPrimeCore_coprime_card)
private theorem pCore_le_PX_and_fP_injective {p : ℕ} (hp : p ∈ c.sig)
    (hN : t.PairNormalizerLe p) :
    Function.Injective ((Cpi t).comp (t.P.subgroupOf (CH t)).subtype) ∧
      CDhat t ≤ CPX t ∧ Function.Injective (CfP t) ∧ (CfP t).range = CPX t := by
  have hPH : t.P ≤ CH t := t.le_centralizer_Z
  have hPsylH : CFSG.ABGLocalTools.IsSylowOf 3 t.P (CH t) :=
    (t.isSylowOf_top hp hN).of_le hPH le_top
  have hPsylHtop : CFSG.ABGLocalTools.IsSylowOf 3 (t.P.subgroupOf (CH t)) ⊤ := by
    refine (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (K := CH t)).mp ?_
    simpa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPH,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype] using hPsylH
  have hPXsyl : CFSG.ABGLocalTools.IsSylowOf 3 (CPX t) ⊤ := by
    have h := CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC327.isSylowOf_map (Cpi t) hPsylHtop
    simpa [CPX, Subgroup.map_top_of_surjective (Cpi t)
      (QuotientGroup.mk'_surjective (CO t))] using h
  have hPXp : IsPGroup 3 (CPX t) := hPXsyl.isPGroup
  have hPXidx : ¬ 3 ∣ (CPX t).index := by
    simpa [Subgroup.relIndex_top_right] using
      (CFSG.ABGLocalTools.isSylowOf_iff.mp hPXsyl).2.2
  let S : Sylow 3 (CX t) := hPXp.toSylow hPXidx
  have hScoe : (S : Subgroup (CX t)) = CPX t := rfl
  have hDhat_p : IsPGroup 3 (CDhat t) := CFSG.pCore_isPGroup
  haveI : (CDhat t).Normal := CFSG.pCore_normal
  have hDhat_le : CDhat t ≤ CPX t := by
    have h := hDhat_p.le_sylow_of_normal S
    rwa [hScoe] at h
  have hinj : Function.Injective ((Cpi t).comp (t.P.subgroupOf (CH t)).subtype) :=
    CFSG.GroupTheory.SteinbergBS.injective_mk'_comp_subtype (p := 3) (N := CO t)
      (not_dvd_card_CO t) hPsylHtop.isPGroup
  have hfPrange : (CfP t).range = CPX t := by
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      exact Subgroup.mem_map_of_mem (Cpi t) (Subgroup.mem_subgroupOf.mpr q.2)
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      exact ⟨⟨y, hy⟩, rfl⟩
  refine ⟨hinj, hDhat_le, ?_, hfPrange⟩
  intro q r hqr
  have hqP : (⟨q, hPH q.2⟩ : ↥(CH t)) ∈ t.P.subgroupOf (CH t) :=
    Subgroup.mem_subgroupOf.mpr q.2
  have hrP : (⟨r, hPH r.2⟩ : ↥(CH t)) ∈ t.P.subgroupOf (CH t) :=
    Subgroup.mem_subgroupOf.mpr r.2
  have h := hinj (show ((Cpi t).comp (t.P.subgroupOf (CH t)).subtype)
      ⟨⟨q, hPH q.2⟩, hqP⟩ = ((Cpi t).comp (t.P.subgroupOf (CH t)).subtype)
      ⟨⟨r, hPH r.2⟩, hrP⟩ from hqr)
  exact Subtype.ext (congrArg (fun z : ↥(t.P.subgroupOf (CH t)) =>
    ((z : ↥(CH t)) : G)) h)

private theorem D0_setup {p : ℕ} (hp : p ∈ c.sig) (hN : t.PairNormalizerLe p)
    (hDhat : Nat.card (CDhat t) = 27) :
    Nat.card (CD0P t) = 27 ∧ Nat.card (CD0G t) = 27 ∧
      (CD0H t).map (CH t).subtype = CD0G t ∧ (CD0H t).map (Cpi t) = CDhat t ∧
      CD0H t ≤ t.P.subgroupOf (CH t) ∧
      CFSG.ABGLocalTools.IsSylowOf 3 (CD0H t) (CD0H t ⊔ CO t) ∧
      t.P ≤ Subgroup.normalizer (CD0G t) ∧
      (CD0G t).subgroupOf (CH t) = CD0H t := by
  obtain ⟨-, hDhat_le, hinjP, hfPrange⟩ := pCore_le_PX_and_fP_injective t hp hN
  have hD0P_map : (CD0P t).map (CfP t) = CDhat t :=
    Subgroup.map_comap_eq_self (by rw [hfPrange]; exact hDhat_le)
  have hD0P_card : Nat.card (CD0P t) = 27 := by
    have h := Subgroup.card_map_of_injective (K := CD0P t) hinjP
    rw [hD0P_map, hDhat] at h
    exact h.symm
  have hD0H_map : (CD0H t).map (CH t).subtype = CD0G t := by
    simp only [CD0H, CD0G, Subgroup.map_map]
    congr 1
  have hD0H_map_pi : (CD0H t).map (Cpi t) = CDhat t := by
    simp only [CD0H, Subgroup.map_map]
    exact hD0P_map
  have hD0G_card : Nat.card (CD0G t) = 27 := by
    simp only [CD0G]
    rw [Subgroup.card_map_of_injective t.P.subtype_injective, hD0P_card]
  have hPH3 : IsPGroup 3 (t.P.subgroupOf (CH t)) :=
    (t.isSylowOf_top hp hN).isPGroup.comap_subtype
  have hD0H_le_PH : CD0H t ≤ t.P.subgroupOf (CH t) := by
    rintro y ⟨q, -, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr q.2
  have hD0H_p : IsPGroup 3 (CD0H t) := hPH3.to_le hD0H_le_PH
  have hcop : Nat.Coprime 3 (Nat.card (CO t)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (not_dvd_card_CO t)
  have hD0H_sylow' : CFSG.ABGLocalTools.IsSylowOf 3 (CD0H t) (CD0H t ⊔ CO t) := by
    rw [sup_comm]
    exact CFSG.ABGLocalTools.isSylowOf_sup_of_coprime (p := 3) hcop hD0H_p
  haveI : (CD0P t).Normal := (CFSG.pCore_normal (p := 3) (G := CX t)).comap (CfP t)
  have hD0G_norm : t.P ≤ Subgroup.normalizer (CD0G t) := by
    have h := Subgroup.le_normalizer_map (H := CD0P t) t.P.subtype
    rw [Subgroup.normalizer_eq_top (CD0P t), ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h
    exact h
  have hD0G_sub : (CD0G t).subgroupOf (CH t) = CD0H t := by
    apply Subgroup.map_injective (CH t).subtype_injective
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr
      ((Subgroup.map_subtype_le (CD0P t)).trans t.le_centralizer_Z), hD0H_map]
  exact ⟨hD0P_card, hD0G_card, hD0H_map, hD0H_map_pi, hD0H_le_PH, hD0H_sylow',
    hD0G_norm, hD0G_sub⟩
private theorem CDpre_eq {p : ℕ} (hp : p ∈ c.sig) (hN : t.PairNormalizerLe p)
    (hDhat : Nat.card (CDhat t) = 27) :
    CDpre t = CD0H t ⊔ CO t := by
  obtain ⟨-, -, -, hD0H_map_pi, -⟩ := D0_setup t hp hN hDhat
  rw [CDpre, ← hD0H_map_pi, Subgroup.comap_map_eq, QuotientGroup.ker_mk']


private theorem A_sup_le_CH : t.d.A 0 ⊔ t.d.A 1 ≤ CH t :=
  sup_le ((show t.d.A 0 ≤ t.d.AA from le_sup_left.trans le_sup_left).trans
      (t.AA_le_P.trans t.le_centralizer_Z))
    ((show t.d.A 1 ≤ t.d.AA from le_sup_right.trans le_sup_left).trans
      (t.AA_le_P.trans t.le_centralizer_Z))

private theorem le_of_card_CB_eq_27 {p : ℕ} (hp : p ∈ c.sig) (hN : t.PairNormalizerLe p)
    (hDhat : Nat.card (CDhat t) = 27) (hB27 : Nat.card (CB t) = 27) :
    CH t ≤ c.S.M := by
  obtain ⟨-, hD0G, hD0H_map, hD0H_map_pi, -⟩ := D0_setup t hp hN hDhat
  have hB_eq_AA : CB t = t.d.AA := by
    refine Subgroup.eq_of_le_of_card_ge inf_le_left ?_
    rw [hB27, t.d.card_AA]
  have hAA_le_D0G : t.d.AA ≤ CD0G t := by
    have h : t.d.AA ≤ t.d.AA ⊓ CD0G t := by
      rw [← hB_eq_AA]
      exact le_inf le_rfl inf_le_right
    exact h.trans inf_le_right
  have hD0_eq_AA : CD0G t = t.d.AA := by
    refine (Subgroup.eq_of_le_of_card_ge hAA_le_D0G ?_).symm
    rw [hD0G, t.d.card_AA]
  have hD0H_eq : CD0H t = t.d.AA.subgroupOf (CH t) := by
    apply Subgroup.map_injective (CH t).subtype_injective
    rw [hD0H_map, hD0_eq_AA, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr (t.AA_le_P.trans t.le_centralizer_Z)]
  have hDhat_eq : CDhat t = (t.d.AA.subgroupOf (CH t)).map (Cpi t) := by
    rw [← hD0H_eq, hD0H_map_pi]
  haveI : ((t.d.AA.subgroupOf (CH t)).map (Cpi t)).Normal := by
    rw [← hDhat_eq]
    exact CFSG.pCore_normal
  have hAAH_p : IsPGroup 3 (t.d.AA.subgroupOf (CH t)) :=
    t.d.isElemAbelian_AA.isPGroup.comap_subtype
  have hnorm := CFSG.GroupTheory.normal_coprime_quotient_normalizer (p := 3) (CO t)
    (not_dvd_card_CO t) (t.d.AA.subgroupOf (CH t)) hAAH_p
  have hNtop : (Subgroup.normalizer ((t.d.AA.subgroupOf (CH t)) : Set ↥(CH t))).map
      (Cpi t) = ⊤ := by
    rw [hnorm]
    exact Subgroup.normalizer_eq_top _
  refine le_of_normalizer_map_eq_top t hN (A_sup_le_CH t) ?_ hNtop
  exact normalizer_subgroupOf_map_le (hAK := t.AA_le_P.trans t.le_centralizer_Z)
    (normalizer_AA_le t hp hN)
private theorem Z_le_CB {p : ℕ} (hp : p ∈ c.sig) (hN : t.PairNormalizerLe p)
    (hDhat : Nat.card (CDhat t) = 27) (hB9 : Nat.card (CB t) = 9) : t.Z ≤ CB t := by
  obtain ⟨-, -, -, -, -, -, hND0, -⟩ := D0_setup t hp hN hDhat
  have hB_le_P : CB t ≤ t.P := inf_le_right.trans (Subgroup.map_subtype_le (CD0P t))
  have hB_norm : t.P ≤ Subgroup.normalizer (CB t) :=
    (le_inf (AA_le_normalizer_P t) hND0).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := t.d.AA) (K := CD0G t))
  haveI hP3fact : Fact (IsPGroup 3 ↥t.P) := ⟨(t.isSylowOf_top hp hN).isPGroup⟩
  have hBtP_normal : ((CB t).subgroupOf t.P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hB_le_P).mpr hB_norm
  haveI : ((CB t).subgroupOf t.P).Normal := hBtP_normal
  have hBtP_card : Nat.card ↥((CB t).subgroupOf t.P) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB_le_P).toEquiv, hB9]
  haveI : Nontrivial ↥((CB t).subgroupOf t.P) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hBtP_card]; norm_num)
  obtain ⟨w, hwne, hwcenter⟩ :=
    CFSG.exists_nontrivial_center_mem_normal (N := (CB t).subgroupOf t.P) (p := 3)
  let wG : G := ((w : ↥t.P) : G)
  have hwP : wG ∈ t.P := (w : ↥t.P).2
  have hwc : ∀ g ∈ t.P, g * wG = wG * g := fun g hg =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hwcenter ⟨g, hg⟩)
  have hwAA : wG ∈ t.d.AA :=
    (inf_le_left : CB t ≤ t.d.AA) (Subgroup.mem_subgroupOf.mp w.2)
  have hw3 : wG ^ 3 = 1 := t.d.isElemAbelian_AA.2 wG hwAA
  have hwZ : wG ∈ t.Z := t.mem_Z_of_forall_commute hwP hwc hw3
  have hwneG : wG ≠ 1 := by
    intro h
    apply hwne
    exact Subtype.ext (by simpa [wG] using h)
  have hzp : t.Z = Subgroup.zpowers wG := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hwZ) ?_).symm
    rw [Nat.card_zpowers, orderOf_eq_prime hw3 hwneG, t.card_Z]
  rw [hzp]
  exact Subgroup.zpowers_le.mpr (Subgroup.mem_subgroupOf.mp w.2)

private theorem exists_conj_CBhat_le {p : ℕ} (hp : p ∈ c.sig) (hN : t.PairNormalizerLe p)
    (hDhat : Nat.card (CDhat t) = 27) (hB9 : Nat.card (CB t) = 9)
    (hBhat_not_normal : ¬ (CBhat t).Normal) :
    ∃ h : ↥(CH t), (CBhat t).map (MulAut.conj (Cpi t h)).toMonoidHom ≤ CDhat t ∧
      (CBhat t).map (MulAut.conj (Cpi t h)).toMonoidHom ≠ CBhat t := by
  haveI : (CDhat t).Normal := CFSG.pCore_normal
  obtain ⟨-, -, -, hD0H_map_pi, -, -, -, hD0G_sub⟩ := D0_setup t hp hN hDhat
  have hBhat_le_Dhat : CBhat t ≤ CDhat t := by
    rw [← hD0H_map_pi, ← hD0G_sub]
    refine Subgroup.map_mono ?_
    intro y hy
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    exact (inf_le_right : CB t ≤ CD0G t) hy
  have hDhat_fix : ∀ z : CX t,
      (CDhat t).map (MulAut.conj z).toMonoidHom = CDhat t := by
    intro z
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (by rw [Subgroup.normalizer_eq_top]; trivial)
  have hex : ∃ xhat : CX t, (CBhat t).map (MulAut.conj xhat).toMonoidHom ≠ CBhat t := by
    by_contra h
    apply hBhat_not_normal
    refine Subgroup.Normal.mk ?_
    intro n hn g
    have hg : g ∈ Subgroup.normalizer (CBhat t : Set (CX t)) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr (by
        by_contra hne
        exact h ⟨g, hne⟩)
    exact (Subgroup.mem_normalizer_iff.mp hg n).mp hn
  obtain ⟨xhat, hxhat⟩ := hex
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (CO t) xhat
  refine ⟨h, ?_, hxhat⟩
  calc (CBhat t).map (MulAut.conj (Cpi t h)).toMonoidHom
      ≤ (CDhat t).map (MulAut.conj (Cpi t h)).toMonoidHom := Subgroup.map_mono hBhat_le_Dhat
    _ = CDhat t := hDhat_fix _

private theorem exists_conj_CB_le_D0G {p : ℕ} (hp : p ∈ c.sig) (hN : t.PairNormalizerLe p)
    (hDhat : Nat.card (CDhat t) = 27) {h : ↥(CH t)}
    (hBh_le : (CBhat t).map (MulAut.conj (Cpi t h)).toMonoidHom ≤ CDhat t) :
    ∃ k : ↥(CH t), Cpi t k ∈ CDhat t ∧
      (CB t).map (MulAut.conj (((k⁻¹ * h : ↥(CH t)) : G))).toMonoidHom ≤ CD0G t := by
  obtain ⟨-, -, hD0H_map, hD0H_map_pi, -, hD0H_sylow', -, -⟩ := D0_setup t hp hN hDhat
  have hB_le_P : CB t ≤ t.P := inf_le_right.trans (Subgroup.map_subtype_le (CD0P t))
  have hB_le_H : CB t ≤ CH t := hB_le_P.trans t.le_centralizer_Z
  have hBH_p : IsPGroup 3 ((CB t).subgroupOf (CH t)) :=
    (t.d.isElemAbelian_AA.isPGroup.to_le (inf_le_left : CB t ≤ t.d.AA)).comap_subtype
  have hBh_le_Dpre : ((CB t).subgroupOf (CH t)).map (MulAut.conj h).toMonoidHom ≤ CDpre t := by
    rw [← Subgroup.map_le_iff_le_comap,
      CFSG.Timmesfeld.RankOne.map_map_conj (Cpi t) ((CB t).subgroupOf (CH t)) h]
    exact hBh_le
  let BhH : Subgroup ↥(CH t) := ((CB t).subgroupOf (CH t)).map (MulAut.conj h).toMonoidHom
  have hBhH_le : BhH ≤ CD0H t ⊔ CO t := by
    rw [← CDpre_eq t hp hN hDhat]
    exact hBh_le_Dpre
  let Psub : Subgroup ↥(CD0H t ⊔ CO t) := BhH.subgroupOf (CD0H t ⊔ CO t)
  have hPsub_p : IsPGroup 3 Psub := (hBH_p.map _).comap_subtype
  obtain ⟨S1, hS1⟩ := hPsub_p.exists_le_sylow
  let R : Subgroup ↥(CH t) := (S1 : Subgroup ↥(CD0H t ⊔ CO t)).map (CD0H t ⊔ CO t).subtype
  have hRsyl : CFSG.ABGLocalTools.IsSylowOf 3 R (CD0H t ⊔ CO t) := ⟨S1, rfl⟩
  have hBhH_le_R : BhH ≤ R := by
    intro y hy
    have hyS : (⟨y, hBhH_le hy⟩ : ↥(CD0H t ⊔ CO t)) ∈
        (S1 : Subgroup ↥(CD0H t ⊔ CO t)) := hS1 (Subgroup.mem_subgroupOf.mpr hy)
    exact Subgroup.mem_map_of_mem (CD0H t ⊔ CO t).subtype hyS
  obtain ⟨k, hkK, hkconj⟩ := hD0H_sylow'.exists_mem_conj hRsyl
  have hkD0H : BhH.map (MulAut.conj k⁻¹).toMonoidHom ≤ CD0H t := by
    intro y hy
    obtain ⟨y0, hy0, rfl⟩ := Subgroup.mem_map.mp hy
    simpa [MulAut.conj_apply] using (hkconj y0).mp (hBhH_le_R hy0)
  have hkBh : ((CB t).subgroupOf (CH t)).map (MulAut.conj (k⁻¹ * h)).toMonoidHom ≤
      CD0H t := by
    rw [CFSG.SolvableHall.map_conj_mul ((CB t).subgroupOf (CH t)) k⁻¹ h]
    exact hkD0H
  have hBh_kG : (CB t).map (MulAut.conj (((k⁻¹ * h : ↥(CH t)) : G))).toMonoidHom ≤
      CD0G t := by
    have hcomp : (CH t).subtype.comp (MulAut.conj (k⁻¹ * h)).toMonoidHom =
        (MulAut.conj (((k⁻¹ * h : ↥(CH t)) : G))).toMonoidHom.comp (CH t).subtype := by
      ext y
      simp [MulAut.conj_apply, mul_assoc]
    have hBeq : ((CB t).subgroupOf (CH t)).map (CH t).subtype = CB t := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hB_le_H]
    have h1 := Subgroup.map_mono (f := (CH t).subtype) hkBh
    rwa [Subgroup.map_map, hcomp, ← Subgroup.map_map, hBeq, hD0H_map] at h1
  have hpi_k : Cpi t k ∈ CDhat t := by
    simpa [Subgroup.map_sup, hD0H_map_pi, QuotientGroup.map_mk'_self, sup_bot_eq]
      using Subgroup.mem_map_of_mem (Cpi t) hkK
  exact ⟨k, hpi_k, hBh_kG⟩
private theorem map_conj_CBhat_eq {p : ℕ} (hp : p ∈ c.sig) (hN : t.PairNormalizerLe p)
    (hDhat : Nat.card (CDhat t) = 27) (hB9 : Nat.card (CB t) = 9)
    {h k : ↥(CH t)} (hk : Cpi t k ∈ CDhat t)
    (hBh_le : (CBhat t).map (MulAut.conj (Cpi t h)).toMonoidHom ≤ CDhat t) :
    (CBhat t).map (MulAut.conj (Cpi t (k⁻¹ * h))).toMonoidHom =
      (CBhat t).map (MulAut.conj (Cpi t h)).toMonoidHom := by
  haveI : (CDhat t).Normal := CFSG.pCore_normal
  have hBhat_h_normalD : (((CBhat t).map (MulAut.conj (Cpi t h)).toMonoidHom).subgroupOf
      (CDhat t)).Normal := by
    have hcard : Nat.card ↥(((CBhat t).map (MulAut.conj (Cpi t h)).toMonoidHom).subgroupOf
        (CDhat t)) = 9 := by
      have hB_le_P : CB t ≤ t.P := inf_le_right.trans (Subgroup.map_subtype_le (CD0P t))
      have hB_le_H : CB t ≤ CH t := hB_le_P.trans t.le_centralizer_Z
      have hBH_card : Nat.card ↥((CB t).subgroupOf (CH t)) = 9 := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB_le_H).toEquiv, hB9]
      have hinjBH : Function.Injective ((Cpi t).comp ((CB t).subgroupOf (CH t)).subtype) := by
        intro x y hxy
        have hxP : ((x : ↥(CH t))) ∈ t.P.subgroupOf (CH t) := by
          rw [Subgroup.mem_subgroupOf]
          exact hB_le_P (Subgroup.mem_subgroupOf.mp x.2)
        have hyP : ((y : ↥(CH t))) ∈ t.P.subgroupOf (CH t) := by
          rw [Subgroup.mem_subgroupOf]
          exact hB_le_P (Subgroup.mem_subgroupOf.mp y.2)
        have h := (pCore_le_PX_and_fP_injective t hp hN).1
          (show ((Cpi t).comp (t.P.subgroupOf (CH t)).subtype)
            ⟨(x : ↥(CH t)), hxP⟩ = ((Cpi t).comp (t.P.subgroupOf (CH t)).subtype)
            ⟨(y : ↥(CH t)), hyP⟩ from hxy)
        exact Subtype.ext (Subgroup.subtype_injective (CH t)
          (congrArg (fun z : ↥(t.P.subgroupOf (CH t)) => ((z : ↥(CH t)) : G)) h))
      have hrange : ((Cpi t).comp ((CB t).subgroupOf (CH t)).subtype).range = CBhat t := by
        simp only [CBhat]
        rw [MonoidHom.range_comp, Subgroup.range_subtype]
      have hcardCBhat : Nat.card (CBhat t) = 9 := by
        rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinjBH).toEquiv, hBH_card]
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
          (H := (CBhat t).map (MulAut.conj (Cpi t h)).toMonoidHom) (K := CDhat t) hBh_le).toEquiv,
        Subgroup.card_map_of_injective (MulAut.conj (Cpi t h)).injective,
        hcardCBhat]
    have hmin : (Nat.card ↥(CDhat t)).minFac = 3 := by rw [hDhat]; norm_num
    refine Subgroup.normal_of_index_eq_minFac_card ?_
    have hmul := Subgroup.card_mul_index
      (((CBhat t).map (MulAut.conj (Cpi t h)).toMonoidHom).subgroupOf (CDhat t))
    rw [hcard, hDhat] at hmul
    have hidx : (((CBhat t).map (MulAut.conj (Cpi t h)).toMonoidHom).subgroupOf
        (CDhat t)).index = 3 := by omega
    rw [hidx, hmin]
  have hDhat_le_normBh : CDhat t ≤ Subgroup.normalizer
      ((CBhat t).map (MulAut.conj (Cpi t h)).toMonoidHom : Set (CX t)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBh_le).mp hBhat_h_normalD
  have hzip : Cpi t (k⁻¹ * h) = (Cpi t k)⁻¹ * Cpi t h := by
    simp only [map_mul, map_inv]
  rw [hzip, CFSG.SolvableHall.map_conj_mul (CBhat t) (Cpi t k)⁻¹ (Cpi t h)]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (hDhat_le_normBh ((CDhat t).inv_mem hk))

private theorem exists_conj_CB_le_CD0G_ne {p : ℕ} (hp : p ∈ c.sig) (hN : t.PairNormalizerLe p)
    (hDhat : Nat.card (CDhat t) = 27) (hB9 : Nat.card (CB t) = 9)
    (hBhat_not_normal : ¬ (CBhat t).Normal) :
    ∃ z : ↥(CH t), (CB t).map (MulAut.conj (z : G)).toMonoidHom ≤ CD0G t ∧
      (CB t).map (MulAut.conj (z : G)).toMonoidHom ≠ CB t := by
  obtain ⟨h, hBh_le, hBh_ne⟩ := exists_conj_CBhat_le t hp hN hDhat hB9 hBhat_not_normal
  obtain ⟨k, hk, hk_le⟩ := exists_conj_CB_le_D0G t hp hN hDhat hBh_le
  let z : ↥(CH t) := k⁻¹ * h
  have hzBhat : (CBhat t).map (MulAut.conj (Cpi t z)).toMonoidHom =
      (CBhat t).map (MulAut.conj (Cpi t h)).toMonoidHom :=
    map_conj_CBhat_eq t hp hN hDhat hB9 hk hBh_le
  refine ⟨z, hk_le, ?_⟩
  have hB_le_H : CB t ≤ CH t :=
    (inf_le_right.trans (Subgroup.map_subtype_le (CD0P t))).trans t.le_centralizer_Z
  have hBH_ne : ((CB t).subgroupOf (CH t)).map (MulAut.conj z).toMonoidHom ≠
      (CB t).subgroupOf (CH t) := by
    intro heq
    have hmap := congrArg (fun S : Subgroup ↥(CH t) => S.map (Cpi t)) heq
    have hleft : (((CB t).subgroupOf (CH t)).map (MulAut.conj z).toMonoidHom).map (Cpi t) =
        (CBhat t).map (MulAut.conj (Cpi t z)).toMonoidHom :=
      CFSG.Timmesfeld.RankOne.map_map_conj (Cpi t) ((CB t).subgroupOf (CH t)) z
    rw [hleft, hzBhat] at hmap
    exact hBh_ne hmap
  intro heq
  apply hBH_ne
  apply Subgroup.map_injective (CH t).subtype_injective
  have hcomp : (CH t).subtype.comp (MulAut.conj z).toMonoidHom =
      (MulAut.conj (z : G)).toMonoidHom.comp (CH t).subtype := by
    ext y
    simp [MulAut.conj_apply, mul_assoc]
  have hBeq : ((CB t).subgroupOf (CH t)).map (CH t).subtype = CB t := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hB_le_H]
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hBeq, heq, hBeq.symm]
private theorem le_of_card_CB_eq_9 {p : ℕ} (hp : p ∈ c.sig) (hN : t.PairNormalizerLe p)
    (hpL : p ∣ Nat.card c.L) (hDhat : Nat.card (CDhat t) = 27)
    (hB9 : Nat.card (CB t) = 9) : CH t ≤ c.S.M := by
  obtain ⟨-, -, -, -, -, -, hND0, -⟩ := D0_setup t hp hN hDhat
  have hB_le_AA : CB t ≤ t.d.AA := inf_le_left
  have hB_le_P : CB t ≤ t.P := inf_le_right.trans (Subgroup.map_subtype_le (CD0P t))
  have hB_le_H : CB t ≤ CH t := hB_le_P.trans t.le_centralizer_Z
  have hB_norm : t.P ≤ Subgroup.normalizer (CB t) :=
    (le_inf (AA_le_normalizer_P t) hND0).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := t.d.AA) (K := CD0G t))
  have hZleB : t.Z ≤ CB t := Z_le_CB t hp hN hDhat hB9
  have hyB : t.y ∈ Subgroup.normalizer (CB t) := hB_norm t.hyP
  by_cases hBhat_normal : (CBhat t).Normal
  · haveI : (CBhat t).Normal := hBhat_normal
    have hBH_p : IsPGroup 3 ((CB t).subgroupOf (CH t)) :=
      (t.d.isElemAbelian_AA.isPGroup.to_le hB_le_AA).comap_subtype
    have hnorm := CFSG.GroupTheory.normal_coprime_quotient_normalizer (p := 3) (CO t)
      (not_dvd_card_CO t) ((CB t).subgroupOf (CH t)) hBH_p
    have hNtop : (Subgroup.normalizer (((CB t).subgroupOf (CH t)) : Set ↥(CH t))).map
        (Cpi t) = ⊤ := by
      rw [hnorm]
      exact Subgroup.normalizer_eq_top _
    refine le_of_normalizer_map_eq_top t hN (A_sup_le_CH t) ?_ hNtop
    exact normalizer_subgroupOf_map_le (hAK := hB_le_H)
      (normalizer_plane_le t hp hN hB_le_AA hB9 hZleB hyB)
  · obtain ⟨z, hz_le, hz_ne⟩ :=
      exists_conj_CB_le_CD0G_ne t hp hN hDhat hB9 hBhat_normal
    exact False.elim (false_of_conj_plane t hp hN hpL hB_le_AA hB9 hZleB
      (Subgroup.map_subtype_le (CD0P t)) (show t.d.AA ⊓ CD0G t = CB t from rfl)
      z.2 hz_le hz_ne)




theorem centralizer_Z_le_of_card_pCore {p : ℕ} (hp : p ∈ c.sig) (hN : t.PairNormalizerLe p)
    (hpL : p ∣ Nat.card c.L) (hP : Nat.card t.P = 81)
    (hO : Nat.card (CFSG.pCore 3 (↥(Subgroup.centralizer (t.Z : Set G)) ⧸
      CFSG.pPrimeCore 3 ↥(Subgroup.centralizer (t.Z : Set G)))) = 27) :
    Subgroup.centralizer (t.Z : Set G) ≤ c.S.M := by
  have hDhat : Nat.card (CDhat t) = 27 := by
    simpa [CDhat, CX, CO, CH] using hO
  have hD0G : Nat.card (CD0G t) = 27 := (D0_setup t hp hN hDhat).2.1
  have hcases : Nat.card (CB t) = 9 ∨ Nat.card (CB t) = 27 := by
    have hB_p : IsPGroup 3 ↥(CB t) :=
      t.d.isElemAbelian_AA.isPGroup.to_le (inf_le_left : CB t ≤ t.d.AA)
    have hB_ge : 9 ≤ Nat.card (CB t) :=
      nine_le_card_inf_AA t hP (Subgroup.map_subtype_le (CD0P t)) hD0G
    have hB_le : Nat.card (CB t) ≤ 27 := by
      calc Nat.card (CB t) ≤ Nat.card t.d.AA := Subgroup.card_le_of_le (inf_le_left : _ ≤ _)
        _ = 27 := t.d.card_AA
    obtain ⟨k, hk⟩ := hB_p.exists_card_eq
    have hk_ge : 2 ≤ k := by
      by_contra h
      have h1 : k ≤ 1 := by omega
      have h9 : 9 ≤ 3 ^ k := by simpa only [← hk] using hB_ge
      have h3 : 3 ^ k ≤ 3 := by simpa using Nat.pow_le_pow_right (by norm_num) h1
      omega
    have hk_le : k ≤ 3 := by
      by_contra h
      have h4 : 4 ≤ k := by omega
      have hpow : 3 ^ 4 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) h4
      norm_num at hpow
      have h81 : 81 ≤ Nat.card (CB t) := by simpa only [← hk] using hpow
      omega
    interval_cases k
    · left; simpa using hk
    · right; simpa using hk
  rcases hcases with h9 | h27
  · exact le_of_card_CB_eq_9 t hp hN hpL hDhat h9
  · exact le_of_card_CB_eq_27 t hp hN hDhat h27

theorem centralizer_Z_le_of_pairNormalizerLe
    (hK : CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326.K326P2S)
    {p : ℕ} (hp : p ∈ c.sig)
    (h76 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 c.S.M p)
    (hN : t.PairNormalizerLe p) :
    Subgroup.centralizer (t.Z : Set G) ≤ c.S.M := by
  by_cases hpL : p ∣ Nat.card c.L
  swap
  · exact t.centralizer_Z_le_of_not_dvd hp h76 hpL
  obtain ⟨n, hn, -, ⟨e⟩⟩ := t.exists_mulEquiv_zwr
  have hcent : ∀ x ∈ t.P, (∀ g ∈ t.P, g * x = x * g) → x ^ 3 = 1 →
      Subgroup.centralizer (t.Z : Set G) ≤ Subgroup.centralizer ({x} : Set G) :=
    fun x hxP hxc hx3 => Subgroup.centralizer_le
      (Set.singleton_subset_iff.mpr (t.mem_Z_of_forall_commute hxP hxc hx3))
  obtain ⟨hKX, hcore, hsyl, he, hom, a, ha, ha', hle⟩ :=
    t.k326_hypotheses hp hN t.centralizer_Z_ne_top t.le_centralizer_Z hcent hn e
  rcases hK _ hKX hcore n hn _ hsyl he hom _ a ha ha' hle with htop | ⟨rfl, hO, -, -⟩
  · exact t.centralizer_Z_le_of_map_eq_top hN htop
  · have hP : Nat.card t.P = 81 := by
      rw [Nat.card_congr e.toEquiv, RegularWreathProduct.card]
      simp [Nat.card_eq_fintype_card, ZMod.card]
    exact t.centralizer_Z_le_of_card_pCore hp hN hpL hP hO

section Full

variable {G : Type} [Group G] [Finite G] {c : Ctx812 G} (t : CaseTwoTransitive c.toCtx812E)

theorem centralizer_Z_le (hK : CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326.K326P2S)
    {p : ℕ} (hp : p ∈ c.sig)
    (h76 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 c.S.M p) :
    Subgroup.centralizer (t.Z : Set G) ≤ c.S.M :=
  t.centralizer_Z_le_of_pairNormalizerLe hK hp h76 (t.pairNormalizerLe hp h76)

end Full

end CaseTwoTransitive

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
