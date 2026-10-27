module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3CtxDefs
import CFSG.RankThree.PartTwo.Sec4.StepsBender
import CFSG.RankThree.PartTwo.Sec13.Item134HoldsTools
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec15.Item152ResProofW
import CFSG.RankThree.PartTwo.Sec15.Sylow155CDR4
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3Defs

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3

open CFSG CFSG.RankThree.PartTwo.Sec13

variable {G : Type} [Group G] [Finite G]

private theorem not_dvd_card_core (d : G) :
    ¬ 3 ∣ Nat.card (CFSG.pPrimeCore 3 ↥(res3C d)) :=
  (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 CFSG.pPrimeCore_coprime_card

omit [Finite G] in
private theorem map_conj_map_conj (F : Subgroup G) (x y : G) :
    (F.map (MulAut.conj x).toMonoidHom).map (MulAut.conj y).toMonoidHom =
      F.map (MulAut.conj (y * x)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext z
  simp [MulAut.conj_apply, mul_assoc]

theorem res3QAmb_oThreePrime (d : G) :
    ∀ N : Subgroup (Res3Bar d), N.Normal → ¬ 3 ∣ Nat.card N → N = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro N hN hN3
  exact (CFSG.pPrimeCore_eq_bot_iff.mp
    (CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := ↥(res3C d)) 3)) N hN
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN3)

namespace Res3Ctx

variable {A : Subgroup G} {c : G} {L : Subgroup G} {d : G} {K : Subgroup G}

theorem res3Proj_injOn (h : Res3Ctx A c L d K) {x y : ↥(res3C d)} (hx : (x : G) ∈ A)
    (hy : (y : G) ∈ A) (hxy : res3Proj d x = res3Proj d y) : x = y := by
  have hker : x⁻¹ * y ∈ CFSG.pPrimeCore 3 ↥(res3C d) := QuotientGroup.eq.mp hxy
  have h3 : (x⁻¹ * y) ^ 3 = 1 := Subtype.ext (by
    simpa using h.R.toSec13Data.isElemAbelian.2 ((x : G)⁻¹ * y) (A.mul_mem (A.inv_mem hx) hy))
  have h1 := Sec4.eq_one_of_pow_prime_pow_eq_one Nat.prime_three (not_dvd_card_core d) hker
    (a := 1) (by rwa [pow_one])
  exact inv_mul_eq_one.mp h1

theorem res3QAmb_A_max (h : Res3Ctx A c L d K) :
    ∀ x ∈ Subgroup.centralizer (res3Img d A : Set (Res3Bar d)), x ^ 3 = 1 →
      x ∈ res3Img d A := by
  intro x hx hx3
  have hA3 := h.R.toSec13Data.isElemAbelian.2
  have hApg : IsPGroup 3 (A.subgroupOf (res3C d)) := fun g =>
    ⟨1, Subtype.ext (Subtype.ext (by simpa using hA3 ((g : ↥(res3C d)) : G) g.2))⟩
  obtain ⟨y, hyC, hy3, rfl⟩ :=
    Sec4.exists_lift_pow_three_eq_one (not_dvd_card_core d) hApg hx hx3
  have hcomm : ∀ a ∈ A, a * (y : G) = (y : G) * a := fun a ha =>
    congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hyC ⟨a, h.le_C ha⟩ ha)
  have hy3' : (y : G) ^ 3 = 1 := by simpa using congrArg Subtype.val hy3
  have hsup := isElemAbelian_sup_zpowers h.R.toSec13Data.isElemAbelian hy3' hcomm
  have heq := h.R.toSec13Data.eq_of_le hsup le_sup_left
  have hyA : (y : G) ∈ A := by
    have hmem : (y : G) ∈ A ⊔ Subgroup.zpowers (y : G) :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    rwa [heq] at hmem
  exact Subgroup.mem_map.mpr ⟨y, hyA, rfl⟩

theorem res3QAmb_R4 (h : Res3Ctx A c L d K) :
    ∀ E T : Subgroup (Res3Bar d), CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 81 →
      IsPGroup 2 T → T ≠ ⊥ → E ≤ Subgroup.normalizer (T : Set (Res3Bar d)) → False :=
  fun _ _ hE hE81 hT hT1 hET =>
    Sylow155CD.false_of_elemAbelian_quot h.R.toSec14Std (C := res3C d)
      (N := CFSG.pPrimeCore 3 ↥(res3C d)) (not_dvd_card_core d) hE hE81 hT hT1 hET

theorem res3QAmb_wsym (h : Res3Ctx A c L d K) :
    ∀ e ∈ Subgroup.zpowers (res3Pt d c h.c_mem_C) ⊔ Subgroup.zpowers (res3Pt d d h.d_mem_C),
      e ∉ Subgroup.zpowers (res3Pt d d h.d_mem_C) →
        ∃ w : MulAut (Res3Bar d), (∀ a ∈ res3Img d A, w a ∈ res3Img d A) ∧
          w e ∉ Subgroup.zpowers e := by
  intro e he hed
  have hD := h.R.toSec13Data
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hD.mem_partTwoE
  have hcA : c ∈ A := h.c_mem
  have hc1 : c ≠ 1 := hD.ne_one
  have hdA : d ∈ A := h.d_mem
  have hd1 : d ≠ 1 := h.d_ne
  have hd3 : d ^ 3 = 1 := hD.isElemAbelian.2 d hdA
  have hcd : c ∉ Subgroup.zpowers d := fun hh =>
    h.c_notMem (Subgroup.zpowers_le.mpr h.d_L hh)
  have hdc : d ∉ Subgroup.zpowers c := Proof152ResW.not_mem_zpowers_symm hA hd1 hcA hcd
  set E : Subgroup G := Subgroup.zpowers c ⊔ Subgroup.zpowers d
  have hEA : E ≤ A := sup_le (Subgroup.zpowers_le.mpr hcA) (Subgroup.zpowers_le.mpr hdA)
  have hlift : e ∈ (E.subgroupOf (res3C d)).map (res3Proj d) := by
    refine (sup_le ?_ ?_ : Subgroup.zpowers (res3Pt d c h.c_mem_C) ⊔
      Subgroup.zpowers (res3Pt d d h.d_mem_C) ≤ (E.subgroupOf (res3C d)).map (res3Proj d)) he
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_map_of_mem _
        (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left (Subgroup.mem_zpowers c)))
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_map_of_mem _
        (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right (Subgroup.mem_zpowers d)))
  obtain ⟨y, hyE, rfl⟩ := Subgroup.mem_map.mp hlift
  have hyE' : (y : G) ∈ E := Subgroup.mem_subgroupOf.mp hyE
  have hyA : (y : G) ∈ A := hEA hyE'
  have hyd : (y : G) ∉ Subgroup.zpowers d := by
    intro hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine hed (Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩)
    have h1 : res3Proj d ((⟨d, h.d_mem_C⟩ : ↥(res3C d)) ^ k) = res3Proj d y :=
      congrArg (res3Proj d) (Subtype.ext (by simpa using hk))
    rwa [map_zpow] at h1
  have hy1 : (y : G) ≠ 1 := fun h1 => hyd (h1 ▸ Subgroup.one_mem _)
  have hy3 : (y : G) ^ 3 = 1 := hD.isElemAbelian.2 _ hyA
  obtain ⟨b, hb, hFb⟩ := Proof152ResW.exists_eq_zpowers_mul hA hcA hdA hd1 hcd
    (F := Subgroup.zpowers (y : G)) (Subgroup.zpowers_le.mpr hyE')
    (Sec13.card_zpowers_of_pow_three hy3 hy1)
    (fun hh => hyd (hh ▸ Subgroup.mem_zpowers _))
  have hΩ := Proof152ResW.omegaA_facts_of_case2 hA hcA hc1 hdA hd1 hdc h.NA h.Pstar_elem
    h.Pstar_card (Or.inl ⟨h.omega, h.ncard⟩)
  have hFΩ : Subgroup.zpowers (y : G) ∈ omegaA A := hFb ▸ hΩ.2 b hb
  obtain ⟨w, hwP, hwF⟩ : ∃ w ∈ oThreeWPre A,
      (Subgroup.zpowers (y : G)).map (MulAut.conj w).toMonoidHom ≠ Subgroup.zpowers (y : G) := by
    by_contra hno
    push Not at hno
    obtain ⟨p, hpP, hpF⟩ : Subgroup.zpowers (y : G) ∈
        orbitIn (oThreeWPre A) (Subgroup.zpowers c) := h.omega ▸ hFΩ
    have horb : orbitIn (oThreeWPre A) (Subgroup.zpowers c) ⊆ {Subgroup.zpowers (y : G)} := by
      rintro _ ⟨w, hw, rfl⟩
      rw [Set.mem_singleton_iff]
      have h1 : (Subgroup.zpowers (y : G)).map (MulAut.conj (w * p⁻¹)).toMonoidHom =
          (Subgroup.zpowers c).map (MulAut.conj w).toMonoidHom := by
        conv_lhs => rw [hpF]
        rw [map_conj_map_conj, inv_mul_cancel_right]
      exact h1.symm.trans (hno _ (mul_mem hw (inv_mem hpP)))
    have h3 : (orbitIn (oThreeWPre A) (Subgroup.zpowers c)).ncard = 3 := h.omega ▸ h.ncard
    have h4 := Set.ncard_le_ncard horb (Set.toFinite _)
    rw [h3, Set.ncard_singleton] at h4
    omega
  have hwN : w ∈ Subgroup.normalizer (A : Set G) := (Holds134.mem_oThreeWPre_iff.mp hwP).1
  have hw3 : (A.normalizerMonoidHom ⟨w, hwN⟩) ^ 3 = 1 :=
    h.Pstar_elem.2 _ (Holds134.mem_oThreeWPre_iff.mp hwP).2
  have hwd : w * d * w⁻¹ = d :=
    Proof152ResW.conj_eq_of_mem_normalizer hwN hw3 hdA hd3 hd1 (h.NA hwN)
  have hwC : w ∈ res3C d := Subgroup.mem_centralizer_singleton_iff.mpr (by
    calc w * d = w * d * w⁻¹ * w := by group
      _ = d * w := by rw [hwd])
  refine ⟨MulAut.conj (res3Pt d w hwC), ?_, ?_⟩
  · intro a ha
    obtain ⟨x, hxA, rfl⟩ := Subgroup.mem_map.mp ha
    refine Subgroup.mem_map.mpr ⟨⟨w, hwC⟩ * x * ⟨w, hwC⟩⁻¹, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp hwN (x : G)).mp hxA
    · rw [MulAut.conj_apply, res3Pt, map_mul, map_mul, map_inv]
  · intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hk' : res3Proj d (y ^ k) = res3Proj d (⟨w, hwC⟩ * y * ⟨w, hwC⟩⁻¹) := by
      rw [map_zpow, hk, MulAut.conj_apply, res3Pt, map_mul, map_mul, map_inv]
    have hinj := h.res3Proj_injOn (A.zpow_mem hyA k)
      ((Subgroup.mem_normalizer_iff.mp hwN (y : G)).mp hyA) hk'
    have hkG : (y : G) ^ k = w * (y : G) * w⁻¹ := congrArg Subtype.val hinj
    apply hwF
    have hmapF : (Subgroup.zpowers (y : G)).map (MulAut.conj w).toMonoidHom =
        Subgroup.zpowers (w * (y : G) * w⁻¹) := by
      rw [MonoidHom.map_zpowers]
      rfl
    have hle : (Subgroup.zpowers (y : G)).map (MulAut.conj w).toMonoidHom ≤
        Subgroup.zpowers (y : G) := by
      rw [hmapF, Subgroup.zpowers_le]
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, hkG⟩
    exact Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (MulAut.conj w).injective).ge

theorem res3QAmb (h : Res3Ctx A c L d K) :
    Res3QAmb (res3Pt d c h.c_mem_C) (res3Pt d d h.d_mem_C) (res3Img d A) :=
  ⟨h.res3QAmb_A_max, res3QAmb_oThreePrime d, h.res3QAmb_R4, h.res3QAmb_wsym⟩

end Res3Ctx

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3
