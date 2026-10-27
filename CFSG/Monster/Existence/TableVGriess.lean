module

public import CFSG.Monster.Existence.TwoPoint.ShapeOneHC
public import CFSG.Monster.Existence.TwoPoint.EvenShapes
public import CFSG.Monster.Existence.BabyOrder
public import CFSG.Monster.Existence.TwoPointTwoB
public import CFSG.Monster.GMS.BabyCover
public import CFSG.Monster.GMS.TableVOfCentralizer
public import CFSG.Sporadic.Co2
import Mathlib.Tactic.Group
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3045
public import Certificates.Certificate3048
public import Certificates.Certificate3049
public import Certificates.Certificate3050
public import Certificates.Certificate3051
public import Certificates.Certificate3101
public import Certificates.Certificate3102
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3107
public import Certificates.Certificate3108
public import Certificates.Certificate3109
public import Certificates.Certificate3115
public import Certificates.Certificate3116
public import Certificates.Certificate3117
public import Certificates.Certificate3138
public import Certificates.Certificate6001
public import Certificates.Certificate6002
public import Certificates.Certificate6003
public import Certificates.Certificate6004
public import Certificates.Certificate6005
public import Certificates.Certificate6007
public import Certificates.Certificate16026
public import Certificates.Certificate1020
public import Certificates.Certificate1022
public import Certificates.Certificate3015
public import Certificates.Certificate3016
public import Certificates.Certificate3018
public import Certificates.Certificate3020
public import Certificates.Certificate3021
public import Certificates.Certificate3022
public import Certificates.Certificate3023
public import Certificates.Certificate3024
public import Certificates.Certificate3027
public import Certificates.Certificate6021
public import Certificates.Certificate6022
public import Certificates.Certificate6023
public import Certificates.Certificate6024
public import Certificates.Certificate8954
public import Certificates.Certificate8955
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Monster.Existence.TwoPoint.Fi23ConjBase
public import CFSG.Monster.Existence.TwoPoint.Fi23MiscBase
public import CFSG.Monster.Existence.TwoPoint.Fi23Rels0Base
public import CFSG.Monster.Existence.TwoPoint.Fi23Rels1Base
public import CFSG.Monster.Existence.TwoPoint.Fi23Rels2Base
public import CFSG.Monster.Existence.TwoPoint.Fi23Rels3Base
public import CFSG.Monster.Existence.TwoPoint.Fi23Rels4Base
public import CFSG.Monster.Existence.TwoPoint.Fi23Rels5Base
public import CFSG.Monster.Existence.TwoPoint.Fi23RelsLongADBase
public import CFSG.Monster.Existence.TwoPoint.Fi23RelsLongJ
public import CFSG.Monster.Existence.TwoPoint.Fi23RelsLongJBase
public import CFSG.Monster.Existence.TwoPoint.Fi23RelsLongM
public import CFSG.Monster.Existence.TwoPoint.Fi23RelsLongMBase
public import CFSG.Monster.Existence.TwoPoint.Fi23RelsLongP
public import CFSG.Monster.Existence.TwoPoint.Fi23RelsLongPBase
public import CFSG.Monster.Existence.TwoPoint.OddAssembly
public import CFSG.Sporadic.Fi22
public import CFSG.Sporadic.HN.CertificateBase
public import Certificates.Certificate6047Base
public import Certificates.Certificate6048Base
public import Certificates.Certificate6049Base
public import Certificates.Certificate6050Base
public import Certificates.Certificate6051Base
public import Certificates.Certificate6052Base
public import Certificates.Certificate6053Base
public import Certificates.Certificate6054Base
public import Certificates.Certificate6055Base
public import Certificates.Certificate6056Base
public import Certificates.Certificate6057Base
public import Certificates.Certificate6058Base

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster.GMS CFSG.Blueprint.NativeSporadic

theorem exists_isBabyCover_of_isTwoACentralizer {G : Type} [Group G] {a : G}
    (ha : orderOf a = 2) (hA : IsTwoACentralizer a) :
    ∃ φ : ↥(Subgroup.centralizer ({a} : Set G)) →* B, IsBabyCover a φ := by
  obtain ⟨-, hZ, ⟨e⟩⟩ := hA
  let ψ : ↥(cent a) →* (↥(cent a) ⧸ Subgroup.center ↥(cent a)) := QuotientGroup.mk' _
  let φ : ↥(cent a) →* B := (e : (↥(cent a) ⧸ Subgroup.center ↥(cent a)) →* B).comp ψ
  refine ⟨φ, ha, ?_, ?_⟩
  · exact e.surjective.comp (QuotientGroup.mk'_surjective _)
  · show (φ.ker).map (cent a).subtype = Subgroup.zpowers a
    have : φ.ker = Subgroup.center ↥(cent a) := by
      ext c
      simp only [φ, ψ, MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.coe_ofClass,
        MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rw [this]
    exact hZ

theorem natCard_cent2_tGriess_xGriess :
    Nat.card ↥(cent2 tGriess xGriess) = tableVOrderZ := by
  have hs : HasLayeredTwoShape (cent2 tGriess (tGriess * xGriess)) 2 22
      fun X _ => Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Co2) := twoPointShape_tGriess_mul_xGriess
  obtain ⟨N, _, _, _, _, _, _, _, hN, hP⟩ := hs
  obtain ⟨e⟩ := hP
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup N
  rw [Nat.card_congr e.toEquiv, hN, CFSG.Sporadic.Co2.card_Co2] at h
  have heq : cent2 tGriess (tGriess * xGriess) = cent2 tGriess xGriess :=
    centralizer_inf_mul_eq tGriess xGriess
  rw [← heq, h]
  norm_num [tableVOrderZ]

theorem xGriess_mem_cent_tGriess : xGriess ∈ cent tGriess :=
  Subgroup.mem_centralizer_singleton_iff.2
    ((Subgroup.mem_centralizer_iff.1 xGriess_mem_centralizer_FE) tGriess
      (mem_FE.2 (Or.inr (Or.inl rfl)))).symm

theorem uGriess_mem_cent_tGriess : uGriess ∈ cent tGriess :=
  Subgroup.mem_centralizer_singleton_iff.2 uGriess_mul_tGriess

theorem xGriess_ne_tGriess : xGriess ≠ tGriess := fun h =>
  not_isConj_xGriess_tGriess (h ▸ IsConj.refl _)

theorem orderOf_uGriess : orderOf uGriess = 2 :=
  orderOf_eq_prime (by rw [sq]; exact uGriess_mul_self) uGriess_ne_one

theorem not_conj_xGriess_tGriess_mul
    (g : MGriess) : g * xGriess * g⁻¹ ≠ tGriess * xGriess := by
  intro h
  obtain ⟨h1, -⟩ := tGriess_mul_xGriess_mem_twoBNbr
  exact not_isConj_xGriess_tGriess ((isConj_iff.2 ⟨g, h⟩).trans h1.symm)

section TableV

variable [Finite MGriess] {φ : ↥(cent tGriess) →* B}

omit [Finite MGriess] in
theorem exists_conj_or_of_babyInv (h : IsBabyCover tGriess φ) (hT3 : BabyTableIII) {k : Fin 4}
    {s r : MGriess} (hs : s ∈ cent tGriess) (hr : r ∈ cent tGriess)
    (hks : BabyInv k (coverMap φ s)) (hkr : BabyInv k (coverMap φ r)) :
    ∃ g ∈ cent tGriess, g * s * g⁻¹ = r ∨ g * s * g⁻¹ = tGriess * r := by
  obtain ⟨c, hc⟩ := isConj_iff.1 (hT3.2 k _ _ hks hkr)
  obtain ⟨g, hg, rfl⟩ := h.exists_coverMap_eq c
  refine ⟨g, hg, ?_⟩
  have hgs : g * s * g⁻¹ ∈ cent tGriess :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hs) (Subgroup.inv_mem _ hg)
  have e : coverMap φ r = coverMap φ (g * s * g⁻¹) := by
    rw [coverMap_conj hg hs, hc]
  rcases (h.coverMap_eq_iff hr hgs).1 e with h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1

omit [Finite MGriess] in
theorem conj_inv_swap {g r : MGriess} (hg : g * r * g⁻¹ = tGriess * r) :
    g⁻¹ * (tGriess * r) * g⁻¹⁻¹ = r := by
  rw [← hg]
  group

theorem tableV_tGriess_of
    (h : IsBabyCover tGriess φ) (hT3 : BabyTableIII)
    (hcard : Nat.card ↥(cent tGriess) = twoBabyOrder)
    (hb : Nat.card ↥(cent2 tGriess uGriess) = tableVOrderB)
    {u : MGriess} (huC : u ∈ cent tGriess) (hu2 : orderOf u = 2) (hut : u ≠ tGriess)
    (huswap : ∃ g ∈ cent tGriess, g * u * g⁻¹ = tGriess * u)
    (hucard : Nat.card ↥(cent2 tGriess u) = tableVOrderU)
    (hw4 : ∃ w ∈ cent tGriess, w * w = tGriess)
    (hsyl : ∀ T : Subgroup MGriess, T ≤ cent2 tGriess xGriess → Nat.card T = 2 ^ 42 →
      ∀ y : MGriess, (y ∈ T ∧ ∀ s ∈ T, y * s = s * y) ↔
        (y = 1 ∨ y = tGriess ∨ y = xGriess ∨ y = tGriess * xGriess)) :
    TableV tGriess uGriess xGriess u := by
  have hb' : Nat.card ↥(Subgroup.centralizer ({tGriess} : Set MGriess) ⊓
      Subgroup.centralizer {uGriess}) = tableVOrderB := hb
  have hz' : Nat.card ↥(Subgroup.centralizer ({tGriess} : Set MGriess) ⊓
      Subgroup.centralizer {xGriess}) = tableVOrderZ := natCard_cent2_tGriess_xGriess
  have hu' : Nat.card ↥(Subgroup.centralizer ({tGriess} : Set MGriess) ⊓
      Subgroup.centralizer {u}) = tableVOrderU := hucard
  have hkb : BabyInv 0 (coverMap φ uGriess) := by
    obtain ⟨k, hk, hcase⟩ := h.exists_babyInv_cases hT3 uGriess_mem_cent_tGriess orderOf_uGriess
      uGriess_ne_tGriess
    rcases hcase with ⟨-, hc⟩ | ⟨hno, -⟩
    · rw [hb'] at hc
      rwa [(tableVOrderB_eq_iff k).1 hc] at hk
    · exact absurd swapGriess_conj_uGriess (hno _ swapGriess_mem_cent)
  have hkz : BabyInv 1 (coverMap φ xGriess) := by
    obtain ⟨k, hk, hcase⟩ := h.exists_babyInv_cases hT3 xGriess_mem_cent_tGriess orderOf_xGriess
      xGriess_ne_tGriess
    rcases hcase with ⟨⟨g, -, hg⟩, -⟩ | ⟨-, hc⟩
    · exact absurd hg (not_conj_xGriess_tGriess_mul g)
    · rw [hz'] at hc
      rwa [(tableVOrderZ_eq_two_mul_iff k).1 hc] at hk
  have hku : BabyInv 2 (coverMap φ u) := by
    obtain ⟨k, hk, hcase⟩ := h.exists_babyInv_cases hT3 huC hu2 hut
    rcases hcase with ⟨-, hc⟩ | ⟨hno, -⟩
    · rw [hu'] at hc
      rwa [(tableVOrderU_eq_iff k).1 hc] at hk
    · obtain ⟨g, hg, hgu⟩ := huswap
      exact absurd hgu (hno g hg)
  refine ⟨uGriess_mem_cent_tGriess, xGriess_mem_cent_tGriess, huC, orderOf_uGriess,
    orderOf_xGriess, hu2, uGriess_ne_tGriess, xGriess_ne_tGriess, hut, ?_, hcard, hb', hz', hu',
    hsyl⟩
  intro s hs hs2 hst
  obtain ⟨k, hk, hcase⟩ := h.exists_babyInv_cases hT3 hs hs2 hst
  fin_cases k
  · obtain ⟨g, hg, hgs | hgs⟩ := exists_conj_or_of_babyInv h hT3 hs uGriess_mem_cent_tGriess hk hkb
    · exact ⟨g, hg, Or.inl hgs⟩
    · refine ⟨swapGriess⁻¹ * g, Subgroup.mul_mem _ (Subgroup.inv_mem _ swapGriess_mem_cent) hg,
        Or.inl ?_⟩
      calc swapGriess⁻¹ * g * s * (swapGriess⁻¹ * g)⁻¹ =
          swapGriess⁻¹ * (g * s * g⁻¹) * swapGriess⁻¹⁻¹ := by group
        _ = uGriess := by rw [hgs]; exact conj_inv_swap swapGriess_conj_uGriess
  · obtain ⟨g, hg, hgs | hgs⟩ := exists_conj_or_of_babyInv h hT3 hs xGriess_mem_cent_tGriess hk hkz
    · exact ⟨g, hg, Or.inr (Or.inl hgs)⟩
    · exact ⟨g, hg, Or.inr (Or.inr (Or.inl hgs))⟩
  · obtain ⟨g, hg, hgs | hgs⟩ := exists_conj_or_of_babyInv h hT3 hs huC hk hku
    · exact ⟨g, hg, Or.inr (Or.inr (Or.inr hgs))⟩
    · obtain ⟨g₀, hg₀, hg₀u⟩ := huswap
      refine ⟨g₀⁻¹ * g, Subgroup.mul_mem _ (Subgroup.inv_mem _ hg₀) hg,
        Or.inr (Or.inr (Or.inr ?_))⟩
      calc g₀⁻¹ * g * s * (g₀⁻¹ * g)⁻¹ = g₀⁻¹ * (g * s * g⁻¹) * g₀⁻¹⁻¹ := by group
        _ = u := by rw [hgs]; exact conj_inv_swap hg₀u
  · exfalso
    obtain ⟨w, hwC, hww⟩ := hw4
    have ht1 : tGriess ≠ 1 := tGriess_ne_one
    have hwt' : w * tGriess = tGriess * w := Subgroup.mem_centralizer_singleton_iff.1 hwC
    have hw1 : w ≠ 1 := fun e => ht1 (by rw [← hww, e, one_mul])
    have hwt : w ≠ tGriess := fun e => ht1 (by
      have h' := hww
      rw [e, tGriess_mul_self] at h'
      exact h'.symm)
    have hw2 : orderOf (coverMap φ w) = 2 := by
      apply orderOf_eq_prime
      · rw [sq, ← coverMap_mul hwC hwC, hww, h.coverMap_b]
      · intro e
        rcases (h.coverMap_eq_one_iff hwC).1 e with e1 | e1
        · exact hw1 e1
        · exact hwt e1
    obtain ⟨k', hk'⟩ := hT3.1 _ hw2
    have hsq : ∀ g ∈ cent tGriess, (g * w * g⁻¹) * (g * w * g⁻¹) = tGriess := by
      intro g hg
      have hgt : g * tGriess = tGriess * g := Subgroup.mem_centralizer_singleton_iff.1 hg
      calc (g * w * g⁻¹) * (g * w * g⁻¹) = g * (w * w) * g⁻¹ := by group
        _ = g * tGriess * g⁻¹ := by rw [hww]
        _ = tGriess := by rw [hgt, mul_inv_cancel_right]
    have hinv : ∀ r ∈ cent tGriess, r * r = 1 → ∀ g ∈ cent tGriess,
        g * w * g⁻¹ ≠ r ∧ g * w * g⁻¹ ≠ tGriess * r := by
      intro r hr hrr g hg
      have hrt : r * tGriess = tGriess * r := Subgroup.mem_centralizer_singleton_iff.1 hr
      have htr2 : (tGriess * r) * (tGriess * r) = 1 := by
        calc (tGriess * r) * (tGriess * r) = tGriess * (r * tGriess) * r := by group
          _ = tGriess * (tGriess * r) * r := by rw [hrt]
          _ = (tGriess * tGriess) * (r * r) := by group
          _ = 1 := by rw [tGriess_mul_self, hrr, one_mul]
      refine ⟨fun e => ht1 ?_, fun e => ht1 ?_⟩
      · rw [← hsq g hg, e, hrr]
      · rw [← hsq g hg, e, htr2]
    have hss : s * s = 1 := by
      rw [← sq, ← hs2, pow_orderOf_eq_one]
    fin_cases k'
    · obtain ⟨g, hg, e | e⟩ := exists_conj_or_of_babyInv h hT3 hwC uGriess_mem_cent_tGriess hk' hkb
      · exact (hinv _ uGriess_mem_cent_tGriess uGriess_mul_self g hg).1 e
      · exact (hinv _ uGriess_mem_cent_tGriess uGriess_mul_self g hg).2 e
    · obtain ⟨g, hg, e | e⟩ := exists_conj_or_of_babyInv h hT3 hwC xGriess_mem_cent_tGriess hk' hkz
      · exact (hinv _ xGriess_mem_cent_tGriess xGriess_mul_self g hg).1 e
      · exact (hinv _ xGriess_mem_cent_tGriess xGriess_mul_self g hg).2 e
    · have huu : u * u = 1 := by rw [← sq, ← hu2, pow_orderOf_eq_one]
      obtain ⟨g, hg, e | e⟩ := exists_conj_or_of_babyInv h hT3 hwC huC hk' hku
      · exact (hinv _ huC huu g hg).1 e
      · exact (hinv _ huC huu g hg).2 e
    ·
      obtain ⟨g, hg, e | e⟩ := exists_conj_or_of_babyInv h hT3 hs hwC hk hk'
      · have h2 : (g * s * g⁻¹) * (g * s * g⁻¹) = 1 := by
          calc (g * s * g⁻¹) * (g * s * g⁻¹) = g * (s * s) * g⁻¹ := by group
            _ = 1 := by rw [hss]; group
        rw [e, hww] at h2
        exact ht1 h2
      · have h2 : (g * s * g⁻¹) * (g * s * g⁻¹) = 1 := by
          calc (g * s * g⁻¹) * (g * s * g⁻¹) = g * (s * s) * g⁻¹ := by group
            _ = 1 := by rw [hss]; group
        rw [e] at h2
        apply ht1
        calc tGriess = (tGriess * tGriess) * (w * w) := by rw [tGriess_mul_self, hww, one_mul]
          _ = tGriess * (tGriess * w) * w := by group
          _ = tGriess * (w * tGriess) * w := by rw [hwt']
          _ = (tGriess * w) * (tGriess * w) := by group
          _ = 1 := h2

end TableV

theorem tableVIn_MGriess_of
    [Finite MGriess]
    (hcls : ∀ s : MGriess, orderOf s = 2 → IsConj tGriess s ∨ IsConj xGriess s)
    {b z u : MGriess} (hV : TableV tGriess b z u) : TableVIn MGriess := by
  intro a ha
  rcases hcls a ha.1 with h | h
  · obtain ⟨g, rfl⟩ := isConj_iff.1 h
    refine TableV.exists_of_centralizerMulEquiv
      (CFSG.Monster.B.CTIB.centralizerEquiv (MulAut.conj g) tGriess) (fun c hc => ?_) hV
    show (MulAut.conj g) (c : MGriess) = g * tGriess * g⁻¹
    rw [hc, MulAut.conj_apply]
  · exfalso
    obtain ⟨φ, hφ⟩ := ha.exists_cover
    have hker : Nat.card φ.ker = 2 := by
      rw [← Subgroup.card_map_of_injective
        (Subgroup.centralizer ({a} : Set MGriess)).subtype_injective, hφ.ker_eq,
        Nat.card_zpowers, hφ.orderOf_eq]
    have hcard := Subgroup.card_ker_mul_card_of_surjective hφ.surjective
    rw [hker, card_nativeB] at hcard
    have h17 : 17 ∣ Nat.card ↥(cent a) := by
      rw [show cent a = Subgroup.centralizer ({a} : Set MGriess) from rfl, ← hcard]
      exact Dvd.dvd.mul_left (by norm_num [CFSG.Open.monsterBabyOrder]) 2
    exact (isTwoBCentralizer_MGriess a h).2.2.2.2.2 h17

end CFSG.Monster.Existence
