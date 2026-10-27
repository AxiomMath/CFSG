module

public import CFSG.RankThree.PartTwo.Sec15.Item152ExclSL2Tools
public import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofRead
public import CFSG.RankThree.PartTwo.Sec14.Concl142HJ
import CFSG.RankThree.PartTwo.Sec8.Item812Res3ProofTools
import CFSG.RankThree.PartTwo.Sec15.Item15Res3ProofInner
import CFSG.RankThree.PartTwo.KFacts.K71SU3AutFacts
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec13.OmegaNonempty
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

namespace Proof15Res6

variable {G : Type} [Group G] [Finite G]

@[expose] def actTriv (X N : Subgroup G) : Subgroup G where
  carrier := {y | y ∈ Subgroup.normalizer (N : Set G) ∧ ∀ x ∈ X, ⁅x, y⁆ ∈ N}
  mul_mem' := by
    rintro y z ⟨hyN, hy⟩ ⟨hzN, hz⟩
    refine ⟨mul_mem hyN hzN, fun x hx => ?_⟩
    have h2 : y * ⁅x, z⁆ * y⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp hyN _).mp (hz x hx)
    have heq : ⁅x, y * z⁆ = ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [heq]
    exact mul_mem (hy x hx) h2
  one_mem' := ⟨one_mem _, fun x _ => by simp [commutatorElement_def]⟩
  inv_mem' := by
    rintro y ⟨hyN, hy⟩
    refine ⟨inv_mem hyN, fun x hx => ?_⟩
    have h2 : y⁻¹ * ⁅x, y⁆⁻¹ * y⁻¹⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp (inv_mem hyN) _).mp (inv_mem (hy x hx))
    have heq : ⁅x, y⁻¹⁆ = y⁻¹ * ⁅x, y⁆⁻¹ * y⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [heq]
    exact h2

omit [Finite G] in
theorem conj_mem_actTriv {X N : Subgroup G} {w y : G}
    (hwX : w ∈ Subgroup.normalizer (X : Set G)) (hwN : w ∈ Subgroup.normalizer (N : Set G))
    (hy : y ∈ actTriv X N) : w * y * w⁻¹ ∈ actTriv X N := by
  obtain ⟨hyN, hyX⟩ := hy
  refine ⟨mul_mem (mul_mem hwN hyN) (inv_mem hwN), fun x hx => ?_⟩
  have hx' : w⁻¹ * x * w⁻¹⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (inv_mem hwX) x).mp hx
  have h1 : w * ⁅w⁻¹ * x * w⁻¹⁻¹, y⁆ * w⁻¹ ∈ N :=
    (Subgroup.mem_normalizer_iff.mp hwN _).mp (hyX _ hx')
  have heq : ⁅x, w * y * w⁻¹⁆ = w * ⁅w⁻¹ * x * w⁻¹⁻¹, y⁆ * w⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [heq]
  exact h1

theorem mem_zpowers_of_mem_actTriv {A : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hA27 : Nat.card A = 27) {LB : Subgroup G → Subgroup G}
    (hLB : ∀ B : Subgroup G, IsHyperplane A B → LB B = ⊥) {X N : Subgroup G}
    (hΔ : X = delta A LB X) (hXN : X ≤ Subgroup.normalizer (N : Set G))
    (hN3 : ¬ 3 ∣ Nat.card N) (hX3 : 3 ∣ Nat.card X) {a b : G} (ha : a ∈ A) (hb : b ∈ A)
    (ha1 : a ≠ 1) (haX : a ∈ actTriv X N) (hbX : b ∈ actTriv X N) :
    b ∈ Subgroup.zpowers a := by
  by_contra hb'
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set B := Subgroup.zpowers a ⊔ Subgroup.zpowers b with hBdef
  have hab : a * b = b * a := congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hB9 : Nat.card B = 3 ^ 2 :=
    Sec8.Item812Res3.card_sup_zpowers_eq_sq Nat.prime_three (hA.2 a ha) ha1 (hA.2 b hb) hb' hab
  have hBA : B ≤ A := sup_le (Subgroup.zpowers_le.mpr ha) (Subgroup.zpowers_le.mpr hb)
  have hB : IsHyperplane A B := ⟨hBA, by rw [hA27, hB9]; norm_num⟩
  have hB3 : IsPGroup 3 B := IsPGroup.of_card hB9
  have hBT : B ≤ actTriv X N :=
    sup_le (Subgroup.zpowers_le.mpr haX) (Subgroup.zpowers_le.mpr hbX)
  exact threePrime_of_qGen hΔ hB hB3 (hLB B hB) hXN hN3 (fun x hx y hy => (hBT hy).2 x hx) hX3

theorem zpowers_eq_of_mem_actTriv {A : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hA27 : Nat.card A = 27) {LB : Subgroup G → Subgroup G}
    (hLB : ∀ B : Subgroup G, IsHyperplane A B → LB B = ⊥) {X N : Subgroup G}
    (hΔ : X = delta A LB X) (hXN : X ≤ Subgroup.normalizer (N : Set G))
    (hN3 : ¬ 3 ∣ Nat.card N) (hX3 : 3 ∣ Nat.card X) {a b : G} (ha : a ∈ A) (hb : b ∈ A)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (haX : a ∈ actTriv X N) (hbX : b ∈ actTriv X N) :
    Subgroup.zpowers b = Subgroup.zpowers a := by
  have hba := mem_zpowers_of_mem_actTriv hA hA27 hLB hΔ hXN hN3 hX3 ha hb ha1 haX hbX
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hba) ?_
  rw [Sec13.card_zpowers_eq_three hA ha ha1, Sec13.card_zpowers_eq_three hA hb hb1]

omit [Finite G] in
theorem mem_actTriv_of_eq_sup {A : Subgroup G} {LB : Subgroup G → Subgroup G} {X : Subgroup G}
    {c' : G} (hcA : c' ∈ A) (hc3 : orderOf c' = 3)
    (hAX : A ≤ Subgroup.normalizer (X : Set G))
    (hX : X = pPrimeCoreOf 3 X ⊔
      deltaZero A LB (X ⊓ Subgroup.normalizer (Subgroup.zpowers c' : Set G))) :
    c' ∈ actTriv X (pPrimeCoreOf 3 X) := by
  set O := pPrimeCoreOf 3 X with hO
  set D := deltaZero A LB (X ⊓ Subgroup.normalizer (Subgroup.zpowers c' : Set G)) with hD
  have hcO : c' ∈ Subgroup.normalizer (O : Set G) :=
    (hAX.trans (normalizer_le_normalizer_pPrimeCoreOf 3 X)) hcA
  have hXO : X ≤ Subgroup.normalizer (O : Set G) := le_normalizer_pPrimeCoreOf 3 X
  have hDc : D ≤ Subgroup.centralizer ({c'} : Set G) := by
    refine sSup_le fun Q hQ => ?_
    exact le_centralizer_of_mem_invariantPiSubgroups hcA hc3
      ⟨hQ.2.trans inf_le_right, hQ.1.1.1.2.1, hQ.1.1.1.2.2⟩
  let S : Subgroup G :=
    { carrier := {x | x ∈ X ∧ ⁅x, c'⁆ ∈ O}
      mul_mem' := by
        rintro x y ⟨hx, hxc⟩ ⟨hy, hyc⟩
        refine ⟨mul_mem hx hy, ?_⟩
        have h1 : x * ⁅y, c'⁆ * x⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.mp (hXO hx) _).mp hyc
        have heq : ⁅x * y, c'⁆ = x * ⁅y, c'⁆ * x⁻¹ * ⁅x, c'⁆ := by
          simp only [commutatorElement_def]
          group
        rw [heq]
        exact mul_mem h1 hxc
      one_mem' := ⟨one_mem _, by simp [commutatorElement_def]⟩
      inv_mem' := by
        rintro x ⟨hx, hxc⟩
        refine ⟨inv_mem hx, ?_⟩
        have h1 : x⁻¹ * ⁅x, c'⁆⁻¹ * x⁻¹⁻¹ ∈ O :=
          (Subgroup.mem_normalizer_iff.mp (hXO (inv_mem hx)) _).mp (inv_mem hxc)
        have heq : ⁅x⁻¹, c'⁆ = x⁻¹ * ⁅x, c'⁆⁻¹ * x⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [heq]
        exact h1 }
  have hOS : O ≤ S := by
    intro n hn
    refine ⟨pPrimeCoreOf_le 3 X hn, ?_⟩
    have h1 : c' * n⁻¹ * c'⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.mp hcO _).mp (inv_mem hn)
    have heq : ⁅n, c'⁆ = n * (c' * n⁻¹ * c'⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [heq]
    exact mul_mem hn h1
  have hDS : D ≤ S := by
    intro d hd
    refine ⟨(deltaZero_le _ hd).1, ?_⟩
    have hdc : d * c' = c' * d := Subgroup.mem_centralizer_singleton_iff.mp (hDc hd)
    have heq : ⁅d, c'⁆ = 1 := by
      rw [commutatorElement_def, hdc]
      group
    rw [heq]
    exact one_mem _
  have hXS : X ≤ S := by
    rw [hX]
    exact sup_le hOS hDS
  exact ⟨hcO, fun x hx => (hXS hx).2⟩

theorem not_allPointsHJ_of_isEmpty {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (hL : IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    ¬ AllPointsHJ A := by
  intro hHJ
  obtain ⟨Le, hLe, ⟨φ⟩⟩ := hHJ c h.zpowers_mem_omegaA
  have h3 : 3 ∣ Nat.card Le := by
    have hc : Nat.card (↥Le ⧸ aschbacherSolvableCore 3 ↥Le) = 604800 := by
      rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_nativeJ2]
    have hdvd := Subgroup.card_quotient_dvd_card (aschbacherSolvableCore 3 ↥Le)
    rw [hc] at hdvd
    exact (by norm_num : (3 : ℕ) ∣ 604800).trans hdvd
  have hLeL : Le = L := (h.chosen136.2 c h.zpowers_mem_omegaA L h.mem_lA).2 Le hLe.1 h3
  subst hLeL
  exact hL.false φ

theorem isEmpty_j2_of_isoLThreePi {L : Type} [Group L] {p e : ℕ} [Fact p.Prime]
    (hL : Sec4.IsoLThreePi L p e) :
    IsEmpty (L ≃* CFSG.Blueprint.NativeSporadic.J2) :=
  ⟨fun ψ => KFacts.KS14.ks17J2NotList.1 p e (Proof1515.isoLThreePi_congr ψ hL)⟩

theorem isEmpty_j2_of_types {L : Type} [Group L]
    (hL : IsLThreePi L ∨ Nonempty (L ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (L ≃* CFSG.Blueprint.NativeSporadic.M22)) :
    IsEmpty (L ≃* CFSG.Blueprint.NativeSporadic.J2) := by
  refine ⟨fun ψ => ?_⟩
  rcases hL with ⟨p, e, hp, -, hiso⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · exact (isEmpty_j2_of_isoLThreePi hiso).false ψ
  · exact KFacts.KS14.ks17J2NotList.2.1.false (ψ.symm.trans φ)
  · exact KFacts.KS14.ks17J2NotList.2.2.false (ψ.symm.trans φ)

theorem exists_e9_of_quot {Y : Subgroup G} {E : Subgroup (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y)}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9) :
    ∃ B : Subgroup G, B ≤ Y ∧ CFSG.Assembly.IsElemAbelian 3 B ∧ Nat.card B = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := CFSG.pPrimeCore 3 ↥Y with hN
  set φ := QuotientGroup.mk' N with hφ
  have hE3 : IsPGroup 3 E := IsPGroup.of_card (n := 2) (by rw [hE9]; norm_num)
  have hEle : E ≤ (⊤ : Subgroup ↥Y).map φ := by
    rw [← MonoidHom.range_eq_map, QuotientGroup.range_mk']
    exact le_top
  obtain ⟨P, -, hP3, hPE⟩ := Proof15Res3Inner.exists_isPGroup_map_eq_of_le_map φ hE3 hEle
  have hN3 : ¬ 3 ∣ Nat.card N :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  have hinj : Function.Injective (φ.comp P.subtype) := by
    intro u v huv
    have h1 : (u : ↥Y)⁻¹ * v ∈ N := by
      have := huv
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, hφ, QuotientGroup.mk'_apply,
        QuotientGroup.eq] at this
      exact this
    obtain ⟨k, hk⟩ := hP3 (u⁻¹ * v)
    have h2 : ((u : ↥Y)⁻¹ * v) ^ 3 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have h3 := KFacts.eq_one_of_pow_three_pow_eq_one hN3 h1 h2
    exact Subtype.ext (inv_mul_eq_one.mp h3)
  have hrange : (φ.comp P.subtype).range = E := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hPE]
  let e : ↥P ≃* ↥E := (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  have hPcard : Nat.card P = 9 := by rw [Nat.card_congr e.toEquiv, hE9]
  have hPab : CFSG.Assembly.IsElemAbelian 3 P := by
    refine ⟨⟨⟨fun x y => e.injective ?_⟩⟩, fun x hx => ?_⟩
    · rw [map_mul, map_mul]
      exact hE.1.is_comm.comm (e x) (e y)
    · have h1 : ((e ⟨x, hx⟩ : ↥E) : ↥Y ⧸ N) ^ 3 = 1 := hE.2 _ (e ⟨x, hx⟩).2
      have h2 : e (⟨x, hx⟩ ^ 3) = e 1 := by
        apply Subtype.ext
        rw [map_pow, map_one, Subgroup.coe_pow, h1]
        rfl
      exact congrArg Subtype.val (e.injective h2)
  refine ⟨P.map Y.subtype, Subgroup.map_subtype_le P, CFSG.SectionRank.isElemAbelian_map hPab _, ?_⟩
  rw [Subgroup.card_map_of_injective Y.subtype_injective, hPcard]

end Proof15Res6

end CFSG.RankThree.PartTwo.Sec15
