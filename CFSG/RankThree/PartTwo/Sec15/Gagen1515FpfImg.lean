module

import CFSG.RankThree.PartTwo.Sec14.Item148StepQuot
import CFSG.RankThree.PartTwo.Sec14.LBNatural
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Closure
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical
import CFSG.RankThree.PartTwo.Sec15.Gagen1515FpfLift
public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements
public import CFSG.RankThree.PartTwo.Sec14.Std

public section

namespace CFSG.RankThree.PartTwo.Sec15.Gagen1515Fpf

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem pPrimeCoreOf_deltaZero_le {A Y : Subgroup G} (hY : Y ∈ scriptY A)
    (hF1 : letI := ker148_normal hY.2
      ∀ N : Subgroup ↥(img148 A Y (deltaZero A (lB A) Y)), N.Normal → ¬ 3 ∣ Nat.card N →
        N = ⊥) :
    pPrimeCoreOf 3 (deltaZero A (lB A) Y) ≤ pPrimeCoreOf 3 Y := by
  letI := ker148_normal hY.2
  set X := deltaZero A (lB A) Y with hXdef
  set O := pPrimeCoreOf 3 X with hOdef
  have hOle : O ≤ pPrimeCoreOf 3 Y := by
    have hOY : O ≤ Y := (pPrimeCoreOf_le 3 X).trans (deltaZero_le Y)
    have hOYA : O ≤ Y ⊔ A := hOY.trans le_sup_left
    have hOX : O ≤ X := pPrimeCoreOf_le 3 X
    have hle : img148 A Y O ≤ img148 A Y X := img148_mono hOX
    have hN : img148 A Y X ≤
        Subgroup.normalizer (img148 A Y O : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
      img148_le_normalizer (le_normalizer_pPrimeCoreOf 3 X)
    have hn : ((img148 A Y O).subgroupOf (img148 A Y X)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr hN
    have hcard : ¬ 3 ∣ Nat.card ((img148 A Y O).subgroupOf (img148 A Y X)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
      intro h3
      have hdvd : Nat.card (img148 A Y O) ∣ Nat.card O := by
        have h := Subgroup.card_map_dvd (O.subgroupOf (Y ⊔ A))
          (QuotientGroup.mk' (ker148 A Y))
        rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOYA).toEquiv] at h
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
        (coprime_card_pPrimeCoreOf 3 X) (h3.trans hdvd)
    have hbot := hF1 _ hn hcard
    rw [Subgroup.subgroupOf_eq_bot] at hbot
    have hOimg : img148 A Y O = ⊥ := hbot.eq_bot_of_le hle
    intro o ho
    have hoY : o ∈ Y := hOY ho
    have hmem : QuotientGroup.mk' (ker148 A Y) ⟨o, Subgroup.mem_sup_left hoY⟩ ∈
        img148 A Y O :=
      Subgroup.mem_map.mpr ⟨⟨o, Subgroup.mem_sup_left hoY⟩, Subgroup.mem_subgroupOf.mpr ho, rfl⟩
    rw [hOimg] at hmem
    have hq : QuotientGroup.mk' (ker148 A Y) ⟨o, Subgroup.mem_sup_left hoY⟩ = 1 :=
      Subgroup.mem_bot.mp hmem
    exact (mk'_ker148_eq_one_iff (A := A) (Y := Y)).mp hq
  exact hOle

theorem deltaZero_inf_normalizer_le_centralizer_lB {A Y : Subgroup G} {c : G}
    (hcA : c ∈ A) (hc3 : orderOf c = 3) :
    deltaZero A (lB A) (Y ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G)) ≤
      Subgroup.centralizer ({c} : Set G) := by
  refine sSup_le fun Q hQ => ?_
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hxN := (hQ.2.trans inf_le_right) hx
  have h1 : x * c * x⁻¹ * c⁻¹ ∈ Subgroup.zpowers c :=
    mul_mem ((Subgroup.mem_normalizer_iff.mp hxN c).mp (Subgroup.mem_zpowers c))
      (inv_mem (Subgroup.mem_zpowers c))
  have h2 : x * c * x⁻¹ * c⁻¹ ∈ Q := by
    have h3 : c * x⁻¹ * c⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hQ.1.1.1.2.2 hcA) x⁻¹).mp (inv_mem hx)
    have e : x * c * x⁻¹ * c⁻¹ = x * (c * x⁻¹ * c⁻¹) := by group
    rw [e]
    exact mul_mem hx h3
  have hQ3 : ¬ 3 ∣ Nat.card Q :=
    (isPiSubgroup_piCompl_iff Nat.prime_three Q).mp hQ.1.1.1.2.1
  have hdisj : Subgroup.zpowers c ⊓ Q = ⊥ := by
    have hd : Disjoint (Subgroup.zpowers c) Q :=
      Subgroup.disjoint_of_coprime_natCard (by
        rw [Nat.card_zpowers, hc3]
        exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hQ3)
    exact hd.eq_bot
  have h4 : x * c * x⁻¹ * c⁻¹ ∈ Subgroup.zpowers c ⊓ Q := ⟨h1, h2⟩
  rw [hdisj, Subgroup.mem_bot] at h4
  calc x * c = x * c * x⁻¹ * c⁻¹ * (c * x) := by group
    _ = c * x := by rw [h4, one_mul]

theorem commutator_zpowers_le_of_sup_of_centralizer {O D : Subgroup G} {c : G}
    (hD : D ≤ Subgroup.normalizer (O : Set G))
    (hc : c ∈ Subgroup.normalizer (O : Set G))
    (hDc : D ≤ Subgroup.centralizer ({c} : Set G)) :
    ⁅O ⊔ D, Subgroup.zpowers c⁆ ≤ O := by
  rw [Subgroup.commutator_le]
  intro r hr h hh
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  have hr' : r ∈ (O : Set G) * (D : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left O D hD]
    exact hr
  obtain ⟨n, hn, y, hy, rfl⟩ := hr'
  have hck : c ^ k ∈ Subgroup.normalizer (O : Set G) := Subgroup.zpow_mem _ hc k
  have hyc : y * c ^ k = c ^ k * y := by
    have h1 : y * c = c * y := Subgroup.mem_centralizer_singleton_iff.mp (hDc hy)
    exact (Commute.zpow_right h1 k).eq
  have e : ⁅n * y, c ^ k⁆ = n * (c ^ k * n⁻¹ * (c ^ k)⁻¹) := by
    simp only [commutatorElement_def]
    calc n * y * c ^ k * (n * y)⁻¹ * (c ^ k)⁻¹ =
        n * (y * c ^ k) * y⁻¹ * n⁻¹ * (c ^ k)⁻¹ := by group
      _ = n * (c ^ k * y) * y⁻¹ * n⁻¹ * (c ^ k)⁻¹ := by rw [hyc]
      _ = n * (c ^ k * n⁻¹ * (c ^ k)⁻¹) := by group
  rw [e]
  exact O.mul_mem hn ((Subgroup.mem_normalizer_iff.mp hck n⁻¹).mp (O.inv_mem hn))

theorem commutator_zpowers_conj_le {X O : Subgroup G} {c d g : G}
    (hcomm : ⁅X, Subgroup.zpowers c⁆ ≤ O)
    (hgX : g ∈ Subgroup.normalizer (X : Set G))
    (hgO : g ∈ Subgroup.normalizer (O : Set G))
    (hgc : g * c * g⁻¹ = c * d) :
    ⁅X, Subgroup.zpowers (c * d)⁆ ≤ O := by
  have hgX' : g⁻¹ ∈ Subgroup.normalizer (X : Set G) := inv_mem hgX
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hx' : g⁻¹ * x * g ∈ X := by
    simpa using (Subgroup.mem_normalizer_iff.mp hgX' x).mp hx
  have hbase : ⁅g⁻¹ * x * g, c ^ k⁆ ∈ O :=
    (Subgroup.commutator_le.mp hcomm) _ hx' _ (Subgroup.zpow_mem_zpowers c k)
  have hpow : (c * d) ^ k = g * c ^ k * g⁻¹ := by
    rw [← hgc]
    have h1 : (MulAut.conj g) (c ^ k) = ((MulAut.conj g) c) ^ k := map_zpow _ _ _
    rw [MulAut.conj_apply, MulAut.conj_apply] at h1
    exact h1.symm
  have e : ⁅x, (c * d) ^ k⁆ = g * ⁅g⁻¹ * x * g, c ^ k⁆ * g⁻¹ := by
    rw [hpow]
    simp only [commutatorElement_def]
    group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp hgO (⁅g⁻¹ * x * g, c ^ k⁆)).mp hbase

theorem commutator_element_zpowers_le {X O : Subgroup G} {c d : G}
    (hcomm_c : ⁅X, Subgroup.zpowers c⁆ ≤ O)
    (hcomm_cd : ⁅X, Subgroup.zpowers (c * d)⁆ ≤ O)
    (hcO : c ∈ Subgroup.normalizer (O : Set G))
    (hcdO : c * d ∈ Subgroup.normalizer (O : Set G)) :
    ∀ x ∈ X, ⁅x, d⁆ ∈ O ∧ ⁅x, d⁻¹⁆ ∈ O := by
  intro x hx
  have hxc : ⁅x, c⁆ ∈ O :=
    (Subgroup.commutator_le.mp hcomm_c) x hx c (Subgroup.mem_zpowers c)
  have hxci : ⁅x, c⁻¹⁆ ∈ O :=
    (Subgroup.commutator_le.mp hcomm_c) x hx c⁻¹ (inv_mem (Subgroup.mem_zpowers c))
  have hxcd : ⁅x, c * d⁆ ∈ O :=
    (Subgroup.commutator_le.mp hcomm_cd) x hx (c * d) (Subgroup.mem_zpowers (c * d))
  have hxcdi : ⁅x, (c * d)⁻¹⁆ ∈ O :=
    (Subgroup.commutator_le.mp hcomm_cd) x hx (c * d)⁻¹
      (inv_mem (Subgroup.mem_zpowers (c * d)))
  constructor
  · have hd_eq : d = c⁻¹ * (c * d) := by group
    rw [hd_eq]
    have e : ⁅x, c⁻¹ * (c * d)⁆ =
        ⁅x, c⁻¹⁆ * (c⁻¹ * ⁅x, c * d⁆ * (c⁻¹)⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact O.mul_mem hxci
      ((Subgroup.mem_normalizer_iff.mp (inv_mem hcO) (⁅x, c * d⁆)).mp hxcd)
  · have hd_eq : d⁻¹ = (c * d)⁻¹ * c := by group
    rw [hd_eq]
    have e : ⁅x, (c * d)⁻¹ * c⁆ =
        ⁅x, (c * d)⁻¹⁆ * ((c * d)⁻¹ * ⁅x, c⁆ * ((c * d)⁻¹)⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact O.mul_mem hxcdi
      ((Subgroup.mem_normalizer_iff.mp (inv_mem hcdO) (⁅x, c⁆)).mp hxc)

private theorem commutator_zpowers_le_of_point {X O : Subgroup G} {d : G}
    (hdO : d ∈ Subgroup.normalizer (O : Set G))
    (hpoint : ∀ x ∈ X, ⁅x, d⁆ ∈ O ∧ ⁅x, d⁻¹⁆ ∈ O) :
    ⁅X, Subgroup.zpowers d⁆ ≤ O := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  obtain ⟨hxd, hxdi⟩ := hpoint x hx
  refine (zpow_induction_right (P := fun a => a ∈ Subgroup.normalizer (O : Set G) ∧
    ⁅x, a⁆ ∈ O) ?_ ?_ ?_ k).2
  · exact ⟨(Subgroup.normalizer (O : Set G)).one_mem, by simp⟩
  · rintro a ⟨haN, haO⟩
    refine ⟨(Subgroup.normalizer (O : Set G)).mul_mem haN hdO, ?_⟩
    have e : ⁅x, a * d⁆ = ⁅x, a⁆ * (a * ⁅x, d⁆ * a⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact O.mul_mem haO ((Subgroup.mem_normalizer_iff.mp haN (⁅x, d⁆)).mp hxd)
  · rintro a ⟨haN, haO⟩
    refine ⟨(Subgroup.normalizer (O : Set G)).mul_mem haN (inv_mem hdO), ?_⟩
    have e : ⁅x, a * d⁻¹⁆ = ⁅x, a⁆ * (a * ⁅x, d⁻¹⁆ * a⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact O.mul_mem haO ((Subgroup.mem_normalizer_iff.mp haN (⁅x, d⁻¹⁆)).mp hxdi)

theorem commutator_zpowers_le {A Y : Subgroup G} {c d g : G} (hY : Y ∈ scriptY A)
    (hcA : c ∈ A) (hc3 : orderOf c = 3) (hgA : g ∈ Subgroup.normalizer (A : Set G))
    (hgY : g ∈ Subgroup.normalizer (Y : Set G)) (hgc : g * c * g⁻¹ = c * d)
    (hO : pPrimeCoreOf 3 (deltaZero A (lB A) Y) ≤ pPrimeCoreOf 3 Y)
    (hX : deltaZero A (lB A) Y = pPrimeCoreOf 3 (deltaZero A (lB A) Y) ⊔
      deltaZero A (lB A) (Y ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G))) :
    ⁅deltaZero A (lB A) Y, Subgroup.zpowers d⁆ ≤ pPrimeCoreOf 3 Y := by
  set X := deltaZero A (lB A) Y with hXdef
  set O := pPrimeCoreOf 3 X with hOdef
  set V := pPrimeCoreOf 3 Y with hVdef
  set Dc := deltaZero A (lB A) (Y ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G)) with hDcdef
  have hXeq : X = O ⊔ Dc := by
    rw [hXdef, hOdef, hDcdef]
    exact hX
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.2
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := fun a ha =>
    Sec14.mem_normalizer_deltaZero (Sec14.isNaturalFamily_lB A)
      (Subgroup.le_normalizer ha) (hAY ha)
  have hAO : A ≤ Subgroup.normalizer (O : Set G) :=
    hAX.trans (Sec14.normalizer_le_normalizer_pPrimeCoreOf 3 X)
  have hcO : c ∈ Subgroup.normalizer (O : Set G) := hAO hcA
  have hDcX : Dc ≤ X := by
    rw [hDcdef, hXdef]
    exact deltaZero_mono inf_le_left
  have hDcO : Dc ≤ Subgroup.normalizer (O : Set G) :=
    hDcX.trans (Sec14.le_normalizer_pPrimeCoreOf 3 X)
  have hDcC : Dc ≤ Subgroup.centralizer ({c} : Set G) :=
    deltaZero_inf_normalizer_le_centralizer_lB hcA hc3
  have hcomm_c : ⁅X, Subgroup.zpowers c⁆ ≤ O := by
    rw [hXeq]
    exact commutator_zpowers_le_of_sup_of_centralizer hDcO hcO hDcC
  have hgX : g ∈ Subgroup.normalizer (X : Set G) :=
    Sec14.mem_normalizer_deltaZero (Sec14.isNaturalFamily_lB A) hgA hgY
  have hgO : g ∈ Subgroup.normalizer (O : Set G) :=
    Sec14.normalizer_le_normalizer_pPrimeCoreOf 3 X hgX
  have hcomm_cd : ⁅X, Subgroup.zpowers (c * d)⁆ ≤ O :=
    commutator_zpowers_conj_le hcomm_c hgX hgO hgc
  have hcdO : c * d ∈ Subgroup.normalizer (O : Set G) := by
    rw [← hgc]
    exact (Subgroup.normalizer (O : Set G)).mul_mem
      ((Subgroup.normalizer (O : Set G)).mul_mem hgO hcO) (inv_mem hgO)
  have hdO : d ∈ Subgroup.normalizer (O : Set G) := by
    have hd_eq : d = c⁻¹ * (c * d) := by group
    rw [hd_eq]
    exact (Subgroup.normalizer (O : Set G)).mul_mem (inv_mem hcO) hcdO
  exact (commutator_zpowers_le_of_point hdO
    (commutator_element_zpowers_le hcomm_c hcomm_cd hcO hcdO)).trans hO

theorem img148_eq_bot_of_le_pPrimeCoreOf {A Y Z : Subgroup G} [(ker148 A Y).Normal]
    (hZ : Z ≤ pPrimeCoreOf 3 Y) : img148 A Y Z = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨z, hz, hzZ, hzx⟩ := mem_img148_iff.mp hx
  rw [← hzx]
  exact (mk'_ker148_eq_one_iff (A := A) (Y := Y)).mpr (hZ hzZ)

theorem mem_normalizer_deltaZero_inf_normalizer {A Y : Subgroup G} {c d : G}
    (hY : A ≤ Subgroup.normalizer (Y : Set G)) (hdA : d ∈ A) (hcd : Commute c d) :
    d ∈ Subgroup.normalizer
      (deltaZero A (lB A) (Y ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
        Set G) := by
  have hdNA : d ∈ Subgroup.normalizer (A : Set G) := Subgroup.le_normalizer hdA
  have hdNY : d ∈ Subgroup.normalizer (Y : Set G) := hY hdA
  have hdc : d * c * d⁻¹ = c := by
    rw [hcd.eq.symm]
    group
  have hmapc : (Subgroup.zpowers c).map (MulAut.conj d).toMonoidHom = Subgroup.zpowers c := by
    rw [MonoidHom.map_zpowers]
    have h1 : (MulAut.conj d).toMonoidHom c = c := by
      change (MulAut.conj d) c = c
      rw [MulAut.conj_apply, hdc]
    rw [h1]
  have hdNNc : d ∈ Subgroup.normalizer
      (Subgroup.normalizer (Subgroup.zpowers c : Set G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have h : (Subgroup.normalizer (Subgroup.zpowers c : Set G)).map
        (MulAut.conj d).toMonoidHom = Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
      rw [Subgroup.map_equiv_normalizer_eq, hmapc]
    exact h
  have hdNYc : d ∈ Subgroup.normalizer
      ((Y ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G) : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf (Subgroup.mem_inf.mpr ⟨hdNY, hdNNc⟩)
  exact Sec14.mem_normalizer_deltaZero (Sec14.isNaturalFamily_lB A) hdNA hdNYc

theorem deltaZero_le_inf_centralizer_sup_inf {A Y : Subgroup G} {c d : G}
    (hY : Y ∈ scriptY A) (hdA : d ∈ A) (hd3 : orderOf d = 3) (hcd : Commute c d)
    (hd : ⁅deltaZero A (lB A) Y, Subgroup.zpowers d⁆ ≤ pPrimeCoreOf 3 Y) :
    deltaZero A (lB A) (Y ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G)) ≤
      (deltaZero A (lB A) (Y ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G)) ⊓
        Subgroup.centralizer ({d} : Set G)) ⊔
      (deltaZero A (lB A) (Y ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G)) ⊓
        pPrimeCoreOf 3 Y) := by
  set X := deltaZero A (lB A) Y with hXdef
  set V := pPrimeCoreOf 3 Y with hVdef
  set Dc := deltaZero A (lB A) (Y ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G)) with hDcdef
  set K := Dc ⊓ V with hKdef
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.2
  have hAV : A ≤ Subgroup.normalizer (V : Set G) := by
    rw [hVdef]
    exact hAY.trans (Sec14.normalizer_le_normalizer_pPrimeCoreOf 3 Y)
  have hDcY : Dc ≤ Y := by
    rw [hDcdef]
    exact (deltaZero_le _).trans inf_le_left
  have hDcX : Dc ≤ X := by
    rw [hDcdef, hXdef]
    exact deltaZero_mono inf_le_left
  have hdDc : d ∈ Subgroup.normalizer (Dc : Set G) := by
    rw [hDcdef]
    exact mem_normalizer_deltaZero_inf_normalizer hAY hdA hcd
  have hdV : d ∈ Subgroup.normalizer (V : Set G) := hAV hdA
  have hKV : K ≤ V := by
    rw [hKdef]
    exact inf_le_right
  have hK3 : ¬ 3 ∣ Nat.card K := by
    intro h3
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (Sec14.coprime_card_pPrimeCoreOf 3 Y) (h3.trans (Subgroup.card_dvd_of_le hKV))
  have hdK : d ∈ Subgroup.normalizer (K : Set G) := by
    rw [hKdef]
    exact Subgroup.inf_normalizer_le_normalizer_inf (Subgroup.mem_inf.mpr ⟨hdDc, hdV⟩)
  have hDcK : Dc ≤ Subgroup.normalizer (K : Set G) := by
    rw [hKdef]
    exact (le_inf Subgroup.le_normalizer
      (hDcY.trans (Sec14.le_normalizer_pPrimeCoreOf 3 Y))).trans
        Subgroup.inf_normalizer_le_normalizer_inf
  have hcommK : ⁅Dc, Subgroup.zpowers d⁆ ≤ K := by
    refine le_inf ?_ ?_
    · exact (Subgroup.le_normalizer_iff_commutator_le_left).mp
        (Subgroup.zpowers_le.mpr hdDc)
    · exact (Subgroup.commutator_mono hDcX le_rfl).trans hd
  exact le_inf_centralizer_sup (by rw [hKdef]; exact inf_le_left) hDcK hdK hd3 hK3 hcommK

theorem img148_eq_of_eq_sup_of_le_pPrimeCoreOf {A Y X O D E K : Subgroup G}
    [(ker148 A Y).Normal] (hX : X = O ⊔ D) (hO : O ≤ pPrimeCoreOf 3 Y)
    (hD : D = E ⊔ K) (hDle : D ≤ Y ⊔ A) (hK : K ≤ pPrimeCoreOf 3 Y) :
    img148 A Y X = img148 A Y E := by
  have hOY : O ≤ Y ⊔ A := (hO.trans (pPrimeCoreOf_le 3 Y)).trans le_sup_left
  have hEY : E ≤ Y ⊔ A := (le_sup_left.trans (le_of_eq hD.symm)).trans hDle
  have hKY : K ≤ Y ⊔ A := (hK.trans (pPrimeCoreOf_le 3 Y)).trans le_sup_left
  have hOimg : img148 A Y O = ⊥ := img148_eq_bot_of_le_pPrimeCoreOf hO
  have hKimg : img148 A Y K = ⊥ := img148_eq_bot_of_le_pPrimeCoreOf hK
  have hDimg : img148 A Y D = img148 A Y E := by
    rw [hD, img148_sup hEY hKY, hKimg, sup_bot_eq]
  rw [hX, img148_sup hOY hDle, hOimg, bot_sup_eq, hDimg]

theorem three_dvd_card_inSubgroup_perfectResidual_of_img148 {A Y E : Subgroup G}
    [(ker148 A Y).Normal] (hEYA : E ≤ Y ⊔ A)
    (h : 3 ∣ Nat.card (inSubgroup perfectResidual (img148 A Y E))) :
    3 ∣ Nat.card (inSubgroup perfectResidual E) := by
  set M : Subgroup ↥(Y ⊔ A) := E.subgroupOf (Y ⊔ A) with hMdef
  have hMπ : M.map (QuotientGroup.mk' (ker148 A Y)) = img148 A Y E := rfl
  have hres_map : (inSubgroup perfectResidual M).map
      (QuotientGroup.mk' (ker148 A Y)) =
      inSubgroup perfectResidual (M.map (QuotientGroup.mk' (ker148 A Y))) := by
    have h := CFSG.SignalizerFunctorTheorem.Nonsolvable.map_perfectResidual_map
      (G := ↥(Y ⊔ A)) (QuotientGroup.mk' (ker148 A Y)) M
    simpa only [inSubgroup] using h
  have hdvd : Nat.card (inSubgroup perfectResidual (img148 A Y E)) ∣
      Nat.card (inSubgroup perfectResidual M) := by
    rw [← hMπ, ← hres_map]
    exact Subgroup.card_map_dvd _ _
  have hsub : (inSubgroup perfectResidual E).subgroupOf (Y ⊔ A) =
      inSubgroup perfectResidual M := by
    unfold inSubgroup
    apply Subgroup.map_injective (Subgroup.subtype_injective (Y ⊔ A))
    rw [Subgroup.subgroupOf_map_subtype, Subgroup.map_map]
    rw [inf_eq_left.mpr ((Subgroup.map_subtype_le (perfectResidual E)).trans hEYA)]
    rw [← Subgroup.map_map,
      CFSG.SignalizerFunctorTheorem.Nonsolvable.map_perfectResidual_map
        (Y ⊔ A).subtype M,
      Subgroup.map_subgroupOf_eq_of_le hEYA]
  have hcard_sub : Nat.card ((inSubgroup perfectResidual E).subgroupOf (Y ⊔ A)) =
      Nat.card (inSubgroup perfectResidual E) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      ((Subgroup.map_subtype_le (perfectResidual E)).trans hEYA)).toEquiv
  rw [← hcard_sub, hsub]
  exact h.trans hdvd

theorem three_dvd_card_residual {A Y : Subgroup G} {c d : G} (hY : Y ∈ scriptY A)
    (hdA : d ∈ A) (hd3 : orderOf d = 3) (hcd : Commute c d)
    (hO : pPrimeCoreOf 3 (deltaZero A (lB A) Y) ≤ pPrimeCoreOf 3 Y)
    (hX : deltaZero A (lB A) Y = pPrimeCoreOf 3 (deltaZero A (lB A) Y) ⊔
      deltaZero A (lB A) (Y ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G)))
    (hd : ⁅deltaZero A (lB A) Y, Subgroup.zpowers d⁆ ≤ pPrimeCoreOf 3 Y)
    (hF2 : letI := ker148_normal hY.2
      3 ∣ Nat.card (inSubgroup perfectResidual (img148 A Y (deltaZero A (lB A) Y)))) :
    3 ∣ Nat.card (inSubgroup perfectResidual
      (deltaZero A (lB A) (Y ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G)) ⊓
        Subgroup.centralizer ({d} : Set G))) := by
  letI := ker148_normal hY.2
  set X := deltaZero A (lB A) Y with hXdef
  set O := pPrimeCoreOf 3 X with hOdef
  set V := pPrimeCoreOf 3 Y with hVdef
  set Dc := deltaZero A (lB A) (Y ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G)) with hDcdef
  set E := Dc ⊓ Subgroup.centralizer ({d} : Set G) with hEdef
  set K := Dc ⊓ V with hKdef
  have hXeq : X = O ⊔ Dc := by
    rw [hXdef, hOdef, hDcdef]
    exact hX
  have hDcY : Dc ≤ Y := by
    rw [hDcdef]
    exact (deltaZero_le _).trans inf_le_left
  have hDc_le : Dc ≤ E ⊔ K :=
    deltaZero_le_inf_centralizer_sup_inf hY hdA hd3 hcd hd
  have hDcEq : Dc = E ⊔ K := by
    refine le_antisymm hDc_le (sup_le ?_ ?_)
    · rw [hEdef]
      exact inf_le_left
    · rw [hKdef]
      exact inf_le_left
  have himg : img148 A Y X = img148 A Y E := by
    refine img148_eq_of_eq_sup_of_le_pPrimeCoreOf hXeq hO hDcEq ?_ ?_
    · exact hDcY.trans le_sup_left
    · rw [hKdef]
      exact inf_le_right
  have h3img : 3 ∣ Nat.card (inSubgroup perfectResidual (img148 A Y E)) := by
    rw [← himg]
    exact hF2
  exact three_dvd_card_inSubgroup_perfectResidual_of_img148
    ((inf_le_left.trans hDcY).trans le_sup_left) h3img

end CFSG.RankThree.PartTwo.Sec15.Gagen1515Fpf
