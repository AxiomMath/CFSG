module

public import Mathlib.GroupTheory.PGroup

import CFSG.GroupTheory.CommutatorCentralizerIn
import CFSG.GroupTheory.CoprimeActionSupport.CoprimeSeries
import CFSG.GroupTheory.HuppertProduct.Quotient
import CFSG.RankThree.PartTwo.Sec20.Item20Res3ProofComm
import Mathlib.Topology.Sheaves.Presheaf

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup
open CFSG.GroupTheory (commutatorCentralizerIn mem_commutatorCentralizerIn)
open CFSG.GroupTheory.CoprimeActionSupport (commutator_mem_of_coprime_of_commutator_mem)

variable {G : Type*} [Group G]

private abbrev cm (x y : G) : G := x * y * x⁻¹ * y⁻¹

private lemma cm_comm (x y : G) : cm x y = (cm y x)⁻¹ := by
  simp only [cm]
  group

private lemma centralizes_of_centralizes_mod {Q₀ W B B' : Subgroup G} (hBQ₀ : B ≤ Q₀)
    (hQ₀B : Q₀ ≤ normalizer (B : Set G)) (hQ₀W : Q₀ ≤ normalizer (W : Set G))
    (hBB' : B ⊓ B' = W) (hB' : ∀ x ∈ Q₀, ∀ a ∈ B, x * a * x⁻¹ * a⁻¹ ∈ B') :
    ∀ b ∈ B, ∀ x ∈ Q₀, b * x * b⁻¹ * x⁻¹ ∈ W := by
  have hcent : B ≤ commutatorCentralizerIn Q₀ W Q₀ hQ₀W := by
    intro a ha
    refine (mem_commutatorCentralizerIn hQ₀W).mpr ⟨hBQ₀ ha, fun x hx => ?_⟩
    show a * x * a⁻¹ * x⁻¹ ∈ W
    have hmemB : a * x * a⁻¹ * x⁻¹ ∈ B := by
      have hx' : x * a⁻¹ * x⁻¹ ∈ B := by
        simpa using (Subgroup.le_normalizer_iff.mp hQ₀B x hx) a⁻¹ (B.inv_mem ha)
      have hid : a * x * a⁻¹ * x⁻¹ = a * (x * a⁻¹ * x⁻¹) := by group
      rw [hid]
      exact B.mul_mem ha hx'
    have hmemB' : a * x * a⁻¹ * x⁻¹ ∈ B' := by
      have h := hB' x hx a ha
      have hid : a * x * a⁻¹ * x⁻¹ = (x * a * x⁻¹ * a⁻¹)⁻¹ := by group
      rw [hid]
      exact B'.inv_mem h
    have hinf : a * x * a⁻¹ * x⁻¹ ∈ B ⊓ B' := ⟨hmemB, hmemB'⟩
    rwa [hBB'] at hinf
  exact fun b hb x hx => ((mem_commutatorCentralizerIn hQ₀W).mp (hcent hb)).2 x hx

private lemma commutator_mem_of_mem_sup_of_inf_eq {Q₀ W A A' : Subgroup G} (hAQ₀ : A ≤ Q₀)
    (hA'Q₀ : A' ≤ Q₀) (hQ₀A : Q₀ ≤ normalizer (A : Set G))
    (hQ₀A' : Q₀ ≤ normalizer (A' : Set G)) (hQ₀W : Q₀ ≤ normalizer (W : Set G))
    (hAA' : A ⊓ A' = W) (hA : ∀ x ∈ Q₀, ∀ a ∈ A, x * a * x⁻¹ * a⁻¹ ∈ A')
    (hA' : ∀ x ∈ Q₀, ∀ a ∈ A', x * a * x⁻¹ * a⁻¹ ∈ A) :
    ∀ y ∈ A ⊔ A', ∀ x ∈ Q₀, cm y x ∈ W := by
  have h1 : A ≤ commutatorCentralizerIn Q₀ W Q₀ hQ₀W := fun b hb =>
    (mem_commutatorCentralizerIn hQ₀W).mpr
      ⟨hAQ₀ hb, centralizes_of_centralizes_mod hAQ₀ hQ₀A hQ₀W hAA' hA b hb⟩
  have h2 : A' ≤ commutatorCentralizerIn Q₀ W Q₀ hQ₀W := fun b hb =>
    (mem_commutatorCentralizerIn hQ₀W).mpr
      ⟨hA'Q₀ hb,
        centralizes_of_centralizes_mod hA'Q₀ hQ₀A' hQ₀W (by rw [inf_comm, hAA']) hA' b hb⟩
  intro y hy x hx
  exact ((mem_commutatorCentralizerIn hQ₀W).mp (sup_le h1 h2 hy)).2 x hx

private lemma sup_eq_sup_commutator_sup {Q₀ W A A' : Subgroup G} (hWY : W ≤ A ⊔ A')
    (hA'A : A' ≤ ⁅Q₀, Q₀⁆ ⊔ A) (hAA' : A ≤ ⁅Q₀, Q₀⁆ ⊔ A') (hD : ⁅Q₀, Q₀⁆ ≤ A ⊔ A') :
    A ⊔ A' = A ⊔ (⁅Q₀, Q₀⁆ ⊔ W) ∧ A ⊔ A' = A' ⊔ (⁅Q₀, Q₀⁆ ⊔ W) := by
  have hDDle : ⁅Q₀, Q₀⁆ ⊔ W ≤ A ⊔ A' := sup_le hD hWY
  constructor
  · refine le_antisymm ?_ ?_
    · refine sup_le le_sup_left ?_
      have h1 : ⁅Q₀, Q₀⁆ ≤ A ⊔ (⁅Q₀, Q₀⁆ ⊔ W) :=
        (le_sup_left : ⁅Q₀, Q₀⁆ ≤ ⁅Q₀, Q₀⁆ ⊔ W).trans le_sup_right
      exact hA'A.trans (sup_le h1 le_sup_left)
    · exact sup_le le_sup_left hDDle
  · refine le_antisymm ?_ ?_
    · refine sup_le ?_ le_sup_left
      have h1 : ⁅Q₀, Q₀⁆ ≤ A' ⊔ (⁅Q₀, Q₀⁆ ⊔ W) :=
        (le_sup_left : ⁅Q₀, Q₀⁆ ≤ ⁅Q₀, Q₀⁆ ⊔ W).trans le_sup_right
      exact hAA'.trans (sup_le h1 le_sup_left)
    · exact sup_le le_sup_right hDDle

private lemma cm_cm_mem_of_centralizes {L Q₀ Y W : Subgroup G} (hYQ₀ : Y ≤ Q₀)
    (hQ₀W : Q₀ ≤ normalizer (W : Set G)) (hcentY : ∀ y ∈ Y, ∀ x ∈ Q₀, cm y x ∈ W)
    (hcentL : ∀ g ∈ L, ∀ x ∈ Q₀, cm g x ∈ Y) :
    ∀ g ∈ L, ∀ x ∈ Q₀, ∀ y ∈ Q₀, cm g (cm x y) ∈ W := by
  intro g hg x hx y hy
  have hu : cm g x ∈ Y := hcentL g hg x hx
  have hv : cm g y ∈ Y := hcentL g hg y hy
  have huQ : cm g x ∈ Q₀ := hYQ₀ hu
  have hvQ : cm g y ∈ Q₀ := hYQ₀ hv
  have hxvy : cm x y ∈ Q₀ :=
    Q₀.mul_mem (Q₀.mul_mem (Q₀.mul_mem hx hy) (Q₀.inv_mem hx)) (Q₀.inv_mem hy)
  have h1 : cm g x * cm x (cm g y) * (cm g x)⁻¹ ∈ W := by
    have hmem : cm x (cm g y) ∈ W := by
      have h0 : cm (cm g y) x ∈ W := hcentY _ hv x hx
      have h1 : (cm x (cm g y))⁻¹ ∈ W := by rwa [cm_comm (cm g y) x] at h0
      simpa only [inv_inv] using W.inv_mem h1
    exact (Subgroup.le_normalizer_iff (H := Q₀) (K := W)).mp hQ₀W _ huQ _ hmem
  have h2 : cm (cm g x * cm g y) (cm x y) ∈ W := by
    have hprod : cm g x * cm g y ∈ Y := Y.mul_mem hu hv
    exact hcentY _ hprod (cm x y) hxvy
  have h3 : cm x y * cm (cm g x) (cm g y * y) * (cm x y)⁻¹ ∈ W := by
    have hvy : cm g y * y ∈ Q₀ := Q₀.mul_mem hvQ hy
    have hmem : cm (cm g x) (cm g y * y) ∈ W := hcentY _ hu _ hvy
    exact (Subgroup.le_normalizer_iff (H := Q₀) (K := W)).mp hQ₀W _ hxvy _ hmem
  have hid : cm g (cm x y) = (cm g x * cm x (cm g y) * (cm g x)⁻¹)
      * cm (cm g x * cm g y) (cm x y)
      * (cm x y * cm (cm g x) (cm g y * y) * (cm x y)⁻¹) := by
    simp only [cm]
    group
  rw [hid]
  exact W.mul_mem (W.mul_mem h1 h2) h3

private lemma centralizes_commutator_sup_of_centralizes {L Q₀ Y W : Subgroup G} (hYQ₀ : Y ≤ Q₀)
    (hQ₀W : Q₀ ≤ normalizer (W : Set G)) (hLW : L ≤ normalizer (W : Set G))
    (hDDW : ⁅Q₀, Q₀⁆ ⊔ W ≤ normalizer (W : Set G))
    (hcentY : ∀ y ∈ Y, ∀ x ∈ Q₀, cm y x ∈ W)
    (hcentL : ∀ g ∈ L, ∀ x ∈ Q₀, cm g x ∈ Y) :
    ∀ g ∈ L, ∀ d ∈ ⁅Q₀, Q₀⁆ ⊔ W, cm d g ∈ W := by
  have hkey := cm_cm_mem_of_centralizes hYQ₀ hQ₀W hcentY hcentL
  have hWtriv : W ≤ commutatorCentralizerIn (⁅Q₀, Q₀⁆ ⊔ W) W L hDDW := by
    intro w hw
    refine (mem_commutatorCentralizerIn hDDW).mpr ⟨Subgroup.mem_sup_right hw, fun g hg => ?_⟩
    have hgw : g * w * g⁻¹ * w⁻¹ ∈ W :=
      W.mul_mem ((Subgroup.le_normalizer_iff (H := L) (K := W)).mp hLW g hg w hw) (W.inv_mem hw)
    show cm w g ∈ W
    have hid : cm w g = (g * w * g⁻¹ * w⁻¹)⁻¹ := by simp only [cm]; group
    rw [hid]
    exact W.inv_mem hgw
  have hcommTriv : ⁅Q₀, Q₀⁆ ≤ commutatorCentralizerIn (⁅Q₀, Q₀⁆ ⊔ W) W L hDDW := by
    refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
    show cm x y ∈ commutatorCentralizerIn (⁅Q₀, Q₀⁆ ⊔ W) W L hDDW
    refine (mem_commutatorCentralizerIn hDDW).mpr
      ⟨Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hx hy), fun g hg => ?_⟩
    have h := hkey g hg x hx y hy
    show cm (cm x y) g ∈ W
    have hid : cm (cm x y) g = (cm g (cm x y))⁻¹ := cm_comm _ _
    rw [hid]
    exact W.inv_mem h
  intro g hg d hd
  exact ((mem_commutatorCentralizerIn hDDW).mp (sup_le hcommTriv hWtriv hd)).2 g hg

private lemma centralizes_sup_of_centralizes {S A D Y : Subgroup G}
    (hAD : A ≤ normalizer (D : Set G)) (hY : Y = A ⊔ D)
    (hSD : S ≤ normalizer (D : Set G)) (hSA : ∀ s ∈ S, ∀ a ∈ A, cm s a ∈ D) :
    ∀ s ∈ S, ∀ y ∈ Y, cm s y ∈ D := by
  have hYD : Y ≤ normalizer (D : Set G) := by
    rw [hY]
    exact sup_le hAD Subgroup.le_normalizer
  have hAle : A ≤ commutatorCentralizerIn Y D S hYD := by
    intro a ha
    have haY : a ∈ Y := by rw [hY]; exact Subgroup.mem_sup_left ha
    refine (mem_commutatorCentralizerIn hYD).mpr ⟨haY, fun s hs => ?_⟩
    show cm a s ∈ D
    rw [cm_comm]
    exact D.inv_mem (hSA s hs a ha)
  have hDle : D ≤ commutatorCentralizerIn Y D S hYD := by
    intro d hd
    have hdY : d ∈ Y := by rw [hY]; exact Subgroup.mem_sup_right hd
    refine (mem_commutatorCentralizerIn hYD).mpr ⟨hdY, fun s hs => ?_⟩
    show cm d s ∈ D
    have h1 : s * d⁻¹ * s⁻¹ ∈ D :=
      (Subgroup.le_normalizer_iff (H := S) (K := D)).mp hSD s hs d⁻¹ (D.inv_mem hd)
    have hid : cm d s = d * (s * d⁻¹ * s⁻¹) := by simp only [cm]; group
    rw [hid]
    exact D.mul_mem hd h1
  intro s hs y hy
  have hy' : y ∈ A ⊔ D := by rwa [hY] at hy
  show cm s y ∈ D
  rw [cm_comm]
  exact D.inv_mem (((mem_commutatorCentralizerIn hYD).mp (sup_le hAle hDle hy')).2 s hs)

private lemma normalizer_facts {L Q₀ W A A' S S' : Subgroup G} (hQ₀L : Q₀ ≤ L)
    (hLQ₀ : L ≤ normalizer (Q₀ : Set G)) (hLW : L ≤ normalizer (W : Set G))
    (hSL : S ≤ L) (hS'L : S' ≤ L) (hL : L ≤ S ⊔ S') (hSA : S ≤ normalizer (A : Set G))
    (hS'A' : S' ≤ normalizer (A' : Set G)) (hAQ₀ : A ≤ Q₀)
    (hYA : A ⊔ A' = A ⊔ (⁅Q₀, Q₀⁆ ⊔ W)) (hYA' : A ⊔ A' = A' ⊔ (⁅Q₀, Q₀⁆ ⊔ W)) :
    L ≤ normalizer ((A ⊔ A' : Subgroup G) : Set G) ∧
      A ≤ normalizer ((⁅Q₀, Q₀⁆ ⊔ W : Subgroup G) : Set G) ∧
      A ⊔ A' ≤ normalizer ((⁅Q₀, Q₀⁆ ⊔ W : Subgroup G) : Set G) ∧
      L ≤ normalizer ((⁅Q₀, Q₀⁆ ⊔ W : Subgroup G) : Set G) ∧
      ⁅Q₀, Q₀⁆ ⊔ W ≤ normalizer (W : Set G) := by
  have hLcomm : L ≤ normalizer (⁅Q₀, Q₀⁆ : Subgroup G) :=
    CFSG.RankThree.PartTwo.Sec20.Res3.le_normalizer_commutator hLQ₀ hLQ₀
  have hQ₀comm : Q₀ ≤ normalizer (⁅Q₀, Q₀⁆ : Subgroup G) :=
    CFSG.RankThree.PartTwo.Sec20.Res3.le_normalizer_commutator Subgroup.le_normalizer
      Subgroup.le_normalizer
  have hLDD : L ≤ normalizer ((⁅Q₀, Q₀⁆ ⊔ W : Subgroup G) : Set G) :=
    CFSG.GroupTheory.HuppertProduct.le_normalizer_sup hLcomm hLW
  have hADD : A ≤ normalizer ((⁅Q₀, Q₀⁆ ⊔ W : Subgroup G) : Set G) :=
    CFSG.GroupTheory.HuppertProduct.le_normalizer_sup (hAQ₀.trans hQ₀comm)
      (hAQ₀.trans (hQ₀L.trans hLW))
  have hYDD : A ⊔ A' ≤ normalizer ((⁅Q₀, Q₀⁆ ⊔ W : Subgroup G) : Set G) := by
    have h : A ⊔ (⁅Q₀, Q₀⁆ ⊔ W) ≤ normalizer ((⁅Q₀, Q₀⁆ ⊔ W : Subgroup G) : Set G) :=
      sup_le hADD Subgroup.le_normalizer
    rwa [← hYA] at h
  have hSDD : S ≤ normalizer ((⁅Q₀, Q₀⁆ ⊔ W : Subgroup G) : Set G) :=
    CFSG.GroupTheory.HuppertProduct.le_normalizer_sup
      (CFSG.RankThree.PartTwo.Sec20.Res3.le_normalizer_commutator (hSL.trans hLQ₀) (hSL.trans hLQ₀))
      (hSL.trans hLW)
  have hS'DD : S' ≤ normalizer ((⁅Q₀, Q₀⁆ ⊔ W : Subgroup G) : Set G) :=
    CFSG.GroupTheory.HuppertProduct.le_normalizer_sup
      (CFSG.RankThree.PartTwo.Sec20.Res3.le_normalizer_commutator
        (hS'L.trans hLQ₀) (hS'L.trans hLQ₀))
      (hS'L.trans hLW)
  have hSY : S ≤ normalizer ((A ⊔ A' : Subgroup G) : Set G) := by
    rw [hYA]
    exact CFSG.GroupTheory.HuppertProduct.le_normalizer_sup hSA hSDD
  have hS'Y : S' ≤ normalizer ((A ⊔ A' : Subgroup G) : Set G) := by
    rw [hYA']
    exact CFSG.GroupTheory.HuppertProduct.le_normalizer_sup hS'A' hS'DD
  refine ⟨hL.trans (sup_le hSY hS'Y), hADD, hYDD, hLDD, ?_⟩
  exact sup_le ((Subgroup.commutator_le_self Q₀).trans (hQ₀L.trans hLW)) Subgroup.le_normalizer

private lemma centralizes_of_le_sup {L Q₀ A A' S S' : Subgroup G} (hSL : S ≤ L)
    (hS'L : S' ≤ L) (hL : L ≤ S ⊔ S') (hLY : L ≤ normalizer ((A ⊔ A' : Subgroup G) : Set G))
    (hSQ : ∀ s ∈ S, ∀ x ∈ Q₀, cm s x ∈ A ⊔ A')
    (hS'Q : ∀ s ∈ S', ∀ x ∈ Q₀, cm s x ∈ A ⊔ A') :
    ∀ g ∈ L, ∀ x ∈ Q₀, cm g x ∈ A ⊔ A' := by
  have hS1 : S ≤ commutatorCentralizerIn L (A ⊔ A') Q₀ hLY :=
    fun s hs => (mem_commutatorCentralizerIn hLY).mpr ⟨hSL hs, hSQ s hs⟩
  have hS'1 : S' ≤ commutatorCentralizerIn L (A ⊔ A') Q₀ hLY :=
    fun s hs => (mem_commutatorCentralizerIn hLY).mpr ⟨hS'L hs, hS'Q s hs⟩
  have h := hL.trans (sup_le hS1 hS'1)
  exact fun g hg => ((mem_commutatorCentralizerIn hLY).mp (h hg)).2

theorem commutator_mem_of_coprime_of_central_images {p : ℕ} [Fact p.Prime]
    {L Q₀ W A A' S S' : Subgroup G} (hQ₀ : IsPGroup p Q₀) (hQ₀L : Q₀ ≤ L)
    (hWA : W ≤ A) (hAQ₀ : A ≤ Q₀) (hA'Q₀ : A' ≤ Q₀)
    (hAn : Q₀ ≤ normalizer (A : Set G)) (hA'n : Q₀ ≤ normalizer (A' : Set G))
    (hLW : L ≤ normalizer (W : Set G)) (hLQ₀ : L ≤ normalizer (Q₀ : Set G)) (hAA' : A ⊓ A' = W)
    (hA : ∀ x ∈ Q₀, ∀ a ∈ A, x * a * x⁻¹ * a⁻¹ ∈ A')
    (hA' : ∀ x ∈ Q₀, ∀ a ∈ A', x * a * x⁻¹ * a⁻¹ ∈ A)
    (hD : ⁅Q₀, Q₀⁆ ≤ A ⊔ A') (hDA : A' ≤ ⁅Q₀, Q₀⁆ ⊔ A) (hDA' : A ≤ ⁅Q₀, Q₀⁆ ⊔ A')
    (hSL : S ≤ L) (hS'L : S' ≤ L) (hL : L ≤ S ⊔ S')
    (hSA : S ≤ normalizer (A : Set G)) (hS'A' : S' ≤ normalizer (A' : Set G))
    (hSQ : ∀ s ∈ S, ∀ x ∈ Q₀, s * x * s⁻¹ * x⁻¹ ∈ A ⊔ A')
    (hS'Q : ∀ s ∈ S', ∀ x ∈ Q₀, s * x * s⁻¹ * x⁻¹ ∈ A ⊔ A')
    (hSW : ∀ s ∈ S, ∀ a ∈ A, s * a * s⁻¹ * a⁻¹ ∈ W)
    (hS'W : ∀ s ∈ S', ∀ a ∈ A', s * a * s⁻¹ * a⁻¹ ∈ W)
    {l : G} (hl : l ∈ L) (hcop : (orderOf l).Coprime p) :
    ∀ x ∈ Q₀, l * x * l⁻¹ * x⁻¹ ∈ W := by
  classical
  have hWY : W ≤ A ⊔ A' := hWA.trans le_sup_left
  have hYQ₀ : A ⊔ A' ≤ Q₀ := sup_le hAQ₀ hA'Q₀
  have hQ₀W : Q₀ ≤ normalizer (W : Set G) := hQ₀L.trans hLW
  have hDDQ₀ : ⁅Q₀, Q₀⁆ ⊔ W ≤ Q₀ := sup_le (Subgroup.commutator_le_self Q₀) (hWA.trans hAQ₀)
  obtain ⟨hYA, hYA'⟩ := sup_eq_sup_commutator_sup hWY hDA hDA' hD
  obtain ⟨hLY, hADD, hYDD, hLDD, hDDW⟩ :=
    normalizer_facts hQ₀L hLQ₀ hLW hSL hS'L hL hSA hS'A' hAQ₀ hYA hYA'
  have hYcomm : ∀ y ∈ A ⊔ A', ∀ x ∈ Q₀, cm y x ∈ W :=
    commutator_mem_of_mem_sup_of_inf_eq hAQ₀ hA'Q₀ hAn hA'n hQ₀W hAA' hA hA'
  have h4 : ∀ g ∈ L, ∀ x ∈ Q₀, cm g x ∈ A ⊔ A' :=
    centralizes_of_le_sup hSL hS'L hL hLY (fun s hs => by simpa only [cm] using hSQ s hs)
      (fun s hs => by simpa only [cm] using hS'Q s hs)
  have h5 : ∀ g ∈ L, ∀ d ∈ ⁅Q₀, Q₀⁆ ⊔ W, cm d g ∈ W :=
    centralizes_commutator_sup_of_centralizes hYQ₀ hQ₀W hLW hDDW hYcomm h4
  have hA'DD : A' ≤ normalizer ((⁅Q₀, Q₀⁆ ⊔ W : Subgroup G) : Set G) :=
    le_sup_right.trans hYDD
  have h6S : ∀ s ∈ S, ∀ y ∈ A ⊔ A', cm s y ∈ ⁅Q₀, Q₀⁆ ⊔ W :=
    centralizes_sup_of_centralizes hADD hYA (hSL.trans hLDD)
      (fun s hs => fun a ha => Subgroup.mem_sup_right (hSW s hs a ha))
  have h6S' : ∀ s ∈ S', ∀ y ∈ A ⊔ A', cm s y ∈ ⁅Q₀, Q₀⁆ ⊔ W :=
    centralizes_sup_of_centralizes hA'DD hYA' (hS'L.trans hLDD)
      (fun s hs => fun a ha => Subgroup.mem_sup_right (hS'W s hs a ha))
  have h6 : ∀ g ∈ L, ∀ y ∈ A ⊔ A', cm g y ∈ ⁅Q₀, Q₀⁆ ⊔ W := by
    have hS1 : S ≤ commutatorCentralizerIn L (⁅Q₀, Q₀⁆ ⊔ W) (A ⊔ A') hLDD :=
      fun s hs => (mem_commutatorCentralizerIn hLDD).mpr ⟨hSL hs, h6S s hs⟩
    have hS'1 : S' ≤ commutatorCentralizerIn L (⁅Q₀, Q₀⁆ ⊔ W) (A ⊔ A') hLDD :=
      fun s hs => (mem_commutatorCentralizerIn hLDD).mpr ⟨hS'L hs, h6S' s hs⟩
    have h := hL.trans (sup_le hS1 hS'1)
    exact fun g hg => ((mem_commutatorCentralizerIn hLDD).mp (h hg)).2
  have hYp : IsPGroup p ↥(A ⊔ A') := hQ₀.to_le hYQ₀
  have hDDp : IsPGroup p ↥(⁅Q₀, Q₀⁆ ⊔ W) := hQ₀.to_le hDDQ₀
  have hYW : A ⊔ A' ≤ normalizer (W : Set G) := hYQ₀.trans hQ₀W
  have hlW : l ∈ normalizer (W : Set G) := hLW hl
  have hYW' : ∀ y ∈ A ⊔ A', l * y * l⁻¹ * y⁻¹ ∈ W :=
    commutator_mem_of_coprime_of_commutator_mem (P := A ⊔ A') (W := ⁅Q₀, Q₀⁆ ⊔ W) (Z := W)
      hDDp hDDW hcop hlW (fun y hy => by simpa only [cm] using h6 l hl y hy)
      (fun d hd => by
        have h : cm d l ∈ W := h5 l hl d hd
        have hid : l * d * l⁻¹ * d⁻¹ = (cm d l)⁻¹ := by simp only [cm]; group
        rw [hid]
        exact W.inv_mem h)
  have hQ₀W' : ∀ x ∈ Q₀, l * x * l⁻¹ * x⁻¹ ∈ W :=
    commutator_mem_of_coprime_of_commutator_mem (P := Q₀) (W := A ⊔ A') (Z := W) hYp hYW hcop hlW
      (fun x hx => by simpa only [cm] using h4 l hl x hx) hYW'
  intro x hx
  simpa only [cm] using hQ₀W' x hx

end CFSG.Quasithin.Stroth.Rq

end
