module

public import CFSG.OddTranspositions.PartThree.LocalBenderBasic
public import CFSG.GroupTheory.PCore.SolvableRadical
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Comparator.Defs
public import CFSG.Timmesfeld.Bridge.OddTranspDefs

import CFSG.GroupTheory.OddCoreQuotient
import CFSG.Timmesfeld.Bridge.Asc72Bender
import CFSG.Timmesfeld.RootSubgroupBasic
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.Models
import CFSG.OddTranspositions.O4PairTenWidth
import CFSG.OddTranspositions.Width
import CFSG.Walter.Defs
import Certificates.Certificate1
import Certificates.Certificate2

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld (commute_of_mem_closure)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {D : Set G}

omit [Finite G] in
theorem not_mem_center_localGroup_of_transitive {z u v : G} (hu : u ∈ centSet D z)
    (hv : v ∈ centSet D z) (huv : u ≠ v)
    (htrans : ∀ x ∈ centSet D z, ∀ y ∈ centSet D z, ∃ h ∈ localGroup D z, h * x * h⁻¹ = y) :
    ∀ x : localGroup D z, (x : G) ∈ centSet D z → x ∉ Subgroup.center (localGroup D z) := by
  intro x hx hxZ
  have hconj : ∀ h : localGroup D z, h * x * h⁻¹ = x := by
    intro h
    calc h * x * h⁻¹ = x * h * h⁻¹ := by rw [Subgroup.mem_center_iff.mp hxZ h]
      _ = x := by group
  have hxu : (x : G) = u := by
    obtain ⟨h, hhH, hh⟩ := htrans x hx u hu
    have h1 : (h : G) * (x : G) * (h : G)⁻¹ = (x : G) := by
      simpa using congrArg Subtype.val (hconj ⟨h, hhH⟩)
    exact h1.symm.trans hh
  have hxv : (x : G) = v := by
    obtain ⟨h, hhH, hh⟩ := htrans x hx v hv
    have h1 : (h : G) * (x : G) * (h : G)⁻¹ = (x : G) := by
      simpa using congrArg Subtype.val (hconj ⟨h, hhH⟩)
    exact h1.symm.trans hh
  exact huv (hxu.symm.trans hxv)

omit [Finite G] in
theorem ne_mul_of_transitive (hS : Setup G D) {z u v : G} (hu : u ∈ centSet D z)
    (hv : v ∈ centSet D z) (huv : u ≠ v)
    (htrans : ∀ x ∈ centSet D z, ∀ y ∈ centSet D z, ∃ h ∈ localGroup D z, h * x * h⁻¹ = y)
    {r s : G} (hr : r ∈ D) (hs : s ∈ D) (hrs : r ≠ s) (hcrs : Commute r s) : z ≠ r * s := by
  intro hzrs
  have hrz : Commute r z := by
    simpa [hzrs] using (Commute.refl r).mul_right hcrs
  have hsz : Commute s z := by
    simpa [hzrs] using (hcrs.symm).mul_right (Commute.refl s)
  have hrC : r ∈ centSet D z := ⟨hr, hrz⟩
  have hcommr : ∀ x ∈ centSet D z, Commute x r := by
    intro x hx
    have h1 : Commute x (r * s) := by simpa [hzrs] using hx.2
    exact ((hS.oddT.commute_mul_iff hr hs hx.1 hrs hcrs).mp h1).1
  have hrH : r ∈ localGroup D z := mem_localGroup_of_mem hrC
  have hrZ : (⟨r, hrH⟩ : localGroup D z) ∈ Subgroup.center (localGroup D z) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact (commute_of_mem_closure
      (S := centSet D z) (S' := {r}) (fun a ha b hb => by
        rw [Set.mem_singleton_iff] at hb
        rw [hb]
        exact hcommr a ha) g.2 (Subgroup.subset_closure (by simp))).eq
  exact not_mem_center_localGroup_of_transitive hu hv huv htrans ⟨r, hrH⟩ hrC hrZ

theorem localGroup_involution_cases_of_isBenderGroup (hS : Setup G D) {z u v : G}
    (hu : u ∈ centSet D z) (hv : v ∈ centSet D z) (huv : u ≠ v)
    (htrans : ∀ x ∈ centSet D z, ∀ y ∈ centSet D z, ∃ h ∈ localGroup D z, h * x * h⁻¹ = y)
    (hR : CFSG.solvableRadical (localGroup D z) ≤ Subgroup.center (localGroup D z))
    (hZ2 : ∀ c ∈ Subgroup.center (localGroup D z), c * c = 1 → (c : G) = 1 ∨ (c : G) = z)
    (hB : CFSG.BenderSuzuki.IsBenderGroup
      (localGroup D z ⧸ CFSG.solvableRadical (localGroup D z)))
    {t : G} (ht : t ∈ localGroup D z) (htt : t * t = 1) :
    t = 1 ∨ t = z ∨ t ∈ centSet D z ∨ t * z ∈ centSet D z := by
  classical
  set H := localGroup D z with hH
  set R : Subgroup H := CFSG.solvableRadical H with hRdef
  let T : H := ⟨t, ht⟩
  have hTT : T * T = 1 := Subtype.ext htt
  have huH : u ∈ H := mem_localGroup_of_mem hu
  let U : H := ⟨u, huH⟩
  have hUU : U * U = 1 := Subtype.ext (by simpa using hS.oddT.mul_self_eq_one hu.1)
  have hUR : U ∉ R := by
    intro hUR
    exact not_mem_center_localGroup_of_transitive hu hv huv htrans U hu (hR hUR)
  by_cases hTR : T ∈ R
  · have hTZ : T ∈ Subgroup.center H := hR hTR
    rcases hZ2 T hTZ hTT with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
  · obtain ⟨d, r, ⟨g, hgd⟩, hrR, hT_eq, hrr⟩ :=
      CFSG.GroupTheory.exists_conj_mul_mem_solvableRadical hR hB hUU hUR hTT hTR
    have hrZ : r ∈ Subgroup.center H := hR hrR
    have hdD : (d : G) ∈ D := by
      rw [hgd]
      exact hS.conj_mem (g : G) hu.1
    have hdz : Commute (d : G) z := by
      rw [hgd]
      have hgz : Commute (g : G) z := commute_of_mem_localGroup g.2
      have h := (hgz.mul_left hu.2).mul_left hgz.inv_left
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h
    have hdC : (d : G) ∈ centSet D z := ⟨hdD, hdz⟩
    rcases hZ2 r hrZ hrr with hr1 | hrz
    · have htG : t = (d : G) := by
        have h := congrArg Subtype.val hT_eq
        simpa [T, hr1] using h
      exact Or.inr (Or.inr (Or.inl (by simpa [htG] using hdC)))
    · have hzz : z * z = 1 := by
        have h : (r : G) * (r : G) = 1 := by simpa using congrArg Subtype.val hrr
        simpa [hrz] using h
      have htG : t * z = (d : G) := by
        have h : t = (d : G) * (r : G) := by
          simpa [T] using congrArg Subtype.val hT_eq
        calc t * z = (d : G) * (r : G) * z := by rw [h]
          _ = (d : G) * z * z := by rw [hrz]
          _ = (d : G) := by rw [mul_assoc, hzz, mul_one]
      exact Or.inr (Or.inr (Or.inr (by simpa [htG] using hdC)))

omit [Finite G] in
theorem false_of_eq_conj_mul_mul (hS : Setup G D) {z u v c : G}
    (hu : u ∈ centSet D z) (hv : v ∈ centSet D z) (huv : u ≠ v) (hc : Commute u v)
    (htrans : ∀ x ∈ centSet D z, ∀ y ∈ centSet D z,
      ∃ h ∈ localGroup D z, h * x * h⁻¹ = y)
    (huvz : u * v * z ∈ D) (hzD : z ∉ D)
    (hz_eq : z = c * (v * (u * v * z)) * c⁻¹) : False := by
  have hwv : u * v * z ≠ v :=
    (mul_mul_ne_self_of_mem_centSet_of_not_mem hS.oddT hzD hu hv).2
  have hvc : Commute v (u * v * z) := (commute_self_mul_mul_of_mem_centSet hu hv hc).2
  let r : G := c * v * c⁻¹
  let s : G := c * (u * v * z) * c⁻¹
  have hrD : r ∈ D := by simpa only [r] using hS.conj_mem c hv.1
  have hsD : s ∈ D := by simpa only [s] using hS.conj_mem c huvz
  have hrne : r ≠ s := by
    intro heq
    apply hwv
    calc u * v * z = c⁻¹ * s * c := by simp only [s]; group
      _ = c⁻¹ * r * c := by rw [heq]
      _ = v := by simp only [r]; group
  have hcomm : Commute r s := by
    have h := hvc.conj c
    simpa only [r, s] using h
  have hzrs : z = r * s := by
    calc z = c * (v * (u * v * z)) * c⁻¹ := hz_eq
      _ = r * s := by simp only [r, s]; group
  exact ne_mul_of_transitive hS hu hv huv htrans hrD hsD hrne hcomm hzrs

theorem mul_mul_mem_of_isBenderGroup (hS : Setup G D) {z u v : G}
    (hu : u ∈ centSet D z) (hv : v ∈ centSet D z) (huv : u ≠ v)
    (htrans : ∀ x ∈ centSet D z, ∀ y ∈ centSet D z, ∃ h ∈ localGroup D z, h * x * h⁻¹ = y)
    (hR : CFSG.solvableRadical (localGroup D z) ≤ Subgroup.center (localGroup D z))
    (hZ2 : ∀ c ∈ Subgroup.center (localGroup D z), c * c = 1 → (c : G) = 1 ∨ (c : G) = z)
    (hB : CFSG.BenderSuzuki.IsBenderGroup
      (localGroup D z ⧸ CFSG.solvableRadical (localGroup D z)))
    (hH' : ∀ x : localGroup D z, (x : G) ∈ centSet D z → x ∉ commutator (localGroup D z)) :
    ∀ d ∈ centSet D z, ∀ e ∈ centSet D z, d ≠ e → Commute d e → d * e * z ∈ D := by
  intro d hd e he hde hcde
  set H := localGroup D z with hH
  have hdH : d ∈ H := mem_localGroup_of_mem hd
  have heH : e ∈ H := mem_localGroup_of_mem he
  let T : H := ⟨d * e, H.mul_mem hdH heH⟩
  have hTT : T * T = 1 := by
    apply Subtype.ext
    show d * e * (d * e) = 1
    calc d * e * (d * e) = d * (e * d) * e := by group
      _ = d * (d * e) * e := by rw [hcde.eq]
      _ = (d * d) * (e * e) := by group
      _ = 1 := by rw [hS.oddT.mul_self_eq_one hd.1, hS.oddT.mul_self_eq_one he.1, one_mul]
  have hTTG : d * e * (d * e) = 1 := by simpa using congrArg Subtype.val hTT
  rcases localGroup_involution_cases_of_isBenderGroup hS hu hv huv htrans hR hZ2 hB
    (t := d * e) T.2 hTTG with h1 | h1 | hC | hC
  · have hdeq : d = e := by
      have h : e = d⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [h, hS.oddT.inv_eq hd.1]
    exact absurd hdeq hde
  · exact absurd h1.symm (ne_mul_of_transitive hS hu hv huv htrans hd.1 he.1 hde hcde)
  · exfalso
    obtain ⟨k, hkH, hk⟩ := htrans e he d hd
    have hk' : (⟨k, hkH⟩ : H) * (⟨e, heH⟩ : H) * (⟨k, hkH⟩ : H)⁻¹ = ⟨d, hdH⟩ :=
      Subtype.ext hk
    have hmem := CFSG.GroupTheory.mul_mem_commutator_of_conj (H := H) hk'
      (Subtype.ext (hS.oddT.mul_self_eq_one he.1))
    exact (hH' T (by simpa using hC)) (by simpa [T] using hmem)
  · exact hC.1

theorem conj_eq_of_isBenderGroup (hS : Setup G D) {z u v : G}
    (hu : u ∈ centSet D z) (hv : v ∈ centSet D z) (huv : u ≠ v) (hc : Commute u v)
    (huvz : u * v * z ∈ D) (hzD : z ∉ D)
    (htrans : ∀ x ∈ centSet D z, ∀ y ∈ centSet D z,
      ∃ h ∈ localGroup D z, h * x * h⁻¹ = y)
    (hR : CFSG.solvableRadical (localGroup D z) ≤ Subgroup.center (localGroup D z))
    (hZ2 : ∀ c ∈ Subgroup.center (localGroup D z), c * c = 1 → (c : G) = 1 ∨ (c : G) = z)
    (hB : CFSG.BenderSuzuki.IsBenderGroup
      (localGroup D z ⧸ CFSG.solvableRadical (localGroup D z))) :
    ∀ g : G, g * z * g⁻¹ ∈ localGroup D z → g * z * g⁻¹ = z := by
  classical
  intro g hg
  have hz2 : z * z = 1 := mul_self_eq_one_of_mul_mul_mem hS.oddT hu hv hc huvz
  set H := localGroup D z with hH
  let T : H := ⟨g * z * g⁻¹, hg⟩
  have hTTG : g * z * g⁻¹ * (g * z * g⁻¹) = 1 := by
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hz2, mul_one, mul_inv_cancel]
  have hTT : T * T = 1 := Subtype.ext hTTG
  rcases localGroup_involution_cases_of_isBenderGroup hS hu hv huv htrans hR hZ2 hB
    (t := g * z * g⁻¹) hg hTTG with h1 | h1 | hC | hC
  · have hz1 : z = 1 := by
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    rw [hz1] at h1 ⊢
    exact h1
  · exact h1
  · exfalso
    apply hzD
    have h := hS.conj_mem g⁻¹ hC.1
    rwa [inv_inv, show g⁻¹ * (g * z * g⁻¹) * g = z by group] at h
  · exfalso
    obtain ⟨k, hkH, hk⟩ := htrans u hu (g * z * g⁻¹ * z) hC
    have hkz : Commute k z := commute_of_mem_localGroup hkH
    have hkT : g * z * g⁻¹ = k * (u * z) * k⁻¹ := by
      calc g * z * g⁻¹ = (g * z * g⁻¹) * (z * z) := by rw [hz2, mul_one]
        _ = ((g * z * g⁻¹) * z) * z := by group
        _ = (k * u * k⁻¹) * z := by rw [← hk]
        _ = k * (u * z) * k⁻¹ := by
          have h1 : k⁻¹ * z = z * k⁻¹ := hkz.inv_left.eq
          calc k * u * k⁻¹ * z = k * u * (k⁻¹ * z) := by rw [mul_assoc]
            _ = k * u * (z * k⁻¹) := by rw [h1]
            _ = k * (u * z) * k⁻¹ := by group
    have huz : u * z = v * (u * v * z) :=
      mul_eq_mul_mul_mul_of_mem_centSet hS.oddT hv hc
    refine false_of_eq_conj_mul_mul hS hu hv huv hc htrans huvz hzD (c := g⁻¹ * k) ?_
    calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = g⁻¹ * (k * (u * z) * k⁻¹) * g := by rw [hkT]
      _ = (g⁻¹ * k) * (v * (u * v * z)) * (g⁻¹ * k)⁻¹ := by rw [huz]; group

end CFSG.OddTranspositions.PartThree
