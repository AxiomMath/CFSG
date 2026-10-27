module

public import CFSG.GH74.GLS.C3.Layer1.Back112Iv2
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.GH74.GLS.C3.Layer1.BackBasic
public import CFSG.GroupTheory.ABGLocalTools.SylowNormalizerGrows
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3323C23
public import CFSG.RankThree.GF2n.Parrott.ActionV
public import CFSG.RankThree.GF2n.Parrott.Section1

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup
open CFSG.GH74.GLS.C3.Layer1.Back (mem_conjugate_iff' conjugate_mul' conjugate_inf'
  conjugate_centralizer_singleton isSylowOf_conjugate exists_mem_conjugate_le_of_isSylowOf
  card_conjugate' isPGroup_conjugate' isElementaryAbelian_of_forall
  forall_of_isElementaryAbelian isElementaryAbelian_conjugate)

variable {G : Type} [Group G] [Finite G] {z : G}

omit [Finite G] in
private theorem conj_z_eq_self_of_mem_H {c : G} (hc : c ∈ H z) : c * z * c⁻¹ = z :=
  Commute.mul_inv_cancel
    (Subgroup.mem_centralizer_singleton_iff.mp (show c ∈ Subgroup.centralizer ({z} : Set G) from hc))

omit [Finite G] in
private theorem eq_z_of_conj_eq_z_of_mem_H {c a : G} (hc : c ∈ H z) (h : c * a * c⁻¹ = z) :
    a = z := by
  calc a = c⁻¹ * (c * a * c⁻¹) * c := by group
    _ = c⁻¹ * z * c := by rw [h]
    _ = c⁻¹ * (c * z * c⁻¹) * c := by rw [conj_z_eq_self_of_mem_H hc]
    _ = z := by group

omit [Finite G] in
private theorem z_mul_self (h : Tim79a.ParrottHyp z) : z * z = 1 := by
  have := pow_orderOf_eq_one z
  rwa [h.1, pow_two] at this

omit [Finite G] in
private theorem z_inv (h : Tim79a.ParrottHyp z) : z⁻¹ = z :=
  inv_eq_iff_mul_eq_one.mpr (z_mul_self h)

omit [Finite G] in
private theorem eq_z_of_mem_J_of_isConj {T₂ : Subgroup G}
    (hJT : ∀ j ∈ J z, orderOf j = 2 → j ≠ z → ∃ c ∈ H z, c * j * c⁻¹ ∈ T₂)
    (hSup : ∀ x ∈ T₂, x ≠ z → ¬ IsConj z x) {j : G} (hjJ : j ∈ J z)
    (hjord : orderOf j = 2) (hjconj : IsConj z j) : j = z := by
  by_contra hjne
  obtain ⟨c, hcH, hcT⟩ := hJT j hjJ hjord hjne
  have hcne : c * j * c⁻¹ ≠ z := fun hz => hjne (eq_z_of_conj_eq_z_of_mem_H hcH hz)
  exact hSup (c * j * c⁻¹) hcT hcne (hjconj.trans (isConj_iff.mpr ⟨c, rfl⟩))

omit [Finite G] in
private theorem not_mem_T2_of_isConj {T₂ : Subgroup G}
    (hSup : ∀ x ∈ T₂, x ≠ z → ¬ IsConj z x) {y : G} (hyne : y ≠ z)
    (hyconj : IsConj z y) : ∀ c ∈ H z, c * y * c⁻¹ ∉ T₂ := by
  intro c hcH hcT
  have hcne : c * y * c⁻¹ ≠ z := fun hz => hyne (eq_z_of_conj_eq_z_of_mem_H hcH hz)
  exact hSup (c * y * c⁻¹) hcT hcne (hyconj.trans (isConj_iff.mpr ⟨c, rfl⟩))

private theorem exists_zstar_y (h : Tim79a.ParrottHyp z)
    (hHO : centralizer ({z} : Set G) ⊔ pPrimeCore 2 G ≠ ⊤) {T₂ : Subgroup G}
    (hSup : ∀ x ∈ T₂, x ≠ z → ¬ IsConj z x) :
    ∃ (y g : G), g * z * g⁻¹ = y ∧ y ∈ H z ∧ y ≠ z ∧ IsConj z y ∧
      ∀ c ∈ H z, c * y * c⁻¹ ∉ T₂ := by
  obtain ⟨y, ⟨g, hgy⟩, hyord, hyH, hynotzp⟩ := prop2_conj_centralizer h.1 hHO
  have hyne : y ≠ z := fun hz => hynotzp (hz ▸ Subgroup.mem_zpowers z)
  have hyconj : IsConj z y := isConj_iff.mpr ⟨g, hgy⟩
  have hnotT₂ : ∀ c ∈ H z, c * y * c⁻¹ ∉ T₂ := not_mem_T2_of_isConj hSup hyne hyconj
  exact ⟨y, g, hgy, hyH, hyne, hyconj, hnotT₂⟩

private theorem zstar_pair_y' (h : Tim79a.ParrottHyp z) {y g : G}
    (hgy : g * z * g⁻¹ = y) (hyH : y ∈ H z) (hyne : y ≠ z) :
    ∃ y' : G, g * y' * g⁻¹ = z ∧ y' ∈ H z ∧ y' ≠ z ∧ IsConj z y' ∧ orderOf y' = 2 := by
  let y' : G := g⁻¹ * z * g
  have hgy' : g * y' * g⁻¹ = z := by
    show g * (g⁻¹ * z * g) * g⁻¹ = z
    group
  have hy'H : y' ∈ H z := by
    rw [H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
    show y' * z = z * y'
    have hyz : y * z = z * y := Subgroup.mem_centralizer_singleton_iff.mp hyH
    have hyz' : (g * z * g⁻¹) * z = z * (g * z * g⁻¹) := by
      simpa only [← hgy] using hyz
    have h1 : z * y' = y' * z := by
      show z * (g⁻¹ * z * g) = (g⁻¹ * z * g) * z
      calc z * (g⁻¹ * z * g) = g⁻¹ * ((g * z * g⁻¹) * z) * g := by group
        _ = g⁻¹ * (z * (g * z * g⁻¹)) * g := by rw [hyz']
        _ = (g⁻¹ * z * g) * z := by group
    exact h1.symm
  have hy'ne : y' ≠ z := by
    intro hz
    apply hyne
    calc y = g * z * g⁻¹ := hgy.symm
      _ = g * y' * g⁻¹ := by rw [hz]
      _ = z := hgy'
  have hy'conj : IsConj z y' := by
    refine isConj_iff.mpr ⟨g⁻¹, ?_⟩
    show g⁻¹ * z * (g⁻¹)⁻¹ = y'
    rw [inv_inv]
  have hy'ord : orderOf y' = 2 := (IsConj.orderOf_eq hy'conj).symm.trans h.1
  exact ⟨y', hgy', hy'H, hy'ne, hy'conj, hy'ord⟩

private theorem sym_pair_B_le {y y' g : G} (hgy : g * z * g⁻¹ = y)
    (hy'rel : g * y' * g⁻¹ = z) :
    conjugate (J z ⊓ centralizer ({y'} : Set G)) g⁻¹ ≤
      H z ⊓ centralizer ({y} : Set G) := by
  have hy'eq : y' = g⁻¹ * z * g := by
    calc y' = g⁻¹ * (g * y' * g⁻¹) * g := by group
      _ = g⁻¹ * z * g := by rw [hy'rel]
  intro b hb
  have hbC : g⁻¹ * b * g ∈ J z ⊓ centralizer ({y'} : Set G) := by
    have h := mem_conjugate_iff'.mp hb
    simpa only [inv_inv] using h
  have hb_eq : b = g * (g⁻¹ * b * g) * g⁻¹ := by group
  have hdH : g⁻¹ * b * g ∈ H z := J_le_H hbC.1
  have hdz : (g⁻¹ * b * g) * z * (g⁻¹ * b * g)⁻¹ = z :=
    Commute.mul_inv_cancel
      (Subgroup.mem_centralizer_singleton_iff.mp (by rw [← H_eq_centralizer]; exact hdH))
  have hbz : b * z * b⁻¹ = z := by
    calc b * z * b⁻¹
        = g * ((g⁻¹ * b * g) * (g⁻¹ * z * g) * (g⁻¹ * b * g)⁻¹) * g⁻¹ := by
          rw [hb_eq]; group
      _ = g * (g⁻¹ * z * g) * g⁻¹ := by
          rw [show (g⁻¹ * b * g) * (g⁻¹ * z * g) * (g⁻¹ * b * g)⁻¹ = g⁻¹ * z * g by
            rw [← hy'eq]
            exact Commute.mul_inv_cancel
              (Subgroup.mem_centralizer_singleton_iff.mp hbC.2)]
      _ = z := by group
  have hbCz : b ∈ H z := by
    rw [H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
    calc b * z = (b * z * b⁻¹) * b := by group
      _ = z * b := by rw [hbz]
  have hgyz : g⁻¹ * y * g = z := by rw [← hgy]; group
  have hby : b * y * b⁻¹ = y := by
    calc b * y * b⁻¹
        = g * ((g⁻¹ * b * g) * (g⁻¹ * y * g) * (g⁻¹ * b * g)⁻¹) * g⁻¹ := by
          rw [hb_eq]; group
      _ = g * (g⁻¹ * y * g) * g⁻¹ := by
          rw [hgyz]
          exact congrArg (fun t => g * t * g⁻¹)
            (Commute.mul_inv_cancel
              (Subgroup.mem_centralizer_singleton_iff.mp (by rw [← H_eq_centralizer]; exact hdH)))
      _ = y := by group
  refine Subgroup.mem_inf.mpr ⟨hbCz, ?_⟩
  refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
  calc b * y = (b * y * b⁻¹) * b := by group
    _ = y * b := by rw [hby]

private theorem conj_mem_H_of_mem_H_of_mem_centralizer {c y g : G}
    (hcy : c * y * c⁻¹ = y) (hgy : g * z * g⁻¹ = y) :
    g⁻¹ * c * g ∈ H z := by
  rw [H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
  have h1 : (g⁻¹ * c * g) * z * (g⁻¹ * c * g)⁻¹ = z := by
    calc (g⁻¹ * c * g) * z * (g⁻¹ * c * g)⁻¹
        = g⁻¹ * (c * (g * z * g⁻¹) * c⁻¹) * g := by group
      _ = g⁻¹ * (c * y * c⁻¹) * g := by rw [hgy]
      _ = g⁻¹ * y * g := by rw [hcy]
      _ = z := by rw [← hgy]; group
  calc (g⁻¹ * c * g) * z
      = ((g⁻¹ * c * g) * z * (g⁻¹ * c * g)⁻¹) * (g⁻¹ * c * g) := by group
    _ = z * (g⁻¹ * c * g) := by rw [h1]

private theorem conj_mem_centralizer_y' {c y' g : G} (hcH : c ∈ H z)
    (hgy' : g * y' * g⁻¹ = z) :
    g⁻¹ * c * g ∈ Subgroup.centralizer ({y'} : Set G) := by
  have hy'eq : y' = g⁻¹ * z * g := by
    calc y' = g⁻¹ * (g * y' * g⁻¹) * g := by group
      _ = g⁻¹ * z * g := by rw [hgy']
  have hcz : c * z * c⁻¹ = z :=
    Commute.mul_inv_cancel
      (Subgroup.mem_centralizer_singleton_iff.mp (by rw [← H_eq_centralizer]; exact hcH))
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 : (g⁻¹ * c * g) * y' * (g⁻¹ * c * g)⁻¹ = y' := by
    calc (g⁻¹ * c * g) * y' * (g⁻¹ * c * g)⁻¹
        = g⁻¹ * (c * z * c⁻¹) * g := by
          rw [hy'eq]
          group
      _ = g⁻¹ * z * g := by rw [hcz]
      _ = y' := hy'eq.symm
  calc (g⁻¹ * c * g) * y'
      = ((g⁻¹ * c * g) * y' * (g⁻¹ * c * g)⁻¹) * (g⁻¹ * c * g) := by group
    _ = y' * (g⁻¹ * c * g) := by rw [h1]

private theorem sym_pair_B_normal {y y' g : G} (hgy : g * z * g⁻¹ = y)
    (hy'rel : g * y' * g⁻¹ = z) :
    ∀ c ∈ H z ⊓ centralizer ({y} : Set G),
      ∀ b ∈ conjugate (J z ⊓ centralizer ({y'} : Set G)) g⁻¹,
      c * b * c⁻¹ ∈ conjugate (J z ⊓ centralizer ({y'} : Set G)) g⁻¹ := by
  intro c hc b hb
  have hcH : c ∈ H z := hc.1
  have hcCy : c ∈ Subgroup.centralizer ({y} : Set G) := hc.2
  have hcy : c * y * c⁻¹ = y :=
    Commute.mul_inv_cancel (Subgroup.mem_centralizer_singleton_iff.mp hcCy)
  have hbC : g⁻¹ * b * g ∈ J z ⊓ centralizer ({y'} : Set G) := by
    have h := mem_conjugate_iff'.mp hb
    simpa only [inv_inv] using h
  have hdH := conj_mem_H_of_mem_H_of_mem_centralizer hcy hgy
  have hdCy' := conj_mem_centralizer_y' hcH hy'rel
  have hdeJ : (g⁻¹ * c * g) * (g⁻¹ * b * g) * (g⁻¹ * c * g)⁻¹ ∈ J z := by
    have hHN : H z ≤ Subgroup.normalizer (J z : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (J_le_H (z := z))).mp
        (J_subgroupOf_normal z)
    exact (Subgroup.mem_normalizer_iff.mp (hHN hdH) (g⁻¹ * b * g)).mp hbC.1
  have hdeCy' : (g⁻¹ * c * g) * (g⁻¹ * b * g) * (g⁻¹ * c * g)⁻¹ ∈
      Subgroup.centralizer ({y'} : Set G) := by
    have hdy : Commute (g⁻¹ * c * g) y' :=
      Subgroup.mem_centralizer_singleton_iff.mp hdCy'
    have hey : Commute (g⁻¹ * b * g) y' :=
      Subgroup.mem_centralizer_singleton_iff.mp hbC.2
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (show ((g⁻¹ * c * g) * (g⁻¹ * b * g) * (g⁻¹ * c * g)⁻¹) * y' =
        y' * ((g⁻¹ * c * g) * (g⁻¹ * b * g) * (g⁻¹ * c * g)⁻¹) from
        ((hdy.mul_left hey).mul_left hdy.inv_left).eq)
  refine mem_conjugate_iff'.mpr ?_
  have heq : (g⁻¹) * (c * b * c⁻¹) * (g⁻¹)⁻¹ =
      (g⁻¹ * c * g) * (g⁻¹ * b * g) * (g⁻¹ * c * g)⁻¹ := by
    rw [inv_inv]; group
  rw [heq]
  exact ⟨hdeJ, hdeCy'⟩

private theorem sym_pair_B_mem (h : Tim79a.ParrottHyp z) {T₂ : Subgroup G}
    (hJT : ∀ j ∈ J z, orderOf j = 2 → j ≠ z → ∃ c ∈ H z, c * j * c⁻¹ ∈ T₂)
    (hSup : ∀ x ∈ T₂, x ≠ z → ¬ IsConj z x) {y y' g : G}
    (hgy : g * z * g⁻¹ = y) (hgy' : g * y' * g⁻¹ = z)
    (hy'H : y' ∈ H z) (hy'ne : y' ≠ z)
    (hy'ord : orderOf y' = 2) (hy'conj : IsConj z y') :
    y ∈ conjugate (J z ⊓ centralizer ({y'} : Set G)) g⁻¹ ∧
      z ∉ conjugate (J z ⊓ centralizer ({y'} : Set G)) g⁻¹ := by
  have hy'eq : y' = g⁻¹ * z * g := by
    calc y' = g⁻¹ * (g * y' * g⁻¹) * g := by group
      _ = g⁻¹ * z * g := by rw [hgy']
  have hzC : z ∈ J z ⊓ centralizer ({y'} : Set G) := by
    refine ⟨z_mem_J h, ?_⟩
    have hy'z : y' * z = z * y' := Subgroup.mem_centralizer_singleton_iff.mp hy'H
    exact Subgroup.mem_centralizer_singleton_iff.mpr hy'z.symm
  have hyB : y ∈ conjugate (J z ⊓ centralizer ({y'} : Set G)) g⁻¹ := by
    refine mem_conjugate_iff'.mpr ?_
    have h : (g⁻¹) * y * (g⁻¹)⁻¹ = z := by rw [inv_inv, ← hgy]; group
    rw [h]
    exact hzC
  have hzB : z ∉ conjugate (J z ⊓ centralizer ({y'} : Set G)) g⁻¹ := by
    intro hzB
    have hy'C : y' ∈ J z ⊓ centralizer ({y'} : Set G) := by
      have h := mem_conjugate_iff'.mp hzB
      simpa only [inv_inv, ← hy'eq] using h
    exact hy'ne (eq_z_of_mem_J_of_isConj hJT hSup hy'C.1 hy'ord hy'conj)
  exact ⟨hyB, hzB⟩

private theorem sym_pair_final_contradiction (h : Tim79a.ParrottHyp z) {T₂ : Subgroup G}
    (hJT : ∀ j ∈ J z, orderOf j = 2 → j ≠ z → ∃ c ∈ H z, c * j * c⁻¹ ∈ T₂)
    (hSup : ∀ x ∈ T₂, x ≠ z → ¬ IsConj z x) {y y' g : G}
    (hgy : g * z * g⁻¹ = y) (hyconj : IsConj z y) (hgy' : g * y' * g⁻¹ = z)
    (hy'H : y' ∈ H z) (hy'ne : y' ≠ z)
    (hy'ord : orderOf y' = 2) (hy'conj : IsConj z y')
    (hle : Nat.card ↥(J z ⊓ centralizer ({y} : Set G)) ≤
      Nat.card ↥(J z ⊓ centralizer ({y'} : Set G)))
    (hbadB : ∀ B : Subgroup G, B ≤ H z ⊓ centralizer ({y} : Set G) →
      (∀ c ∈ H z ⊓ centralizer ({y} : Set G), ∀ b ∈ B, c * b * c⁻¹ ∈ B) →
      IsPGroup 2 B → y ∈ B → z ∉ B →
      Nat.card ↥(J z ⊓ centralizer ({y} : Set G)) ≤ Nat.card B →
      ∃ c ∈ H z, c * y * c⁻¹ ∈ B ∧ c * y * c⁻¹ ≠ y) : False := by
  let B : Subgroup G := conjugate (J z ⊓ centralizer ({y'} : Set G)) g⁻¹
  have hB_le : B ≤ H z ⊓ centralizer ({y} : Set G) := sym_pair_B_le hgy hgy'
  have hBnorm := sym_pair_B_normal hgy hgy'
  have hB2 : IsPGroup 2 B := isPGroup_conjugate' (isPGroup_J h).to_inf_left g⁻¹
  obtain ⟨hyB, hzB⟩ := sym_pair_B_mem h hJT hSup hgy hgy' hy'H hy'ne hy'ord hy'conj
  have hBbig : Nat.card ↥(J z ⊓ centralizer ({y} : Set G)) ≤ Nat.card B := by
    rw [card_conjugate']
    exact hle
  obtain ⟨c, hcH, hcB, hcne⟩ := hbadB B hB_le hBnorm hB2 hyB hzB hBbig
  have hjC : g⁻¹ * (c * y * c⁻¹) * g ∈ J z ⊓ centralizer ({y'} : Set G) := by
    have h := mem_conjugate_iff'.mp hcB
    simpa only [inv_inv] using h
  have hjconj : IsConj z (g⁻¹ * (c * y * c⁻¹) * g) := by
    have h1 : IsConj (c * y * c⁻¹) (g⁻¹ * (c * y * c⁻¹) * g) := by
      refine isConj_iff.mpr ⟨g⁻¹, ?_⟩
      group
    exact (hyconj.trans (isConj_iff.mpr ⟨c, rfl⟩)).trans h1
  have hjne : g⁻¹ * (c * y * c⁻¹) * g ≠ z := by
    intro hz
    apply hcne
    have h : g * (g⁻¹ * (c * y * c⁻¹) * g) * g⁻¹ = c * y * c⁻¹ := by group
    calc c * y * c⁻¹ = g * (g⁻¹ * (c * y * c⁻¹) * g) * g⁻¹ := h.symm
      _ = g * z * g⁻¹ := by rw [hz]
      _ = y := hgy
  exact hjne (eq_z_of_mem_J_of_isConj hJT hSup hjC.1
    ((IsConj.orderOf_eq hjconj).symm.trans h.1) hjconj)

theorem exists_mem_T2_isConj_z (h : Tim79a.ParrottHyp z)
    (hHO : centralizer ({z} : Set G) ⊔ pPrimeCore 2 G ≠ ⊤) {T₂ : Subgroup G}
    (hJT : ∀ j ∈ J z, orderOf j = 2 → j ≠ z → ∃ c ∈ H z, c * j * c⁻¹ ∈ T₂)
    (hbad : ∀ y ∈ H z, orderOf y = 2 → y ≠ z → (∀ c ∈ H z, c * y * c⁻¹ ∉ T₂) →
      ∀ B : Subgroup G, B ≤ H z ⊓ centralizer ({y} : Set G) →
        (∀ c ∈ H z ⊓ centralizer ({y} : Set G), ∀ b ∈ B, c * b * c⁻¹ ∈ B) →
        IsPGroup 2 B → y ∈ B → z ∉ B →
        Nat.card ↥(J z ⊓ centralizer ({y} : Set G)) ≤ Nat.card B →
        ∃ c ∈ H z, c * y * c⁻¹ ∈ B ∧ c * y * c⁻¹ ≠ y) :
    ∃ x ∈ T₂, x ≠ z ∧ IsConj z x := by
  by_contra hcon
  have hSup : ∀ x ∈ T₂, x ≠ z → ¬ IsConj z x := fun x hxT hxne hxconj =>
    hcon ⟨x, hxT, hxne, hxconj⟩
  obtain ⟨y, g, hgy, hyH, hyne, hyconj, hnotT₂⟩ := exists_zstar_y h hHO hSup
  have hyord : orderOf y = 2 := (IsConj.orderOf_eq hyconj).symm.trans h.1
  obtain ⟨y', hgy', hy'H, hy'ne, hy'conj, hy'ord⟩ := zstar_pair_y' h hgy hyH hyne
  have hnotT₂' : ∀ c ∈ H z, c * y' * c⁻¹ ∉ T₂ := not_mem_T2_of_isConj hSup hy'ne hy'conj
  rcases le_total (Nat.card ↥(J z ⊓ centralizer ({y} : Set G)))
      (Nat.card ↥(J z ⊓ centralizer ({y'} : Set G))) with hle | hle
  · exact sym_pair_final_contradiction h hJT hSup hgy hyconj hgy' hy'H hy'ne hy'ord hy'conj hle
      (hbad y hyH hyord hyne hnotT₂)
  · have hg'y' : g⁻¹ * z * g⁻¹⁻¹ = y' := by rw [← hgy']; group
    have hg'y : g⁻¹ * y * g⁻¹⁻¹ = z := by rw [← hgy]; group
    exact sym_pair_final_contradiction h hJT hSup hg'y' hy'conj hg'y hyH hyne hyord hyconj hle
      (hbad y' hy'H hy'ord hy'ne hnotT₂')

omit [Finite G] in
private theorem z_ne_one (h : Tim79a.ParrottHyp z) : z ≠ 1 := by
  rintro rfl
  have h2 : orderOf (1 : G) = 2 := h.1
  rw [orderOf_one] at h2
  norm_num at h2

omit [Finite G] in
private theorem not_isConj_z_of_conj_mem_W {σ : G} {W : Subgroup G} {a : G}
    (hSup2 : ∀ w ∈ W, w ≠ z → ¬ IsConj z w)
    (hconjW : ∃ c ∈ H z ⊓ centralizer ({σ} : Set G), c * a * c⁻¹ ∈ W)
    (hne : a ≠ z) : ¬ IsConj z a := by
  intro haconj
  obtain ⟨b, hbY, hbW⟩ := hconjW
  have hbH : b ∈ H z := hbY.1
  have hbne : b * a * b⁻¹ ≠ z := fun hz => hne (eq_z_of_conj_eq_z_of_mem_H hbH hz)
  exact hSup2 (b * a * b⁻¹) hbW hbne (haconj.trans (isConj_iff.mpr ⟨b, rfl⟩))

private theorem exists_sylow_K (h : Tim79a.ParrottHyp z) {σ x : G}
    (hP4 : ∀ t ∈ H z ⊓ centralizer ({σ} : Set G), orderOf t = 2 → IsConj z t →
      ∃ c ∈ centralizer ({σ} : Set G), c * t * c⁻¹ = z)
    (hxY : x ∈ H z ⊓ centralizer ({σ} : Set G)) (hzx : IsConj z x) :
    ∃ K : Subgroup G,
      IsSylowOf 2 K (H z ⊓ centralizer ({σ} : Set G) ⊓ centralizer ({x} : Set G)) ∧
      z ∈ K ∧ z ∈ Subgroup.centralizer (K : Set G) := by
  have hx2 : orderOf x = 2 := (IsConj.orderOf_eq hzx).symm.trans h.1
  obtain ⟨c, hcCσ, hcx⟩ := hP4 x hxY hx2 hzx
  have hzCσ : z ∈ centralizer ({σ} : Set G) := by
    have hcσ' : Commute c σ := Subgroup.mem_centralizer_singleton_iff.mp hcCσ
    have hxσ' : Commute x σ := Subgroup.mem_centralizer_singleton_iff.mp hxY.2
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (show z * σ = σ * z from by
        rw [← hcx]
        exact ((hcσ'.mul_left hxσ').mul_left hcσ'.inv_left).eq)
  have hzCx : z ∈ centralizer ({x} : Set G) := by
    have hxz' : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.mp hxY.1
    exact Subgroup.mem_centralizer_singleton_iff.mpr hxz'.symm
  let Yx : Subgroup G := H z ⊓ centralizer ({σ} : Set G) ⊓ centralizer ({x} : Set G)
  have hzYx : z ∈ Yx := ⟨⟨z_mem_H, hzCσ⟩, hzCx⟩
  obtain ⟨K, hK⟩ := exists_isSylowOf 2 Yx
  have hzCK : z ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hkH : k ∈ H z := (hK.le hk).1.1
    exact Subgroup.mem_centralizer_singleton_iff.mp hkH
  have hzK : z ∈ K := by
    have hzp : IsPGroup 2 (Subgroup.zpowers z) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.1]; norm_num)
    have hzNK : z ∈ Subgroup.normalizer (K : Set G) :=
      Subgroup.centralizer_le_normalizer (K : Set G) hzCK
    have hsupP : IsPGroup 2 ↥(K ⊔ Subgroup.zpowers z) :=
      IsPGroup.to_sup_of_normal_left' hK.isPGroup hzp (Subgroup.zpowers_le.mpr hzNK)
    have hsupLe : K ⊔ Subgroup.zpowers z ≤ Yx :=
      sup_le hK.le (Subgroup.zpowers_le.mpr hzYx)
    have heq : K ⊔ Subgroup.zpowers z = K := hK.eq_of_le le_sup_left hsupLe hsupP
    exact heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  exact ⟨K, by simpa only [Yx] using hK, hzK, hzCK⟩

omit [Finite G] in
private theorem mem_pair_of_Ktype_cover {x a : G} {K : Subgroup G} (hzx : IsConj z x)
    (hcover : ∀ e ∈ centerIn K, e = 1 ∨ e = z ∨ e = a ∨ e = a * z ∨
      ∃ c ∈ H z, c * x * c⁻¹ = e) :
    ∀ e ∈ centerIn K, e ≠ 1 → e ≠ z → ¬ IsConj z e → e = a ∨ e = a * z := by
  intro e he he1 hez heconj
  rcases hcover e he with h1 | h1 | h1 | h1 | ⟨b, hbH, hbe⟩
  · exact absurd h1 he1
  · exact absurd h1 hez
  · exact Or.inl h1
  · exact Or.inr h1
  · exact absurd (by rw [← hbe]; exact hzx.trans (isConj_iff.mpr ⟨b, rfl⟩)) heconj

omit [Finite G] in
private theorem conj_central_mem_pair {n e a b : G} {K : Subgroup G}
    (hnZ : n ∈ Subgroup.normalizer (centerIn K : Set G)) (heK : e ∈ centerIn K)
    (he1 : e ≠ 1) (he_nc : ¬ IsConj z e)
    (hcases : ∀ f ∈ centerIn K, f ≠ 1 → f ≠ z → ¬ IsConj z f → f = a ∨ f = b) :
    n * e * n⁻¹ = a ∨ n * e * n⁻¹ = b := by
  have he_center : n * e * n⁻¹ ∈ centerIn K :=
    (Subgroup.mem_normalizer_iff.mp hnZ e).mp heK
  exact hcases (n * e * n⁻¹) he_center
    (by
      intro heq
      apply he1
      calc e = n⁻¹ * (n * e * n⁻¹) * n := by group
        _ = 1 := by rw [heq]; group)
    (by
      intro heq
      apply he_nc
      refine isConj_iff.mpr ⟨n⁻¹, ?_⟩
      rw [inv_inv, ← heq]
      group)
    (by
      intro hconj
      apply he_nc
      exact hconj.trans (isConj_iff.mpr ⟨n⁻¹, by group⟩))

omit [Finite G] in
private theorem conj_z_eq_z_of_pair (h : Tim79a.ParrottHyp z) {n a : G}
    (hna : n * a * n⁻¹ = a ∨ n * a * n⁻¹ = a * z)
    (hnaz : n * (a * z) * n⁻¹ = a ∨ n * (a * z) * n⁻¹ = a * z)
    (hdist : n * a * n⁻¹ ≠ n * (a * z) * n⁻¹) : n * z * n⁻¹ = z := by
  have hkey : n * z * n⁻¹ = (n * a * n⁻¹)⁻¹ * (n * (a * z) * n⁻¹) := by group
  rcases hna with h1 | h1 <;> rcases hnaz with h2 | h2
  · exact absurd (by rw [h1, h2]) hdist
  · calc n * z * n⁻¹ = (n * a * n⁻¹)⁻¹ * (n * (a * z) * n⁻¹) := hkey
      _ = a⁻¹ * (a * z) := by rw [h1, h2]
      _ = z := by group
  · calc n * z * n⁻¹ = (n * a * n⁻¹)⁻¹ * (n * (a * z) * n⁻¹) := hkey
      _ = (a * z)⁻¹ * a := by rw [h1, h2]
      _ = z⁻¹ := by group
      _ = z := z_inv h
  · exact absurd (by rw [h1, h2]) hdist

private theorem normalizer_inf_le_H_of_Ktype (h : Tim79a.ParrottHyp z) {σ x : G}
    {K W : Subgroup G} (hzK : z ∈ K) (hzCK : z ∈ Subgroup.centralizer (K : Set G))
    {a : G} (haK : a ∈ centerIn K) (ha1 : a ≠ 1) (haz : a ≠ z)
    (hainW : ∃ c ∈ H z ⊓ centralizer ({σ} : Set G), c * a * c⁻¹ ∈ W)
    (hazinW : ∃ c ∈ H z ⊓ centralizer ({σ} : Set G), c * (a * z) * c⁻¹ ∈ W)
    (hcover : ∀ e ∈ centerIn K, e = 1 ∨ e = z ∨ e = a ∨ e = a * z ∨
      ∃ c ∈ H z, c * x * c⁻¹ = e)
    (hSup2 : ∀ w ∈ W, w ≠ z → ¬ IsConj z w) (hzx : IsConj z x) :
    normalizer (K : Set G) ⊓
      (centralizer ({σ} : Set G) ⊓ centralizer ({x} : Set G)) ≤ H z := by
  intro n hn
  have hnNorm : n ∈ normalizer (K : Set G) := hn.1
  have hnZ : n ∈ Subgroup.normalizer (centerIn K : Set G) := by
    simpa [CFSG.centerIn, CFSG.Quasithin.centerOf] using
      (CFSG.Quasithin.H13.C23.mem_normalizer_centerOf hnNorm)
  have hazK : a * z ∈ centerIn K :=
    ⟨K.mul_mem haK.1 hzK, Subgroup.mul_mem _ haK.2 hzCK⟩
  have ha_nc := not_isConj_z_of_conj_mem_W hSup2 hainW haz
  have haz_ne : a * z ≠ z := by
    intro hz
    apply ha1
    calc a = (a * z) * z := by rw [mul_assoc, z_mul_self h, mul_one]
      _ = z * z := by rw [hz]
      _ = 1 := z_mul_self h
  have haz_nc := not_isConj_z_of_conj_mem_W hSup2 hazinW haz_ne
  have hcover' := mem_pair_of_Ktype_cover hzx hcover
  have haz1 : a * z ≠ 1 := by
    intro hz
    apply haz
    calc a = (a * z) * z := by rw [mul_assoc, z_mul_self h, mul_one]
      _ = 1 * z := by rw [hz]
      _ = z := one_mul z
  have hna := conj_central_mem_pair hnZ haK ha1 ha_nc hcover'
  have hnaz := conj_central_mem_pair hnZ hazK haz1 haz_nc hcover'
  have hdist : n * a * n⁻¹ ≠ n * (a * z) * n⁻¹ := by
    intro heq
    apply z_ne_one h
    have haz_eq : a = a * z := by
      calc a = n⁻¹ * (n * a * n⁻¹) * n := by group
        _ = n⁻¹ * (n * (a * z) * n⁻¹) * n := by rw [heq]
        _ = a * z := by group
    have h1 : a⁻¹ * a = a⁻¹ * (a * z) := congrArg (fun t => a⁻¹ * t) haz_eq
    have h2 : (1 : G) = z := by
      calc (1 : G) = a⁻¹ * a := (inv_mul_cancel a).symm
        _ = a⁻¹ * (a * z) := h1
        _ = z := by group
    exact h2.symm
  have hnz := conj_z_eq_z_of_pair h hna hnaz hdist
  rw [H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
  calc n * z = (n * z * n⁻¹) * n := by group
    _ = z * n := by rw [hnz]

omit [Finite G] in
private theorem closure_squares_le_centralizer {σ : G} {K : Subgroup G}
    (hKσ : K ≤ centralizer ({σ} : Set G)) :
    Subgroup.closure ((fun k => k * k) '' (K : Set G)) ≤
      centralizer ({σ} : Set G) := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro y ⟨k, hkK, rfl⟩
  exact Subgroup.mul_mem _ (hKσ hkK) (hKσ hkK)

omit [Finite G] in
private theorem mem_normalizer_closure_squares {n : G} {K : Subgroup G}
    (hnNorm : n ∈ Subgroup.normalizer (K : Set G)) :
    n ∈ Subgroup.normalizer
      (Subgroup.closure ((fun k => k * k) '' (K : Set G)) : Set G) := by
  have hS : (MulAut.conj n).toMonoidHom '' ((fun k => k * k) '' (K : Set G)) =
      (fun k => k * k) '' (K : Set G) := by
    ext y
    constructor
    · rintro ⟨w, ⟨k, hkK, rfl⟩, rfl⟩
      refine ⟨n * k * n⁻¹, (Subgroup.mem_normalizer_iff.mp hnNorm k).mp hkK, ?_⟩
      change (n * k * n⁻¹) * (n * k * n⁻¹) = MulAut.conj n (k * k)
      rw [MulAut.conj_apply]
      group
    · rintro ⟨k, hkK, rfl⟩
      refine ⟨n⁻¹ * (k * k) * n, ⟨n⁻¹ * k * n, ?_, ?_⟩, ?_⟩
      · simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hnNorm) k).mp hkK
      · group
      · change MulAut.conj n (n⁻¹ * (k * k) * n) = k * k
        rw [MulAut.conj_apply]
        group
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_closure]
  exact congrArg Subgroup.closure hS

private theorem normalizer_inf_le_H_of_Ltype (h : Tim79a.ParrottHyp z) {σ x : G}
    {K W : Subgroup G}
    (hKle : K ≤ H z ⊓ centralizer ({σ} : Set G) ⊓ centralizer ({x} : Set G))
    (hzM : z ∈ Subgroup.closure ((fun k => k * k) '' (K : Set G)))
    (hMJ : Subgroup.closure ((fun k => k * k) '' (K : Set G)) ≤ J z)
    (hJY : ∀ j ∈ J z ⊓ centralizer ({σ} : Set G), orderOf j = 2 → j ≠ z →
      ∃ c ∈ H z ⊓ centralizer ({σ} : Set G), c * j * c⁻¹ ∈ W)
    (hSup2 : ∀ w ∈ W, w ≠ z → ¬ IsConj z w) :
    normalizer (K : Set G) ⊓
      (centralizer ({σ} : Set G) ⊓ centralizer ({x} : Set G)) ≤ H z := by
  intro n hn
  have hnNorm : n ∈ normalizer (K : Set G) := hn.1
  have hnCσ : n ∈ centralizer ({σ} : Set G) := hn.2.1
  have hMCσ := closure_squares_le_centralizer (fun k hk => (hKle hk).1.2)
  have hzCσ : z ∈ centralizer ({σ} : Set G) := hMCσ hzM
  have hnM := mem_normalizer_closure_squares hnNorm
  have hnzM := (Subgroup.mem_normalizer_iff.mp hnM z).mp hzM
  have hnzJ : n * z * n⁻¹ ∈ J z := hMJ hnzM
  have hnzCσ : n * z * n⁻¹ ∈ centralizer ({σ} : Set G) := by
    have hnσ : Commute n σ := Subgroup.mem_centralizer_singleton_iff.mp hnCσ
    have hzσ : Commute z σ := Subgroup.mem_centralizer_singleton_iff.mp hzCσ
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      ((hnσ.mul_left hzσ).mul_left hnσ.inv_left).eq
  have hnz2 : orderOf (n * z * n⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, h.1]
  by_cases hnz_eq : n * z * n⁻¹ = z
  · rw [H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
    calc n * z = (n * z * n⁻¹) * n := by group
      _ = z * n := by rw [hnz_eq]
  · exfalso
    obtain ⟨b, hbY, hbW⟩ := hJY (n * z * n⁻¹) ⟨hnzJ, hnzCσ⟩ hnz2 hnz_eq
    have hbH : b ∈ H z := hbY.1
    have hbne : b * (n * z * n⁻¹) * b⁻¹ ≠ z :=
      fun hz => hnz_eq (eq_z_of_conj_eq_z_of_mem_H hbH hz)
    exact hSup2 (b * (n * z * n⁻¹) * b⁻¹) hbW hbne
      ((isConj_iff.mpr ⟨n, rfl⟩).trans (isConj_iff.mpr ⟨b, rfl⟩))

private theorem sylow_card_contradiction (h : Tim79a.ParrottHyp z) {σ x : G}
    {T₂ K : Subgroup G}
    (hP4 : ∀ t ∈ H z ⊓ centralizer ({σ} : Set G), orderOf t = 2 → IsConj z t →
      ∃ c ∈ centralizer ({σ} : Set G), c * t * c⁻¹ = z)
    (hT₂ : IsSylowOf 2 T₂ (H z ⊓ centralizer ({σ} : Set G)))
    (hT₂c : Nat.card T₂ = 2 ^ 8)
    (hK : IsSylowOf 2 K (H z ⊓ centralizer ({σ} : Set G) ⊓ centralizer ({x} : Set G)))
    (hNle : normalizer (K : Set G) ⊓
      (centralizer ({σ} : Set G) ⊓ centralizer ({x} : Set G)) ≤ H z)
    (hKcard : Nat.card K < 2 ^ 8) (hzx : IsConj z x)
    (hxY : x ∈ H z ⊓ centralizer ({σ} : Set G)) : False := by
  have hx2 : orderOf x = 2 := (IsConj.orderOf_eq hzx).symm.trans h.1
  obtain ⟨c, hcCσ, hcx⟩ := hP4 x hxY hx2 hzx
  have hcσ : c * σ * c⁻¹ = σ :=
    Commute.mul_inv_cancel (Subgroup.mem_centralizer_singleton_iff.mp hcCσ)
  have hT : IsSylowOf 2 K
      (H z ⊓ (centralizer ({σ} : Set G) ⊓ centralizer ({x} : Set G))) := by
    simpa only [inf_assoc] using hK
  have hKtop : IsSylowOf 2 K (centralizer ({σ} : Set G) ⊓ centralizer ({x} : Set G)) :=
    isSylowOf_of_normalizer_inf_le hT hNle
  have hconjY : conjugate (centralizer ({σ} : Set G) ⊓ centralizer ({x} : Set G)) c⁻¹ =
      H z ⊓ centralizer ({σ} : Set G) := by
    rw [conjugate_inf', conjugate_centralizer_singleton, conjugate_centralizer_singleton]
    rw [show (c⁻¹)⁻¹ * σ * c⁻¹ = σ from by rw [inv_inv, hcσ],
      show (c⁻¹)⁻¹ * x * c⁻¹ = z from by rw [inv_inv, hcx]]
    rw [H_eq_centralizer, inf_comm]
  have hKconj : IsSylowOf 2 (conjugate K c⁻¹) (H z ⊓ centralizer ({σ} : Set G)) := by
    have := isSylowOf_conjugate hKtop c⁻¹
    rwa [hconjY] at this
  have hfac : 2 ^ (Nat.card ↥(H z ⊓ centralizer ({σ} : Set G))).factorization 2 = 2 ^ 8 := by
    have h := hT₂.card_eq
    rw [hT₂c] at h
    exact h.symm
  have hcardConj : Nat.card (conjugate K c⁻¹) = 2 ^ 8 := by
    rw [hKconj.card_eq, hfac]
  have hcardK : Nat.card K = 2 ^ 8 := by
    rw [← card_conjugate' K c⁻¹]
    exact hcardConj
  omega

theorem exists_mem_W_isConj_z (h : Tim79a.ParrottHyp z) {σ : G} {T₂ W : Subgroup G}
    (hP4 : ∀ t ∈ H z ⊓ centralizer ({σ} : Set G), orderOf t = 2 → IsConj z t →
      ∃ c ∈ centralizer ({σ} : Set G), c * t * c⁻¹ = z)
    (hT₂ : IsSylowOf 2 T₂ (H z ⊓ centralizer ({σ} : Set G))) (hT₂c : Nat.card T₂ = 2 ^ 8)
    (hJY : ∀ j ∈ J z ⊓ centralizer ({σ} : Set G), orderOf j = 2 → j ≠ z →
      ∃ c ∈ H z ⊓ centralizer ({σ} : Set G), c * j * c⁻¹ ∈ W)
    (hKL : ∀ x ∈ H z ⊓ centralizer ({σ} : Set G), orderOf x = 2 →
      (∀ c ∈ H z ⊓ centralizer ({σ} : Set G), c * x * c⁻¹ ∉ W) →
      ∀ K : Subgroup G,
        IsSylowOf 2 K (H z ⊓ centralizer ({σ} : Set G) ⊓ centralizer ({x} : Set G)) →
        Nat.card K < 2 ^ 8 ∧
        ((∃ a ∈ centerIn K, a ≠ 1 ∧ a ≠ z ∧
            (∃ c ∈ H z ⊓ centralizer ({σ} : Set G), c * a * c⁻¹ ∈ W) ∧
            (∃ c ∈ H z ⊓ centralizer ({σ} : Set G), c * (a * z) * c⁻¹ ∈ W) ∧
            ∀ e ∈ centerIn K, e = 1 ∨ e = z ∨ e = a ∨ e = a * z ∨ ∃ c ∈ H z, c * x * c⁻¹ = e) ∨
          (z ∈ Subgroup.closure ((fun k => k * k) '' (K : Set G)) ∧
            Subgroup.closure ((fun k => k * k) '' (K : Set G)) ≤ J z)))
    {x : G} (hxY : x ∈ H z ⊓ centralizer ({σ} : Set G)) (hxz : x ≠ z) (hzx : IsConj z x) :
    ∃ w ∈ W, w ≠ z ∧ IsConj z w := by
  by_contra hcon
  have hSup2 : ∀ w ∈ W, w ≠ z → ¬ IsConj z w := fun w hwW hwne hwconj =>
    hcon ⟨w, hwW, hwne, hwconj⟩
  have hx2 : orderOf x = 2 := (IsConj.orderOf_eq hzx).symm.trans h.1
  have hnotW : ∀ c ∈ H z ⊓ centralizer ({σ} : Set G), c * x * c⁻¹ ∉ W := by
    intro c hcY hcW
    have hcH : c ∈ H z := hcY.1
    have hcne : c * x * c⁻¹ ≠ z := fun hz => hxz (eq_z_of_conj_eq_z_of_mem_H hcH hz)
    exact hSup2 (c * x * c⁻¹) hcW hcne (hzx.trans (isConj_iff.mpr ⟨c, rfl⟩))
  obtain ⟨K, hK, hzK, hzCK⟩ := exists_sylow_K h hP4 hxY hzx
  obtain ⟨hKcard, hKtype⟩ := hKL x hxY hx2 hnotW K hK
  have hNle : normalizer (K : Set G) ⊓
      (centralizer ({σ} : Set G) ⊓ centralizer ({x} : Set G)) ≤ H z := by
    rcases hKtype with ⟨a, haK, ha1, haz, hainW, hazinW, hcover⟩ | ⟨hzM, hMJ⟩
    · exact normalizer_inf_le_H_of_Ktype h hzK hzCK haK ha1 haz hainW hazinW hcover hSup2 hzx
    · exact normalizer_inf_le_H_of_Ltype h hK.le hzM hMJ hJY hSup2
  exact sylow_card_contradiction h hP4 hT₂ hT₂c hK hNle hKcard hzx hxY

private theorem conj_W_le_Y {σ : G} {T₂ W : Subgroup G} {c w : G}
    (hT₂ : IsSylowOf 2 T₂ (H z ⊓ centralizer ({σ} : Set G)))
    (hWT : W ≤ T₂) (hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a)
    (hcw : c * w * c⁻¹ = z) (hcCσ : c ∈ centralizer ({σ} : Set G)) (hwW : w ∈ W) :
    conjugate W c⁻¹ ≤ H z ⊓ centralizer ({σ} : Set G) := by
  have hcw' : c⁻¹ * z * c = w := by
    calc c⁻¹ * z * c = c⁻¹ * (c * w * c⁻¹) * c := by rw [hcw]
      _ = w := by group
  intro x hx
  have hxW : c⁻¹ * x * c ∈ W := by
    simpa using (mem_conjugate_iff'.mp hx : (c⁻¹) * x * (c⁻¹)⁻¹ ∈ W)
  obtain ⟨b, hbW, hxeq⟩ : ∃ b ∈ W, x = MulAut.conj c b := by
    refine ⟨c⁻¹ * x * c, hxW, ?_⟩
    rw [MulAut.conj_apply]
    group
  have hbY : b ∈ H z ⊓ centralizer ({σ} : Set G) := hT₂.le (hWT hbW)
  have hbw : b * w = w * b := hWab b hbW w hwW
  have hxeq' : x = c * b * c⁻¹ := by
    simpa only [MulAut.conj_apply] using hxeq
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
    have hxz : x * z * x⁻¹ = z := by
      calc x * z * x⁻¹ = c * (b * (c⁻¹ * z * c) * b⁻¹) * c⁻¹ := by
            rw [hxeq']; group
        _ = c * (b * w * b⁻¹) * c⁻¹ := by rw [hcw']
        _ = c * w * c⁻¹ := by rw [show b * w * b⁻¹ = w by rw [hbw, mul_inv_cancel_right]]
        _ = z := hcw
    calc x * z = (x * z * x⁻¹) * x := by group
      _ = z * x := by rw [hxz]
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have hcσ' : c * σ * c⁻¹ = σ :=
      Commute.mul_inv_cancel (Subgroup.mem_centralizer_singleton_iff.mp hcCσ)
    have hcσ'' : c⁻¹ * σ * c = σ := by
      calc c⁻¹ * σ * c = c⁻¹ * (c * σ * c⁻¹) * c := by rw [hcσ']
        _ = σ := by group
    have hbσ' : b * σ * b⁻¹ = σ :=
      Commute.mul_inv_cancel (Subgroup.mem_centralizer_singleton_iff.mp hbY.2)
    have hxσ : x * σ * x⁻¹ = σ := by
      calc x * σ * x⁻¹ = c * (b * (c⁻¹ * σ * c) * b⁻¹) * c⁻¹ := by
            rw [hxeq']; group
        _ = c * (b * σ * b⁻¹) * c⁻¹ := by rw [hcσ'']
        _ = c * σ * c⁻¹ := by rw [hbσ']
        _ = σ := hcσ'
    calc x * σ = (x * σ * x⁻¹) * x := by group
      _ = σ * x := by rw [hxσ]

private theorem exists_conj_W_eq_W {σ : G} {T₂ W : Subgroup G} {c : G}
    (hT₂ : IsSylowOf 2 T₂ (H z ⊓ centralizer ({σ} : Set G)))
    (hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (hW2 : ∀ a ∈ W, a * a = 1)
    (hWc : Nat.card W = 32)
    (hWu : ∀ E : Subgroup G, E ≤ T₂ → (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) →
      (∀ a ∈ E, a * a = 1) → Nat.card E = 32 → E = W)
    (hW'Y : conjugate W c⁻¹ ≤ H z ⊓ centralizer ({σ} : Set G))
    (hW'p : IsPGroup 2 (conjugate W c⁻¹)) :
    ∃ d ∈ H z ⊓ centralizer ({σ} : Set G), conjugate (conjugate W c⁻¹) d = W := by
  obtain ⟨d, hdY, hdW'⟩ := exists_mem_conjugate_le_of_isSylowOf hT₂ hW'Y hW'p
  refine ⟨d, hdY, ?_⟩
  set W'' : Subgroup G := conjugate (conjugate W c⁻¹) d with hW''def
  have hW''T : W'' ≤ T₂ := hdW'
  have hW''form : W'' = conjugate W (c⁻¹ * d) := (conjugate_mul' W c⁻¹ d).symm
  have hWea : CFSG.IsElementaryAbelian 2 ↥W := isElementaryAbelian_of_forall hWab hW2
  have hW''ea : CFSG.IsElementaryAbelian 2 ↥W'' := by
    rw [hW''form]
    exact isElementaryAbelian_conjugate hWea (c⁻¹ * d)
  obtain ⟨hW''ab, hW''2⟩ := forall_of_isElementaryAbelian hW''ea
  have hW''c : Nat.card W'' = 32 := by
    rw [hW''form, card_conjugate', hWc]
  exact hWu W'' hW''T hW''ab hW''2 hW''c

private theorem exists_normalizer_conj_of_W {σ : G} {W : Subgroup G} {c d w : G}
    (hcCσ : c ∈ centralizer ({σ} : Set G))
    (hdY : d ∈ H z ⊓ centralizer ({σ} : Set G))
    (hcw : c * w * c⁻¹ = z)
    (hW''eq : conjugate (conjugate W c⁻¹) d = W) :
    ∃ n ∈ normalizer (W : Set G) ⊓ centralizer ({σ} : Set G), n * z * n⁻¹ = w := by
  have hcw' : c⁻¹ * z * c = w := by
    calc c⁻¹ * z * c = c⁻¹ * (c * w * c⁻¹) * c := by rw [hcw]
      _ = w := by group
  have hW''form : conjugate (conjugate W c⁻¹) d = conjugate W (c⁻¹ * d) :=
    (conjugate_mul' W c⁻¹ d).symm
  have hWeq : W = conjugate W (c⁻¹ * d) := hW''eq.symm.trans hW''form
  have hmNorm : c⁻¹ * d ∈ Subgroup.normalizer (W : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 : x ∈ W ↔ x ∈ conjugate W (c⁻¹ * d) := by
      conv_lhs => rw [hWeq]
    exact h1.trans (mem_conjugate_iff' (H := W) (g := c⁻¹ * d) (x := x))
  have hmCσ : c⁻¹ * d ∈ centralizer ({σ} : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hcCσ) hdY.2
  have hdz : d * z * d⁻¹ = z :=
    Commute.mul_inv_cancel
      (Subgroup.mem_centralizer_singleton_iff.mp (by rw [← H_eq_centralizer]; exact hdY.1))
  have hmz : (c⁻¹ * d) * z * (c⁻¹ * d)⁻¹ = w := by
    calc (c⁻¹ * d) * z * (c⁻¹ * d)⁻¹ = c⁻¹ * (d * z * d⁻¹) * c := by group
      _ = c⁻¹ * z * c := by rw [hdz]
      _ = w := hcw'
  exact ⟨c⁻¹ * d, Subgroup.mem_inf.mpr ⟨hmNorm, hmCσ⟩, hmz⟩

theorem exists_normalizer_conj_of_mem_W (h : Tim79a.ParrottHyp z) {σ : G} {T₂ W : Subgroup G}
    (hP4 : ∀ t ∈ H z ⊓ centralizer ({σ} : Set G), orderOf t = 2 → IsConj z t →
      ∃ c ∈ centralizer ({σ} : Set G), c * t * c⁻¹ = z)
    (hT₂ : IsSylowOf 2 T₂ (H z ⊓ centralizer ({σ} : Set G)))
    (hWT : W ≤ T₂) (hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (hW2 : ∀ a ∈ W, a * a = 1)
    (hWc : Nat.card W = 32)
    (hWu : ∀ E : Subgroup G, E ≤ T₂ → (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) →
      (∀ a ∈ E, a * a = 1) → Nat.card E = 32 → E = W)
    {w : G} (hwW : w ∈ W) (hzw : IsConj z w) :
    ∃ n ∈ normalizer (W : Set G) ⊓ centralizer ({σ} : Set G), n * z * n⁻¹ = w := by
  have hw2 : orderOf w = 2 := (IsConj.orderOf_eq hzw).symm.trans h.1
  have hwY : w ∈ H z ⊓ centralizer ({σ} : Set G) := hT₂.le (hWT hwW)
  obtain ⟨c, hcCσ, hcw⟩ := hP4 w hwY hw2 hzw
  have hWp : IsPGroup 2 W := IsPGroup.of_card (n := 5) (by rw [hWc]; norm_num)
  have hW'Y : conjugate W c⁻¹ ≤ H z ⊓ centralizer ({σ} : Set G) :=
    conj_W_le_Y hT₂ hWT hWab hcw hcCσ hwW
  have hW'p : IsPGroup 2 (conjugate W c⁻¹) := isPGroup_conjugate' hWp c⁻¹
  obtain ⟨d, hdY, hW''eq⟩ :=
    exists_conj_W_eq_W hT₂ hWab hW2 hWc hWu hW'Y hW'p
  exact exists_normalizer_conj_of_W hcCσ hdY hcw hW''eq

theorem exists_mem_normalizer_not_mem_H (h : Tim79a.ParrottHyp z)
    (hHO : centralizer ({z} : Set G) ⊔ pPrimeCore 2 G ≠ ⊤) {σ : G} {T₂ W : Subgroup G}
    (hP4 : ∀ t ∈ H z ⊓ centralizer ({σ} : Set G), orderOf t = 2 → IsConj z t →
      ∃ c ∈ centralizer ({σ} : Set G), c * t * c⁻¹ = z)
    (hT₂ : IsSylowOf 2 T₂ (H z ⊓ centralizer ({σ} : Set G))) (hT₂c : Nat.card T₂ = 2 ^ 8)
    (hJT : ∀ j ∈ J z, orderOf j = 2 → j ≠ z → ∃ c ∈ H z, c * j * c⁻¹ ∈ T₂)
    (hbad : ∀ y ∈ H z, orderOf y = 2 → y ≠ z → (∀ c ∈ H z, c * y * c⁻¹ ∉ T₂) →
      ∀ B : Subgroup G, B ≤ H z ⊓ centralizer ({y} : Set G) →
        (∀ c ∈ H z ⊓ centralizer ({y} : Set G), ∀ b ∈ B, c * b * c⁻¹ ∈ B) →
        IsPGroup 2 B → y ∈ B → z ∉ B →
        Nat.card ↥(J z ⊓ centralizer ({y} : Set G)) ≤ Nat.card B →
        ∃ c ∈ H z, c * y * c⁻¹ ∈ B ∧ c * y * c⁻¹ ≠ y)
    (hWT : W ≤ T₂) (hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (hW2 : ∀ a ∈ W, a * a = 1)
    (hWc : Nat.card W = 32)
    (hWu : ∀ E : Subgroup G, E ≤ T₂ → (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) →
      (∀ a ∈ E, a * a = 1) → Nat.card E = 32 → E = W)
    (hJY : ∀ j ∈ J z ⊓ centralizer ({σ} : Set G), orderOf j = 2 → j ≠ z →
      ∃ c ∈ H z ⊓ centralizer ({σ} : Set G), c * j * c⁻¹ ∈ W)
    (hKL : ∀ x ∈ H z ⊓ centralizer ({σ} : Set G), orderOf x = 2 →
      (∀ c ∈ H z ⊓ centralizer ({σ} : Set G), c * x * c⁻¹ ∉ W) →
      ∀ K : Subgroup G,
        IsSylowOf 2 K (H z ⊓ centralizer ({σ} : Set G) ⊓ centralizer ({x} : Set G)) →
        Nat.card K < 2 ^ 8 ∧
        ((∃ a ∈ centerIn K, a ≠ 1 ∧ a ≠ z ∧
            (∃ c ∈ H z ⊓ centralizer ({σ} : Set G), c * a * c⁻¹ ∈ W) ∧
            (∃ c ∈ H z ⊓ centralizer ({σ} : Set G), c * (a * z) * c⁻¹ ∈ W) ∧
            ∀ e ∈ centerIn K, e = 1 ∨ e = z ∨ e = a ∨ e = a * z ∨ ∃ c ∈ H z, c * x * c⁻¹ = e) ∨
          (z ∈ Subgroup.closure ((fun k => k * k) '' (K : Set G)) ∧
            Subgroup.closure ((fun k => k * k) '' (K : Set G)) ≤ J z))) :
    ∃ n ∈ normalizer (W : Set G) ⊓ centralizer ({σ} : Set G), n ∉ H z := by
  obtain ⟨x, hxT, hxne, hxconj⟩ := exists_mem_T2_isConj_z h hHO hJT hbad
  have hxY : x ∈ H z ⊓ centralizer ({σ} : Set G) := hT₂.le hxT
  obtain ⟨w, hwW, hwne, hzw⟩ :=
    exists_mem_W_isConj_z h hP4 hT₂ hT₂c hJY hKL hxY hxne hxconj
  obtain ⟨n, hn, hnz⟩ :=
    exists_normalizer_conj_of_mem_W h hP4 hT₂ hWT hWab hW2 hWc hWu hwW hzw
  refine ⟨n, hn, ?_⟩
  intro hnH
  exact hwne (by rw [← hnz, conj_z_eq_self_of_mem_H hnH])

end CFSG.RankThree.GF2n.Parrott
