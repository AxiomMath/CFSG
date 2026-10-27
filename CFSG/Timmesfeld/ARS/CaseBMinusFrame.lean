module

public import CFSG.Timmesfeld.ARS.CaseBQuad
public import CFSG.Timmesfeld.ARS.CaseBSpFrame
public import CFSG.Timmesfeld.RankTwo.LevisBMinusFrame

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement Pointwise
open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.Timmesfeld.RankTwo Matrix
open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.Assembly.LowTwoRank CFSG.Blueprint

namespace CaseB

variable {G : Type} [Group G] {R : Set (Subgroup G)} {F : Type} [Field F]
  {Ψ : SpecialLinearGroup (Fin 4) F →* G}

theorem starCoord_neg_eq_planeRefl [CharP F 2] {b c : F} (t : ShortField b c) :
    starCoord (-t) = planeRefl b c planeOne (fieldCoord t) := by
  have hn : ∀ x : F, -x = x := CharTwo.neg_eq
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  ext k
  fin_cases k
  · simp only [starCoord, fieldCoord, planeRefl, polarPlane, planeNorm, planeOne,
      QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg]
    simp [hn, h2, CharTwo.sub_eq_add]
  · simp only [starCoord, fieldCoord, planeRefl, polarPlane, planeNorm, planeOne,
      QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg]
    simp [hn]

variable (Ψ) in
noncomputable abbrev ψU' [CharP F 2] (ι : (Fin 2 → F) → G) (p : Fin 2 → F) : G :=
  piT Ψ * ι p * (piT Ψ)⁻¹

variable (Ψ) in
noncomputable abbrev ψN [CharP F 2] (ι : (Fin 2 → F) → G) (p : Fin 2 → F) : G :=
  pi13 Ψ * ι p * (pi13 Ψ)⁻¹

variable (Ψ) in
noncomputable abbrev ψN' [CharP F 2] (ι : (Fin 2 → F) → G) (p : Fin 2 → F) : G :=
  pi13 Ψ * ψU' Ψ ι p * (pi13 Ψ)⁻¹

variable (Ψ) in
@[expose] noncomputable def mL : Fin 12 → F → G :=
  ![xs Ψ ne21, xs Ψ ne12, xs Ψ ne13, xs Ψ ne31, fun _ => 1, fun _ => 1, xs Ψ ne23, xs Ψ ne32,
    fun _ => 1, fun _ => 1, xs Ψ ne02, xs Ψ ne20]

variable (Ψ) in
@[expose] noncomputable def mS [CharP F 2] (ι : (Fin 2 → F) → G) : Fin 12 → (Fin 2 → F) → G :=
  ![fun _ => 1, fun _ => 1, fun _ => 1, fun _ => 1, ι, ψU' Ψ ι, fun _ => 1, fun _ => 1, ψN Ψ ι,
    ψN' Ψ ι, fun _ => 1, fun _ => 1]

variable (Ψ) in
@[expose] noncomputable def wE [CharP F 2] (b c : F) [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)]
    (ι : (Fin 2 → F) → G) : G :=
  ι (fieldCoord (1 : ShortField b c)) * yE Ψ ι (-(1 : ShortField b c)⁻¹) *
    ι (fieldCoord (1 : ShortField b c))

variable (Ψ) in
@[expose] noncomputable def mW02 [CharP F 2] (b c : F) [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)]
    (ι : (Fin 2 → F) → G) : Fin 3 → G :=
  ![pi12 Ψ, 1, wE Ψ b c ι]

omit [Field F] in
theorem conj_conj_of_mul_self {w : G} (hw : w * w = 1) (x : G) : w * (w * x * w⁻¹) * w⁻¹ = x := by
  calc w * (w * x * w⁻¹) * w⁻¹ = (w * w) * x * (w * w)⁻¹ := by group
    _ = x := by rw [hw, inv_one, one_mul, mul_one]

section Frame

variable [CharP F 2] [Finite F] (h : Hyp G R) (hS : Skel R Ψ) (hP : PtHyp R Ψ) {b c : F}
  [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)] {ι : (Fin 2 → F) → G} (hι : LinParamU R Ψ 2 ι)
  (hQ : ∀ p, Qc R Ψ (ι p) = planeNorm b c p)

section Centralizers

include h hS

omit [Finite F] in
theorem pi12_conj_of_mem {u : G} (hu : u ∈ hU R Ψ ∨ u ∈ hU R (perm Ψ σT)) :
    pi12 Ψ * u * (pi12 Ψ)⁻¹ = u := by
  have hmem := pm_swap_mem_sup (Ψ := Ψ) ne12
  have hST := hS.perm σT
  have h1 : ∀ x ∈ xg Ψ 1 2, Commute x u := fun x hx => by
    rcases hu with hu | hu
    · exact (commuting_hU h hS ne12 (by decide) u hu x hx).symm
    · have hc := commuting_hU h hST (a := 0) (b := 3) ne03 (by decide) u hu
      rw [xg_perm] at hc
      exact (hc x hx).symm
  have h2 : ∀ x ∈ xg Ψ 2 1, Commute x u := fun x hx => by
    rcases hu with hu | hu
    · exact (commuting_hU h hS ne21 (by decide) u hu x hx).symm
    · have hc := commuting_hU h hST (a := 3) (b := 0) ne30 (by decide) u hu
      rw [xg_perm] at hc
      exact (hc x hx).symm
  have hle : xg Ψ 1 2 ⊔ xg Ψ 2 1 ≤ Subgroup.centralizer {u} :=
    sup_le (fun x hx => Subgroup.mem_centralizer_singleton_iff.2 (h1 x hx).eq)
      (fun x hx => Subgroup.mem_centralizer_singleton_iff.2 (h2 x hx).eq)
  rw [Subgroup.mem_centralizer_singleton_iff.1 (hle hmem)]
  group

omit [Finite F] in
theorem pmT₀_conj_of_mem {u : G} (hu : u ∈ hU R (perm Ψ σT)) :
    Ψ (pm σT₀) * u * (Ψ (pm σT₀))⁻¹ = u := by
  have hST := hS.perm σT
  have hc : ∀ {a b : Fin 4} (hab : a ≠ b), (a = 0 ∨ a = 3 ∨ b = 1 ∨ b = 2) →
      Commuting (hU R (perm Ψ σT)) (xg Ψ (σT a) (σT b)) := fun {a b} hab hcond => by
    rw [← xg_perm]
    exact commuting_hU h hST hab hcond
  have hle : xg Ψ 0 3 ⊔ xg Ψ 3 0 ⊔ (xg Ψ 1 2 ⊔ xg Ψ 2 1) ≤ Subgroup.centralizer {u} := by
    refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_) <;> intro x hx <;>
      rw [Subgroup.mem_centralizer_singleton_iff]
    · exact (hc (a := 1) (b := 2) (by decide) (by decide) _ hu x hx).symm.eq
    · exact (hc (a := 2) (b := 1) (by decide) (by decide) _ hu x hx).symm.eq
    · exact (hc (a := 0) (b := 3) (by decide) (by decide) _ hu x hx).symm.eq
    · exact (hc (a := 3) (b := 0) (by decide) (by decide) _ hu x hx).symm.eq
  have hmem : Ψ (pm σT₀) ∈ xg Ψ 0 3 ⊔ xg Ψ 3 0 ⊔ (xg Ψ 1 2 ⊔ xg Ψ 2 1) := by
    rw [← pm_mul, map_mul]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (pm_swap_mem_sup ne03))
      (Subgroup.mem_sup_right (pm_swap_mem_sup ne12))
  rw [Subgroup.mem_centralizer_singleton_iff.1 (hle hmem)]
  group

omit [Finite F] in
theorem piT_conj_pi13_conj {u : G} (hu : u ∈ hU R (perm Ψ σT)) :
    piT Ψ * (pi13 Ψ * u * (pi13 Ψ)⁻¹) * (piT Ψ)⁻¹ = pi13 Ψ * u * (pi13 Ψ)⁻¹ := by
  have e : piT Ψ * pi13 Ψ = pi13 Ψ * Ψ (pm σT₀) := by
    rw [← map_mul, ← map_mul, pm_mul, pm_mul]
    congr 2
    decide
  calc piT Ψ * (pi13 Ψ * u * (pi13 Ψ)⁻¹) * (piT Ψ)⁻¹ =
      (piT Ψ * pi13 Ψ) * u * (piT Ψ * pi13 Ψ)⁻¹ := by group
    _ = pi13 Ψ * (Ψ (pm σT₀) * u * (Ψ (pm σT₀))⁻¹) * (pi13 Ψ)⁻¹ := by
        rw [e]
        group
    _ = pi13 Ψ * u * (pi13 Ψ)⁻¹ := by rw [pmT₀_conj_of_mem h hS hu]

end Centralizers

include h hS hP hι hQ

omit [Finite F] in
theorem wE_conj_ι (p : Fin 2 → F) :
    wE Ψ b c ι * ι p * (wE Ψ b c ι)⁻¹ = ψU' Ψ ι (planeRefl b c planeOne p) ∧
      wE Ψ b c ι * ψU' Ψ ι p * (wE Ψ b c ι)⁻¹ = ι (planeRefl b c planeOne p) := by
  have hone : (1 : ShortField b c) ≠ 0 := one_ne_zero
  have key : ∀ q : Fin 2 → F,
      wE Ψ b c ι * ι q * (wE Ψ b c ι)⁻¹ = ψU' Ψ ι (planeRefl b c planeOne q) := by
    intro q
    obtain ⟨t, rfl⟩ := exists_fieldCoord_eq (b := b) (c := c) q
    have e := rankOneE_conj h hS hP hι hQ hone t
    rw [show -((1 : ShortField b c) ^ 2)⁻¹ * t = -t by rw [one_pow, inv_one, neg_one_mul]] at e
    rw [wE, e, yE, starCoord_neg_eq_planeRefl]
  have hinv : (wE Ψ b c ι)⁻¹ = wE Ψ b c ι := by
    rw [wE, _root_.mul_inv_rev, _root_.mul_inv_rev, inv_eq_of_mul_eq_one_left (xE_mul_self hι _),
      inv_eq_of_mul_eq_one_left (yE_mul_self hι _)]
    group
  refine ⟨key p, ?_⟩
  have hr := planeRefl_planeRefl (b := b) (c := c) (a := planeOne) planeNorm_planeOne_ne_zero p
  have e := key (planeRefl b c planeOne p)
  rw [hr] at e
  rw [← e]
  calc wE Ψ b c ι * (wE Ψ b c ι * ι (planeRefl b c planeOne p) * (wE Ψ b c ι)⁻¹) *
        (wE Ψ b c ι)⁻¹ =
      (wE Ψ b c ι * wE Ψ b c ι) * ι (planeRefl b c planeOne p) *
        ((wE Ψ b c ι)⁻¹ * (wE Ψ b c ι)⁻¹) := by group
    _ = ι (planeRefl b c planeOne p) := by
      rw [show wE Ψ b c ι * wE Ψ b c ι = 1 by
        nth_rw 2 [← hinv]
        exact mul_inv_cancel _, hinv, show wE Ψ b c ι * wE Ψ b c ι = 1 by
        nth_rw 2 [← hinv]
        exact mul_inv_cancel _]
      group

omit [Finite F] hP hQ in
theorem wE_conj_xs (s : F) :
    wE Ψ b c ι * xs Ψ ne21 s * (wE Ψ b c ι)⁻¹ = xs Ψ ne21 s ∧
      wE Ψ b c ι * xs Ψ ne12 s * (wE Ψ b c ι)⁻¹ = xs Ψ ne12 s := by
  have hST := hS.perm σT
  have hcU : ∀ {u : G}, u ∈ hU R Ψ → Commute u (xs Ψ ne21 s) ∧ Commute u (xs Ψ ne12 s) :=
    fun hu => ⟨commuting_hU h hS ne21 (by decide) _ hu _ (xs_mem _ _),
      commuting_hU h hS ne12 (by decide) _ hu _ (xs_mem _ _)⟩
  have hcU' : ∀ {u : G}, u ∈ hU R (perm Ψ σT) →
      Commute u (xs Ψ ne21 s) ∧ Commute u (xs Ψ ne12 s) := by
    intro u hu
    have h1 := commuting_hU h hST (a := 3) (b := 0) ne30 (by decide) _ hu
    have h2 := commuting_hU h hST (a := 0) (b := 3) ne03 (by decide) _ hu
    rw [xg_perm] at h1 h2
    exact ⟨h1 _ (xs_mem _ _), h2 _ (xs_mem _ _)⟩
  have hx := hcU (hι.mem (fieldCoord (1 : ShortField b c)))
  have hy := hcU' (yE_mem h hι (-(1 : ShortField b c)⁻¹))
  have key : ∀ y : G, Commute (ι (fieldCoord (1 : ShortField b c))) y →
      Commute (yE Ψ ι (-(1 : ShortField b c)⁻¹)) y → wE Ψ b c ι * y * (wE Ψ b c ι)⁻¹ = y := by
    intro y h1 h2
    rw [wE, ((h1.mul_left h2).mul_left h1).eq]
    group
  exact ⟨key _ hx.1 hy.1, key _ hx.2 hy.2⟩

omit [Finite F] hS hP hQ in
theorem exists_ψU'_eq {u : G} (hu : u ∈ hU R (perm Ψ σT)) : ∃ p, ψU' Ψ ι p = u := by
  rw [hU_perm_T' h] at hu
  obtain ⟨v, hv, rfl⟩ := hu
  obtain ⟨p, rfl⟩ := hι.surj v hv
  exact ⟨p, rfl⟩

theorem isB3Frame (hB : HypB G R (xg Ψ 0 3)) :
    IsB3Frame (b := b) (c := c) (mL Ψ) (mS Ψ ι) (spW01 Ψ) (spW12 Ψ) (mW02 Ψ b c ι) where
  addL0 := xs_add ne21
  addL2 := xs_add ne13
  addL6 := xs_add ne23
  addL10 := xs_add ne02
  addS4 := hι.add
  addS8 p q := by
    change pi13 Ψ * ι (p + q) * (pi13 Ψ)⁻¹ =
      (pi13 Ψ * ι p * (pi13 Ψ)⁻¹) * (pi13 Ψ * ι q * (pi13 Ψ)⁻¹)
    rw [hι.add]
    group
  comm_0_2 s t := by
    change ⁅xs Ψ ne21 s, xs Ψ ne13 t⁆ = xs Ψ ne23 (s * t)
    rw [xs, xs, xs, ← map_commutatorElement, SpecialLinearGroup.commutatorElement_transvection]
  commute_0_6 s t :=
    commuting_xg (Ψ := Ψ) ne21 ne23 (by decide) (by decide) _ (xs_mem _ _) _ (xs_mem _ _)
  commute_6_2 s t :=
    commuting_xg (Ψ := Ψ) ne23 ne13 (by decide) (by decide) _ (xs_mem _ _) _ (xs_mem _ _)
  comm_4_2 p s := by
    change ⁅ι p, xs Ψ ne13 s⁆ = (pi13 Ψ * ι (s • p) * (pi13 Ψ)⁻¹) * xs Ψ ne02 (s * planeNorm b c p)
    have e := hι.commutator_xs13 h hS s p
    rw [hQ, Lc_eq_conj_pm13 h hS (hι.mem _)] at e
    have hN : pi13 Ψ * ι (s • p) * (pi13 Ψ)⁻¹ ∈ hid R Ψ := by
      rw [← conjSub_hU_pm13 h hS]
      exact conj_mem_conjSub _ (hι.mem _)
    have hNN := mul_self_of_mem_hid h hS hN
    have hCC : xs Ψ ne02 (s * planeNorm b c p) * xs Ψ ne02 (s * planeNorm b c p) = 1 := by
      rw [← xs_add, CharTwo.add_self_eq_zero, xs_zero]
    rw [← commutatorElement_inv, e, _root_.mul_inv_rev, inv_eq_of_mul_eq_one_left hNN,
      inv_eq_of_mul_eq_one_left hCC]
  comm_4_8 p q := by
    change ⁅ι p, pi13 Ψ * ι q * (pi13 Ψ)⁻¹⁆ = xs Ψ ne02 (polarPlane b c p q)
    rw [← Lc_eq_conj_pm13 h hS (hι.mem q), ← (hι.xs_βU h hS p q).1, βU_eq_polarPlane hQ]
  commute_4_10 p s := commute_of_mem_hU_of_mem_02 h hS (hι.mem p) (xs_mem _ _)
  commute_8_10 p s := by
    have hN : pi13 Ψ * ι p * (pi13 Ψ)⁻¹ ∈ hid R Ψ := by
      rw [← conjSub_hU_pm13 h hS]
      exact conj_mem_conjSub _ (hι.mem _)
    exact commuting_hid_02 h hS _ hN _ (xs_mem _ _)
  commute_8_2 p s := by
    have hN : pi13 Ψ * ι p * (pi13 Ψ)⁻¹ ∈ hid R Ψ := by
      rw [← conjSub_hU_pm13 h hS]
      exact conj_mem_conjSub _ (hι.mem _)
    exact commuting_hid_13 h hS _ hN _ (xs_mem _ _)
  commute_10_2 s t := (commute_13_02 t s).symm
  commute_0_4 s p := (commuting_hU h hS ne21 (by decide) _ (hι.mem p) _ (xs_mem _ _)).symm
  w01_0_0 x := pm_conj_xs (Equiv.swap 1 2) ne21 x
  w01_0_1 x := pm_conj_xs (Equiv.swap 1 2) ne12 x
  w01_0_2 x := pm_conj_xs (Equiv.swap 1 2) ne13 x
  w01_0_3 x := pm_conj_xs (Equiv.swap 1 2) ne31 x
  w01_0_6 x := pm_conj_xs (Equiv.swap 1 2) ne23 x
  w01_0_7 x := pm_conj_xs (Equiv.swap 1 2) ne32 x
  w01_1_0 x := pm_conj_xs (Equiv.swap 1 3) ne21 x
  w01_1_1 x := pm_conj_xs (Equiv.swap 1 3) ne12 x
  w01_1_2 x := pm_conj_xs (Equiv.swap 1 3) ne13 x
  w01_1_3 x := pm_conj_xs (Equiv.swap 1 3) ne31 x
  w01_1_6 x := pm_conj_xs (Equiv.swap 1 3) ne23 x
  w01_1_7 x := pm_conj_xs (Equiv.swap 1 3) ne32 x
  w12_1_2 x := pm_conj_xs (Equiv.swap 1 3) ne13 x
  w12_1_3 x := pm_conj_xs (Equiv.swap 1 3) ne31 x
  w12_1_4 p := rfl
  w12_1_5 p := rfl
  w12_1_8 p := conj_conj_of_mul_self pm13_mul_self (ι p)
  w12_1_9 p := conj_conj_of_mul_self pm13_mul_self (ψU' Ψ ι p)
  w12_1_10 x := pm_conj_xs (Equiv.swap 1 3) ne02 x
  w12_1_11 x := pm_conj_xs (Equiv.swap 1 3) ne20 x
  w12_2_2 x := piT_conj_xs13 x
  w12_2_3 x := piT_conj_xs ne31 x
  w12_2_4 p := rfl
  w12_2_5 p := conj_conj_of_mul_self piT_mul_self (ι p)
  w12_2_8 p := by
    have hN : pi13 Ψ * ι p * (pi13 Ψ)⁻¹ ∈ hid R Ψ := by
      rw [← conjSub_hU_pm13 h hS]
      exact conj_mem_conjSub _ (hι.mem _)
    exact piT_conj_hid h hS hN
  w12_2_9 p := by
    have hu : ψU' Ψ ι p ∈ hU R (perm Ψ σT) := by
      rw [hU_perm_T' h]
      exact conj_mem_conjSub _ (hι.mem _)
    exact piT_conj_pi13_conj h hS hu
  w12_2_10 x := piT_conj_xs02 x
  w12_2_11 x := piT_conj_xs ne20 x
  w02_0_0 x := pm_conj_xs (Equiv.swap 1 2) ne21 x
  w02_0_1 x := pm_conj_xs (Equiv.swap 1 2) ne12 x
  w02_0_4 p := pi12_conj_of_mem h hS (.inl (hι.mem p))
  w02_0_5 p := by
    have hu : ψU' Ψ ι p ∈ hU R (perm Ψ σT) := by
      rw [hU_perm_T' h]
      exact conj_mem_conjSub _ (hι.mem _)
    exact pi12_conj_of_mem h hS (.inr hu)
  w02_2_0 x := (wE_conj_xs h hS hι x).1
  w02_2_1 x := (wE_conj_xs h hS hι x).2
  w02_2_4 p := (wE_conj_ι h hS hP hι hQ p).1
  w02_2_5 p := (wE_conj_ι h hS hP hι hQ p).2
  rank0 := ⟨blk Ψ ne21, fun c => by rw [← LevisExtras.tv01_eq_sl2Upper]; exact blk_tv01 ne21 c,
    fun c => by rw [← LevisExtras.tv10_eq_sl2Lower]; exact blk_tv10 ne21 c⟩
  rank1 := ⟨blk Ψ ne13, fun c => by rw [← LevisExtras.tv01_eq_sl2Upper]; exact blk_tv01 ne13 c,
    fun c => by rw [← LevisExtras.tv10_eq_sl2Lower]; exact blk_tv10 ne13 c⟩
  rank2 := exists_hom_SL2_xE h hS hP hι hQ
  gen := by
    rw [eq_top_iff, ← fundSub_eq_top h hS hB]
    set S := Set.range (mL Ψ 0) ∪ Set.range (mL Ψ 1) ∪ Set.range (mL Ψ 2) ∪
      Set.range (mL Ψ 3) ∪ Set.range (mS Ψ ι 4) ∪ Set.range (mS Ψ ι 5) with hSdef
    have hxg : ∀ {a b' : Fin 4} (hab : a ≠ b') (i : Fin 12), i.val < 4 →
        (∀ c', mL Ψ i c' = xs Ψ hab c') → xg Ψ a b' ≤ Subgroup.closure S := by
      intro a b' hab i hi hc x hx
      obtain ⟨c', rfl⟩ := (mem_xg_iff hab).1 hx
      rw [← hc]
      refine Subgroup.subset_closure ?_
      fin_cases i <;> simp only [Fin.reduceFinMk, Fin.isValue] at hi ⊢ <;>
        first
        | omega
        | exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨c', rfl⟩))))
        | exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨c', rfl⟩))))
        | exact Or.inl (Or.inl (Or.inl (Or.inr ⟨c', rfl⟩)))
        | exact Or.inl (Or.inl (Or.inr ⟨c', rfl⟩))
    refine sup_le (sup_le (sup_le (hxg ne21 0 (by decide) fun _ => rfl)
      (hxg ne12 1 (by decide) fun _ => rfl)) (sup_le (hxg ne13 2 (by decide) fun _ => rfl)
        (hxg ne31 3 (by decide) fun _ => rfl))) (sup_le (fun u hu => ?_) (fun u hu => ?_))
    · obtain ⟨p, rfl⟩ := hι.surj u hu
      exact Subgroup.subset_closure (Or.inl (Or.inr ⟨p, rfl⟩))
    · obtain ⟨p, rfl⟩ := exists_ψU'_eq h hι hu
      exact Subgroup.subset_closure (Or.inr ⟨p, rfl⟩)
  nt := ⟨1, fun h1 => one_ne_zero (xs_injective hS ne21 (h1.trans (xs_zero ne21).symm))⟩

end Frame

theorem omega8Outcome {f : ℕ} (hf : 1 ≤ f) (h : Hyp G R)
    {Ψ : SpecialLinearGroup (Fin 4) (GaloisField 2 f) →* G} (hS : Skel R Ψ)
    (hB : HypB G R (xg Ψ 0 3)) {ι : (Fin 2 → GaloisField 2 f) → G} (hι : LinParamU R Ψ 2 ι) :
    NonSimplyLacedOutcome G ∧ NSLFrame G R := by
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hP := ptHyp_of_hypB hB
  obtain ⟨b, c, ι', hι', hQ, hirr⟩ := exists_normParam h hS hι hP
  have := fact_shortField hirr
  have hC := isB3Frame h hS hP hι' hQ hB
  have hframe : IsCTFrame (minusDatum 4 hirr) G (b3PhiOf hirr (mL Ψ) (mS Ψ ι')) :=
    ⟨hC.hcone hirr, hC.hrank hirr, hC.hgen hirr, hC.hnt hirr⟩
  have hadm : StatedLieAdmissible .POmegaMinus 4 2 f := ⟨Nat.prime_two, hf, le_rfl⟩
  have hCT := CurtisTits.curtisTitsConclusion_spinMinus (n := 4) hirr hadm hF
  have hL := leviConePresented_spinMinus hirr (le_refl 4)
  refine ⟨.inr (.inl ⟨4, f, le_rfl, hf, hframe.lieModel hCT hL h.center⟩), ?_⟩
  refine hframe.nslFrame hCT hL (minusDatum_isCTGroupDatum 4 hirr le_rfl)
    (minusDatum_steinbergExtras 4 hirr) rfl (NSLType.minusDatum le_rfl hirr) (b3_isPGroup hirr)
    (fun hC' => absurd hC' (minusDatum_cartan_ne hirr)) (hS.mem 2 1 ne21) ?_ ?_
    (hS.opp 2 1 ne21)
  · have key : ∀ γ : Fin 3 → ℤ, b3r 0 = γ →
        (xg Ψ 2 1 : Set G) = Set.range (b3PhiOf hirr (mL Ψ) (mS Ψ ι') γ) := by
      rintro γ rfl
      ext x
      constructor
      · intro hx
        obtain ⟨s, rfl⟩ := (mem_xg_iff ne21).1 hx
        exact ⟨⟨b3xL b c 0 s, b3xL_mem hirr (a := 0) rfl s⟩,
          b3PhiOf_long hirr (mL Ψ) (mS Ψ ι') (a := 0) rfl s _⟩
      · rintro ⟨⟨y, hy⟩, rfl⟩
        obtain ⟨s, rfl⟩ := exists_b3xL_eq hirr (a := 0) rfl hy
        rw [b3PhiOf_long hirr (mL Ψ) (mS Ψ ι') (a := 0) rfl s hy]
        exact xs_mem ne21 s
    have e : b3r 0 = (Pi.single (0 : Fin 3) 1 : Fin 3 → ℤ) := by decide
    exact key _ e
  · have key : ∀ γ : Fin 3 → ℤ, b3r 1 = γ →
        (xg Ψ 1 2 : Set G) = Set.range (b3PhiOf hirr (mL Ψ) (mS Ψ ι') γ) := by
      rintro γ rfl
      ext x
      constructor
      · intro hx
        obtain ⟨s, rfl⟩ := (mem_xg_iff ne12).1 hx
        exact ⟨⟨b3xL b c 1 s, b3xL_mem hirr (a := 1) rfl s⟩,
          b3PhiOf_long hirr (mL Ψ) (mS Ψ ι') (a := 1) rfl s _⟩
      · rintro ⟨⟨y, hy⟩, rfl⟩
        obtain ⟨s, rfl⟩ := exists_b3xL_eq hirr (a := 1) rfl hy
        rw [b3PhiOf_long hirr (mL Ψ) (mS Ψ ι') (a := 1) rfl s hy]
        exact xs_mem ne12 s
    have e : b3r 1 = -(Pi.single (0 : Fin 3) 1 : Fin 3 → ℤ) := by decide
    exact key _ e

end CaseB

end CFSG.Timmesfeld.ARS
