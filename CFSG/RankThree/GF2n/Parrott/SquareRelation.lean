module

public import CFSG.RankThree.GF2n.Parrott.LiftClaimC
public import CFSG.RankThree.GF2n.Parrott.SpinConfig
public import CFSG.RankThree.GF2n.Parrott.Section4SpinGlue
public import CFSG.RankThree.GF2n.Parrott.Section4SylowFiveStructure
public import CFSG.RankThree.GF2n.Parrott.SpinFixedCardUT
public import CFSG.RankThree.GF2n.Parrott.SpinFixedCardMore
public import CFSG.RankThree.GF2n.Parrott.Section4NoFusionLift
public import CFSG.RankThree.GF2n.Parrott.QA45SylowFacts
public import CFSG.RankThree.GF2n.Parrott.QA45ElementaryAbelian

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.GroupTheory CFSG.ABGLocalTools Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped Matrix commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "vA" => (⟨v, v_mem_A⟩ : A45)

private noncomputable def specToV (h : Tim79a.ParrottHyp z) (P : GL8) (w : V) :
    QuotientV.V z :=
  (mulEquivV h).symm (Multiplicative.ofAdd (((P : Matrix (Fin 8) (Fin 8) (ZMod 2))) *ᵥ w))

private theorem toAdd_mulEquivV_specToV (h : Tim79a.ParrottHyp z) (P : GL8) (w : V) :
    Multiplicative.toAdd (mulEquivV h (specToV h P w)) =
      ((P : Matrix (Fin 8) (Fin 8) (ZMod 2))) *ᵥ w := by
  simp [specToV]

private theorem specToV_add (h : Tim79a.ParrottHyp z) (P : GL8) (u w : V) :
    specToV h P (u + w) = specToV h P u * specToV h P w := by
  apply (mulEquivV h).injective
  rw [map_mul]
  apply Multiplicative.toAdd.injective
  rw [toAdd_mul, toAdd_mulEquivV_specToV, toAdd_mulEquivV_specToV, toAdd_mulEquivV_specToV,
    Matrix.mulVec_add]

private theorem specToV_injective (h : Tim79a.ParrottHyp z) (P : GL8) :
    Function.Injective (specToV h P) := by
  intro w w' hww
  have h1 := congrArg (fun v => Multiplicative.toAdd (mulEquivV h v)) hww
  simp only [toAdd_mulEquivV_specToV] at h1
  have h2 := congrArg (fun u => ((P⁻¹ : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ u) h1
  simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mulVec] at h2
  exact h2

private theorem specToV_surjective (h : Tim79a.ParrottHyp z) (P : GL8) :
    Function.Surjective (specToV h P) := by
  intro v
  refine ⟨((P⁻¹ : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ
    Multiplicative.toAdd (mulEquivV h v), ?_⟩
  apply (mulEquivV h).injective
  apply Multiplicative.toAdd.injective
  rw [toAdd_mulEquivV_specToV, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, Matrix.one_mulVec]

variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

private theorem conjV_specToV (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹) (y : ↥(H z)) (w : V) :
    conjV h y (specToV h P w) =
      specToV h P (((rhoA (qH D y) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w) := by
  apply (mulEquivV h).injective
  apply Multiplicative.toAdd.injective
  rw [← mulVec_mulAutVEquivGL h (conjV h y) (specToV h P w), toAdd_mulEquivV_specToV,
    ← actionQA45_qH D h y, hP, toAdd_mulEquivV_specToV]
  have key : (P * rhoA (qH D y) * P⁻¹ * P : GL8) = P * rhoA (qH D y) := by group
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, key, Units.val_mul, ← Matrix.mulVec_mulVec]

private theorem qVZMod_seven' (h : Tim79a.ParrottHyp z) (a b c : QuotientV.V z) :
    qVZMod h (a * b * c) + qVZMod h (a * b) + qVZMod h (a * c) + qVZMod h (b * c) +
      qVZMod h a + qVZMod h b + qVZMod h c = 0 := by
  rw [qVZMod_mul_add h (a * b) c, polarVZMod_add h a b c, qVZMod_mul_add h a c,
    qVZMod_mul_add h b c]
  have key : ∀ x1 x2 x3 x4 x5 x6 : ZMod 2,
      (x1 + x2 + (x3 + x4)) + x1 + (x5 + x2 + x3) + (x6 + x2 + x4) + x5 + x6 + x2 = 0 := by
    decide
  exact key _ _ _ _ _ _

private theorem qVZMod_specToV_eq_q (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹) (w : V) :
    qVZMod h (specToV h P w) = q w := by
  have hQ : (fun w : V => qVZMod h (specToV h P w)) = 0 ∨
      (fun w : V => qVZMod h (specToV h P w)) = q := by
    refine spinInvariantQuadratic_unique _ ?_ ?_
    · intro u u' w
      have h1 := qVZMod_seven' h (specToV h P u) (specToV h P u') (specToV h P w)
      rwa [← specToV_add, ← specToV_add, ← specToV_add, ← specToV_add] at h1
    · intro a w
      obtain ⟨y, rfl⟩ := qH_surjective D a
      show qVZMod h (specToV h P _) = qVZMod h (specToV h P w)
      rw [← conjV_specToV D h P hP y w, qVZMod_conj]
  rcases hQ with h0 | hq
  · exfalso
    have hall : ∀ v : QuotientV.V z, qVZMod h v = 0 := by
      intro v
      obtain ⟨w', rfl⟩ := specToV_surjective h P v
      exact congrFun h0 w'
    have hone : ∀ v : QuotientV.V z, v = 1 := by
      intro v
      refine polarVZMod_nondegenerate h v (fun w' => ?_)
      have h1 := qVZMod_mul_add h v w'
      rw [hall, hall, hall] at h1
      simpa using h1.symm
    have hcard := QuotientV.card_V h
    have hsub : Subsingleton (QuotientV.V z) := ⟨fun a b => (hone a).trans (hone b).symm⟩
    have h1 : Nat.card (QuotientV.V z) = 1 := Nat.card_unique
    rw [hcard] at h1
    norm_num at h1
  · exact congrFun hq w

theorem qVZMod_eq_zero_of_spin (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹) {x : ↥(H z)}
    (hq : ∀ w : V, ((rhoA (qH D x) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w → q w = 0) :
    ∀ v : QuotientV.V z, conjV h x v = v → qVZMod h v = 0 := by
  intro v hv
  obtain ⟨w, rfl⟩ := specToV_surjective h P v
  rw [conjV_specToV D h P hP x w] at hv
  have hw := specToV_injective h P hv
  rw [qVZMod_specToV_eq_q D h P hP]
  exact hq w hw

theorem free_of_spin (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹) {x y : ↥(H z)}
    (hfree : ∀ w : V, ((rhoA (qH D x) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w →
      ((rhoA (qH D y) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w →
      ∃ w' : V, ((rhoA (qH D x) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w' = w' ∧
        ((rhoA (qH D y) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w' + w' = w) :
    ∀ v : QuotientV.V z, conjV h x v = v → conjV h y v = v →
      ∃ w : QuotientV.V z, conjV h x w = w ∧ conjV h y w * w⁻¹ = v := by
  intro v hvx hvy
  obtain ⟨w₀, rfl⟩ := specToV_surjective h P v
  rw [conjV_specToV D h P hP x w₀] at hvx
  rw [conjV_specToV D h P hP y w₀] at hvy
  have hx := specToV_injective h P hvx
  have hy := specToV_injective h P hvy
  obtain ⟨w', hw'x, hw'y⟩ := hfree w₀ hx hy
  refine ⟨specToV h P w', ?_, ?_⟩
  · rw [conjV_specToV D h P hP x w', hw'x]
  · rw [conjV_specToV D h P hP y w']
    have hinv : (specToV h P w')⁻¹ = specToV h P w' := by
      have hzero : specToV h P 0 = 1 := by
        apply (mulEquivV h).injective
        apply Multiplicative.toAdd.injective
        simp [toAdd_mulEquivV_specToV]
      have h2 : ∀ x : ZMod 2, x + x = 0 := by decide
      have : specToV h P w' * specToV h P w' = 1 := by
        rw [← specToV_add]
        have : w' + w' = 0 := by
          funext i
          exact h2 (w' i)
        rw [this, hzero]
      exact inv_eq_of_mul_eq_one_right this
    rw [hinv, ← specToV_add, hw'y]

theorem qH_eq_of_inv_mul_mem {a b : ↥(H z)} (hab : a⁻¹ * b ∈ (J z).subgroupOf (H z)) :
    qH D a = qH D b := by
  have h1 := (J_mem_iff D (a⁻¹ * b)).mp hab
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1

theorem mul_self_eq_of_isConj_qH (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z)) {x₀ x : G} (hx₀ : x₀ ∈ H z) (hx : x ∈ H z)
    (hdim : fixDimV h ⟨x₀, hx₀⟩ = 4) (hconj : IsConj (qH D ⟨x, hx⟩) (qH D ⟨x₀, hx₀⟩))
    (h₀ : x₀ * x₀ ∈ centerIn (J z)) (h₁ : x * x ∈ centerIn (J z)) : x₀ * x₀ = x * x := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  obtain ⟨g, rfl⟩ := qH_surjective D c
  have hx'H : (g : G) * x * (g : G)⁻¹ ∈ H z :=
    (H z).mul_mem ((H z).mul_mem g.2 hx) ((H z).inv_mem g.2)
  have hq : qH D ⟨(g : G) * x * (g : G)⁻¹, hx'H⟩ = qH D ⟨x₀, hx₀⟩ := by
    have e : (⟨(g : G) * x * (g : G)⁻¹, hx'H⟩ : ↥(H z)) = g * ⟨x, hx⟩ * g⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
    exact hc
  have hcos : x₀⁻¹ * ((g : G) * x * (g : G)⁻¹) ∈ J z := by
    have h1 : (⟨x₀, hx₀⟩ : ↥(H z))⁻¹ * ⟨(g : G) * x * (g : G)⁻¹, hx'H⟩ ∈
        (J z).subgroupOf (H z) := by
      rw [J_mem_iff D, map_mul, map_inv, hq, inv_mul_cancel]
    exact Subgroup.mem_subgroupOf.mp h1
  have hgx : (g : G) * (x * x) = (x * x) * (g : G) := centerIn_J_comm_H hZ h₁ g.2
  have hx'x' : ((g : G) * x * (g : G)⁻¹) * ((g : G) * x * (g : G)⁻¹) = x * x := by
    calc ((g : G) * x * (g : G)⁻¹) * ((g : G) * x * (g : G)⁻¹)
        = (g : G) * (x * x) * (g : G)⁻¹ := by group
      _ = (x * x) * (g : G) * (g : G)⁻¹ := by rw [hgx]
      _ = x * x := by group
  have hx'Z : ((g : G) * x * (g : G)⁻¹) * ((g : G) * x * (g : G)⁻¹) ∈ centerIn (J z) := by
    rw [hx'x']; exact h₁
  have := mul_self_eq_of_fixDimV_eq_four h hZ hx₀ hcos hdim h₀ hx'Z
  rw [this, hx'x']

theorem fixDimV_eq_four_of_spin_class (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹) {a₀ : A45}
    (hρ : ∀ a : A45, IsConj a a₀ →
      fixCard (((rhoA a : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2))) = 16) :
    ∀ y : ↥(H z), IsConj (qH D y) a₀ → fixDimV h y = 4 :=
  fixDimV_eq_of_conj_rep D h rhoA P hP (fun a => IsConj a a₀) 4 (fun a ha => by
    rw [hρ a ha]; norm_num)

theorem exists_square_triple (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) = centerIn (H z))
    (P : GL8) (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹) :
    ∃ (x₀ y₀ : G) (hx₀ : x₀ ∈ H z) (hy₀ : y₀ ∈ H z),
      IsConj (qH D ⟨x₀, hx₀⟩) (uA * vA) ∧ x₀ * x₀ ∈ centerIn (J z) ∧ y₀ * y₀ ∈ centerIn (J z) ∧
      x₀ * y₀ = y₀ * x₀ ∧ IsConj (qH D ⟨y₀, hy₀⟩) (uA * tA) ∧
      IsConj (qH D ⟨x₀ * y₀, (H z).mul_mem hx₀ hy₀⟩) vA := by
  obtain ⟨g₁, g₂, hc1, hc2, hbb, hcut, hcv, hq, hfree⟩ := exists_spinConfig
  obtain ⟨x₁, hx₁⟩ := qH_surjective D (uA * vA)
  have hdimuv : ∀ y : ↥(H z), IsConj (qH D y) (uA * vA) → fixDimV h y = 4 :=
    fixDimV_eq_four_of_spin_class D h P hP (fun a ha => spinFixedCard_uv a ha)
  have hx₁sq : (x₁ : G) * x₁ ∈ J z := by
    have : (x₁ * x₁ : ↥(H z)) ∈ (J z).subgroupOf (H z) :=
      (J_mem_iff D _).mpr (by rw [map_mul, hx₁]; exact uv_mul_self_A)
    exact Subgroup.mem_subgroupOf.mp this
  have hdim₁ : fixDimV h x₁ = 4 := hdimuv x₁ (by rw [hx₁])
  obtain ⟨j, hjJ, hxx⟩ := exists_lift_sq_mem_centerIn h x₁ hdim₁ hx₁sq
  set x₀ : ↥(H z) := ⟨(x₁ : G) * j, (H z).mul_mem x₁.2 (J_le_H hjJ)⟩ with hx₀def
  have hqx₀ : qH D x₀ = uA * vA := by
    have e : x₀ = x₁ * ⟨j, J_le_H hjJ⟩ := rfl
    rw [e, map_mul, hx₁,
      (J_mem_iff D ⟨j, J_le_H hjJ⟩).mp (Subgroup.mem_subgroupOf.mpr hjJ), mul_one]
  have hdim₀ : fixDimV h x₀ = 4 := hdimuv x₀ (by rw [hqx₀])
  obtain ⟨g₁', hg₁'⟩ := qH_surjective D g₁
  obtain ⟨g₂', hg₂'⟩ := qH_surjective D g₂
  have hq0 : ∀ v : QuotientV.V z, conjV h x₀ v = v → qVZMod h v = 0 :=
    qVZMod_eq_zero_of_spin D h P hP (x := x₀) (by rw [hqx₀]; exact hq)
  have hcomJ : ∀ (g' : ↥(H z)) (g : A45), qH D g' = g → (uA * vA) * g = g * (uA * vA) →
      ⁅(x₀ : G), (g' : G)⁆ ∈ J z := by
    intro g' g hg' hcm
    have h1 : ⁅x₀, g'⁆ ∈ (J z).subgroupOf (H z) := by
      rw [J_mem_iff D, map_commutatorElement, hqx₀, hg']
      exact commutatorElement_eq_one_iff_mul_comm.mpr hcm
    exact Subgroup.mem_subgroupOf.mp h1
  have hb2 : (((⁅g₁', g₂'⁆ : ↥(H z)) : G) * ((⁅g₁', g₂'⁆ : ↥(H z)) : G)) ∈ J z := by
    have h1 : (⁅g₁', g₂'⁆ * ⁅g₁', g₂'⁆ : ↥(H z)) ∈ (J z).subgroupOf (H z) := by
      rw [J_mem_iff D, map_mul, map_commutatorElement, hg₁', hg₂']
      exact hbb
    exact Subgroup.mem_subgroupOf.mp h1
  have hfree' : ∀ y' : ↥(H z), ((⁅g₁', g₂'⁆ : ↥(H z))⁻¹ * y' : ↥(H z)) ∈
      (J z).subgroupOf (H z) → ∀ v : QuotientV.V z, conjV h x₀ v = v → conjV h y' v = v →
      ∃ w : QuotientV.V z, conjV h x₀ w = w ∧ conjV h y' w * w⁻¹ = v := by
    intro y' hy'
    have hqy' : qH D y' = ⁅g₁, g₂⁆ := by
      rw [← qH_eq_of_inv_mul_mem D hy', map_commutatorElement, hg₁', hg₂']
    refine free_of_spin D h P hP (x := x₀) (y := y') ?_
    rw [hqx₀, hqy']
    exact hfree
  obtain ⟨y, hyb, hyy, hxy⟩ := exists_commuting_lift_of_derived h hZ x₀ g₁' g₂' hdim₀ hxx hq0
    (hcomJ g₁' g₁ hg₁' hc1) (hcomJ g₂' g₂ hg₂' hc2) hb2 hfree'
  have hqy : qH D y = ⁅g₁, g₂⁆ := by
    rw [← qH_eq_of_inv_mul_mem D hyb, map_commutatorElement, hg₁', hg₂']
  refine ⟨(x₀ : G), (y : G), x₀.2, y.2, ?_, hxx, hyy, hxy, ?_, ?_⟩
  · rw [hqx₀]
  · rw [hqy]; exact hcut
  · have e : (⟨(x₀ : G) * (y : G), (H z).mul_mem x₀.2 y.2⟩ : ↥(H z)) = x₀ * y := rfl
    rw [e, map_mul, hqx₀, hqy]
    exact hcv

theorem mul_self_eq_mul_of_classes (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z)) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    (x y w : G) (hx : x ∈ H z) (hy : y ∈ H z) (hw : w ∈ H z)
    (hxc : IsConj (qH D ⟨x, hx⟩) (uA * vA)) (hyc : IsConj (qH D ⟨y, hy⟩) vA)
    (hwc : IsConj (qH D ⟨w, hw⟩) (uA * tA))
    (hxZ : x * x ∈ centerIn (J z)) (hyZ : y * y ∈ centerIn (J z))
    (hwZ : w * w ∈ centerIn (J z)) : y * y = (x * x) * (w * w) := by
  obtain ⟨x₀, y₀, hx₀, hy₀, hx₀c, hx₀Z, hy₀Z, hcomm, hy₀c, hxy₀c⟩ :=
    exists_square_triple D h hZ P hP
  have hdimuv : ∀ y : ↥(H z), IsConj (qH D y) (uA * vA) → fixDimV h y = 4 :=
    fixDimV_eq_four_of_spin_class D h P hP (fun a ha => spinFixedCard_uv a ha)
  have hdimut : ∀ y : ↥(H z), IsConj (qH D y) (uA * tA) → fixDimV h y = 4 :=
    fixDimV_eq_four_of_spin_class D h P hP (fun a ha => spinFixedCard_ut a ha)
  have hdimv : ∀ y : ↥(H z), IsConj (qH D y) vA → fixDimV h y = 4 :=
    fixDimV_eq_four_of_spin_class D h P hP (fun a ha => spinFixedCard_v a ha)
  have e1 : x₀ * x₀ = x * x :=
    mul_self_eq_of_isConj_qH D h hZ hx₀ hx (hdimuv ⟨x₀, hx₀⟩ hx₀c) (hxc.trans hx₀c.symm)
      hx₀Z hxZ
  have e2 : y₀ * y₀ = w * w :=
    mul_self_eq_of_isConj_qH D h hZ hy₀ hw (hdimut ⟨y₀, hy₀⟩ hy₀c) (hwc.trans hy₀c.symm)
      hy₀Z hwZ
  have e4 : (x₀ * y₀) * (x₀ * y₀) = (x₀ * x₀) * (y₀ * y₀) := by
    calc (x₀ * y₀) * (x₀ * y₀) = x₀ * (y₀ * x₀) * y₀ := by group
      _ = x₀ * (x₀ * y₀) * y₀ := by rw [hcomm]
      _ = (x₀ * x₀) * (y₀ * y₀) := by group
  have hxyZ : (x₀ * y₀) * (x₀ * y₀) ∈ centerIn (J z) := by
    rw [e4]; exact (centerIn (J z)).mul_mem hx₀Z hy₀Z
  have e3 : (x₀ * y₀) * (x₀ * y₀) = y * y :=
    mul_self_eq_of_isConj_qH D h hZ ((H z).mul_mem hx₀ hy₀) hy
      (hdimv ⟨x₀ * y₀, (H z).mul_mem hx₀ hy₀⟩ hxy₀c) (hyc.trans hxy₀c.symm) hxyZ hyZ
  rw [← e3, e4, e1, e2]

theorem exists_involution_ut_of_isParrottE {E : Subgroup G} (hE : IsParrottE z E) :
    ∃ (w : G) (hw : w ∈ H z), w * w = 1 ∧ IsConj (qH D ⟨w, hw⟩) (uA * tA) := by
  obtain ⟨hEH, hEN, hZE, hEel, hEcard, hEJcard, -, -⟩ := hE
  have hcardbar : Nat.card (imageQA45 D hEH) = 16 := by
    have h1 := card_eq_card_inf_J_mul_card_imageQA45 D hEH
    rw [hEcard, hEJcard] at h1
    norm_num at h1
    omega
  have hel := isElemAbelian_imageQA45 D hEH hEel
  have hle := imageQA45_le_Q D hEH hEN
  obtain ⟨g, hg⟩ := (qa45_elemAbelian_sixteen.2 (imageQA45 D hEH) hel hcardbar hle)
  have hut : uA * tA ∈ sQA45 :=
    Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  rw [← hg] at hut
  obtain ⟨a, ha, hau⟩ := Subgroup.mem_map.mp hut
  obtain ⟨e, he, hqe⟩ := (mem_imageQA45_iff D hEH a).mp ha
  refine ⟨e, hEH he, ?_, ?_⟩
  · have h1 := hEel.2 e he
    rwa [pow_two] at h1
  · refine isConj_iff.mpr ⟨g, ?_⟩
    rw [hqe]
    simpa [MulAut.conj_apply] using hau

theorem hv_of_isParrottE (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) = centerIn (H z))
    (P : GL8) (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {E : Subgroup G} (hE : IsParrottE z E) :
    ∀ (y : G) (hy : y ∈ H z), y * y = 1 → IsConj (qH D ⟨y, hy⟩) vA →
      ∃ B : Subgroup G, IsSylowOf 5 B (H z) ∧ ∃ x₀ ∈ H z, x₀ * x₀ = 1 ∧
        x₀ ∉ ⁅H z, H z⁆ ⊔ centerIn (J z) ∧ ∀ b ∈ B, x₀ * b = b * x₀ := by
  intro y hy hyy hyc
  obtain ⟨w, hw, hww, hwc⟩ := exists_involution_ut_of_isParrottE D hE
  obtain ⟨x₀, y₀, hx₀, hy₀, hx₀c, hx₀Z, -, -, -, -⟩ := exists_square_triple D h hZ P hP
  have hrel := mul_self_eq_mul_of_classes D h hZ P hP x₀ y w hx₀ hy hw hx₀c hyc hwc hx₀Z
    (by rw [hyy]; exact (centerIn (J z)).one_mem) (by rw [hww]; exact (centerIn (J z)).one_mem)
  rw [hyy, hww, mul_one] at hrel
  have hV2 : ∀ y : ↥(H z), IsConj (qH D y) (uA * vA) → fixDimV h y = 4 :=
    fixDimV_eq_four_of_spin_class D h P hP (fun a ha => spinFixedCard_uv a ha)
  have hV5 : ∀ y : ↥(H z), orderOf (qH D y) = 5 → fixDimV h y = 0 :=
    fixDimV_eq_of_conj_rep D h rhoA P hP (fun a => orderOf a = 5) 0
      (fun a ha => by simpa using spinFixedCard_five a ha)
  have hC5 : ∀ B : Subgroup A45, Nat.card B = 5 → Nat.card (centralizer (B : Set A45)) = 10 ∧
      ∃ w : A45, orderOf w = 2 ∧ IsConj w (uA * vA) ∧
        centralizer (B : Set A45) = B ⊔ zpowers w := fun B hB =>
    ⟨(qa45_sylowFive B hB).2.1, (qa45_sylowFive B hB).2.2⟩
  exact hlift_of_uv_involution D h hZ hV2 hV5 hC5 hx₀ hrel.symm hx₀c

end CFSG.RankThree.GF2n.Parrott
