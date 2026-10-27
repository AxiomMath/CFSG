module

public import CFSG.Quasithin.Recognition.Stroth.MoufangRootAction
public import CFSG.GH74.GLS.SP.GlueT3Core

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Quasithin CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.Geometry.GeneralizedPolygons

open scoped Pointwise

variable {V : Type} [Fintype V] {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
  {n : ℕ} {D : Type} [Group D] [MulAction D V] [FaithfulSMul D V] [GraphAction D Γ]

noncomputable abbrev reflOneL (t : ZMod (2 * n) → V) (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n) :
    ↥(littleGroup D Γ n) :=
  ((reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM : ↥(moufangN D Γ n t)) :
    ↥(littleGroup D Γ n))

noncomputable abbrev reflTwoL (t : ZMod (2 * n) → V) (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n) :
    ↥(littleGroup D Γ n) :=
  ((reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM : ↥(moufangN D Γ n t)) :
    ↥(littleGroup D Γ n))

theorem moufangCartan_conj_mem {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ)
    {h k : ↥(littleGroup D Γ n)} (hh : h ∈ moufangCartan D Γ n t)
    (hk : k ∈ moufangN D Γ n t) : k * h * k⁻¹ ∈ moufangCartan D Γ n t := by
  have hnorm := (Subgroup.normal_subgroupOf_iff
    (inf_le_right : moufangB D Γ n t ⊓ moufangN D Γ n t ≤ moufangN D Γ n t)).mp
    (by simpa [cartan, moufangCartan] using moufangCartan_normal (t := t) ht hn hP hT)
  exact hnorm h k hh hk

theorem reflOneL_sq_mem_cartan {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n) :
    reflOneL (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM *
        reflOneL (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM ∈
      moufangCartan D Γ n t := by
  have h := reflOneN_sq_mem_cartan (t := t) ht hn hP hT hM
  rw [cartan] at h
  rw [moufangCartan]
  simpa [reflOneL] using Subgroup.mem_subgroupOf.mp h

theorem reflTwoL_sq_mem_cartan {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n) :
    reflTwoL (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM *
        reflTwoL (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM ∈
      moufangCartan D Γ n t := by
  have h := reflTwoN_sq_mem_cartan (t := t) ht hn hP hT hM
  rw [cartan] at h
  rw [moufangCartan]
  simpa [reflTwoL] using Subgroup.mem_subgroupOf.mp h

theorem mem_moufangCartan_of_fix_apartment {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ)
    {m : ↥(littleGroup D Γ n)} (hfix : ∀ k : ℤ, (m : D) • apt t k = apt t k) :
    m ∈ moufangCartan D Γ n t := by
  rw [moufangCartan_eq_fixingSubgroup (t := t) ht hn hP hT]
  refine Subgroup.mem_subgroupOf.mpr ?_
  rw [mem_fixingSubgroup_iff]
  intro y hy
  obtain ⟨k, rfl⟩ := hy
  obtain ⟨j, rfl⟩ := ZMod.intCast_surjective k
  exact hfix j

theorem conjBy_inv_of_sq {X : Type*} [Group X] {H : Subgroup X} {root : ℤ → Subgroup X}
    {r : X} (hinv : ∀ i, IsRoot n i → ∀ h ∈ H, ∀ x ∈ root i, h * x * h⁻¹ ∈ root i)
    (hsq : r * r ∈ H) {i j : ℤ} (hi : IsRoot n i)
    (h : CFSG.GH74.BNPair.conjBy r (root i) = root j) :
    CFSG.GH74.BNPair.conjBy r⁻¹ (root i) = root j := by
  have hsq' : r⁻¹ * r⁻¹ ∈ H := by
    have := H.inv_mem hsq
    simpa [mul_inv_rev] using this
  have hH : CFSG.GH74.BNPair.conjBy (r⁻¹ * r⁻¹) (root i) = root i := by
    ext x
    rw [CFSG.GH74.BNPair.mem_conjBy_iff]
    constructor
    · intro hx
      have := hinv i hi (r⁻¹ * r⁻¹)⁻¹ (H.inv_mem hsq')
        ((r⁻¹ * r⁻¹) * x * (r⁻¹ * r⁻¹)⁻¹) hx
      have hx' : (r⁻¹ * r⁻¹)⁻¹ * ((r⁻¹ * r⁻¹) * x * (r⁻¹ * r⁻¹)⁻¹) *
          (r⁻¹ * r⁻¹) = x := by group
      rw [inv_inv] at this
      rwa [hx'] at this
    · intro hx
      exact hinv i hi (r⁻¹ * r⁻¹) hsq' x hx
  calc CFSG.GH74.BNPair.conjBy r⁻¹ (root i)
      = CFSG.GH74.BNPair.conjBy ((r⁻¹ * r⁻¹) * r) (root i) := by
        congr 1
        group
    _ = CFSG.GH74.BNPair.conjBy r (CFSG.GH74.BNPair.conjBy (r⁻¹ * r⁻¹) (root i)) := by
        rw [CFSG.GH74.BNPair.conjBy_mul]
    _ = CFSG.GH74.BNPair.conjBy r (root i) := by rw [hH]
    _ = root j := h

theorem action_one_moufang_inv {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ)
    (hM : MoufangCondition D Γ n) :
    CFSG.GH74.BNPair.conjBy (reflOneL (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM)⁻¹
        (rootL (D := D) (Γ := Γ) (n := n) t 1) =
      rootL (D := D) (Γ := Γ) (n := n) t (-1) ∧
    CFSG.GH74.BNPair.conjBy (reflOneL (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM)⁻¹
        (rootL (D := D) (Γ := Γ) (n := n) t (-1)) =
      rootL (D := D) (Γ := Γ) (n := n) t 1 ∧
    ∀ i : ℤ, 2 ≤ i → i ≤ (n : ℤ) →
      CFSG.GH74.BNPair.conjBy (reflOneL (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM)⁻¹
          (rootL (D := D) (Γ := Γ) (n := n) t i) =
        rootL (D := D) (Γ := Γ) (n := n) t ((n : ℤ) + 2 - i) ∧
      CFSG.GH74.BNPair.conjBy (reflOneL (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM)⁻¹
          (rootL (D := D) (Γ := Γ) (n := n) t (-i)) =
        rootL (D := D) (Γ := Γ) (n := n) t (-((n : ℤ) + 2 - i)) := by
  haveI : (cartan (moufangB D Γ n t) (moufangN D Γ n t)).Normal :=
    moufangCartan_normal (t := t) ht hn hP hT
  have hR := isRootGroupSystem_moufang (t := t) ht hn hP hT hM
  have hinv : ∀ i, IsRoot n i → ∀ h ∈ moufangCartan D Γ n t,
      ∀ x ∈ rootL (D := D) (Γ := Γ) (n := n) t i, h * x * h⁻¹ ∈
        rootL (D := D) (Γ := Γ) (n := n) t i := hR.invariant
  have hsq := reflOneL_sq_mem_cartan (t := t) ht hn hP hT hM
  have hdir := action_one_moufang (t := t) ht hn hP hT hM
    (reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM) rfl
  refine ⟨?_, ?_, fun i hi2 hin => ⟨?_, ?_⟩⟩
  · exact conjBy_inv_of_sq hinv hsq (isRoot_of_pos_le le_rfl (by omega)) hdir.1
  · exact conjBy_inv_of_sq hinv hsq
      (RGD2.isRoot_neg (isRoot_of_pos_le le_rfl (by omega))) hdir.2.1
  · exact conjBy_inv_of_sq hinv hsq
      (isRoot_of_pos_le (by omega) (by omega)) (hdir.2.2 i hi2 hin).1
  · exact conjBy_inv_of_sq hinv hsq
      (RGD2.isRoot_neg (isRoot_of_pos_le (by omega) (by omega))) (hdir.2.2 i hi2 hin).2

theorem action_two_moufang_inv {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ)
    (hM : MoufangCondition D Γ n) :
    CFSG.GH74.BNPair.conjBy (reflTwoL (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM)⁻¹
        (rootL (D := D) (Γ := Γ) (n := n) t (n : ℤ)) =
      rootL (D := D) (Γ := Γ) (n := n) t (-(n : ℤ)) ∧
    CFSG.GH74.BNPair.conjBy (reflTwoL (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM)⁻¹
        (rootL (D := D) (Γ := Γ) (n := n) t (-(n : ℤ))) =
      rootL (D := D) (Γ := Γ) (n := n) t (n : ℤ) ∧
    ∀ i : ℤ, 1 ≤ i → i ≤ (n : ℤ) - 1 →
      CFSG.GH74.BNPair.conjBy (reflTwoL (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM)⁻¹
          (rootL (D := D) (Γ := Γ) (n := n) t i) =
        rootL (D := D) (Γ := Γ) (n := n) t ((n : ℤ) - i) ∧
      CFSG.GH74.BNPair.conjBy (reflTwoL (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM)⁻¹
          (rootL (D := D) (Γ := Γ) (n := n) t (-i)) =
        rootL (D := D) (Γ := Γ) (n := n) t (-((n : ℤ) - i)) := by
  haveI : (cartan (moufangB D Γ n t) (moufangN D Γ n t)).Normal :=
    moufangCartan_normal (t := t) ht hn hP hT
  have hR := isRootGroupSystem_moufang (t := t) ht hn hP hT hM
  have hinv : ∀ i, IsRoot n i → ∀ h ∈ moufangCartan D Γ n t,
      ∀ x ∈ rootL (D := D) (Γ := Γ) (n := n) t i, h * x * h⁻¹ ∈
        rootL (D := D) (Γ := Γ) (n := n) t i := hR.invariant
  have hsq := reflTwoL_sq_mem_cartan (t := t) ht hn hP hT hM
  have hdir := action_two_moufang (t := t) ht hn hP hT hM
    (reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM) rfl
  refine ⟨?_, ?_, fun i hi1 hin => ⟨?_, ?_⟩⟩
  · exact conjBy_inv_of_sq hinv hsq (isRoot_of_pos_le (by omega) le_rfl) hdir.1
  · exact conjBy_inv_of_sq hinv hsq
      (RGD2.isRoot_neg (isRoot_of_pos_le (by omega) le_rfl)) hdir.2.1
  · exact conjBy_inv_of_sq hinv hsq
      (isRoot_of_pos_le hi1 (by omega)) (hdir.2.2 i hi1 hin).1
  · exact conjBy_inv_of_sq hinv hsq
      (RGD2.isRoot_neg (isRoot_of_pos_le hi1 (by omega))) (hdir.2.2 i hi1 hin).2


theorem rank_one_moufang {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ)
    (hM : MoufangCondition D Γ n) {y : ↥(littleGroup D Γ n)}
    (hy : y ∈ rootL (D := D) (Γ := Γ) (n := n) t (-1)) (hy1 : y ≠ 1) :
    y ∈ (rootL (D := D) (Γ := Γ) (n := n) t 1 : Set ↥(littleGroup D Γ n)) *
      (moufangCartan D Γ n t : Set ↥(littleGroup D Γ n)) *
      {reflOneL (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM} *
      (rootL (D := D) (Γ := Γ) (n := n) t 1 : Set ↥(littleGroup D Γ n)) := by
  let r₁ : ↥(littleGroup D Γ n) := reflOneL (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM
  let z : ↥(littleGroup D Γ n) := r₁ * y * r₁⁻¹
  have hconjH : ∀ h ∈ moufangCartan D Γ n t,
      r₁⁻¹ * h * r₁ ∈ moufangCartan D Γ n t := by
    intro h hh
    simpa [r₁, reflOneL, inv_inv] using moufangCartan_conj_mem (t := t) ht hn hP hT hh
      ((moufangN D Γ n t).inv_mem
        (reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM).2)
  have hactinv := action_one_moufang_inv (t := t) ht hn hP hT hM
  have hdir := action_one_moufang (t := t) ht hn hP hT hM
    (reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM) rfl
  have hzroot : z ∈ rootL (D := D) (Γ := Γ) (n := n) t 1 := by
    dsimp [z, r₁]
    exact mem_of_conjBy_inv hactinv.2.1 hy
  have hz1 : z ≠ 1 := by
    intro h
    apply hy1
    have := congrArg (fun w => r₁⁻¹ * w * r₁) h
    simpa [z, mul_assoc] using this
  have hzD : (z : D) ∈ aptRoot D Γ n t 1 := by
    have := Subgroup.mem_subgroupOf.mp hzroot
    simpa [rootL, rootD] using this
  have hz1D : (z : D) ≠ 1 := fun h => hz1 (Subtype.ext h)
  obtain ⟨v, hv, w, hw, hactm, -⟩ :=
    exists_reflection_apt (t := t) ht hn hP hT hM (i := 1) (u := (z : D)) hzD hz1D
  have hvL : v ∈ littleGroup D Γ n :=
    aptRoot_le_littleGroup ht (by omega) (1 + (n : ℤ)) hv
  have hwL : w ∈ littleGroup D Γ n :=
    aptRoot_le_littleGroup ht (by omega) (1 + (n : ℤ)) hw
  let vL : ↥(littleGroup D Γ n) := ⟨v, hvL⟩
  let wL : ↥(littleGroup D Γ n) := ⟨w, hwL⟩
  have hvroot : vL ∈ rootL (D := D) (Γ := Γ) (n := n) t (-1) := by
    rw [rootL, Subgroup.mem_subgroupOf, rootD, if_neg (by omega)]
    simpa [vL, show (n : ℤ) - (-1) = 1 + (n : ℤ) by ring] using hv
  have hwroot : wL ∈ rootL (D := D) (Γ := Γ) (n := n) t (-1) := by
    rw [rootL, Subgroup.mem_subgroupOf, rootD, if_neg (by omega)]
    simpa [wL, show (n : ℤ) - (-1) = 1 + (n : ℤ) by ring] using hw
  let mL : ↥(littleGroup D Γ n) := vL * z * wL
  have hmL : (mL : D) = v * (z : D) * w := by
    simp [mL, vL, wL]
  have hfix : ∀ k : ℤ, ((mL * r₁⁻¹ : ↥(littleGroup D Γ n)) : D) • apt t k = apt t k := by
    intro k
    rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul]
    have hr : (r₁ : D)⁻¹ • apt t k = apt t (2 * ((n : ℤ) + 1) - k) := by
      dsimp [r₁]
      simpa using reflOne_inv_smul (t := t) ht hn hP hT hM k
    rw [hr]
    have hm : (mL : D) • apt t (2 * ((n : ℤ) + 1) - k) =
        apt t (2 * (1 : ℤ) - (2 * ((n : ℤ) + 1) - k)) := by
      rw [hmL]
      simpa using hactm (2 * ((n : ℤ) + 1) - k)
    rw [hm]
    rw [show 2 * (1 : ℤ) - (2 * ((n : ℤ) + 1) - k) = k + 2 * (n : ℤ) * (-1) by ring,
      apt_add_two_mul]
  have hmemH : mL * r₁⁻¹ ∈ moufangCartan D Γ n t :=
    mem_moufangCartan_of_fix_apartment (t := t) ht hn hP hT hfix
  let hL : ↥(moufangCartan D Γ n t) := ⟨mL * r₁⁻¹, hmemH⟩
  have hm_eq : mL = (hL : ↥(littleGroup D Γ n)) * r₁ := by
    dsimp [hL]
    group
  have hzfac : z = vL⁻¹ * (hL : ↥(littleGroup D Γ n)) * r₁ * wL⁻¹ := by
    have h1 : vL * z * wL = (hL : ↥(littleGroup D Γ n)) * r₁ := by
      rw [← hm_eq]
    calc z = vL⁻¹ * (vL * z * wL) * wL⁻¹ := by group
      _ = vL⁻¹ * ((hL : ↥(littleGroup D Γ n)) * r₁) * wL⁻¹ := by rw [h1]
      _ = vL⁻¹ * (hL : ↥(littleGroup D Γ n)) * r₁ * wL⁻¹ := by group
  have hyfac : y = (r₁⁻¹ * vL⁻¹ * r₁) *
      (r₁⁻¹ * (hL : ↥(littleGroup D Γ n)) * r₁) * r₁ * (r₁⁻¹ * wL⁻¹ * r₁) := by
    calc y = r₁⁻¹ * z * r₁ := by dsimp [z]; group
      _ = r₁⁻¹ * (vL⁻¹ * (hL : ↥(littleGroup D Γ n)) * r₁ * wL⁻¹) * r₁ := by rw [hzfac]
      _ = (r₁⁻¹ * vL⁻¹ * r₁) *
          (r₁⁻¹ * (hL : ↥(littleGroup D Γ n)) * r₁) * r₁ * (r₁⁻¹ * wL⁻¹ * r₁) := by group
  have ha : r₁⁻¹ * vL⁻¹ * r₁ ∈ rootL (D := D) (Γ := Γ) (n := n) t 1 := by
    have hmem : r₁⁻¹ * vL⁻¹ * r₁ ∈
        CFSG.GH74.BNPair.conjBy r₁ (rootL (D := D) (Γ := Γ) (n := n) t (-1)) := by
      rw [CFSG.GH74.BNPair.mem_conjBy_iff]
      simpa [mul_assoc] using Subgroup.inv_mem _ hvroot
    rwa [hdir.2.1] at hmem
  have hb : r₁⁻¹ * wL⁻¹ * r₁ ∈ rootL (D := D) (Γ := Γ) (n := n) t 1 := by
    have hmem : r₁⁻¹ * wL⁻¹ * r₁ ∈
        CFSG.GH74.BNPair.conjBy r₁ (rootL (D := D) (Γ := Γ) (n := n) t (-1)) := by
      rw [CFSG.GH74.BNPair.mem_conjBy_iff]
      simpa [mul_assoc] using Subgroup.inv_mem _ hwroot
    rwa [hdir.2.1] at hmem
  have hhL : r₁⁻¹ * (hL : ↥(littleGroup D Γ n)) * r₁ ∈ moufangCartan D Γ n t :=
    hconjH _ hL.2
  refine Set.mem_mul.2 ⟨(r₁⁻¹ * vL⁻¹ * r₁) *
      (r₁⁻¹ * (hL : ↥(littleGroup D Γ n)) * r₁) * r₁,
    Set.mem_mul.2 ⟨(r₁⁻¹ * vL⁻¹ * r₁) *
        (r₁⁻¹ * (hL : ↥(littleGroup D Γ n)) * r₁),
      Set.mem_mul.2 ⟨r₁⁻¹ * vL⁻¹ * r₁, ha,
        r₁⁻¹ * (hL : ↥(littleGroup D Γ n)) * r₁, hhL, rfl⟩, r₁, rfl, rfl⟩,
    r₁⁻¹ * wL⁻¹ * r₁, hb, hyfac.symm⟩

theorem rank_two_moufang {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ)
    (hM : MoufangCondition D Γ n) {y : ↥(littleGroup D Γ n)}
    (hy : y ∈ rootL (D := D) (Γ := Γ) (n := n) t (-(n : ℤ))) (hy1 : y ≠ 1) :
    y ∈ (rootL (D := D) (Γ := Γ) (n := n) t (n : ℤ) : Set ↥(littleGroup D Γ n)) *
      (moufangCartan D Γ n t : Set ↥(littleGroup D Γ n)) *
      {reflTwoL (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM} *
      (rootL (D := D) (Γ := Γ) (n := n) t (n : ℤ) : Set ↥(littleGroup D Γ n)) := by
  let r₂ : ↥(littleGroup D Γ n) := reflTwoL (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM
  let z : ↥(littleGroup D Γ n) := r₂ * y * r₂⁻¹
  have hconjH : ∀ h ∈ moufangCartan D Γ n t,
      r₂⁻¹ * h * r₂ ∈ moufangCartan D Γ n t := by
    intro h hh
    simpa [r₂, reflTwoL, inv_inv] using moufangCartan_conj_mem (t := t) ht hn hP hT hh
      ((moufangN D Γ n t).inv_mem
        (reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM).2)
  have hactinv := action_two_moufang_inv (t := t) ht hn hP hT hM
  have hdir := action_two_moufang (t := t) ht hn hP hT hM
    (reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM) rfl
  have hzroot : z ∈ rootL (D := D) (Γ := Γ) (n := n) t (n : ℤ) := by
    dsimp [z, r₂]
    exact mem_of_conjBy_inv hactinv.2.1 hy
  have hz1 : z ≠ 1 := by
    intro h
    apply hy1
    have := congrArg (fun w => r₂⁻¹ * w * r₂) h
    simpa [z, mul_assoc] using this
  have hzD : (z : D) ∈ aptRoot D Γ n t (n : ℤ) := by
    have h := Subgroup.mem_subgroupOf.mp hzroot
    simpa only [rootD, if_pos (by omega : (0 : ℤ) < (n : ℤ))] using h
  have hz1D : (z : D) ≠ 1 := fun h => hz1 (Subtype.ext h)
  obtain ⟨v, hv, w, hw, hactm, -⟩ :=
    exists_reflection_apt (t := t) ht hn hP hT hM (i := (n : ℤ)) (u := (z : D)) hzD hz1D
  have hvL : v ∈ littleGroup D Γ n :=
    aptRoot_le_littleGroup ht (by omega) ((n : ℤ) + (n : ℤ)) hv
  have hwL : w ∈ littleGroup D Γ n :=
    aptRoot_le_littleGroup ht (by omega) ((n : ℤ) + (n : ℤ)) hw
  let vL : ↥(littleGroup D Γ n) := ⟨v, hvL⟩
  let wL : ↥(littleGroup D Γ n) := ⟨w, hwL⟩
  have hvroot : vL ∈ rootL (D := D) (Γ := Γ) (n := n) t (-(n : ℤ)) := by
    rw [rootL, Subgroup.mem_subgroupOf, rootD, if_neg (by omega)]
    simpa [vL, show (n : ℤ) - (-(n : ℤ)) = (n : ℤ) + (n : ℤ) by ring] using hv
  have hwroot : wL ∈ rootL (D := D) (Γ := Γ) (n := n) t (-(n : ℤ)) := by
    rw [rootL, Subgroup.mem_subgroupOf, rootD, if_neg (by omega)]
    simpa [wL, show (n : ℤ) - (-(n : ℤ)) = (n : ℤ) + (n : ℤ) by ring] using hw
  let mL : ↥(littleGroup D Γ n) := vL * z * wL
  have hmL : (mL : D) = v * (z : D) * w := by
    simp [mL, vL, wL]
  have hfix : ∀ k : ℤ, ((mL * r₂⁻¹ : ↥(littleGroup D Γ n)) : D) • apt t k = apt t k := by
    intro k
    rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul]
    have hr : (r₂ : D)⁻¹ • apt t k = apt t (2 * (n : ℤ) - k) := by
      dsimp [r₂]
      simpa using reflTwo_inv_smul (t := t) ht hn hP hT hM k
    rw [hr]
    have hm : (mL : D) • apt t (2 * (n : ℤ) - k) =
        apt t (2 * (n : ℤ) - (2 * (n : ℤ) - k)) := by
      rw [hmL]
      simpa using hactm (2 * (n : ℤ) - k)
    rw [hm]
    rw [show 2 * (n : ℤ) - (2 * (n : ℤ) - k) = k by ring]
  have hmemH : mL * r₂⁻¹ ∈ moufangCartan D Γ n t :=
    mem_moufangCartan_of_fix_apartment (t := t) ht hn hP hT hfix
  let hL : ↥(moufangCartan D Γ n t) := ⟨mL * r₂⁻¹, hmemH⟩
  have hm_eq : mL = (hL : ↥(littleGroup D Γ n)) * r₂ := by
    dsimp [hL]
    group
  have hzfac : z = vL⁻¹ * (hL : ↥(littleGroup D Γ n)) * r₂ * wL⁻¹ := by
    have h1 : vL * z * wL = (hL : ↥(littleGroup D Γ n)) * r₂ := by
      rw [← hm_eq]
    calc z = vL⁻¹ * (vL * z * wL) * wL⁻¹ := by group
      _ = vL⁻¹ * ((hL : ↥(littleGroup D Γ n)) * r₂) * wL⁻¹ := by rw [h1]
      _ = vL⁻¹ * (hL : ↥(littleGroup D Γ n)) * r₂ * wL⁻¹ := by group
  have hyfac : y = (r₂⁻¹ * vL⁻¹ * r₂) *
      (r₂⁻¹ * (hL : ↥(littleGroup D Γ n)) * r₂) * r₂ * (r₂⁻¹ * wL⁻¹ * r₂) := by
    calc y = r₂⁻¹ * z * r₂ := by dsimp [z]; group
      _ = r₂⁻¹ * (vL⁻¹ * (hL : ↥(littleGroup D Γ n)) * r₂ * wL⁻¹) * r₂ := by rw [hzfac]
      _ = (r₂⁻¹ * vL⁻¹ * r₂) *
          (r₂⁻¹ * (hL : ↥(littleGroup D Γ n)) * r₂) * r₂ * (r₂⁻¹ * wL⁻¹ * r₂) := by group
  have ha : r₂⁻¹ * vL⁻¹ * r₂ ∈ rootL (D := D) (Γ := Γ) (n := n) t (n : ℤ) := by
    have hmem : r₂⁻¹ * vL⁻¹ * r₂ ∈
        CFSG.GH74.BNPair.conjBy r₂
          (rootL (D := D) (Γ := Γ) (n := n) t (-(n : ℤ))) := by
      rw [CFSG.GH74.BNPair.mem_conjBy_iff]
      simpa [mul_assoc] using Subgroup.inv_mem _ hvroot
    rwa [hdir.2.1] at hmem
  have hb : r₂⁻¹ * wL⁻¹ * r₂ ∈ rootL (D := D) (Γ := Γ) (n := n) t (n : ℤ) := by
    have hmem : r₂⁻¹ * wL⁻¹ * r₂ ∈
        CFSG.GH74.BNPair.conjBy r₂
          (rootL (D := D) (Γ := Γ) (n := n) t (-(n : ℤ))) := by
      rw [CFSG.GH74.BNPair.mem_conjBy_iff]
      simpa [mul_assoc] using Subgroup.inv_mem _ hwroot
    rwa [hdir.2.1] at hmem
  have hhL : r₂⁻¹ * (hL : ↥(littleGroup D Γ n)) * r₂ ∈ moufangCartan D Γ n t :=
    hconjH _ hL.2
  refine Set.mem_mul.2 ⟨(r₂⁻¹ * vL⁻¹ * r₂) *
      (r₂⁻¹ * (hL : ↥(littleGroup D Γ n)) * r₂) * r₂,
    Set.mem_mul.2 ⟨(r₂⁻¹ * vL⁻¹ * r₂) *
        (r₂⁻¹ * (hL : ↥(littleGroup D Γ n)) * r₂),
      Set.mem_mul.2 ⟨r₂⁻¹ * vL⁻¹ * r₂, ha,
        r₂⁻¹ * (hL : ↥(littleGroup D Γ n)) * r₂, hhL, rfl⟩, r₂, rfl, rfl⟩,
    r₂⁻¹ * wL⁻¹ * r₂, hb, hyfac.symm⟩

theorem moufangB_eq_cartan_sup_rootU {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ)
    (hM : MoufangCondition D Γ n) :
    moufangCartan D Γ n t ⊔ rootU (D := D) (Γ := Γ) (n := n) t =
      moufangB D Γ n t := by
  refine le_antisymm ?_ ?_
  · exact sup_le inf_le_left (rootU_le_littleBorel (t := t) ht hn hP hT hM)
  · intro x hx
    have hx' : (x : ↥(littleGroup D Γ n)) ∈
        (moufangCartan D Γ n t : Set ↥(littleGroup D Γ n)) *
          (rootU (D := D) (Γ := Γ) (n := n) t : Set ↥(littleGroup D Γ n)) := by
      rw [← moufangB_eq_cartan_mul_rootU (t := t) ht hn hP hT hM]
      exact hx
    obtain ⟨h, hh, u, hu, rfl⟩ := Set.mem_mul.1 hx'
    exact (moufangCartan D Γ n t ⊔ rootU (D := D) (Γ := Γ) (n := n) t).mul_mem
      (Subgroup.mem_sup_left hh) (Subgroup.mem_sup_right hu)

theorem moufangN_eq_closure {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ)
    (hM : MoufangCondition D Γ n) :
    Subgroup.closure ((moufangCartan D Γ n t : Set ↥(littleGroup D Γ n)) ∪
      {reflOneL (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM,
       reflTwoL (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM}) =
      moufangN D Γ n t := by
  haveI hcart : (cartan (moufangB D Γ n t) (moufangN D Γ n t)).Normal :=
    moufangCartan_normal (t := t) ht hn hP hT
  haveI hH : ((moufangCartan D Γ n t).subgroupOf (moufangN D Γ n t)).Normal := by
    simpa [cartan, moufangCartan] using hcart
  have h₁ : reflOneL (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM ∈ moufangN D Γ n t :=
    (reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM).2
  have h₂ : reflTwoL (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM ∈ moufangN D Γ n t :=
    (reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM).2
  have hq₁ : ((⟨reflOneL (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM, h₁⟩ :
        ↥(moufangN D Γ n t)) :
      WeylGroup (moufangB D Γ n t) (moufangN D Γ n t)) =
      titsW1 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM := by
    change QuotientGroup.mk (⟨reflOneL (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM, h₁⟩ :
      ↥(moufangN D Γ n t)) =
      QuotientGroup.mk (reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM)
    exact congrArg QuotientGroup.mk (Subtype.ext rfl)
  have hq₂ : ((⟨reflTwoL (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM, h₂⟩ :
        ↥(moufangN D Γ n t)) :
      WeylGroup (moufangB D Γ n t) (moufangN D Γ n t)) =
      titsW2 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM := by
    change QuotientGroup.mk (⟨reflTwoL (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM, h₂⟩ :
      ↥(moufangN D Γ n t)) =
      QuotientGroup.mk (reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM)
    exact congrArg QuotientGroup.mk (Subtype.ext rfl)
  have hgen : Subgroup.closure
      ({((⟨reflOneL (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM, h₁⟩ :
            ↥(moufangN D Γ n t)) :
          WeylGroup (moufangB D Γ n t) (moufangN D Γ n t)),
        ((⟨reflTwoL (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM, h₂⟩ :
            ↥(moufangN D Γ n t)) :
          WeylGroup (moufangB D Γ n t) (moufangN D Γ n t))} :
        Set (WeylGroup (moufangB D Γ n t) (moufangN D Γ n t))) = ⊤ := by
    have hset : ({((⟨reflOneL (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM, h₁⟩ :
          ↥(moufangN D Γ n t)) :
        WeylGroup (moufangB D Γ n t) (moufangN D Γ n t)),
      ((⟨reflTwoL (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM, h₂⟩ :
          ↥(moufangN D Γ n t)) :
        WeylGroup (moufangB D Γ n t) (moufangN D Γ n t))} :
        Set (WeylGroup (moufangB D Γ n t) (moufangN D Γ n t))) =
        ({titsW1 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM,
          titsW2 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM} :
          Set (WeylGroup (moufangB D Γ n t) (moufangN D Γ n t))) := by
      rw [hq₁, hq₂]
    rw [hset]
    exact closure_titsW_eq_top (t := t) ht hn hP hT hM
  have hHN : moufangCartan D Γ n t ≤ moufangN D Γ n t := inf_le_right
  exact closure_union_pair_eq_of_quotient_closure_eq_top
    (H := moufangCartan D Γ n t) (N := moufangN D Γ n t) hHN h₁ h₂ hgen

noncomputable def moufangCore {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ)
    (hM : MoufangCondition D Γ n) :
    RGD2Core n (moufangCartan D Γ n t)
      (reflOneL (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM)
      (reflTwoL (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM)
      (rootU (D := D) (Γ := Γ) (n := n) t)
      (rootL (D := D) (Γ := Γ) (n := n) t) := by
  haveI : (cartan (moufangB D Γ n t) (moufangN D Γ n t)).Normal :=
    moufangCartan_normal (t := t) ht hn hP hT
  exact
    { three_le := hn
      conj_H₁ := fun h hh => by
        simpa [reflOneL] using moufangCartan_conj_mem (t := t) ht hn hP hT hh
          (reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM).2
      conj_H₂ := fun h hh => by
        simpa [reflTwoL] using moufangCartan_conj_mem (t := t) ht hn hP hT hh
          (reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM).2
      sq₁ := reflOneL_sq_mem_cartan (t := t) ht hn hP hT hM
      sq₂ := reflTwoL_sq_mem_cartan (t := t) ht hn hP hT hM
      ne_bot := (isRootGroupSystem_moufang (t := t) ht hn hP hT hM).ne_bot
      invariant := (isRootGroupSystem_moufang (t := t) ht hn hP hT hM).invariant
      carrier_eq := (isRootGroupSystem_moufang (t := t) ht hn hP hT hM).carrier_eq
      subgroup := (isRootGroupSystem_moufang (t := t) ht hn hP hT hM).subgroup
      act₁ := action_one_moufang_inv (t := t) ht hn hP hT hM
      act₂ := action_two_moufang_inv (t := t) ht hn hP hT hM
      meet_one := fun x hx hxc =>
        (isRootGroupSystem_moufang (t := t) ht hn hP hT hM).meet_one x
          ((moufangB_eq_cartan_sup_rootU (t := t) ht hn hP hT hM) ▸ hx) hxc
      rank₁ := fun y hy hy1 => rank_one_moufang (t := t) ht hn hP hT hM hy hy1
      rank₂ := fun y hy hy1 => rank_two_moufang (t := t) ht hn hP hT hM hy hy1 }

theorem moufang_t3_one {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ)
    (hM : MoufangCondition D Γ n) [(cartan (moufangB D Γ n t) (moufangN D Γ n t)).Normal]
    (x : ↥(moufangN D Γ n t)) :
    ({reflOneL (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM} :
        Set ↥(littleGroup D Γ n)) *
      (moufangB D Γ n t : Set ↥(littleGroup D Γ n)) * {(x : ↥(littleGroup D Γ n))} ⊆
      dc (moufangB D Γ n t) (moufangN D Γ n t)
        ((QuotientGroup.mk (reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM) :
            ↥(moufangN D Γ n t) ⧸ cartan (moufangB D Γ n t) (moufangN D Γ n t)) *
          (QuotientGroup.mk x :
            ↥(moufangN D Γ n t) ⧸ cartan (moufangB D Γ n t) (moufangN D Γ n t))) ∪
      dc (moufangB D Γ n t) (moufangN D Γ n t)
        (x : WeylGroup (moufangB D Γ n t) (moufangN D Γ n t)) := by
  have hcore := moufangCore (t := t) ht hn hP hT hM
  have hB := moufangB_eq_cartan_sup_rootU (t := t) ht hn hP hT hM
  have hN := moufangN_eq_closure (t := t) ht hn hP hT hM
  have hxR : (x : ↥(littleGroup D Γ n)) ∈ hcore.N := by
    change (x : ↥(littleGroup D Γ n)) ∈
      Subgroup.closure ((moufangCartan D Γ n t : Set ↥(littleGroup D Γ n)) ∪
        {reflOneL (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM,
         reflTwoL (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM})
    rw [hN]
    exact x.2
  have hset := RGD2.t3_set (x : ↥(littleGroup D Γ n)) (hcore.t3_r₁ _ hxR)
  have hset' : ({reflOneL (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM} :
        Set ↥(littleGroup D Γ n)) *
      (moufangB D Γ n t : Set ↥(littleGroup D Γ n)) * {(x : ↥(littleGroup D Γ n))} ⊆
      (moufangB D Γ n t : Set ↥(littleGroup D Γ n)) *
        {reflOneL (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM *
          (x : ↥(littleGroup D Γ n))} *
        (moufangB D Γ n t : Set ↥(littleGroup D Γ n)) ∪
      (moufangB D Γ n t : Set ↥(littleGroup D Γ n)) *
        {(x : ↥(littleGroup D Γ n))} *
        (moufangB D Γ n t : Set ↥(littleGroup D Γ n)) := by
    rw [← hB]
    exact hset
  refine Set.Subset.trans hset' (Set.union_subset ?_ ?_)
  · intro y hy
    refine Or.inl ((mem_dc_of_lift (n := reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM * x)
      (hn := by dsimp [titsW1])).2 ?_)
    · have hcoe : ((reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM * x :
          ↥(moufangN D Γ n t)) : ↥(littleGroup D Γ n)) =
          reflOneL (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM *
            (x : ↥(littleGroup D Γ n)) := by
        rw [Subgroup.coe_mul]
      rw [hcoe]
      exact mem_dcoset_iff.1 hy
  · intro y hy
    exact Or.inr ((mem_dc_of_lift (n := x) rfl).2 (mem_dcoset_iff.1 hy))

theorem moufang_t3_two {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ)
    (hM : MoufangCondition D Γ n) [(cartan (moufangB D Γ n t) (moufangN D Γ n t)).Normal]
    (x : ↥(moufangN D Γ n t)) :
    ({reflTwoL (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM} :
        Set ↥(littleGroup D Γ n)) *
      (moufangB D Γ n t : Set ↥(littleGroup D Γ n)) * {(x : ↥(littleGroup D Γ n))} ⊆
      dc (moufangB D Γ n t) (moufangN D Γ n t)
        ((QuotientGroup.mk (reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM) :
            ↥(moufangN D Γ n t) ⧸ cartan (moufangB D Γ n t) (moufangN D Γ n t)) *
          (QuotientGroup.mk x :
            ↥(moufangN D Γ n t) ⧸ cartan (moufangB D Γ n t) (moufangN D Γ n t))) ∪
      dc (moufangB D Γ n t) (moufangN D Γ n t)
        (x : WeylGroup (moufangB D Γ n t) (moufangN D Γ n t)) := by
  have hcore := moufangCore (t := t) ht hn hP hT hM
  have hB := moufangB_eq_cartan_sup_rootU (t := t) ht hn hP hT hM
  have hN := moufangN_eq_closure (t := t) ht hn hP hT hM
  have hxR : (x : ↥(littleGroup D Γ n)) ∈ hcore.N := by
    change (x : ↥(littleGroup D Γ n)) ∈
      Subgroup.closure ((moufangCartan D Γ n t : Set ↥(littleGroup D Γ n)) ∪
        {reflOneL (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM,
         reflTwoL (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM})
    rw [hN]
    exact x.2
  have hset := RGD2.t3_set (x : ↥(littleGroup D Γ n)) (hcore.t3_r₂ _ hxR)
  have hset' : ({reflTwoL (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM} :
        Set ↥(littleGroup D Γ n)) *
      (moufangB D Γ n t : Set ↥(littleGroup D Γ n)) * {(x : ↥(littleGroup D Γ n))} ⊆
      (moufangB D Γ n t : Set ↥(littleGroup D Γ n)) *
        {reflTwoL (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM *
          (x : ↥(littleGroup D Γ n))} *
        (moufangB D Γ n t : Set ↥(littleGroup D Γ n)) ∪
      (moufangB D Γ n t : Set ↥(littleGroup D Γ n)) *
        {(x : ↥(littleGroup D Γ n))} *
        (moufangB D Γ n t : Set ↥(littleGroup D Γ n)) := by
    rw [← hB]
    exact hset
  refine Set.Subset.trans hset' (Set.union_subset ?_ ?_)
  · intro y hy
    refine Or.inl ((mem_dc_of_lift (n := reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM * x)
      (hn := by dsimp [titsW2])).2 ?_)
    · have hcoe : ((reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM * x :
          ↥(moufangN D Γ n t)) : ↥(littleGroup D Γ n)) =
          reflTwoL (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM *
            (x : ↥(littleGroup D Γ n)) := by
        rw [Subgroup.coe_mul]
      rw [hcoe]
      exact mem_dcoset_iff.1 hy
  · intro y hy
    exact Or.inr ((mem_dc_of_lift (n := x) rfl).2 (mem_dcoset_iff.1 hy))

theorem moufang_hne_one {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ)
    (hM : MoufangCondition D Γ n) :
    ¬ ({reflOneL (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM} :
        Set ↥(littleGroup D Γ n)) *
      (moufangB D Γ n t : Set ↥(littleGroup D Γ n)) *
      {(reflOneL (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM)⁻¹} ⊆
      (moufangB D Γ n t : Set ↥(littleGroup D Γ n)) := by
  have h := (moufangCore (t := t) ht hn hP hT hM).t4_r₁
  rw [moufangB_eq_cartan_sup_rootU (t := t) ht hn hP hT hM] at h
  exact h

theorem moufang_hne_two {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ)
    (hM : MoufangCondition D Γ n) :
    ¬ ({reflTwoL (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM} :
        Set ↥(littleGroup D Γ n)) *
      (moufangB D Γ n t : Set ↥(littleGroup D Γ n)) *
      {(reflTwoL (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM)⁻¹} ⊆
      (moufangB D Γ n t : Set ↥(littleGroup D Γ n)) := by
  have h := (moufangCore (t := t) ht hn hP hT hM).t4_r₂
  rw [moufangB_eq_cartan_sup_rootU (t := t) ht hn hP hT hM] at h
  exact h

open Classical in
theorem isTitsSystem_moufang {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ)
    (hM : MoufangCondition D Γ n) :
    letI : (cartan (moufangB D Γ n t) (moufangN D Γ n t)).Normal :=
      moufangCartan_normal (t := t) ht hn hP hT
    IsTitsSystem (moufangB D Γ n t) (moufangN D Γ n t)
      {titsW1 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM,
       titsW2 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM} := by
  letI : (cartan (moufangB D Γ n t) (moufangN D Γ n t)).Normal :=
    moufangCartan_normal (t := t) ht hn hP hT
  have hgen := moufangB_sup_moufangN_eq_top (t := t) ht hn hP hT hM
  have hord : ∀ i : Fin 2,
      orderOf ((![reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM,
        reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM] i : ↥(moufangN D Γ n t)) :
        WeylGroup (moufangB D Γ n t) (moufangN D Γ n t)) = 2 := by
    intro i
    fin_cases i
    · simpa [titsW1_eq_mk] using orderOf_titsW1 (t := t) ht hn hP hT hM
    · simpa [titsW2_eq_mk] using orderOf_titsW2 (t := t) ht hn hP hT hM
  have hclos : Subgroup.closure (Set.range fun i : Fin 2 =>
      ((![reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM,
        reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM] i :
        ↥(moufangN D Γ n t)) :
        WeylGroup (moufangB D Γ n t) (moufangN D Γ n t))) = ⊤ := by
    have hset : Set.range (fun i : Fin 2 =>
        ((![reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM,
          reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM] i :
          ↥(moufangN D Γ n t)) :
          WeylGroup (moufangB D Γ n t) (moufangN D Γ n t))) =
        ({titsW1 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM,
          titsW2 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM} :
          Set (WeylGroup (moufangB D Γ n t) (moufangN D Γ n t))) := by
      ext s
      constructor
      · rintro ⟨i, rfl⟩
        fin_cases i
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
    rw [hset]
    exact closure_titsW_eq_top (t := t) ht hn hP hT hM
  have hmul : ∀ i : Fin 2, ∀ x : ↥(moufangN D Γ n t),
      ({((![reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM,
          reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM] i :
          ↥(moufangN D Γ n t)) : ↥(littleGroup D Γ n))} :
        Set ↥(littleGroup D Γ n)) *
        (moufangB D Γ n t : Set ↥(littleGroup D Γ n)) *
        {(x : ↥(littleGroup D Γ n))} ⊆
        dc (moufangB D Γ n t) (moufangN D Γ n t)
          (((![reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM,
            reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM] i :
            ↥(moufangN D Γ n t)) :
            WeylGroup (moufangB D Γ n t) (moufangN D Γ n t)) *
            (x : WeylGroup (moufangB D Γ n t) (moufangN D Γ n t))) ∪
        dc (moufangB D Γ n t) (moufangN D Γ n t)
          (x : WeylGroup (moufangB D Γ n t) (moufangN D Γ n t)) := by
    intro i x
    fin_cases i
    · simpa [titsW1_eq_mk] using moufang_t3_one (t := t) ht hn hP hT hM x
    · simpa [titsW2_eq_mk] using moufang_t3_two (t := t) ht hn hP hT hM x
  have hne : ∀ i : Fin 2,
      ¬ ({((![reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM,
          reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM] i :
          ↥(moufangN D Γ n t)) : ↥(littleGroup D Γ n))} :
        Set ↥(littleGroup D Γ n)) *
        (moufangB D Γ n t : Set ↥(littleGroup D Γ n)) *
        {((![reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM,
          reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM] i :
          ↥(moufangN D Γ n t)) : ↥(littleGroup D Γ n))⁻¹} ⊆
        (moufangB D Γ n t : Set ↥(littleGroup D Γ n)) := by
    intro i
    fin_cases i
    · simpa using moufang_hne_one (t := t) ht hn hP hT hM
    · simpa using moufang_hne_two (t := t) ht hn hP hT hM
  exact CFSG.GH74.GLS.SP.RGD2Core.isTitsSystem_of_two_generators
    (n₁ := reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM)
    (n₂ := reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM)
    hgen hord hclos hmul hne
