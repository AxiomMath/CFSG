module

public import CFSG.Sporadic.ThSchreier.PlaneStabilizerBase1

public import CFSG.Sporadic.ThSchreier.OrbitCheck819
public import CFSG.Sporadic.ThSchreier.PlaneFacts
public meta import CFSG.Sporadic.ThSchreier.Transporter
public meta import CFSG.Sporadic.ThSchreier.UASpace
public import Certificates.Certificate2320
public import CFSG.Sporadic.ThSchreier.GlobalData
public import CFSG.Sporadic.Th.Simple
public meta import CFSG.Sporadic.ThSchreier.Row
public meta import CFSG.Sporadic.ThSchreier.LocalOrbit
public import CFSG.Sporadic.ThSchreier.LocalOrbitInputs
public meta import CFSG.Sporadic.ThSchreier.Words
public meta import CFSG.Sporadic.ThSchreier.LocalData
public import CFSG.Sporadic.ThSchreier.OrbitCheck819Inputs
public import CFSG.Sporadic.ThSchreier.RowInputs
public meta import Certificates.Data.CFSGNative.Th.Base
public import CFSG.Sporadic.ThSchreier.UASpaceInputs
public meta import CFSG.Sporadic.ThSchreier.CentralizerData
public import CFSG.Sporadic.Th.Plane
public import CFSG.Sporadic.Th.FormBase
public import Certificates.Data.CFSGNative.Th.Base
public import Mathlib
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Certificates.SchreierStabilizerGenerators
public import Certificates.Data.CFSGNative.Th.Certificate
public import CFSG.Sporadic.Th.Max3.Data
public import CFSG.Sporadic.Th.KernelPlanes

public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 Pointwise

private theorem native_star_inUA : inUA starKey.u = true ∧ inUA starKey.v = true :=
  Certificates.certificate2320

theorem planeStar_subset_planeUA : planeStar ⊆ (planeUA : Set RowV) := by
  rw [planeStar_eq_rowPlane, rowPlane_subset_planeUA_iff]
  exact native_star_inUA

theorem involT_smul_planeWSet : involT • planeWSet = planeWSet := by
  have h := a_smul_plane_of_subset planeStar_subset_planeUA
  rw [planeStar] at h
  rw [involT, mul_smul, mul_smul, h, inv_smul_smul]

theorem involT_mem_H {c : ℕ} (hC : CertFacts c) : involT ∈ localH := by
  rw [localH_eq, ← stabilizer_planeWSet hC]
  exact involT_smul_planeWSet

theorem isRows_conjRowsH (l : ℕ) {E : Array V4} {g : J} (hE : IsRows E g) :
    IsRows (conjRowsH l E) (labGenH l * g * (labGenH l)⁻¹) := by
  unfold conjRowsH labGenH
  split_ifs
  · exact (isRows_localX.mul hE).mul isRows_localX_inv
  · exact (isRows_localY.mul hE).mul isRows_localY_inv

theorem isRows_orbRows (i : ℕ) : IsRows (orbRows i) (orbElem i) := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rw [orbRows, orbElem]
    split_ifs with h
    · exact isRows_conjRowsH _ (ih _ h.2)
    · exact isRows_rowsT

theorem orbit_parts :
    (∀ i < 819, (i = 0 ∨ (orbPar i < i ∧ (orbLab i = 1 ∨ orbLab i = 2))) ∧
      orbEdge i 1 < 819 ∧ orbEdge i 2 < 819 ∧
      eqRows (conjRowsH 1 (orbRows i)) (orbRows (orbEdge i 1)) = true ∧
      eqRows (conjRowsH 2 (orbRows i)) (orbRows (orbEdge i 2)) = true) ∧
    (∀ i < 819, ∀ j < i, eqRows (orbRows i) (orbRows j) = false) := by
  have h := orbit_facts
  unfold orbitChecks at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨-, h1⟩, h2⟩ := h
  refine ⟨fun i hi => ?_, fun i hi j hj => ?_⟩
  · obtain ⟨⟨⟨⟨hr, he1⟩, he2⟩, hc1⟩, hc2⟩ := h1 i hi
    rw [orbTable_getElem hi, orbTable_getElem he1] at hc1
    rw [orbTable_getElem hi, orbTable_getElem he2] at hc2
    exact ⟨hr, he1, he2, hc1, hc2⟩
  · have := h2 i hi j hj
    rwa [orbTable_getElem hi, orbTable_getElem (lt_trans hj hi)] at this

theorem orbElem_mem_conj {i : ℕ} (hi : i < 819) :
    ∃ h ∈ localH, orbElem i = h * involT * h⁻¹ := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rcases (orbit_parts.1 i hi).1 with rfl | ⟨hp, hl⟩
    · exact ⟨1, localH.one_mem, by rw [orbElem_zero]; group⟩
    · obtain ⟨h, hh, he⟩ := ih _ hp (by omega)
      have hg : labGenH (orbLab i) ∈ localH := by
        unfold labGenH
        split_ifs
        · exact localX_mem_H
        · exact localY_mem_H
      refine ⟨labGenH (orbLab i) * h, localH.mul_mem hg hh, ?_⟩
      rw [orbElem, dite_eq_left ⟨by omega, hp⟩, he]
      group

theorem conj_orbElem {i : ℕ} (hi : i < 819) :
    localX * orbElem i * localX⁻¹ = orbElem (orbEdge i 1) ∧
      localY * orbElem i * localY⁻¹ = orbElem (orbEdge i 2) := by
  obtain ⟨-, -, -, hc1, hc2⟩ := orbit_parts.1 i hi
  have e1 := (isRows_conjRowsH 1 (isRows_orbRows i)).eq_of_eqRows (isRows_orbRows _) hc1
  have e2 := (isRows_conjRowsH 2 (isRows_orbRows i)).eq_of_eqRows (isRows_orbRows _) hc2
  simp only [labGenH, ite_true, show (2 : ℕ) ≠ 1 by decide, ite_false] at e1 e2
  exact ⟨e1, e2⟩

theorem orbElem_injOn : Set.InjOn orbElem (Finset.range 819 : Set ℕ) := by
  intro i hi j hj hij
  simp only [Finset.coe_range, Set.mem_Iio] at hi hj
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact (isRows_orbRows j).ne_of_eqRows (isRows_orbRows i) (orbit_parts.2 j hj i h) hij.symm
  · exact (isRows_orbRows i).ne_of_eqRows (isRows_orbRows j) (orbit_parts.2 i hi j h) hij

theorem conj_mem_orbSet {g : J} (hg : g ∈ orbSet) :
    localX * g * localX⁻¹ ∈ orbSet ∧ localY * g * localY⁻¹ ∈ orbSet := by
  obtain ⟨i, hi, rfl⟩ := hg
  simp only [Finset.coe_range, Set.mem_Iio] at hi
  obtain ⟨-, he1, he2, -, -⟩ := orbit_parts.1 i hi
  rw [(conj_orbElem hi).1, (conj_orbElem hi).2]
  exact ⟨⟨_, by simpa using he1, rfl⟩, ⟨_, by simpa using he2, rfl⟩⟩

theorem conj_involT_eq : {g : J | ∃ h ∈ localH, g = h * involT * h⁻¹} = orbSet := by
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩
    rw [localH] at hh
    induction hh using Subgroup.closure_induction_left with
    | one => exact ⟨0, by simp, by rw [orbElem_zero]; group⟩
    | mul_left x hx y _ ih =>
      have e : x * y * involT * (x * y)⁻¹ = x * (y * involT * y⁻¹) * x⁻¹ := by group
      rw [e]
      rcases hx with rfl | rfl
      · exact (conj_mem_orbSet ih).1
      · exact (conj_mem_orbSet ih).2
    | inv_mul_cancel x hx y _ ih =>
      have e : x⁻¹ * y * involT * (x⁻¹ * y)⁻¹ = x⁻¹ * (y * involT * y⁻¹) * x⁻¹⁻¹ := by group
      rw [e]
      rcases hx with rfl | rfl
      · rw [show localX⁻¹ = localX from inv_eq_of_mul_eq_one_right localX_mul_self]
        exact (conj_mem_orbSet ih).1
      · have hy : localY⁻¹ = localY * localY :=
          inv_eq_of_mul_eq_one_right (by rw [← mul_assoc]; exact localY_cube)
        rw [hy]
        have e2 : localY * localY * (y * involT * y⁻¹) * (localY * localY)⁻¹ =
            localY * (localY * (y * involT * y⁻¹) * localY⁻¹) * localY⁻¹ := by group
        rw [e2]
        exact (conj_mem_orbSet (conj_mem_orbSet ih).2).2
  · rintro ⟨i, hi, rfl⟩
    simp only [Finset.coe_range, Set.mem_Iio] at hi
    exact orbElem_mem_conj hi

theorem ncard_conj_involT : {g : J | ∃ h ∈ localH, g = h * involT * h⁻¹}.ncard = 819 := by
  rw [conj_involT_eq, orbSet, orbElem_injOn.ncard_image, Set.ncard_coe_finset,
    Finset.card_range]

theorem card_centralizer_involT {c : ℕ} (hC : CertFacts c) :
    Nat.card (Subgroup.centralizer {involT} ⊓ localH : Subgroup J) = 774144 := by
  let _ : MulAction localH J := MulAction.compHom J ((MulAut.conj (G := J)).comp localH.subtype)
  have hsmul : ∀ (h : localH) (g : J), h • g = (h : J) * g * (h : J)⁻¹ := fun _ _ => rfl
  have horb : MulAction.orbit localH involT = {g : J | ∃ h ∈ localH, g = h * involT * h⁻¹} := by
    ext g
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨h, h.2, hsmul h involT⟩
    · rintro ⟨h, hh, rfl⟩
      exact ⟨⟨h, hh⟩, hsmul ⟨h, hh⟩ involT⟩
  have hstab : MulAction.stabilizer localH involT =
      (Subgroup.centralizer {involT}).subgroupOf localH := by
    ext h
    rw [MulAction.mem_stabilizer_iff, hsmul, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro e
      calc (h : J) * involT = (h : J) * involT * (h : J)⁻¹ * h := by group
        _ = involT * h := by rw [e]
    · intro e
      rw [e]
      group
  have h1 := MulAction.index_stabilizer localH involT
  rw [hstab, horb, ncard_conj_involT] at h1
  have hH : Nat.card localH = 634023936 := by rw [localH_eq]; exact card_H hC
  have h2 := Subgroup.card_mul_index ((Subgroup.centralizer {involT}).subgroupOf localH)
  rw [h1, hH] at h2
  have h3 : Nat.card ((Subgroup.centralizer {involT}).subgroupOf localH) = 774144 :=
    Nat.eq_of_mul_eq_mul_right (by norm_num) (h2.trans (by norm_num))
  rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective localH.subtype_injective]
  exact h3

end CFSG.Sporadic.ThSchreier
