module

import Mathlib.Tactic.IrreducibleDef
public import CFSG.Sporadic.J4.Group
public import CFSG.Sporadic.Th.OrbitSpec
public import CFSG.Sporadic.Th.TableSpec

public section

namespace CFSG.Sporadic.J4

open Native Matrix CFSG.Sporadic.Th

@[expose] def Row : Type := Fin 112 → ZMod 2

@[expose] def toRow (w : Fin 112 → ZMod 2) : Row := w

@[expose] def ofRow (w : Row) : Fin 112 → ZMod 2 := w

noncomputable instance rowAction : MulAction J Row where
  smul g w := toRow (ofRow w ᵥ* (((g⁻¹ : J) : GL (Fin 112) (ZMod 2)) :
    Matrix (Fin 112) (Fin 112) (ZMod 2)))
  one_smul w := by
    show toRow (ofRow w ᵥ* (((1⁻¹ : J) : GL (Fin 112) (ZMod 2)) :
      Matrix (Fin 112) (Fin 112) (ZMod 2))) = w
    rw [inv_one, OneMemClass.coe_one, Units.val_one, Matrix.vecMul_one]; rfl
  mul_smul g h w := by
    show toRow (ofRow w ᵥ* ((((g * h)⁻¹ : J) : GL (Fin 112) (ZMod 2)) :
      Matrix (Fin 112) (Fin 112) (ZMod 2))) =
      toRow (ofRow (toRow (ofRow w ᵥ* (((h⁻¹ : J) : GL (Fin 112) (ZMod 2)) :
        Matrix (Fin 112) (Fin 112) (ZMod 2)))) ᵥ* (((g⁻¹ : J) : GL (Fin 112) (ZMod 2)) :
          Matrix (Fin 112) (Fin 112) (ZMod 2)))
    rw [_root_.mul_inv_rev, Subgroup.coe_mul, Units.val_mul, ← Matrix.vecMul_vecMul]; rfl

theorem smul_row (g : J) (w : Row) :
    ofRow (g • w) = ofRow w ᵥ* (((g⁻¹ : J) : GL (Fin 112) (ZMod 2)) :
      Matrix (Fin 112) (Fin 112) (ZMod 2)) := rfl

theorem inv_smul_row (g : J) (w : Row) :
    ofRow (g⁻¹ • w) = ofRow w ᵥ* ((g : GL (Fin 112) (ZMod 2)) :
      Matrix (Fin 112) (Fin 112) (ZMod 2)) := by
  rw [smul_row, inv_inv]

theorem ofRow_inj {v w : Row} : ofRow v = ofRow w ↔ v = w := Iff.rfl

noncomputable irreducible_def bs0 : BFSState := bfs (frTable rowsA) (frTable rowsB) rootV nPts

@[expose] noncomputable def vecAt (i : ℕ) : Row := toRow (rdV2 bs0.keys i).toVec

structure OrbitFacts : Prop where
  count : bs0.count = nPts
  ok : orbitOK (frTable rowsA) (frTable rowsB) rootV bs0 nPts 3 = true
  mat : MatFacts

section Orbit

variable (hO : OrbitFacts)
include hO

theorem orbit_parts : 0 < nPts ∧ nPts < 2 ^ 28 ∧ rdV2 bs0.keys 0 = rootV ∧
    ∀ i < nPts, orbitCheckAt (frTable rowsA) (frTable rowsB) bs0 nPts i = true := by
  have h := hO.ok
  unfold orbitOK at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_iff,
    decide_eq_true_iff, V2.beq_iff] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, fun i hi => parAllS_eq_true h.2 i hi⟩

theorem check_parts {i : ℕ} (hi : i < nPts) :
    (rdV2 bs0.keys i).wf = true ∧ findIdx bs0.keys bs0.slots (rdV2 bs0.keys i) = i + 1 ∧
      rdU32 bs0.alpha i < nPts ∧ rdU32 bs0.beta i < nPts ∧
      rdV2 bs0.keys (rdU32 bs0.alpha i) = frApply (frTable rowsA) (rdV2 bs0.keys i) ∧
      rdV2 bs0.keys (rdU32 bs0.beta i) = frApply (frTable rowsB) (rdV2 bs0.keys i) := by
  have h := (orbit_parts hO).2.2.2 i hi
  unfold orbitCheckAt at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, V2.beq_iff] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem vecAt_injective {i j : ℕ} (hi : i < nPts) (hj : j < nPts) (h : vecAt i = vecAt j) :
    i = j := by
  have hi' := check_parts hO hi
  have hj' := check_parts hO hj
  have e : rdV2 bs0.keys i = rdV2 bs0.keys j := V2.eq_of_toVec_eq hi'.1 hj'.1 h
  have := hi'.2.1
  rw [e, hj'.2.1] at this
  omega

theorem vecAt_zero : vecAt 0 = toRow rootV.toVec := by
  unfold vecAt; rw [(orbit_parts hO).2.2.1]

theorem a_inv_smul_vecAt {i : ℕ} (hi : i < nPts) :
    (a⁻¹ : J) • vecAt i = vecAt (rdU32 bs0.alpha i) := by
  rw [← ofRow_inj, inv_smul_row, a_coe, gA_val hO.mat, vecAt, vecAt,
    (check_parts hO hi).2.2.2.2.1, frApply_toVec_eq_vecMul, rowsMatrix_rowsA]
  rfl

theorem b_inv_smul_vecAt {i : ℕ} (hi : i < nPts) :
    (b⁻¹ : J) • vecAt i = vecAt (rdU32 bs0.beta i) := by
  rw [← ofRow_inj, inv_smul_row, b_coe, gB_val hO.mat, vecAt, vecAt,
    (check_parts hO hi).2.2.2.2.2, frApply_toVec_eq_vecMul, rowsMatrix_rowsB]
  rfl

end Orbit

theorem closure_inv_ab : Subgroup.closure ({a⁻¹, b⁻¹} : Set J) = ⊤ := by
  rw [eq_top_iff, ← closure_ab, Subgroup.closure_le]
  have ha : a⁻¹ ∈ Subgroup.closure ({a⁻¹, b⁻¹} : Set J) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hb : b⁻¹ ∈ Subgroup.closure ({a⁻¹, b⁻¹} : Set J) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  rintro _ (rfl | rfl)
  · exact (Subgroup.inv_mem_iff _).1 ha
  · exact (Subgroup.inv_mem_iff _).1 hb

noncomputable abbrev ptSet : Set Row := vecAt '' Set.Iio nPts

theorem smul_mem_ptSet (hO : OrbitFacts) (g : J) : ∀ v ∈ ptSet, g • v ∈ ptSet := by
  refine smul_mem_of_closure closure_inv_ab ((Set.finite_Iio nPts).image _) ?_ ?_ g
  · rintro _ ⟨i, hi, rfl⟩
    exact ⟨_, (check_parts hO hi).2.2.1, (a_inv_smul_vecAt hO hi).symm⟩
  · rintro _ ⟨i, hi, rfl⟩
    exact ⟨_, (check_parts hO hi).2.2.2.1, (b_inv_smul_vecAt hO hi).symm⟩

@[expose] noncomputable def ptSub (hO : OrbitFacts) : SubMulAction J Row where
  carrier := ptSet
  smul_mem' g _ hv := smul_mem_ptSet hO g _ hv

@[expose] noncomputable def ptEquiv (hO : OrbitFacts) : Fin nPts ≃ ptSub hO :=
  Equiv.ofBijective (fun i => ⟨vecAt i, ⟨i, i.isLt, rfl⟩⟩)
    ⟨fun i j h => Fin.ext (vecAt_injective hO i.isLt j.isLt (congrArg Subtype.val h)), by
      rintro ⟨v, ⟨i, hi, rfl⟩⟩
      exact ⟨⟨i, hi⟩, rfl⟩⟩

theorem ptEquiv_apply (hO : OrbitFacts) (i : Fin nPts) : (ptEquiv hO i : Row) = vecAt i := rfl

noncomputable instance idxAction : MulAction J (Fin nPts) where
  smul g i := by
    classical
    exact if h : OrbitFacts then (ptEquiv h).symm (g • ptEquiv h i) else i
  one_smul i := by
    classical
    show (if h : OrbitFacts then (ptEquiv h).symm ((1 : J) • ptEquiv h i) else i) = i
    split
    · rw [one_smul, Equiv.symm_apply_apply]
    · rfl
  mul_smul g h i := by
    classical
    show (if hF : OrbitFacts then (ptEquiv hF).symm ((g * h) • ptEquiv hF i) else i) =
      (if hF : OrbitFacts then (ptEquiv hF).symm (g • ptEquiv hF
        (if hF : OrbitFacts then (ptEquiv hF).symm (h • ptEquiv hF i) else i)) else
        (if hF : OrbitFacts then (ptEquiv hF).symm (h • ptEquiv hF i) else i))
    split
    · rw [Equiv.apply_symm_apply, mul_smul]
    · rfl

section Idx

variable (hO : OrbitFacts)
include hO

theorem ptEquiv_smul (g : J) (i : Fin nPts) : ptEquiv hO (g • i) = g • ptEquiv hO i := by
  have : (g • i : Fin nPts) = (ptEquiv hO).symm (g • ptEquiv hO i) := by
    classical
    show (if h : OrbitFacts then (ptEquiv h).symm (g • ptEquiv h i) else i) = _
    rw [dite_eq_left hO]
  rw [this, Equiv.apply_symm_apply]

theorem vecAt_smul (g : J) (i : Fin nPts) : vecAt (g • i : Fin nPts) = g • vecAt i := by
  have := congrArg Subtype.val (ptEquiv_smul hO g i)
  simpa [ptEquiv_apply] using this

theorem idx_eq_iff {g : J} {i j : ℕ} (hi : i < nPts) (hj : j < nPts) :
    idx nPts g i = j ↔ g • vecAt i = vecAt j := by
  rw [idx, dite_eq_left hi]
  constructor
  · intro h
    have := vecAt_smul hO g ⟨i, hi⟩
    rw [h] at this
    exact this.symm
  · intro h
    have e := vecAt_smul hO g ⟨i, hi⟩
    rw [h] at e
    exact vecAt_injective hO (g • (⟨i, hi⟩ : Fin nPts)).isLt hj e

@[expose] def RepB (t : ByteArray) (g : J) : Prop := ∀ i < nPts, rdU32 t i = idx nPts g i

theorem repB_of_vec {t : ByteArray} {g : J} (h : ∀ i < nPts, rdU32 t i < nPts ∧
    g • vecAt i = vecAt (rdU32 t i)) : RepB t g := by
  intro i hi
  exact ((idx_eq_iff hO hi (h i hi).1).2 (h i hi).2).symm

theorem rep_alpha : RepB bs0.alpha a⁻¹ :=
  repB_of_vec hO fun _ hi => ⟨(check_parts hO hi).2.2.1, a_inv_smul_vecAt hO hi⟩

theorem rep_beta : RepB bs0.beta b⁻¹ :=
  repB_of_vec hO fun _ hi => ⟨(check_parts hO hi).2.2.2.1, b_inv_smul_vecAt hO hi⟩

end Idx

end CFSG.Sporadic.J4
