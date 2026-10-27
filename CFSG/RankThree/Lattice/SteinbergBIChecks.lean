module

public import CFSG.RankThree.Lattice.SteinbergBIRoots
public import CFSG.LieType.Chevalley.LangRootArithmeticDet
public import CFSG.RankThree.Lattice.SteinbergBIOrbitLattice

public section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley Matrix

variable {n : ℕ}

@[expose] def lneq (n : ℕ) (A B : List (List ℤ)) : Bool :=
  (List.finRange n).any fun i => (List.finRange n).any fun j => lget A i j != lget B i j

theorem toMat_ne_of_lneq {A B : List (List ℤ)} (h : lneq n A B = true) : toMat n A ≠ toMat n B := by
  intro hAB
  simp only [lneq, List.any_eq_true, List.mem_finRange, true_and, bne_iff_ne, ne_eq] at h
  obtain ⟨i, j, hij⟩ := h
  exact hij (congrFun (congrFun hAB i) j)

theorem orderOf_toMat_eq {A : List (List ℤ)} {m : ℕ} (hm : 0 < m) (hpow : lpow n A m = lid n)
    (hne : ∀ d ∈ List.range m, 0 < d → lneq n (lpow n A d) (lid n) = true) :
    orderOf (toMat n A) = m := by
  rw [orderOf_eq_iff hm]
  refine ⟨by rw [← toMat_lpow, hpow, toMat_lid], fun d hd hd0 => ?_⟩
  rw [← toMat_lpow, ← toMat_lid]
  exact toMat_ne_of_lneq (hne d (List.mem_range.2 hd) hd0)

@[expose] def lorbit (n : ℕ) (A : List (List ℤ)) (x : List ℤ) (m : ℕ) : List (List ℤ) :=
  (List.range m).map fun j => lmulVec n (lpow n A j) x

theorem toVec_lorbit_getD {A : List (List ℤ)} {x : List ℤ} {m j : ℕ} (hj : j < m) :
    toVec n ((lorbit n A x m).getD j []) = (toMat n A ^ j) *ᵥ toVec n x := by
  rw [lorbit, List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getElem_range,
    toVec_lmulVec, toMat_lpow]

theorem orbitMat_eq_toMat (A : List (List ℤ)) (x : List ℤ) :
    orbitMat (toMat n A) (toVec n x) n = toMat n (lcols n (lorbit n A x n)) := by
  rw [toMat_lcols]
  ext i j
  simp only [orbitMat, Matrix.of_apply]
  rw [toVec_lorbit_getD j.isLt]

theorem mem_powOrbit_iff {w : Matrix (Fin n) (Fin n) ℤ} {m : ℕ} (hm : 0 < m) (hw : w ^ m = 1)
    (x v : Fin n → ℤ) : (∃ j : ℕ, v = (w ^ j) *ᵥ x) ↔ ∃ j < m, v = (w ^ j) *ᵥ x := by
  constructor
  · rintro ⟨j, rfl⟩
    refine ⟨j % m, Nat.mod_lt _ hm, ?_⟩
    conv_lhs => rw [← Nat.div_add_mod j m, pow_add, pow_mul, hw, one_pow, one_mul]
  · rintro ⟨j, -, rfl⟩
    exact ⟨j, rfl⟩

theorem toVec_injective_of_length {u v : List ℤ} (hu : u.length = n) (hv : v.length = n)
    (h : toVec n u = toVec n v) : u = v := by
  rw [← ofFn_toVec hu, ← ofFn_toVec hv, h]

theorem length_lmulVec (A : List (List ℤ)) (x : List ℤ) : (lmulVec n A x).length = n := by
  simp [lmulVec, vofFn]

theorem ncard_powOrbit {A : List (List ℤ)} {x : List ℤ} {m : ℕ} (hm : 0 < m)
    (hw : toMat n A ^ m = 1) (hnd : (lorbit n A x m).Nodup) :
    {v | ∃ j : ℕ, v = (toMat n A ^ j) *ᵥ toVec n x}.ncard = m := by
  classical
  have hset : {v | ∃ j : ℕ, v = (toMat n A ^ j) *ᵥ toVec n x} =
      ((lorbit n A x m).map (toVec n)).toFinset := by
    ext v
    simp only [Set.mem_ofPred_eq, mem_powOrbit_iff hm hw, List.coe_toFinset, List.mem_map,
      lorbit, List.mem_range]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨_, ⟨j, hj, rfl⟩, by rw [toVec_lmulVec, toMat_lpow]⟩
    · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩
      exact ⟨j, hj, by rw [toVec_lmulVec, toMat_lpow]⟩
  rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup, List.length_map, lorbit,
    List.length_map, List.length_range]
  refine List.Nodup.map_on ?_ hnd
  intro u hu v hv h
  simp only [lorbit, List.mem_map, List.mem_range] at hu hv
  obtain ⟨j, -, rfl⟩ := hu
  obtain ⟨k, -, rfl⟩ := hv
  exact toVec_injective_of_length (length_lmulVec _ _) (length_lmulVec _ _) h

theorem det_toMat_eq (A : List (List ℤ)) :
    (toMat n A).det = CFSG.LieType.Chevalley.laplaceDet n (toMat n A) :=
  (CFSG.LieType.Chevalley.laplaceDet_eq_det n _).symm

@[expose] def lorbitDet (n : ℕ) (W : List (List ℤ)) (x : List ℤ) : ℤ :=
  CFSG.LieType.Chevalley.laplaceDet n (toMat n (lcols n (lorbit n W x n)))

theorem det_orbitMat_toVec (W : List (List ℤ)) (x : List ℤ) :
    (orbitMat (toMat n W) (toVec n x) n).det = lorbitDet n W x := by
  rw [orbitMat_eq_toMat, det_toMat_eq, lorbitDet]

theorem wordMat_eq_toMat (τ : Tag) (l : List (Fin τ.rank)) {L : List (List ℤ)}
    (h : lword τ.rank (cartanList τ) (l.map Fin.val) = L) : wordMat τ l = toMat τ.rank L := by
  rw [← h, toMat_lword τ (toMat_cartanList τ)]

theorem ncard_isRoot_orbitDet {τ : Tag} (W : List (List ℤ)) (P : ℤ → Prop) [DecidablePred P] :
    {v | IsRoot τ v ∧ P (orbitMat (toMat τ.rank W) v τ.rank).det}.ncard =
      (τ.artifactRoots.filter fun l => decide (P (lorbitDet τ.rank W l))).length := by
  rw [ncard_isRoot_and]
  congr 1
  refine List.filter_congr fun l _ => ?_
  rw [det_orbitMat_toVec]

theorem forall_isRoot_orbitDet {τ : Tag} (W : List (List ℤ)) (P : ℤ → Prop)
    (h : ∀ l ∈ τ.artifactRoots, P (lorbitDet τ.rank W l)) :
    ∀ v, IsRoot τ v → P (orbitMat (toMat τ.rank W) v τ.rank).det := by
  rw [forall_isRoot_iff]
  intro l hl
  rw [det_orbitMat_toVec]
  exact h l hl

end CFSG.RankThree.Lattice
