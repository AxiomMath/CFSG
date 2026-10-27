module

public import CFSG.Sporadic.Schreier.Co1ChainCheck
public import CFSG.Sporadic.Schreier.Co1OrbEnum

public section

namespace CFSG.Sporadic.Co1Schreier

open CFSG.Sporadic.SmallF2 (toVecD toVecD_injective)
open CFSG.Sporadic.SmallF2.Native Matrix

@[expose, instance_reducible] def vecAct : MulAction GL24 Vec24 where
  smul g v := (g : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v
  one_smul v := by
    show ((1 : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v
    rw [Units.val_one, one_mulVec]
  mul_smul g h v := by
    show ((g * h : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v =
      (g : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ ((h : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v)
    rw [Units.val_mul, mulVec_mulVec]

attribute [local instance] vecAct

theorem vecAct_smul (g : GL24) (v : Vec24) :
    g • v = (g : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v := rfl

noncomputable def vChain (G : Subgroup GL24) (base : List ℕ) : ℕ → Subgroup GL24
  | 0 => G
  | i + 1 => (MulAction.stabilizer (vChain G base i) (toVecD 24 (base.getD i 0))).map
      (vChain G base i).subtype

variable {G : Subgroup GL24} {base : List ℕ}

theorem mem_vChain_succ {i : ℕ} {g : GL24} :
    g ∈ vChain G base (i + 1) ↔
      g ∈ vChain G base i ∧ g • toVecD 24 (base.getD i 0) = toVecD 24 (base.getD i 0) := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h.2, hh⟩
  · rintro ⟨hg, hs⟩
    exact ⟨⟨g, hg⟩, hs, rfl⟩

theorem card_vChain (i : ℕ) : Nat.card (vChain G base i) =
    Nat.card (MulAction.orbit (vChain G base i) (toVecD 24 (base.getD i 0))) *
      Nat.card (vChain G base (i + 1)) := by
  rw [← Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (vChain G base i)
      (toVecD 24 (base.getD i 0))),
    Nat.card_prod, vChain, Subgroup.card_map_of_injective (vChain G base i).subtype_injective]

variable {L : ℕ → GL24} {cols : Array Native.Rows} {gens : List (List ℕ)} {sizes : List ℕ}

theorem towerOK_parts (h : Native.vTowerOK cols base gens sizes = true) {i : ℕ}
    (hi : i < base.length) :
    base.getD i 0 < 2 ^ 24 ∧
    (∀ j ∈ gens.getD i [], j < cols.size ∧ ∀ l < i,
      vecMulN 24 (cols.getD j #[]) (base.getD l 0) = base.getD l 0) ∧
    Native.vTreeOK cols (gens.getD i []) (base.getD i 0) (sizes.getD i 0)
      (Native.vBfs cols (gens.getD i []) (base.getD i 0) (sizes.getD i 0)) = true := by
  simp only [Native.vTowerOK, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h i hi
  exact ⟨h1, h2, h3⟩

theorem L_mem_vChain (hL : ∀ j < cols.size, L j ∈ G)
    (hcols : ∀ j < cols.size, ActsBy (L j) (cols.getD j #[]))
    (h : Native.vTowerOK cols base gens sizes = true) {i : ℕ} (hi : i < base.length) {j : ℕ}
    (hj : j ∈ gens.getD i []) : L j ∈ vChain G base i := by
  obtain ⟨-, hfix, -⟩ := towerOK_parts h hi
  obtain ⟨hjc, hfixl⟩ := hfix j hj
  suffices ∀ k ≤ i, L j ∈ vChain G base k from this i le_rfl
  intro k
  induction k with
  | zero => exact fun _ => hL j hjc
  | succ k ih =>
    intro hk
    refine mem_vChain_succ.mpr ⟨ih (by omega), ?_⟩
    rw [vecAct_smul, hcols j hjc, hfixl k (by omega)]

theorem vSorted_pairwise : ∀ l : List ℕ, Native.vSorted l = true → List.Pairwise (· < ·) l
  | [] => fun _ => List.Pairwise.nil
  | [a] => fun _ => List.pairwise_singleton _ a
  | a :: b :: r => fun h => by
    simp only [Native.vSorted, Bool.and_eq_true, decide_eq_true_eq] at h
    have hp := vSorted_pairwise (b :: r) h.2
    refine List.Pairwise.cons (fun z hz => ?_) hp
    rcases List.mem_cons.mp hz with rfl | hz
    · exact h.1
    · exact h.1.trans (List.rel_of_pairwise_cons hp hz)

theorem vTreeOK_parts {gs : List ℕ} {root n : ℕ} {t : Array (ℕ × ℕ × ℕ)}
    (h : Native.vTreeOK cols gs root n t = true) :
    t.size = n ∧ (t.getD 0 (0, 0, 0)).1 = root ∧
    (∀ m < n, (t.getD m (0, 0, 0)).1 < 2 ^ 24 ∧
      (m = 0 ∨ (t.getD m (0, 0, 0)).2.1 < m ∧ (t.getD m (0, 0, 0)).2.2 ∈ gs ∧
        (t.getD m (0, 0, 0)).1 = vecMulN 24 (cols.getD (t.getD m (0, 0, 0)).2.2 #[])
          (t.getD (t.getD m (0, 0, 0)).2.1 (0, 0, 0)).1)) ∧
    (t.toList.map (·.1)).Nodup := by
  simp only [Native.vTreeOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq, Bool.or_eq_true, List.contains_iff_mem, and_assoc] at h
  obtain ⟨hs, hr, hall, hsort⟩ := h
  exact ⟨hs, hr, hall, (List.mergeSort_perm _ _).nodup_iff.mp
    ((vSorted_pairwise _ hsort).imp ne_of_lt)⟩

theorem tree_mem_vOrbit (hL : ∀ j < cols.size, L j ∈ G)
    (hcols : ∀ j < cols.size, ActsBy (L j) (cols.getD j #[]))
    (h : Native.vTowerOK cols base gens sizes = true) {i : ℕ} (hi : i < base.length) :
    ∀ m < sizes.getD i 0, toVecD 24 ((Native.vBfs cols (gens.getD i []) (base.getD i 0)
      (sizes.getD i 0)).getD m (0, 0, 0)).1 ∈
      MulAction.orbit (vChain G base i) (toVecD 24 (base.getD i 0)) := by
  obtain ⟨-, hfix, htree⟩ := towerOK_parts h hi
  obtain ⟨-, hroot, hall, -⟩ := vTreeOK_parts htree
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    rcases (hall m hm).2 with rfl | ⟨hp, hg, he⟩
    · rw [hroot]
      exact MulAction.mem_orbit_iff.mpr ⟨1, one_smul _ _⟩
    · obtain ⟨g, hg'⟩ := MulAction.mem_orbit_iff.mp (ih _ hp (hp.trans hm))
      have hjc := (hfix _ hg).1
      refine MulAction.mem_orbit_iff.mpr ⟨⟨L _, L_mem_vChain hL hcols h hi hg⟩ * g, ?_⟩
      rw [mul_smul, hg', Subgroup.smul_def, vecAct_smul, hcols _ hjc, he]

theorem size_le_card_orbit (hL : ∀ j < cols.size, L j ∈ G)
    (hcols : ∀ j < cols.size, ActsBy (L j) (cols.getD j #[]))
    (h : Native.vTowerOK cols base gens sizes = true) {i : ℕ} (hi : i < base.length) :
    sizes.getD i 0 ≤ Nat.card (MulAction.orbit (vChain G base i) (toVecD 24 (base.getD i 0))) := by
  obtain ⟨-, -, htree⟩ := towerOK_parts h hi
  obtain ⟨hsize, -, hall, hnodup⟩ := vTreeOK_parts htree
  have hmem := tree_mem_vOrbit hL hcols h hi
  have hget : ∀ m (hm : m < sizes.getD i 0), ((Native.vBfs cols (gens.getD i []) (base.getD i 0)
      (sizes.getD i 0)).getD m (0, 0, 0)).1 =
      ((Native.vBfs cols (gens.getD i []) (base.getD i 0) (sizes.getD i 0)).toList.map
        (·.1))[m]'(by rw [List.length_map, Array.length_toList, hsize]; exact hm) := by
    intro m hm
    have hm' : m < (Native.vBfs cols (gens.getD i []) (base.getD i 0) (sizes.getD i 0)).size := by
      rw [hsize]
      exact hm
    rw [List.getElem_map, Array.getElem_toList, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem hm', Option.getD_some]
  have hinj : Function.Injective fun m : Fin (sizes.getD i 0) =>
      (⟨_, hmem m.val m.isLt⟩ : MulAction.orbit (vChain G base i) (toVecD 24 (base.getD i 0))) := by
    intro m m' hmm
    have hpair := congrArg Subtype.val hmm
    have hv := toVecD_injective (hall m m.isLt).1 (hall m' m'.isLt).1 hpair
    rw [hget m m.isLt, hget m' m'.isLt] at hv
    exact Fin.ext ((hnodup.getElem_inj_iff).mp hv)
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_eq_fintype_card, Fintype.card_fin] at this

theorem card_ge_of_towerOK (hL : ∀ j < cols.size, L j ∈ G)
    (hcols : ∀ j < cols.size, ActsBy (L j) (cols.getD j #[]))
    (h : Native.vTowerOK cols base gens sizes = true) :
    ∏ i ∈ Finset.range base.length, sizes.getD i 0 ≤ Nat.card G := by
  have key : ∀ k ≤ base.length, (∏ i ∈ Finset.range k, sizes.getD i 0) *
      Nat.card (vChain G base k) ≤ Nat.card (vChain G base 0) := by
    intro k
    induction k with
    | zero => intro _; rw [Finset.prod_range_zero, one_mul]
    | succ k ih =>
      intro hk
      refine le_trans ?_ (ih (by omega))
      rw [Finset.prod_range_succ, mul_assoc, card_vChain (G := G) (base := base) k]
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _
        (size_le_card_orbit hL hcols h (by omega)))
  have hk := key base.length le_rfl
  exact le_trans (Nat.le_mul_of_pos_right _ Nat.card_pos) hk

end CFSG.Sporadic.Co1Schreier
