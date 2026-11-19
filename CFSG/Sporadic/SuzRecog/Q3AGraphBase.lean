
module

public import CFSG.Sporadic.SuzRecog.Q3A
public import CFSG.Sporadic.SuzRecog.Q3ACheck

@[expose] public noncomputable section

namespace CFSG.Sporadic.SuzRecog.Q3A

open Subgroup CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native Check
  CFSG.Sporadic.SuzRecog.LevelTwoData

theorem keyOf_eq_sum (l : Array ℕ) : keyOf l = (l.toList.map fun x => wt[x]!).sum := by
  unfold keyOf
  rw [← Array.foldl_toList]
  generalize l.toList = L
  suffices h : ∀ acc : UInt64, L.foldl (fun acc x => acc + wt[x]!) acc =
      acc + (L.map fun x => wt[x]!).sum by
    simpa using h 0
  induction L with
  | nil => intro acc; simp
  | cons a L ih =>
    intro acc
    rw [List.foldl_cons, ih, List.map_cons, List.sum_cons, add_assoc]

theorem keyOf_eq_of_mem_iff {l l' : Array ℕ} (hl : l.toList.Nodup) (hl' : l'.toList.Nodup)
    (h : ∀ x, x ∈ l ↔ x ∈ l') : keyOf l = keyOf l' := by
  rw [keyOf_eq_sum, keyOf_eq_sum]
  refine List.Perm.sum_eq (List.Perm.map _ ((List.perm_ext_iff_of_nodup hl hl').2 fun x => ?_))
  rw [Array.mem_toList_iff, Array.mem_toList_iff]
  exact h x

def IsFixList (x : Vtx) (l : Array ℕ) : Prop :=
  l.toList.Nodup ∧ (∀ y ∈ l, y < 1782) ∧ ∀ p : Fin 1782, p ∈ fixSet x ↔ (p : ℕ) ∈ l

theorem IsFixList.key_eq {x : Vtx} {l l' : Array ℕ} (h : IsFixList x l) (h' : IsFixList x l') :
    keyOf l = keyOf l' := by
  refine keyOf_eq_of_mem_iff h.1 h'.1 fun y => ⟨fun hy => ?_, fun hy => ?_⟩
  · have := (h.2.2 ⟨y, h.2.1 y hy⟩).2 hy
    exact (h'.2.2 ⟨y, h.2.1 y hy⟩).1 this
  · have := (h'.2.2 ⟨y, h'.2.1 y hy⟩).2 hy
    exact (h.2.2 ⟨y, h'.2.1 y hy⟩).1 this

theorem IsFixList.smul {x : Vtx} {l : Array ℕ} (h : IsFixList x l) (g : ↥suzM) {a : Array ℕ}
    (ha : Rep 1782 a (g : Equiv.Perm (Fin 1782))) : IsFixList (g • x) (imgA a l) := by
  obtain ⟨hnd, hlt, hmem⟩ := h
  have hval : ∀ y (hy : y ∈ l), a[y]! = ((g : Equiv.Perm (Fin 1782)) ⟨y, hlt y hy⟩ : ℕ) :=
    fun y hy => ha.apply (hlt y hy)
  refine ⟨?_, ?_, fun p => ?_⟩
  · unfold imgA
    rw [Array.toList_map]
    refine hnd.map_on fun y hy z hz hyz => ?_
    rw [Array.mem_toList_iff] at hy hz
    rw [hval y hy, hval z hz] at hyz
    have := (g : Equiv.Perm (Fin 1782)).injective (Fin.ext hyz)
    simpa using congrArg Fin.val this
  · intro y hy
    unfold imgA at hy
    obtain ⟨z, hz, rfl⟩ := Array.mem_map.1 hy
    exact ha.lt (hlt z hz)
  · rw [fixSet_smul]
    constructor
    · rintro ⟨q, hq, rfl⟩
      unfold imgA
      refine Array.mem_map.2 ⟨q, (hmem q).1 hq, ?_⟩
      exact ha.apply q.2
    · intro hp
      unfold imgA at hp
      obtain ⟨z, hz, hzp⟩ := Array.mem_map.1 hp
      refine ⟨⟨z, hlt z hz⟩, (hmem _).2 hz, Fin.ext ?_⟩
      rw [← hzp, ha.apply (hlt z hz)]

theorem mem_fix0_iff (y : ℕ) : y ∈ fix0 ↔ y < 1782 ∧ rhoArr[y]! = y := by
  unfold fix0
  rw [Array.mem_filter, Array.mem_range, beq_iff_eq]

theorem getElem!_map_range {α : Type} [Inhabited α] {f : ℕ → α} {n i : ℕ} (hi : i < n) :
    ((Array.range n).map f)[i]! = f i := by
  rw [getElem!_pos ((Array.range n).map f) i (by simpa using hi)]
  simp

theorem xA_zero : xA 0 = x1 := by simp [xA]

theorem xA_one : xA 1 = x2 := by simp [xA]

theorem rhoPow_one : rhoPow 1 = rhoArr := by simp [rhoPow]

theorem rhoPow_two : rhoPow 2 = compA 1782 rhoArr rhoArr := by simp [rhoPow]

theorem getElem!_pair {α : Type*} [Inhabited α] (a b : α) :
    (#[a, b] : Array α)[0]! = a ∧ (#[a, b] : Array α)[1]! = b := ⟨rfl, rfl⟩

theorem xTab_get {s y : ℕ} (hs : s < 2) (hy : y < 22880) : (xTab[s]!)[y]! = actIdx (xA s) y := by
  have h := getElem!_pair ((Array.range 22880).map (actIdx x1)) ((Array.range 22880).map (actIdx x2))
  have e0 : xTab[0]! = (Array.range 22880).map (actIdx x1) := h.1
  have e1 : xTab[1]! = (Array.range 22880).map (actIdx x2) := h.2
  interval_cases s
  · rw [e0, xA_zero]
    exact getElem!_map_range hy
  · rw [e1, xA_one]
    exact getElem!_map_range hy

theorem mem_roots {r : ℕ} : r ∈ roots ↔ r < 22880 ∧ froot[r]! = r := by
  unfold roots
  rw [Array.mem_filter, Array.mem_range, beq_iff_eq]

theorem adj0Arr_get {r : ℕ} (hr : r < 22880) : adj0Arr[r]! = (froot[r]! == r && adj0 r) :=
  getElem!_map_range hr

theorem isInvol_iff {g : Array ℕ} {G : Equiv.Perm (Fin 1782)} (hg : Rep 1782 g G) :
    isInvol g = true ↔ orderOf G = 2 := by
  rw [orderOf_eq_prime_iff, pow_two, ne_eq,
    ← eqA_iff (rep_compA hg hg) (rep_idA (n := 1782)), ← eqA_iff hg (rep_idA (n := 1782)),
    isInvol, Bool.and_eq_true, Bool.not_eq_true', Bool.not_eq_true]

theorem exists_pow_iff (a b : Equiv.Perm (Fin 1782)) :
    (∃ i ∈ ({1, 2} : Finset ℕ), ∃ j ∈ ({1, 2} : Finset ℕ), orderOf (a ^ i * b ^ j) = 2) ↔
      (orderOf (a * b) = 2 ∨ orderOf (a * (b * b)) = 2) ∨
        (orderOf (a * a * b) = 2 ∨ orderOf (a * a * (b * b)) = 2) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, exists_eq_or_imp, exists_eq_left, pow_one,
    sq]

def bP (s : ℕ) : Equiv.Perm (Fin 1782) := if s = 0 then suzB0 else suzB1

theorem bP_mem (s : ℕ) : bP s ∈ suzM := by
  unfold bP
  split_ifs
  · exact subset_closure (Set.mem_insert _ _)
  · exact subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

def cPerm (i : ℕ) : Equiv.Perm (Fin 1782) :=
  if _h : 0 < i ∧ tpar[i]! < i then bP tlab[i]! * cPerm tpar[i]! else 1
termination_by i
decreasing_by exact _h.2

theorem cPerm_eq (i : ℕ) :
    cPerm i = if 0 < i ∧ tpar[i]! < i then bP tlab[i]! * cPerm tpar[i]! else 1 := by
  rw [cPerm]
  split_ifs <;> rfl

theorem cPerm_mem (i : ℕ) : cPerm i ∈ suzM := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rw [cPerm_eq]
    split_ifs with h
    · exact mul_mem (bP_mem _) (ih _ h.2)
    · exact one_mem _

theorem cArr_eq (i : ℕ) :
    cArr i = if 0 < i ∧ tpar[i]! < i then compA 1782 (bA tlab[i]!) (cArr tpar[i]!) else idA 1782 := by
  rw [cArr]
  split_ifs <;> rfl

theorem cArrInv_eq (i : ℕ) :
    cArrInv i =
      if 0 < i ∧ tpar[i]! < i then compA 1782 (cArrInv tpar[i]!) (bAi tlab[i]!) else idA 1782 := by
  rw [cArrInv]
  split_ifs <;> rfl

def cG (i : ℕ) : ↥suzM := ⟨cPerm i, cPerm_mem i⟩

def vtx (i : ℕ) : Vtx := cG i • v0

theorem vtx_zero : vtx 0 = v0 := by
  unfold vtx cG
  have : cPerm 0 = 1 := by rw [cPerm_eq]; simp
  have h1 : (⟨cPerm 0, cPerm_mem 0⟩ : ↥suzM) = 1 := Subtype.ext this
  rw [h1, one_smul]

theorem vtx_succ {i : ℕ} (h : 0 < i ∧ tpar[i]! < i) :
    vtx i = (⟨bP tlab[i]!, bP_mem _⟩ : ↥suzM) • vtx tpar[i]! := by
  unfold vtx
  rw [← mul_smul]
  congr 1
  apply Subtype.ext
  show cPerm i = bP tlab[i]! * cPerm tpar[i]!
  rw [cPerm_eq i, ite_eq_left h]

def xP (s : ℕ) : Equiv.Perm (Fin 1782) := permC 1782 (xA s)

theorem card_vtx_eq : Nat.card Vtx = (MulAction.stabilizer ↥suzM v0).index := by
  rw [MulAction.index_stabilizer]
  refine (Nat.card_congr (Equiv.subtypeUnivEquiv fun x => ?_)).symm
  obtain ⟨g, rfl⟩ := exists_smul x
  exact MulAction.mem_orbit v0 g

theorem stabilizer_v0_eq :
    MulAction.stabilizer ↥suzM v0 =
      (normalizer (base : Set (Equiv.Perm (Fin 1782)))).subgroupOf suzM := by
  ext g
  rw [MulAction.mem_stabilizer_iff, mem_subgroupOf, smul_v0_eq_iff]

theorem card_stabilizer_v0 :
    Nat.card (MulAction.stabilizer ↥suzM v0) =
      Nat.card ↥(normalizer (base : Set (Equiv.Perm (Fin 1782))) ⊓ suzM) := by
  rw [stabilizer_v0_eq, ← inf_subgroupOf_right]
  exact Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv

theorem card_vtx_mul :
    Nat.card Vtx * Nat.card ↥(normalizer (base : Set (Equiv.Perm (Fin 1782))) ⊓ suzM) =
      448345497600 := by
  have h1 := (MulAction.stabilizer ↥suzM v0).index_mul_card
  rwa [card_stabilizer_v0, ← card_vtx_eq, suzM_card_chain] at h1

abbrev NrhoBound : Prop :=
  19595520 ≤ Nat.card ↥(normalizer (base : Set (Equiv.Perm (Fin 1782))) ⊓ suzM)

theorem mem_normalizer_of_comm {x : Equiv.Perm (Fin 1782)} (hx : x * Model.rho1 = Model.rho1 * x) :
    x ∈ normalizer (base : Set (Equiv.Perm (Fin 1782))) := by
  refine centralizer_le_normalizer _ (mem_centralizer_iff.2 fun h hh => ?_)
  rw [SetLike.mem_coe] at hh
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hh
  exact (Commute.zpow_left (show Commute Model.rho1 x from hx.symm) k).eq

section Check

end Check

section Table

theorem rep_bA (s : ℕ) : Rep 1782 (bA s) (bP s) := by
  unfold bA bP
  by_cases h : s = 0
  · subst h
    simpa [Check.b0] using rep_b0
  · simpa [Check.b1, h] using rep_b1

theorem rep_cArr (i : ℕ) : Rep 1782 (cArr i) (cPerm i) := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rw [cArr_eq, cPerm_eq]
    split_ifs with h
    · exact rep_compA (rep_bA _) (ih _ h.2)
    · exact rep_idA

end Table

end CFSG.Sporadic.SuzRecog.Q3A
