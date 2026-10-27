module

public import CFSG.Sporadic.Co1Patterson.TwistNativeCheck
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LargeExtraspecial.S12TriQ
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.Co1Block.TwoACent

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Patterson.TwistNative

open Subgroup CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Schreier CFSG.LargeExtraspecial
open CFSG.Blueprint (NativeSporadic.Co1)

theorem rows_eq_iff {X Y : Native.Rows} {g h : GL24} (hX : MRep X g) (hY : MRep Y h)
    (vX : CFSG.Sporadic.Co1.InvNative.validRows X = true)
    (vY : CFSG.Sporadic.Co1.InvNative.validRows Y = true) : X = Y ↔ g = h := by
  constructor
  · rintro rfl
    exact hX.eq hY
  · rintro rfl
    exact CFSG.Sporadic.Co1.Module.rowsMatrix_injective_of_valid vX vY (hX.trans hY.symm)

theorem rows_beq_iff {X Y : Native.Rows} {g h : GL24} (hX : MRep X g) (hY : MRep Y h)
    (vX : CFSG.Sporadic.Co1.InvNative.validRows X = true)
    (vY : CFSG.Sporadic.Co1.InvNative.validRows Y = true) : (X == Y) = true ↔ g = h := by
  rw [beq_iff_eq, rows_eq_iff hX hY vX vY]

theorem valid_mul {X Y : Native.Rows} (vX : CFSG.Sporadic.Co1.InvNative.validRows X = true)
    (vY : CFSG.Sporadic.Co1.InvNative.validRows Y = true) :
    CFSG.Sporadic.Co1.InvNative.validRows (Native.mul X Y) = true :=
  CFSG.Sporadic.Co1.Module.TwoB.validRows_mulRows vX vY

theorem rep_foldl_if (l : List ℕ) (p : ℕ → Bool) (r : ℕ → Native.Rows) (x : ℕ → GL24)
    (hr : ∀ i ∈ l, MRep (r i) (x i)) {acc : Native.Rows} {g : GL24} (h : MRep acc g) :
    MRep (l.foldl (fun a i => if p i then Native.mul a (r i) else a) acc)
      (l.foldl (fun b i => if p i then b * x i else b) g) := by
  induction l generalizing acc g with
  | nil => exact h
  | cons i l ih =>
    simp only [List.foldl_cons]
    refine ih (fun j hj => hr j (List.mem_cons_of_mem _ hj)) ?_
    by_cases hp : p i
    · rw [ite_eq_left hp, ite_eq_left hp]
      exact h.mul (hr i List.mem_cons_self)
    · rw [ite_eq_right hp, ite_eq_right hp]
      exact h

theorem valid_foldl_if (l : List ℕ) (p : ℕ → Bool) (r : ℕ → Native.Rows)
    (hr : ∀ i ∈ l, CFSG.Sporadic.Co1.InvNative.validRows (r i) = true) {acc : Native.Rows}
    (h : CFSG.Sporadic.Co1.InvNative.validRows acc = true) :
    CFSG.Sporadic.Co1.InvNative.validRows
      (l.foldl (fun a i => if p i then Native.mul a (r i) else a) acc) = true := by
  induction l generalizing acc with
  | nil => exact h
  | cons i l ih =>
    simp only [List.foldl_cons]
    refine ih (fun j hj => hr j (List.mem_cons_of_mem _ hj)) ?_
    by_cases hp : p i
    · rw [ite_eq_left hp]
      exact valid_mul h (hr i List.mem_cons_self)
    · rw [ite_eq_right hp]
      exact h

theorem foldl_if_mem {G : Type*} [Group G] {H : Subgroup G} (l : List ℕ) (p : ℕ → Bool)
    (x : ℕ → G) (hx : ∀ i ∈ l, x i ∈ H) {g : G} (hg : g ∈ H) :
    l.foldl (fun b i => if p i then b * x i else b) g ∈ H := by
  induction l generalizing g with
  | nil => exact hg
  | cons i l ih =>
    simp only [List.foldl_cons]
    refine ih (fun j hj => hx j (List.mem_cons_of_mem _ hj)) ?_
    by_cases hp : p i
    · rw [ite_eq_left hp]
      exact H.mul_mem hg (hx i List.mem_cons_self)
    · rw [ite_eq_right hp]
      exact hg

theorem map_foldl_if {G G' : Type*} [Group G] [Group G'] (f : G →* G') (l : List ℕ)
    (p : ℕ → Bool) (x : ℕ → G) (g : G) :
    f (l.foldl (fun b i => if p i then b * x i else b) g) =
      l.foldl (fun b i => if p i then b * f (x i) else b) (f g) := by
  induction l generalizing g with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldl_cons]
    rw [ih]
    by_cases hp : p i
    · rw [ite_eq_left hp, ite_eq_left hp, map_mul]
    · rw [ite_eq_right hp, ite_eq_right hp]

@[expose] noncomputable def twBaseG : List GL24 := [A₁, A₂, aG] ++ (List.range 8).map twoAQg

theorem rep_twBase :
    List.Forall₂ MRep twBaseRows twBaseG := by
  refine List.rel_append (.cons rep_A₁ (.cons rep_A₂ (.cons rep_iotaA .nil))) ?_
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact List.forall₂_same.2 fun k _ => rep_iotaQ k

theorem twBase_mem_GA : ∀ g ∈ twBaseG, g ∈ GA := by
  intro g hg
  rcases List.mem_append.1 hg with h | h
  · rcases List.mem_cons.1 h with h1 | h
    · exact h1 ▸ A₁_mem
    rcases List.mem_cons.1 h with h1 | h
    · exact h1 ▸ A₂_mem
    rcases List.mem_cons.1 h with h1 | h
    · exact h1 ▸ iotaA_mem_GA
    exact absurd h List.not_mem_nil
  · obtain ⟨k, -, rfl⟩ := List.mem_map.1 h
    exact iotaQ_mem_GA k

@[expose] noncomputable def twG (j : ℕ) : GL24 := (dagG twBaseG twDerivs).getD (j - 1) 1

theorem twG_mem_GA (j : ℕ) : twG j ∈ GA :=
  getD_mem_of_forall (dagG_mem twBase_mem_GA twDerivs) _

@[expose] noncomputable def qWordG (e : ℕ) : GL24 :=
  (List.range 8).foldl (fun acc k => if e.testBit k then acc * twoAQg k else acc) 1

@[expose] noncomputable def yG (i : ℕ) : GL24 := qWordG (yBits.getD i 0)

@[expose] noncomputable def yprodG (c : ℕ) : GL24 :=
  (List.range 8).foldl (fun acc i => if c.testBit i then acc * yG i else acc) 1

theorem rep_qWordG
    (e : ℕ) : MRep (qWordRow e) (qWordG e) :=
  rep_foldl_if _ _ _ _ (fun k _ => rep_iotaQ k) MRep.one

theorem rep_yG
    (i : ℕ) : MRep (yRow i) (yG i) :=
  rep_qWordG _

theorem rep_yprodG
    (c : ℕ) : MRep (yprodRow c) (yprodG c) :=
  rep_foldl_if _ _ _ _ (fun i _ => rep_yG i) MRep.one

theorem qWordG_mem_twoAQ (e : ℕ) : qWordG e ∈ twoAQ :=
  foldl_if_mem _ _ _ (fun k hk => by
    rw [twoAQ, qSub]
    exact subset_closure ⟨k, by rw [twoAQRows_length]; exact List.mem_range.1 hk, rfl⟩)
    (one_mem _)

theorem yG_mem_twoAQ (i : ℕ) : yG i ∈ twoAQ := qWordG_mem_twoAQ _

theorem yprodG_mem_twoAQ (c : ℕ) : yprodG c ∈ twoAQ :=
  foldl_if_mem _ _ _ (fun i _ => yG_mem_twoAQ i) (one_mem _)


theorem dagOK_parts : (Native.dag twBaseRows twDerivs).2.2 = true ∧
    CFSG.Sporadic.Co1.InvNative.validRows iotaARows = true ∧
    (∀ i < 8, CFSG.Sporadic.Co1.InvNative.validRows (yRow i) = true) ∧
    (∀ c < 256, CFSG.Sporadic.Co1.InvNative.validRows (yprodRow c) = true) ∧
    ∀ j ∈ hIdx ++ [h4Idx, h4pIdx], CFSG.Sporadic.Co1.InvNative.validRows (twRow j) = true := by
  have h := tw_dag_check
  simp only [dagOK, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem rep_twG
    (j : ℕ) : MRep (twRow j) (twG j) :=
  getD_rep (dag_rep rep_twBase twDerivs dagOK_parts.1) MRep.one (j - 1)

end CFSG.Sporadic.Co1Patterson.TwistNative
