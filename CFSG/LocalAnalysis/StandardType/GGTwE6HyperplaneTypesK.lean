module

public import CFSG.HardMathSupport.Malle.E27Lie.ExcCross.E6TwoPack
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSylow
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeModel
public import CFSG.Blueprint.ChevalleyRoots

public section

namespace CFSG.StandardType.TwE6HyperplaneTypes.K

open CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Malle.E27Lie.ExcCross.E6Pack

@[expose] def eqK (l l' : List (Fin Tag.E6.rank)) (j : ℕ) : Bool :=
  bandK (Nat.blt (actK l (ej j)) BAD)
    (bandK (Nat.blt (actK l' (ej j)) BAD) (Nat.beq (actK l (ej j)) (actK l' (ej j))))

@[expose] def neK (l : List (Fin Tag.E6.rank)) (j : ℕ) : Bool :=
  bandK (Nat.blt (actK l (ej j)) BAD) (Bool.rec true false (Nat.beq (actK l (ej j)) (ej j)))

theorem stepK_reflect (i : Fin Tag.E6.rank) (x : ℕ) (h : stepK i.val x < BAD) :
    x < BAD ∧ toV (stepK i.val x) = reflect Tag.E6 i (toV x) := by
  fin_cases i
  · obtain ⟨a, b⟩ := spec0 x h
    exact ⟨a, funext b⟩
  · obtain ⟨a, b⟩ := spec1 x h
    exact ⟨a, funext b⟩
  · obtain ⟨a, b⟩ := spec2 x h
    exact ⟨a, funext b⟩
  · obtain ⟨a, b⟩ := spec3 x h
    exact ⟨a, funext b⟩
  · obtain ⟨a, b⟩ := spec4 x h
    exact ⟨a, funext b⟩
  · obtain ⟨a, b⟩ := spec5 x h
    exact ⟨a, funext b⟩

theorem actK_wordAct (l : List (Fin Tag.E6.rank)) (x : ℕ) (h : actK l x < BAD) :
    x < BAD ∧ toV (actK l x) = TableBExc.wordAct .E6 l (toV x) := by
  induction l with
  | nil => exact ⟨h, rfl⟩
  | cons i l ih =>
    change stepK i.val (actK l x) < BAD at h
    obtain ⟨h1, h2⟩ := stepK_reflect i _ h
    obtain ⟨h3, h4⟩ := ih h1
    refine ⟨h3, ?_⟩
    change toV (stepK i.val (actK l x)) = reflect Tag.E6 i (TableBExc.wordAct .E6 l (toV x))
    rw [h2, h4]

theorem actK_single {l : List (Fin Tag.E6.rank)} {j : Fin Tag.E6.rank}
    (h : actK l (ej j.val) < BAD) :
    toV (actK l (ej j.val)) = TableBExc.wordAct .E6 l (Pi.single j 1) := by
  rw [(actK_wordAct l _ h).2]
  exact congrArg _ (toV_ej j)

theorem eqK_sound {l l' : List (Fin Tag.E6.rank)} {j : Fin Tag.E6.rank}
    (h : eqK l l' j.val = true) :
    TableBExc.wordAct .E6 l (Pi.single j 1) = TableBExc.wordAct .E6 l' (Pi.single j 1) := by
  unfold eqK at h
  rw [bandK_eq, bandK_eq, Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq,
    Nat.beq_eq] at h
  obtain ⟨h1, h2, h3⟩ := h
  rw [← actK_single h1, ← actK_single h2, h3]

theorem neK_sound {l : List (Fin Tag.E6.rank)} {j : Fin Tag.E6.rank}
    (h : neK l j.val = true) : TableBExc.wordAct .E6 l (Pi.single j 1) ≠ Pi.single j 1 := by
  unfold neK at h
  rw [bandK_eq, Bool.and_eq_true, Nat.blt_eq, brec_eq] at h
  obtain ⟨h1, h2⟩ := h
  intro he
  rw [← actK_single h1] at he
  have := toV_inj h1 (ej_lt j) (he.trans (toV_ej j).symm)
  rw [if_pos (by rw [this]; exact Nat.beq_refl _)] at h2
  exact absurd h2 (by decide)

@[expose] def cubK (l : List (Fin Tag.E6.rank)) (j : ℕ) : Bool :=
  bandK (Nat.blt (actK (l ++ l) (ej j)) BAD)
    (allNK 6 fun m => Nat.beq (Nat.add (Nat.add (lnK (ej j) (Nat.mul 8 m))
      (lnK (actK l (ej j)) (Nat.mul 8 m))) (lnK (actK (l ++ l) (ej j)) (Nat.mul 8 m))) 384)

theorem actK_append (l l' : List (Fin Tag.E6.rank)) (x : ℕ) :
    actK (l ++ l') x = actK l (actK l' x) := by
  induction l with
  | nil => rfl
  | cons i l ih => exact congrArg (stepK i.val) ih

theorem cubK_sound {l : List (Fin Tag.E6.rank)} {j : Fin Tag.E6.rank}
    (h : cubK l j.val = true) :
    (Pi.single j 1 : Fin Tag.E6.rank → ℤ) + TableBExc.wordAct .E6 l (Pi.single j 1) +
      TableBExc.wordAct .E6 l (TableBExc.wordAct .E6 l (Pi.single j 1)) = 0 := by
  unfold cubK at h
  rw [bandK_eq, Bool.and_eq_true, Nat.blt_eq, allNK_iff] at h
  obtain ⟨h1, h2⟩ := h
  rw [actK_append] at h1 h2
  obtain ⟨hin, hout⟩ := actK_wordAct l _ h1
  have e1 := actK_single hin
  rw [e1] at hout
  have te : toV (ej j.val) = (Pi.single j 1 : Fin Tag.E6.rank → ℤ) := toV_ej j
  rw [← hout, ← e1, ← te]
  funext m
  have hm := h2 m.val m.isLt
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq] at hm
  simp only [Pi.add_apply, Pi.zero_apply, toV]
  omega

@[expose] def rootE6 (n : ℕ) : Fin Tag.E6.rank → ℤ := Tag.E6.rootCertificate.root n

@[expose] def sgP : ℕ :=
  19358185631285779041841869610841798513373875420754281365299027882102708220080152227449173344849261987147301595152924049090840811026169480993057079557

@[expose] def sg (n : ℕ) : ℕ := Nat.land (Nat.shiftRight sgP (Nat.mul 7 n)) 127

local instance rootDecEqK : DecidableEq (Fin Tag.E6.rank → ℤ) :=
  Fintype.decidablePiFintype

theorem mem_rootFinset_E6 {α : Fin Tag.E6.rank → ℤ} :
    α ∈ rootFinset .E6 ↔ ∃ n < 72, rootE6 n = α := by
  have hl : Tag.E6.rootCertificate.roots.length = 72 := rfl
  rw [rootFinset, List.mem_toFinset, List.mem_map, hl]
  simp only [List.mem_range, rootE6]

theorem rootE6_mem {n : ℕ} (h : n < 72) : rootE6 n ∈ rootFinset .E6 :=
  mem_rootFinset_E6.2 ⟨n, h, rfl⟩

set_option maxRecDepth 100000 in
theorem cAct_rootE6 : ∀ n < 72, sg n < 72 ∧
    TableBExc.wordAct .E6 TableBExc.E6Three.wordE6C (rootE6 n) = rootE6 (sg n) := by
  decide +kernel

theorem rootE6_35 : rootE6 35 = ![0, 0, 1, 1, 1, 1] := by
  funext j
  fin_cases j <;> decide +kernel

theorem rootE6_33 : rootE6 33 = ![0, 1, 0, 1, 1, 1] := by
  funext j
  fin_cases j <;> decide +kernel

theorem forall_root_c (P : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ) →
      (Fin Tag.E6.rank → ℤ) → Prop)
    (h : ∀ n < 72, P (rootE6 n) (rootE6 (sg n)) (rootE6 (sg (sg n)))) :
    ∀ α ∈ rootFinset .E6, P α (TableBExc.wordAct .E6 TableBExc.E6Three.wordE6C α)
      (TableBExc.wordAct .E6 TableBExc.E6Three.wordE6C
        (TableBExc.wordAct .E6 TableBExc.E6Three.wordE6C α)) := by
  intro α hα
  obtain ⟨n, hn, rfl⟩ := mem_rootFinset_E6.1 hα
  obtain ⟨h1, e1⟩ := cAct_rootE6 n hn
  rw [e1, (cAct_rootE6 _ h1).2]
  exact h n hn

theorem root_c_of_forall (P : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ) →
      (Fin Tag.E6.rank → ℤ) → Prop)
    (h : ∀ α ∈ rootFinset .E6, P α (TableBExc.wordAct .E6 TableBExc.E6Three.wordE6C α)
      (TableBExc.wordAct .E6 TableBExc.E6Three.wordE6C
        (TableBExc.wordAct .E6 TableBExc.E6Three.wordE6C α))) :
    ∀ n < 72, P (rootE6 n) (rootE6 (sg n)) (rootE6 (sg (sg n))) := by
  intro n hn
  have := h _ (rootE6_mem hn)
  obtain ⟨h1, e1⟩ := cAct_rootE6 n hn
  rwa [e1, (cAct_rootE6 _ h1).2] at this

end CFSG.StandardType.TwE6HyperplaneTypes.K

end
