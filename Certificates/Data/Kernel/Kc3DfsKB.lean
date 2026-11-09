module

public import Certificates.Data.Kernel.Kc3DfsK

public section

namespace CFSG.KC.Kc3K

open CFSG.QuasithinUnique.A5.Kc3SporPerm

@[expose] def okSizeB (c : Nat) : Bool :=
  Nat.beq c 0 || Nat.beq c 60 || Nat.beq c 90 || Nat.beq c 120 || Nat.beq c 150 || Nat.beq c 210

theorem dlt (a b : Nat) : decide (a < b) = Nat.blt a b := by
  cases h : Nat.blt a b
  · simp only [decide_eq_false_iff_not]; intro h'; exact absurd (Nat.blt_eq.mpr h') (by simp [h])
  · simp only [decide_eq_true_eq]; exact Nat.blt_eq.mp h

@[expose] def g2B (M : Nat) (pr : Nat → Nat → Nat) (i j : Nat) : Bool :=
  Nat.blt i j && Nat.blt (pr i j) M && Nat.blt j (pr i j)

@[expose] def g3B (M : Nat) (pr : Nat → Nat → Nat) (i j k : Nat) : Bool :=
  Nat.blt j k && Nat.blt (pr i k) M && Nat.blt (pr j k) M && Nat.blt (pr (pr i j) k) M &&
    Nat.blt k (pr i k) && Nat.blt k (pr j k) && Nat.blt k (pr (pr i j) k)

@[expose] def g4B (M : Nat) (pr : Nat → Nat → Nat) (i j k l : Nat) : Bool :=
  Nat.blt k l && Nat.blt (pr i l) M && Nat.blt (pr j l) M && Nat.blt (pr (pr i j) l) M &&
    Nat.blt (pr k l) M && Nat.blt (pr (pr i k) l) M && Nat.blt (pr (pr j k) l) M &&
    Nat.blt (pr (pr (pr i j) k) l) M && Nat.blt l (pr i l) && Nat.blt l (pr j l) &&
    Nat.blt l (pr (pr i j) l) && Nat.blt l (pr k l) && Nat.blt l (pr (pr i k) l) &&
    Nat.blt l (pr (pr j k) l) && Nat.blt l (pr (pr (pr i j) k) l)

theorem g2_eq (M : Nat) (pr : Nat → Nat → Nat) (i j : Nat) : g2 M pr i j = g2B M pr i j := by
  simp only [g2, g2B, dlt]

theorem g3_eq (M : Nat) (pr : Nat → Nat → Nat) (i j k : Nat) :
    g3 M pr i j k = g3B M pr i j k := by
  simp only [g3, g3B, dlt]

theorem g4_eq (M : Nat) (pr : Nat → Nat → Nat) (i j k l : Nat) :
    g4 M pr i j k l = g4B M pr i j k l := by
  simp only [g4, g4B, dlt]

@[expose] noncomputable def leafV (ct : Nat → Nat → Nat)
    (e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 : Nat) : Bool :=
  (fun vals => (fun H => vals.any fun v => !(okSizeB (cntK H v))) (histK vals))
    [ct e1 e2, ct e1 e3, ct e1 e4, ct e1 e5, ct e1 e6, ct e1 e7, ct e1 e8, ct e1 e9, ct e1 e10,
      ct e1 e11, ct e1 e12, ct e1 e13, ct e1 e14, ct e1 e15, ct e2 e1, ct e2 e3, ct e2 e4,
      ct e2 e5, ct e2 e6, ct e2 e7, ct e2 e8, ct e2 e9, ct e2 e10, ct e2 e11, ct e2 e12,
      ct e2 e13, ct e2 e14, ct e2 e15, ct e3 e1, ct e3 e2, ct e3 e4, ct e3 e5, ct e3 e6,
      ct e3 e7, ct e3 e8, ct e3 e9, ct e3 e10, ct e3 e11, ct e3 e12, ct e3 e13, ct e3 e14,
      ct e3 e15, ct e4 e1, ct e4 e2, ct e4 e3, ct e4 e5, ct e4 e6, ct e4 e7, ct e4 e8, ct e4 e9,
      ct e4 e10, ct e4 e11, ct e4 e12, ct e4 e13, ct e4 e14, ct e4 e15, ct e5 e1, ct e5 e2,
      ct e5 e3, ct e5 e4, ct e5 e6, ct e5 e7, ct e5 e8, ct e5 e9, ct e5 e10, ct e5 e11,
      ct e5 e12, ct e5 e13, ct e5 e14, ct e5 e15, ct e6 e1, ct e6 e2, ct e6 e3, ct e6 e4,
      ct e6 e5, ct e6 e7, ct e6 e8, ct e6 e9, ct e6 e10, ct e6 e11, ct e6 e12, ct e6 e13,
      ct e6 e14, ct e6 e15, ct e7 e1, ct e7 e2, ct e7 e3, ct e7 e4, ct e7 e5, ct e7 e6, ct e7 e8,
      ct e7 e9, ct e7 e10, ct e7 e11, ct e7 e12, ct e7 e13, ct e7 e14, ct e7 e15, ct e8 e1,
      ct e8 e2, ct e8 e3, ct e8 e4, ct e8 e5, ct e8 e6, ct e8 e7, ct e8 e9, ct e8 e10, ct e8 e11,
      ct e8 e12, ct e8 e13, ct e8 e14, ct e8 e15, ct e9 e1, ct e9 e2, ct e9 e3, ct e9 e4,
      ct e9 e5, ct e9 e6, ct e9 e7, ct e9 e8, ct e9 e10, ct e9 e11, ct e9 e12, ct e9 e13,
      ct e9 e14, ct e9 e15, ct e10 e1, ct e10 e2, ct e10 e3, ct e10 e4, ct e10 e5, ct e10 e6,
      ct e10 e7, ct e10 e8, ct e10 e9, ct e10 e11, ct e10 e12, ct e10 e13, ct e10 e14,
      ct e10 e15, ct e11 e1, ct e11 e2, ct e11 e3, ct e11 e4, ct e11 e5, ct e11 e6, ct e11 e7,
      ct e11 e8, ct e11 e9, ct e11 e10, ct e11 e12, ct e11 e13, ct e11 e14, ct e11 e15,
      ct e12 e1, ct e12 e2, ct e12 e3, ct e12 e4, ct e12 e5, ct e12 e6, ct e12 e7, ct e12 e8,
      ct e12 e9, ct e12 e10, ct e12 e11, ct e12 e13, ct e12 e14, ct e12 e15, ct e13 e1,
      ct e13 e2, ct e13 e3, ct e13 e4, ct e13 e5, ct e13 e6, ct e13 e7, ct e13 e8, ct e13 e9,
      ct e13 e10, ct e13 e11, ct e13 e12, ct e13 e14, ct e13 e15, ct e14 e1, ct e14 e2,
      ct e14 e3, ct e14 e4, ct e14 e5, ct e14 e6, ct e14 e7, ct e14 e8, ct e14 e9, ct e14 e10,
      ct e14 e11, ct e14 e12, ct e14 e13, ct e14 e15, ct e15 e1, ct e15 e2, ct e15 e3, ct e15 e4,
      ct e15 e5, ct e15 e6, ct e15 e7, ct e15 e8, ct e15 e9, ct e15 e10, ct e15 e11, ct e15 e12,
      ct e15 e13, ct e15 e14]

@[expose] noncomputable def leafKB (pr ct : Nat → Nat → Nat) (i j k l : Nat) : Bool :=
  leafV ct i j (pr i j) k (pr i k) (pr j k) (pr (pr i j) k) l (pr i l) (pr j l) (pr (pr i j) l)
    (pr k l) (pr (pr i k) l) (pr (pr j k) l) (pr (pr (pr i j) k) l)

set_option maxRecDepth 100000 in
theorem leafK_eq (pr ct : Nat → Nat → Nat) (i j k l : Nat) :
    leafK pr ct i j k l = leafKB pr ct i j k l := rfl

theorem leafK_fun (pr ct : Nat → Nat → Nat) : leafK pr ct = leafKB pr ct :=
  funext fun i => funext fun j => funext fun k => funext fun l => leafK_eq pr ct i j k l

@[expose] noncomputable def dfsKG (M : Nat) (pr : Nat → Nat → Nat) (nbr : Nat → List Nat)
    (NM : Nat → Nat) (leaf : Nat → Nat → Nat → Nat → Bool) (i : Nat) : Bool :=
  (nbr i).all fun j =>
    !(g2B M pr i j) ||
      (fun K => (nbr i).all fun k =>
        !(K.testBit k) || !(g3B M pr i j k) ||
          (fun L => (nbr i).all fun l =>
            !(L.testBit l) || !(g4B M pr i j k l) || leaf i j k l)
          (K &&& NM k &&& NM (pr i k) &&& NM (pr j k) &&& NM (pr (pr i j) k)))
      (NM i &&& NM j &&& NM (pr i j))

@[expose] noncomputable def dfsKRB (M : Nat) (pr : Nat → Nat → Nat) (nbr : Nat → List Nat)
    (NM : Nat → Nat) (leaf : Nat → Nat → Nat → Nat → Bool) (lo len : Nat) : Bool :=
  (List.range len).all fun t => dfsKG M pr nbr NM leaf (lo + t)

theorem dfsKI_eq (M : Nat) (pr ct : Nat → Nat → Nat) (nbr : Nat → List Nat) (NM : Nat → Nat)
    (i : Nat) : dfsKI M pr ct nbr NM i = dfsKG M pr nbr NM (leafKB pr ct) i := by
  unfold dfsKI dfsKG
  simp only [g2_eq, g3_eq, g4_eq, leafK_eq]

theorem dfsKR_eq (M : Nat) (pr ct : Nat → Nat → Nat) (nbr : Nat → List Nat) (NM : Nat → Nat)
    (lo len : Nat) : dfsKR M pr ct nbr NM lo len = dfsKRB M pr nbr NM (leafKB pr ct) lo len := by
  unfold dfsKR dfsKRB
  simp only [dfsKI_eq]

theorem dfsKRB_of_singles {M : Nat} {pr : Nat → Nat → Nat} {nbr : Nat → List Nat}
    {NM : Nat → Nat} {leaf : Nat → Nat → Nat → Nat → Bool} {lo len : Nat}
    (h : ∀ q < len, dfsKG M pr nbr NM leaf (lo + q) = true) :
    dfsKRB M pr nbr NM leaf lo len = true := by
  unfold dfsKRB
  rw [List.all_eq_true]
  intro t ht
  exact h t (List.mem_range.1 ht)

end CFSG.KC.Kc3K

end
