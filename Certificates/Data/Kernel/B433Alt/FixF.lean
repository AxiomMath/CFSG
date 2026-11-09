module

public import Certificates.Data.Kernel.B433Alt.Fix
public import Certificates.Data.Kernel.B433Alt.OmF

public section

namespace CFSG.KC.B4A

open CFSG.KC CFSG.KC.YModel CFSG.KC.MonsterConv.Perm CFSG.KC.Loop

@[expose] noncomputable def netApplyF (k W U N X : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun j ih x => sF
      ((fun i => CFSG.KC.MonsterConv.Perm.dsw (CFSG.KC.MonsterConv.Perm.stageShift k i)
          (Nat.mul (Nat.land (Nat.shiftRight N (Nat.mul i W)) (CFSG.KC.MonsterConv.Perm.ones W)) U) x)
        (Nat.sub (Nat.sub (Nat.mul (nat_lit 2) k) (nat_lit 2)) j)) ih)
    (Nat.sub (Nat.mul (nat_lit 2) k) (nat_lit 1)) X

theorem strictN_eq_app (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem netApply_eq_F : @netApply = @netApplyF := by
  funext k W U N X
  unfold netApply netApplyF
  simp only [strictN_eq_app, sF_eq]

section
variable (Nf : Nat → Nat)

@[expose] noncomputable def apPF (P : Nat) (w : List Nat) (X : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun c _ ih x => sF (netApplyF (nat_lit 15) (wid (nat_lit 15)) (repU (wid (nat_lit 15)) P) (Nf c) x) ih)
    w X

end

theorem apP_eq_F : @apP = @apPF := by
  funext Nf P w X
  unfold apP apPF
  simp only [strictN_eq_app, sF_eq, netApply_eq_F]

theorem apPF_cons (Nf : Nat → Nat) (P c : Nat) (w : List Nat) (X : Nat) :
    apPF Nf P (c :: w) X =
      apPF Nf P w (netApplyF (nat_lit 15) (wid (nat_lit 15)) (repU (wid (nat_lit 15)) P) (Nf c) X) := by
  first
    | exact sF_eq _ _
    | (show sF _ _ = _; exact sF_eq _ _)
    | (unfold apPF; exact sF_eq _ _)

theorem apPF_append (Nf : Nat → Nat) (P : Nat) (w2 : List Nat) :
    ∀ (w1 : List Nat) (X : Nat), apPF Nf P (w1 ++ w2) X = apPF Nf P w2 (apPF Nf P w1 X)
  | [], _ => rfl
  | c :: w, X => by rw [List.cons_append, apPF_cons, apPF_cons, apPF_append Nf P w2 w]

private theorem drop_succ_mul (w : List Nat) (j L : Nat) :
    List.drop L (List.drop (j * L) w) = List.drop ((j + 1) * L) w := by
  rw [List.drop_drop]
  congr 1
  first
    | exact (Nat.succ_mul j L).symm
    | exact ((Nat.succ_mul j L).trans (Nat.add_comm _ _)).symm

theorem apPF_chain (Nf : Nat → Nat) (P : Nat) (w : List Nat) (L : Nat) (S : List Nat) :
    ∀ (m j : Nat), w.length ≤ (j + m) * L →
    (∀ k, j ≤ k → k < j + m →
      apPF Nf P (List.take L (List.drop (k * L) w)) (S.getD k 0) = S.getD (k + 1) 0) →
    apPF Nf P (List.drop (j * L) w) (S.getD j 0) = S.getD (j + m) 0
  | 0, j, hl, _ => by
    have hl' : w.length ≤ j * L := by simpa using hl
    have hd : List.drop (j * L) w = [] := by
      first
        | exact List.drop_eq_nil_of_le hl'
        | exact List.drop_eq_nil_iff.mpr hl'
        | simpa using hl'
    rw [hd]
    rfl
  | m + 1, j, hl, h => by
    have hjm : j + 1 + m = j + (m + 1) := by omega
    have e : List.drop (j * L) w =
        List.take L (List.drop (j * L) w) ++ List.drop ((j + 1) * L) w := by
      rw [← drop_succ_mul, List.take_append_drop]
    rw [e, apPF_append, h j (Nat.le_refl j) (by omega), ← hjm]
    exact apPF_chain Nf P w L S m (j + 1) (by rw [hjm]; exact hl)
      (fun k h1 h2 => h k (by omega) (by omega))

theorem apPF_beq_chain (Nf : Nat → Nat) (P : Nat) (w : List Nat) (L K : Nat) (S : List Nat)
    (X Y : Nat) (h0 : S.getD 0 0 = X) (hK : S.getD K 0 = Y) (hl : w.length ≤ K * L)
    (h : ∀ k < K, Nat.beq (apPF Nf P (List.take L (List.drop (k * L) w)) (S.getD k 0))
      (S.getD (k + 1) 0) = true) :
    Nat.beq (apPF Nf P w X) Y = true := by
  have hc := apPF_chain Nf P w L S K 0 (by rw [Nat.zero_add]; exact hl)
    (fun k _ hk => Nat.eq_of_beq_eq_true (h k (by omega)))
  rw [Nat.zero_mul, List.drop_zero, h0, Nat.zero_add, hK] at hc
  rw [hc]
  first
    | exact Nat.beq_refl Y
    | exact Nat.beq_self_eq_true Y
    | simp

theorem allLt2 {p : Nat → Prop} (h0 : p (nat_lit 0)) (h1 : p (nat_lit 1)) : ∀ k < 2, p k
  | 0, _ => h0
  | 1, _ => h1
  | _ + 2, h => absurd h (by omega)

theorem allLt3 {p : Nat → Prop} (h0 : p (nat_lit 0)) (h1 : p (nat_lit 1)) (h2 : p (nat_lit 2)) :
    ∀ k < 3, p k
  | 0, _ => h0
  | 1, _ => h1
  | 2, _ => h2
  | _ + 3, h => absurd h (by omega)

end CFSG.KC.B4A

end
