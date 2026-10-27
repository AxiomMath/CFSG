module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporPcChain
public import CFSG.Sporadic.He.FpSpec

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SporLy

open CFSG.Sporadic.He.Native CFSG.RankThree.PartTwo.Sec4.Item434SporE81

abbrev Mat := Array (Array ℕ)

@[expose] def powL (M : Mat) (e : ℕ) : Mat := if e = 1 then M else powM 5 111 M e

theorem toMat_powL (M : Mat) (e : ℕ) : toMat 5 111 (powL M e) = toMat 5 111 M ^ e := by
  unfold powL
  split_ifs with h
  · subst h
    rw [pow_one]
  · exact toMat_powM 5 111 M e

@[expose] def evalWord (gs : Array Mat) (w : List (ℕ × ℕ)) : Mat :=
  w.foldl (fun acc x => mulM 5 111 acc (powL gs[x.1]! x.2)) (idM 111)

theorem toMat_evalWord (gs : Array Mat) (w : List (ℕ × ℕ)) :
    toMat 5 111 (evalWord gs w) = (w.map fun x => toMat 5 111 gs[x.1]! ^ x.2).prod := by
  have key : ∀ (w : List (ℕ × ℕ)) (acc : Mat),
      toMat 5 111 (w.foldl (fun acc x => mulM 5 111 acc (powL gs[x.1]! x.2)) acc) =
        toMat 5 111 acc * (w.map fun x => toMat 5 111 gs[x.1]! ^ x.2).prod := by
    intro w
    induction w with
    | nil => intro acc; simp
    | cons x w ih =>
      intro acc
      rw [List.foldl_cons, ih, toMat_mulM, toMat_powL, List.map_cons, List.prod_cons, mul_assoc]
  rw [evalWord, key, toMat_idM, one_mul]

@[expose] def wordG {W : Type*} [Group W] (g : ℕ → W) (w : List (ℕ × ℕ)) : W :=
  (w.map fun x => g x.1 ^ x.2).prod

theorem wordG_mem {W : Type*} [Group W] {g : ℕ → W} {S : Subgroup W} {w : List (ℕ × ℕ)}
    (h : ∀ x ∈ w, g x.1 ∈ S) : wordG g w ∈ S :=
  Subgroup.list_prod_mem _ fun y hy => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    exact S.pow_mem (h x hx) _

theorem toMat_evalWord_eq {gs : Array Mat} {g : ℕ → GL (Fin 111) (ZMod 5)} {w : List (ℕ × ℕ)}
    (h : ∀ x ∈ w, toMat 5 111 gs[x.1]! = ((g x.1 : GL (Fin 111) (ZMod 5)) :
      Matrix (Fin 111) (Fin 111) (ZMod 5))) :
    toMat 5 111 (evalWord gs w) = ((wordG g w : GL (Fin 111) (ZMod 5)) :
      Matrix (Fin 111) (Fin 111) (ZMod 5)) := by
  rw [toMat_evalWord, wordG]
  induction w with
  | nil => simp
  | cons x w ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, Units.val_mul,
      Units.val_pow_eq_pow_val, h x (List.mem_cons_self ..),
      ih fun y hy => h y (List.mem_cons_of_mem _ hy)]

@[expose] def slpM (A B : Mat) : Mat × Mat × Bool :=
  let r3 := mulM 5 111 A B
  let r4 := mulM 5 111 r3 B
  let r5 := mulM 5 111 r3 r4
  let r9 := mulM 5 111 B r5
  let r6 := mulM 5 111 r3 r5
  let r7 := mulM 5 111 r6 r3
  let r8 := mulM 5 111 r7 r7
  let r2 := mulM 5 111 r7 r8
  let r3' := powM 5 111 r6 15
  let r4' := invM 5 111 r3'
  let r5' := mulM 5 111 r3' A
  let c := mulM 5 111 r5' r4'
  let r8' := powM 5 111 r9 12
  let r7' := invM 5 111 r8'
  let r3'' := mulM 5 111 r7' r2
  let d := mulM 5 111 r3'' r8'
  (c, d, (mulM 5 111 r3' r4' == idM 111) && (mulM 5 111 r8' r7' == idM 111))

@[expose] def slpG {W : Type*} [Group W] (a b : W) : W × W :=
  let r3 := a * b
  let r4 := r3 * b
  let r5 := r3 * r4
  let r9 := b * r5
  let r6 := r3 * r5
  let r7 := r6 * r3
  let r8 := r7 * r7
  let r2 := r7 * r8
  let r3' := r6 ^ 15
  let r4' := r3'⁻¹
  let r5' := r3' * a
  let c := r5' * r4'
  let r8' := r9 ^ 12
  let r7' := r8'⁻¹
  let r3'' := r7' * r2
  let d := r3'' * r8'
  (c, d)

theorem slpG_mem {W : Type*} [Group W] {J : Subgroup W} {a b : W} (ha : a ∈ J) (hb : b ∈ J) :
    (slpG a b).1 ∈ J ∧ (slpG a b).2 ∈ J := by
  simp only [slpG]
  have h3 := J.mul_mem ha hb
  have h4 := J.mul_mem h3 hb
  have h5 := J.mul_mem h3 h4
  have h9 := J.mul_mem hb h5
  have h6 := J.mul_mem h3 h5
  have h7 := J.mul_mem h6 h3
  have h8 := J.mul_mem h7 h7
  have h2 := J.mul_mem h7 h8
  have h3' := J.pow_mem h6 15
  have h8' := J.pow_mem h9 12
  exact ⟨J.mul_mem (J.mul_mem h3' ha) (J.inv_mem h3'),
    J.mul_mem (J.mul_mem (J.inv_mem h8') h2) h8'⟩

theorem toMat_invM {x : Mat} {g : GL (Fin 111) (ZMod 5)}
    (hx : toMat 5 111 x = (g : Matrix (Fin 111) (Fin 111) (ZMod 5)))
    (h : mulM 5 111 x (invM 5 111 x) = idM 111) :
    toMat 5 111 (invM 5 111 x) = ((g⁻¹ : GL (Fin 111) (ZMod 5)) :
      Matrix (Fin 111) (Fin 111) (ZMod 5)) := by
  have := congrArg (toMat 5 111) h
  rw [toMat_mulM, toMat_idM, hx] at this
  exact (Units.inv_eq_of_mul_eq_one_right this).symm

@[expose, reducible] def Rp (M : Mat) (g : GL (Fin 111) (ZMod 5)) : Prop :=
  toMat 5 111 M = (g : Matrix (Fin 111) (Fin 111) (ZMod 5))

theorem Rp.mul {X Y : Mat} {g h : GL (Fin 111) (ZMod 5)} (hX : Rp X g) (hY : Rp Y h) :
    Rp (mulM 5 111 X Y) (g * h) := by
  unfold Rp at *
  rw [toMat_mulM, hX, hY, Units.val_mul]

theorem Rp.pow {X : Mat} {g : GL (Fin 111) (ZMod 5)} (hX : Rp X g) (e : ℕ) :
    Rp (powM 5 111 X e) (g ^ e) := by
  unfold Rp at *
  rw [toMat_powM, hX, Units.val_pow_eq_pow_val]

theorem Rp.inv {X : Mat} {g : GL (Fin 111) (ZMod 5)} (hX : Rp X g)
    (h : mulM 5 111 X (invM 5 111 X) = idM 111) : Rp (invM 5 111 X) g⁻¹ :=
  toMat_invM hX h

theorem Rp.eq_of_eq {X Y : Mat} {g h : GL (Fin 111) (ZMod 5)} (hX : Rp X g) (hY : Rp Y h)
    (e : X = Y) : g = h := by
  subst e
  exact Units.ext (hX.symm.trans hY)

theorem slpM_rep {A B : Mat} {a b : GL (Fin 111) (ZMod 5)} (hA : Rp A a) (hB : Rp B b)
    (hok : (slpM A B).2.2 = true) :
    Rp (slpM A B).1 (slpG a b).1 ∧ Rp (slpM A B).2.1 (slpG a b).2 := by
  simp only [slpM, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨hi1, hi2⟩ := hok
  simp only [slpM, slpG]
  have p3 := hA.mul hB
  have p4 := p3.mul hB
  have p5 := p3.mul p4
  have p9 := hB.mul p5
  have p6 := p3.mul p5
  have p7 := p6.mul p3
  have p8 := p7.mul p7
  have p2 := p7.mul p8
  have p3' := p6.pow 15
  have p4' := p3'.inv hi1
  have p5' := p3'.mul hA
  have p8' := p9.pow 12
  have p7' := p8'.inv hi2
  exact ⟨p5'.mul p4', (p7'.mul p2).mul p8'⟩

@[expose] def pcCheck (n : ℕ) (P : Array Mat) (cubeW : Array (List (ℕ × ℕ)))
    (commW : Array (Array (List (ℕ × ℕ)))) : Bool :=
  decide (P.size = n) && (List.range n).all (fun i =>
    (cubeW[i]!).all (fun x => decide (i < x.1 ∧ x.1 < n)) &&
      (evalWord P [(i, 3)] == evalWord P cubeW[i]!) &&
      (List.range n).all (fun j => decide (j ≤ i) ||
        (((commW[i]!)[j]!).all (fun x => decide (i < x.1 ∧ x.1 < n)) &&
          (evalWord P [(i, 1), (j, 1)] == evalWord P ((commW[i]!)[j]! ++ [(i, 1)])))))

theorem pcCheck_size {n : ℕ} {P : Array Mat} {cubeW : Array (List (ℕ × ℕ))}
    {commW : Array (Array (List (ℕ × ℕ)))} (h : pcCheck n P cubeW commW = true) : P.size = n := by
  simp only [pcCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem pc_sound {n : ℕ} {P : Array Mat} {cubeW : Array (List (ℕ × ℕ))}
    {commW : Array (Array (List (ℕ × ℕ)))} {g : ℕ → GL (Fin 111) (ZMod 5)}
    (hg : ∀ l < n, Rp P[l]! (g l)) (h : pcCheck n P cubeW commW = true) :
    (∀ i < n, g i ^ 3 ∈ tailGroup g n (i + 1)) ∧
      ∀ i < n, ∀ j, i < j → j < n → g i * g j * (g i)⁻¹ ∈ tailGroup g n (i + 1) := by
  simp only [pcCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨hsize, h⟩ := h
  have hword : ∀ w : List (ℕ × ℕ), (∀ x ∈ w, x.1 < n) →
      Rp (evalWord P w) (wordG g w) := fun w hw =>
    toMat_evalWord_eq fun x hx => hg x.1 (hw x hx)
  have hmem : ∀ i, ∀ w : List (ℕ × ℕ), (∀ x ∈ w, i < x.1 ∧ x.1 < n) →
      wordG g w ∈ tailGroup g n (i + 1) := by
    intro i w hw
    refine wordG_mem fun x hx => ?_
    exact Subgroup.subset_closure ⟨x.1, ⟨(hw x hx).1, (hw x hx).2⟩, rfl⟩
  refine ⟨fun i hi => ?_, fun i hi j hij hjn => ?_⟩
  · obtain ⟨⟨hl, he⟩, -⟩ := h i hi
    have hl' : ∀ x ∈ cubeW[i]!, i < x.1 ∧ x.1 < n := hl
    have hrep := hword cubeW[i]! fun x hx => (hl' x hx).2
    have hrep3 := hword [(i, 3)] (by simpa using hi)
    have := hrep3.eq_of_eq hrep (beq_iff_eq.1 he)
    have e3 : wordG g [(i, 3)] = g i ^ 3 := by simp [wordG]
    rw [e3] at this
    rw [this]
    exact hmem i _ hl'
  · obtain ⟨-, h2⟩ := h i hi
    have h3 := h2 j hjn
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, List.all_eq_true] at h3
    rcases h3 with h3 | ⟨hl, he⟩
    · omega
    · have hl' : ∀ x ∈ (commW[i]!)[j]!, i < x.1 ∧ x.1 < n := hl
      have hrep := hword ((commW[i]!)[j]! ++ [(i, 1)]) (by
        intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact (hl' x hx).2
        · simp only [List.mem_singleton] at hx
          rw [hx]
          exact hi)
      have hrep2 := hword [(i, 1), (j, 1)] (by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact hi
        · exact hjn)
      have := hrep2.eq_of_eq hrep (beq_iff_eq.1 he)
      have e2 : wordG g [(i, 1), (j, 1)] = g i * g j := by simp [wordG]
      have e3 : wordG g ((commW[i]!)[j]! ++ [(i, 1)]) =
          wordG g (commW[i]!)[j]! * g i := by simp [wordG, List.map_append, List.prod_append]
      rw [e2, e3] at this
      rw [this, mul_inv_cancel_right]
      exact hmem i _ hl'

end CFSG.RankThree.PartTwo.Sec4.Item434SporLy
