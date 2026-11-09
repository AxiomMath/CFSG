module

public import Certificates.Data.Kernel.Cert690.SqA8T

public section

namespace CFSG.KC.C690

open CFSG.GF2Type.Smith1979W3.Cert690 CFSG.LargeExtraspecial.O62

@[expose] noncomputable def frcA8 {α : Sort _} (x : ℕ) (k : ℕ → α) : α :=
  Nat.rec (motive := fun _ => α) (k 0) (fun n _ => k (Nat.succ n)) x

theorem frcA8_eq {α : Sort _} (x : ℕ) (k : ℕ → α) : frcA8 x k = k x := by
  cases x <;> rfl

@[expose] noncomputable def frcLA8 {α : Sort _} (l : List ℕ) : (List ℕ → α) → α :=
  List.rec (motive := fun _ => (List ℕ → α) → α) (fun k => k [])
    (fun x _ ih k => frcA8 x fun y => ih fun ys => k (y :: ys)) l

theorem frcLA8_eq {α : Sort _} (l : List ℕ) (k : List ℕ → α) : frcLA8 l k = k l := by
  induction l generalizing k with
  | nil => rfl
  | cons x l ih =>
    change frcA8 x (fun y => frcLA8 l fun ys => k (y :: ys)) = _
    rw [frcA8_eq, ih]

@[expose] noncomputable def selA8 (G : List ℕ) : List ℕ → ℕ → ℕ :=
  List.rec (motive := fun _ => List ℕ → ℕ → ℕ) (fun _ _ => 0)
    (fun g _ ih L x => List.rec (motive := fun _ => ℕ) 0
      (fun v L' _ => Bool.rec (motive := fun _ => ℕ) (ih L' x) v (Nat.beq g x)) L) G

theorem selA8_map (F : ℕ → ℕ) (G : List ℕ) (x : ℕ) (hx : x ∈ G) : selA8 G (G.map F) x = F x := by
  induction G with
  | nil => simp at hx
  | cons g G ih =>
    change Bool.rec (motive := fun _ => ℕ) (selA8 G (G.map F) x) (F g) (Nat.beq g x) = F x
    cases h : Nat.beq g x
    · rcases List.mem_cons.1 hx with rfl | hx
      · simp at h
      · exact ih hx
    · rw [Nat.eq_of_beq_eq_true h]

@[expose] def xorLowA8 (m : ℕ) (d : Bool) : ℕ :=
  (m % 2 ^^^ Bool.rec (motive := fun _ => ℕ) 0 1 d) + 2 * (m / 2)

theorem liftF_xorLowA8 (g f z : ℕ) : liftF g f z = xorLowA8 (liftF g 0 z) (dotN f (z / 2)) := by
  have h0 : dotN 0 (z / 2) = false := by simp [dotN]
  unfold liftF xorLowA8
  rw [h0]
  generalize fB g 64 (z / 2) = p
  generalize dotN f (z / 2) = d
  generalize Code.act g (z / 2) = c
  rcases Nat.mod_two_eq_zero_or_one z with h | h <;> rw [h] <;> cases p <;> cases d <;>
    simp <;> omega

@[expose] noncomputable def zA8 (r₁ r₂ : ℕ) (w : ℕ × ℕ × ℕ × ℕ) (x : ℕ) : ℕ :=
  liftF w.2.2.1 0 (invF (if w.2.1 = 0 then r₁ else r₂) (if w.2.1 = 0 then r₁ else r₂) 0
    (invF w.2.2.1 w.2.2.2 0 x))

@[expose] noncomputable def yA8 (r₁ r₂ : ℕ) (w : ℕ × ℕ × ℕ × ℕ) (y : ℕ) : ℕ :=
  liftF w.2.2.1 0 (liftF (if w.2.1 = 0 then r₁ else r₂) 0 (invF w.2.2.1 w.2.2.2 0 y))

@[expose] noncomputable def candGA8 (φ Y : ℕ → ℕ) (P : ℕ) : Option ℕ :=
  match guessG φ with
  | some e => if e < 128 then some (qmulN (qmulN P (qWordF Y e)) e) else none
  | none => none

theorem candA8Y_eq_candGA8 (r₁ r₂ : ℕ) (w : ℕ × ℕ × ℕ × ℕ) (f : ℕ) (b : Bool × Bool) :
    candA8Y r₁ r₂ w f b = candGA8 (fun x => liftF w.1 f (zA8 r₁ r₂ w x)) (yA8 r₁ r₂ w)
      (liftF w.2.2.1 0 (sOf #[rootF r₁, rootF r₂] b.1 b.2 w.2.1)) := rfl

theorem all_congr_memA8 (l : List ℕ) (p q : ℕ → Bool) (h : ∀ x ∈ l, p x = q x) :
    l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons]
    rw [h a (by simp), ih fun x hx => h x (by simp [hx])]

theorem qWord_mem_qGens (e y : ℕ) (hy : y ∈ qWord e) : y ∈ qGens := by
  have hl : ∀ y ∈ ((List.range 6).filter fun j => (e / 2).testBit j).map (fun j => 2 ^ (j + 1)),
      y ∈ qGens := by
    intro y hy
    simp only [List.mem_map, List.mem_filter, List.mem_range] at hy
    obtain ⟨j, ⟨hj, _⟩, rfl⟩ := hy
    rcases j with _ | _ | _ | _ | _ | _ | j <;> simp [qGens]
    omega
  unfold qWord at hy
  simp only at hy
  split at hy
  · exact hl y hy
  · rcases List.mem_append.1 hy with hy | hy
    · exact hl y hy
    · simp at hy; subst hy; simp [qGens]

theorem qWordF_congrA8 (Y Y' : ℕ → ℕ) (h : ∀ y ∈ qGens, Y y = Y' y) (e : ℕ) :
    qWordF Y e = qWordF Y' e := by
  unfold qWordF
  rw [h 0 (by simp [qGens])]
  have hw := qWord_mem_qGens e
  generalize qWord e = l at hw
  generalize Y' 0 = a
  induction l generalizing a with
  | nil => rfl
  | cons g l ih =>
    simp only [List.foldl_cons]
    rw [h g (hw g (by simp)), ih (fun y hy => hw y (by simp [hy]))]

theorem guessG_congrA8 (φ ψ : ℕ → ℕ) (h : ∀ x ∈ qGens, φ x = ψ x) : guessG φ = guessG ψ := by
  have hinn : innWF φ = innWF ψ := by
    unfold innWF
    rw [h 2 (by simp [qGens]), h 4 (by simp [qGens]), h 8 (by simp [qGens]), h 16 (by simp [qGens]),
      h 32 (by simp [qGens]), h 64 (by simp [qGens])]
  unfold guessG
  rw [hinn, all_congr_memA8 qGens _ _ fun x hx => by rw [h x hx]]

theorem candGA8_congr (φ ψ Y Y' : ℕ → ℕ) (P : ℕ) (hφ : ∀ x ∈ qGens, φ x = ψ x)
    (hY : ∀ y ∈ qGens, Y y = Y' y) : candGA8 φ Y P = candGA8 ψ Y' P := by
  unfold candGA8
  rw [guessG_congrA8 φ ψ hφ]
  simp only [qWordF_congrA8 Y Y' hY]

@[expose] noncomputable def candFA8 (ψ Y : ℕ → ℕ) (P : ℕ) : Option ℕ :=
  frcA8 (2 * innWF ψ) fun e =>
    if qGens.all (fun x => qmulN (qmulN (qinvN e) x) e == ψ x) then
      if e < 128 then some (qmulN (qmulN P (qWordF Y e)) e) else none
    else none

theorem candFA8_eq (ψ Y : ℕ → ℕ) (P : ℕ) : candFA8 ψ Y P = candGA8 ψ Y P := by
  unfold candFA8 candGA8 guessG
  rw [frcA8_eq]
  split <;> rfl

@[expose] noncomputable def candA8K (ZL ML YL : List ℕ) (P f : ℕ) : Option ℕ :=
  frcLA8 (List.zipWith (fun m z => xorLowA8 m (dotN f (z / 2))) ML ZL) fun VL =>
    candFA8 (selA8 qGens VL) (selA8 qGens YL) P

@[expose] noncomputable def preA8K {α : Sort _} (r₁ r₂ : ℕ) (w : ℕ × ℕ × ℕ × ℕ) (b : Bool × Bool)
    (k : List ℕ → List ℕ → List ℕ → ℕ → α) : α :=
  frcLA8 (qGens.map (zA8 r₁ r₂ w)) fun ZL => frcLA8 (ZL.map (liftF w.1 0)) fun ML =>
    frcLA8 (qGens.map (yA8 r₁ r₂ w)) fun YL =>
      frcA8 (liftF w.2.2.1 0 (sOf #[rootF r₁, rootF r₂] b.1 b.2 w.2.1)) fun P => k ZL ML YL P

theorem preA8K_eq {α : Sort _} (r₁ r₂ : ℕ) (w : ℕ × ℕ × ℕ × ℕ) (b : Bool × Bool)
    (k : List ℕ → List ℕ → List ℕ → ℕ → α) :
    preA8K r₁ r₂ w b k = k (qGens.map (zA8 r₁ r₂ w)) ((qGens.map (zA8 r₁ r₂ w)).map (liftF w.1 0))
      (qGens.map (yA8 r₁ r₂ w)) (liftF w.2.2.1 0 (sOf #[rootF r₁, rootF r₂] b.1 b.2 w.2.1)) := by
  unfold preA8K
  rw [frcLA8_eq, frcLA8_eq, frcLA8_eq, frcA8_eq]

theorem zipWith_map_selfA8 (h : ℕ → ℕ → ℕ) (M : ℕ → ℕ) (L : List ℕ) :
    List.zipWith h (L.map M) L = L.map fun z => h (M z) z := by
  induction L with
  | nil => rfl
  | cons a L ih => simp [ih]

theorem candA8K_eq (r₁ r₂ : ℕ) (w : ℕ × ℕ × ℕ × ℕ) (b : Bool × Bool) (f : ℕ) :
    preA8K r₁ r₂ w b (fun ZL ML YL P => candA8K ZL ML YL P f) = candA8Y r₁ r₂ w f b := by
  rw [preA8K_eq, candA8Y_eq_candGA8]
  unfold candA8K
  rw [frcLA8_eq, candFA8_eq, zipWith_map_selfA8, List.map_map]
  apply candGA8_congr
  · intro x hx
    rw [selA8_map _ _ x hx]
    simp only [Function.comp_apply]
    rw [← liftF_xorLowA8]
  · intro y hy
    rw [selA8_map _ _ y hy]

@[expose] noncomputable def tagA8K (r₁ r₂ : ℕ) (Ws : List (ℕ × ℕ × ℕ × ℕ)) : List (ℕ × Option ℕ) :=
  evensF.map (fun f => (0, candOneA8G f)) ++ Ws.flatMap fun w =>
    preA8K r₁ r₂ w (false, false) fun ZL ML YL P =>
      evensF.map fun f => (if w.2.1 == 0 then 1 else 2, candA8K ZL ML YL P f)

theorem tagA8K_eq (r₁ r₂ : ℕ) (Ws : List (ℕ × ℕ × ℕ × ℕ)) : tagA8K r₁ r₂ Ws = tagA8 r₁ r₂ Ws := by
  unfold tagA8K tagA8
  congr 1
  congr 1
  funext w
  rw [preA8K_eq]
  congr 1
  funext f
  rw [← candA8K_eq, preA8K_eq]

@[expose] noncomputable def a8K (r₁ r₂ : ℕ) (Ws : List (ℕ × ℕ × ℕ × ℕ)) : Bool :=
  invPairM r₁ r₁ && invPairM r₂ r₂ && Ws.all (fun w => invPairM w.2.2.1 w.2.2.2) &&
    match cnt12A8 (tagA8K r₁ r₂ Ws) with
    | some s => certBits.all fun b => (decTA8 b s).1 == 120 && [72, 336, 408, 672].contains (decTA8 b s).2
    | none => false

theorem a8K_eq (r₁ r₂ : ℕ) (Ws : List (ℕ × ℕ × ℕ × ℕ)) : a8K r₁ r₂ Ws = a8T r₁ r₂ Ws := by
  unfold a8K a8T fuseA8
  rw [tagA8K_eq]
  rfl

end CFSG.KC.C690

end
