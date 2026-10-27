module

public import CFSG.Quasithin.Background.H156Gen
public import CFSG.Quasithin.AppendixH.H14.Vocab

public section

open scoped Matrix

namespace CFSG.Quasithin.H156

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.Monster.Code

@[expose] def imgBits (cs : List ℕ) (N bs : ℕ) : ℕ :=
  (List.range N).foldl (fun a x => if bs.testBit x then a ||| (1 <<< actM cs x) else a) bs

@[expose] def orbBits (N : ℕ) (gens : List (List ℕ)) : ℕ → ℕ → ℕ
  | 0, bs => bs
  | r + 1, bs => orbBits N gens r (gens.foldl (fun b cs => imgBits cs N b) bs)

@[expose] def addSpan (N sp x : ℕ) : ℕ :=
  (List.range N).foldl (fun a s => if sp.testBit s then a ||| (1 <<< (s ^^^ x)) else a) sp

@[expose] def spanBits (N bs : ℕ) : ℕ :=
  (List.range N).foldl
    (fun sp x => if bs.testBit x then (if sp.testBit x then sp else addSpan N sp x) else sp) 1

@[expose] def SetOK {n : ℕ} (W' : Subgroup (Wn n)) (bs : ℕ) : Prop :=
  ∀ x, bs.testBit x = true → toW n x ∈ W'

theorem setOK_or {n : ℕ} {W' : Subgroup (Wn n)} {a z : ℕ} (ha : SetOK W' a) (hz : toW n z ∈ W') :
    SetOK W' (a ||| (1 <<< z)) := by
  intro x hx
  simp only [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true,
    decide_eq_true_eq] at hx
  rcases hx with hx | rfl
  · exact ha x hx
  · exact hz

theorem foldl_ok {n : ℕ} {W' : Subgroup (Wn n)} (step : ℕ → ℕ → ℕ)
    (hstep : ∀ a x, SetOK W' a → SetOK W' (step a x)) :
    ∀ (L : List ℕ) (a : ℕ), SetOK W' a → SetOK W' (L.foldl step a)
  | [], _, h => h
  | x :: L, a, h => foldl_ok step hstep L _ (hstep a x h)

theorem imgBits_ok {n : ℕ} {W' : Subgroup (Wn n)} {cs : List ℕ} (hcs : cs.length = n)
    (hinv : ∀ w ∈ W', maskHom n n cs w ∈ W') (N : ℕ) {bs : ℕ} (h : SetOK W' bs) :
    SetOK W' (imgBits cs N bs) := by
  refine foldl_ok _ (fun a x ha => ?_) _ _ h
  by_cases hx : bs.testBit x = true
  · rw [if_pos hx]
    refine setOK_or ha ?_
    rw [← maskHom_toW hcs]
    exact hinv _ (h x hx)
  · rw [if_neg hx]
    exact ha

theorem addSpan_ok {n : ℕ} {W' : Subgroup (Wn n)} (N : ℕ) {sp x : ℕ} (hsp : SetOK W' sp)
    (hx : toW n x ∈ W') : SetOK W' (addSpan N sp x) := by
  refine foldl_ok _ (fun a s ha => ?_) _ _ hsp
  by_cases hs : sp.testBit s = true
  · rw [if_pos hs]
    refine setOK_or ha ?_
    rw [toW_xor]
    exact W'.mul_mem (hsp s hs) hx
  · rw [if_neg hs]
    exact ha

theorem spanBits_ok {n : ℕ} {W' : Subgroup (Wn n)} (N : ℕ) {bs : ℕ} (h : SetOK W' bs) :
    SetOK W' (spanBits N bs) := by
  have h1 : SetOK W' 1 := by
    intro x hx
    rw [Nat.testBit_one_eq_true_iff_self_eq_zero] at hx
    subst hx
    rw [toW_zero]
    exact W'.one_mem
  refine foldl_ok _ (fun sp x hsp => ?_) _ _ h1
  by_cases hx : bs.testBit x = true
  · rw [if_pos hx]
    by_cases hs : sp.testBit x = true
    · rw [if_pos hs]
      exact hsp
    · rw [if_neg hs]
      exact addSpan_ok N hsp (h x hx)
  · rw [if_neg hx]
    exact hsp

theorem orbBits_ok {n : ℕ} {W' : Subgroup (Wn n)} {gens : List (List ℕ)}
    (hlen : ∀ cs ∈ gens, cs.length = n) (hinv : ∀ cs ∈ gens, ∀ w ∈ W', maskHom n n cs w ∈ W')
    (N : ℕ) : ∀ (r : ℕ) {bs : ℕ}, SetOK W' bs → SetOK W' (orbBits N gens r bs)
  | 0, _, h => h
  | r + 1, bs, h => by
    refine orbBits_ok hlen hinv N r ?_
    have key : ∀ (L : List (List ℕ)), (∀ cs ∈ L, cs ∈ gens) → ∀ b, SetOK W' b →
        SetOK W' (L.foldl (fun b cs => imgBits cs N b) b) := by
      intro L
      induction L with
      | nil => intro _ b hb; exact hb
      | cons cs L ih =>
        intro hL b hb
        exact ih (fun c hc => hL c (List.mem_cons_of_mem _ hc)) _
          (imgBits_ok (hlen cs (hL cs List.mem_cons_self)) (hinv cs (hL cs List.mem_cons_self))
            N hb)
    exact key gens (fun _ h => h) bs h

theorem irred_of_check {n : ℕ} (gens : List (List ℕ)) (hlen : ∀ cs ∈ gens, cs.length = n)
    (R : ℕ)
    (hcheck : ∀ m < 2 ^ n, m ≠ 0 → ∀ y < 2 ^ n,
      (spanBits (2 ^ n) (orbBits (2 ^ n) gens R (1 <<< m))).testBit y = true)
    {W' : Subgroup (Wn n)} (hinv : ∀ cs ∈ gens, ∀ w ∈ W', maskHom n n cs w ∈ W') :
    W' = ⊥ ∨ W' = ⊤ := by
  by_cases hbot : W' = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨⟨w, hw⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hbot
  obtain ⟨m, hm, hmw⟩ := toW_surj n w
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hw1 (Subtype.ext (hmw.symm.trans (toW_zero n)))
  have h0 : SetOK W' (1 <<< m) := by
    intro x hx
    simp only [Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_eq] at hx
    subst hx
    rw [hmw]
    exact hw
  have hfin := spanBits_ok (2 ^ n) (orbBits_ok hlen hinv (2 ^ n) R h0)
  rw [eq_top_iff]
  intro v _
  obtain ⟨y, hy, rfl⟩ := toW_surj n v
  exact hfin y (hcheck m hm hm0 y hy)

@[expose] def g3 : List (List ℕ) :=
  [[1, 3, 4], [1, 2, 5], [3, 2, 4], [1, 2, 6], [5, 2, 4], [1, 6, 4]]

@[expose] def g2 : List (List ℕ) := [[1, 3], [3, 2]]

theorem g3_len : ∀ cs ∈ g3, cs.length = 3 := by decide

theorem g2_len : ∀ cs ∈ g2, cs.length = 2 := by decide

theorem g3_sq : ∀ cs ∈ g3, colMat 3 cs * colMat 3 cs = 1 := by decide +kernel

theorem g2_sq : ∀ cs ∈ g2, colMat 2 cs * colMat 2 cs = 1 := by decide +kernel

theorem maskHom_eq_natHom {n : ℕ} {cs : List ℕ} (hcs : cs.length = n)
    (h : colMat n cs * colMat n cs = 1) (w : Wn n) :
    maskHom n n cs w = natHom n (ZMod 2) (mkGL n cs cs h h) w := by
  obtain ⟨m, -, rfl⟩ := toW_surj n w
  rw [maskHom_toW hcs, natHom_mkGL hcs]

theorem g3_check : ∀ m < 8, m ≠ 0 → ∀ y < 8,
    (spanBits 8 (orbBits 8 g3 2 (1 <<< m))).testBit y = true := by
  decide +kernel

theorem g2_check : ∀ m < 4, m ≠ 0 → ∀ y < 4,
    (spanBits 4 (orbBits 4 g2 1 (1 <<< m))).testBit y = true := by
  decide +kernel

theorem irred3 (W' : Subgroup (Wn 3))
    (hinv : ∀ γ ∈ natSub 3 (ZMod 2) ⊤, ∀ w ∈ W', γ w ∈ W') : W' = ⊥ ∨ W' = ⊤ := by
  refine irred_of_check g3 g3_len 2 g3_check fun cs hcs w hw => ?_
  rw [maskHom_eq_natHom (g3_len cs hcs) (g3_sq cs hcs)]
  exact hinv _ ⟨_, Subgroup.mem_top _, rfl⟩ w hw

theorem irred2 (W' : Subgroup (Wn 2))
    (hinv : ∀ γ ∈ natSub 2 (ZMod 2) ⊤, ∀ w ∈ W', γ w ∈ W') : W' = ⊥ ∨ W' = ⊤ := by
  refine irred_of_check g2 g2_len 1 g2_check fun cs hcs w hw => ?_
  rw [maskHom_eq_natHom (g2_len cs hcs) (g2_sq cs hcs)]
  exact hinv _ ⟨_, Subgroup.mem_top _, rfl⟩ w hw

@[expose] def tensAut (g : GL (Fin 3) (ZMod 2)) (h : GL (Fin 2) (ZMod 2)) : MulAut Mat32 where
  toFun X := Multiplicative.ofAdd
    ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * Multiplicative.toAdd X *
      ((h : Matrix (Fin 2) (Fin 2) (ZMod 2)))ᵀ)
  invFun X := Multiplicative.ofAdd
    (((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) * Multiplicative.toAdd X *
      (((h⁻¹ : GL (Fin 2) (ZMod 2)) : Matrix (Fin 2) (Fin 2) (ZMod 2)))ᵀ)
  left_inv X := by
    apply Multiplicative.toAdd.injective
    have hg : ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
        (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 := Units.inv_mul g
    have hh : ((h : GL (Fin 2) (ZMod 2)) : Matrix (Fin 2) (Fin 2) (ZMod 2))ᵀ *
        (((h⁻¹ : GL (Fin 2) (ZMod 2)) : Matrix (Fin 2) (Fin 2) (ZMod 2)))ᵀ = 1 := by
      rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]
    simp only [toAdd_ofAdd]
    calc _ = (((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
          (g : Matrix (Fin 3) (Fin 3) (ZMod 2))) * Multiplicative.toAdd X *
          (((h : GL (Fin 2) (ZMod 2)) : Matrix (Fin 2) (Fin 2) (ZMod 2))ᵀ *
          (((h⁻¹ : GL (Fin 2) (ZMod 2)) : Matrix (Fin 2) (Fin 2) (ZMod 2)))ᵀ) := by
            simp only [Matrix.mul_assoc]
      _ = _ := by rw [hg, hh, Matrix.one_mul, Matrix.mul_one]
  right_inv X := by
    apply Multiplicative.toAdd.injective
    have hg : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
        ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 := Units.mul_inv g
    have hh : (((h⁻¹ : GL (Fin 2) (ZMod 2)) : Matrix (Fin 2) (Fin 2) (ZMod 2)))ᵀ *
        ((h : GL (Fin 2) (ZMod 2)) : Matrix (Fin 2) (Fin 2) (ZMod 2))ᵀ = 1 := by
      rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
    simp only [toAdd_ofAdd]
    calc _ = ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
          ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))) *
          Multiplicative.toAdd X *
          ((((h⁻¹ : GL (Fin 2) (ZMod 2)) : Matrix (Fin 2) (Fin 2) (ZMod 2)))ᵀ *
          ((h : GL (Fin 2) (ZMod 2)) : Matrix (Fin 2) (Fin 2) (ZMod 2))ᵀ) := by
            simp only [Matrix.mul_assoc]
      _ = _ := by rw [hg, hh, Matrix.one_mul, Matrix.mul_one]
  map_mul' X Y := by
    apply Multiplicative.toAdd.injective
    simp [Matrix.mul_add, Matrix.add_mul]

theorem tensAut_mem (g : GL (Fin 3) (ZMod 2)) (h : GL (Fin 2) (ZMod 2)) :
    tensAut g h ∈ tensorSet32 := ⟨g, h, fun _ => rfl⟩

@[expose] def kronL (cs : List ℕ) : List ℕ :=
  (List.range 6).map fun k => cs.getD (k % 3) 0 <<< (3 * (k / 3))

@[expose] def kronR (cs : List ℕ) : List ℕ :=
  (List.range 6).map fun k =>
    ((cs.getD (k / 3) 0 &&& 1) <<< (k % 3)) ||| (((cs.getD (k / 3) 0 >>> 1) &&& 1) <<< (k % 3 + 3))

@[expose] def gT : List (List ℕ) := g3.map kronL ++ g2.map kronR

theorem gT_len : ∀ cs ∈ gT, cs.length = 6 := by decide

theorem gT_check : ∀ m < 64, m ≠ 0 → ∀ y < 64,
    (spanBits 64 (orbBits 64 gT 3 (1 <<< m))).testBit y = true := by
  decide +kernel

theorem kronL_check : ∀ cs ∈ g3, ∀ m < 64,
    matOfW (toW 6 (actM (kronL cs) m)) =
      Multiplicative.ofAdd (colMat 3 cs * Multiplicative.toAdd (matOfW (toW 6 m))) := by
  decide +kernel

theorem kronR_check : ∀ cs ∈ g2, ∀ m < 64,
    matOfW (toW 6 (actM (kronR cs) m)) =
      Multiplicative.ofAdd (Multiplicative.toAdd (matOfW (toW 6 m)) * (colMat 2 cs)ᵀ) := by
  decide +kernel

theorem matOfW_kronL {cs : List ℕ} (hcs : cs ∈ g3) (w : Wn 6) :
    matOfW (maskHom 6 6 (kronL cs) w) =
      tensAut (mkGL 3 cs cs (g3_sq cs hcs) (g3_sq cs hcs)) 1 (matOfW w) := by
  obtain ⟨m, hm, rfl⟩ := toW_surj 6 w
  have hl : (kronL cs).length = 6 := by simp [kronL]
  rw [maskHom_toW hl, kronL_check cs hcs m hm]
  simp [tensAut, mkGL]

theorem matOfW_kronR {cs : List ℕ} (hcs : cs ∈ g2) (w : Wn 6) :
    matOfW (maskHom 6 6 (kronR cs) w) =
      tensAut 1 (mkGL 2 cs cs (g2_sq cs hcs) (g2_sq cs hcs)) (matOfW w) := by
  obtain ⟨m, hm, rfl⟩ := toW_surj 6 w
  have hl : (kronR cs).length = 6 := by simp [kronR]
  rw [maskHom_toW hl, kronR_check cs hcs m hm]
  simp [tensAut, mkGL]

theorem irrT (W' : Subgroup Mat32)
    (hinv : ∀ γ ∈ Subgroup.closure tensorSet32, ∀ w ∈ W', γ w ∈ W') : W' = ⊥ ∨ W' = ⊤ := by
  have hmem : ∀ (g : GL (Fin 3) (ZMod 2)) (h : GL (Fin 2) (ZMod 2)), ∀ w ∈ W', tensAut g h w ∈ W' :=
    fun g h w hw => hinv _ (Subgroup.subset_closure (tensAut_mem g h)) w hw
  have key := irred_of_check (W' := W'.comap matOfW) gT gT_len 3 gT_check (by
    intro cs hcs w hw
    simp only [gT, List.mem_append, List.mem_map] at hcs
    rcases hcs with ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩
    · show matOfW (maskHom 6 6 (kronL c) w) ∈ W'
      rw [matOfW_kronL hc]
      exact hmem _ _ _ hw
    · show matOfW (maskHom 6 6 (kronR c) w) ∈ W'
      rw [matOfW_kronR hc]
      exact hmem _ _ _ hw)
  rcases key with h0 | h1
  · left
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨w, rfl⟩ := matOfW_bijective.2 x
    have : w ∈ W'.comap matOfW := hx
    rw [h0, Subgroup.mem_bot] at this
    rw [this, map_one]
    exact Subgroup.one_mem _
  · right
    rw [eq_top_iff]
    intro x _
    obtain ⟨w, rfl⟩ := matOfW_bijective.2 x
    have : w ∈ W'.comap matOfW := by rw [h1]; exact Subgroup.mem_top _
    exact this

end CFSG.Quasithin.H156
