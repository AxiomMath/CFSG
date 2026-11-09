module

public import Certificates.Data.Kernel.PermCent.KGrpC

public section

namespace CFSG.Certificates.Kernel.PkCV.SemiReg

@[expose] def applyW (A B : Nat → Nat) (w : List Bool) (x : Nat) : Nat :=
  w.foldr (fun s y => if s then B y else A y) x

theorem applyW_lt {n : Nat} {A B : Nat → Nat} (hA : ∀ x < n, A x < n) (hB : ∀ x < n, B x < n)
    (w : List Bool) {x : Nat} (hx : x < n) : applyW A B w x < n := by
  induction w with
  | nil => exact hx
  | cons s w ih =>
    show (if s then B (applyW A B w x) else A (applyW A B w x)) < n
    cases s
    · exact hA _ ih
    · exact hB _ ih

theorem applyW_comm {n : Nat} {A B S : Nat → Nat} (hA : ∀ x < n, A x < n) (hB : ∀ x < n, B x < n)
    (hSA : ∀ x < n, S (A x) = A (S x)) (hSB : ∀ x < n, S (B x) = B (S x)) (w : List Bool) {x : Nat}
    (hx : x < n) : S (applyW A B w x) = applyW A B w (S x) := by
  induction w with
  | nil => rfl
  | cons s w ih =>
    show S (if s then B (applyW A B w x) else A (applyW A B w x)) =
      (if s then B (applyW A B w (S x)) else A (applyW A B w (S x)))
    cases s
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hSA _ (applyW_lt hA hB w hx), ih]
    · simp only [↓reduceIte]
      rw [hSB _ (applyW_lt hA hB w hx), ih]

@[expose] def semiregChk (n : Nat) (A B : Nat → Nat) (R : List Nat) (ρ : List Nat) (W : List (List Bool))
    (wit : List (Nat × Bool)) : Bool :=
  (List.range n).all (fun p => decide (ρ.getD p 0 < R.length) &&
    applyW A B (W.getD p []) (R.getD (ρ.getD p 0) 0) == p) &&
  (List.range R.length).all fun i => decide (R.getD i 0 < n) &&
    (List.range n).all fun j => j == R.getD i 0 ||
      (let ps := wit.getD (i * n + j) (0, false)
       let g := if ps.2 then B else A
       decide (ps.1 < n) && ρ.getD ps.1 0 == i && ρ.getD (g ps.1) 0 == i &&
         applyW A B (W.getD (g ps.1) []) j != g (applyW A B (W.getD ps.1 []) j))

theorem semireg_core {n : Nat} {A B S : Nat → Nat} {R ρ : List Nat} {W : List (List Bool)}
    {wit : List (Nat × Bool)} (hA : ∀ x < n, A x < n) (hB : ∀ x < n, B x < n)
    (hSA : ∀ x < n, S (A x) = A (S x)) (hSB : ∀ x < n, S (B x) = B (S x))
    (hSn : ∀ x < n, S x < n) (h : semiregChk n A B R ρ W wit = true) : ∀ p < n, S p = p := by
  simp only [semiregChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    decide_eq_true_eq] at h
  obtain ⟨hW, hR⟩ := h
  have hSp : ∀ p < n, S p = applyW A B (W.getD p []) (S (R.getD (ρ.getD p 0) 0)) := by
    intro p hp
    have e := (hW p hp).2
    have hr := (hR _ (hW p hp).1).1
    calc S p = S (applyW A B (W.getD p []) (R.getD (ρ.getD p 0) 0)) := by rw [e]
      _ = _ := applyW_comm hA hB hSA hSB _ hr
  have hfix : ∀ i < R.length, S (R.getD i 0) = R.getD i 0 := by
    intro i hi
    obtain ⟨hr, hj⟩ := hR i hi
    by_contra hne
    have := hj (S (R.getD i 0)) (hSn _ hr)
    rw [show (S (R.getD i 0) == R.getD i 0) = false from beq_eq_false_iff_ne.mpr hne,
      Bool.false_or, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      beq_iff_eq, beq_iff_eq, bne_iff_ne] at this
    obtain ⟨⟨⟨hp, hρp⟩, hρg⟩, hneq⟩ := this
    apply hneq
    generalize wit.getD (i * n + S (R.getD i 0)) (0, false) = ps at hp hρp hρg hneq
    obtain ⟨p, s⟩ := ps
    simp only at hp hρp hρg ⊢
    have hg : (if s then B else A) p < n := by
      cases s
      · exact hA p hp
      · exact hB p hp
    have hSg : S ((if s then B else A) p) = (if s then B else A) (S p) := by
      cases s
      · exact hSA p hp
      · exact hSB p hp
    calc applyW A B (W.getD ((if s then B else A) p) []) (S (R.getD i 0))
        = S ((if s then B else A) p) := by rw [hSp _ hg, hρg]
      _ = (if s then B else A) (S p) := hSg
      _ = _ := by rw [hSp p hp, hρp]
  intro p hp
  rw [hSp p hp, hfix _ (hW p hp).1, (hW p hp).2]

variable {n : Nat} [Small n]

theorem comm_img {σ a : CV n} (h : eq22C σ a a σ = true) :
    ∀ x < n, img n σ.1 (img n a.1 x) = img n a.1 (img n σ.1 x) := by
  rw [eq22C_eq, decide_eq_true_iff] at h
  intro x hx
  have := congrArg (fun c : CV n => (ev c ⟨x, hx⟩ : Nat)) h
  simp only [ev_mul, Equiv.Perm.mul_apply, ev_apply] at this
  exact this

theorem eq_one_of_semireg (a b : CV n) {R ρ : List Nat} {W : List (List Bool)}
    {wit : List (Nat × Bool)} (h : semiregChk n (img n a.1) (img n b.1) R ρ W wit = true)
    (σ : CV n) (ha : eq22C σ a a σ = true) (hb : eq22C σ b b σ = true) : σ = 1 := by
  have hfix := semireg_core (S := img n σ.1) (fun x hx => a.2.2.1 x hx) (fun x hx => b.2.2.1 x hx)
    (comm_img ha) (comm_img hb) (fun x hx => σ.2.2.1 x hx) h
  apply ev_injective
  ext i
  rw [ev_apply, ev_one, Equiv.Perm.one_apply]
  exact hfix i i.2

theorem centTrivC_of_semireg (L : List (CV n)) (a b : CV n) {R ρ : List Nat}
    {W : List (List Bool)} {wit : List (Nat × Bool)}
    (h : semiregChk n (img n a.1) (img n b.1) R ρ W wit = true) :
    KGrp.centTrivC L a b = true := by
  unfold KGrp.centTrivC
  rw [List.all_eq_true]
  intro σ _
  by_cases hc : (eq22C σ a a σ && eq22C σ b b σ) = true
  · rw [Bool.and_eq_true] at hc
    rw [eq_one_of_semireg a b h σ hc.1 hc.2]
    simp
  · rw [Bool.not_eq_true] at hc
    rw [hc]
    rfl

end CFSG.Certificates.Kernel.PkCV.SemiReg

end
