module

public import CFSG.RankThree.PartTwo.Sec21.Hering2119KNorm
import all CFSG.RankThree.PartTwo.Sec21.Hering2119SShareK

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering2119S

open Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

structure NormElS (g g' : M4) (m : F3) (σ : Equiv.Perm (Fin 4)) : Prop where
  mul_inv : g * g' = 1
  inv_mul : g' * g = 1
  mult_sq : m * m = 1
  symp : ∀ x y, omega4 (g.mulVec x) (g.mulVec y) = m * omega4 x y
  line : ∀ i, ∃ ε : F3, ε * ε = 1 ∧ g.mulVec (lineVec i) = ε • lineVec (σ i)

theorem omega4_smul_left (c : F3) (x y : V4) : omega4 (c • x) y = c * omega4 x y := by
  simp only [omega4, Pi.smul_apply, smul_eq_mul]
  ring

theorem inA_add {x y : V4} (hx : inA x) (hy : inA y) : inA (x + y) :=
  ⟨by simp [hx.1, hy.1], by simp [hx.2, hy.2]⟩

theorem inA_smul_lineVec (c : F3) (i : Fin 4) : inA (c • lineVec i) := by
  fin_cases i <;> simp [inA, lineVec]

theorem inA_eq {v : V4} (hv : inA v) : v = v 0 • lineVec 0 + v 1 • lineVec 1 := by
  obtain ⟨h2, h3⟩ := hv
  ext i
  fin_cases i <;> simp [lineVec, h2, h3]

theorem inA_of_line {g : M4} {σ : Equiv.Perm (Fin 4)}
    (hl : ∀ i, ∃ ε : F3, ε * ε = 1 ∧ g.mulVec (lineVec i) = ε • lineVec (σ i)) {v : V4}
    (hv : inA v) : inA (g.mulVec v) := by
  obtain ⟨e0, -, h0⟩ := hl 0
  obtain ⟨e1, -, h1⟩ := hl 1
  rw [inA_eq hv, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, h0, h1, smul_smul,
    smul_smul]
  exact inA_add (inA_smul_lineVec _ _) (inA_smul_lineVec _ _)

namespace NormElS

variable {g g' : M4} {m : F3} {σ : Equiv.Perm (Fin 4)}

theorem inv_apply (h : NormElS g g' m σ) (w : V4) : g'.mulVec (g.mulVec w) = w := by
  rw [Matrix.mulVec_mulVec, h.inv_mul, Matrix.one_mulVec]

theorem apply_inv (h : NormElS g g' m σ) (w : V4) : g.mulVec (g'.mulVec w) = w := by
  rw [Matrix.mulVec_mulVec, h.mul_inv, Matrix.one_mulVec]

theorem symp_inv (h : NormElS g g' m σ) (x y : V4) :
    omega4 (g'.mulVec x) (g'.mulVec y) = m * omega4 x y := by
  have := h.symp (g'.mulVec x) (g'.mulVec y)
  rw [h.apply_inv, h.apply_inv] at this
  rw [this, ← mul_assoc, h.mult_sq, one_mul]

theorem inv_of_apply (h : NormElS g g' m σ) {a b : V4} {ε : F3} (hε : ε * ε = 1)
    (hab : g.mulVec a = ε • b) : g'.mulVec b = ε • a := by
  have hb : b = ε • g.mulVec a := by rw [hab, smul_smul, hε, one_smul]
  rw [hb, Matrix.mulVec_smul, h.inv_apply]

theorem line_inv (h : NormElS g g' m σ) (i : Fin 4) :
    ∃ ε : F3, ε * ε = 1 ∧ g'.mulVec (lineVec i) = ε • lineVec (σ.symm i) := by
  obtain ⟨ε, hε, he⟩ := h.line (σ.symm i)
  rw [Equiv.apply_symm_apply] at he
  exact ⟨ε, hε, h.inv_of_apply hε he⟩

theorem symm (h : NormElS g g' m σ) : NormElS g' g m σ.symm :=
  ⟨h.inv_mul, h.mul_inv, h.mult_sq, h.symp_inv, h.line_inv⟩

theorem presA_inv (h : NormElS g g' m σ) {v : V4} (hv : inA v) : inA (g'.mulVec v) :=
  inA_of_line h.line_inv hv

theorem ofNormEl (h : NormEl g g') : NormElS g g' 1 1 where
  mul_inv := h.mul_inv
  inv_mul := h.inv_mul
  mult_sq := one_mul 1
  symp x y := by rw [h.symp, one_mul]
  line i := ⟨1, one_mul 1, by rw [one_smul, h.fixA _ (inA_lineVec i), Equiv.Perm.one_apply]⟩

theorem comp {k k' : M4} {n : F3} {τ : Equiv.Perm (Fin 4)} (h : NormElS g g' m σ)
    (h2 : NormElS k k' n τ) : NormElS (k * g) (g' * k') (n * m) (σ.trans τ) where
  mul_inv := by rw [mul_assoc, ← mul_assoc g, h.mul_inv, one_mul, h2.mul_inv]
  inv_mul := by rw [mul_assoc, ← mul_assoc k', h2.inv_mul, one_mul, h.inv_mul]
  mult_sq := by rw [mul_mul_mul_comm, h2.mult_sq, h.mult_sq, one_mul]
  symp x y := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h2.symp, h.symp, mul_assoc]
  line i := by
    obtain ⟨ε, hε, he⟩ := h.line i
    obtain ⟨δ, hδ, hd⟩ := h2.line (σ i)
    refine ⟨δ * ε, by rw [mul_mul_mul_comm, hδ, hε, one_mul], ?_⟩
    rw [← Matrix.mulVec_mulVec, he, Matrix.mulVec_smul, hd, smul_smul, mul_comm ε δ,
      Equiv.trans_apply]

theorem conj_conj (h : NormElS g g' m σ) (X : M4) : g' * (g * X * g') * g = X := by
  calc g' * (g * X * g') * g = (g' * g) * X * (g' * g) := by simp only [mul_assoc]
    _ = X := by rw [h.inv_mul, one_mul, mul_one]

theorem conj_mul2 (h : NormElS g g' m σ) (A B : M4) :
    (g * A * g') * (g * B * g') = g * (A * B) * g' := by
  calc (g * A * g') * (g * B * g') = g * A * (g' * g) * B * g' := by simp only [mul_assoc]
    _ = g * (A * B) * g' := by rw [h.inv_mul]; simp only [mul_one, mul_assoc]

theorem conj_mul3 (h : NormElS g g' m σ) (A B C : M4) :
    (g * A * g') * (g * B * g') * (g * C * g') = g * (A * B * C) * g' := by
  rw [h.conj_mul2, h.conj_mul2]

theorem conj_one (h : NormElS g g' m σ) : g * 1 * g' = 1 := by
  rw [mul_one, h.mul_inv]

theorem conj_inj (h : NormElS g g' m σ) {A B : M4} (hAB : g * A * g' = g * B * g') : A = B := by
  have := congrArg (fun Z => g' * Z * g) hAB
  rwa [h.conj_conj, h.conj_conj] at this

theorem fix_inv (h : NormElS g g' m σ) {X : M4} {v : V4} (hfix : (g * X * g').mulVec v = v) :
    X.mulVec (g'.mulVec v) = g'.mulVec v := by
  rw [NormEl.conj_apply] at hfix
  calc X.mulVec (g'.mulVec v) = g'.mulVec (g.mulVec (X.mulVec (g'.mulVec v))) :=
        (h.inv_apply _).symm
    _ = g'.mulVec v := by rw [hfix]

theorem inF (h : NormElS g g' m σ) {a b : V4} {ε : F3} (hε : ε * ε = 1)
    (hab : g.mulVec a = ε • b) {X : M4} {w : V4} (hw : InF a X w) :
    InF b (g * X * g') (g.mulVec w) := by
  obtain ⟨c, k, hk1, hk2, rfl⟩ := hw
  have hb : b = ε • g.mulVec a := by rw [hab, smul_smul, hε, one_smul]
  refine ⟨c * ε, g.mulVec k, ?_, ?_, ?_⟩
  · rw [NormEl.conj_apply, h.inv_apply, hk1]
  · rw [hb, omega4_smul_left, h.symp, hk2, mul_zero, mul_zero]
  · rw [Matrix.mulVec_add, Matrix.mulVec_smul, hab, smul_smul]

theorem inF_inv (h : NormElS g g' m σ) {a b : V4} {ε : F3} (hε : ε * ε = 1)
    (hab : g.mulVec a = ε • b) {X : M4} {v : V4} (hv : InF b (g * X * g') v) :
    InF a X (g'.mulVec v) := by
  have := h.symm.inF hε (h.inv_of_apply hε hab) hv
  rwa [h.conj_conj] at this

theorem inH (h : NormElS g g' m σ) {a b : V4} {ε : F3} (hε : ε * ε = 1)
    (hab : g.mulVec a = ε • b) {X : M4} {w : V4} (hw : InH a X w) :
    InH b (g * X * g') (g.mulVec w) := by
  obtain ⟨h1, h2⟩ := hw
  have hb : b = ε • g.mulVec a := by rw [hab, smul_smul, hε, one_smul]
  refine ⟨by rw [NormEl.conj_apply, h.inv_apply, h1], ?_⟩
  rw [hb, omega4_smul_left, h.symp, h2, mul_zero, mul_zero]

theorem isItem (h : NormElS g g' m σ) {a b : V4} {ε : F3} (hε : ε * ε = 1)
    (hab : g.mulVec a = ε • b) {X T : M4} (hI : IsItem a X T) :
    IsItem b (g * X * g') (g * T * g') where
  symp x y := by
    rw [NormEl.conj_apply, NormEl.conj_apply, h.symp, hI.symp, h.symp_inv, ← mul_assoc,
      h.mult_sq, one_mul]
  ne_one := by
    intro h1
    apply hI.ne_one
    apply h.conj_inj
    rw [h1, h.conj_one]
  cube := by
    rw [h.conj_mul3, hI.cube, h.conj_one]
  noFix v hv hne hfix := by
    refine hI.noFix _ (h.presA_inv hv) ?_ (h.fix_inv hfix)
    intro h0
    apply hne
    rw [← h.apply_inv v, h0, Matrix.mulVec_zero]
  presF v hv := by
    have h3 := h.inF hε hab (hI.presF _ (h.inF_inv hε hab hv))
    rw [NormEl.conj_apply]
    exact h3
  sq := by
    rw [h.conj_mul2, hI.sq, h.conj_one]
  mult x y := by
    have hm : ∀ x y, omega4 (T.mulVec x) (T.mulVec y) = -omega4 x y := hI.mult
    rw [NormEl.conj_apply, NormEl.conj_apply, h.symp, hm, h.symp_inv, mul_neg, ← mul_assoc,
      h.mult_sq, one_mul]
    exact rfl
  fixa := by
    rw [NormEl.conj_apply, h.inv_of_apply hε hab, Matrix.mulVec_smul, hI.fixa,
      Matrix.mulVec_smul, hab, smul_smul, hε, one_smul]
  neg v hv := by
    have hn : ∀ w, X.mulVec w = w → T.mulVec w = -w := hI.neg
    rw [NormEl.conj_apply, hn _ (h.fix_inv hv), Matrix.mulVec_neg, h.apply_inv]
    exact rfl

theorem isItems (h : NormElS g g' m σ) {X T : Fin 4 → M4}
    (hI : ∀ i, IsItem (lineVec i) (X i) (T i)) (j : Fin 4) :
    IsItem (lineVec j) (g * X (σ.symm j) * g') (g * T (σ.symm j) * g') := by
  obtain ⟨ε, hε, hab⟩ := h.line (σ.symm j)
  rw [Equiv.apply_symm_apply] at hab
  exact h.isItem hε hab (hI _)

theorem badVec (h : NormElS g g' m σ) {a b : V4} {ε : F3} (hε : ε * ε = 1)
    (hab : g.mulVec a = ε • b) {X : M4} {v : V4} (hv : BadVec b (g * X * g') v) :
    BadVec a X (g'.mulVec v) := by
  rcases hv with ⟨hin, hne⟩ | ⟨hF, hnH⟩
  · refine Or.inl ⟨h.presA_inv hin, ?_⟩
    intro h0
    apply hne
    rw [← h.apply_inv v, h0, Matrix.mulVec_zero]
  · refine Or.inr ⟨h.inF_inv hε hab hF, ?_⟩
    intro hH
    apply hnH
    have := h.inH hε hab hH
    rwa [h.apply_inv] at this

theorem compat (h : NormElS g g' m σ) {X T : Fin 4 → M4} (hC : Compat X T) :
    Compat (fun j => g * X (σ.symm j) * g') (fun j => g * T (σ.symm j) * g') := by
  intro k hk hk1 hk3 j v hv hfix
  have hex : ∃ k0 ∈ Submonoid.closure (Set.range X ∪ Set.range T), k = g * k0 * g' := by
    refine Submonoid.closure_induction (motive := fun k _ => ∃ k0 ∈
      Submonoid.closure (Set.range X ∪ Set.range T), k = g * k0 * g') ?_ ?_ ?_ hk
    · rintro x (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · exact ⟨X (σ.symm i), Submonoid.subset_closure (Or.inl ⟨_, rfl⟩), rfl⟩
      · exact ⟨T (σ.symm i), Submonoid.subset_closure (Or.inr ⟨_, rfl⟩), rfl⟩
    · exact ⟨1, Submonoid.one_mem _, h.conj_one.symm⟩
    · rintro x y _ _ ⟨x0, hx0, rfl⟩ ⟨y0, hy0, rfl⟩
      exact ⟨x0 * y0, Submonoid.mul_mem _ hx0 hy0, h.conj_mul2 x0 y0⟩
  obtain ⟨k0, hk0, rfl⟩ := hex
  have hne : k0 ≠ 1 := by
    intro h1
    apply hk1
    rw [h1, h.conj_one]
  have hcube : k0 * k0 * k0 = 1 := by
    apply h.conj_inj
    rw [← h.conj_mul3, hk3, h.conj_one]
  obtain ⟨ε, hε, hab⟩ := h.line (σ.symm j)
  rw [Equiv.apply_symm_apply] at hab
  have hbad := h.badVec hε hab hv
  exact hC k0 hk0 hne hcube (σ.symm j) _ hbad (h.fix_inv hfix)

theorem sameCyc (h : NormElS g g' m σ) {A B : M4} :
    SameCyc (g * A * g') (g * B * g') ↔ SameCyc A B := by
  unfold SameCyc
  rw [h.conj_mul2]
  constructor
  · rintro (h1 | h1)
    · exact Or.inl (h.conj_inj h1)
    · exact Or.inr (h.conj_inj h1)
  · rintro (h1 | h1)
    · exact Or.inl (by rw [h1])
    · exact Or.inr (by rw [h1])

theorem conclK (h : NormElS g g' m σ) {X : Fin 4 → M4}
    (hK : ConclK (fun j => g * X (σ.symm j) * g')) : ConclK X := by
  obtain ⟨hfix, τ, h1, h2, h3⟩ := hK
  have hf : ∀ (i : Fin 4) (v : V4), (g * X i * g').mulVec (g.mulVec v) = g.mulVec v ↔
      X i *ᵥ v = v := by
    intro i v
    rw [NormEl.conj_apply, h.inv_apply]
    constructor
    · intro hh
      rw [← h.inv_apply (X i *ᵥ v), hh, h.inv_apply]
    · intro hh
      rw [hh]
  refine ⟨fun i j v => ?_, τ.trans σ.symm, h.sameCyc.mp h1, h.sameCyc.mp h2,
    fun hc => h3 (h.sameCyc.mpr hc)⟩
  have := hfix (σ i) (σ j) (g.mulVec v)
  simp only [Equiv.symm_apply_apply] at this
  rw [← hf i v, ← hf j v]
  exact this

end NormElS

end CFSG.RankThree.PartTwo.Sec21.Hering2119S
