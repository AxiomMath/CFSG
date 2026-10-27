module

public import Certificates.Data.CFSGNative.Th.FormCheck
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Sporadic.Th

open Matrix

@[expose] def gramCode (K : Fin 2 → Fin 2 → ZMod 2) : ℕ :=
  (K 0 0).val + 2 * (K 0 1).val + 4 * (K 1 0).val + 8 * (K 1 1).val


namespace FormBase

@[expose] def toM (n : ℕ) : Matrix (Fin 2) (Fin 2) (ZMod 2) := fun a b => (ent n a b : ZMod 2)

theorem toM_apply (n : ℕ) (a b : Fin 2) : toM n a b = (ent n a b : ZMod 2) := rfl

theorem gramCode_lt (K : Fin 2 → Fin 2 → ZMod 2) : gramCode K < 16 := by
  have h00 := ZMod.val_lt (K 0 0)
  have h01 := ZMod.val_lt (K 0 1)
  have h10 := ZMod.val_lt (K 1 0)
  have h11 := ZMod.val_lt (K 1 1)
  unfold gramCode
  omega

theorem ent_gramCode (K : Fin 2 → Fin 2 → ZMod 2) (a b : Fin 2) :
    ent (gramCode K) a b = (K a b).val := by
  have h00 := ZMod.val_lt (K 0 0)
  have h01 := ZMod.val_lt (K 0 1)
  have h10 := ZMod.val_lt (K 1 0)
  have h11 := ZMod.val_lt (K 1 1)
  fin_cases a <;> fin_cases b <;>
    simp only [ent, gramCode, Fin.isValue, Fin.zero_eta, Fin.mk_one, mul_zero, mul_one, zero_add,
      add_zero, pow_zero, pow_one, Nat.div_one, Nat.reduceAdd, Nat.reducePow] <;> omega

theorem toM_gramCode (M : Matrix (Fin 2) (Fin 2) (ZMod 2)) :
    toM (gramCode fun a b => M a b) = M := by
  ext a b
  exact (congrArg (Nat.cast : ℕ → ZMod 2) (ent_gramCode _ a b)).trans (ZMod.natCast_zmod_val _)

theorem toM_nine : toM 9 = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> rfl

theorem ent_lt_two (n a b : ℕ) : ent n a b < 2 := Nat.mod_lt _ two_pos

theorem mul_toM_apply (s k t : ℕ) (a b : Fin 2) :
    (toM s * toM k * (toM t)ᵀ) a b = (prodEnt s k t a b : ZMod 2) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two, toM, prodEnt,
    Fin.val_zero, Fin.val_one]
  push_cast
  ring

theorem eqOK_iff {s k t : ℕ} : eqOK s k t = true ↔ toM s * toM k * (toM t)ᵀ = toM k := by
  have key (a b : Fin 2) :
      (toM s * toM k * (toM t)ᵀ) a b = toM k a b ↔ prodEnt s k t a b % 2 = ent k a b := by
    rw [mul_toM_apply, toM_apply, ZMod.natCast_eq_natCast_iff' _ _ 2,
      Nat.mod_eq_of_lt (ent_lt_two k a b)]
  simp only [eqOK, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨⟨h00, h01⟩, h10⟩, h11⟩
    ext a b
    rw [key]
    fin_cases a <;> fin_cases b
    exacts [h00, h01, h10, h11]
  · intro h
    have e (a b : Fin 2) := (key a b).mp (congrFun (congrFun h a) b)
    exact ⟨⟨⟨e 0 0, e 0 1⟩, e 1 0⟩, e 1 1⟩

theorem det_toM_of_invCode {n : ℕ} (h : invCode n = true) : (toM n).det = 1 := by
  rw [Matrix.det_fin_two, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
  simp only [invCode, beq_iff_eq] at h
  have hcast :
      ((ent n 0 0 * ent n 1 1 + ent n 0 1 * ent n 1 0 : ℕ) : ZMod 2) = ((1 : ℕ) : ZMod 2) :=
    (ZMod.natCast_eq_natCast_iff' _ 1 2).mpr (by rw [h])
  rw [Nat.cast_one] at hcast
  simp only [toM_apply, Fin.val_zero, Fin.val_one]
  exact_mod_cast hcast

theorem toM_eq_of_eqOK {s k t t' : ℕ} (hk : invCode k = true) (ht : eqOK s k t = true)
    (ht' : eqOK s k t' = true) : toM t = toM t' := by
  rw [eqOK_iff] at ht ht'
  have hdk := det_toM_of_invCode hk
  have hdet : (toM s).det * (toM t).det = 1 := by
    have h := congrArg Matrix.det ht
    rwa [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdk, mul_one] at h
  have hu : IsUnit (toM s * toM k) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul, hdk, mul_one]
    exact IsUnit.of_mul_eq_one _ hdet
  exact Matrix.transpose_injective (hu.mul_left_cancel (ht.trans ht'.symm))

theorem mem_of_lookup_eq_some {st : List (ℕ × ℕ)} {p s : ℕ} (h : st.lookup p = some s) :
    (p, s) ∈ st := by
  induction st with
  | nil => simp at h
  | cons e st ih =>
    obtain ⟨w, t⟩ := e
    rw [List.lookup_cons] at h
    by_cases hpw : p = w
    · subst hpw
      simp only [beq_self_eq_true, Option.some.injEq] at h
      simp [h]
    · rw [show (p == w) = false by simpa using hpw] at h
      exact List.mem_cons_of_mem _ (ih h)

def Correct (m : ℕ) (S : ℕ → Matrix (Fin 2) (Fin 2) (ZMod 2)) (st : List (ℕ × ℕ)) : Prop :=
  ∀ e ∈ st, e.1 < m ∧ toM e.2 = S e.1

theorem propagate_spec {m : ℕ} {code : ℕ → ℕ → ℕ} {S : ℕ → Matrix (Fin 2) (Fin 2) (ZMod 2)}
    (hS : ∀ i < m, ∀ j < m, S i * toM (code i j) * (S j)ᵀ = toM (code i j))
    (tree st : List (ℕ × ℕ)) (hst : Correct m S st) :
    propagate m code tree st ≠ .dead ∧
      ∀ st', propagate m code tree st = .ok st' → Correct m S st' := by
  induction tree generalizing st with
  | nil =>
    refine ⟨by simp [propagate], fun st' h => ?_⟩
    simp only [propagate, Outcome.ok.injEq] at h
    exact h ▸ hst
  | cons e rest ih =>
    obtain ⟨v, p⟩ := e
    by_cases hv : v < m
    · by_cases hk : invCode (code p v) = true
      · cases hl : st.lookup p with
        | none => simp [propagate, hv, hk, hl]
        | some s =>
          obtain ⟨hp, hs⟩ := hst _ (mem_of_lookup_eq_some hl)
          have hsol : eqOK s (code p v) (gramCode fun a b => S v a b) = true := by
            rw [eqOK_iff, hs, toM_gramCode]
            exact hS p hp v hv
          cases hf : (List.range 16).find? (eqOK s (code p v)) with
          | none =>
            rw [List.find?_eq_none] at hf
            exact absurd hsol (hf _ (List.mem_range.mpr (gramCode_lt _)))
          | some t =>
            have ht : toM t = S v := by
              rw [toM_eq_of_eqOK hk (List.find?_some hf) hsol, toM_gramCode]
            have hst' : Correct m S ((v, t) :: st) := by
              intro e he
              rcases List.mem_cons.mp he with rfl | he
              · exact ⟨hv, ht⟩
              · exact hst e he
            simpa [propagate, hv, hk, hl, hf] using ih _ hst'
      · simp [propagate, hv, hk]
    · simp [propagate, hv]

theorem propagate_covers {m : ℕ} {code : ℕ → ℕ → ℕ} :
    ∀ (tree st st' : List (ℕ × ℕ)), propagate m code tree st = .ok st' →
      ∀ w, ((∃ t, (w, t) ∈ st) ∨ ∃ e ∈ tree, e.1 = w) → ∃ t, (w, t) ∈ st'
  | [], st, st', h, w, hw => by
    simp only [propagate, Outcome.ok.injEq] at h
    subst h
    simpa using hw
  | (v, p) :: rest, st, st', h, w, hw => by
    by_cases hv : v < m
    · by_cases hk : invCode (code p v) = true
      · cases hl : st.lookup p with
        | none => simp [propagate, hv, hk, hl] at h
        | some s =>
          cases hf : (List.range 16).find? (eqOK s (code p v)) with
          | none => simp [propagate, hv, hk, hl, hf] at h
          | some t =>
            have h' : propagate m code rest ((v, t) :: st) = .ok st' := by
              simpa [propagate, hv, hk, hl, hf] using h
            refine propagate_covers rest _ st' h' w ?_
            rcases hw with ⟨t', ht'⟩ | ⟨e, he, rfl⟩
            · exact Or.inl ⟨t', List.mem_cons_of_mem _ ht'⟩
            · rcases List.mem_cons.mp he with rfl | he
              · exact Or.inl ⟨t, List.mem_cons_self⟩
              · exact Or.inr ⟨e, he, rfl⟩
      · simp [propagate, hv, hk] at h
    · simp [propagate, hv] at h

theorem eq_one_of_formBaseCheck_aux {m : ℕ} {code : ℕ → ℕ → ℕ}
    (hcheck : formBaseCheck m code = true) {S : ℕ → Matrix (Fin 2) (Fin 2) (ZMod 2)}
    (hS : ∀ i < m, ∀ j < m, S i * toM (code i j) * (S j)ᵀ = toM (code i j)) :
    ∀ i < m, S i = 1 := by
  simp only [formBaseCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at hcheck
  obtain ⟨⟨hm, hcov⟩, hall⟩ := hcheck
  set s0 := gramCode fun a b => S 0 a b with hs0
  have hc := hall s0 (gramCode_lt _)
  have h0 : Correct m S [(0, s0)] := by
    intro e he
    rw [List.mem_singleton] at he
    subst he
    exact ⟨hm, toM_gramCode _⟩
  obtain ⟨hdead, hok⟩ := propagate_spec hS (bfsTree m code) _ h0
  unfold candidateOK at hc
  rcases hp : propagate m code (bfsTree m code) [(0, s0)] with _ | _ | st
  · rw [hp] at hc
    simp at hc
  · exact absurd hp hdead
  · rw [hp] at hc
    have hst := hok st hp
    have hall' : allEqs code st = true := by
      simp only [allEqs, List.all_eq_true]
      intro e he f hf
      obtain ⟨he1, he2⟩ := hst e he
      obtain ⟨hf1, hf2⟩ := hst f hf
      rw [eqOK_iff, he2, hf2]
      exact hS _ he1 _ hf1
    have h9 : ∀ e ∈ st, e.2 = 9 := by
      simpa [hall', List.all_eq_true] using hc
    intro i hi
    have hw : (∃ t, (i, t) ∈ [(0, s0)]) ∨ ∃ e ∈ bfsTree m code, e.1 = i := by
      simp only [treeCovers, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
        List.any_eq_true] at hcov
      rcases hcov i hi with rfl | he
      · exact Or.inl ⟨_, List.mem_singleton_self _⟩
      · exact Or.inr he
    obtain ⟨t, ht⟩ := propagate_covers _ _ _ hp i hw
    rw [← (hst _ ht).2, h9 _ ht, toM_nine]

theorem eq_one_of_formBaseCheck {m : ℕ} {code : ℕ → ℕ → ℕ}
    (K : Fin m → Fin m → Matrix (Fin 2) (Fin 2) (ZMod 2))
    (hcode : ∀ i j : Fin m, code i j = gramCode fun a b => K i j a b)
    (hcheck : formBaseCheck m code = true)
    (S : Fin m → Matrix (Fin 2) (Fin 2) (ZMod 2)) (hS : ∀ i j, S i * K i j * (S j)ᵀ = K i j)
    (i : Fin m) : S i = 1 := by
  have key := eq_one_of_formBaseCheck_aux hcheck
    (S := fun n => if h : n < m then S ⟨n, h⟩ else 1) (fun i hi j hj => by
      simp only [hi, hj, dite_true]
      rw [hcode ⟨i, hi⟩ ⟨j, hj⟩, toM_gramCode]
      exact hS _ _) i i.isLt
  simpa using key

end FormBase

open FormBase in
theorem eq_one_of_isometry_fixing_planes {d m : ℕ} (F : Matrix (Fin d) (Fin d) (ZMod 2))
    (c : Fin m → Fin 2 → (Fin d → ZMod 2))
    (hspan : Submodule.span (ZMod 2) (Set.range (fun p : Fin m × Fin 2 => c p.1 p.2)) = ⊤)
    (code : ℕ → ℕ → ℕ)
    (hcode : ∀ i j : Fin m, code i j = gramCode (fun a b => c i a ⬝ᵥ (F *ᵥ c j b)))
    (hcheck : formBaseCheck m code = true)
    (g : Matrix (Fin d) (Fin d) (ZMod 2)) (hg : gᵀ * F * g = F)
    (hfix : ∀ i a, g *ᵥ c i a ∈ Submodule.span (ZMod 2) ({c i 0, c i 1} : Set (Fin d → ZMod 2))) :
    g = 1 := by
  choose r s hrs using fun i a => Submodule.mem_span_pair.mp (hfix i a)
  let S : Fin m → Matrix (Fin 2) (Fin 2) (ZMod 2) := fun i a => ![r i a, s i a]
  have hgc (i : Fin m) (a : Fin 2) : g *ᵥ c i a = ∑ b, S i a b • c i b := by
    rw [Fin.sum_univ_two, ← hrs i a]
    simp [S]
  have hiso (u w : Fin d → ZMod 2) : (g *ᵥ u) ⬝ᵥ (F *ᵥ (g *ᵥ w)) = u ⬝ᵥ (F *ᵥ w) := by
    rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose,
      Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hg, ← Matrix.dotProduct_mulVec]
  let K : Fin m → Fin m → Matrix (Fin 2) (Fin 2) (ZMod 2) := fun i j =>
    Matrix.of fun a b => c i a ⬝ᵥ (F *ᵥ c j b)
  have hK (i j : Fin m) : S i * K i j * (S j)ᵀ = K i j := by
    ext a b
    have h := hiso (c i a) (c j b)
    rw [hgc i a, hgc j b] at h
    simp only [Fin.sum_univ_two, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add,
      add_dotProduct, smul_dotProduct, dotProduct_smul, smul_eq_mul] at h
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two, K, Matrix.of_apply]
    rw [← h]
    ring
  have hS1 := eq_one_of_formBaseCheck K (fun i j => hcode i j) hcheck S hK
  have hfixed (i : Fin m) (a : Fin 2) : g *ᵥ c i a = c i a := by
    rw [hgc, hS1 i]
    simp [Matrix.one_apply]
  have hlin : Matrix.toLin' g = LinearMap.id :=
    LinearMap.ext_on_range hspan fun p => by simp [Matrix.toLin'_apply, hfixed]
  exact Matrix.toLin'.injective (hlin.trans Matrix.toLin'_one.symm)

theorem eq_one_of_isometry_image_planes {d m : ℕ} (F : Matrix (Fin d) (Fin d) (ZMod 2))
    (c : Fin m → Fin 2 → (Fin d → ZMod 2))
    (hspan : Submodule.span (ZMod 2) (Set.range (fun p : Fin m × Fin 2 => c p.1 p.2)) = ⊤)
    (code : ℕ → ℕ → ℕ)
    (hcode : ∀ i j : Fin m, code i j = gramCode (fun a b => c i a ⬝ᵥ (F *ᵥ c j b)))
    (hcheck : formBaseCheck m code = true)
    (g : Matrix (Fin d) (Fin d) (ZMod 2)) (hg : gᵀ * F * g = F)
    (hstab : ∀ i, (fun v => g *ᵥ v) ''
        (Submodule.span (ZMod 2) {c i 0, c i 1} : Set (Fin d → ZMod 2)) =
      (Submodule.span (ZMod 2) {c i 0, c i 1} : Set (Fin d → ZMod 2))) :
    g = 1 := by
  refine eq_one_of_isometry_fixing_planes F c hspan code hcode hcheck g hg fun i a => ?_
  have hmem : c i a ∈ (Submodule.span (ZMod 2) {c i 0, c i 1} : Set (Fin d → ZMod 2)) :=
    Submodule.subset_span (by fin_cases a <;> simp)
  have himg := Set.mem_image_of_mem (fun v => g *ᵥ v) hmem
  rw [hstab i] at himg
  exact himg

end CFSG.Sporadic.Th
