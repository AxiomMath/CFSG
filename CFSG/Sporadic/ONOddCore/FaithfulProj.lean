module

public import CFSG.Sporadic.ONOddCore.MinusIdentity
public import CFSG.Sporadic.Schreier.ONTwoCentralizer

public noncomputable section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier CFSG.Sporadic.ON Matrix

theorem neg_eq_smul (v : CFSG.ONSchreier.Vec) : -v = (-1 : ZMod 3) • v := by
  funext t
  simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  generalize v t = x
  revert x
  decide

theorem neg_one_matrix : (-1 : ZMod 3) • (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) = -1 := by
  ext i j
  simp only [Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]
  generalize (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) i j = x
  revert x
  decide

theorem mulVec_smul3 (A : Matrix (Fin 154) (Fin 154) (ZMod 3)) (c : ZMod 3) (v : CFSG.ONSchreier.Vec) :
    A *ᵥ (c • v) = c • (A *ᵥ v) := Matrix.mulVec_smul _ _ _

theorem smul_dot3 (c : ZMod 3) (x y : CFSG.ONSchreier.Vec) : (c • x) ⬝ᵥ y = c * (x ⬝ᵥ y) :=
  smul_dotProduct c x y

theorem dot_smul3 (c : ZMod 3) (x y : CFSG.ONSchreier.Vec) : x ⬝ᵥ (c • y) = c * (x ⬝ᵥ y) :=
  dotProduct_smul c x y

theorem smul_mul3 (c : ZMod 3) (A B : Matrix (Fin 154) (Fin 154) (ZMod 3)) :
    (c • A) * B = c • (A * B) := Matrix.smul_mul c A B

theorem piMap_phiV
    (g : J) {i : ℕ} (hi : i < N) :
    piMap (phiV g ⟨i, hi⟩) = phiL g ⟨piMap i, piMap_lt hi⟩ := by
  have hpi := piMap_lt hi
  have hl := uu_phiL g ⟨piMap i, hpi⟩
  obtain ⟨c, hc, hcv⟩ := (normalize_spec (vv_ne_zero i hi)).1
  have hw : mat g *ᵥ vv i ≠ 0 :=
    mulVec_ne_zero_of_injective (mat_mulVec_injective g) (vv_ne_zero i hi)
  have h1 : uu (phiL g ⟨piMap i, hpi⟩) = uu (piMap (phiV g ⟨i, hi⟩)) := by
    rw [hl, Fin.val_mk, uu_piMap hi, hcv, mulVec_smul3, (normalize_spec hw).2.2 c hc,
      uu_piMap (phiV g ⟨i, hi⟩).isLt, vv_phiV, Fin.val_mk]
  exact (uu_injective (phiL g _).isLt (piMap_lt (phiV g ⟨i, hi⟩).isLt) h1).symm

theorem phiV_cases
    {g : J} (hg : phiL g = 1) {i : ℕ} (hi : i < N) :
    (phiV g ⟨i, hi⟩ : ℕ) = i ∨ (phiV g ⟨i, hi⟩ : ℕ) = sigmaMap i := by
  have h := piMap_phiV g hi
  rw [hg, Equiv.Perm.one_apply] at h
  have h' : piMap (phiV g ⟨i, hi⟩) = piMap i := h.trans (Fin.val_mk (piMap_lt hi))
  exact (piMap_eq_iff (phiV g ⟨i, hi⟩).isLt hi).1 h'

theorem walk_const {V α : Type*} {G : SimpleGraph V} {f : V → α}
    (hf : ∀ a b, G.Adj a b → f a = f b) {u v : V} (p : G.Walk u v) : f u = f v := by
  induction p with
  | nil => rfl
  | cons h _ ih => exact (hf _ _ h).trans ih

theorem zmod3_sign_mul {a b : ZMod 3} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1)
    {c : ZMod 3} (hc : c ≠ 0) (h : a * b * c = c) : a = b := by
  revert hc h
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> revert c <;> decide

theorem eq_one_of_phiL
    {g : J} (hg : phiL g = 1) : g = 1 := by
  classical
  have hsign : ∀ k : Fin 154, ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧
      mat g *ᵥ vv (spanIndex k) = ε • vv (spanIndex k) := by
    intro k
    have hk : spanIndex k < N := spanIndex_lt k
    have hv : vv (phiV g ⟨spanIndex k, hk⟩) = mat g *ᵥ vv (spanIndex k) :=
      (vv_phiV g ⟨spanIndex k, hk⟩).trans (congrArg (fun x => mat g *ᵥ vv x) (Fin.val_mk hk))
    rcases phiV_cases hg hk with h | h
    · refine ⟨1, Or.inl rfl, ?_⟩
      rw [one_smul, ← hv, h]
    · refine ⟨-1, Or.inr rfl, ?_⟩
      rw [← hv, h]
      exact (vv_sigmaMap hk).trans (neg_eq_smul _)
  choose ε hε using hsign
  have hadj : ∀ i j, gramGraph.Adj i j → ε i = ε j := by
    intro i j hij
    rw [gramGraph_adj] at hij
    have h := pairing_mulVec g (vv (spanIndex i)) (vv (spanIndex j))
    rw [(hε i).2, (hε j).2, mulVec_smul3, smul_dot3, dot_smul3] at h
    exact zmod3_sign_mul (hε i).1 (hε j).1 hij.2 (by rw [pairing]; linear_combination h)
  have hconst : ∀ i, ε i = ε 0 := fun i =>
    walk_const hadj (gramGraph_connected.preconnected i 0).some
  have hcol : mat g * basisMatrix = ε 0 • basisMatrix := by
    ext r k
    have h := congrFun (hε k).2 r
    rw [hconst k] at h
    rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
    simpa [basisMatrix, Matrix.mulVec, dotProduct] using h
  have hmat : mat g = ε 0 • 1 := by
    calc mat g = mat g * (basisMatrix * spanningBasisInverse) := by
          rw [basis_mul.1, Matrix.mul_one]
      _ = ε 0 • 1 := by rw [← Matrix.mul_assoc, hcol, smul_mul3, basis_mul.1]
  rcases (hε 0).1 with h0 | h0
  · apply mat_injective
    rw [hmat, h0, one_smul, mat_one]
  · exfalso
    apply neg_one_not_mem_J
    have hg1 : (g : GL (Fin 154) (ZMod 3)) = -1 := by
      apply Units.ext
      rw [Units.val_neg, Units.val_one]
      show mat g = -1
      rw [hmat, h0]
      exact neg_one_matrix
    rw [← hg1]
    exact g.2

theorem phiL_injective :
    Function.Injective phiL := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  rw [Subgroup.mem_bot]
  exact eq_one_of_phiL hg

theorem card_J :
    Nat.card J = 460815505920 := by
  rw [← Nat.card_congr onEquivJ.toEquiv, Nat.card_congr onEquivPv.toEquiv, ← onM_sup_M1,
    card_joint]

theorem card_Pl :
    Nat.card Pl = 460815505920 := by
  rw [← range_phiL, ← card_J]
  exact (Nat.card_congr (MonoidHom.ofInjective phiL_injective).toEquiv).symm

instance pl_pretransitive :
    MulAction.IsPretransitive Pl (Fin nL) :=
  ⟨fun i j => by
    obtain ⟨g, hg, hgj⟩ := pl_transitive i j
    exact ⟨⟨g, hg⟩, hgj⟩⟩

@[expose] def jEquivPl :
    J ≃* Pl :=
  (MonoidHom.ofInjective phiL_injective).trans (MulEquiv.subgroupCongr range_phiL)

theorem jEquivPl_apply
    (g : J) : (jEquivPl g : Equiv.Perm (Fin nL)) = phiL g := by
  rw [jEquivPl, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply, MonoidHom.ofInjective_apply]

end CFSG.Sporadic.ONOddCore
