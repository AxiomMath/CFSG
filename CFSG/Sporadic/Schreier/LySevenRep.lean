
module

public import CFSG.Sporadic.Schreier.LyCover
public import CFSG.Sporadic.Schreier.LyCheckSeven
public import CFSG.Sporadic.Schreier.LyOperatorBase

public noncomputable section

namespace CFSG.Sporadic.LySchreier

open CFSG.Sporadic.Ly CFSG.Sporadic.Ly.Native CFSG.Sporadic.LySchreier.Native
open CFSG.Sporadic.He.Native Matrix
open CFSG.Sporadic.Th (allIn_eq_true)

theorem restr7_of_eq [LySeed]
    {g : J} {R : Matrix (Fin 7) (Fin 7) (ZMod 5)} (h : mat g * lyU = lyU * R) :
    restr7 g = R := by
  ext r c
  have := congrFun (congrFun h ⟨r.val, by omega⟩) c
  rw [restr7, of_apply, this, mul_apply]
  simp only [lyU_pivot r, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true]

theorem mat_one_mul_lyU
    [LySeed] : mat 1 * lyU = lyU * (1 : Matrix (Fin 7) (Fin 7) (ZMod 5)) := by
  rw [mat_one, Matrix.one_mul, Matrix.mul_one]

theorem restr7_one
    [LySeed] : restr7 1 = 1 := restr7_of_eq mat_one_mul_lyU

theorem stabU_mul [LySeed] {g h : J} (hg : mat g * lyU = lyU * restr7 g)
    (hh : mat h * lyU = lyU * restr7 h) :
    mat (g * h) * lyU = lyU * (restr7 g * restr7 h) := by
  rw [mat_mul, Matrix.mul_assoc, hh, ← Matrix.mul_assoc, hg, Matrix.mul_assoc]

instance [LySeed] : Finite J := inferInstance

@[expose] def stabU [LySeed] : Subgroup J where
  carrier := {g | mat g * lyU = lyU * restr7 g}
  mul_mem' {g h} hg hh := by
    show mat (g * h) * lyU = lyU * restr7 (g * h)
    rw [stabU_mul hg hh, restr7_of_eq (stabU_mul hg hh)]
  one_mem' := by
    show mat 1 * lyU = lyU * restr7 1
    rw [restr7_one]; exact mat_one_mul_lyU
  inv_mem' {g} hg := by
    have hpow : ∀ n : ℕ, mat (g ^ n) * lyU = lyU * restr7 (g ^ n) := by
      intro n
      induction n with
      | zero => rw [pow_zero, restr7_one]; exact mat_one_mul_lyU
      | succ n ih => rw [pow_succ, stabU_mul ih hg, restr7_of_eq (stabU_mul ih hg)]
    have hinv : g⁻¹ = g ^ (orderOf g - 1) := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel (orderOf_pos g),
        pow_orderOf_eq_one]
    show mat g⁻¹ * lyU = lyU * restr7 g⁻¹
    rw [hinv]
    exact hpow _

theorem mem_stabU [LySeed]
    {g : J} : g ∈ stabU ↔ mat g * lyU = lyU * restr7 g := Iff.rfl

@[expose] def rho7
    [LySeed] : stabU →* Matrix (Fin 7) (Fin 7) (ZMod 5) where
  toFun g := restr7 g
  map_one' := restr7_one
  map_mul' g h := restr7_of_eq (stabU_mul g.2 h.2)

theorem rho7_apply [LySeed]
    (g : stabU) : rho7 g = restr7 g := rfl

theorem rho7_inv [LySeed]
    (g : stabU) : rho7 g⁻¹ = (rho7 g)⁻¹ := by
  rw [eq_comm, Matrix.inv_eq_left_inv]
  rw [← map_mul, inv_mul_cancel, map_one]

@[expose, instance_reducible] def sevenAct
    [LySeed] : MulAction stabU (Fin 7 → ZMod 5) where
  smul g v := rho7 g *ᵥ v
  one_smul v := by
    show rho7 1 *ᵥ v = v
    rw [map_one, Matrix.one_mulVec]
  mul_smul g h v := by
    show rho7 (g * h) *ᵥ v = rho7 g *ᵥ (rho7 h *ᵥ v)
    rw [map_mul, Matrix.mulVec_mulVec]

@[expose] def rhoP
    [LySeed] : stabU →* Equiv.Perm (Fin 7 → ZMod 5) :=
  @MulAction.toPermHom stabU (Fin 7 → ZMod 5) _ sevenAct

theorem rhoP_apply [LySeed]
    (g : stabU) (v : Fin 7 → ZMod 5) : rhoP g v = rho7 g *ᵥ v := rfl

theorem rhoP_eq_one [LySeed]
    {g : stabU} (h : rho7 g = 1) : rhoP g = 1 := by
  ext v
  rw [rhoP_apply, h, Matrix.one_mulVec]
  rfl

@[expose] def toMatU (Y : Array (Array ℕ)) : Matrix (Fin 111) (Fin 7) (ZMod 5) :=
  Matrix.of fun i m => ((Y[i.val]!)[m.val]! : ZMod 5)

theorem ofFn_get!' {α : Type*} [Inhabited α] {n : ℕ} (f : Fin n → α) {i : ℕ} (hi : i < n) :
    (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  rw [getElem!_pos (Array.ofFn f) i (by simpa using hi), Array.getElem_ofFn]

theorem toMatU_uArr : toMatU uArr = lyU := by
  ext j m
  simp only [toMatU, uArr, of_apply, lyU, ofFn_get!' _ j.isLt, ofFn_get!' _ m.isLt]

theorem uArr_get (k : ℕ) (hk : k < 111) (m : ℕ) (hm : m < 7) :
    ((uArr[k]!)[m]! : ZMod 5) = lyU ⟨k, hk⟩ ⟨m, hm⟩ := by
  rw [← toMatU_uArr]
  rfl

theorem toMatU_mulXU (X : Mat) : toMatU (mulXU X) = toMat 5 111 X * lyU := by
  ext i m
  simp only [toMatU, mulXU, of_apply, ofFn_get!' _ i.isLt, ofFn_get!' _ m.isLt, mul_apply,
    toMat_apply]
  rw [ZMod.natCast_mod, fold_add_eq_sum, Nat.cast_sum,
    ← Fin.sum_univ_eq_sum_range (fun k => (((X[i.val]!)[k]! * (uArr[k]!)[m.val]! : ℕ) : ZMod 5))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Nat.cast_mul, uArr_get k.val k.isLt m.val m.isLt]

theorem toMatU_mulUR (R : Array ℕ) : toMatU (mulUR R) = lyU * mat7 R := by
  ext i c
  simp only [toMatU, mulUR, of_apply, ofFn_get!' _ i.isLt, ofFn_get!' _ c.isLt, mul_apply,
    mat7]
  rw [ZMod.natCast_mod, fold_add_eq_sum, Nat.cast_sum,
    ← Fin.sum_univ_eq_sum_range (fun m => (((uArr[i.val]!)[m]! * R[7 * m + c.val]! : ℕ) : ZMod 5))]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Nat.cast_mul, uArr_get i.val i.isLt m.val m.isLt]

theorem mat7_restrArr [LySeed]
    {X : Mat} {g : J} (hX : RepM X g) : mat7 (restrArr X) = restr7 g := by
  ext r c
  have e := congrFun (congrFun (toMatU_mulXU X) ⟨r.val, by omega⟩) c
  simp only [mat7, restrArr, of_apply, restr7]
  rw [ofFn_get!' _ (by omega)]
  simp only
  rw [show (7 * r.val + c.val) / 7 = r.val by omega,
    show (7 * r.val + c.val) % 7 = c.val by omega, ← hX]
  exact e

theorem mem_stabU_of_stabOK [LySeed]
    {X : Mat} {g : J} (hX : RepM X g) (h : stabOK X = true) :
    g ∈ stabU := by
  unfold stabOK at h
  rw [beq_iff_eq] at h
  have e := congrArg toMatU h
  rw [toMatU_mulXU, toMatU_mulUR, mat7_restrArr hX, hX] at e
  exact e

@[expose] def toVec7 (v : Array ℕ) : Fin 7 → ZMod 5 := fun r => (v[r.val]! : ZMod 5)

theorem toVec7_mv7 (R v : Array ℕ) : toVec7 (mv7 R v) = mat7 R *ᵥ toVec7 v := by
  funext r
  simp only [toVec7, mv7, ofFn_get!' _ r.isLt, Matrix.mulVec, dotProduct, mat7, of_apply]
  rw [ZMod.natCast_mod, fold_add_eq_sum, Nat.cast_sum,
    ← Fin.sum_univ_eq_sum_range (fun c => ((R[7 * r.val + c]! * v[c]! : ℕ) : ZMod 5))]
  simp only [Nat.cast_mul]

theorem toVec7_stdVec (i : Fin 7) : toVec7 (stdVec i) = Pi.single i 1 := by
  funext r
  simp only [toVec7, stdVec, ofFn_get!' _ r.isLt]
  by_cases h : r = i
  · subst h; simp
  · rw [ite_eq_right (fun e => h (Fin.ext e)), Pi.single_eq_of_ne h]; rfl

theorem toVec7_inj {v w : Array ℕ} (hv : v.size = 7 ∧ ∀ x ∈ v, x < 5)
    (hw : w.size = 7 ∧ ∀ x ∈ w, x < 5) (h : toVec7 v = toVec7 w) : v = w := by
  apply Array.ext (by rw [hv.1, hw.1])
  intro r h1 h2
  have e := congrFun h ⟨r, by rw [← hv.1]; exact h1⟩
  simp only [toVec7] at e
  rw [getElem!_pos v r h1, getElem!_pos w r h2] at e
  have := (ZMod.natCast_eq_natCast_iff' _ _ 5).1 e
  rwa [Nat.mod_eq_of_lt (hv.2 _ (Array.getElem_mem h1)),
    Nat.mod_eq_of_lt (hw.2 _ (Array.getElem_mem h2))] at this

theorem mat7_inj {X Y : Array ℕ} (hX : X.size = 49 ∧ ∀ x ∈ X, x < 5)
    (hY : Y.size = 49 ∧ ∀ x ∈ Y, x < 5) (h : mat7 X = mat7 Y) : X = Y := by
  apply Array.ext (by rw [hX.1, hY.1])
  intro t h1 h2
  have ht : t < 49 := by rw [← hX.1]; exact h1
  have e := congrFun (congrFun h ⟨t / 7, by omega⟩) ⟨t % 7, by omega⟩
  simp only [mat7, of_apply] at e
  rw [show 7 * (t / 7) + t % 7 = t by omega, getElem!_pos X t h1, getElem!_pos Y t h2] at e
  have := (ZMod.natCast_eq_natCast_iff' _ _ 5).1 e
  rwa [Nat.mod_eq_of_lt (hX.2 _ (Array.getElem_mem h1)),
    Nat.mod_eq_of_lt (hY.2 _ (Array.getElem_mem h2))] at this

theorem mat7_id7 : mat7 id7 = 1 := by
  ext i j
  simp only [mat7, of_apply, one_apply, id7]
  rw [ofFn_get!' _ (by omega)]
  simp only
  rw [show (7 * i.val + j.val) / 7 = i.val by omega,
    show (7 * i.val + j.val) % 7 = j.val by omega]
  split_ifs with h1 h2 h2 <;>
    first
      | exact Nat.cast_one
      | exact Nat.cast_zero
      | exact absurd (Fin.ext h1) h2
      | exact absurd (congrArg Fin.val h2) h1

end CFSG.Sporadic.LySchreier
