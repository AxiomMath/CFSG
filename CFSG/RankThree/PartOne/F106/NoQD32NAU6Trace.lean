module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.GL83LieDefs
public import CFSG.RankThree.PartOne.F106.U6Mono
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import Certificates.Data.U6NA

public section

namespace CFSG.RankThree.PartOne.F106

open Matrix CFSG.Assembly.LowTwoRank

section Generic

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] (H : Subgroup (GL ι K))

@[expose] def trZeroP (g : StatedProj H) : Prop :=
  ∃ A : H, QuotientGroup.mk A = g ∧ Matrix.trace (((A : GL ι K) : Matrix ι ι K)) = 0

theorem trZeroP_mk (A : H) :
    trZeroP H (QuotientGroup.mk A) ↔ Matrix.trace (((A : GL ι K) : Matrix ι ι K)) = 0 := by
  constructor
  · rintro ⟨A', hA', h0⟩
    have h1 := QuotientGroup.eq.1 hA'.symm
    rw [Subgroup.mem_subgroupOf] at h1
    obtain ⟨u, hu⟩ := h1
    have h2 : ((A' : GL ι K) : Matrix ι ι K) =
        ((A : GL ι K) : Matrix ι ι K) * Matrix.scalar ι (u : K) := by
      have : (A : GL ι K)⁻¹ * (A' : GL ι K) = Matrix.GeneralLinearGroup.scalar ι u := by
        simpa using hu.symm
      have h3 : (A' : GL ι K) = (A : GL ι K) * Matrix.GeneralLinearGroup.scalar ι u := by
        rw [← this, mul_inv_cancel_left]
      have := congrArg (fun g : GL ι K => (g : Matrix ι ι K)) h3
      simpa using this
    rw [h2, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, mul_one,
      Matrix.trace_smul, smul_eq_mul] at h0
    exact (mul_eq_zero.mp h0).resolve_left u.ne_zero
  · intro h
    exact ⟨A, rfl, h⟩

theorem trZeroP_conj (h g : StatedProj H) : trZeroP H (h * g * h⁻¹) ↔ trZeroP H g := by
  obtain ⟨B, rfl⟩ := QuotientGroup.mk_surjective h
  obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective g
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, trZeroP_mk,
    trZeroP_mk]
  have h1 : (((B * A * B⁻¹ : H) : GL ι K) : Matrix ι ι K) =
      ((B : GL ι K) : Matrix ι ι K) * ((A : GL ι K) : Matrix ι ι K) *
        (((B : GL ι K)⁻¹ : GL ι K) : Matrix ι ι K) := by
    simp
  rw [h1, Matrix.trace_units_conj]

end Generic

section Mono

variable {K : Type} [Field K] [CharP K 2] (c : Cube K)

@[expose] noncomputable def Cube.enc : ZMod 2 × ZMod 2 →+ K :=
  (ZMod.castHom (dvd_refl 2) K).toAddMonoidHom.comp (AddMonoidHom.fst _ _) +
    ((AddMonoidHom.mulRight c.ω).comp (ZMod.castHom (dvd_refl 2) K).toAddMonoidHom).comp
      (AddMonoidHom.snd _ _)

theorem Cube.enc_apply (x y : ZMod 2) :
    c.enc (x, y) = ZMod.castHom (dvd_refl 2) K x + ZMod.castHom (dvd_refl 2) K y * c.ω := rfl

theorem Cube.sq_eq : c.ω ^ 2 = c.ω + 1 := by
  have h1 : (c.ω - 1) * (c.ω ^ 2 + c.ω + 1) = 0 := by
    have := c.cube
    linear_combination this
  have h2 : c.ω - 1 ≠ 0 := sub_ne_zero.mpr c.ne_one
  have h3 : c.ω ^ 2 + c.ω + 1 = 0 := (mul_eq_zero.mp h1).resolve_left h2
  have h4 : c.ω ^ 2 = -(c.ω + 1) := by linear_combination h3
  rw [h4, CharTwo.neg_eq]

theorem Cube.enc_penc (a : ZMod 3) : c.enc (U6Mon.penc a) = c.p a := by
  have key : ∀ a : ZMod 3, a = 0 ∨ a = 1 ∨ a = 2 := by decide
  have e0 : (0 : ZMod 3).val = 0 := rfl
  have e1 : (1 : ZMod 3).val = 1 := rfl
  have e2 : (2 : ZMod 3).val = 2 := rfl
  rcases key a with rfl | rfl | rfl
  · simp only [U6Mon.penc, Cube.p, e0]
    simp [Cube.enc_apply]
  · simp only [U6Mon.penc, Cube.p, e1]
    simp [Cube.enc_apply]
  · simp only [U6Mon.penc, Cube.p, e2]
    simp [Cube.enc_apply, c.sq_eq, add_comm]

theorem Cube.enc_injective : Function.Injective c.enc := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨x, y⟩ h
  have hx : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rw [Cube.enc_apply] at h
  rcases hx x with rfl | rfl <;> rcases hx y with rfl | rfl
  · rfl
  · exfalso
    simp only [map_zero, map_one, zero_add, one_mul] at h
    exact c.ω_ne_zero h
  · exfalso
    simp only [map_zero, map_one, zero_mul, add_zero] at h
    exact one_ne_zero h
  · exfalso
    simp only [map_one, one_mul] at h
    apply c.ne_one
    have : c.ω = -1 := by linear_combination h
    rw [this, CharTwo.neg_eq]

theorem Cube.trace_mono (x : U6Mon) :
    Matrix.trace (c.mono x.d (u6Perm x.t)) = c.enc x.trSum := by
  have e : ∀ i, c.enc (if i = u6Perm x.t i then U6Mon.penc (x.d i) else 0) =
      if i = u6Perm x.t i then c.p (x.d i) else 0 := by
    intro i
    split_ifs with h
    · exact c.enc_penc _
    · exact map_zero _
  unfold U6Mon.trSum
  rw [map_sum]
  exact Finset.sum_congr rfl (fun i _ => (e i).symm)

variable (hK : Nat.card K = (2 ^ 1) ^ 2)

theorem trZeroP_mu {x : U6Mon} (hx : x.Ok) :
    trZeroP (StatedSU 6 (2 ^ 1) K) (c.mu hK x) ↔ x.trB = true := by
  rw [Cube.mu_of_ok c hK hx, trZeroP_mk]
  change Matrix.trace (c.mono x.d (u6Perm x.t)) = 0 ↔ _
  rw [Cube.trace_mono, U6Mon.trB, decide_eq_true_iff, ← map_zero c.enc]
  exact c.enc_injective.eq_iff

end Mono

end CFSG.RankThree.PartOne.F106
