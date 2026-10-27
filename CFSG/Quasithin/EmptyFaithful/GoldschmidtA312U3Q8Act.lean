module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3Q8Sub
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3Quasi

public section

namespace CFSG.Quasithin.A312U3

open Matrix CFSG.Assembly.LowTwoRank CFSG.Quasithin.A38c15 CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial

variable {p : ℕ} {K : Type} [Field K] {M : Subgroup ↥(StatedSU 3 (p ^ 1) K)}
  {H : Subgroup (GL (Fin 3) K)}

theorem aut_eq_one_of_central_perfect' {H : Type*} [Group H] [hperf : Group.IsPerfect H]
    (α : MulAut H) (hα : ∀ h : H, h⁻¹ * α h ∈ Subgroup.center H) : α = 1 := by
  let φ : H →* Subgroup.center H :=
    { toFun := fun h => ⟨h⁻¹ * α h, hα h⟩
      map_one' := by ext; simp
      map_mul' := fun h k => by
        ext
        have hz : h⁻¹ * α h ∈ Subgroup.center H := hα h
        have := Subgroup.mem_center_iff.mp hz (k⁻¹)
        simp only [Subgroup.coe_mul, _root_.mul_inv_rev, map_mul]
        calc k⁻¹ * h⁻¹ * (α h * α k) = k⁻¹ * (h⁻¹ * α h) * α k := by group
          _ = (h⁻¹ * α h) * k⁻¹ * α k := by rw [this]
          _ = h⁻¹ * α h * (k⁻¹ * α k) := by group }
  have hker : φ.ker = ⊤ := by
    rw [eq_top_iff, ← hperf.commutator_eq_top]
    exact Abelianization.commutator_subset_ker φ
  ext h
  have : φ h = 1 := (MonoidHom.mem_ker.mp (by rw [hker]; trivial))
  have h2 : h⁻¹ * α h = 1 := congrArg Subtype.val this
  exact (inv_mul_eq_one.mp h2).symm

@[expose] noncomputable def qAct (h : QCtx p K M H) : ↥M →* MulAut (H ⧸ Subgroup.center H) :=
  (hessK_act h.norm).comp (M.equivMapOfInjective (StatedSU 3 (p ^ 1) K).subtype
    (StatedSU 3 (p ^ 1) K).subtype_injective).toMonoidHom

theorem qAct_apply_mk (h : QCtx p K M H) (g : ↥M) (x : H) :
    qAct h g (QuotientGroup.mk x) =
      QuotientGroup.mk (⟨((g : ↥(StatedSU 3 (p ^ 1) K)) : GL (Fin 3) K) * x *
        ((g : ↥(StatedSU 3 (p ^ 1) K)) : GL (Fin 3) K)⁻¹, h.norm _ ⟨g, g.2, rfl⟩ x x.2⟩ : H) :=
  rfl

theorem qAct_ker_comm (h : QCtx p K M H) {g : ↥M} (hg : qAct h g = 1) {x : GL (Fin 3) K}
    (hx : x ∈ H) : ((g : ↥(StatedSU 3 (p ^ 1) K)) : GL (Fin 3) K) * x =
      x * ((g : ↥(StatedSU 3 (p ^ 1) K)) : GL (Fin 3) K) := by
  have hperf : Group.IsPerfect ↥H := h.quasi.1
  set ĝ : ↥(M.map (StatedSU 3 (p ^ 1) K).subtype) := ⟨_, g, g.2, rfl⟩ with hĝ
  have hker : ĝ ∈ (hessK_act h.norm).ker := hg
  set α : MulAut ↥H := hessK_conj h.norm ĝ with hα
  have hα1 : α = 1 := by
    apply aut_eq_one_of_central_perfect'
    intro y
    rw [Subgroup.mem_center_iff]
    intro z
    apply Subtype.ext
    have := hessK_ker_commute h.norm hker (x := (y : GL (Fin 3) K)) (y := (z : GL (Fin 3) K))
      y.2 z.2
    simpa [hα, hessK_conj_apply, hĝ] using this
  have hx' := congrArg (fun a : MulAut ↥H => ((a ⟨x, hx⟩ : ↥H) : GL (Fin 3) K)) hα1
  simp only [hα, hessK_conj_apply, MulAut.one_apply] at hx'
  have : ((g : ↥(StatedSU 3 (p ^ 1) K)) : GL (Fin 3) K) * x *
      ((g : ↥(StatedSU 3 (p ^ 1) K)) : GL (Fin 3) K)⁻¹ = x := hx'
  rw [mul_inv_eq_iff_eq_mul] at this
  exact this

theorem qAct_ker_scalar (h : QCtx p K M H) {g : ↥M} (hg : qAct h g = 1) :
    ∃ c : K, (((g : ↥(StatedSU 3 (p ^ 1) K)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.scalar (Fin 3) c := by
  refine h.scalar _ fun x hx => ?_
  have := qAct_ker_comm h hg hx
  have h' := congrArg Units.val this
  simp only [Units.val_mul] at h'
  exact h'.symm

theorem qAct_ker_mem_center (h : QCtx p K M H) {g : ↥M} (hg : qAct h g = 1) :
    ((g : ↥(StatedSU 3 (p ^ 1) K)) : GL (Fin 3) K) ∈ Subgroup.center (GL (Fin 3) K) := by
  obtain ⟨c, hc⟩ := qAct_ker_scalar h hg
  exact Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr ⟨c, hc.symm⟩

variable [Fact p.Prime]

theorem qAct_ker_pow_three (hK : Nat.card K = p ^ 2) (h : QCtx p K M H) {g : ↥M}
    (hg : qAct h g = 1) : g ^ 3 = 1 := by
  obtain ⟨c, hc⟩ := qAct_ker_scalar h hg
  have hdet : (((g : ↥(StatedSU 3 (p ^ 1) K)) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K).det = 1 :=
    ((mem_unitarySU_iff (uniData hK)).mp (g : ↥(StatedSU 3 (p ^ 1) K)).2).1
  rw [hc, Matrix.det_fin_three] at hdet
  have hc3 : c ^ 3 = 1 := by
    simp [Matrix.scalar_apply, Matrix.diagonal] at hdet
    linear_combination hdet
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_pow, Subgroup.coe_pow, Units.val_pow_eq_pow_val, hc, ← map_pow, hc3]
  simp

theorem quatPair_qAct (hK : Nat.card K = p ^ 2) (h : QCtx p K M H) {c d : ↥M}
    (hcd : QuatPair c d) : QuatPair (qAct h c) (qAct h d) := by
  obtain ⟨h4, h2, hd, hconj⟩ := hcd
  refine ⟨by rw [← map_pow, h4, map_one], fun e => h2 ?_, ?_, ?_⟩
  · have e' : qAct h (c ^ 2) = 1 := by rw [map_pow, e]
    have h6 := qAct_ker_pow_three hK h e'
    have : c ^ 2 = c ^ 6 := by
      rw [show (6 : ℕ) = 4 + 2 from rfl, pow_add, h4, one_mul]
    rw [this, ← pow_mul] at *
    simpa using h6
  · rw [← map_pow, ← map_pow, hd]
  · rw [← map_mul, ← map_inv, ← map_mul, hconj, map_inv]

end CFSG.Quasithin.A312U3
