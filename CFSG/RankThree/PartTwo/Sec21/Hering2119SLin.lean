module

public import CFSG.RankThree.PartTwo.Sec21.Hering2119SMat
import CFSG.RankThree.PartOne.K1214.Basic
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering2119S

open Module Matrix

section Transport

variable {W : Type*} [AddCommGroup W] [Module F3 W]

@[expose] noncomputable def eqvGL (b : Basis (Fin 2) F3 W) : (W ≃ₗ[F3] W) ≃* GL (Fin 2) F3 :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv F3 W).symm.trans
    (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv)

theorem eqvGL_coe (b : Basis (Fin 2) F3 W) (g : W ≃ₗ[F3] W) :
    ((eqvGL b g : GL (Fin 2) F3) : Matrix (Fin 2) (Fin 2) F3) =
      LinearMap.toMatrix b b (g : W →ₗ[F3] W) := by
  rfl

theorem sl_le_abs (hW : Module.finrank F3 W = 2) (B : Subgroup (W ≃ₗ[F3] W))
    (htrans : ∀ w w' : W, w ≠ 0 → w' ≠ 0 → ∃ b ∈ B, b w = w')
    (h3 : ∃ b ∈ B, b ≠ 1 ∧ b ^ 3 = 1) :
    ∀ g : W ≃ₗ[F3] W, LinearMap.det (g : W →ₗ[F3] W) = 1 → g ∈ B := by
  haveI : Module.Finite F3 W := Module.finite_of_finrank_pos (by omega)
  let b : Basis (Fin 2) F3 W := Module.finBasisOfFinrankEq F3 W hW
  let Θ := eqvGL b
  let Bm : Subgroup (GL (Fin 2) F3) := B.map Θ.toMonoidHom
  have key := sl_le_of_transitive Bm ?_ ?_
  · intro g hg
    have : Θ g ∈ Bm := key (Θ g) (by rw [eqvGL_coe, LinearMap.det_toMatrix]; exact hg)
    obtain ⟨g', hg', e⟩ := this
    have : g' = g := Θ.injective e
    rwa [← this]
  · intro v w hv hw
    have hx : b.equivFun.symm v ≠ 0 := fun h => hv ((LinearEquiv.map_eq_zero_iff _).mp h)
    have hy : b.equivFun.symm w ≠ 0 := fun h => hw ((LinearEquiv.map_eq_zero_iff _).mp h)
    obtain ⟨g, hgB, hgx⟩ := htrans _ _ hx hy
    refine ⟨Θ g, ⟨g, hgB, rfl⟩, ?_⟩
    rw [eqvGL_coe]
    have h := LinearMap.toMatrix_mulVec_repr b b (g : W →ₗ[F3] W) (b.equivFun.symm v)
    have e1 : ⇑(b.repr (b.equivFun.symm v)) = v := b.equivFun.apply_symm_apply v
    have e2 : ⇑(b.repr ((g : W →ₗ[F3] W) (b.equivFun.symm v))) = w := by
      change ⇑(b.repr (g (b.equivFun.symm v))) = w
      rw [hgx]
      exact b.equivFun.apply_symm_apply w
    rw [e1, e2] at h
    exact h
  · obtain ⟨b0, hb0B, hb01, hb03⟩ := h3
    refine ⟨Θ b0, ⟨b0, hb0B, rfl⟩, fun h => hb01 (Θ.injective (by rw [h, map_one])), ?_⟩
    rw [← map_pow, hb03, map_one]

theorem nonscalar_of_singular_abs (hW : Module.finrank F3 W = 2) (ν : W →ₗ[F3] W)
    (hν : ν ≠ 0) (hdet : LinearMap.det ν = 0) : ∀ c : F3, ν ≠ c • (LinearMap.id : W →ₗ[F3] W) := by
  intro c hc
  apply hν
  have hd : LinearMap.det ν = c ^ 2 := by
    rw [hc, LinearMap.det_smul, hW, LinearMap.det_id, mul_one]
  have hc0 : c = 0 := pow_eq_zero_iff (by norm_num) |>.mp (hd ▸ hdet)
  rw [hc, hc0, zero_smul]

theorem eq_top_abs' (hW : Module.finrank F3 W = 2) (B : Subgroup (W ≃ₗ[F3] W))
    (hB : ∀ g : W ≃ₗ[F3] W, LinearMap.det (g : W →ₗ[F3] W) = 1 → g ∈ B)
    (S : AddSubgroup (W →ₗ[F3] W))
    (hconj : ∀ g ∈ B, ∀ ν ∈ S, (g : W →ₗ[F3] W) ∘ₗ ν ∘ₗ (g.symm : W →ₗ[F3] W) ∈ S)
    (h1 : (LinearMap.id : W →ₗ[F3] W) ∈ S) (ν : W →ₗ[F3] W)
    (hν : ∀ c : F3, ν ≠ c • (LinearMap.id : W →ₗ[F3] W)) (hνS : ν ∈ S) : S = ⊤ := by
  haveI : Module.Finite F3 W := Module.finite_of_finrank_pos (by omega)
  let b : Basis (Fin 2) F3 W := Module.finBasisOfFinrankEq F3 W hW
  let Θ := eqvGL b
  let toM := LinearMap.toMatrixAlgEquiv b
  let Sm : AddSubgroup Mat2 := S.comap toM.symm.toAddEquiv.toAddMonoidHom
  have hmem : ∀ μ, μ ∈ Sm ↔ toM.symm μ ∈ S := fun μ => Iff.rfl
  have key := eq_top_of_conj_nonscalar Sm ?_ ?_ (toM ν) ?_ ?_
  · rw [eq_top_iff]
    intro ν' _
    have : toM ν' ∈ Sm := by rw [key]; trivial
    rw [hmem] at this
    simpa using this
  · intro g hg μ hμ
    have hg0 : g.det ≠ 0 := by rw [hg]; exact one_ne_zero
    let ĝ : GL (Fin 2) F3 := Matrix.GeneralLinearGroup.mkOfDetNeZero g hg0
    let G : W ≃ₗ[F3] W := Θ.symm ĝ
    have hGg : toM (G : W →ₗ[F3] W) = g := by
      have := eqvGL_coe b G
      rw [show eqvGL b G = ĝ from Θ.apply_symm_apply ĝ] at this
      exact this.symm
    have hGdet : LinearMap.det (G : W →ₗ[F3] W) = 1 := by
      rw [← LinearMap.det_toMatrix b, ← hg]
      exact congrArg Matrix.det hGg
    have hGB := hB G hGdet
    have hGinv : toM (G.symm : W →ₗ[F3] W) = g.adjugate := by
      have h2 : toM (G.symm : W →ₗ[F3] W) * g = 1 := by
        rw [← hGg, ← map_mul]
        have : (G.symm : W →ₗ[F3] W) * (G : W →ₗ[F3] W) = 1 := by
          ext x; simp
        rw [this, map_one]
      have h3 : g * g.adjugate = 1 := by rw [Matrix.mul_adjugate, hg, one_smul]
      calc toM (G.symm : W →ₗ[F3] W) = toM (G.symm : W →ₗ[F3] W) * (g * g.adjugate) := by
            rw [h3, mul_one]
        _ = (toM (G.symm : W →ₗ[F3] W) * g) * g.adjugate := by rw [mul_assoc]
        _ = g.adjugate := by rw [h2, one_mul]
    have hμ' := (hmem μ).mp hμ
    have hconj' := hconj G hGB _ hμ'
    have e : toM ((G : W →ₗ[F3] W) ∘ₗ toM.symm μ ∘ₗ (G.symm : W →ₗ[F3] W)) =
        g * μ * g.adjugate := by
      have : (G : W →ₗ[F3] W) ∘ₗ toM.symm μ ∘ₗ (G.symm : W →ₗ[F3] W) =
          (G : W →ₗ[F3] W) * toM.symm μ * (G.symm : W →ₗ[F3] W) :=
        LinearMap.ext fun x => by simp only [LinearMap.comp_apply, Module.End.mul_apply]
      rw [this, map_mul, map_mul, hGg, hGinv, AlgEquiv.apply_symm_apply]
    rw [hmem]
    have h' : toM.symm (g * μ * g.adjugate) =
        (G : W →ₗ[F3] W) ∘ₗ toM.symm μ ∘ₗ (G.symm : W →ₗ[F3] W) := by
      apply toM.injective
      rw [AlgEquiv.apply_symm_apply, e]
    rw [h']
    exact hconj'
  · rw [hmem]
    have : toM.symm (1 : Mat2) = LinearMap.id := by rw [map_one]; rfl
    rw [this]; exact h1
  · intro c h
    apply hν c
    have e1 : toM (LinearMap.id : W →ₗ[F3] W) = 1 := map_one toM
    exact toM.injective (by rw [h, map_smul, e1])
  · rw [hmem, AlgEquiv.symm_apply_apply]
    exact hνS

end Transport
section Build

variable {V : Type*} [AddCommGroup V] [Module F3 V]

@[expose] def uMap (ε : V →ₗ[F3] V) (ν : LinearMap.range ε →ₗ[F3] LinearMap.range ε) : V →ₗ[F3] V :=
  LinearMap.id + (LinearMap.range ε).subtype ∘ₗ ν ∘ₗ ε.rangeRestrict

theorem uMap_apply (ε : V →ₗ[F3] V) (ν : LinearMap.range ε →ₗ[F3] LinearMap.range ε) (v : V) :
    uMap ε ν v = v + (ν (ε.rangeRestrict v) : V) := rfl

theorem uMap_mul (ε : V →ₗ[F3] V) (hε : ∀ v, ε (ε v) = 0)
    (ν ν' : LinearMap.range ε →ₗ[F3] LinearMap.range ε) (v : V) :
    uMap ε ν (uMap ε ν' v) = uMap ε (ν + ν') v := by
  have key : ∀ w : LinearMap.range ε, ε.rangeRestrict (w : V) = 0 := by
    rintro ⟨_, v, rfl⟩
    exact Subtype.ext (hε v)
  rw [uMap_apply, uMap_apply, uMap_apply, map_add, key, add_zero, LinearMap.add_apply,
    Submodule.coe_add]
  abel

theorem uMap_zero (ε : V →ₗ[F3] V) (v : V) : uMap ε 0 v = v := by
  simp [uMap_apply]

@[expose] def uEquiv (ε : V →ₗ[F3] V) (hε : ∀ v, ε (ε v) = 0)
    (ν : LinearMap.range ε →ₗ[F3] LinearMap.range ε) : V ≃ₗ[F3] V :=
  LinearEquiv.ofLinear (uMap ε ν) (uMap ε (-ν))
    (LinearMap.ext fun v => by
      rw [LinearMap.comp_apply, uMap_mul ε hε, add_neg_cancel, uMap_zero]; rfl)
    (LinearMap.ext fun v => by
      rw [LinearMap.comp_apply, uMap_mul ε hε, neg_add_cancel, uMap_zero]; rfl)

theorem uEquiv_apply (ε : V →ₗ[F3] V) (hε : ∀ v, ε (ε v) = 0)
    (ν : LinearMap.range ε →ₗ[F3] LinearMap.range ε) (v : V) :
    uEquiv ε hε ν v = v + (ν (ε.rangeRestrict v) : V) := rfl

theorem uEquiv_mul (ε : V →ₗ[F3] V) (hε : ∀ v, ε (ε v) = 0)
    (ν ν' : LinearMap.range ε →ₗ[F3] LinearMap.range ε) :
    uEquiv ε hε ν * uEquiv ε hε ν' = uEquiv ε hε (ν + ν') := by
  ext v
  exact uMap_mul ε hε ν ν' v

@[expose] def hres (ε : V →ₗ[F3] V) (h : V →ₗ[F3] V) (hc : ∀ v, h (ε v) = ε (h v)) :
    LinearMap.range ε →ₗ[F3] LinearMap.range ε :=
  h.restrict (p := LinearMap.range ε) (q := LinearMap.range ε) (fun w hw => by
    obtain ⟨v, rfl⟩ := hw
    exact ⟨h v, (hc v).symm⟩)

theorem hres_apply (ε : V →ₗ[F3] V) (h : V →ₗ[F3] V) (hc : ∀ v, h (ε v) = ε (h v))
    (w : LinearMap.range ε) : ((hres ε h hc w : LinearMap.range ε) : V) = h w := rfl

theorem symm_comm (ε : V →ₗ[F3] V) (h : V ≃ₗ[F3] V) (hc : ∀ v, h (ε v) = ε (h v)) (v : V) :
    h.symm (ε v) = ε (h.symm v) := by
  apply h.injective
  rw [LinearEquiv.apply_symm_apply, hc, LinearEquiv.apply_symm_apply]

theorem conj_uEquiv_apply (ε : V →ₗ[F3] V) (hε : ∀ v, ε (ε v) = 0) (h : V ≃ₗ[F3] V)
    (hc : ∀ v, h (ε v) = ε (h v))
    (ν : LinearMap.range ε →ₗ[F3] LinearMap.range ε) (v : V) :
    h (uEquiv ε hε ν (h.symm v)) = uEquiv ε hε
      (hres ε h hc ∘ₗ ν ∘ₗ hres ε h.symm (symm_comm ε h hc)) v := by
  rw [uEquiv_apply, uEquiv_apply, map_add, LinearEquiv.apply_symm_apply]
  congr 1
  have e1 : hres ε h.symm (symm_comm ε h hc) (ε.rangeRestrict v) = ε.rangeRestrict (h.symm v) := by
    apply Subtype.ext
    rw [hres_apply]
    exact symm_comm ε h hc v
  rw [LinearMap.comp_apply, LinearMap.comp_apply, e1, hres_apply]
  rfl

@[expose] def uHom (ε : V →ₗ[F3] V) (hε : ∀ v, ε (ε v) = 0) :
    Multiplicative (LinearMap.range ε →ₗ[F3] LinearMap.range ε) →* (V ≃ₗ[F3] V) where
  toFun ν := uEquiv ε hε ν.toAdd
  map_one' := by ext v; exact uMap_zero ε v
  map_mul' ν ν' := (uEquiv_mul ε hε ν.toAdd ν'.toAdd).symm

theorem uHom_injective (ε : V →ₗ[F3] V) (hε : ∀ v, ε (ε v) = 0) :
    Function.Injective (uHom ε hε) := by
  intro ν ν' h
  apply Multiplicative.toAdd.injective
  apply LinearMap.ext
  intro w
  obtain ⟨v, rfl⟩ : ∃ v, ε.rangeRestrict v = w := by
    obtain ⟨v, hv⟩ := w.2
    exact ⟨v, Subtype.ext hv⟩
  have := congrArg (fun f : V ≃ₗ[F3] V => (f v - v)) h
  simp only [uHom, MonoidHom.coe_mk, OneHom.coe_mk, uEquiv_apply, add_sub_cancel_left] at this
  exact Subtype.ext this

@[expose] def hresEquiv (ε : V →ₗ[F3] V) (h : V ≃ₗ[F3] V) (hc : ∀ v, h (ε v) = ε (h v)) :
    LinearMap.range ε ≃ₗ[F3] LinearMap.range ε :=
  LinearEquiv.ofLinear (hres ε h hc) (hres ε h.symm (symm_comm ε h hc))
    (LinearMap.ext fun w => Subtype.ext (by
      simp only [LinearMap.comp_apply, hres_apply, LinearMap.id_apply]
      exact h.apply_symm_apply _))
    (LinearMap.ext fun w => Subtype.ext (by
      simp only [LinearMap.comp_apply, hres_apply, LinearMap.id_apply]
      exact h.symm_apply_apply _))

theorem hresEquiv_apply (ε : V →ₗ[F3] V) (h : V ≃ₗ[F3] V) (hc : ∀ v, h (ε v) = ε (h v))
    (w : LinearMap.range ε) : ((hresEquiv ε h hc w : LinearMap.range ε) : V) = h w := rfl

def resSubgroup (ε : V →ₗ[F3] V) (H : Subgroup (V ≃ₗ[F3] V)) :
    Subgroup (LinearMap.range ε ≃ₗ[F3] LinearMap.range ε) where
  carrier := {g | ∃ h ∈ H, ∀ w : LinearMap.range ε, ((g w : LinearMap.range ε) : V) = h w}
  mul_mem' := by
    rintro g₁ g₂ ⟨h₁, hh₁, e₁⟩ ⟨h₂, hh₂, e₂⟩
    refine ⟨h₁ * h₂, H.mul_mem hh₁ hh₂, fun w => ?_⟩
    show ((g₁ (g₂ w) : LinearMap.range ε) : V) = h₁ (h₂ w)
    rw [e₁, e₂]
  one_mem' := ⟨1, H.one_mem, fun w => rfl⟩
  inv_mem' := by
    rintro g ⟨h, hh, e⟩
    refine ⟨h⁻¹, H.inv_mem hh, fun w => ?_⟩
    have : h ((g⁻¹ w : LinearMap.range ε) : V) = w := by
      rw [← e]
      exact congrArg Subtype.val (g.apply_symm_apply w)
    change ((g.symm w : LinearMap.range ε) : V) = h.symm w
    rw [← this]
    simp

theorem exists_factor (ε : V →ₗ[F3] V) (T : V →ₗ[F3] V) (hT : ∀ v, T v ∈ LinearMap.range ε)
    (hker : ∀ v, ε v = 0 → T v = 0) :
    ∃ ν : LinearMap.range ε →ₗ[F3] LinearMap.range ε,
      ∀ v, (ν (ε.rangeRestrict v) : V) = T v := by
  obtain ⟨σ, hσ⟩ := LinearMap.exists_rightInverse_of_surjective ε.rangeRestrict
    (LinearMap.range_rangeRestrict ε)
  refine ⟨(T ∘ₗ σ).codRestrict (LinearMap.range ε) (fun w => hT _), fun v => ?_⟩
  have h1 : ε.rangeRestrict (σ (ε.rangeRestrict v)) = ε.rangeRestrict v :=
    congrArg (fun f => f (ε.rangeRestrict v)) hσ
  have h2 : ε (σ (ε.rangeRestrict v) - v) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact congrArg Subtype.val h1
  have h3 := hker _ h2
  rw [map_sub, sub_eq_zero] at h3
  simpa using h3

end Build

section Helpers

variable {V : Type*} [AddCommGroup V] [Module F3 V]

theorem rr_surj (ε : V →ₗ[F3] V) (w : LinearMap.range ε) : ∃ v, ε.rangeRestrict v = w := by
  obtain ⟨v, hv⟩ := w.2
  exact ⟨v, Subtype.ext hv⟩

theorem conj_u_exists (ε : V →ₗ[F3] V) (hε : ∀ v, ε (ε v) = 0) (h : V ≃ₗ[F3] V)
    (hc : ∀ v, h (ε v) = ε (h v)) (ν : LinearMap.range ε →ₗ[F3] LinearMap.range ε) :
    h * uEquiv ε hε ν * h⁻¹ = uEquiv ε hε
      (hres ε h hc ∘ₗ ν ∘ₗ hres ε h.symm (symm_comm ε h hc)) := by
  ext v
  exact conj_uEquiv_apply ε hε h hc ν v

theorem u_triv (ε : V →ₗ[F3] V) (hε : ∀ v, ε (ε v) = 0)
    (ν : LinearMap.range ε →ₗ[F3] LinearMap.range ε) (w : V) (hw : w ∈ LinearMap.range ε) :
    uEquiv ε hε ν w = w := by
  obtain ⟨v, rfl⟩ := hw
  rw [uEquiv_apply]
  have : ε.rangeRestrict (ε v) = 0 := Subtype.ext (hε v)
  rw [this, map_zero]
  simp

end Helpers

section Core

variable {V : Type*} [AddCommGroup V] [Module F3 V] [Finite V]

theorem finrank_range_eq_two (ε : V →ₗ[F3] V) (hW : Nat.card (LinearMap.range ε) = 9) :
    Module.finrank F3 (LinearMap.range ε) = 2 := by
  have h := Module.natCard_eq_pow_finrank (K := F3) (V := LinearMap.range ε)
  rw [hW, Nat.card_zmod] at h
  have h' : (3 : ℕ) ^ 2 = 3 ^ Module.finrank F3 (LinearMap.range ε) := by rw [← h]; norm_num
  exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) h').symm

theorem na_core' (ε : V →ₗ[F3] V) (hε : ∀ v, ε (ε v) = 0)
    (hW : Nat.card (LinearMap.range ε) = 9)
    (hkerW : ∀ v, ε v = 0 → v ∈ LinearMap.range ε)
    (H : Subgroup (V ≃ₗ[F3] V))
    (hcomm : ∀ h ∈ H, ∀ v, h (ε v) = ε (h v))
    (u₁ : V ≃ₗ[F3] V) (hu₁ : ∀ v, u₁ v = v + ε v) (hu₁H : u₁ ∈ H)
    (htrans : ∀ w w' : V, w ∈ LinearMap.range ε → w' ∈ LinearMap.range ε → w ≠ 0 → w' ≠ 0 →
      ∃ h ∈ H, h w = w')
    (hord3 : ∃ s ∈ H, s ^ 3 = 1 ∧ ∃ w ∈ LinearMap.range ε, s w ≠ w)
    (ν₁ : LinearMap.range ε →ₗ[F3] LinearMap.range ε) (hν₁S : uEquiv ε hε ν₁ ∈ H)
    (hν₁ : ∀ c : F3, ν₁ ≠ c • (LinearMap.id : LinearMap.range ε →ₗ[F3] LinearMap.range ε)) :
    ∃ X : Subgroup (V ≃ₗ[F3] V), X ≤ H ∧ IsPGroup 3 X ∧ 243 ≤ Nat.card X ∧ u₁ ∈ X ∧
      ∀ x ∈ X, x * u₁ = u₁ * x := by
  classical
  have hWf := finrank_range_eq_two ε hW
  set B := resSubgroup ε H with hBdef
  have htransW : ∀ w w' : LinearMap.range ε, w ≠ 0 → w' ≠ 0 → ∃ b ∈ B, b w = w' := by
    intro w w' hw hw'
    obtain ⟨h, hh, hhw⟩ := htrans w w' w.2 w'.2 (fun h => hw (Subtype.ext h))
      (fun h => hw' (Subtype.ext h))
    exact ⟨hresEquiv ε h (hcomm h hh), ⟨h, hh, fun _ => rfl⟩, Subtype.ext hhw⟩
  have h3W : ∃ b ∈ B, b ≠ 1 ∧ b ^ 3 = 1 := by
    obtain ⟨s, hs, hs3, w₀, hw₀, hsw₀⟩ := hord3
    refine ⟨hresEquiv ε s (hcomm s hs), ⟨s, hs, fun _ => rfl⟩, ?_, ?_⟩
    · intro h1
      apply hsw₀
      have := congrArg (fun b : LinearMap.range ε ≃ₗ[F3] LinearMap.range ε =>
        ((b ⟨w₀, hw₀⟩ : LinearMap.range ε) : V)) h1
      simpa [hresEquiv_apply] using this
    · have key : ∀ (n : ℕ) (w : LinearMap.range ε),
          ((((hresEquiv ε s (hcomm s hs)) ^ n) w : LinearMap.range ε) : V) = (s ^ n) (w : V) := by
        intro n
        induction n with
        | zero => intro w; rfl
        | succ n ih =>
          intro w
          rw [pow_succ, pow_succ, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
            ih (hresEquiv ε s (hcomm s hs) w), hresEquiv_apply]
      ext w
      rw [key 3 w, hs3]
      rfl
  have hB := sl_le_abs hWf B htransW h3W
  let S : AddSubgroup (LinearMap.range ε →ₗ[F3] LinearMap.range ε) :=
    { carrier := {ν | uEquiv ε hε ν ∈ H}
      zero_mem' := by
        have : uEquiv ε hε 0 = 1 := by ext v; exact uMap_zero ε v
        show uEquiv ε hε 0 ∈ H
        rw [this]; exact H.one_mem
      add_mem' := by
        intro ν ν' hν hν'
        show uEquiv ε hε (ν + ν') ∈ H
        rw [← uEquiv_mul]
        exact H.mul_mem hν hν'
      neg_mem' := by
        intro ν hν
        show uEquiv ε hε (-ν) ∈ H
        have : uEquiv ε hε (-ν) = (uEquiv ε hε ν)⁻¹ := by
          apply eq_inv_of_mul_eq_one_right
          rw [uEquiv_mul, add_neg_cancel]
          ext v; exact uMap_zero ε v
        rw [this]; exact H.inv_mem hν }
  have hSmem : ∀ ν, ν ∈ S ↔ uEquiv ε hε ν ∈ H := fun ν => Iff.rfl
  have hconj : ∀ g ∈ B, ∀ ν ∈ S, (g : LinearMap.range ε →ₗ[F3] LinearMap.range ε) ∘ₗ ν ∘ₗ
      (g.symm : LinearMap.range ε →ₗ[F3] LinearMap.range ε) ∈ S := by
    rintro g ⟨h, hh, e⟩ ν hν
    have hc := hcomm h hh
    have e1 : (g : LinearMap.range ε →ₗ[F3] LinearMap.range ε) = hres ε h hc :=
      LinearMap.ext fun w => Subtype.ext (e w)
    have e2 : (g.symm : LinearMap.range ε →ₗ[F3] LinearMap.range ε) =
        hres ε h.symm (symm_comm ε h hc) := by
      apply LinearMap.ext
      intro w
      apply Subtype.ext
      have := e (g.symm w)
      rw [LinearEquiv.apply_symm_apply] at this
      change ((g.symm w : LinearMap.range ε) : V) = h.symm (w : V)
      rw [this]
      simp
    rw [e1, e2, hSmem]
    have : uEquiv ε hε (hres ε h hc ∘ₗ ν ∘ₗ hres ε h.symm (symm_comm ε h hc)) =
        h * uEquiv ε hε ν * h⁻¹ := by
      ext v
      exact (conj_uEquiv_apply ε hε h hc ν v).symm
    rw [this]
    exact H.mul_mem (H.mul_mem hh hν) (H.inv_mem hh)
  have h1S : (LinearMap.id : LinearMap.range ε →ₗ[F3] LinearMap.range ε) ∈ S := by
    have : uEquiv ε hε LinearMap.id = u₁ := by
      ext v
      rw [uEquiv_apply, hu₁]
      rfl
    rw [hSmem, this]
    exact hu₁H
  have hStop : S = ⊤ := eq_top_abs' hWf B hB S hconj h1S ν₁ hν₁ hν₁S
  have hu₁eq : uEquiv ε hε LinearMap.id = u₁ := by
    ext v
    rw [uEquiv_apply, hu₁]
    rfl
  have hΛH : (uHom ε hε).range ≤ H := by
    rintro _ ⟨ν, rfl⟩
    have : ν.toAdd ∈ S := by rw [hStop]; trivial
    exact this
  have hΛcard : Nat.card (uHom ε hε).range = 81 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective (uHom_injective ε hε)).toEquiv]
    rw [Nat.card_congr Multiplicative.toAdd, Module.natCard_eq_pow_finrank (K := F3),
      Nat.card_zmod, Module.finrank_linearMap, hWf]
    norm_num
  have hΛp : IsPGroup 3 (uHom ε hε).range := IsPGroup.of_card (n := 4) (by rw [hΛcard]; norm_num)
  obtain ⟨s, hsH, hs3, w₀, hw₀, hsw₀⟩ := hord3
  have hsc := hcomm s hsH
  have hs1 : s ≠ 1 := fun h => hsw₀ (by rw [h]; rfl)
  have hsN : Subgroup.zpowers s ≤ Subgroup.normalizer ((uHom ε hε).range : Set (V ≃ₗ[F3] V)) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · rintro ⟨ν, rfl⟩
      exact ⟨Multiplicative.ofAdd (hres ε s hsc ∘ₗ ν.toAdd ∘ₗ hres ε s.symm (symm_comm ε s hsc)),
        (conj_u_exists ε hε s hsc ν.toAdd).symm⟩
    · rintro ⟨ν, hν⟩
      have hsc' : ∀ v, s.symm (ε v) = ε (s.symm v) := fun v => symm_comm ε s hsc v
      have h := conj_u_exists ε hε s.symm hsc' ν.toAdd
      refine ⟨Multiplicative.ofAdd (hres ε s.symm hsc' ∘ₗ ν.toAdd ∘ₗ
        hres ε s.symm.symm (symm_comm ε s.symm hsc')), ?_⟩
      change uEquiv ε hε (Multiplicative.toAdd (Multiplicative.ofAdd _)) = g
      rw [toAdd_ofAdd, ← h]
      have e1 : (s.symm : V ≃ₗ[F3] V) = s⁻¹ := rfl
      rw [e1]
      change s⁻¹ * (uHom ε hε ν) * s⁻¹⁻¹ = g
      rw [hν]
      group
  have hsorder : orderOf s = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime hs3 hs1
  have hzcard : Nat.card (Subgroup.zpowers s) = 3 := by rw [Nat.card_zpowers, hsorder]
  have hzp : IsPGroup 3 (Subgroup.zpowers s) :=
    IsPGroup.of_card (n := 1) (by rw [hzcard]; norm_num)
  have hinf : (uHom ε hε).range ⊓ Subgroup.zpowers s = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxΛ, hxz⟩
    rw [Subgroup.mem_bot]
    obtain ⟨ν, rfl⟩ := hxΛ
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxz
    have hk' : (s ^ k) w₀ = w₀ := by
      rw [hk]
      exact u_triv ε hε ν.toAdd w₀ hw₀
    have hmod : s ^ (k % 3) = s ^ k := by
      have := zpow_mod_orderOf s k
      rwa [hsorder] at this
    have hr : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hr with hr | hr | hr
    · rw [← hk, ← hmod, hr, zpow_zero]
    · exfalso
      rw [← hmod, hr, zpow_one] at hk'
      exact hsw₀ hk'
    · exfalso
      rw [← hmod, hr] at hk'
      apply hsw₀
      have h2 : (s ^ (2 : ℤ)) w₀ = s (s w₀) := by
        rw [zpow_two, LinearEquiv.mul_apply]
      have h3 : (s ^ 3) w₀ = s (s (s w₀)) := by
        rw [pow_succ, pow_succ, pow_one, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
      rw [h2] at hk'
      have := h3
      rw [hs3, hk'] at this
      simpa using this.symm
  have hXcard : Nat.card ((uHom ε hε).range ⊔ Subgroup.zpowers s : Subgroup (V ≃ₗ[F3] V)) =
      243 := by
    have h := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hsN
    rw [hinf, Subgroup.card_bot, hΛcard, hzcard] at h
    omega
  have hXp : IsPGroup 3 ((uHom ε hε).range ⊔ Subgroup.zpowers s : Subgroup (V ≃ₗ[F3] V)) :=
    IsPGroup.to_sup_of_normal_left' hΛp hzp hsN
  have hu₁Λ : u₁ ∈ (uHom ε hε).range := ⟨Multiplicative.ofAdd LinearMap.id, hu₁eq⟩
  refine ⟨(uHom ε hε).range ⊔ Subgroup.zpowers s, sup_le hΛH (Subgroup.zpowers_le.mpr hsH),
    hXp, by rw [hXcard], Subgroup.mem_sup_left hu₁Λ, ?_⟩
  intro x hx
  have hcent : (uHom ε hε).range ⊔ Subgroup.zpowers s ≤ Subgroup.centralizer {u₁} := by
    refine sup_le ?_ ?_
    · rintro _ ⟨ν, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← hu₁eq]
      change uEquiv ε hε ν.toAdd * uEquiv ε hε LinearMap.id =
        uEquiv ε hε LinearMap.id * uEquiv ε hε ν.toAdd
      rw [uEquiv_mul, uEquiv_mul, add_comm]
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      have h := conj_u_exists ε hε s hsc LinearMap.id
      have h2 : hres ε s hsc ∘ₗ (LinearMap.id : LinearMap.range ε →ₗ[F3] LinearMap.range ε) ∘ₗ
          hres ε s.symm (symm_comm ε s hsc) = LinearMap.id := by
        apply LinearMap.ext
        intro w
        apply Subtype.ext
        simp only [LinearMap.comp_apply, hres_apply, LinearMap.id_apply]
        exact s.apply_symm_apply _
      rw [h2, hu₁eq] at h
      calc s * u₁ = (s * u₁ * s⁻¹) * s := by group
        _ = u₁ * s := by rw [h]
  exact Subgroup.mem_centralizer_singleton_iff.mp (hcent hx)

theorem na_core (ε : V →ₗ[F3] V) (hε : ∀ v, ε (ε v) = 0)
    (hW : Nat.card (LinearMap.range ε) = 9)
    (hkerW : ∀ v, ε v = 0 → v ∈ LinearMap.range ε)
    (H : Subgroup (V ≃ₗ[F3] V))
    (hcomm : ∀ h ∈ H, ∀ v, h (ε v) = ε (h v))
    (u₁ : V ≃ₗ[F3] V) (hu₁ : ∀ v, u₁ v = v + ε v) (hu₁H : u₁ ∈ H)
    (htrans : ∀ w w' : V, w ∈ LinearMap.range ε → w' ∈ LinearMap.range ε → w ≠ 0 → w' ≠ 0 →
      ∃ h ∈ H, h w = w')
    (hord3 : ∃ s ∈ H, s ^ 3 = 1 ∧ ∃ w ∈ LinearMap.range ε, s w ≠ w)
    (τ : V ≃ₗ[F3] V) (hτH : τ ∈ H) (d : V) (hd : d ∈ LinearMap.range ε) (hd0 : d ≠ 0)
    (hτ : ∀ v, τ v - v ∈ Submodule.span F3 {d}) (hτ1 : τ ≠ 1) :
    ∃ X : Subgroup (V ≃ₗ[F3] V), X ≤ H ∧ IsPGroup 3 X ∧ 243 ≤ Nat.card X ∧ u₁ ∈ X ∧
      ∀ x ∈ X, x * u₁ = u₁ * x := by
  classical
  have hWf := finrank_range_eq_two ε hW
  have hεd : ∀ x ∈ Submodule.span F3 {d}, ε x = 0 := by
    intro x hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨v, rfl⟩ := hd
    rw [map_smul, hε, smul_zero]
  obtain ⟨ν₀, hν₀⟩ := exists_factor ε ((τ : V →ₗ[F3] V) - LinearMap.id)
    (fun v => (Submodule.span_singleton_le_iff_mem d _).mpr hd (hτ v))
    (fun v hv => by
      obtain ⟨v', rfl⟩ := hkerW v hv
      have h1 : τ (ε v') = ε (τ v') := hcomm τ hτH v'
      have h2 : ε (τ v' - v') = 0 := hεd _ (hτ v')
      rw [map_sub] at h2
      simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply]
      rw [h1, sub_eq_zero.mp h2, sub_self])
  have hν₀S : uEquiv ε hε ν₀ ∈ H := by
    have : uEquiv ε hε ν₀ = τ := by
      ext v
      rw [uEquiv_apply, hν₀]
      simp
    rw [this]
    exact hτH
  have hν₀ne : ν₀ ≠ 0 := by
    intro h0
    apply hτ1
    ext v
    have := hν₀ v
    rw [h0] at this
    simp only [LinearMap.zero_apply, Submodule.coe_zero, LinearMap.sub_apply, LinearEquiv.coe_coe,
      LinearMap.id_apply] at this
    simpa [sub_eq_zero] using this.symm
  have hν₀det : LinearMap.det ν₀ = 0 := by
    rw [LinearMap.det_eq_zero_iff_ker_ne_bot]
    intro hker
    have hrn := LinearMap.finrank_range_add_finrank_ker ν₀
    rw [hker, finrank_bot, add_zero, hWf] at hrn
    have hd' : (⟨d, hd⟩ : LinearMap.range ε) ≠ 0 := fun h => hd0 (congrArg Subtype.val h)
    have hle : LinearMap.range ν₀ ≤ Submodule.span F3 {(⟨d, hd⟩ : LinearMap.range ε)} := by
      rintro _ ⟨w, rfl⟩
      obtain ⟨v, rfl⟩ := rr_surj ε w
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hτ v)
      rw [Submodule.mem_span_singleton]
      refine ⟨c, Subtype.ext ?_⟩
      have h1 := hν₀ v
      simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply] at h1
      rw [h1, ← hc]
      rfl
    have h2 := Submodule.finrank_mono hle
    have h3 := finrank_span_singleton (K := F3) hd'
    omega
  exact na_core' ε hε hW hkerW H hcomm u₁ hu₁ hu₁H htrans hord3 ν₀ hν₀S
    (nonscalar_of_singular_abs hWf ν₀ hν₀ne hν₀det)

end Core

end CFSG.RankThree.PartTwo.Sec21.Hering2119S
