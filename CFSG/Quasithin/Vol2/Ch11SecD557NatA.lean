module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.G2SL3
public import CFSG.Quasithin.H13.Statements

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open CFSG.Assembly.LowTwoRank (StatedSL)
open CFSG.Quasithin.SL3Model
open scoped MatrixGroups

noncomputable def statedSLEquiv' (n : ℕ) (K : Type) [Field K] : ↥(StatedSL n K) ≃* SL(n, K) :=
  (MulEquiv.subgroupCongr (CFSG.Assembly.LowTwoRank.statedSL_eq_range_toGL n K)).trans
    (MonoidHom.ofInjective Matrix.SpecialLinearGroup.toGL_injective).symm

theorem coe_statedSLEquiv' {n : ℕ} {K : Type} [Field K] (s : ↥(StatedSL n K)) :
    ((statedSLEquiv' n K s : SL(n, K)) : Matrix (Fin n) (Fin n) K) =
      ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  have h := MonoidHom.apply_ofInjective_symm Matrix.SpecialLinearGroup.toGL_injective
    ⟨(s : GL (Fin n) K), (CFSG.Assembly.LowTwoRank.statedSL_eq_range_toGL n K) ▸ s.2⟩
  have h2 := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) h
  exact h2

variable {K K' : Type} [Field K] [Field K']

noncomputable def slMapEquiv (σ : K ≃+* K') : SL(3, K) ≃* SL(3, K') where
  toFun := Matrix.SpecialLinearGroup.map σ.toRingHom
  invFun := Matrix.SpecialLinearGroup.map σ.symm.toRingHom
  left_inv A := Subtype.ext (by ext i j; simp)
  right_inv A := Subtype.ext (by ext i j; simp)
  map_mul' := map_mul _

noncomputable def vecMapEquiv (σ : K ≃+* K') :
    Multiplicative (Fin 3 → K) ≃* Multiplicative (Fin 3 → K') where
  toFun w := Multiplicative.ofAdd (fun i => σ (Multiplicative.toAdd w i))
  invFun w := Multiplicative.ofAdd (fun i => σ.symm (Multiplicative.toAdd w i))
  left_inv w := by simp
  right_inv w := by simp
  map_mul' a b := by
    show Multiplicative.ofAdd _ = Multiplicative.ofAdd _ * Multiplicative.ofAdd _
    rw [← ofAdd_add]
    congr 1
    funext i
    simp [toAdd_mul, map_add]

theorem vecMapEquiv_mulVec (σ : K ≃+* K') (A : SL(3, K)) (w : Multiplicative (Fin 3 → K)) :
    vecMapEquiv σ (Multiplicative.ofAdd ((A : Matrix (Fin 3) (Fin 3) K).mulVec
        (Multiplicative.toAdd w))) =
      natAct3 (slMapEquiv σ A) (vecMapEquiv σ w) := by
  change Multiplicative.ofAdd (fun i => σ (((A : Matrix (Fin 3) (Fin 3) K).mulVec
      (Multiplicative.toAdd w)) i)) =
    Multiplicative.ofAdd ((slMapEquiv σ A) • Multiplicative.toAdd (vecMapEquiv σ w))
  congr 1
  funext i
  simp [slMapEquiv, vecMapEquiv, Matrix.mulVec, dotProduct, map_sum, map_mul,
    Matrix.SpecialLinearGroup.smul_def]

theorem exists_eq_smul_of_card {F : Type} [Field F] [Finite F]
    (A : Subgroup (Multiplicative (Fin 3 → F)))
    (hsmul : ∀ c : F, ∀ a ∈ A, Multiplicative.ofAdd (c • Multiplicative.toAdd a) ∈ A)
    (hcard : Nat.card A = Nat.card F) :
    ∃ w : Fin 3 → F, w ≠ 0 ∧ ∀ a : Multiplicative (Fin 3 → F),
      a ∈ A ↔ ∃ c : F, Multiplicative.toAdd a = c • w := by
  have hA : A ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card A = 1 := by rw [hbot]; exact Subgroup.card_bot
    have h2 : 1 < Nat.card F := Finite.one_lt_card
    omega
  obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA
  set a₀ : Multiplicative (Fin 3 → F) := (x : Multiplicative (Fin 3 → F)) with ha₀def
  have ha₀ : a₀ ∈ A := x.2
  have ha₀1 : a₀ ≠ 1 := fun h => hx (Subtype.ext h)
  set w := Multiplicative.toAdd a₀ with hw
  have hw0 : w ≠ 0 := fun h => ha₀1 (by rw [← ofAdd_toAdd a₀, ← hw, h, ofAdd_zero])
  refine ⟨w, hw0, fun a => ⟨fun ha => ?_, ?_⟩⟩
  · let f : F → ↥A := fun c => ⟨Multiplicative.ofAdd (c • w), hsmul c a₀ ha₀⟩
    have hf : Function.Injective f := by
      intro c c' hcc'
      have h := congrArg (fun x : ↥A => Multiplicative.toAdd (x : Multiplicative (Fin 3 → F)))
        hcc'
      simp only [f, toAdd_ofAdd] at h
      exact smul_left_injective F hw0 h
    obtain ⟨c, hc⟩ := (hf.bijective_of_nat_card_le hcard.le).2 ⟨a, ha⟩
    refine ⟨c, ?_⟩
    have h := congrArg (fun x : ↥A => Multiplicative.toAdd (x : Multiplicative (Fin 3 → F))) hc
    simpa [f] using h.symm
  · rintro ⟨c, hc⟩
    have h := hsmul c a₀ ha₀
    rwa [← hw, ← hc, ofAdd_toAdd] at h

end CFSG.Quasithin.Vol2.Ch11.SecD
