module

public import CFSG.LocalAnalysis.StandardType.GGStdPosLeviTorus
public import CFSG.LocalAnalysis.StandardType.GGStdPosRootKerLift
public import CFSG.LocalAnalysis.StandardType.GGStdPosLocalDefs
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeSUExc
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.CurtisTits

theorem ggStdPosLevi_commute {K : Type*} [Group K] {D : UniversalRootDatum K}
    {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {k : Type*} [Field k] [Finite k]
    [CharP k 2] {x : (Fin D.rank → ℤ) → k → K}
    {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (CFSG.LieType.Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H) (hE : ChevalleyExtras D k x C O)
    {G : Type*} [Group G] (ψ : K →* G) (hker : ψ.ker ≤ Subgroup.center K) {Bs : Subgroup G}
    (hBs : GGKGPosStdPos D ψ Bs) {ν : GGWeyl D →* K} (hν : GGWeylLift D ν) (w : GGWeyl D)
    (i : Fin D.rank) {b : G} (hb : b ∈ Bs)
    (hbm : b * ψ (ν (w * (coxeterMatrix D.isFiniteType).simple i * w⁻¹)) =
      ψ (ν (w * (coxeterMatrix D.isFiniteType).simple i * w⁻¹)) * b) :
    ∀ z ∈ D.rootGroup (weylAction D.isFiniteType w (Pi.single i 1)) ⊔
        D.rootGroup (-weylAction D.isFiniteType w (Pi.single i 1)), b * ψ z = ψ z * b := by
  have hγ : weylAction D.isFiniteType w (Pi.single i 1) ∈ D.roots :=
    weylAction_mem_roots (single_mem_roots i) w
  have hs : weylAction D.isFiniteType (w * (coxeterMatrix D.isFiniteType).simple i * w⁻¹)
      (weylAction D.isFiniteType w (Pi.single i 1)) =
        -weylAction D.isFiniteType w (Pi.single i 1) := by
    have hs1 : weylAction D.isFiniteType ((coxeterMatrix D.isFiniteType).simple i)
        (Pi.single i 1) = -Pi.single i 1 := weylAction_simple_single D.isFiniteType i
    rw [weylAction_mul_apply, weylAction_mul_apply, weylAction_inv_apply_apply, hs1, map_neg]
  obtain ⟨φ, hφ, hu, hl⟩ := hE.rankOne i
  obtain ⟨a, ha⟩ := ggRootKer_weylLift_conj hE hν w (single_mem_roots i)
  obtain ⟨a', ha'⟩ := ggRootKer_weylLift_conj hE hν w (neg_single_mem_roots i)
  obtain ⟨a'', ha''⟩ :=
    ggRootKer_weylLift_conj hE hν (w * (coxeterMatrix D.isFiniteType).simple i * w⁻¹) hγ
  rw [map_neg] at ha'
  rw [hs] at ha''
  generalize weylAction D.isFiniteType w (Pi.single i 1) = γ at hγ ha ha' ha'' ⊢
  generalize ν (w * (coxeterMatrix D.isFiniteType).simple i * w⁻¹) = m at hbm ha''
  have hγ' : -γ ∈ D.roots := OfCartan.neg_mem_roots D.isFiniteType hγ
  have hpar := (hE.param γ hγ).1
  have hpar' := (hE.param (-γ) hγ').1
  obtain ⟨h₁, hh₁, hz₁⟩ := hBs b hb γ hγ
  obtain ⟨h₂, hh₂, hz₂⟩ := hBs b hb (-γ) hγ'
  obtain ⟨μ₁, hμ₁, -⟩ := ggStdPosLevi_conj_scalar hct hext hBU hE hh₁ hγ
  obtain ⟨μ₂, -, hμ₂⟩ := ggStdPosLevi_conj_scalar hct hext hBU hE hh₂ hγ
  have hA : ∀ c, b * ψ (x γ c) * b⁻¹ = ψ (x γ ((μ₁ : k) * c)) := fun c => by
    rw [hz₁ _ ((hpar _).mpr ⟨c, rfl⟩), hμ₁]
  have hB : ∀ c, b * ψ (x (-γ) c) * b⁻¹ = ψ (x (-γ) (((μ₂⁻¹ : kˣ) : k) * c)) := fun c => by
    rw [hz₂ _ ((hpar' _).mpr ⟨c, rfl⟩), hμ₂]
  obtain ⟨Φ, hΦ, hΦu, hΦl⟩ : ∃ Φ : Matrix.SpecialLinearGroup (Fin 2) k →* G,
      Function.Injective Φ ∧ (∀ c, Φ (sl2Upper c) = ψ (x γ ((a : k) * c))) ∧
        ∀ c, Φ (sl2Lower c) = ψ (x (-γ) ((a' : k) * c)) :=
    ⟨ψ.comp ((MulAut.conj (ν w)).toMonoidHom.comp φ),
      PsiDiag.injective_comp_of_ker_le_center _ ((MulAut.conj (ν w)).injective.comp hφ) ψ hker,
      fun c => by
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hu, ha],
      fun c => by
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hl, ha']⟩
  have hbu : ∀ c, b * Φ (sl2Upper c) * b⁻¹ = Φ (sl2Upper ((μ₁ : k) * c)) := fun c => by
    rw [hΦu, hΦu, hA, mul_left_comm]
  have hbl : ∀ c, b * Φ (sl2Lower c) * b⁻¹ = Φ (sl2Lower (((μ₂⁻¹ : kˣ) : k) * c)) := fun c => by
    rw [hΦl, hΦl, hB, mul_left_comm]
  have hm1 := PsiDiagChar.mul_eq_one_of_conj_sl2 Φ hΦ (d := b⁻¹) μ₁
    (fun c => by rw [inv_inv]; exact hbu c) (fun c => by rw [inv_inv]; exact hbl c)
  have hΦm : ∀ c, ψ m * Φ (sl2Upper c) * (ψ m)⁻¹ =
      Φ (sl2Lower (((a'⁻¹ * a'' * a : kˣ) : k) * c)) := fun c => by
    have e : (a' : k) * (((a'⁻¹ * a'' * a : kˣ) : k) * c) = a'' * (a * c) := by
      simp only [Units.val_mul, ← mul_assoc, Units.mul_inv, one_mul]
    rw [hΦu, hΦl, e, ← map_inv ψ, ← map_mul ψ, ← map_mul ψ, ha'']
  have hcomm : ∀ Y : G, b * (ψ m * Y * (ψ m)⁻¹) * b⁻¹ = ψ m * (b * Y * b⁻¹) * (ψ m)⁻¹ := by
    have hbm' := congrArg (·⁻¹) hbm
    simp only [mul_inv_rev] at hbm'
    intro Y
    calc b * (ψ m * Y * (ψ m)⁻¹) * b⁻¹ = b * ψ m * Y * ((ψ m)⁻¹ * b⁻¹) := by group
      _ = ψ m * b * Y * (b⁻¹ * (ψ m)⁻¹) := by rw [hbm, hbm']
      _ = ψ m * (b * Y * b⁻¹) * (ψ m)⁻¹ := by group
  have key : ∀ c, Φ (sl2Lower (((a'⁻¹ * a'' * a : kˣ) : k) * ((μ₁ : k) * c))) =
      Φ (sl2Lower (((μ₂⁻¹ : kˣ) : k) * (((a'⁻¹ * a'' * a : kˣ) : k) * c))) := fun c => by
    rw [← hΦm, ← hbu, ← hcomm, hΦm, hbl]
  have h3 : (μ₁ : k) = ((μ₂⁻¹ : kˣ) : k) := by
    have h2 := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) k =>
      (M : Matrix (Fin 2) (Fin 2) k) 1 0) (hΦ (key 1))
    simp only [PsiDiag.coe_sl2Lower, Matrix.of_apply, Matrix.cons_val_one, Matrix.cons_val_zero,
      Matrix.head_cons, mul_one] at h2
    exact mul_left_cancel₀ (Units.ne_zero _) (h2.trans (mul_comm _ _))
  have h1 : (μ₁ : k) = 1 := CharTwo.sq_injective (show (μ₁ : k) ^ 2 = 1 ^ 2 by
    rw [one_pow, sq]
    exact (congrArg ((μ₁ : k) * ·) h3).trans hm1)
  have hA' : ∀ c, b * ψ (x γ c) * b⁻¹ = ψ (x γ c) := fun c => by rw [hA, h1, one_mul]
  have hB' : ∀ c, b * ψ (x (-γ) c) * b⁻¹ = ψ (x (-γ) c) := fun c => by
    rw [hB, ← h3, h1, one_mul]
  have hle : D.rootGroup γ ⊔ D.rootGroup (-γ) ≤ (Subgroup.centralizer {b}).comap ψ := by
    refine sup_le (fun y hy => ?_) (fun y hy => ?_)
    · obtain ⟨c, rfl⟩ := (hpar y).mp hy
      exact Subgroup.mem_comap.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
        (mul_inv_eq_iff_eq_mul.mp (hA' c)).symm)
    · obtain ⟨c, rfl⟩ := (hpar' y).mp hy
      exact Subgroup.mem_comap.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
        (mul_inv_eq_iff_eq_mul.mp (hB' c)).symm)
  intro z hz
  exact (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_comap.mp (hle hz))).symm

end CFSG.StandardType

end
