module

public import CFSG.Quasithin.Vol2.Ch11SecB414ML

public section

namespace CFSG.Quasithin.H13.Ch4.B414.M

open CFSG.Open hiding StatedSL StatedSp
open CFSG.Quasithin CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
open CFSG.Assembly.LowTwoRank (StatedSL)
open Matrix

variable {F : Type} [Field F] [Finite F] [CharP F 2] {G : Type} [Group G]
  {Γ V Z L X : Subgroup G} {k : ℕ} {α : ↥Γ →* PGL3 F} (m : Model Γ V Z F k α)
  (hF : Nat.card F = 4) (hLΓ : L ≤ Γ) (hXΓ : X ≤ Γ) (hL : (L.subgroupOf Γ).map α = Ptheta F 0)
  {ν : Fˣ} (hX : (X.subgroupOf Γ).map α = Subgroup.zpowers (ProjGenLinGroup.mk (dgHom ν)))
  (α₀' : ↥(Ptheta F 0) →* ↥(StatedSL 2 F)) (α₀ : ↥L →* ↥(StatedSL 2 F))
  (hcomp : ∀ (l : ↥L) (γ : ↥Γ) (p : ↥(Ptheta F 0)), (γ : G) = l →
    (p : PGL3 F) = α γ → α₀ l = α₀' p)
  (T : (Fin 2 → F) ≃+ (Fin 2 → F))
  (hT : ∀ (p : ↥(Ptheta F 0)) (v : Fin 2 → F),
    T (((rhoRef hF p : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ v) =
      (((α₀' p : StatedSL 2 F) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ T v)
  {γx : ↥Γ} {c : Fˣ} (hγx : α γx = ProjGenLinGroup.mk (dgHom c)) {μ : F}
  (hμ : ∀ w : Fin 2 → F, T ((c : F) • w) = μ • T w)

include hF hLΓ hL hcomp hT hγx hμ

theorem Model.natEig_Wp : IsNatEigSection L (γx : G) α₀ (m.pre ⊥) (m.pre Wp) (μ ^ (k + 1)) := by
  refine m.isNatEigSection_layer hF hLΓ hL (W := ⊥) (W' := Wp) kpHom (fun v => ?_)
    (fun M hM => ?_) (fun A _ _ _ M hM => kp_cnj hM) α₀' α₀ hcomp T hT hγx
    (a := (c : F) ^ (k + 1)) (fun M _ => ?_) (tScalar_pow T hμ (k + 1))
  · refine ⟨!![0, v 0, v 1; 0, 0, 0; 0, 0, 0], ?_, ?_, ?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;>
        first | rfl | exact absurd ⟨rfl, by decide⟩ hij
    · simp [Matrix.trace_fin_three]
    · funext i
      fin_cases i <;> rfl
  · have hM' : ∀ i j : Fin 3, ¬ (i = 0 ∧ j ≠ 0) → M i j = 0 := hM
    rw [kpHom_apply, AddSubgroup.mem_bot]
    constructor
    · intro h
      have h01 : M 0 1 = 0 := by simpa [kp] using congrFun h 0
      have h02 : M 0 2 = 0 := by simpa [kp] using congrFun h 1
      ext i j
      by_cases hij : i = 0 ∧ j ≠ 0
      · obtain ⟨rfl, hj⟩ := hij
        fin_cases j
        · exact absurd rfl hj
        · simpa using h01
        · simpa using h02
      · simpa using hM' i j hij
    · rintro rfl
      funext i
      fin_cases i <;> rfl
  · rw [kpHom_apply, kpHom_apply, kp_dg, pow_succ]

theorem Model.natEig_W3 :
    IsNatEigSection L (γx : G) α₀ (m.pre W2) (m.pre W3) (μ ^ (2 * k)) := by
  refine m.isNatEigSection_layer hF hLΓ hL (W := W2) (W' := W3) k2Hom (fun v => ?_)
    (fun M hM => ?_) (fun A h10 h20 _ M hM => k2_cnj h10 h20 (pow_four_eq hF) hM.2.1 hM.2.2.1
      hM.2.2.2) α₀' α₀ hcomp T hT hγx
    (a := (c : F) ^ (2 * k)) (fun M _ => ?_) (tScalar_pow T hμ (2 * k))
  · refine ⟨!![0, 0, 0; 0, 0, v 1 ^ 2; 0, v 0 ^ 2, 0], ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · rfl
    · rfl
    · rfl
    · rfl
    · simp [Matrix.trace_fin_three]
    · funext i
      fin_cases i <;> simp [k2Hom_apply, k2, ← pow_mul, pow_four_eq hF]
  · obtain ⟨h1, h2, h3, h4⟩ := hM
    rw [k2Hom_apply]
    constructor
    · intro h
      have h21 : M 2 1 = 0 := by simpa [k2] using congrFun h 0
      have h12 : M 1 2 = 0 := by simpa [k2] using congrFun h 1
      exact ⟨h1, h2, h3, h12, h21, h4⟩
    · rintro ⟨-, -, -, h12, h21, -⟩
      funext i
      fin_cases i <;> simp [k2, h12, h21]
  · rw [k2Hom_apply, k2Hom_apply, k2_dg, ← pow_mul, mul_comm]

theorem Model.natEig_Wsl :
    IsNatEigSection L (γx : G) α₀ (m.pre W4) (m.pre Wsl) (μ ^ (k + 2)) := by
  have hc3 : (c : F) ^ 3 = 1 := pow_three_eq_one hF c.ne_zero
  have hcinv : ((c⁻¹ : Fˣ) : F) = (c : F) ^ 2 := by
    rw [Units.val_inv_eq_inv_val, inv_eq_iff_eq_inv]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ']; exact hc3)
  refine m.isNatEigSection_layer hF hLΓ hL (W := W4) (W' := Wsl) kmHom (fun v => ?_)
    (fun M hM => ?_) (fun A h10 h20 hdet M _ => km_cnj h10 h20 (delta_eq hF h10 h20 hdet))
    α₀' α₀ hcomp T hT hγx (a := (c : F) ^ (k + 2)) (fun M _ => ?_) (tScalar_pow T hμ (k + 2))
  · refine ⟨!![0, 0, 0; v 1, 0, 0; v 0, 0, 0], ?_, ?_, ?_⟩
    · show Matrix.trace _ = 0
      simp [Matrix.trace_fin_three]
    · simp [Matrix.trace_fin_three]
    · funext i
      fin_cases i <;> rfl
  · rw [kmHom_apply]
    constructor
    · intro h
      have h20 : M 2 0 = 0 := by simpa [km] using congrFun h 0
      have h10 : M 1 0 = 0 := by simpa [km] using congrFun h 1
      exact ⟨hM, h10, h20⟩
    · rintro ⟨-, h10, h20⟩
      funext i
      fin_cases i <;> simp [km, h10, h20]
  · rw [kmHom_apply, kmHom_apply, km_dg, hcinv, ← pow_add]

end CFSG.Quasithin.H13.Ch4.B414.M
