module

public import CFSG.LocalAnalysis.StandardType.GGStdPosTorus
public import CFSG.LocalAnalysis.StandardType.GGStdPosRootKerTorus
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.CurtisTits

private theorem ggStdPosLevi_eq_sl2Diag {k : Type*} [Field k]
    {τ : Matrix.SpecialLinearGroup (Fin 2) k} {c₁ c₂ : k}
    (hu : τ * sl2Upper 1 = sl2Upper c₁ * τ) (hl : τ * sl2Lower 1 = sl2Lower c₂ * τ) :
    ∃ s : kˣ, τ = PsiDiagChar.sl2Diag s := by
  have h10 : (τ : Matrix (Fin 2) (Fin 2) k) 1 0 = 0 := by
    have := congrArg (fun N : Matrix.SpecialLinearGroup (Fin 2) k =>
      (N : Matrix (Fin 2) (Fin 2) k) 1 1) hu
    simpa [Matrix.SpecialLinearGroup.coe_mul, PsiDiag.coe_sl2Upper, Matrix.mul_apply,
      Fin.sum_univ_two] using this
  have h01 : (τ : Matrix (Fin 2) (Fin 2) k) 0 1 = 0 := by
    have := congrArg (fun N : Matrix.SpecialLinearGroup (Fin 2) k =>
      (N : Matrix (Fin 2) (Fin 2) k) 0 0) hl
    simpa [Matrix.SpecialLinearGroup.coe_mul, PsiDiag.coe_sl2Lower, Matrix.mul_apply,
      Fin.sum_univ_two] using this
  have hdet := τ.prop
  rw [Matrix.det_fin_two, h01, h10, mul_zero, sub_zero] at hdet
  have ha : (τ : Matrix (Fin 2) (Fin 2) k) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  refine ⟨Units.mk0 _ ha, ?_⟩
  ext a b
  fin_cases a <;> fin_cases b
  · simp [PsiDiagChar.coe_sl2Diag]
  · simpa [PsiDiagChar.coe_sl2Diag] using h01
  · simpa [PsiDiagChar.coe_sl2Diag] using h10
  · simpa [PsiDiagChar.coe_sl2Diag] using eq_inv_of_mul_eq_one_right hdet

theorem ggStdPosLevi_eq_torusElt {K : Type*} [Group K] {D : UniversalRootDatum K}
    {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {k : Type*} [Field k]
    {x : (Fin D.rank → ℤ) → k → K} {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (CFSG.LieType.Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hE : ChevalleyExtras D k x C O) {j : Fin D.rank} {h : K} (hh : h ∈ H j) :
    ∃ s : kˣ, h = PsiDiag.torusElt x j s := by
  obtain ⟨φ, hφ, hu, hl⟩ := hE.rankOne j
  have hpar := (hE.param _ (single_mem_roots (D := D) j)).1
  have hpar' := (hE.param _ (neg_single_mem_roots (D := D) j)).1
  have hle : rankOne D.rootGroup j ≤ φ.range := by
    refine sup_le (fun z hz => ?_) (fun z hz => ?_)
    · obtain ⟨c, rfl⟩ := (hpar z).mp hz
      exact ⟨sl2Upper c, hu c⟩
    · obtain ⟨c, rfl⟩ := (hpar' z).mp hz
      exact ⟨sl2Lower c, hl c⟩
  obtain ⟨τ, rfl⟩ := hle (hct.H_le j hh)
  obtain ⟨c₁, hc₁⟩ := (hpar _).mp (hct.H_conj_mem j _ (single_mem_roots j) _ hh _
    ((hpar _).mpr ⟨1, rfl⟩))
  obtain ⟨c₂, hc₂⟩ := (hpar' _).mp (hct.H_conj_mem j _ (neg_single_mem_roots j) _ hh _
    ((hpar' _).mpr ⟨1, rfl⟩))
  have e1 : τ * sl2Upper 1 = sl2Upper c₁ * τ := by
    apply hφ
    rw [map_mul, map_mul, hu, hu, hc₁]
    group
  have e2 : τ * sl2Lower 1 = sl2Lower c₂ * τ := by
    apply hφ
    rw [map_mul, map_mul, hl, hl, hc₂]
    group
  obtain ⟨s, rfl⟩ := ggStdPosLevi_eq_sl2Diag e1 e2
  exact ⟨s, (RankOneXfer.torusElt_eq_map_sl2Diag j φ hu hl s).symm⟩

theorem ggStdPosLevi_conj_scalar {K : Type*} [Group K] {D : UniversalRootDatum K}
    {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {k : Type*} [Field k]
    {x : (Fin D.rank → ℤ) → k → K} {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (CFSG.LieType.Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H) (hE : ChevalleyExtras D k x C O)
    {h : K} (hh : h ∈ ggTorus D) {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) :
    ∃ μ : kˣ, (∀ c : k, h * x γ c * h⁻¹ = x γ ((μ : k) * c)) ∧
      ∀ c : k, h * x (-γ) c * h⁻¹ = x (-γ) (((μ⁻¹ : kˣ) : k) * c) := by
  have hγ' : -γ ∈ D.roots := OfCartan.neg_mem_roots D.isFiniteType hγ
  rw [ggStdPos_ggTorus_eq hct hext hBU] at hh
  refine Subgroup.iSup_induction H (C := fun t => ∃ μ : kˣ,
    (∀ c : k, t * x γ c * t⁻¹ = x γ ((μ : k) * c)) ∧
      ∀ c : k, t * x (-γ) c * t⁻¹ = x (-γ) (((μ⁻¹ : kˣ) : k) * c)) hh
    (fun j y hy => ?_) ⟨1, fun c => by simp, fun c => by simp⟩ fun y z hy hz => ?_
  · obtain ⟨s, rfl⟩ := ggStdPosLevi_eq_torusElt hct hE hy
    refine ⟨s ^ coroot D.cartan j γ, PsiDiag.torusElt_conj hE j s hγ, fun c => ?_⟩
    rw [PsiDiag.torusElt_conj hE j s hγ' c, map_neg, zpow_neg]
  · obtain ⟨μ, h1, h2⟩ := hy
    obtain ⟨μ', h1', h2'⟩ := hz
    refine ⟨μ * μ', fun c => ?_, fun c => ?_⟩
    · calc y * z * x γ c * (y * z)⁻¹ = y * (z * x γ c * z⁻¹) * y⁻¹ := by group
        _ = x γ (((μ * μ' : kˣ) : k) * c) := by rw [h1', h1, Units.val_mul, mul_assoc]
    · calc y * z * x (-γ) c * (y * z)⁻¹ = y * (z * x (-γ) c * z⁻¹) * y⁻¹ := by group
        _ = x (-γ) ((((μ * μ')⁻¹ : kˣ) : k) * c) := by
          rw [h2', h2, mul_inv, Units.val_mul, mul_assoc]

theorem ggStdPosLevi_pow_card {K : Type*} [Group K] {D : UniversalRootDatum K}
    {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {k : Type*} [Field k]
    {x : (Fin D.rank → ℤ) → k → K} {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (CFSG.LieType.Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H) (hE : ChevalleyExtras D k x C O)
    {h : K} (hh : h ∈ ggTorus D) : h ^ Nat.card kˣ = 1 := by
  rw [ggStdPos_ggTorus_eq hct hext hBU] at hh
  have hab := LieType.TitsSimplicity.iSup_le_centralizer_iSup hext
  refine Subgroup.iSup_induction' H (C := fun t _ => t ^ Nat.card kˣ = 1) (fun j y hy => ?_)
    (one_pow _) (fun y z hy hz hy' hz' => ?_) hh
  · obtain ⟨s, rfl⟩ := ggStdPosLevi_eq_torusElt hct hE hy
    have hpow := map_pow (MonoidHom.mk' (fun s => PsiDiag.torusElt x j s)
      (ggRootKer_torusElt_mul hE j)) s (Nat.card kˣ)
    simp only [MonoidHom.mk'_apply] at hpow
    rw [← hpow, pow_card_eq_one']
    exact map_one (MonoidHom.mk' (fun s => PsiDiag.torusElt x j s) (ggRootKer_torusElt_mul hE j))
  · have hc : Commute y z := Subgroup.mem_centralizer_iff.mp (hab hz) y hy
    rw [hc.mul_pow, hy', hz', one_mul]

end CFSG.StandardType

end
