module

public import CFSG.LocalAnalysis.StandardType.GGRankOneTorus
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Steinberg

private theorem ggRootKer_sl2Diag_mul {k : Type*} [Field k] (s t : kˣ) :
    PsiDiagChar.sl2Diag (s * t) = PsiDiagChar.sl2Diag s * PsiDiagChar.sl2Diag t := by
  ext a b
  simp only [Matrix.SpecialLinearGroup.coe_mul, PsiDiagChar.coe_sl2Diag, Matrix.mul_fin_two]
  fin_cases a <;> fin_cases b <;> simp [mul_comm]

theorem ggRootKer_torusElt_mul {K : Type*} [Group K] {D : UniversalRootDatum K} {k : Type*}
    [Field k] {x : (Fin D.rank → ℤ) → k → K}
    {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (CFSG.LieType.Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
    (hE : ChevalleyExtras D k x C O) (j : Fin D.rank) (s t : kˣ) :
    PsiDiag.torusElt x j (s * t) = PsiDiag.torusElt x j s * PsiDiag.torusElt x j t := by
  obtain ⟨φ, -, hu, hl⟩ := hE.rankOne j
  have e := RankOneXfer.torusElt_eq_map_sl2Diag j φ hu hl
  rw [e, e, e, ← map_mul, ggRootKer_sl2Diag_mul]

theorem ggRootKer_torusElt_commute {K : Type*} [Group K] {D : UniversalRootDatum K} {k : Type*}
    [Field k] {x : (Fin D.rank → ℤ) → k → K}
    {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (CFSG.LieType.Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
    (hE : ChevalleyExtras D k x C O) (a b : Fin D.rank) (s t : kˣ) :
    Commute (PsiDiag.torusElt x a s) (PsiDiag.torusElt x b t) := by
  set h := PsiDiag.torusElt x b t
  obtain ⟨χ, hχ⟩ : ∃ χ : kˣ, χ = t ^ coroot D.cartan b (Pi.single a 1) := ⟨_, rfl⟩
  have hw : ∀ r : kˣ, h * weylElement x a r * h⁻¹ = weylElement x a (χ * r) := by
    intro r
    have e1 : h * x (Pi.single a 1) r * h⁻¹ = x (Pi.single a 1) ((χ * r : kˣ) : k) := by
      rw [PsiDiag.torusElt_conj hE b t (single_mem_roots a), ← hχ, Units.val_mul]
    have e2 : h * x (-Pi.single a 1) (-((r⁻¹ : kˣ) : k)) * h⁻¹ =
        x (-Pi.single a 1) (-(((χ * r)⁻¹ : kˣ) : k)) := by
      rw [PsiDiag.torusElt_conj hE b t (neg_single_mem_roots a), map_neg, zpow_neg, ← hχ,
        mul_inv, Units.val_mul]
      ring
    calc h * weylElement x a r * h⁻¹ = (h * x (Pi.single a 1) r * h⁻¹) *
          (h * x (-Pi.single a 1) (-((r⁻¹ : kˣ) : k)) * h⁻¹) *
            (h * x (Pi.single a 1) r * h⁻¹) := by
          simp only [weylElement]
          group
      _ = weylElement x a (χ * r) := by rw [e1, e2]; rfl
  have hc : h * PsiDiag.torusElt x a s * h⁻¹ = PsiDiag.torusElt x a s := by
    have e : h * PsiDiag.torusElt x a s * h⁻¹ =
        (h * weylElement x a s * h⁻¹) * (h * weylElement x a 1 * h⁻¹)⁻¹ := by
      simp only [PsiDiag.torusElt]
      group
    have e2 : weylElement x a (χ * s) * (weylElement x a (χ * 1))⁻¹ =
        PsiDiag.torusElt x a (s * χ) * (PsiDiag.torusElt x a χ)⁻¹ := by
      simp only [PsiDiag.torusElt, mul_comm χ s, mul_one]
      group
    rw [e, hw, hw, e2, ggRootKer_torusElt_mul hE, mul_inv_cancel_right]
  exact (mul_inv_eq_iff_eq_mul.mp hc).symm

theorem ggRootKer_mem_ggTorus_of_scalar {K : Type*} [Group K] {D : UniversalRootDatum K}
    {k : Type*} [Field k] {x : (Fin D.rank → ℤ) → k → K}
    {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (CFSG.LieType.Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
    (hE : ChevalleyExtras D k x C O) {h : K}
    (hh : ∀ β ∈ D.roots, ∃ μ : kˣ, ∀ c : k, h * x β c * h⁻¹ = x β ((μ : k) * c)) :
    h ∈ ggTorus D := by
  refine Subgroup.mem_iInf.mpr fun β => Subgroup.mem_iInf.mpr fun hβ => ?_
  obtain ⟨μ, hμ⟩ := hh β hβ
  have hpar := (hE.param β hβ).1
  refine Subgroup.mem_normalizer_iff.mpr fun g => ⟨fun hg => ?_, fun hg => ?_⟩
  · obtain ⟨c, rfl⟩ := (hpar g).mp hg
    rw [hμ c]
    exact (hpar _).mpr ⟨_, rfl⟩
  · obtain ⟨c, hcg⟩ := (hpar _).mp hg
    have e : g = h⁻¹ * x β c * h := by
      rw [hcg]
      group
    rw [e, PsiDiag.inv_conj_of_conj hμ c]
    exact (hpar _).mpr ⟨_, rfl⟩

private theorem ggRootKer_list_prod_pow_eq_one {K : Type*} [Group K] (L : List K)
    (hc : ∀ a ∈ L, ∀ b ∈ L, Commute a b) {n : ℕ} (h1 : ∀ a ∈ L, a ^ n = 1) :
    L.prod ^ n = 1 := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.prod_cons, (Commute.list_prod_right _ _ fun b hb =>
      hc a List.mem_cons_self b (List.mem_cons_of_mem a hb)).mul_pow, h1 a List.mem_cons_self,
      one_mul]
    exact ih (fun y hy z hz => hc y (List.mem_cons_of_mem a hy) z (List.mem_cons_of_mem a hz))
      fun y hy => h1 y (List.mem_cons_of_mem a hy)

theorem ggRootKer_exists_gen {K : Type*} [Group K] {D : UniversalRootDatum K} {k : Type*}
    [Field k] {x : (Fin D.rank → ℤ) → k → K}
    {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (CFSG.LieType.Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
    (hE : ChevalleyExtras D k x C O) (e : Fin D.rank → ℤ) {p : ℕ} {ζ : kˣ} (hζ : ζ ^ p = 1) :
    ∃ g ∈ ggTorus D, g ^ p = 1 ∧ ∀ β ∈ D.roots, ∀ c : k,
      g * x β c * g⁻¹ = x β (((ζ ^ ∑ j, e j * coroot D.cartan j β : kˣ) : k) * c) := by
  have hact : ∀ β ∈ D.roots, ∀ c : k,
      PsiDiag.torusProd x (fun j => ζ ^ e j) * x β c *
          (PsiDiag.torusProd x (fun j => ζ ^ e j))⁻¹ =
        x β (((ζ ^ ∑ j, e j * coroot D.cartan j β : kˣ) : k) * c) := by
    intro β hβ c
    rw [PsiDiag.torusProd_conj hE _ hβ c]
    simp only [← zpow_mul]
    rw [PsiDiag.prod_zpow_eq_zpow_sum]
  refine ⟨_, ggRootKer_mem_ggTorus_of_scalar hE fun β hβ => ⟨_, hact β hβ⟩, ?_, hact⟩
  refine ggRootKer_list_prod_pow_eq_one _ ?_ ?_
  · simp only [List.mem_map, List.mem_finRange, true_and]
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact ggRootKer_torusElt_commute hE i j _ _
  · simp only [List.mem_map, List.mem_finRange, true_and]
    rintro _ ⟨i, rfl⟩
    have hpow := map_pow (MonoidHom.mk' (fun s => PsiDiag.torusElt x i s)
      (ggRootKer_torusElt_mul hE i)) (ζ ^ e i) p
    simp only [MonoidHom.mk'_apply] at hpow
    rw [← hpow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ, one_zpow]
    exact map_one (MonoidHom.mk' (fun s => PsiDiag.torusElt x i s) (ggRootKer_torusElt_mul hE i))

end CFSG.StandardType

end
