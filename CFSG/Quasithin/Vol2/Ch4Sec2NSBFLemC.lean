module

public import CFSG.Quasithin.Vol2.Ch4Sec2NSBKStd

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.Ch4.NSB

open Matrix

private theorem nsbfc_zmod_two_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by
  decide

private theorem nsbfc_map_smul {j n : ℕ} (ι : (Fin j → ZMod 2) →+ (Fin n → ZMod 2))
    (c : ZMod 2) (w : Fin j → ZMod 2) : ι (c • w) = c • ι w := by
  rcases nsbfc_zmod_two_cases c with rfl | rfl <;> simp

theorem exists_functional_sep {j : ℕ} {w₀ w₁ : Fin j → ZMod 2} (hw₁ : w₁ ≠ 0) (hne : w₁ ≠ w₀) :
    ∃ f : (Fin j → ZMod 2) →+ ZMod 2, f w₀ = 0 ∧ f w₁ = 1 := by
  have hnot : w₁ ∉ Submodule.span (ZMod 2) {w₀} := by
    rw [Submodule.mem_span_singleton]
    rintro ⟨a, rfl⟩
    rcases nsbfc_zmod_two_cases a with rfl | rfl
    · exact hw₁ (by simp)
    · exact hne (by simp)
  obtain ⟨f, hfw₁, hfmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  have hf0 : f w₀ = 0 := by
    have hmem : f w₀ ∈ (Submodule.span (ZMod 2) {w₀}).map f :=
      Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self w₀)
    rw [hfmap, Submodule.mem_bot] at hmem
    exact hmem
  have hf1 : f w₁ = 1 := (nsbfc_zmod_two_cases _).resolve_left hfw₁
  exact ⟨f.toAddMonoidHom, hf0, hf1⟩

theorem exists_gl_extend_transvection {n j : ℕ} (ι : (Fin j → ZMod 2) →+ (Fin n → ZMod 2))
    (hι : Function.Injective ι) (w₀ : Fin j → ZMod 2) (f : (Fin j → ZMod 2) →+ ZMod 2)
    (hf : f w₀ = 0) :
    ∃ M : GL (Fin n) (ZMod 2), ∀ x : Fin j → ZMod 2,
      (M : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (ι x) = ι (x + f x • w₀) := by
  obtain ⟨ιl, hιl⟩ : ∃ L : (Fin j → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2), ∀ x, L x = ι x :=
    ⟨ι.toZModLinearMap 2, fun _ => rfl⟩
  have hιinj : Function.Injective ιl := by
    intro a b h
    rw [hιl, hιl] at h
    exact hι h
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective ιl (LinearMap.ker_eq_bot.mpr hιinj)
  have hgι : ∀ x, g (ι x) = x := by
    intro x
    have h := LinearMap.congr_fun hg x
    rw [LinearMap.comp_apply, LinearMap.id_apply, hιl] at h
    exact h
  obtain ⟨Fl, hFl⟩ : ∃ L : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2, ∀ y, L y = f (g y) :=
    ⟨(f.toZModLinearMap 2).comp g, fun _ => rfl⟩
  have hFι : ∀ x, Fl (ι x) = f x := fun x => by rw [hFl, hgι]
  have hFv : Fl (ι w₀) = 0 := by rw [hFι, hf]
  obtain ⟨Φl, hΦl⟩ : ∃ L : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2),
      ∀ y, L y = y + Fl y • ι w₀ :=
    ⟨LinearMap.id + Fl.smulRight (ι w₀), fun _ => rfl⟩
  have hΦΦ : ∀ y, Φl (Φl y) = y := by
    intro y
    have h2 : Fl (Φl y) = Fl y := by
      rw [hΦl, map_add, map_smul, hFv, smul_zero, add_zero]
    have h3 : ∀ c : ZMod 2, c + c = 0 := by decide
    rw [hΦl (Φl y), h2, hΦl y, add_assoc, ← add_smul, h3, zero_smul, add_zero]
  have hcomp : Φl.comp Φl = LinearMap.id := LinearMap.ext hΦΦ
  have hsq : LinearMap.toMatrix' Φl * LinearMap.toMatrix' Φl = 1 := by
    rw [← LinearMap.toMatrix'_comp, hcomp, LinearMap.toMatrix'_id]
  refine ⟨Units.mk (LinearMap.toMatrix' Φl) (LinearMap.toMatrix' Φl) hsq hsq, fun x => ?_⟩
  show (LinearMap.toMatrix' Φl).mulVec (ι x) = ι (x + f x • w₀)
  rw [LinearMap.toMatrix'_mulVec, hΦl, hFι x, map_add, nsbfc_map_smul ι]

theorem exists_submodule_finrank_three {n j : ℕ} (U : AddSubgroup (Fin n → ZMod 2))
    (hU : Nat.card U = 2 ^ j) (hj : 3 ≤ j) :
    ∃ A₁ : Submodule (ZMod 2) (Fin n → ZMod 2), Module.finrank (ZMod 2) A₁ = 3 ∧
      ∀ x ∈ A₁, x ∈ U := by
  have hV : Module.finrank (ZMod 2) (subgroupToSubmodule U) = j :=
    finrank_subgroupToSubmodule U hU
  let b : Module.Basis (Fin j) (ZMod 2) (subgroupToSubmodule U) :=
    Module.finBasisOfFinrankEq (ZMod 2) (subgroupToSubmodule U) hV
  obtain ⟨u, hu⟩ : ∃ u : Fin 3 → (Fin n → ZMod 2),
      ∀ i, u i = ((b (Fin.castLE hj i) : subgroupToSubmodule U) : Fin n → ZMod 2) :=
    ⟨fun i => ((b (Fin.castLE hj i) : subgroupToSubmodule U) : Fin n → ZMod 2), fun _ => rfl⟩
  have hli : LinearIndependent (ZMod 2) u := by
    have h1 : LinearIndependent (ZMod 2) (fun i : Fin 3 => b (Fin.castLE hj i)) :=
      b.linearIndependent.comp (fun i : Fin 3 => Fin.castLE hj i) (Fin.castLE_injective hj)
    have h2 := h1.map' (subgroupToSubmodule U).subtype (Submodule.ker_subtype _)
    have hfun : u = (subgroupToSubmodule U).subtype ∘ (fun i : Fin 3 => b (Fin.castLE hj i)) :=
      funext hu
    rw [hfun]
    exact h2
  refine ⟨Submodule.span (ZMod 2) (Set.range u), ?_, ?_⟩
  · rw [finrank_span_eq_card hli, Fintype.card_fin]
  · have hle : Submodule.span (ZMod 2) (Set.range u) ≤ subgroupToSubmodule U := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [hu i]
      exact (b (Fin.castLE hj i)).2
    intro x hx
    exact (mem_subgroupToSubmodule U x).mp (hle hx)

theorem exists_gl_map_std {n m : ℕ} (A₁ : Submodule (ZMod 2) (Fin n → ZMod 2))
    (h : Module.finrank (ZMod 2) A₁ = m) :
    ∃ κ : GL (Fin n) (ZMod 2), ∀ a : Fin n → ZMod 2, (∀ b : Fin n, m ≤ b.val → a b = 0) →
      (κ : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec a ∈ A₁ := by
  obtain ⟨P, hP⟩ := exists_gl_std_of_finrank A₁ h
  refine ⟨P⁻¹, fun a ha => ?_⟩
  have hPa : (P : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec
      (((P⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec a) = a := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  rw [hP]
  intro b hb
  rw [hPa]
  exact ha b hb

end CFSG.Quasithin.H13.Ch4.NSB
