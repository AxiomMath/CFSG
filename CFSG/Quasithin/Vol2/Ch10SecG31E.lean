module

public import CFSG.Quasithin.Vol2.Ch10SecG31D

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.G31

open Module CFSG.GroupTheory.GLnTwoSplitting

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

namespace Hyp

variable {G : Subgroup (W ≃ₗ[ZMod 2] W)} {Δ : Set W}
  {F : W → Submodule (ZMod 2) (Dual (ZMod 2) W)} [Finite W]

omit [Finite W] in
theorem exists_mem_apply_ne_zero (hspan : Submodule.span (ZMod 2) Δ = ⊤)
    {φ : Dual (ZMod 2) W} (hφ0 : φ ≠ 0) : ∃ y ∈ Δ, φ y ≠ 0 := by
  by_contra! h
  refine hφ0 (LinearMap.ext fun w => ?_)
  have hle : Submodule.span (ZMod 2) Δ ≤ LinearMap.ker φ := Submodule.span_le.2 fun z hz => h z hz
  rw [hspan] at hle
  exact hle Submodule.mem_top

omit [Finite W] in
theorem exists_mem_F_ne_zero (hrank : ∀ x ∈ Δ, 2 ≤ finrank (ZMod 2) (F x)) {x : W}
    (hx : x ∈ Δ) : ∃ φ ∈ F x, φ ≠ 0 := by
  refine Submodule.exists_mem_ne_zero_of_ne_bot fun h => ?_
  have := hrank x hx
  rw [h, finrank_bot] at this
  omega

theorem false_of_isMaxFull (hH : Hyp G Δ F) (hgen : G ≤ Subgroup.closure (gens Δ F))
    (hspan : Submodule.span (ZMod 2) Δ = ⊤) (hrank : ∀ x ∈ Δ, 2 ≤ finrank (ZMod 2) (F x))
    (hO2 : ∀ g ∈ G, (∀ w, ∀ h ∈ G, h (g w - w) = g w - w) → g = 1)
    {P : Submodule (ZMod 2) W} (hM : IsMaxFull Δ F P) (hPtop : P ≠ ⊤) : False := by
  obtain ⟨x₁, hx₁, h₁⟩ := hM.exists_ne
  have hx₁Δ := (hM.full x₁ hx₁ h₁).1
  have h3 : 3 ≤ finrank (ZMod 2) P := by
    have := hH.finrank_F_add_one hM hx₁ h₁
    have := hrank x₁ hx₁Δ
    omega
  obtain ⟨x₂, hx₂, hx₂S⟩ := exists_mem_notMem_of_finrank_lt (U := P)
    (S := Submodule.span (ZMod 2) {x₁}) (by rw [finrank_span_singleton h₁]; omega)
  have h₂ : x₂ ≠ 0 := fun h => hx₂S (h ▸ Submodule.zero_mem _)
  have h₁₂ : x₁ ≠ x₂ := fun h => hx₂S (h ▸ Submodule.mem_span_singleton_self _)
  have hDC : ∀ z ∈ Δ, z ∉ C F x₁ ⊓ C F x₂ → C F x₁ ⊓ C F x₂ ≤ C F z := by
    intro z hz hzD
    by_cases hzP : z ∈ P
    · exact hH.D_le_C hM hx₁ hx₂ h₁ h₂ h₁₂ hzP (hH.ne_zero z hz)
    by_cases hadj : ∃ x ∈ P, x ≠ 0 ∧ z ∉ C F x
    · obtain ⟨x, hx, hx0, hzx⟩ := hadj
      obtain ⟨-, -, -, -, -, -, -, hD, -⟩ :=
        hH.outer hM hx₁ hx₂ h₁ h₂ h₁₂ h3 hz hzP hx hx0 hzx
      exact hD
    · push Not at hadj
      exact absurd ⟨hadj x₁ hx₁ h₁, hadj x₂ hx₂ h₂⟩ hzD
  have hx₁D : x₁ ∉ C F x₁ ⊓ C F x₂ := fun h =>
    not_mem_C_of_isFull hM.full hx₂ hx₁ h₂ h₁ (Ne.symm h₁₂) h.2
  have hall : ∀ z ∈ Δ, C F x₁ ⊓ C F x₂ ≤ C F z := by
    intro z hz
    have hS := hH.forall_mem_of_closed hgen (S := {z | z ∈ Δ ∧ z ∉ C F x₁ ⊓ C F x₂})
      (fun z hz => hz.1) ⟨x₁, hx₁Δ, hx₁D⟩
      (fun u hu v hv hvu => ⟨hv, fun hvD => hvu (hDC u hu.1 hu.2 hvD)⟩) hz
    exact hDC z hz hS.2
  have hfix : ∀ g ∈ Subgroup.closure (gens Δ F), ∀ d ∈ C F x₁ ⊓ C F x₂, g d = d := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem t ht =>
      obtain ⟨z, hz, ψ, hψ, h, rfl⟩ := ht
      intro d hd
      rw [transvection_apply, mem_C.1 (hall z hz hd) ψ hψ, zero_smul, add_zero]
    | one => exact fun d _ => rfl
    | mul a b _ _ ha hb =>
      intro d hd
      rw [LinearEquiv.mul_apply, hb d hd, ha d hd]
    | inv a _ ha =>
      intro d hd
      show a.symm d = d
      rw [LinearEquiv.symm_apply_eq, ha d hd]
  have hex : ∃ y ∈ Δ, y ∉ P ∧ ∃ x ∈ P, x ≠ 0 ∧ y ∉ C F x := by
    by_contra hne
    push Not at hne
    refine hPtop (eq_top_iff.2 ?_)
    rw [← hspan, Submodule.span_le]
    intro z hz
    exact (hH.forall_mem_of_closed hgen (S := {z | z ∈ Δ ∧ z ∈ P}) (fun z hz => hz.1)
      ⟨x₁, hx₁Δ, hx₁⟩ (fun u hu v hv hvu => ⟨hv, by_contra fun hvP =>
        hvu (hne v hv hvP u hu.2 (hH.ne_zero u hu.1))⟩) hz).2
  obtain ⟨y, hy, hyP, x, hx, hx0, hyx⟩ := hex
  obtain ⟨p₀, hp₀, d₀, hd₀, hyeq, hp0, hd0, -, hFeq⟩ :=
    hH.outer hM hx₁ hx₂ h₁ h₂ h₁₂ h3 hy hyP hx hx0 hyx
  have hp₀Δ := (hM.full p₀ hp₀ hp0).1
  obtain ⟨φ, hφ, hφ0⟩ := exists_mem_F_ne_zero hrank hp₀Δ
  have hφp₀ : φ p₀ = 0 := hH.apply_self p₀ hp₀Δ φ hφ
  have hφy : φ y = 0 := hH.apply_self y hy φ (hFeq ▸ hφ)
  have hφd₀ : φ d₀ = 0 := by
    rw [hyeq, map_add, hφp₀, zero_add] at hφy
    exact hφy
  have hmem : LinearEquiv.transvection hφd₀ ∈ G := by
    have := G.mul_mem (hH.mem y hy φ (hFeq ▸ hφ) hφy) (hH.mem p₀ hp₀Δ φ hφ hφp₀)
    rwa [transvection_mul_transvection_left hφy hφp₀ (by rw [map_add, hφy, hφp₀, add_zero]),
      transvection_congr rfl (by rw [hyeq, add_comm p₀, add_assoc, two_add_self, add_zero]) _
        hφd₀] at this
  have h1 := hO2 _ hmem fun w h hh => by
    rw [transvection_apply, add_sub_cancel_left, map_smul, hfix h (hgen hh) d₀ hd₀]
  obtain ⟨w, hw⟩ : ∃ w, φ w ≠ 0 := by
    by_contra! h
    exact hφ0 (LinearMap.ext h)
  have h2 := congrArg (fun g : W ≃ₗ[ZMod 2] W => g w) h1
  change w + φ w • d₀ = w at h2
  rw [add_eq_left, zmod_two_eq_one_of_ne_zero hw, one_smul] at h2
  exact hd0 h2

theorem isFull_top (hH : Hyp G Δ F) (hgen : G ≤ Subgroup.closure (gens Δ F))
    (hspan : Submodule.span (ZMod 2) Δ = ⊤) (hrank : ∀ x ∈ Δ, 2 ≤ finrank (ZMod 2) (F x))
    (hO2 : ∀ g ∈ G, (∀ w, ∀ h ∈ G, h (g w - w) = g w - w) → g = 1) : IsFull Δ F ⊤ := by
  by_cases hΔ : Δ.Nonempty
  swap
  · intro v _ hv0
    refine absurd ?_ hv0
    have hv : v ∈ Submodule.span (ZMod 2) Δ := hspan ▸ Submodule.mem_top
    rwa [Set.not_nonempty_iff_eq_empty.1 hΔ, Submodule.span_empty, Submodule.mem_bot] at hv
  obtain ⟨x, hx⟩ := hΔ
  obtain ⟨φ, hφ, hφ0⟩ := exists_mem_F_ne_zero hrank hx
  obtain ⟨y, hy, hφy⟩ := exists_mem_apply_ne_zero hspan hφ0
  have hP₀ := hH.isFull_span_pair hx hy fun h => hφy (mem_C.1 h φ hφ)
  suffices key : ∀ n, ∀ P : Submodule (ZMod 2) W, IsFull Δ F P → (∃ v ∈ P, v ≠ 0) →
      finrank (ZMod 2) W - finrank (ZMod 2) P = n → IsFull Δ F ⊤ from
    key _ _ hP₀ ⟨x, Submodule.subset_span (Set.mem_insert _ _), hH.ne_zero x hx⟩ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro P hP hne hn
    by_cases hPtop : P = ⊤
    · rw [← hPtop]
      exact hP
    by_cases hfa : ∀ x ∈ P, x ≠ 0 → ∀ φ ∈ F x, (∀ u ∈ P, φ u = 0) → φ = 0
    · exact (hH.false_of_isMaxFull hgen hspan hrank hO2 ⟨hP, hne, hfa⟩ hPtop).elim
    push Not at hfa
    obtain ⟨x, hxP, hx0, φ, hφ, hφP, hφ0⟩ := hfa
    obtain ⟨y, hy, hφy⟩ := exists_mem_apply_ne_zero hspan hφ0
    have hyP : y ∉ P := fun h => hφy (hφP y h)
    have hP' := hH.isFull_sup hP hxP hx0 hφ hφP hy (zmod_two_eq_one_of_ne_zero hφy)
    have hlt : finrank (ZMod 2) P < finrank (ZMod 2) ↥(P ⊔ Submodule.span (ZMod 2) {y}) :=
      Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne le_sup_left fun h => hyP (by
        rw [h]
        exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self y)))
    have hle := Submodule.finrank_le (P ⊔ Submodule.span (ZMod 2) {y})
    exact ih _ (by omega) _ hP' ⟨x, Submodule.mem_sup_left hxP, hx0⟩ rfl

theorem core (hH : Hyp G Δ F) (hgen : G ≤ Subgroup.closure (gens Δ F))
    (hspan : Submodule.span (ZMod 2) Δ = ⊤) (hrank : ∀ x ∈ Δ, 2 ≤ finrank (ZMod 2) (F x))
    (hO2 : ∀ g ∈ G, (∀ w, ∀ h ∈ G, h (g w - w) = g w - w) → g = 1) :
    (∀ v : W, v ≠ 0 → v ∈ Δ) ∧
      (∀ x ∈ Δ, F x = (Submodule.span (ZMod 2) {x}).dualAnnihilator) ∧ G = ⊤ := by
  have hT := hH.isFull_top hgen hspan hrank hO2
  have hΔ : ∀ v : W, v ≠ 0 → v ∈ Δ := fun v hv => (hT v Submodule.mem_top hv).1
  have hF : ∀ x ∈ Δ, F x = (Submodule.span (ZMod 2) {x}).dualAnnihilator := by
    intro x hx
    have hC : C F x = Submodule.span (ZMod 2) {x} := by
      have := (hT x Submodule.mem_top (hH.ne_zero x hx)).2
      rwa [inf_top_eq] at this
    rw [← hC, Subspace.dualCoannihilator_dualAnnihilator_eq]
  refine ⟨hΔ, hF, G11.eq_top_of_forall_transvection_mem G fun β a hβa => ?_⟩
  by_cases ha : a = 0
  · rw [transvection_congr rfl ha hβa (by rw [map_zero]), transvection_eq_one]
    exact G.one_mem
  have haΔ := hΔ a ha
  refine hH.mem a haΔ β ?_ hβa
  rw [hF a haΔ, Submodule.mem_dualAnnihilator]
  intro w hw
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
  rw [map_smul, hβa, smul_zero]

end Hyp

end CFSG.Quasithin.G31
