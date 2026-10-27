module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K322Ext

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6.K323E

open Matrix Subgroup CFSG.RepresentationTheory

variable {p : ℕ} [Fact p.Prime]

theorem center_scalar {H : Subgroup (GL (Fin 3) (ZMod p))}
    (hirr : IsIrreducibleMatrixRep H.subtype) (hZ : Nat.card (center H) = 3) (h31 : p % 3 = 1) :
    ∀ w : H, w ∈ center H → ∃ c : ZMod p,
      ((w : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) =
        algebraMap (ZMod p) (Matrix (Fin 3) (Fin 3) (ZMod p)) c := by
  intro w hw
  have hω : ∃ ω : ZMod p, ω ^ 3 = 1 ∧ ω ≠ 1 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hdvd : 3 ∣ Nat.card (ZMod p)ˣ := by
      rw [Nat.card_eq_fintype_card, ZMod.card_units]
      omega
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
    refine ⟨(u : ZMod p), ?_, ?_⟩
    · rw [← Units.val_pow_eq_pow_val, ← hu, pow_orderOf_eq_one, Units.val_one]
    · intro h
      have : u = 1 := Units.ext h
      rw [this, orderOf_one] at hu
      norm_num at hu
  obtain ⟨ω, hω3, hω1⟩ := hω
  have hz3 : (w : GL (Fin 3) (ZMod p)) ^ 3 = 1 := by
    have h1 : (⟨w, hw⟩ : ↥(center H)) ^ Nat.card ↥(center H) = 1 := pow_card_eq_one'
    rw [hZ] at h1
    have h2 : w ^ 3 = 1 := by
      have := congrArg Subtype.val h1
      rwa [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this
    have := congrArg Subtype.val h2
    rwa [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this
  have hcomm : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) (ZMod p)) * (w : GL (Fin 3) (ZMod p)) =
      ((w : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) * x := by
    intro x hx
    have h := Subgroup.mem_center_iff.1 hw ⟨x, hx⟩
    have h2 := congrArg (fun w : ↥H => ((w : GL (Fin 3) (ZMod p)) :
      Matrix (Fin 3) (Fin 3) (ZMod p))) h
    simpa only [Subgroup.coe_mul, Units.val_mul] using h2
  exact K322Ext.eq_scalar_of_commute_of_pow_three hirr (by norm_num) hω3 hω1 hcomm hz3

theorem exists_moves_line {H : Subgroup (GL (Fin 3) (ZMod p))}
    (hirr : IsIrreducibleMatrixRep H.subtype) {z : Fin 3 → ZMod p} (hz0 : z ≠ 0) :
    ∃ h ∈ H, ∀ c : ZMod p, (h : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ z ≠ c • z := by
  by_contra hcon
  push Not at hcon
  have hinv : ∀ g : H, ∀ w ∈ Submodule.span (ZMod p) {z},
      ((g : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ w ∈
        Submodule.span (ZMod p) {z} := by
    intro g w hw
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw
    obtain ⟨c, hc⟩ := hcon g g.2
    rw [Matrix.mulVec_smul, hc, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self z)
  rcases hirr _ hinv with h | h
  · have : z ∈ Submodule.span (ZMod p) {z} := Submodule.mem_span_singleton_self z
    rw [h] at this
    exact hz0 ((Submodule.mem_bot _).1 this)
  · exfalso
    have he0 : (Pi.single 0 1 : Fin 3 → ZMod p) ∈ Submodule.span (ZMod p) {z} :=
      h ▸ Submodule.mem_top
    have he1 : (Pi.single 1 1 : Fin 3 → ZMod p) ∈ Submodule.span (ZMod p) {z} :=
      h ▸ Submodule.mem_top
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 he0
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.1 he1
    have h1 := congrFun ha 1
    have h2 := congrFun hb 1
    have h3 := congrFun ha 0
    simp at h1 h2 h3
    rcases h1 with h1 | h1
    · rw [h1] at h3
      simp at h3
    · rw [h1] at h2
      simp at h2

theorem false_of_extraspecial27 {G H X : Subgroup (GL (Fin 3) (ZMod p))} (hp5 : 5 ≤ p)
    (hXG : X ≤ G) (hnorm : ∀ g ∈ G, ∀ h ∈ H, g * h * g⁻¹ ∈ H)
    (hirr : IsIrreducibleMatrixRep H.subtype) (h27 : Nat.card H = 27)
    (hex : CFSG.IsExtraspecialPGroup 3 ↥H) (h31 : p % 3 = 1) {z : Fin 3 → ZMod p} (hz0 : z ≠ 0)
    (hXz : ∀ y ∈ X, (y : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ z = z)
    (hXab : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a)
    (hfr : ∀ y ∈ X, y ≠ 1 → ∀ v : Fin 3 → ZMod p,
      (y : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ v = v → ∃ c : ZMod p, v = c • z)
    (hXcard : Nat.card X = (p ^ 2 - 1) / 2) : False := by
  classical
  have hZc : Nat.card (center H) = 3 := hex.2.2.2
  have hsc := center_scalar hirr hZc h31
  have hcent : ∀ (x : GL (Fin 3) (ZMod p)) (w : H), w ∈ center H →
      x * (w : GL (Fin 3) (ZMod p)) = (w : GL (Fin 3) (ZMod p)) * x := by
    intro x w hw
    obtain ⟨c, hc⟩ := hsc w hw
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hc]
    exact (Algebra.commutes c _).symm
  obtain ⟨h₀, hh₀, hmove⟩ := exists_moves_line hirr hz0
  have hnc₀ : (⟨h₀, hh₀⟩ : H) ∉ center H := by
    intro hw
    obtain ⟨c, hc⟩ := hsc _ hw
    apply hmove c
    have : (h₀ : Matrix (Fin 3) (Fin 3) (ZMod p)) = algebraMap (ZMod p) _ c := hc
    rw [this]
    ext i
    simp [Matrix.algebraMap_eq_diagonal, Matrix.mulVec_diagonal]
  have hCX : ∀ y ∈ X, y * h₀ = h₀ * y → y = 1 := by
    intro y hy hcomm
    by_contra hy1
    obtain ⟨c, hc⟩ := hfr y hy hy1 ((h₀ : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ z) (by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, hcomm, Units.val_mul, ← Matrix.mulVec_mulVec,
        hXz y hy])
    exact hmove c hc
  let β : X → H := fun x => ⟨(x : GL (Fin 3) (ZMod p)) * h₀ * (x : GL (Fin 3) (ZMod p))⁻¹,
    hnorm x (hXG x.2) h₀ hh₀⟩
  have hβS : ∀ x, β x ∉ center H := by
    intro x hx
    apply hnc₀
    have h1 := hcent (x : GL (Fin 3) (ZMod p))⁻¹ (β x) hx
    have h2 : (x : GL (Fin 3) (ZMod p))⁻¹ * ((x : GL (Fin 3) (ZMod p)) * h₀ *
        (x : GL (Fin 3) (ZMod p))⁻¹) = h₀ * (x : GL (Fin 3) (ZMod p))⁻¹ := by group
    have h3 : (β x : GL (Fin 3) (ZMod p)) * (x : GL (Fin 3) (ZMod p))⁻¹ =
        (x : GL (Fin 3) (ZMod p))⁻¹ * (β x : GL (Fin 3) (ZMod p)) := h1.symm
    have h4 : h₀ = (β x : GL (Fin 3) (ZMod p)) := by
      have h5 : (x : GL (Fin 3) (ZMod p))⁻¹ * (β x : GL (Fin 3) (ZMod p)) =
          h₀ * (x : GL (Fin 3) (ZMod p))⁻¹ := h2
      have h6 : h₀ * (x : GL (Fin 3) (ZMod p))⁻¹ = (β x : GL (Fin 3) (ZMod p)) *
          (x : GL (Fin 3) (ZMod p))⁻¹ := by rw [← h5, h3]
      exact mul_right_cancel h6
    have h7 : (⟨h₀, hh₀⟩ : H) = β x := Subtype.ext h4
    rw [h7]
    exact hx
  let S : Set H := (center H : Set H)ᶜ
  let β' : X → S := fun x => ⟨β x, hβS x⟩
  have hβ'inj : Function.Injective β' := by
    intro a b hab
    have h1 : (a : GL (Fin 3) (ZMod p)) * h₀ * (a : GL (Fin 3) (ZMod p))⁻¹ =
        (b : GL (Fin 3) (ZMod p)) * h₀ * (b : GL (Fin 3) (ZMod p))⁻¹ :=
      congrArg (fun t : S => ((t : H) : GL (Fin 3) (ZMod p))) hab
    have hy : (a : GL (Fin 3) (ZMod p))⁻¹ * b ∈ X := X.mul_mem (X.inv_mem a.2) b.2
    have hc : (a : GL (Fin 3) (ZMod p))⁻¹ * b * h₀ = h₀ * ((a : GL (Fin 3) (ZMod p))⁻¹ * b) := by
      calc (a : GL (Fin 3) (ZMod p))⁻¹ * b * h₀ = (a : GL (Fin 3) (ZMod p))⁻¹ *
            ((b : GL (Fin 3) (ZMod p)) * h₀ * (b : GL (Fin 3) (ZMod p))⁻¹) * b := by group
        _ = (a : GL (Fin 3) (ZMod p))⁻¹ * ((a : GL (Fin 3) (ZMod p)) * h₀ *
            (a : GL (Fin 3) (ZMod p))⁻¹) * b := by rw [h1]
        _ = h₀ * ((a : GL (Fin 3) (ZMod p))⁻¹ * b) := by group
    exact Subtype.ext (inv_mul_eq_one.1 (hCX _ hy hc))
  have hSc : Nat.card S = 24 := by
    have h1 : Nat.card S = ((center H : Set H)ᶜ).ncard := Nat.card_coe_set_eq _
    have h2 : (center H : Set H).ncard = 3 := by
      rw [← Nat.card_coe_set_eq]
      exact hZc
    rw [h1, Set.ncard_compl, h2, h27]
  have hle : Nat.card X ≤ 24 := hSc ▸ Nat.card_le_card_of_injective β' hβ'inj
  rw [hXcard] at hle
  have hp7 : p = 7 := by
    have h1 : p ^ 2 ≤ 50 := by omega
    have h2 : p ≤ 7 := by nlinarith
    omega
  subst hp7
  have hbij := hβ'inj.bijective_of_nat_card_le (by rw [hSc, hXcard]; norm_num)
  have hsurj : ∀ s : H, s ∉ center H → ∃ x ∈ X,
      (x : GL (Fin 3) (ZMod 7)) * h₀ * (x : GL (Fin 3) (ZMod 7))⁻¹ = (s : GL (Fin 3) (ZMod 7)) := by
    intro s hs
    obtain ⟨⟨x, hxX⟩, hx⟩ := hbij.2 ⟨s, hs⟩
    exact ⟨x, hxX, congrArg (fun t : S => ((t : H) : GL (Fin 3) (ZMod 7))) hx⟩
  haveI : Nontrivial (center H) := Finite.one_lt_card_iff_nontrivial.1 (by rw [hZc]; norm_num)
  obtain ⟨c₀, hc₀1⟩ : ∃ c₀ : center H, c₀ ≠ 1 := exists_ne 1
  set cH : H := (c₀ : H) with hcH
  set c : GL (Fin 3) (ZMod 7) := (cH : GL (Fin 3) (ZMod 7)) with hc
  have hcmem : cH ∈ center H := c₀.2
  have hcc : ∀ x : GL (Fin 3) (ZMod 7), x * c = c * x := fun x => hcent x cH hcmem
  set y₀ : H := ⟨h₀, hh₀⟩ with hy₀
  have hs₁ : y₀ * cH ∉ center H := by
    intro hs
    apply hnc₀
    have : y₀ = (y₀ * cH) * cH⁻¹ := by group
    show y₀ ∈ center H
    rw [this]
    exact Subgroup.mul_mem _ hs (Subgroup.inv_mem _ hcmem)
  have hs₂ : y₀ * y₀ ∉ center H := by
    intro hs
    apply hnc₀
    have h3 := K322Ext.pow_three_mem_center h27 hex y₀
    have : y₀ = y₀ ^ 3 * (y₀ * y₀)⁻¹ := by group
    show y₀ ∈ center H
    rw [this]
    exact Subgroup.mul_mem _ h3 (Subgroup.inv_mem _ hs)
  obtain ⟨x₁, hx₁X, hx₁⟩ := hsurj _ hs₁
  obtain ⟨x₂, hx₂X, hx₂⟩ := hsurj _ hs₂
  have hx₁' : (x₁ : GL (Fin 3) (ZMod 7)) * h₀ * (x₁ : GL (Fin 3) (ZMod 7))⁻¹ = h₀ * c := hx₁
  have hx₂' : (x₂ : GL (Fin 3) (ZMod 7)) * h₀ * (x₂ : GL (Fin 3) (ZMod 7))⁻¹ = h₀ * h₀ := hx₂
  have hx12 : (x₁ : GL (Fin 3) (ZMod 7)) * x₂ = x₂ * x₁ := hXab x₁ hx₁X x₂ hx₂X
  have e1 : (x₁ : GL (Fin 3) (ZMod 7)) * (h₀ * h₀) * (x₁ : GL (Fin 3) (ZMod 7))⁻¹ =
      h₀ * h₀ * c * c := by
    calc (x₁ : GL (Fin 3) (ZMod 7)) * (h₀ * h₀) * (x₁ : GL (Fin 3) (ZMod 7))⁻¹
        = ((x₁ : GL (Fin 3) (ZMod 7)) * h₀ * (x₁ : GL (Fin 3) (ZMod 7))⁻¹) *
          ((x₁ : GL (Fin 3) (ZMod 7)) * h₀ * (x₁ : GL (Fin 3) (ZMod 7))⁻¹) := by group
      _ = (h₀ * c) * (h₀ * c) := by rw [hx₁']
      _ = h₀ * (c * h₀) * c := by group
      _ = h₀ * (h₀ * c) * c := by rw [hcc h₀]
      _ = h₀ * h₀ * c * c := by group
  have e2 : (x₁ : GL (Fin 3) (ZMod 7)) * (h₀ * h₀) * (x₁ : GL (Fin 3) (ZMod 7))⁻¹ =
      h₀ * h₀ * c := by
    calc (x₁ : GL (Fin 3) (ZMod 7)) * (h₀ * h₀) * (x₁ : GL (Fin 3) (ZMod 7))⁻¹
        = (x₁ : GL (Fin 3) (ZMod 7)) * ((x₂ : GL (Fin 3) (ZMod 7)) * h₀ *
          (x₂ : GL (Fin 3) (ZMod 7))⁻¹) * (x₁ : GL (Fin 3) (ZMod 7))⁻¹ := by rw [hx₂']
      _ = ((x₁ : GL (Fin 3) (ZMod 7)) * x₂) * h₀ * ((x₁ : GL (Fin 3) (ZMod 7)) * x₂)⁻¹ := by
          group
      _ = ((x₂ : GL (Fin 3) (ZMod 7)) * x₁) * h₀ * ((x₂ : GL (Fin 3) (ZMod 7)) * x₁)⁻¹ := by
          rw [hx12]
      _ = (x₂ : GL (Fin 3) (ZMod 7)) * ((x₁ : GL (Fin 3) (ZMod 7)) * h₀ *
          (x₁ : GL (Fin 3) (ZMod 7))⁻¹) * (x₂ : GL (Fin 3) (ZMod 7))⁻¹ := by group
      _ = (x₂ : GL (Fin 3) (ZMod 7)) * (h₀ * c) * (x₂ : GL (Fin 3) (ZMod 7))⁻¹ := by rw [hx₁']
      _ = (x₂ : GL (Fin 3) (ZMod 7)) * h₀ * (c * (x₂ : GL (Fin 3) (ZMod 7))⁻¹) := by group
      _ = (x₂ : GL (Fin 3) (ZMod 7)) * h₀ * ((x₂ : GL (Fin 3) (ZMod 7))⁻¹ * c) := by
          rw [hcc (x₂ : GL (Fin 3) (ZMod 7))⁻¹]
      _ = ((x₂ : GL (Fin 3) (ZMod 7)) * h₀ * (x₂ : GL (Fin 3) (ZMod 7))⁻¹) * c := by group
      _ = h₀ * h₀ * c := by rw [hx₂']
  have hc1 : c = 1 := by
    have h1 : (h₀ * h₀ * c) * c = (h₀ * h₀ * c) * 1 := by
      rw [mul_one]
      exact e1.symm.trans e2
    exact mul_left_cancel h1
  exact hc₀1 (Subtype.ext (Subtype.ext hc1))

end CFSG.LocalAnalysis.UniquenessCase.UC6.K323E
