module

public import Mathlib.FieldTheory.Finiteness
public import Mathlib.GroupTheory.PGroup
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

public section

namespace CFSG.RankThree.GF2n.Stroth80

section

theorem sec7_subquotient_rep {K H E : Type*} [Field K] [AddCommGroup E] [Module K E] [Group H]
    (T : H →* Module.End K E) (P U : Submodule K E)
    (hP : ∀ h, ∀ p ∈ P, T h p ∈ P) (hU : ∀ h, ∀ p ∈ U, T h p ∈ U) :
    ∃ ρ : H →* Module.End K (↥P ⧸ U.submoduleOf P),
      ∀ h (p : ↥P), ρ h (Submodule.Quotient.mk p) = Submodule.Quotient.mk ⟨T h p, hP h p p.2⟩ := by
  have hle : ∀ h, U.submoduleOf P ≤ (U.submoduleOf P).comap ((T h).restrict (hP h)) := by
    intro h x hx
    rw [Submodule.mem_comap]
    exact hU h x.1 hx
  let f : H → Module.End K (↥P ⧸ U.submoduleOf P) := fun h =>
    Submodule.mapQ (U.submoduleOf P) (U.submoduleOf P) ((T h).restrict (hP h)) (hle h)
  have hf : ∀ h (p : ↥P), f h (Submodule.Quotient.mk p) =
      Submodule.Quotient.mk ⟨T h p, hP h p p.2⟩ := fun _ _ => rfl
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_ }, fun h p => hf h p⟩
  · refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (U.submoduleOf P) y
    rw [hf, Module.End.one_apply]
    congr 1
    exact Subtype.ext (by simp)
  · intro h h'
    refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (U.submoduleOf P) y
    rw [Module.End.mul_apply, hf, hf, hf]
    congr 1
    exact Subtype.ext (by simp [map_mul])

end

section

theorem sec7_subquotient_irred {K H E : Type*} [Field K] [AddCommGroup E] [Module K E] [Group H]
    (T : H →* Module.End K E) (P U : Submodule K E) (hUP : U ≤ P)
    (hP : ∀ h, ∀ p ∈ P, T h p ∈ P)
    (ρ : H →* Module.End K (↥P ⧸ U.submoduleOf P))
    (hρ : ∀ h (p : ↥P), ρ h (Submodule.Quotient.mk p) = Submodule.Quotient.mk ⟨T h p, hP h p p.2⟩)
    (hirr : ∀ A : AddSubgroup E, A ≤ P.toAddSubgroup → U.toAddSubgroup ≤ A →
      (∀ h, ∀ a ∈ A, T h a ∈ A) → A = U.toAddSubgroup ∨ A = P.toAddSubgroup)
    (A' : AddSubgroup (↥P ⧸ U.submoduleOf P)) (hA' : ∀ h y, y ∈ A' → ρ h y ∈ A') :
    A' = ⊥ ∨ A' = ⊤ := by
  obtain ⟨A, hA⟩ : ∃ A : AddSubgroup E, ∀ e, e ∈ A ↔
      ∃ p : ↥P, (p : E) = e ∧ (Submodule.Quotient.mk p : ↥P ⧸ U.submoduleOf P) ∈ A' := by
    refine ⟨{ carrier := {e | ∃ p : ↥P, (p : E) = e ∧
                (Submodule.Quotient.mk p : ↥P ⧸ U.submoduleOf P) ∈ A'}
              add_mem' := ?_
              zero_mem' := ?_
              neg_mem' := ?_ }, fun e => Iff.rfl⟩
    · rintro _ _ ⟨p, rfl, hp⟩ ⟨q, rfl, hq⟩
      exact ⟨p + q, rfl, by rw [Submodule.Quotient.mk_add]; exact A'.add_mem hp hq⟩
    · exact ⟨0, rfl, by rw [Submodule.Quotient.mk_zero]; exact A'.zero_mem⟩
    · rintro _ ⟨p, rfl, hp⟩
      exact ⟨-p, rfl, by rw [Submodule.Quotient.mk_neg]; exact A'.neg_mem hp⟩
  have hAP : A ≤ P.toAddSubgroup := by
    intro e he
    obtain ⟨p, rfl, -⟩ := (hA e).1 he
    exact p.2
  have hUA : U.toAddSubgroup ≤ A := by
    intro u hu
    have hu' : u ∈ U := hu
    have h0 : (Submodule.Quotient.mk (⟨u, hUP hu'⟩ : ↥P) : ↥P ⧸ U.submoduleOf P) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 hu'
    refine (hA u).2 ⟨⟨u, hUP hu'⟩, rfl, ?_⟩
    rw [h0]
    exact A'.zero_mem
  have hinv : ∀ h : H, ∀ a ∈ A, T h a ∈ A := by
    intro h e he
    obtain ⟨p, rfl, hp⟩ := (hA e).1 he
    refine (hA (T h p)).2 ⟨⟨T h p, hP h p p.2⟩, rfl, ?_⟩
    have hmem := hA' h _ hp
    rw [hρ h p] at hmem
    exact hmem
  rcases hirr A hAP hUA hinv with hAU | hAP'
  · left
    rw [AddSubgroup.eq_bot_iff_forall]
    intro y hy
    obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have hpA : (p : E) ∈ A := (hA _).2 ⟨p, rfl, hy⟩
    rw [hAU] at hpA
    have hpU : (p : E) ∈ U := hpA
    exact (Submodule.Quotient.mk_eq_zero _).2 hpU
  · right
    rw [AddSubgroup.eq_top_iff']
    intro y
    obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have hpA : (p : E) ∈ A := by
      rw [hAP']
      exact p.2
    obtain ⟨q, hq, hqA⟩ := (hA _).1 hpA
    obtain rfl : q = p := Subtype.ext hq
    exact hqA

end

section

theorem sec7_nontrivial_of_irred {K Y Γ : Type*} [Field K] [CharP K 2] [AddCommGroup Y]
    [Module K Y] [Group Γ] (ρ : Γ →* Module.End K Y)
    (hirr : ∀ A : AddSubgroup Y, (∀ g y, y ∈ A → ρ g y ∈ A) → A = ⊥ ∨ A = ⊤)
    (hbig : 2 < Nat.card Y) : ∃ g y, ρ g y ≠ y := by
  by_contra h
  push Not at h
  have hnt : Nontrivial Y := by
    have hfin : Finite Y := Nat.finite_of_card_ne_zero (by omega)
    exact Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨y₀, hy₀⟩ := exists_ne (0 : Y)
  have h2 : (2 : ℕ) • y₀ = 0 := by
    rw [← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero, zero_smul]
  have hord : addOrderOf y₀ ≤ 2 :=
    Nat.le_of_dvd (by decide) (addOrderOf_dvd_of_nsmul_eq_zero h2)
  have hinv : ∀ g y, y ∈ AddSubgroup.zmultiples y₀ → ρ g y ∈ AddSubgroup.zmultiples y₀ := by
    intro g y hy
    rw [h g y]
    exact hy
  rcases hirr (AddSubgroup.zmultiples y₀) hinv with hbot | htop
  · have hmem : y₀ ∈ AddSubgroup.zmultiples y₀ := AddSubgroup.mem_zmultiples y₀
    rw [hbot, AddSubgroup.mem_bot] at hmem
    exact hy₀ hmem
  · have hcard : Nat.card Y = Nat.card (AddSubgroup.zmultiples y₀) := by
      rw [htop, AddSubgroup.card_top]
    rw [Nat.card_zmultiples] at hcard
    omega

end

section

theorem sec7_exists_fixed_of_two_group {K Y Γ : Type*} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup Y] [Module K Y] [Module.Finite K Y] [Group Γ] (ρ : Γ →* Module.End K Y)
    (L : Subgroup Γ) (hL : IsPGroup 2 L) (D : Submodule K Y) (hD : D ≠ ⊥)
    (hDL : ∀ l ∈ L, ∀ y ∈ D, ρ l y ∈ D) :
    ∃ y ∈ D, y ≠ 0 ∧ ∀ l ∈ L, ρ l y = y := by
  have hNz : ∃ w : Y, w ∈ D ∧ w ≠ 0 ∧ ∀ l : L, ρ (l : Γ) w = w := by
    have hDnt : Nontrivial D := Submodule.nontrivial_iff_ne_bot.2 hD
    have hfinD : Finite D := Module.finite_of_finite (R := K)
    have hcardD : 1 < Nat.card D := Finite.one_lt_card_iff_nontrivial.2 hDnt
    have h2K : 2 ∣ Nat.card K := by
      have h1 : addOrderOf (1 : K) = 2 := CharP.eq K (CharP.addOrderOf_one K) inferInstance
      have h2 := addOrderOf_dvd_natCard (1 : K)
      rwa [h1] at h2
    have hd : Module.finrank K D ≠ 0 := by
      intro h0
      have h1 := Module.natCard_eq_pow_finrank (K := K) (V := D)
      rw [h0, pow_zero] at h1
      omega
    have hDeven : Nat.card D ≡ 0 [MOD 2] := by
      apply Nat.modEq_zero_iff_dvd.2
      rw [Module.natCard_eq_pow_finrank (K := K) (V := D)]
      exact dvd_pow h2K hd
    letI : MulAction (↥L) (↥D) :=
      { smul := fun l w => ⟨ρ (l : Γ) (w : Y), hDL _ l.2 _ w.2⟩
        one_smul := fun w => Subtype.ext (by
          show ρ ((1 : L) : Γ) (w : Y) = (w : Y)
          simp)
        mul_smul := fun l m w => Subtype.ext (by
          show ρ ((l * m : L) : Γ) (w : Y) = ρ (l : Γ) (ρ (m : Γ) (w : Y))
          simp [map_mul, Module.End.mul_apply]) }
    have hfixmem : ∀ w : D, w ∈ MulAction.fixedPoints (↥L) (↥D) ↔
        ∀ l : L, ρ (l : Γ) (w : Y) = (w : Y) := by
      intro w
      rw [MulAction.mem_fixedPoints]
      exact ⟨fun h l => congrArg Subtype.val (h l), fun h l => Subtype.ext (h l)⟩
    have hzero_fix : (0 : D) ∈ MulAction.fixedPoints (↥L) (↥D) := by
      rw [hfixmem]
      intro l
      rw [Submodule.coe_zero]
      exact map_zero _
    have hcong := hL.card_modEq_card_fixedPoints D
    have hfixed : Nat.card (MulAction.fixedPoints (↥L) (↥D)) ≡ 0 [MOD 2] :=
      hcong.symm.trans hDeven
    by_contra hcon
    have hcon' : ∀ w : D, (∀ l : L, ρ (l : Γ) (w : Y) = (w : Y)) → w = 0 := by
      intro w hw
      by_contra hne
      exact hcon ⟨w.1, w.2, fun h => hne (Submodule.coe_eq_zero.mp h), hw⟩
    have hone : Nat.card (MulAction.fixedPoints (↥L) (↥D)) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun a b => Subtype.ext ?_⟩, ⟨⟨0, hzero_fix⟩⟩⟩
      rw [hcon' a.1 ((hfixmem a.1).1 a.2), hcon' b.1 ((hfixmem b.1).1 b.2)]
    rw [hone] at hfixed
    exact absurd hfixed (by decide)
  obtain ⟨w₀, hw₀D, hw₀ne, hw₀fix⟩ := hNz
  exact ⟨w₀, hw₀D, hw₀ne, fun l hl => hw₀fix ⟨l, hl⟩⟩

end

section

theorem sec7_perp_eq_of_opp {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    [FiniteDimensional K E] (B : LinearMap.BilinForm K E) (hB : B.Nondegenerate)
    (hr : B.IsRefl) (U A₁ : Submodule K E) (A₂ : Set E) (hU1 : U ≤ A₁)
    (hsplit : ∀ w ∈ B.orthogonal U, ∃ a₁ ∈ A₁, ∃ a₂ ∈ A₂, w = a₁ + a₂)
    (h1 : ∀ x ∈ A₁, ∀ y ∈ A₁, B x y = 0) (h2 : ∀ x ∈ A₂, ∀ y ∈ A₂, B x y = 0) :
    B.orthogonal A₁ = A₁ := by
  refine le_antisymm (fun e he => ?_) (fun a ha => ?_)
  · have heU : e ∈ B.orthogonal U := LinearMap.BilinForm.orthogonal_le hU1 he
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := hsplit e heU
    have ha₂U : a₂ ∈ U := by
      rw [← LinearMap.BilinForm.orthogonal_orthogonal hB hr U,
        LinearMap.BilinForm.mem_orthogonal_iff]
      intro w hw
      obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := hsplit w hw
      rw [map_add, LinearMap.add_apply, h2 b₂ hb₂ a₂ ha₂, add_zero]
      have h3 : B b₁ (a₁ + a₂) = 0 := LinearMap.BilinForm.mem_orthogonal_iff.mp he b₁ hb₁
      rw [map_add, h1 b₁ hb₁ a₁ ha₁, zero_add] at h3
      exact h3
    exact A₁.add_mem ha₁ (hU1 ha₂U)
  · rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    exact h1 n hn a ha

theorem sec7_closure_of_fixed {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (B : LinearMap.BilinForm K E) (ψ : E →ₗ[K] E) (hψ : ∀ e e', B (ψ e) e' = B e (ψ e'))
    (S A : Submodule K E) (hS : ∀ x ∈ S, ∀ y ∈ S, B x y = 0) (hA : B.orthogonal A = A)
    (hfix : (∀ s ∈ S, ψ s = 0) ∨ ∀ a ∈ A, ψ a ∈ S) :
    ∀ s ∈ S, ψ s ∈ A := by
  intro s hs
  rcases hfix with h0 | hfix
  · rw [h0 s hs]
    exact A.zero_mem
  · rw [← hA, LinearMap.BilinForm.mem_orthogonal_iff]
    intro a ha
    rw [← hψ]
    exact hS _ (hfix a ha) s hs

end

section

theorem sec7_span_iso {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (B : LinearMap.BilinForm K E) (X : Set E) (hX : ∀ x ∈ X, ∀ y ∈ X, B x y = 0) :
    ∀ x ∈ Submodule.span K X, ∀ y ∈ Submodule.span K X, B x y = 0 := by
  intro x hx y hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
    induction hy using Submodule.span_induction with
    | mem y hy => exact hX x hx y hy
    | zero => rw [map_zero]
    | add y y' _ _ h1 h2 => rw [map_add, h1, h2, add_zero]
    | smul c y _ h => rw [map_smul, h, smul_zero]
  | zero => simp
  | add x x' _ _ h1 h2 => rw [map_add, LinearMap.add_apply, h1, h2, add_zero]
  | smul c x _ h => rw [map_smul, LinearMap.smul_apply, h, smul_zero]

end

end CFSG.RankThree.GF2n.Stroth80
