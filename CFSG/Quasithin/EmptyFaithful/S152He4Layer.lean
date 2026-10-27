module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import CFSG.Quasithin.EmptyFaithful.S152He4Count
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.Quasithin.He4

section Layer

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]

noncomputable def layerEquiv (A B : Submodule F V) (g : V ≃ₗ[F] V)
    (hA : A.map (g : V →ₗ[F] V) = A) (hB : B.map (g : V →ₗ[F] V) = B) :
    (B ⧸ A.comap B.subtype) ≃ₗ[F] (B ⧸ A.comap B.subtype) :=
  Submodule.Quotient.equiv _ _ (g.ofSubmodules B B hB) (by
    ext x
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have : g (y : V) ∈ A.map (g : V →ₗ[F] V) := Submodule.mem_map_of_mem hy
      rw [hA] at this
      exact this
    · intro hx
      have hxA : (x : V) ∈ A.map (g : V →ₗ[F] V) := by rw [hA]; exact hx
      obtain ⟨a, haA, hax⟩ := hxA
      have hxB : (x : V) ∈ B.map (g : V →ₗ[F] V) := by rw [hB]; exact x.2
      obtain ⟨b, hbB, hbx⟩ := hxB
      have hab : a = b := g.injective (by simpa using hax.trans hbx.symm)
      refine ⟨⟨a, hab ▸ hbB⟩, haA, ?_⟩
      exact Subtype.ext (by simpa using hax))


theorem layerEquiv_mk (A B : Submodule F V) (g : V ≃ₗ[F] V) (hA : A.map (g : V →ₗ[F] V) = A)
    (hB : B.map (g : V →ₗ[F] V) = B) (b : B) :
    layerEquiv A B g hA hB (Submodule.Quotient.mk b) =
      Submodule.Quotient.mk (g.ofSubmodules B B hB b) := by
  simp [layerEquiv, Submodule.Quotient.equiv_apply, Submodule.mapQ_apply]

variable (G : Type*) [Group G]

noncomputable def layerHom (ρ : G →* (V ≃ₗ[F] V)) (A B : Submodule F V)
    (hA : ∀ g, A.map (ρ g : V →ₗ[F] V) = A) (hB : ∀ g, B.map (ρ g : V →ₗ[F] V) = B) :
    G →* ((B ⧸ A.comap B.subtype) ≃ₗ[F] (B ⧸ A.comap B.subtype)) where
  toFun g := layerEquiv A B (ρ g) (hA g) (hB g)
  map_one' := by
    ext x
    induction x using Submodule.Quotient.induction_on with | _ b => ?_
    rw [layerEquiv_mk]
    congr 1
    exact Subtype.ext (by simp)
  map_mul' g h := by
    ext x
    induction x using Submodule.Quotient.induction_on with | _ b => ?_
    rw [LinearEquiv.mul_apply, layerEquiv_mk, layerEquiv_mk, layerEquiv_mk]
    congr 1
    exact Subtype.ext (by simp)

theorem layerHom_eq_one_iff (ρ : G →* (V ≃ₗ[F] V)) (A B : Submodule F V)
    (hA : ∀ g, A.map (ρ g : V →ₗ[F] V) = A) (hB : ∀ g, B.map (ρ g : V →ₗ[F] V) = B) (g : G) :
    layerHom G ρ A B hA hB g = 1 ↔ ∀ b ∈ B, ρ g b - b ∈ A := by
  constructor
  · intro h b hb
    have h1 := LinearEquiv.congr_fun h (Submodule.Quotient.mk ⟨b, hb⟩)
    change layerEquiv A B (ρ g) (hA g) (hB g) _ = _ at h1
    rw [layerEquiv_mk] at h1
    have h2 : (Submodule.Quotient.mk (((ρ g).ofSubmodules B B (hB g)) ⟨b, hb⟩) :
        B ⧸ A.comap B.subtype) = Submodule.Quotient.mk ⟨b, hb⟩ := h1
    rw [Submodule.Quotient.eq] at h2
    simpa using h2
  · intro h
    ext x
    induction x using Submodule.Quotient.induction_on with | _ b => ?_
    change layerEquiv A B (ρ g) (hA g) (hB g) _ = Submodule.Quotient.mk b
    rw [layerEquiv_mk, Submodule.Quotient.eq]
    simpa using h b b.2

end Layer

theorem card_linearEquiv_zmod_two {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Finite E]
    {d : ℕ} (hd : Module.finrank (ZMod 2) E = d) :
    Nat.card (E ≃ₗ[ZMod 2] E) = ∏ i : Fin d, (2 ^ d - 2 ^ (i : ℕ)) := by
  let b : Module.Basis (Fin d) (ZMod 2) E := Module.finBasisOfFinrankEq (ZMod 2) E hd
  let e : (E ≃ₗ[ZMod 2] E) ≃* Matrix.GeneralLinearGroup (Fin d) (ZMod 2) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) E).symm.trans
      (Matrix.GeneralLinearGroup.toLin' b).symm
  rw [Nat.card_congr e.toEquiv]
  have := Matrix.card_GL_field (n := d) (𝔽 := ZMod 2)
  simpa using this

theorem add_self_zmod_two {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (x : V) :
    x + x = 0 := by
  rw [← two_smul (ZMod 2) x]
  have : (2 : ZMod 2) = 0 := by decide
  rw [this, zero_smul]


theorem map_eq_of_forall_mem {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (P : Subgroup (V ≃ₗ[ZMod 2] V)) (S : Submodule (ZMod 2) V)
    (hS : ∀ p ∈ P, ∀ x ∈ S, p x ∈ S) (g : ↥P) :
    S.map ((g : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) = S := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact hS g g.2 x hx
  · intro x hx
    refine ⟨(g : V ≃ₗ[ZMod 2] V).symm x, ?_, by simp⟩
    have := hS (g⁻¹ : ↥P) (g⁻¹ : ↥P).2 x hx
    simpa using this

theorem noInvCommNine_linearEquiv {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (hV : Module.finrank (ZMod 2) V ≤ 5) : NoInvCommNine (V ≃ₗ[ZMod 2] V) := by
  intro P hP t ht hc
  by_contra hne
  have h2 := add_self_zmod_two (V := V)
  have htv : ∀ v, t (t v) = v := fun v => by
    have := congrArg (fun f : V ≃ₗ[ZMod 2] V => f v) ht
    simpa using this
  let τ : V →ₗ[ZMod 2] V := (t : V →ₗ[ZMod 2] V) - LinearMap.id
  have hτ : ∀ v, τ v = t v - v := fun v => rfl
  have hττ : ∀ v, τ (τ v) = 0 := by
    intro v
    have : τ (τ v) = (v + v) - (t v + t v) := by
      simp only [hτ, map_sub, htv]
      abel
    rw [this, h2, h2, sub_zero]
  have hcomm : ∀ p ∈ P, ∀ v, p (t v) = t (p v) := fun p hp v => by
    have := congrArg (fun f : V ≃ₗ[ZMod 2] V => f v) (hc p hp)
    simpa using this
  have hpτ : ∀ p ∈ P, ∀ v, p (τ v) = τ (p v) := fun p hp v => by
    simp only [hτ, map_sub, hcomm p hp]
  set U : Submodule (ZMod 2) V := LinearMap.range τ with hUdef
  set W : Submodule (ZMod 2) V := LinearMap.ker τ with hWdef
  have hUW : U ≤ W := by
    rintro _ ⟨v, rfl⟩
    exact LinearMap.mem_ker.2 (hττ v)
  have hUp : ∀ p ∈ P, ∀ x ∈ U, p x ∈ U := by
    rintro p hp _ ⟨v, rfl⟩
    exact ⟨p v, (hpτ p hp v).symm⟩
  have hWp : ∀ p ∈ P, ∀ x ∈ W, p x ∈ W := by
    intro p hp x hx
    have hx' : τ x = 0 := LinearMap.mem_ker.1 hx
    exact LinearMap.mem_ker.2 (by rw [← hpτ p hp, hx', map_zero])
  let ρ : ↥P →* (V ≃ₗ[ZMod 2] V) := P.subtype
  have hU : ∀ g : ↥P, U.map ((ρ g : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) = U :=
    map_eq_of_forall_mem P U hUp
  have hW : ∀ g : ↥P, W.map ((ρ g : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) = W :=
    map_eq_of_forall_mem P W hWp
  have hbot : ∀ g : ↥P, (⊥ : Submodule (ZMod 2) V).map
      ((ρ g : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) = ⊥ := fun g => Submodule.map_bot _
  let L₁ := layerHom ↥P ρ ⊥ U hbot hU
  let L₂ := layerHom ↥P ρ U W hU hW
  let Φ := L₁.prod L₂
  have hΦ : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have h1 : L₁ g = 1 ∧ L₂ g = 1 := Prod.mk_eq_one.1 hg
    have hf1 := (layerHom_eq_one_iff ↥P ρ ⊥ U hbot hU g).1 h1.1
    have hf2 := (layerHom_eq_one_iff ↥P ρ U W hU hW g).1 h1.2
    set gg : V ≃ₗ[ZMod 2] V := (g : V ≃ₗ[ZMod 2] V) with hgg
    have hgP : gg ∈ P := g.2
    have hf1' : ∀ u ∈ U, gg u = u := fun u hu => by
      have := hf1 u hu
      have h0 : (ρ g) u - u = 0 := by simpa using this
      exact sub_eq_zero.1 (show gg u - u = 0 from h0)
    have hf3 : ∀ v, gg v - v ∈ W := by
      intro v
      refine LinearMap.mem_ker.2 ?_
      have : τ (gg v - v) = gg (τ v) - τ v := by
        simp only [map_sub, hpτ gg hgP]
      rw [this, hf1' (τ v) ⟨v, rfl⟩, sub_self]
    have hkey : ∀ v, gg (gg (gg (gg v))) = v := by
      intro v
      set a : V := gg v - v with ha
      set b : V := gg a - a with hb
      have haW : a ∈ W := hf3 v
      have hbU : b ∈ U := hf2 a haW
      have e1 : gg v = v + a := by rw [ha]; abel
      have e2 : gg a = a + b := by rw [hb]; abel
      have e3 : gg b = b := hf1' b hbU
      have e4 : gg (gg v) = v + b := by
        calc gg (gg v) = gg (v + a) := by rw [← e1]
          _ = gg v + gg a := map_add _ _ _
          _ = (v + a) + (a + b) := by rw [e1, e2]
          _ = v + (a + a) + b := by abel
          _ = v + b := by rw [h2 a, add_zero]
      calc gg (gg (gg (gg v))) = gg (gg (v + b)) := by rw [e4]
        _ = gg (gg v) + gg (gg b) := by rw [map_add, map_add]
        _ = (v + b) + b := by rw [e4, e3, e3]
        _ = v + (b + b) := by abel
        _ = v := by rw [h2 b, add_zero]
    have hg4 : g ^ 4 = 1 := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro v
      change (gg ^ 4) v = v
      simp only [pow_succ, pow_zero, one_mul, LinearEquiv.mul_apply]
      exact hkey v
    have hg9 : g ^ 9 = 1 := by
      rw [← hP]
      exact pow_card_eq_one'
    have hord : orderOf g ∣ Nat.gcd 4 9 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hg4)
      (orderOf_dvd_of_pow_eq_one hg9)
    have : orderOf g = 1 := Nat.dvd_one.1 (by simpa using hord)
    exact orderOf_eq_one_iff.1 this
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have hn := LinearMap.finrank_range_add_finrank_ker τ
  have hUW' : Module.finrank (ZMod 2) U ≤ Module.finrank (ZMod 2) W := Submodule.finrank_mono hUW
  set E₁ := ↥U ⧸ (⊥ : Submodule (ZMod 2) V).comap U.subtype with hE₁def
  set E₂ := ↥W ⧸ U.comap W.subtype with hE₂def
  have hE₁ : Module.finrank (ZMod 2) E₁ = Module.finrank (ZMod 2) U := by
    have h1 := Submodule.finrank_quotient_add_finrank ((⊥ : Submodule (ZMod 2) V).comap U.subtype)
    have h0 : (⊥ : Submodule (ZMod 2) V).comap U.subtype = ⊥ := by simp
    have h00 : Module.finrank (ZMod 2) ↥((⊥ : Submodule (ZMod 2) V).comap U.subtype) = 0 := by
      rw [h0]
      exact finrank_bot (ZMod 2) ↥U
    rw [h00] at h1
    exact h1
  have hE₂ : Module.finrank (ZMod 2) E₂ + Module.finrank (ZMod 2) U =
      Module.finrank (ZMod 2) W := by
    have := Submodule.finrank_quotient_add_finrank (U.comap W.subtype)
    rw [LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hUW)] at this
    exact this
  have hUpos : 1 ≤ Module.finrank (ZMod 2) U := by
    have hne' : U ≠ ⊥ := by
      intro hUbot
      apply hne
      refine LinearEquiv.ext fun v => ?_
      have : τ v ∈ U := ⟨v, rfl⟩
      rw [hUbot, Submodule.mem_bot, hτ] at this
      exact sub_eq_zero.1 this
    have : Nontrivial U := Submodule.nontrivial_iff_ne_bot.2 hne'
    exact Module.finrank_pos
  have : Finite E₁ := Finite.of_surjective (Submodule.Quotient.mk : ↥U → E₁)
    (Submodule.Quotient.mk_surjective _)
  have : Finite E₂ := Finite.of_surjective (Submodule.Quotient.mk : ↥W → E₂)
    (Submodule.Quotient.mk_surjective _)
  have hdvd := Subgroup.card_dvd_of_injective Φ hΦ
  have c1 := card_linearEquiv_zmod_two (E := E₁) (d := Module.finrank (ZMod 2) U) hE₁
  have c2 := card_linearEquiv_zmod_two (E := E₂) (d := Module.finrank (ZMod 2) E₂) rfl
  rw [hP, Nat.card_prod, c1, c2] at hdvd
  generalize Module.finrank (ZMod 2) E₂ = d2 at hdvd hE₂
  generalize Module.finrank (ZMod 2) U = r at hdvd hE₂ hUpos hUW' hn
  generalize Module.finrank (ZMod 2) W = m at hE₂ hUW' hn
  have hr : r ≤ 2 := by omega
  have hd2 : d2 ≤ 3 := by omega
  interval_cases r <;> interval_cases d2 <;> simp [Fin.prod_univ_succ] at hdvd <;> omega


theorem NoInvCommNine.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : NoInvCommNine Y) : NoInvCommNine X := by
  intro P hP t ht hc
  have h1 : Nat.card (P.map e.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective e.injective, hP]
  have h2 : e t * e t = 1 := by rw [← map_mul, ht, map_one]
  have h3 : ∀ p ∈ P.map e.toMonoidHom, p * e t = e t * p := by
    rintro _ ⟨p, hp, rfl⟩
    change e p * e t = e t * e p
    rw [← map_mul, ← map_mul, hc p hp]
  exact e.injective (by rw [map_one]; exact h _ h1 _ h2 h3)

theorem NoInvCommNine.of_injective {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    (hf : Function.Injective f) (h : NoInvCommNine Y) : NoInvCommNine X := by
  intro P hP t ht hc
  have h1 : Nat.card (P.map f) = 9 := by rw [Subgroup.card_map_of_injective hf, hP]
  have h2 : f t * f t = 1 := by rw [← map_mul, ht, map_one]
  have h3 : ∀ p ∈ P.map f, p * f t = f t * p := by
    rintro _ ⟨p, hp, rfl⟩
    rw [← map_mul, ← map_mul, hc p hp]
  exact hf (by rw [map_one]; exact h _ h1 _ h2 h3)

theorem noInvCommNine_gl (n : ℕ) (hn : n ≤ 5) : NoInvCommNine (Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) := by
  let e : Matrix.GeneralLinearGroup (Fin n) (ZMod 2) ≃*
      ((Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2)) :=
    Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _)
  exact NoInvCommNine.of_mulEquiv e (noInvCommNine_linearEquiv (le_of_eq_of_le
    (Module.finrank_fin_fun (ZMod 2)) hn))

end CFSG.Quasithin.He4
