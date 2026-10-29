module

public import Mathlib
public import CFSG.Milestones.ASVolI.H1
public import CFSG.Quasithin.Background.HSL3Pair
public import CFSG.Quasithin.H13.VolIH5
public import CFSG.Quasithin.MS93.ML3Syl
public import CFSG.Foundations.Catalog
public import CFSG.Quasithin.Background.HConj
public import CFSG.Quasithin.MS93.ML3Ext2
public import CFSG.Quasithin.MS93.ML3Gen

public section

open scoped commutatorElement

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

abbrev V3 : Type := Fin 3 → ZMod 2

abbrev PermV : Type := Multiplicative (V3 → ZMod 2)

theorem inv_mulVec_mulVec (g : GL (Fin 3) (ZMod 2)) (v : V3) :
    ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
      ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem mulVec_inv_mulVec (g : GL (Fin 3) (ZMod 2)) (v : V3) :
    (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
      (((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

@[expose] def gl3Act : GL (Fin 3) (ZMod 2) →* MulAut PermV where
  toFun g :=
    { toFun := fun f => Multiplicative.ofAdd fun v =>
        Multiplicative.toAdd f (((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v)
      invFun := fun f => Multiplicative.ofAdd fun v =>
        Multiplicative.toAdd f ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v)
      left_inv := fun f => by
        apply Multiplicative.toAdd.injective
        funext v
        simp
      right_inv := fun f => by
        apply Multiplicative.toAdd.injective
        funext v
        simp
      map_mul' := fun f f' => by
        apply Multiplicative.toAdd.injective
        funext v
        simp }
  map_one' := by
    ext f v
    simp
  map_mul' g h := by
    ext f v
    simp [mul_inv_rev, Matrix.mulVec_mulVec]

@[expose] def U0sub : Subgroup PermV :=
  AddSubgroup.toSubgroup (AddMonoidHom.ker (Pi.evalAddMonoidHom (fun _ : V3 => ZMod 2) 0))

@[expose] def Ucore : Subgroup PermV :=
  U0sub ⊓ AddSubgroup.toSubgroup (AddMonoidHom.ker (∑ v : V3, Pi.evalAddMonoidHom (fun _ : V3 => ZMod 2) v))

open scoped Classical in
@[expose] noncomputable def omegaVec : PermV :=
  Multiplicative.ofAdd fun v => if v = 0 then 0 else 1

open scoped Classical in
@[expose] noncomputable def uOf (S : Set V3) : PermV :=
  Multiplicative.ofAdd fun v => if v ≠ 0 ∧ v ∉ S then 1 else 0

@[expose] def IsLine (r : Submodule (ZMod 2) V3) : Prop := Module.finrank (ZMod 2) r = 2

@[expose] def O1set : Set PermV := {x | ∃ q : V3, q ≠ 0 ∧ x = uOf {q}}

@[expose] def O2set : Set PermV :=
  {x | ∃ r : Submodule (ZMod 2) V3, IsLine r ∧ x = uOf (r : Set V3)}

@[expose] def O3set : Set PermV :=
  {x | x ∈ U0sub ∧ Nat.card {v : V3 // Multiplicative.toAdd x v ≠ 0} = 2}

@[expose] def O4set : Set PermV :=
  {x | ∃ v₁ v₂ v₃ : V3, LinearIndependent (ZMod 2) ![v₁, v₂, v₃] ∧ x = uOf {v₁, v₂, v₃}}

@[expose] def Oset : Fin 4 → Set PermV
  | 0 => O1set
  | 1 => O2set
  | 2 => O3set
  | 3 => O4set

@[expose] def Lpt (p : V3) : Subgroup (GL (Fin 3) (ZMod 2)) := glFix {p}

@[expose] def Lln (l : Submodule (ZMod 2) V3) : Subgroup (GL (Fin 3) (ZMod 2)) :=
  glStab (l : Set V3)

structure HypH5 (T : Subgroup (GL (Fin 3) (ZMod 2))) (p : V3) (l : Submodule (ZMod 2) V3) : Prop where
  sylow : IsSylowIn 2 T ⊤
  p_ne : p ≠ 0
  p_fix : ∀ g ∈ T, (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec p = p
  l_line : IsLine l
  l_inv : ∀ g ∈ T, ∀ v ∈ l, (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ l

@[expose] def modNat : GL (Fin 3) (ZMod 2) →* MulAut (Multiplicative V3) := natHom 3 (ZMod 2)

@[expose] def modDual : GL (Fin 3) (ZMod 2) →* MulAut (Multiplicative V3) :=
  (natHom 3 (ZMod 2)).comp CFSG.Quasithin.H.SL3Pair.dualHom

@[expose] def modTriv : GL (Fin 3) (ZMod 2) →* MulAut (Multiplicative (ZMod 2)) := 1

@[expose] def IsoSec {G : Type*} [Group G] {X : Type*} [CommGroup X] (ρ : G →* MulAut X)
    (U Z : Subgroup X) (A : Type*) [CommGroup A] (act : G →* MulAut A) : Prop :=
  Z ≤ U ∧ (∀ g, ∀ u ∈ U, ρ g u ∈ U) ∧ (∀ g, ∀ z ∈ Z, ρ g z ∈ Z) ∧
  ∃ β : ↥U →* A, Function.Surjective β ∧ (∀ u : ↥U, β u = 1 ↔ (u : X) ∈ Z) ∧
    ∀ (g : G) (u u' : ↥U), (u' : X) = ρ g u → β u' = act g (β u)

end CFSG.ASVolI.ChH

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.ASVolI.ChH

@[expose] def H_5_1 : Prop :=
  Ucore ⊔ Subgroup.zpowers omegaVec = U0sub ∧ Ucore ⊓ Subgroup.zpowers omegaVec = ⊥ ∧
  (∀ g : GL (Fin 3) (ZMod 2), ∀ u ∈ U0sub, gl3Act g u ∈ U0sub) ∧
  (∀ g : GL (Fin 3) (ZMod 2), ∀ u ∈ Ucore, gl3Act g u ∈ Ucore) ∧
  (∀ g : GL (Fin 3) (ZMod 2), gl3Act g omegaVec = omegaVec)

open scoped Classical in
private theorem omegaVec_toAdd (v : V3) :
    Multiplicative.toAdd omegaVec v = if v = 0 then 0 else 1 := rfl

private theorem gl3Act_toAdd (g : GL (Fin 3) (ZMod 2)) (f : PermV) (v : V3) :
    Multiplicative.toAdd (gl3Act g f) v =
      Multiplicative.toAdd f (((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v) :=
  rfl

private theorem mem_U0sub' {x : PermV} : x ∈ U0sub ↔ Multiplicative.toAdd x 0 = 0 := by
  simp [U0sub, AddMonoidHom.mem_ker]

private theorem mem_Ucore' {x : PermV} :
    x ∈ Ucore ↔ Multiplicative.toAdd x 0 = 0 ∧ ∑ v : V3, Multiplicative.toAdd x v = 0 := by
  simp [Ucore, mem_U0sub', AddMonoidHom.mem_ker, AddMonoidHom.finset_sum_apply]

private theorem sum_mulVec_eq (h : GL (Fin 3) (ZMod 2)) (F : V3 → ZMod 2) :
    ∑ v : V3, F (((h : Matrix (Fin 3) (Fin 3) (ZMod 2))).mulVec v) = ∑ v : V3, F v := by
  have key : ∀ x y : V3, (h : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec x =
      (h : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec y → x = y := fun x y hxy => by
    have := congrArg (((h⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec) hxy
    rwa [inv_mulVec_mulVec, inv_mulVec_mulVec] at this
  refine Fintype.sum_bijective (fun v : V3 => (h : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v)
    ⟨fun v w hvw => key v w hvw, fun w => ⟨((h⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w,
      mulVec_inv_mulVec h w⟩⟩ _ _ (fun v => rfl)

private theorem omegaVec_mul_self : omegaVec * omegaVec = (1 : PermV) := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_mul, toAdd_one]
  funext v
  rw [Pi.add_apply, omegaVec_toAdd, Pi.zero_apply]
  split_ifs <;> decide

private theorem sum_omegaVec : ∑ v : V3, Multiplicative.toAdd omegaVec v = 1 := by
  have h7 : ∀ v : V3, Multiplicative.toAdd omegaVec v = (if v = 0 then 0 else 1) :=
    fun v => omegaVec_toAdd v
  rw [Finset.sum_congr rfl (fun v _ => h7 v)]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : V3))]
  rw [if_pos rfl, add_zero]
  rw [Finset.sum_congr rfl (fun v hv => if_neg (Finset.ne_of_mem_erase hv))]
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin]
  decide

theorem as_H_5_1 : H_5_1 := by
  have hΩU : omegaVec ∈ U0sub := mem_U0sub'.2 (by simp [omegaVec_toAdd])
  have hΩnot : omegaVec ∉ Ucore := fun h => by
    have := (mem_Ucore'.1 h).2
    rw [sum_omegaVec] at this
    exact absurd this (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply le_antisymm
    · exact sup_le inf_le_left (Subgroup.zpowers_le.2 hΩU)
    · intro u hu
      rw [mem_U0sub'] at hu
      by_cases hs : ∑ v : V3, Multiplicative.toAdd u v = 0
      · exact Subgroup.mem_sup_left (mem_Ucore'.2 ⟨hu, hs⟩)
      · have hs1 : ∑ v : V3, Multiplicative.toAdd u v = 1 := by
          revert hs; generalize (∑ v : V3, Multiplicative.toAdd u v) = s; revert s; decide
        have hmem : u * omegaVec ∈ Ucore := by
          refine mem_Ucore'.2 ⟨?_, ?_⟩
          · rw [toAdd_mul, Pi.add_apply, hu, omegaVec_toAdd]; simp
          · have hsplit : ∑ v : V3, Multiplicative.toAdd (u * omegaVec) v =
                ∑ v : V3, (Multiplicative.toAdd u v + Multiplicative.toAdd omegaVec v) := by
              simp only [toAdd_mul, Pi.add_apply]
            rw [hsplit, Finset.sum_add_distrib, hs1, sum_omegaVec]
            decide
        have hu' : u = (u * omegaVec) * omegaVec := by rw [mul_assoc, omegaVec_mul_self, mul_one]
        rw [hu']
        exact mul_mem (Subgroup.mem_sup_left hmem) (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  · rw [eq_bot_iff]
    rintro x ⟨hxU, hxZ⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxZ
    rw [Subgroup.mem_bot]
    have hΩne1 : omegaVec ≠ 1 := fun h => hΩnot (h ▸ Subgroup.one_mem _)
    have hord : orderOf omegaVec = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact omegaVec_mul_self) hΩne1
    have hpow : ∀ j : ℤ, omegaVec ^ j = 1 ∨ omegaVec ^ j = omegaVec := by
      intro j
      rw [← zpow_mod_orderOf omegaVec j, hord]
      push_cast
      rcases Int.emod_two_eq_zero_or_one j with h | h <;> rw [h]
      · left; simp
      · right; simp
    rcases hpow k with h | h
    · exact h
    · exfalso
      apply hΩnot
      rw [h] at hxU
      exact hxU
  · intro g u hu
    rw [mem_U0sub'] at hu ⊢
    rw [gl3Act_toAdd, Matrix.mulVec_zero]
    exact hu
  · intro g u hu
    rw [mem_Ucore'] at hu ⊢
    refine ⟨?_, ?_⟩
    · rw [gl3Act_toAdd, Matrix.mulVec_zero]
      exact hu.1
    · simp only [gl3Act_toAdd]
      rw [sum_mulVec_eq (g⁻¹) (fun v => Multiplicative.toAdd u v)]
      exact hu.2
  · intro g
    apply Multiplicative.toAdd.injective
    funext v
    rw [gl3Act_toAdd, omegaVec_toAdd, omegaVec_toAdd]
    by_cases hv : v = 0
    · subst hv
      simp
    · have hgv : ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ≠ 0 := by
        intro h0
        apply hv
        have := mulVec_inv_mulVec g v
        rw [h0, Matrix.mulVec_zero] at this
        exact this.symm
      rw [if_neg hgv, if_neg hv]

@[expose] def H_5_2 : Prop :=
  (∀ r s t : Submodule (ZMod 2) V3, IsLine r → IsLine s → IsLine t → r ≠ s → t ≠ r → t ≠ s →
    ∀ q : V3, q ≠ 0 → q ∈ r → q ∈ s → q ∈ t →
      uOf (r : Set V3) * uOf (s : Set V3) = uOf (t : Set V3)) ∧
  ∀ (T : Subgroup (GL (Fin 3) (ZMod 2))) (p : V3) (l : Submodule (ZMod 2) V3), HypH5 T p l →
    (Ucore ⊓ fixV (T.map gl3Act) = Subgroup.closure {uOf {p}, uOf (l : Set V3)} ∧
      rk ↥(Ucore ⊓ fixV (T.map gl3Act)) = 2) ∧
    (rk ↥(Ucore ⊓ fixV ((CFSG.Open.pCoreOf 2 (Lpt p)).map gl3Act)) = 3 ∧
      rk ↥(Ucore ⊓ fixV ((CFSG.Open.pCoreOf 2 (Lln l)).map gl3Act)) = 3) ∧
    (rk ↥(commOn Ucore ((CFSG.Open.pCoreOf 2 (Lpt p)).map gl3Act)) = 3 ∧
      rk ↥(commOn Ucore ((CFSG.Open.pCoreOf 2 (Lln l)).map gl3Act)) = 3) ∧
    (Ucore ⊓ fixV ((Lpt p).map gl3Act) = Subgroup.zpowers (uOf {p}) ∧
      Ucore ⊓ fixV ((Lln l).map gl3Act) = Subgroup.zpowers (uOf (l : Set V3))) ∧
    (∃ β : PermV → PermV → ZMod 2,
      (∀ u ∈ Ucore, ∀ u' ∈ Ucore, ∀ w ∈ Ucore, β (u * u') w = β u w + β u' w) ∧
      (∀ u ∈ Ucore, ∀ w ∈ Ucore, ∀ w' ∈ Ucore, β u (w * w') = β u w + β u w') ∧
      (∀ g : GL (Fin 3) (ZMod 2), ∀ u ∈ Ucore, ∀ w ∈ Ucore, β (gl3Act g u) (gl3Act g w) = β u w) ∧
      (∀ u ∈ Ucore, u ≠ 1 → ∃ w ∈ Ucore, β u w ≠ 0)) ∧
    (∀ (Y : Subgroup (GL (Fin 3) (ZMod 2))) (q : V3), IsSylowIn 3 Y (Lln l) → q ≠ 0 →
      (∀ y ∈ Y, (y : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec q = q) →
      (∀ v : V3, (∀ y ∈ Y, (y : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v = v) → v = 0 ∨ v = q) →
      Ucore ⊓ fixV (Y.map gl3Act) = Subgroup.closure {uOf (l : Set V3), uOf {q}})

@[expose] def H_5_3 : Prop :=
  ∃ Wg : Subgroup PermV, (Wg : Set PermV) = {1} ∪ O2set ∧
    (Wg ≤ Ucore ∧ (∀ g : GL (Fin 3) (ZMod 2), ∀ w ∈ Wg, gl3Act g w ∈ Wg) ∧
      IsoSec gl3Act Wg ⊥ (Multiplicative V3) modDual) ∧
    IsoSec gl3Act Ucore Wg (Multiplicative V3) modNat ∧
    ((∀ i : Fin 4, ∀ x ∈ Oset i, ∀ g : GL (Fin 3) (ZMod 2), gl3Act g x ∈ Oset i) ∧
      (∀ i : Fin 4, ∀ x ∈ Oset i, ∀ y ∈ Oset i, ∃ g : GL (Fin 3) (ZMod 2), gl3Act g x = y) ∧
      (∀ i : Fin 4, ∀ x ∈ Oset i, x ∈ Ucore ∧ x ≠ 1) ∧
      (∀ x ∈ Ucore, x ≠ 1 → ∃ i : Fin 4, x ∈ Oset i) ∧
      (∀ i j : Fin 4, i ≠ j → Disjoint (Oset i) (Oset j))) ∧
    (Set.ncard O1set = 7 ∧ Set.ncard O2set = 7 ∧ Set.ncard O3set = 21 ∧ Set.ncard O4set = 28) ∧
    ((∀ A B : Subgroup PermV, A ≤ Ucore → B ≤ Ucore → (∀ g : GL (Fin 3) (ZMod 2), ∀ a ∈ A, gl3Act g a ∈ A) →
        (∀ g : GL (Fin 3) (ZMod 2), ∀ b ∈ B, gl3Act g b ∈ B) → A ⊔ B = Ucore → A ⊓ B = ⊥ →
        A = ⊥ ∨ B = ⊥) ∧
      Wg = ⨆ (N : Subgroup PermV) (_ : N ≤ Ucore)
        (_ : ∀ g : GL (Fin 3) (ZMod 2), ∀ n ∈ N, gl3Act g n ∈ N)
        (_ : IsIrredOn gl3Act.range N), N)

@[expose] def H_5_4 : Prop :=
  (∀ (T : Subgroup (GL (Fin 3) (ZMod 2))) (p : V3) (l : Submodule (ZMod 2) V3), HypH5 T p l →
    ¬ (Ucore ⊓ fixV ((Lpt p).map gl3Act) ≤
        commOn (Ucore ⊓ fixV (T.map gl3Act)) ((Lln l).map gl3Act)) ∧
    (Ucore ⊓ fixV ((Lln l).map gl3Act) ≤ commOn (Ucore ⊓ fixV (T.map gl3Act)) ((Lpt p).map gl3Act))) ∧
  (∀ a ∈ O1set, ∀ b ∈ O1set, ∀ c ∈ O1set, a ≠ b → a ≠ c → b ≠ c → a * b * c ≠ 1)

@[expose] def H_5_5 : Prop :=
  ∀ (T : Subgroup (GL (Fin 3) (ZMod 2))) (p : V3) (l : Submodule (ZMod 2) V3), HypH5 T p l →
  ∀ (A : Type) [CommGroup A] [Finite A], (∀ a : A, a ^ 2 = 1) →
  ∀ act : GL (Fin 3) (ZMod 2) →* MulAut A, ∀ x : A, x ≠ 1 →
    (∀ g ∈ Lpt p, act g x = x) →
    Subgroup.closure (Set.range fun g : GL (Fin 3) (ZMod 2) => act g x) = ⊤ →
    rk ↥(Subgroup.closure ((fun g : GL (Fin 3) (ZMod 2) => act g x) '' (Lln l : Set _))) = 2 →
      ∃ e : A ≃* Multiplicative V3, ∀ (g : GL (Fin 3) (ZMod 2)) (a : A), e (act g a) = modNat g (e a)

section HBridge55
open CFSG.Quasithin.MS93 Matrix

set_option synthInstance.maxHeartbeats 400000
private abbrev e1 : Fin 3 → ZMod 2 := ![1, 0, 0]

private def line0 : Submodule (ZMod 2) (Fin 3 → ZMod 2) :=
  LinearMap.ker (LinearMap.proj (R := ZMod 2) (φ := fun _ : Fin 3 => ZMod 2) (2 : Fin 3))

private theorem mem_line0 {v : Fin 3 → ZMod 2} : v ∈ line0 ↔ v 2 = 0 := by
  simp [line0]

private theorem toGL_surjective' :
    Function.Surjective (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) →* GL (Fin 3) (ZMod 2)) := by
  intro g
  have hdet : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).det = 1 := by
    have hu : IsUnit (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit
    have hne : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).det ≠ 0 := hu.ne_zero
    revert hne
    generalize (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).det = d
    revert d
    decide
  exact ⟨⟨(g : Matrix (Fin 3) (Fin 3) (ZMod 2)), hdet⟩, Units.ext rfl⟩

private noncomputable def slGL : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) ≃* GL (Fin 3) (ZMod 2) :=
  MulEquiv.ofBijective Matrix.SpecialLinearGroup.toGL
    ⟨Matrix.SpecialLinearGroup.toGL_injective, toGL_surjective'⟩

private theorem slGL_coe (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    ((slGL g : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) := rfl

private noncomputable def B0 : Subgroup (GL (Fin 3) (ZMod 2)) :=
  CFSG.Quasithin.MS93.sStar.map slGL.toMonoidHom

private theorem mem_B0 (x : GL (Fin 3) (ZMod 2)) :
    x ∈ B0 ↔ ∃ a b c : ZMod 2,
      (x : Matrix (Fin 3) (Fin 3) (ZMod 2)) = !![1, a, b; 0, 1, c; 0, 0, 1] := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨a, b, c, rfl⟩ := mem_sStar_iff.mp hy
    exact ⟨a, b, c, rfl⟩
  · rintro ⟨a, b, c, hx⟩
    refine ⟨uniTri a b c, mem_sStar_iff.mpr ⟨a, b, c, rfl⟩, ?_⟩
    apply Units.ext
    exact hx.symm

private theorem sylow_smul_mem {G : Type*} [Group G] {p : ℕ} {P : Sylow p G} {g x : G} :
    x ∈ (g • P : Sylow p G) ↔ g⁻¹ * x * g ∈ (P : Subgroup G) := by
  show x ∈ ((g • P : Sylow p G) : Subgroup G) ↔ _
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
    MulAut.smul_def, MulAut.conj_apply, inv_inv]

private theorem sylow_conj (T : Subgroup (GL (Fin 3) (ZMod 2))) (hT : IsPGroup 2 T)
    (hTi : ¬ 2 ∣ T.index) :
    ∃ c : GL (Fin 3) (ZMod 2), ∀ x : GL (Fin 3) (ZMod 2), x ∈ T ↔ c⁻¹ * x * c ∈ B0 := by
  classical
  have hF : Nat.card (ZMod 2) = 2 ^ 1 := by simp
  set Ts : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := T.comap slGL.toMonoidHom
    with hTs
  have hmap : Ts.map slGL.toMonoidHom = T :=
    Subgroup.map_comap_eq_self_of_surjective slGL.surjective T
  have hTsP : IsPGroup 2 Ts := by
    have h1 : IsPGroup 2 (Ts.map slGL.toMonoidHom) := by rw [hmap]; exact hT
    exact h1.of_injective (Subgroup.equivMapOfInjective Ts slGL.toMonoidHom slGL.injective).toMonoidHom
      (Subgroup.equivMapOfInjective Ts slGL.toMonoidHom slGL.injective).injective
  have hTsi : ¬ 2 ∣ Ts.index := by
    rw [hTs, Subgroup.index_comap_of_surjective T (f := slGL.toMonoidHom) slGL.surjective]
    exact hTi
  let P' : Sylow 2 (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    (isPGroup_sStar hF).toSylow (not_two_dvd_index_sStar hF)
  let Q : Sylow 2 (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := hTsP.toSylow hTsi
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) P' Q
  refine ⟨slGL g, fun x => ?_⟩
  obtain ⟨y, rfl⟩ := slGL.surjective x
  have hQ : y ∈ Q ↔ y ∈ Ts := Iff.rfl
  have hA : slGL y ∈ T ↔ y ∈ Ts := by
    rw [hTs, Subgroup.mem_comap]
    rfl
  have hB : slGL y ∈ T ↔ g⁻¹ * y * g ∈ CFSG.Quasithin.MS93.sStar := by
    rw [hA, ← hQ, ← hg, sylow_smul_mem]
    rfl
  rw [hB, B0, Subgroup.mem_map_equiv]
  simp [map_inv, map_mul]

private theorem fix_decide : ∀ v : Fin 3 → ZMod 2,
    (!![1, 1, 0; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v = v →
    (!![1, 0, 0; 0, 1, 1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v = v →
    v = 0 ∨ v = e1 := by
  decide

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
private theorem line_decide : ∀ F : Finset (Fin 3 → ZMod 2), (0 : Fin 3 → ZMod 2) ∈ F →
    (∀ a ∈ F, ∀ b ∈ F, a + b ∈ F) → F.card = 4 →
    (∀ v ∈ F, (!![1, 1, 0; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ F) →
    (∀ v ∈ F, (!![1, 0, 0; 0, 1, 1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ F) →
    F = Finset.univ.filter (fun v : Fin 3 → ZMod 2 => v 2 = 0) := by
  decide +kernel

private theorem natCard_submod_field {K : Type} [Field K] [Fintype K] {V : Type} [AddCommGroup V]
    {inst : Module K V} [Finite V] (W : Submodule K V) :
    Nat.card W = Fintype.card K ^ Module.finrank K W := by
  haveI : Module.Finite K V := Module.Finite.of_finite
  rw [Module.natCard_eq_pow_finrank (K := K) (V := W), Nat.card_eq_fintype_card]

private theorem natCard_of_finrank_two (l : Submodule (ZMod 2) (Fin 3 → ZMod 2))
    (h : Module.finrank (ZMod 2) l = 2) : Nat.card l = 4 := by
  have hc : Nat.card l = Fintype.card (ZMod 2) ^ Module.finrank (ZMod 2) l := natCard_submod_field l
  rw [hc, h, ZMod.card]
  norm_num

private theorem line_unique (P : (Fin 3 → ZMod 2) → Prop) [DecidablePred P] (h0 : P 0)
    (hadd : ∀ a b, P a → P b → P (a + b)) (hcard : (Finset.univ.filter P).card = 4)
    (ht : ∀ v, P v → P ((!![1, 1, 0; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v))
    (hu : ∀ v, P v → P ((!![1, 0, 0; 0, 1, 1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v)) :
    ∀ v, P v ↔ v 2 = 0 := by
  have key := line_decide (Finset.univ.filter P)
    (by simpa using h0)
    (by
      intro a ha b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb ⊢
      exact hadd a b ha hb)
    hcard
    (by
      intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      exact ht v hv)
    (by
      intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      exact hu v hv)
  intro v
  have hv : v ∈ Finset.univ.filter P ↔ v ∈ Finset.univ.filter (fun v : Fin 3 → ZMod 2 => v 2 = 0) := by
    rw [key]
  simpa using hv

private theorem card_of_rk_two {A : Type} [CommGroup A] [Finite A] (hA : ∀ a : A, a ^ 2 = 1)
    (W : Subgroup A) (h : CFSG.Quasithin.rk ↥W = 2) : Nat.card W = 4 := by
  have hP : IsPGroup 2 W := fun w => ⟨1, Subtype.ext (by simpa using hA (w : A))⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hP
  unfold CFSG.Quasithin.rk at h
  rw [hn, padicValNat.prime_pow] at h
  rw [hn, h]
  rfl

private theorem natCard_toAddSubgroup {A : Type} [CommGroup A] (W : Subgroup A) :
    Nat.card ↥(W.toAddSubgroup) = Nat.card ↥W :=
  Nat.card_congr (Equiv.subtypeEquiv Additive.ofMul (fun a => Iff.rfl))

private theorem mem_Lpt (k : GL (Fin 3) (ZMod 2)) (p : Fin 3 → ZMod 2) :
    k ∈ Lpt p ↔ ∀ v ∈ ({p} : Set (Fin 3 → ZMod 2)), (k : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v = v :=
  Iff.rfl

private theorem mem_Lln (k : GL (Fin 3) (ZMod 2)) (l : Submodule (ZMod 2) (Fin 3 → ZMod 2)) :
    k ∈ Lln l ↔ ∀ v ∈ (l : Set (Fin 3 → ZMod 2)),
      (k : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ l ∧
        ((k⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ l :=
  Iff.rfl

private theorem mulVec_gl (g h : GL (Fin 3) (ZMod 2)) (v : Fin 3 → ZMod 2) :
    ((g * h : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v =
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec ((h : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v) := by
  rw [Units.val_mul, Matrix.mulVec_mulVec]

private theorem mem_Lp_iff (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    g ∈ CFSG.Quasithin.H6.Lp ↔ slGL g ∈ Lpt e1 := by
  rw [CFSG.Quasithin.H6.Lp, MulAction.mem_stabilizer_iff, mem_Lpt]
  have hsm : ∀ v : Fin 3 → ZMod 2, g • v = (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v :=
    fun v => rfl
  constructor
  · intro h v hv
    rw [Set.mem_singleton_iff.mp hv, slGL_coe, ← hsm]
    exact h
  · intro h
    have h' := h e1 (Set.mem_singleton _)
    rw [slGL_coe, ← hsm] at h'
    exact h'

private theorem mem_Ll_iff (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    g ∈ CFSG.Quasithin.H6.Ll ↔ slGL g ∈ Lln line0 := by
  have hL : g ∈ CFSG.Quasithin.H6.Ll ↔ CFSG.Quasithin.H6.IsLl g := Iff.rfl
  rw [hL, mem_Lln]
  have hg' : ∀ k : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2), CFSG.Quasithin.H6.IsLl k →
      ∀ w : Fin 3 → ZMod 2, w 2 = 0 → (k : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w 2 = 0 := by
    rintro k ⟨k20, k21⟩ w hw
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, k20, k21, hw]
  constructor
  · rintro ⟨h20, h21⟩ v hv
    have hv' : v ∈ line0 := hv
    rw [mem_line0] at hv'
    refine ⟨?_, ?_⟩
    · rw [slGL_coe, mem_line0]
      exact hg' g ⟨h20, h21⟩ v hv'
    · rw [← map_inv, slGL_coe, mem_line0]
      exact hg' g⁻¹ (CFSG.Quasithin.H6.isLl_inv g ⟨h20, h21⟩) v hv'
  · intro h
    have h0 := (h (fun i => if i = 0 then 1 else 0) (by simp [mem_line0])).1
    have h1 := (h (fun i => if i = 1 then 1 else 0) (by simp [mem_line0])).1
    rw [slGL_coe, mem_line0] at h0 h1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h0 h1
    exact ⟨h0, h1⟩

private theorem mem_Lln_conj (c : GL (Fin 3) (ZMod 2)) (l : Submodule (ZMod 2) (Fin 3 → ZMod 2))
    (hl : ∀ v : Fin 3 → ZMod 2, (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ l ↔ v 2 = 0)
    (k : GL (Fin 3) (ZMod 2)) : k ∈ Lln line0 ↔ c * k * c⁻¹ ∈ Lln l := by
  have hcinv : ∀ w : Fin 3 → ZMod 2,
      ((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
        ((c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w) = w := by
    intro w; rw [← mulVec_gl, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hcc : ∀ w : Fin 3 → ZMod 2,
      (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
        (((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w) = w := by
    intro w; rw [← mulVec_gl, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hconj : ∀ (k' : GL (Fin 3) (ZMod 2)) (w : Fin 3 → ZMod 2),
      ((c * k' * c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
        ((c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w) =
      (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec ((k' : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w) := by
    intro k' w; rw [mulVec_gl, mulVec_gl, hcinv]
  have hinvconj : ∀ k' : GL (Fin 3) (ZMod 2), (c * k' * c⁻¹ : GL (Fin 3) (ZMod 2))⁻¹ = c * k'⁻¹ * c⁻¹ :=
    fun k' => by group
  rw [mem_Lln, mem_Lln]
  constructor
  · intro h v hv
    obtain ⟨w, rfl⟩ : ∃ w, v = (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w :=
      ⟨_, (hcc v).symm⟩
    have hw : w 2 = 0 := (hl w).1 hv
    obtain ⟨hk1, hk2⟩ := h w ((mem_line0).2 hw)
    rw [hconj]
    rw [hinvconj, hconj]
    exact ⟨(hl _).2 ((mem_line0).1 hk1), (hl _).2 ((mem_line0).1 hk2)⟩
  · intro h w hw
    have hwl : (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w ∈ l := (hl w).2 ((mem_line0).1 hw)
    obtain ⟨h1, h2⟩ := h _ hwl
    rw [hconj] at h1
    rw [hinvconj, hconj] at h2
    exact ⟨(mem_line0).2 ((hl _).1 h1), (mem_line0).2 ((hl _).1 h2)⟩

private theorem fixB0 (v : Fin 3 → ZMod 2)
    (hv : ∀ y ∈ B0, (y : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v = v) : v = 0 ∨ v = e1 := by
  have tmem : slGL (uniTri 1 0 0) ∈ B0 := (mem_B0 _).2 ⟨1, 0, 0, rfl⟩
  have umem : slGL (uniTri 0 0 1) ∈ B0 := (mem_B0 _).2 ⟨0, 0, 1, rfl⟩
  exact fix_decide v (hv _ tmem) (hv _ umem)

private theorem tG_mem : slGL (uniTri 1 0 0) ∈ B0 := (mem_B0 _).2 ⟨1, 0, 0, rfl⟩
private theorem uG_mem : slGL (uniTri 0 0 1) ∈ B0 := (mem_B0 _).2 ⟨0, 0, 1, rfl⟩

private theorem tG_mat : ((slGL (uniTri 1 0 0) : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
    !![1, 1, 0; 0, 1, 0; 0, 0, 1] := rfl

private theorem uG_mat : ((slGL (uniTri 0 0 1) : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
    !![1, 0, 0; 0, 1, 1; 0, 0, 1] := rfl

theorem as_H_5_5 : H_5_5 := by
  intro T p l hyp A _ _ hA act x hx1 hfix hclos hrk
  obtain ⟨-, hTp, hTi⟩ := hyp.sylow
  rw [Subgroup.relIndex_top_right] at hTi
  obtain ⟨c, hc⟩ := sylow_conj T hTp hTi
  have hconjT : ∀ y ∈ B0, c * y * c⁻¹ ∈ T := by
    intro y hy
    refine (hc _).2 ?_
    rw [show c⁻¹ * (c * y * c⁻¹) * c = y by group]
    exact hy
  have hcinv : ∀ w : Fin 3 → ZMod 2,
      ((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
        ((c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w) = w := by
    intro w; rw [← mulVec_gl, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hcc : ∀ w : Fin 3 → ZMod 2,
      (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
        (((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w) = w := by
    intro w; rw [← mulVec_gl, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  obtain ⟨q, hq⟩ : ∃ q : Fin 3 → ZMod 2,
      ((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec p = q := ⟨_, rfl⟩
  have hpq : (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec q = p := by rw [← hq, hcc]
  have hfixq : ∀ y ∈ B0, (y : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec q = q := by
    intro y hy
    have h1 := hyp.p_fix _ (hconjT y hy)
    rw [mulVec_gl, mulVec_gl, hq] at h1
    calc (y : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec q
        = ((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
            ((c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec ((y : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec q)) :=
          (hcinv _).symm
      _ = q := by rw [h1, hq]
  have hq0 : q = e1 := by
    rcases fixB0 q hfixq with h | h
    · exfalso
      apply hyp.p_ne
      rw [← hpq, h, Matrix.mulVec_zero]
    · exact h
  have hpc : (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec e1 = p := by rw [← hq0, hpq]
  have hline : ∀ v : Fin 3 → ZMod 2, (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ l ↔ v 2 = 0 := by
    classical
    have hfr : Module.finrank (ZMod 2) l = 2 := hyp.l_line
    have hcardl : Nat.card l = 4 := natCard_of_finrank_two l hfr
    refine line_unique (fun v => (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ l) ?_ ?_ ?_ ?_ ?_
    · simp
    · intro a b ha hb
      rw [Matrix.mulVec_add]
      exact l.add_mem ha hb
    · let e' : (Fin 3 → ZMod 2) ≃ (Fin 3 → ZMod 2) :=
        { toFun := fun v => (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v
          invFun := fun w => ((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w
          left_inv := hcinv
          right_inv := hcc }
      have h1 : (Finset.univ.filter (fun v : Fin 3 → ZMod 2 =>
            (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ l)).card =
          (Finset.univ.filter (fun w : Fin 3 → ZMod 2 => w ∈ l)).card :=
        Finset.card_equiv e' (fun i => by simp [e'])
      rw [h1, ← Fintype.card_subtype]
      have := hcardl
      rw [Nat.card_eq_fintype_card] at this
      exact this
    · intro v hv
      have h := hyp.l_inv _ (hconjT _ tG_mem) _ hv
      rw [mulVec_gl, mulVec_gl, hcinv] at h
      show (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
        ((!![1, 1, 0; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v) ∈ l
      rw [← tG_mat]
      exact h
    · intro v hv
      have h := hyp.l_inv _ (hconjT _ uG_mem) _ hv
      rw [mulVec_gl, mulVec_gl, hcinv] at h
      show (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
        ((!![1, 0, 0; 0, 1, 1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v) ∈ l
      rw [← uG_mat]
      exact h
  let actA : GL (Fin 3) (ZMod 2) →* AddMonoid.End (Additive A) :=
    { toFun := fun h => AddMonoidHom.mk' (fun y => Additive.ofMul (act h (Additive.toMul y)))
        (fun y z => by
          show Additive.ofMul (act h (Additive.toMul y * Additive.toMul z)) = _
          rw [map_mul]
          rfl)
      map_one' := by
        ext y
        show Additive.ofMul (act 1 (Additive.toMul y)) = y
        rw [map_one]
        rfl
      map_mul' := fun h k => by
        ext y
        show Additive.ofMul (act (h * k) (Additive.toMul y)) =
          Additive.ofMul (act h (Additive.toMul (Additive.ofMul (act k (Additive.toMul y)))))
        rw [map_mul]
        rfl }
  let ρ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) →* AddMonoid.End (Additive A) :=
    (actA.comp (MulAut.conj c).toMonoidHom).comp slGL.toMonoidHom
  have hρ : ∀ (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (y : Additive A),
      ρ g y = Additive.ofMul (act (c * slGL g * c⁻¹) (Additive.toMul y)) := fun g y => rfl
  have hm2 : ∀ m : Additive A, m + m = 0 := by
    intro m
    have h := hA (Additive.toMul m)
    rw [sq] at h
    exact h
  have hx0 : Additive.ofMul x ≠ 0 := fun h => hx1 h
  have hmemLl : ∀ g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      g ∈ CFSG.Quasithin.H6.Ll → c * slGL g * c⁻¹ ∈ Lln l :=
    fun g hg => (mem_Lln_conj c l hline (slGL g)).1 ((mem_Ll_iff g).1 hg)
  have hfix' : ∀ g ∈ CFSG.Quasithin.H6.Lp, ρ g (Additive.ofMul x) = Additive.ofMul x := by
    intro g hg
    have hk : c * slGL g * c⁻¹ ∈ Lpt p := by
      rw [mem_Lpt]
      intro v hv
      rw [Set.mem_singleton_iff.mp hv, ← hpc]
      have hg' := (mem_Lp_iff g).1 hg
      rw [mem_Lpt] at hg'
      rw [mulVec_gl, mulVec_gl, hcinv, hg' e1 (Set.mem_singleton _)]
    show Additive.ofMul (act (c * slGL g * c⁻¹) x) = Additive.ofMul x
    rw [hfix _ hk]
  have hrange : Additive.toMul ⁻¹' (Set.range fun h : GL (Fin 3) (ZMod 2) => act h x) =
      Set.range fun g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) => ρ g (Additive.ofMul x) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_range]
    constructor
    · rintro ⟨h, hh⟩
      refine ⟨slGL.symm (c⁻¹ * h * c), ?_⟩
      rw [hρ, MulEquiv.apply_symm_apply, show c * (c⁻¹ * h * c) * c⁻¹ = h by group]
      show Additive.ofMul (act h x) = y
      rw [hh]
      rfl
    · rintro ⟨g, rfl⟩
      exact ⟨c * slGL g * c⁻¹, by rw [hρ]; rfl⟩
  have hclos' : AddSubgroup.closure
      (Set.range fun g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) => ρ g (Additive.ofMul x)) = ⊤ := by
    rw [← hrange]
    have h1 := Subgroup.toAddSubgroup_closure (Set.range fun h : GL (Fin 3) (ZMod 2) => act h x)
    rw [hclos] at h1
    rw [← h1]
    exact AddSubgroup.ext (fun _ => Iff.rfl)
  have hsetLl : {y : Additive A | ∃ g ∈ CFSG.Quasithin.H6.Ll, ρ g (Additive.ofMul x) = y} =
      Additive.toMul ⁻¹' ((fun h => act h x) '' (Lln l : Set (GL (Fin 3) (ZMod 2)))) := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_image, SetLike.mem_coe]
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨c * slGL g * c⁻¹, hmemLl g hg, by rw [hρ]; rfl⟩
    · rintro ⟨h, hh, hact⟩
      refine ⟨slGL.symm (c⁻¹ * h * c), ?_, ?_⟩
      · rw [mem_Ll_iff, MulEquiv.apply_symm_apply, mem_Lln_conj c l hline (c⁻¹ * h * c),
          show c * (c⁻¹ * h * c) * c⁻¹ = h by group]
        exact hh
      · rw [hρ, MulEquiv.apply_symm_apply, show c * (c⁻¹ * h * c) * c⁻¹ = h by group]
        show Additive.ofMul (act h x) = y
        rw [hact]
        rfl
  have hcard' : Nat.card ↥(AddSubgroup.closure
      {y : Additive A | ∃ g ∈ CFSG.Quasithin.H6.Ll, ρ g (Additive.ofMul x) = y}) = 4 := by
    rw [hsetLl, ← Subgroup.toAddSubgroup_closure, natCard_toAddSubgroup]
    exact card_of_rk_two hA _ hrk
  obtain ⟨f, hf, hfe⟩ := CFSG.Quasithin.H6.volI_H_5_5 (Additive A) ρ hm2 (Additive.ofMul x) hx0 hfix'
    hclos' hcard'
  let fe : (Fin 3 → ZMod 2) ≃+ Additive A := AddEquiv.ofBijective f hf
  refine ⟨{ toFun := fun a => Multiplicative.ofAdd
              ((c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec (fe.symm (Additive.ofMul a)))
            invFun := fun w => Additive.toMul
              (fe (((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
                (Multiplicative.toAdd w)))
            left_inv := fun a => ?_
            right_inv := fun w => ?_
            map_mul' := fun a b => ?_ }, ?_⟩
  · show Additive.toMul (fe (((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
      (Multiplicative.toAdd (Multiplicative.ofAdd
        ((c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec (fe.symm (Additive.ofMul a))))))) = a
    rw [toAdd_ofAdd, hcinv, AddEquiv.apply_symm_apply]
    rfl
  · show Multiplicative.ofAdd ((c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
      (fe.symm (fe (((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
        (Multiplicative.toAdd w))))) = w
    rw [AddEquiv.symm_apply_apply, hcc]
    rfl
  · show Multiplicative.ofAdd ((c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
        (fe.symm (Additive.ofMul (a * b)))) = Multiplicative.ofAdd
        (((c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec (fe.symm (Additive.ofMul a))) +
          ((c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec (fe.symm (Additive.ofMul b))))
    congr 1
    rw [ofMul_mul, map_add, Matrix.mulVec_add]
  · intro g a
    have hv : fe (fe.symm (Additive.ofMul a)) = Additive.ofMul a := AddEquiv.apply_symm_apply fe _
    have hslg' : slGL (slGL.symm (c⁻¹ * g * c)) = c⁻¹ * g * c := MulEquiv.apply_symm_apply slGL _
    have key : f (CFSG.Quasithin.H6.ρV (slGL.symm (c⁻¹ * g * c)) (fe.symm (Additive.ofMul a))) =
        Additive.ofMul (act g a) := by
      rw [hfe]
      change ρ _ (fe (fe.symm (Additive.ofMul a))) = _
      rw [hv, hρ, hslg', show c * (c⁻¹ * g * c) * c⁻¹ = g by group]
      rfl
    have key2 : fe.symm (Additive.ofMul (act g a)) =
        CFSG.Quasithin.H6.ρV (slGL.symm (c⁻¹ * g * c)) (fe.symm (Additive.ofMul a)) := by
      rw [← key]
      exact AddEquiv.symm_apply_apply fe _
    have key3 : ∀ w : Fin 3 → ZMod 2,
        (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
          (CFSG.Quasithin.H6.ρV (slGL.symm (c⁻¹ * g * c)) w) =
        (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec ((c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w) := by
      intro w
      have h1 : CFSG.Quasithin.H6.ρV (slGL.symm (c⁻¹ * g * c)) w =
          (((slGL (slGL.symm (c⁻¹ * g * c))) : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w :=
        rfl
      rw [h1, hslg', mulVec_gl, mulVec_gl, hcc]
    show Multiplicative.ofAdd ((c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
        (fe.symm (Additive.ofMul (act g a)))) = modNat g (Multiplicative.ofAdd
        ((c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec (fe.symm (Additive.ofMul a))))
    rw [key2, key3]
    rfl

end HBridge55

section H54
open CFSG.Quasithin.MS93 Matrix

private theorem mulVec_conj54 (c b : GL (Fin 3) (ZMod 2)) (y : V3) :
    ((c * b * c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec y =
      (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
        ((b : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
          (((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec y)) := by
  rw [mulVec_gl, mulVec_gl]

private theorem conj_data54 (T : Subgroup (GL (Fin 3) (ZMod 2))) (p : V3) (l : Submodule (ZMod 2) V3)
    (hyp : HypH5 T p l) :
    ∃ c : GL (Fin 3) (ZMod 2), (∀ y ∈ B0, c * y * c⁻¹ ∈ T) ∧
      (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec e1 = p ∧
      (∀ v : V3, (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ l ↔ v 2 = 0) := by
  obtain ⟨-, hTp, hTi⟩ := hyp.sylow
  rw [Subgroup.relIndex_top_right] at hTi
  obtain ⟨c, hc⟩ := sylow_conj T hTp hTi
  have hconjT : ∀ y ∈ B0, c * y * c⁻¹ ∈ T := by
    intro y hy
    refine (hc _).2 ?_
    rw [show c⁻¹ * (c * y * c⁻¹) * c = y by group]
    exact hy
  have hcinv : ∀ w : V3,
      ((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
        ((c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w) = w := by
    intro w; rw [← mulVec_gl, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hcc : ∀ w : V3,
      (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
        (((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w) = w := by
    intro w; rw [← mulVec_gl, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  obtain ⟨q, hq⟩ : ∃ q : V3,
      ((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec p = q := ⟨_, rfl⟩
  have hpq : (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec q = p := by rw [← hq, hcc]
  have hfixq : ∀ y ∈ B0, (y : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec q = q := by
    intro y hy
    have h1 := hyp.p_fix _ (hconjT y hy)
    rw [mulVec_gl, mulVec_gl, hq] at h1
    calc (y : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec q
        = ((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
            ((c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec ((y : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec q)) :=
          (hcinv _).symm
      _ = q := by rw [h1, hq]
  have hq0 : q = e1 := by
    rcases fixB0 q hfixq with h | h
    · exfalso
      apply hyp.p_ne
      rw [← hpq, h, Matrix.mulVec_zero]
    · exact h
  have hpc : (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec e1 = p := by rw [← hq0, hpq]
  have hline : ∀ v : V3, (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ l ↔ v 2 = 0 := by
    classical
    have hfr : Module.finrank (ZMod 2) l = 2 := hyp.l_line
    have hcardl : Nat.card l = 4 := natCard_of_finrank_two l hfr
    refine line_unique (fun v => (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ l) ?_ ?_ ?_ ?_ ?_
    · simp
    · intro a b ha hb
      rw [Matrix.mulVec_add]
      exact l.add_mem ha hb
    · let e' : (Fin 3 → ZMod 2) ≃ (Fin 3 → ZMod 2) :=
        { toFun := fun v => (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v
          invFun := fun w => ((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w
          left_inv := hcinv
          right_inv := hcc }
      have h1 : (Finset.univ.filter (fun v : Fin 3 → ZMod 2 =>
            (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ l)).card =
          (Finset.univ.filter (fun w : Fin 3 → ZMod 2 => w ∈ l)).card :=
        Finset.card_equiv e' (fun i => by simp [e'])
      rw [h1, ← Fintype.card_subtype]
      have := hcardl
      rw [Nat.card_eq_fintype_card] at this
      exact this
    · intro v hv
      have h := hyp.l_inv _ (hconjT _ tG_mem) _ hv
      rw [mulVec_gl, mulVec_gl, hcinv] at h
      show (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
        ((!![1, 1, 0; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v) ∈ l
      rw [← tG_mat]
      exact h
    · intro v hv
      have h := hyp.l_inv _ (hconjT _ uG_mem) _ hv
      rw [mulVec_gl, mulVec_gl, hcinv] at h
      show (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
        ((!![1, 0, 0; 0, 1, 1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v) ∈ l
      rw [← uG_mat]
      exact h
  exact ⟨c, hconjT, hpc, hline⟩

private theorem B0_le_Lln_line0 (b : GL (Fin 3) (ZMod 2)) (hb : b ∈ B0) : b ∈ Lln line0 := by
  have key : ∀ k : GL (Fin 3) (ZMod 2), k ∈ B0 → ∀ v : V3, v 2 = 0 →
      (k : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v 2 = 0 := by
    intro k hk v hv
    obtain ⟨a, b', c', hk'⟩ := (mem_B0 k).1 hk
    rw [hk']
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hv]
  rw [mem_Lln]
  intro v hv
  have hv' : v 2 = 0 := mem_line0.1 (SetLike.mem_coe.1 hv)
  refine ⟨?_, ?_⟩
  · exact mem_line0.2 (key b hb v hv')
  · exact mem_line0.2 (key _ (Subgroup.inv_mem B0 hb) v hv')

private theorem zmod2_eq_one_of_ne : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide

private theorem unitri_vec (y z : V3) (hy : y 2 = 1) (hz : z 2 = 1) :
    (!![1, 0, y 0 + z 0; 0, 1, y 1 + z 1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec y = z := by
  have key : ∀ a b : ZMod 2, a + (a + b) = b := by decide
  funext i
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hy, key]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hy, key]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hy, hz]

private def blkMat : Fin 6 → Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  ![!![1, 0, 0; 0, 1, 0; 0, 0, 1], !![0, 1, 0; 1, 0, 0; 0, 0, 1],
    !![1, 1, 0; 0, 1, 0; 0, 0, 1], !![1, 0, 0; 1, 1, 0; 0, 0, 1],
    !![0, 1, 0; 1, 1, 0; 0, 0, 1], !![1, 1, 0; 1, 0, 0; 0, 0, 1]]

private def blkInv : Fin 6 → Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  ![!![1, 0, 0; 0, 1, 0; 0, 0, 1], !![0, 1, 0; 1, 0, 0; 0, 0, 1],
    !![1, 1, 0; 0, 1, 0; 0, 0, 1], !![1, 0, 0; 1, 1, 0; 0, 0, 1],
    !![1, 1, 0; 1, 0, 0; 0, 0, 1], !![0, 1, 0; 1, 1, 0; 0, 0, 1]]

private theorem blk_mul_inv : ∀ i, blkMat i * blkInv i = 1 := by decide

private theorem blk_inv_mul : ∀ i, blkInv i * blkMat i = 1 := by decide

private def blkGL (i : Fin 6) : GL (Fin 3) (ZMod 2) :=
  ⟨blkMat i, blkInv i, blk_mul_inv i, blk_inv_mul i⟩

private theorem blk_stab : ∀ i : Fin 6, ∀ v : V3, v 2 = 0 →
    (blkMat i).mulVec v 2 = 0 ∧ (blkInv i).mulVec v 2 = 0 := by decide

private theorem blkGL_mem (i : Fin 6) : blkGL i ∈ Lln line0 := by
  rw [mem_Lln]
  intro v hv
  have hv' : v 2 = 0 := mem_line0.1 (SetLike.mem_coe.1 hv)
  exact ⟨mem_line0.2 (blk_stab i v hv').1, mem_line0.2 (blk_stab i v hv').2⟩

private theorem blk_transitive : ∀ a b : V3, a 2 = 0 → b 2 = 0 → a ≠ 0 → b ≠ 0 →
    ∃ i : Fin 6, (blkMat i).mulVec a = b := by decide

private def swapGL : GL (Fin 3) (ZMod 2) :=
  ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 0], !![1, 0, 0; 0, 0, 1; 0, 1, 0], by decide, by decide⟩

private def shearGL : GL (Fin 3) (ZMod 2) :=
  ⟨!![1, 0, 0; 0, 1, 0; 0, 1, 1], !![1, 0, 0; 0, 1, 0; 0, 1, 1], by decide, by decide⟩

private theorem swapGL_mem : swapGL ∈ Lpt e1 :=
  (mem_Lpt _ _).2 (fun v hv => by rw [Set.mem_singleton_iff.1 hv]; decide)

private theorem shearGL_mem : shearGL ∈ Lpt e1 :=
  (mem_Lpt _ _).2 (fun v hv => by rw [Set.mem_singleton_iff.1 hv]; decide)

private def Qv (x : V3) : ZMod 2 := if x ≠ 0 ∧ x 2 ≠ 0 then 1 else 0

private theorem three_lines : ∀ w : V3,
    Qv (((swapGL⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w) +
      Qv (((shearGL⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w) +
      Qv w = 0 := by decide

private theorem zmod2_three_four (α β : ZMod 2) (h : α * ((3 : ℕ) : ZMod 2) + β * ((4 : ℕ) : ZMod 2) = 0) :
    α = 0 := by
  revert α β; decide

private theorem compl_trans (c : GL (Fin 3) (ZMod 2)) (l : Submodule (ZMod 2) V3)
    (hline : ∀ v : V3, (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ l ↔ v 2 = 0)
    (y y' : V3) (hy : y ∉ l) (hy' : y' ∉ l) :
    ∃ b : GL (Fin 3) (ZMod 2), b ∈ B0 ∧
      ((c * b * c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec y = y' := by
  have hcoord : ∀ z : V3, z ∉ l →
      ((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec z 2 = 1 := by
    intro z hz
    have h := hline (((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec z)
    rw [mulVec_inv_mulVec] at h
    exact zmod2_eq_one_of_ne _ (fun h0 => hz (h.2 h0))
  obtain ⟨y0, hy0⟩ : ∃ y0 : V3,
      ((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec y = y0 := ⟨_, rfl⟩
  obtain ⟨z0, hz0⟩ : ∃ z0 : V3,
      ((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec y' = z0 := ⟨_, rfl⟩
  have h1 : y0 2 = 1 := by rw [← hy0]; exact hcoord y hy
  have h2 : z0 2 = 1 := by rw [← hz0]; exact hcoord y' hy'
  refine ⟨slGL (uniTri 0 (y0 0 + z0 0) (y0 1 + z0 1)),
    (mem_B0 _).2 ⟨0, y0 0 + z0 0, y0 1 + z0 1, rfl⟩, ?_⟩
  have hb : ((slGL (uniTri 0 (y0 0 + z0 0) (y0 1 + z0 1)) : GL (Fin 3) (ZMod 2)) :
      Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec y0 = z0 :=
    unitri_vec y0 z0 h1 h2
  rw [mulVec_conj54, hy0, hb, ← hz0, mulVec_inv_mulVec]

private theorem mem_Lpt_conj54 (c : GL (Fin 3) (ZMod 2)) (p : V3)
    (hpc : (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec e1 = p) (k : GL (Fin 3) (ZMod 2))
    (hk : k ∈ Lpt e1) : c * k * c⁻¹ ∈ Lpt p := by
  rw [mem_Lpt]
  intro v hv
  rw [Set.mem_singleton_iff.1 hv, ← hpc, mulVec_conj54, inv_mulVec_mulVec]
  rw [(mem_Lpt _ _).1 hk e1 (Set.mem_singleton _)]

private theorem Lln_inv_mem54 (g : GL (Fin 3) (ZMod 2)) (l : Submodule (ZMod 2) V3)
    (hg : g ∈ Lln l) (v : V3) : v ∈ l ↔ (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ l := by
  constructor
  · intro hv
    exact ((mem_Lln g l).1 hg v (SetLike.mem_coe.2 hv)).1
  · intro hv
    have h := ((mem_Lln g⁻¹ l).1 (Subgroup.inv_mem _ hg)) _ (SetLike.mem_coe.2 hv)
    rw [inv_mulVec_mulVec] at h
    exact h.1

private theorem T_trans54 (T : Subgroup (GL (Fin 3) (ZMod 2))) (c : GL (Fin 3) (ZMod 2))
    (hconjT : ∀ y ∈ B0, c * y * c⁻¹ ∈ T) (l : Submodule (ZMod 2) V3)
    (hline : ∀ v : V3, (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ l ↔ v 2 = 0)
    (y y' : V3) (hy : y ∉ l) (hy' : y' ∉ l) :
    ∃ t ∈ T, (t : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec y = y' := by
  obtain ⟨b, hb, hby⟩ := compl_trans c l hline y y' hy hy'
  exact ⟨c * b * c⁻¹, hconjT b hb, hby⟩

private theorem Lln_trans_compl54 (c : GL (Fin 3) (ZMod 2)) (l : Submodule (ZMod 2) V3)
    (hline : ∀ v : V3, (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ l ↔ v 2 = 0)
    (y y' : V3) (hy : y ∉ l) (hy' : y' ∉ l) :
    ∃ g ∈ Lln l, (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec y = y' := by
  obtain ⟨b, hb, hby⟩ := compl_trans c l hline y y' hy hy'
  exact ⟨c * b * c⁻¹, (mem_Lln_conj c l hline b).1 (B0_le_Lln_line0 b hb), hby⟩

private theorem Lln_trans_line54 (c : GL (Fin 3) (ZMod 2)) (l : Submodule (ZMod 2) V3)
    (hline : ∀ v : V3, (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ l ↔ v 2 = 0)
    (y y' : V3) (hy : y ∈ l) (hy0 : y ≠ 0) (hy' : y' ∈ l) (hy0' : y' ≠ 0) :
    ∃ g ∈ Lln l, (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec y = y' := by
  obtain ⟨z, hz⟩ : ∃ z : V3, ((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec y = z :=
    ⟨_, rfl⟩
  obtain ⟨z', hz'⟩ : ∃ z' : V3, ((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec y' = z' :=
    ⟨_, rfl⟩
  have hzl : z 2 = 0 := by
    have h := (hline z).1 (by rw [← hz, mulVec_inv_mulVec]; exact hy)
    exact h
  have hzl' : z' 2 = 0 := by
    have h := (hline z').1 (by rw [← hz', mulVec_inv_mulVec]; exact hy')
    exact h
  have hz0 : z ≠ 0 := by
    intro h0
    apply hy0
    rw [← mulVec_inv_mulVec c y, hz, h0, Matrix.mulVec_zero]
  have hz0' : z' ≠ 0 := by
    intro h0
    apply hy0'
    rw [← mulVec_inv_mulVec c y', hz', h0, Matrix.mulVec_zero]
  obtain ⟨i, hi⟩ := blk_transitive z z' hzl hzl' hz0 hz0'
  refine ⟨c * blkGL i * c⁻¹, (mem_Lln_conj c l hline (blkGL i)).1 (blkGL_mem i), ?_⟩
  rw [mulVec_conj54, hz]
  have hi' : ((blkGL i : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec z = z' := hi
  rw [hi', ← hz', mulVec_inv_mulVec]

private theorem toAdd_uOf_of {S : Set V3} {v : V3} (h : v ≠ 0 ∧ v ∉ S) :
    Multiplicative.toAdd (uOf S) v = 1 := by
  unfold uOf
  simp only [toAdd_ofAdd]
  rw [if_pos h]

private theorem toAdd_uOf_not {S : Set V3} {v : V3} (h : ¬ (v ≠ 0 ∧ v ∉ S)) :
    Multiplicative.toAdd (uOf S) v = 0 := by
  unfold uOf
  simp only [toAdd_ofAdd]
  rw [if_neg h]

private theorem toAdd_uOf_congr {S : Set V3} {v w : V3}
    (h : v ≠ 0 ∧ v ∉ S ↔ w ≠ 0 ∧ w ∉ S) :
    Multiplicative.toAdd (uOf S) v = Multiplicative.toAdd (uOf S) w := by
  by_cases hv : v ≠ 0 ∧ v ∉ S
  · rw [toAdd_uOf_of hv, toAdd_uOf_of (h.1 hv)]
  · rw [toAdd_uOf_not hv, toAdd_uOf_not (fun hw => hv (h.2 hw))]

open scoped Classical in
private theorem sum_toAdd_uOf (S : Set V3) :
    ∑ v : V3, Multiplicative.toAdd (uOf S) v =
      ((Finset.univ.filter (fun v : V3 => v ≠ 0 ∧ v ∉ S)).card : ZMod 2) := by
  have h : ∀ v : V3, Multiplicative.toAdd (uOf S) v = if v ≠ 0 ∧ v ∉ S then 1 else 0 := by
    intro v
    by_cases hv : v ≠ 0 ∧ v ∉ S
    · rw [toAdd_uOf_of hv, if_pos hv]
    · rw [toAdd_uOf_not hv, if_neg hv]
  rw [Finset.sum_congr rfl (fun v _ => h v), Finset.sum_boole]

private theorem card_univ_V3 : (Finset.univ : Finset V3).card = 8 := by
  simp [Finset.card_univ, Fintype.card_fun, ZMod.card]

open scoped Classical in
private theorem card_mem_l (l : Submodule (ZMod 2) V3) (hl : IsLine l) :
    (Finset.univ.filter (fun v : V3 => v ∈ l)).card = 4 := by
  have h4 : Nat.card l = 4 := natCard_of_finrank_two l hl
  rw [Nat.card_eq_fintype_card] at h4
  rw [← h4, Fintype.card_subtype]

open scoped Classical in
private theorem card_compl_l (l : Submodule (ZMod 2) V3) (hl : IsLine l) :
    (Finset.univ.filter (fun v : V3 => v ∉ l)).card = 4 := by
  have h1 := card_mem_l l hl
  have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset V3))
    (fun v : V3 => v ∈ l)
  rw [card_univ_V3] at h2
  omega

open scoped Classical in
private theorem card_mem_l_ne_zero (l : Submodule (ZMod 2) V3) (hl : IsLine l) :
    (Finset.univ.filter (fun v : V3 => v ∈ l ∧ v ≠ 0)).card = 3 := by
  have h4 := card_mem_l l hl
  have hfe : Finset.univ.filter (fun v : V3 => v ∈ l ∧ v ≠ 0) =
      (Finset.univ.filter (fun v : V3 => v ∈ l)).erase 0 := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩
    · rintro ⟨h2, h1⟩; exact ⟨h1, h2⟩
  rw [hfe, Finset.card_erase_of_mem (by simp [Submodule.zero_mem]), h4]

private theorem uOf_pt_mem_Ucore (p : V3) (hp : p ≠ 0) : uOf ({p} : Set V3) ∈ Ucore := by
  rw [mem_Ucore']
  refine ⟨toAdd_uOf_not (S := ({p} : Set V3)) (v := 0) (by simp), ?_⟩
  have h : ∀ v : V3, Multiplicative.toAdd (uOf ({p} : Set V3)) v =
      1 + (if v = 0 then 1 else 0) + (if v = p then 1 else 0) := by
    intro v
    by_cases h0 : v = 0
    · subst h0
      rw [toAdd_uOf_not (S := ({p} : Set V3)) (v := 0) (by simp), if_pos (rfl : (0 : V3) = 0),
        if_neg (Ne.symm hp)]
      decide
    · by_cases hpv : v = p
      · subst hpv
        rw [toAdd_uOf_not (S := ({v} : Set V3)) (v := v) (by simp), if_neg h0, if_pos (rfl : v = v)]
        decide
      · rw [toAdd_uOf_of (S := ({p} : Set V3)) (v := v) ⟨h0, by simpa using hpv⟩, if_neg h0,
          if_neg hpv]
        decide
  rw [Finset.sum_congr rfl (fun v _ => h v)]
  simp [Finset.sum_add_distrib, Finset.sum_ite_eq', card_univ_V3]
  decide

open scoped Classical in
private theorem uOf_l_mem_Ucore (l : Submodule (ZMod 2) V3) (hl : IsLine l) :
    uOf (l : Set V3) ∈ Ucore := by
  rw [mem_Ucore']
  refine ⟨toAdd_uOf_not (by simp), ?_⟩
  rw [sum_toAdd_uOf]
  have hfe : Finset.univ.filter (fun v : V3 => v ≠ 0 ∧ v ∉ (l : Set V3)) =
      Finset.univ.filter (fun v : V3 => v ∉ l) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, SetLike.mem_coe]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨fun h0 => h (h0 ▸ l.zero_mem), h⟩
  rw [hfe, card_compl_l l hl]
  decide

private theorem gl_mulVec_zero_iff (k : GL (Fin 3) (ZMod 2)) (v : V3) :
    (k : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have := congrArg (((k⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec) h
    rwa [inv_mulVec_mulVec, Matrix.mulVec_zero] at this
  · intro h; rw [h, Matrix.mulVec_zero]

private theorem gl_mulVec_eq_iff (k : GL (Fin 3) (ZMod 2)) (p v : V3)
    (hk : (k : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec p = p)
    (hk' : ((k⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec p = p) :
    (k : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v = p ↔ v = p := by
  constructor
  · intro h
    have := congrArg (((k⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec) h
    rw [inv_mulVec_mulVec, hk'] at this
    exact this
  · intro h; rw [h, hk]

private theorem pt_iff (k : GL (Fin 3) (ZMod 2)) (p v : V3)
    (hk : (k : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec p = p)
    (hk' : ((k⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec p = p) :
    ((k : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ≠ 0 ∧
        (k : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∉ ({p} : Set V3)) ↔
      (v ≠ 0 ∧ v ∉ ({p} : Set V3)) := by
  have h0 := gl_mulVec_zero_iff k v
  have hp := gl_mulVec_eq_iff k p v hk hk'
  simp only [ne_eq, Set.mem_singleton_iff, h0, hp]

private theorem l_iff (k : GL (Fin 3) (ZMod 2)) (l : Submodule (ZMod 2) V3)
    (hk : ∀ w ∈ l, (k : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w ∈ l)
    (hk' : ∀ w ∈ l, ((k⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w ∈ l)
    (v : V3) : (k : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ l ↔ v ∈ l := by
  constructor
  · intro h
    have := hk' _ h
    rwa [inv_mulVec_mulVec] at this
  · intro h; exact hk v h

private theorem gl3Act_uOf_pt (p : V3) (g : GL (Fin 3) (ZMod 2)) (hg : g ∈ Lpt p) :
    gl3Act g (uOf ({p} : Set V3)) = uOf ({p} : Set V3) := by
  apply Multiplicative.toAdd.injective
  funext v
  rw [gl3Act_toAdd]
  have hgp : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec p = p :=
    (mem_Lpt _ _).1 hg p (Set.mem_singleton _)
  have hgp' : ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec p = p :=
    (mem_Lpt _ _).1 (Subgroup.inv_mem _ hg) p (Set.mem_singleton _)
  apply toAdd_uOf_congr
  exact pt_iff g⁻¹ p v hgp' (by rw [inv_inv]; exact hgp)

private theorem gl3Act_uOf_l_T (T : Subgroup (GL (Fin 3) (ZMod 2))) (l : Submodule (ZMod 2) V3)
    (hl_inv : ∀ g ∈ T, ∀ v ∈ l, (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ l)
    (t : GL (Fin 3) (ZMod 2)) (ht : t ∈ T) :
    gl3Act t (uOf (l : Set V3)) = uOf (l : Set V3) := by
  apply Multiplicative.toAdd.injective
  funext v
  rw [gl3Act_toAdd]
  apply toAdd_uOf_congr
  have hk : ∀ w ∈ l, ((t⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w ∈ l :=
    fun w hw => hl_inv _ (Subgroup.inv_mem _ ht) w hw
  have hk' : ∀ w ∈ l, (((t⁻¹ : GL (Fin 3) (ZMod 2))⁻¹ : GL (Fin 3) (ZMod 2)) :
      Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w ∈ l := by
    intro w hw
    rw [inv_inv]
    exact hl_inv _ ht w hw
  have h0 := gl_mulVec_zero_iff (t⁻¹ : GL (Fin 3) (ZMod 2)) v
  have hl := l_iff (t⁻¹ : GL (Fin 3) (ZMod 2)) l hk hk' v
  simp only [ne_eq, SetLike.mem_coe, h0, hl]

private theorem Z_const54 (T : Subgroup (GL (Fin 3) (ZMod 2))) (c : GL (Fin 3) (ZMod 2))
    (hconjT : ∀ y ∈ B0, c * y * c⁻¹ ∈ T) (l : Submodule (ZMod 2) V3)
    (hline : ∀ v : V3, (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ l ↔ v 2 = 0)
    (w : PermV) (hw : w ∈ fixV (T.map gl3Act)) (y y' : V3) (hy : y ∉ l) (hy' : y' ∉ l) :
    Multiplicative.toAdd w y = Multiplicative.toAdd w y' := by
  obtain ⟨t, ht, hty⟩ := T_trans54 T c hconjT l hline y y' hy hy'
  have h := (mem_fixV.1 hw) (gl3Act t) (Subgroup.mem_map_of_mem gl3Act ht)
  have h3 : Multiplicative.toAdd (gl3Act t w) y' = Multiplicative.toAdd w y' :=
    congrArg (fun F : PermV => Multiplicative.toAdd F y') h
  have hy_eq : ((t⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec y' = y := by
    rw [← hty, inv_mulVec_mulVec]
  rw [gl3Act_toAdd, hy_eq] at h3
  exact h3

private theorem LL_const54 (l : Submodule (ZMod 2) V3) (f : PermV)
    (hf : f ∈ fixV ((Lln l).map gl3Act)) (g : GL (Fin 3) (ZMod 2)) (hg : g ∈ Lln l) (v : V3) :
    Multiplicative.toAdd f ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v) = Multiplicative.toAdd f v := by
  have h := (mem_fixV.1 hf) (gl3Act g⁻¹) (Subgroup.mem_map_of_mem gl3Act (Subgroup.inv_mem _ hg))
  have h2 : Multiplicative.toAdd (gl3Act g⁻¹ f) v = Multiplicative.toAdd f v :=
    congrArg (fun F : PermV => Multiplicative.toAdd F v) h
  rw [gl3Act_toAdd, inv_inv] at h2
  exact h2

private theorem uOf_l_c (c : GL (Fin 3) (ZMod 2)) (l : Submodule (ZMod 2) V3)
    (hline : ∀ v : V3, (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ l ↔ v 2 = 0) (x : V3) :
    Multiplicative.toAdd (uOf (l : Set V3)) ((c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec x) = Qv x := by
  have hc0 : (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec x ≠ 0 ↔ x ≠ 0 :=
    not_congr (gl_mulVec_zero_iff c x)
  have hcl : (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec x ∉ (l : Set V3) ↔ x 2 ≠ 0 := by
    rw [SetLike.mem_coe]
    exact not_congr (hline x)
  by_cases h : x ≠ 0 ∧ x 2 ≠ 0
  · rw [toAdd_uOf_of ⟨hc0.2 h.1, hcl.2 h.2⟩]
    simp [Qv, h]
  · rw [toAdd_uOf_not (fun hh => h ⟨hc0.1 hh.1, hcl.1 hh.2⟩)]
    simp [Qv, h]

private theorem conj_inv_mulVec (c h : GL (Fin 3) (ZMod 2)) (w : V3) :
    (((c * h * c⁻¹)⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
        ((c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w) =
      (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
        (((h⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w) := by
  have e : (c * h * c⁻¹)⁻¹ = c * h⁻¹ * c⁻¹ := by group
  rw [e, mulVec_conj54, inv_mulVec_mulVec]

private theorem exists_fresh54 : ∀ q1 q2 q3 : V3, ∃ v : V3, v ≠ 0 ∧ v ≠ q1 ∧ v ≠ q2 ∧ v ≠ q3 := by
  decide

private theorem comm_aux54 {G : Type*} [CommGroup G] (a x u : G) :
    a * x * (a * u)⁻¹ = x * u⁻¹ := by
  rw [mul_inv, mul_mul_mul_comm, mul_inv_cancel, one_mul]

private theorem uOf_l_mem_comm (T : Subgroup (GL (Fin 3) (ZMod 2))) (p : V3) (l : Submodule (ZMod 2) V3)
    (hyp : HypH5 T p l) (c : GL (Fin 3) (ZMod 2))
    (hpc : (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec e1 = p)
    (hline : ∀ v : V3, (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ l ↔ v 2 = 0) :
    uOf (l : Set V3) ∈ commOn (Ucore ⊓ fixV (T.map gl3Act)) ((Lpt p).map gl3Act) := by
  classical
  have hp0 : p ≠ 0 := hyp.p_ne
  have hz : uOf ({p} : Set V3) * uOf (l : Set V3) ∈ Ucore ⊓ fixV (T.map gl3Act) := by
    refine Subgroup.mem_inf.2 ⟨mul_mem (uOf_pt_mem_Ucore p hp0) (uOf_l_mem_Ucore l hyp.l_line), mem_fixV.2 ?_⟩
    intro x hx
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hx
    have htp : t ∈ Lpt p := (mem_Lpt _ _).2 (fun v hv => by
      rw [Set.mem_singleton_iff.1 hv]; exact hyp.p_fix t ht)
    show gl3Act t (uOf ({p} : Set V3) * uOf (l : Set V3)) = uOf ({p} : Set V3) * uOf (l : Set V3)
    have e1 : gl3Act t (uOf ({p} : Set V3) * uOf (l : Set V3)) =
        gl3Act t (uOf ({p} : Set V3)) * gl3Act t (uOf (l : Set V3)) :=
      MulEquiv.map_mul (gl3Act t) _ _
    rw [e1, gl3Act_uOf_pt p t htp, gl3Act_uOf_l_T T l hyp.l_inv t ht]
  have hcommg : ∀ g ∈ Lpt p, gl3Act g (uOf (l : Set V3)) * (uOf (l : Set V3))⁻¹ ∈
      commOn (Ucore ⊓ fixV (T.map gl3Act)) ((Lpt p).map gl3Act) := by
    intro g hg
    apply Subgroup.subset_closure
    refine ⟨gl3Act g, Subgroup.mem_map_of_mem gl3Act hg, _, hz, ?_⟩
    show gl3Act g (uOf (l : Set V3)) * (uOf (l : Set V3))⁻¹ =
      gl3Act g (uOf ({p} : Set V3) * uOf (l : Set V3)) * (uOf ({p} : Set V3) * uOf (l : Set V3))⁻¹
    have e1 : gl3Act g (uOf ({p} : Set V3) * uOf (l : Set V3)) =
        gl3Act g (uOf ({p} : Set V3)) * gl3Act g (uOf (l : Set V3)) :=
      MulEquiv.map_mul (gl3Act g) _ _
    rw [e1, gl3Act_uOf_pt p g hg]
    exact (comm_aux54 _ _ _).symm
  have hg1 : c * swapGL * c⁻¹ ∈ Lpt p := mem_Lpt_conj54 c p hpc swapGL swapGL_mem
  have hg2 : c * shearGL * c⁻¹ ∈ Lpt p := mem_Lpt_conj54 c p hpc shearGL shearGL_mem
  have hid : ∀ v : V3, Multiplicative.toAdd (gl3Act (c * swapGL * c⁻¹) (uOf (l : Set V3))) v +
      Multiplicative.toAdd (gl3Act (c * shearGL * c⁻¹) (uOf (l : Set V3))) v +
      Multiplicative.toAdd (uOf (l : Set V3)) v = 0 := by
    intro v
    obtain ⟨w, rfl⟩ : ∃ w, v = (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w :=
      ⟨_, (mulVec_inv_mulVec c v).symm⟩
    rw [gl3Act_toAdd, gl3Act_toAdd, conj_inv_mulVec, conj_inv_mulVec, uOf_l_c c l hline,
      uOf_l_c c l hline, uOf_l_c c l hline]
    exact three_lines w
  have hX : gl3Act (c * swapGL * c⁻¹) (uOf (l : Set V3)) * (uOf (l : Set V3))⁻¹ *
      (gl3Act (c * shearGL * c⁻¹) (uOf (l : Set V3)) * (uOf (l : Set V3))⁻¹) = uOf (l : Set V3) := by
    apply Multiplicative.toAdd.injective
    funext v
    have h := hid v
    simp only [toAdd_mul, toAdd_inv, Pi.add_apply, Pi.neg_apply]
    generalize Multiplicative.toAdd (gl3Act (c * swapGL * c⁻¹) (uOf (l : Set V3))) v = A at *
    generalize Multiplicative.toAdd (gl3Act (c * shearGL * c⁻¹) (uOf (l : Set V3))) v = B at *
    generalize Multiplicative.toAdd (uOf (l : Set V3)) v = C at *
    revert A B C
    decide
  have hm := mul_mem (hcommg _ hg1) (hcommg _ hg2)
  exact (congrArg (fun x => x ∈ commOn (Ucore ⊓ fixV (T.map gl3Act)) ((Lpt p).map gl3Act)) hX.symm).mpr hm

private theorem H54_one (T : Subgroup (GL (Fin 3) (ZMod 2))) (p : V3) (l : Submodule (ZMod 2) V3)
    (hyp : HypH5 T p l) (c : GL (Fin 3) (ZMod 2)) (hconjT : ∀ y ∈ B0, c * y * c⁻¹ ∈ T)
    (hpc : (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec e1 = p)
    (hline : ∀ v : V3, (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ l ↔ v 2 = 0) :
    ¬ (Ucore ⊓ fixV ((Lpt p).map gl3Act) ≤
        commOn (Ucore ⊓ fixV (T.map gl3Act)) ((Lln l).map gl3Act)) := by
  classical
  intro hle
  obtain ⟨x0, hx0⟩ : ∃ x0 : V3,
      (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec ![0, 0, 1] = x0 := ⟨_, rfl⟩
  have hx0l : x0 ∉ l := by
    rw [← hx0, hline]
    decide
  have hpl : p ∈ l := by
    rw [← hpc, hline]
    decide
  have hp0 : p ≠ 0 := hyp.p_ne
  obtain ⟨K, hK⟩ : ∃ K : Subgroup PermV, ∀ f : PermV, f ∈ K ↔ Multiplicative.toAdd f x0 = 0 :=
    ⟨AddSubgroup.toSubgroup (AddMonoidHom.ker (Pi.evalAddMonoidHom (fun _ : V3 => ZMod 2) x0)),
      fun f => by simp [AddMonoidHom.mem_ker]⟩
  have hcomm : commOn (Ucore ⊓ fixV (T.map gl3Act)) ((Lln l).map gl3Act) ≤ K := by
    unfold commOn
    apply (Subgroup.closure_le _).2
    rintro u ⟨a, ha, w, hw, rfl⟩
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 ha
    have hwfix : w ∈ fixV (T.map gl3Act) := (Subgroup.mem_inf.1 hw).2
    show gl3Act g w * w⁻¹ ∈ K
    rw [hK, toAdd_mul, toAdd_inv, Pi.add_apply, Pi.neg_apply, gl3Act_toAdd]
    have hy : ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec x0 ∉ l :=
      fun h => hx0l ((Lln_inv_mem54 _ l (Subgroup.inv_mem _ hg) x0).2 h)
    rw [Z_const54 T c hconjT l hline w hwfix _ x0 hy hx0l]
    exact add_neg_cancel _
  have hu : uOf ({p} : Set V3) ∈ Ucore ⊓ fixV ((Lpt p).map gl3Act) := by
    refine Subgroup.mem_inf.2 ⟨uOf_pt_mem_Ucore p hp0, mem_fixV.2 ?_⟩
    intro x hx
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hx
    exact gl3Act_uOf_pt p g hg
  have h1 := (hK _).1 (hcomm (hle hu))
  have h2 : Multiplicative.toAdd (uOf ({p} : Set V3)) x0 = 1 := by
    apply toAdd_uOf_of
    refine ⟨?_, ?_⟩
    · intro h0
      apply hx0l
      rw [h0]
      exact l.zero_mem
    · intro hmem
      rw [Set.mem_singleton_iff] at hmem
      apply hx0l
      rw [hmem]
      exact hpl
  rw [h2] at h1
  exact absurd h1 (by decide)

private theorem H54_two (T : Subgroup (GL (Fin 3) (ZMod 2))) (p : V3) (l : Submodule (ZMod 2) V3)
    (hyp : HypH5 T p l) (c : GL (Fin 3) (ZMod 2)) (hconjT : ∀ y ∈ B0, c * y * c⁻¹ ∈ T)
    (hpc : (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec e1 = p)
    (hline : ∀ v : V3, (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ l ↔ v 2 = 0) :
    Ucore ⊓ fixV ((Lln l).map gl3Act) ≤
      commOn (Ucore ⊓ fixV (T.map gl3Act)) ((Lpt p).map gl3Act) := by
  classical
  intro f hf
  obtain ⟨hfU, hfix⟩ := Subgroup.mem_inf.1 hf
  have hf0 : Multiplicative.toAdd f 0 = 0 := (mem_Ucore'.1 hfU).1
  have hfsum : ∑ v : V3, Multiplicative.toAdd f v = 0 := (mem_Ucore'.1 hfU).2
  obtain ⟨x0, hx0⟩ : ∃ x0 : V3,
      (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec ![0, 0, 1] = x0 := ⟨_, rfl⟩
  have hx0l : x0 ∉ l := by
    rw [← hx0, hline]
    decide
  have hpl : p ∈ l := by
    rw [← hpc, hline]
    decide
  have hp0 : p ≠ 0 := hyp.p_ne
  have hout : ∀ v : V3, v ∉ l → Multiplicative.toAdd f v = Multiplicative.toAdd f x0 := by
    intro v hv
    obtain ⟨g, hg, hgv⟩ := Lln_trans_compl54 c l hline x0 v hx0l hv
    rw [← hgv, LL_const54 l f hfix g hg]
  have hin : ∀ v : V3, v ∈ l → v ≠ 0 → Multiplicative.toAdd f v = Multiplicative.toAdd f p := by
    intro v hv hv0
    obtain ⟨g, hg, hgv⟩ := Lln_trans_line54 c l hline p v hpl hp0 hv hv0
    rw [← hgv, LL_const54 l f hfix g hg]
  obtain ⟨α, hα⟩ : ∃ α, Multiplicative.toAdd f p = α := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β, Multiplicative.toAdd f x0 = β := ⟨_, rfl⟩
  have hform : ∀ v : V3, Multiplicative.toAdd f v =
      α * (if v ∈ l ∧ v ≠ 0 then 1 else 0) + β * (if v ∉ l then 1 else 0) := by
    intro v
    by_cases hv : v ∈ l
    · by_cases hv0 : v = 0
      · subst hv0
        simp [hf0]
      · rw [hin v hv hv0, hα]
        simp [hv, hv0]
    · rw [hout v hv, hβ]
      simp [hv]
  have hsum2 : ∑ v : V3, Multiplicative.toAdd f v =
      α * ((3 : ℕ) : ZMod 2) + β * ((4 : ℕ) : ZMod 2) := by
    rw [Finset.sum_congr rfl (fun v _ => hform v), Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, Finset.sum_boole, Finset.sum_boole, card_mem_l_ne_zero l hyp.l_line,
      card_compl_l l hyp.l_line]
  have hα0 : α = 0 := zmod2_three_four α β (by rw [← hsum2, hfsum])
  have hu := uOf_l_mem_comm T p l hyp c hpc hline
  by_cases hβ0 : β = 0
  · have hf1 : f = 1 := by
      apply Multiplicative.toAdd.injective
      funext v
      rw [hform v, hα0, hβ0, toAdd_one, Pi.zero_apply]
      simp
    rw [hf1]
    exact one_mem _
  · have hβ1 : β = 1 := zmod2_eq_one_of_ne β hβ0
    have hf2 : f = uOf (l : Set V3) := by
      apply Multiplicative.toAdd.injective
      funext v
      rw [hform v, hα0, hβ1]
      by_cases hv : v ∈ l
      · have hv' : ¬ (v ≠ 0 ∧ v ∉ (l : Set V3)) := fun h => h.2 (SetLike.mem_coe.2 hv)
        rw [toAdd_uOf_not hv']
        simp [hv]
      · have hv' : v ≠ 0 ∧ v ∉ (l : Set V3) :=
          ⟨fun h0 => hv (h0 ▸ l.zero_mem), fun h => hv (SetLike.mem_coe.1 h)⟩
        rw [toAdd_uOf_of hv']
        simp [hv]
    rw [hf2]
    exact hu

theorem as_H_5_4 : H_5_4 := by
  refine ⟨fun T p l hyp => ?_, ?_⟩
  · obtain ⟨c, hconjT, hpc, hline⟩ := conj_data54 T p l hyp
    exact ⟨H54_one T p l hyp c hconjT hpc hline, H54_two T p l hyp c hconjT hpc hline⟩
  · intro a ha b hb d hd _ _ _ hprod
    obtain ⟨q1, -, rfl⟩ := ha
    obtain ⟨q2, -, rfl⟩ := hb
    obtain ⟨q3, -, rfl⟩ := hd
    obtain ⟨v, hv0, hv1, hv2, hv3⟩ := exists_fresh54 q1 q2 q3
    have h' : Multiplicative.toAdd (uOf {q1} * uOf {q2} * uOf {q3}) v = Multiplicative.toAdd (1 : PermV) v :=
      congrArg (fun F : PermV => Multiplicative.toAdd F v) hprod
    simp only [toAdd_mul, toAdd_one, Pi.add_apply, Pi.zero_apply] at h'
    rw [toAdd_uOf_of ⟨hv0, by simpa using hv1⟩, toAdd_uOf_of ⟨hv0, by simpa using hv2⟩,
      toAdd_uOf_of ⟨hv0, by simpa using hv3⟩] at h'
    exact absurd h' (by decide)

end H54

section H5Lin

set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 800000

private theorem H5_one_of_ne : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide

private def H5dot (a v : V3) : ZMod 2 := a 0 * v 0 + a 1 * v 1 + a 2 * v 2

private def H5lin (a : V3) : PermV := Multiplicative.ofAdd fun v => H5dot a v

private theorem toAdd_H5lin (a v : V3) : Multiplicative.toAdd (H5lin a) v = H5dot a v := rfl

private theorem H5dot_zero_right (a : V3) : H5dot a 0 = 0 := by simp [H5dot]

private theorem H5dot_zero_left (v : V3) : H5dot 0 v = 0 := by simp [H5dot]

private theorem H5dot_add_right (a v w : V3) : H5dot a (v + w) = H5dot a v + H5dot a w := by
  simp only [H5dot, Pi.add_apply]; ring

private theorem H5dot_add_left (a b v : V3) : H5dot (a + b) v = H5dot a v + H5dot b v := by
  simp only [H5dot, Pi.add_apply]; ring

private theorem H5dot_smul (a v : V3) (c : ZMod 2) : H5dot a (c • v) = c * H5dot a v := by
  simp only [H5dot, Pi.smul_apply, smul_eq_mul]; ring

private theorem H5lin_mul (a b : V3) : H5lin (a + b) = H5lin a * H5lin b := by
  apply Multiplicative.toAdd.injective
  funext v
  rw [toAdd_mul, Pi.add_apply]
  simp only [toAdd_H5lin, H5dot_add_left]

private theorem H5lin_zero : H5lin 0 = 1 := by
  apply Multiplicative.toAdd.injective
  funext v
  rw [toAdd_H5lin, H5dot_zero_left]
  rfl

private theorem H5lin_inj {a b : V3} (h : H5lin a = H5lin b) : a = b := by
  have key : ∀ v, H5dot a v = H5dot b v := fun v => by
    have := congrArg (fun F : PermV => Multiplicative.toAdd F v) h
    simpa only [toAdd_H5lin] using this
  funext i
  fin_cases i
  · simpa [H5dot] using key ![1, 0, 0]
  · simpa [H5dot] using key ![0, 1, 0]
  · simpa [H5dot] using key ![0, 0, 1]

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
private theorem H5lines_decide : ∀ F : Finset V3, (0 : V3) ∈ F →
    (∀ a ∈ F, ∀ b ∈ F, a + b ∈ F) → F.card = 4 →
    ∃ a : V3, a ≠ 0 ∧ ∀ v : V3, v ∈ F ↔ H5dot a v = 0 := by
  decide +kernel

private theorem H5dot_filter_card : ∀ a : V3, a ≠ 0 →
    (Finset.univ.filter (fun v : V3 => H5dot a v = 0)).card = 4 := by
  decide

private theorem H5line_dot (r : Submodule (ZMod 2) V3) (hr : IsLine r) :
    ∃ a : V3, a ≠ 0 ∧ ∀ v, v ∈ r ↔ H5dot a v = 0 := by
  classical
  obtain ⟨a, ha, hF⟩ := H5lines_decide (Finset.univ.filter (fun v : V3 => v ∈ r))
    (by simp [Submodule.zero_mem])
    (fun x hx y hy => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy ⊢
      exact r.add_mem hx hy)
    (card_mem_l r hr)
  refine ⟨a, ha, fun v => ?_⟩
  have := hF v
  simpa using this

private def H5sub (a : V3) : Submodule (ZMod 2) V3 where
  carrier := {v | H5dot a v = 0}
  add_mem' := fun {u v} hu hv => by
    simp only [Set.mem_setOf_eq] at hu hv ⊢
    rw [H5dot_add_right, hu, hv, add_zero]
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    exact H5dot_zero_right a
  smul_mem' := fun c v hv => by
    simp only [Set.mem_setOf_eq] at hv ⊢
    rw [H5dot_smul, hv, mul_zero]

private theorem mem_H5sub {a v : V3} : v ∈ H5sub a ↔ H5dot a v = 0 := Iff.rfl

private theorem H5sub_isLine (a : V3) (ha : a ≠ 0) : IsLine (H5sub a) := by
  classical
  have hc : Nat.card (H5sub a) = 4 := by
    have h1 : Nat.card (H5sub a) = (Finset.univ.filter (fun v : V3 => H5dot a v = 0)).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      congr 1
      exact Finset.filter_congr (fun v _ => mem_H5sub)
    rw [h1, H5dot_filter_card a ha]
  unfold IsLine
  have h2 : Nat.card (H5sub a) =
      Fintype.card (ZMod 2) ^ Module.finrank (ZMod 2) (H5sub a) :=
    natCard_submod_field (H5sub a)
  have h4 : (4 : ℕ) = 2 ^ Module.finrank (ZMod 2) (H5sub a) := by
    rw [← hc, h2, ZMod.card]
  have h5 : (2 : ℕ) ^ 2 = 2 ^ Module.finrank (ZMod 2) (H5sub a) := by
    rw [← h4]; norm_num
  exact (Nat.pow_right_injective (le_refl 2) h5).symm

private theorem exists_line_dot (a : V3) (ha : a ≠ 0) :
    ∃ r : Submodule (ZMod 2) V3, IsLine r ∧ ∀ v, v ∈ r ↔ H5dot a v = 0 :=
  ⟨H5sub a, H5sub_isLine a ha, fun _ => mem_H5sub⟩

private theorem uOf_H5lin (a : V3) (r : Submodule (ZMod 2) V3)
    (hr : ∀ v, v ∈ r ↔ H5dot a v = 0) : uOf (r : Set V3) = H5lin a := by
  unfold uOf H5lin
  congr 1
  funext v
  by_cases h : H5dot a v = 0
  · rw [if_neg (fun hh => hh.2 ((hr v).2 h)), h]
  · have hv0 : v ≠ 0 := fun h0 => h (by rw [h0, H5dot_zero_right])
    have hvr : v ∉ r := fun hh => h ((hr v).1 hh)
    rw [if_pos ⟨hv0, hvr⟩, H5_one_of_ne _ h]

private def H5dualVec (g : GL (Fin 3) (ZMod 2)) (a : V3) : V3 :=
  (((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).transpose).mulVec a

private theorem H5dot_transpose_mulVec (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) (a v : V3) :
    H5dot ((M.transpose).mulVec a) v = H5dot a (M.mulVec v) := by
  simp only [H5dot, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.transpose_apply]
  ring

private theorem gl3Act_H5lin (g : GL (Fin 3) (ZMod 2)) (a : V3) :
    gl3Act g (H5lin a) = H5lin (H5dualVec g a) := by
  apply Multiplicative.toAdd.injective
  funext v
  rw [gl3Act_toAdd]
  simp only [toAdd_H5lin, H5dualVec]
  rw [H5dot_transpose_mulVec]

private def basisM (a b c : V3) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  !![a 0, b 0, c 0; a 1, b 1, c 1; a 2, b 2, c 2]

private theorem basisM_mulVec (a b c : V3) :
    (basisM a b c).mulVec ![1, 0, 0] = a ∧ (basisM a b c).mulVec ![0, 1, 0] = b ∧
      (basisM a b c).mulVec ![0, 0, 1] = c := by
  refine ⟨?_, ?_, ?_⟩ <;> funext i <;> fin_cases i <;>
    simp [basisM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

private theorem gl_map_bases (a b c a' b' c' : V3) (h : (basisM a b c).det ≠ 0)
    (h' : (basisM a' b' c').det ≠ 0) :
    ∃ g : GL (Fin 3) (ZMod 2), (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec a = a' ∧
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec b = b' ∧
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec c = c' := by
  obtain ⟨hA, hB, hC⟩ := basisM_mulVec a b c
  obtain ⟨hA', hB', hC'⟩ := basisM_mulVec a' b' c'
  have hu : IsUnit (basisM a b c) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 h)
  have hM : ((basisM a' b' c') * (basisM a b c)⁻¹).det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    exact mul_ne_zero h' (inv_ne_zero h)
  have hinv : ∀ w : V3, (basisM a b c)⁻¹.mulVec ((basisM a b c).mulVec w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hu),
      Matrix.one_mulVec]
  have hBa : (basisM a b c)⁻¹.mulVec a = ![1, 0, 0] := by
    calc (basisM a b c)⁻¹.mulVec a
        = (basisM a b c)⁻¹.mulVec ((basisM a b c).mulVec ![1, 0, 0]) := by
          rw [hA]
      _ = ![1, 0, 0] := hinv _
  have hBb : (basisM a b c)⁻¹.mulVec b = ![0, 1, 0] := by
    calc (basisM a b c)⁻¹.mulVec b
        = (basisM a b c)⁻¹.mulVec ((basisM a b c).mulVec ![0, 1, 0]) := by
          rw [hB]
      _ = ![0, 1, 0] := hinv _
  have hBc : (basisM a b c)⁻¹.mulVec c = ![0, 0, 1] := by
    calc (basisM a b c)⁻¹.mulVec c
        = (basisM a b c)⁻¹.mulVec ((basisM a b c).mulVec ![0, 0, 1]) := by
          rw [hC]
      _ = ![0, 0, 1] := hinv _
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hM, ?_, ?_, ?_⟩
  · show ((basisM a' b' c') * (basisM a b c)⁻¹).mulVec a = a'
    rw [← Matrix.mulVec_mulVec, hBa, hA']
  · show ((basisM a' b' c') * (basisM a b c)⁻¹).mulVec b = b'
    rw [← Matrix.mulVec_mulVec, hBb, hB']
  · show ((basisM a' b' c') * (basisM a b c)⁻¹).mulVec c = c'
    rw [← Matrix.mulVec_mulVec, hBc, hC']

private theorem sum_V3 {M : Type*} [AddCommMonoid M] (g : V3 → M) :
    ∑ v : V3, g v = g ![0, 0, 0] + g ![1, 0, 0] + g ![0, 1, 0] + g ![1, 1, 0] +
      g ![0, 0, 1] + g ![1, 0, 1] + g ![0, 1, 1] + g ![1, 1, 1] := by
  have h : (Finset.univ : Finset V3) = {![0, 0, 0], ![1, 0, 0], ![0, 1, 0], ![1, 1, 0],
      ![0, 0, 1], ![1, 0, 1], ![0, 1, 1], ![1, 1, 1]} := by decide
  rw [h, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  abel

private theorem H5lin_mem_Ucore (a : V3) : H5lin a ∈ Ucore := by
  rw [mem_Ucore']
  refine ⟨by rw [toAdd_H5lin, H5dot_zero_right], ?_⟩
  have key : ∀ b : V3, ∑ v : V3, H5dot b v = 0 := by decide
  simp only [toAdd_H5lin]
  exact key a

private def pairV (a b : V3) : PermV := Multiplicative.ofAdd fun v => if v = a ∨ v = b then 1 else 0

private theorem toAdd_pairV (a b v : V3) :
    Multiplicative.toAdd (pairV a b) v = if v = a ∨ v = b then 1 else 0 := rfl

private theorem gl_inv_mulVec_eq_iff (g : GL (Fin 3) (ZMod 2)) (v a : V3) :
    ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v = a ↔
      v = (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec a := by
  constructor
  · rintro rfl
    exact (mulVec_inv_mulVec g v).symm
  · rintro rfl
    exact inv_mulVec_mulVec g a

private theorem gl3Act_pairV (g : GL (Fin 3) (ZMod 2)) (a b : V3) :
    gl3Act g (pairV a b) = pairV ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec a)
      ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec b) := by
  apply Multiplicative.toAdd.injective
  funext v
  rw [gl3Act_toAdd]
  simp only [toAdd_pairV, gl_inv_mulVec_eq_iff]

private theorem toAdd_uOf_congr2 {S S' : Set V3} {v w : V3}
    (h : v ≠ 0 ∧ v ∉ S ↔ w ≠ 0 ∧ w ∉ S') :
    Multiplicative.toAdd (uOf S) v = Multiplicative.toAdd (uOf S') w := by
  by_cases hv : v ≠ 0 ∧ v ∉ S
  · rw [toAdd_uOf_of hv, toAdd_uOf_of (h.1 hv)]
  · rw [toAdd_uOf_not hv, toAdd_uOf_not (fun hw => hv (h.2 hw))]

private theorem gl3Act_uOf (g : GL (Fin 3) (ZMod 2)) (S : Set V3) :
    gl3Act g (uOf S) =
      uOf {w | ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w ∈ S} := by
  apply Multiplicative.toAdd.injective
  funext v
  rw [gl3Act_toAdd]
  apply toAdd_uOf_congr2
  simp only [Set.mem_setOf_eq, ne_eq, gl_mulVec_zero_iff]

private theorem uOf_pt_mul_uOf_pt (q q' : V3) (hq : q ≠ 0) (hq' : q' ≠ 0) (hne : q ≠ q') :
    uOf ({q} : Set V3) * uOf ({q'} : Set V3) = pairV q q' := by
  apply Multiplicative.toAdd.injective
  funext v
  rw [toAdd_mul, Pi.add_apply, toAdd_pairV]
  have key : ∀ q q' v : V3, q ≠ 0 → q' ≠ 0 → q ≠ q' →
      ((if v ≠ 0 ∧ v ≠ q then (1 : ZMod 2) else 0) + (if v ≠ 0 ∧ v ≠ q' then 1 else 0)) =
        if v = q ∨ v = q' then 1 else 0 := by decide
  have h1 : Multiplicative.toAdd (uOf ({q} : Set V3)) v =
      if v ≠ 0 ∧ v ≠ q then 1 else 0 := by
    unfold uOf; simp only [toAdd_ofAdd, Set.mem_singleton_iff]
  have h2 : Multiplicative.toAdd (uOf ({q'} : Set V3)) v =
      if v ≠ 0 ∧ v ≠ q' then 1 else 0 := by
    unfold uOf; simp only [toAdd_ofAdd, Set.mem_singleton_iff]
  rw [h1, h2]
  exact key q q' v hq hq' hne

private def D3 (a b c : V3) : ZMod 2 :=
  a 0 * b 1 * c 2 - a 0 * c 1 * b 2 - b 0 * a 1 * c 2 + b 0 * c 1 * a 2 +
    c 0 * a 1 * b 2 - c 0 * b 1 * a 2

private theorem basisM_det (a b c : V3) : (basisM a b c).det = D3 a b c := by
  rw [Matrix.det_fin_three]
  simp [basisM, D3]

private theorem basisM_col (a b c : V3) : (basisM a b c).col = ![a, b, c] := by
  funext i
  fin_cases i <;> (funext j; fin_cases j <;> rfl)

private theorem linIndep_iff_D3 (a b c : V3) :
    LinearIndependent (ZMod 2) ![a, b, c] ↔ D3 a b c ≠ 0 := by
  rw [← basisM_col, Matrix.linearIndependent_cols_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
    isUnit_iff_ne_zero, basisM_det]

private theorem complete1 : ∀ a : V3, a ≠ 0 → ∃ b c : V3, D3 a b c ≠ 0 := by decide

private theorem complete2 : ∀ a b : V3, a ≠ 0 → b ≠ 0 → a ≠ b → ∃ c : V3, D3 a b c ≠ 0 := by
  decide

private theorem gl_map_pair (a b a' b' : V3) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (ha' : a' ≠ 0) (hb' : b' ≠ 0) (hab' : a' ≠ b') :
    ∃ g : GL (Fin 3) (ZMod 2), (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec a = a' ∧
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec b = b' := by
  obtain ⟨c, hc⟩ := complete2 a b ha hb hab
  obtain ⟨c', hc'⟩ := complete2 a' b' ha' hb' hab'
  obtain ⟨g, h1, h2, -⟩ := gl_map_bases a b c a' b' c' (by rw [basisM_det]; exact hc)
    (by rw [basisM_det]; exact hc')
  exact ⟨g, h1, h2⟩

private theorem gl_map_vec (a b : V3) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ g : GL (Fin 3) (ZMod 2), (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec a = b := by
  obtain ⟨c, d, hcd⟩ := complete1 a ha
  obtain ⟨c', d', hcd'⟩ := complete1 b hb
  obtain ⟨g, h1, -, -⟩ := gl_map_bases a c d b c' d' (by rw [basisM_det]; exact hcd)
    (by rw [basisM_det]; exact hcd')
  exact ⟨g, h1⟩

private theorem gl_map_dual (a b : V3) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ g : GL (Fin 3) (ZMod 2), H5dualVec g a = b := by
  obtain ⟨N, hN⟩ := gl_map_vec a b ha hb
  refine ⟨CFSG.Quasithin.H.SL3Pair.dualGL N, ?_⟩
  have hinv : ((CFSG.Quasithin.H.SL3Pair.dualGL N)⁻¹ : GL (Fin 3) (ZMod 2)) =
      CFSG.Quasithin.H.SL3Pair.dualGL N⁻¹ := by
    have := map_inv CFSG.Quasithin.H.SL3Pair.dualHom N
    rw [CFSG.Quasithin.H.SL3Pair.dualHom_apply, CFSG.Quasithin.H.SL3Pair.dualHom_apply] at this
    exact this.symm
  unfold H5dualVec
  rw [hinv, CFSG.Quasithin.H.SL3Pair.coe_dualGL, inv_inv, Matrix.transpose_transpose, hN]

private theorem uOf_ne_one (S : Set V3) (w : V3) (h : w ≠ 0 ∧ w ∉ S) : uOf S ≠ 1 := by
  intro h1
  have h2 : Multiplicative.toAdd (uOf S) w = 1 := toAdd_uOf_of h
  rw [h1, toAdd_one, Pi.zero_apply] at h2
  exact zero_ne_one h2

private theorem H5lin_ne_one {a : V3} (ha : a ≠ 0) : H5lin a ≠ 1 := by
  intro h
  apply ha
  apply H5lin_inj
  rw [h, H5lin_zero]

private theorem O2set_eq : O2set = {x | ∃ a : V3, a ≠ 0 ∧ x = H5lin a} := by
  ext x
  simp only [O2set, Set.mem_setOf_eq]
  constructor
  · rintro ⟨r, hr, rfl⟩
    obtain ⟨a, ha, hmem⟩ := H5line_dot r hr
    exact ⟨a, ha, uOf_H5lin a r hmem⟩
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨r, hr, hmem⟩ := exists_line_dot a ha
    exact ⟨r, hr, (uOf_H5lin a r hmem).symm⟩

private theorem O4set_eq : O4set = {x | ∃ a b c : V3, D3 a b c ≠ 0 ∧ x = uOf {a, b, c}} := by
  ext x
  simp only [O4set, Set.mem_setOf_eq]
  constructor
  · rintro ⟨a, b, c, hind, rfl⟩
    exact ⟨a, b, c, (linIndep_iff_D3 a b c).1 hind, rfl⟩
  · rintro ⟨a, b, c, hD, rfl⟩
    exact ⟨a, b, c, (linIndep_iff_D3 a b c).2 hD, rfl⟩

private theorem mem_U0sub_pairV {a b : V3} (ha : a ≠ 0) (hb : b ≠ 0) : pairV a b ∈ U0sub := by
  rw [mem_U0sub', toAdd_pairV, if_neg]
  rintro (h | h)
  · exact ha h.symm
  · exact hb h.symm

private theorem O3set_eq : O3set = {x | ∃ a b : V3, a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧ x = pairV a b} := by
  ext x
  simp only [O3set, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hU, hcard⟩
    have hU0 : Multiplicative.toAdd x 0 = 0 := mem_U0sub'.1 hU
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hcard
    obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.1 hcard
    have hmem : ∀ v : V3, Multiplicative.toAdd x v ≠ 0 ↔ (v = a ∨ v = b) := by
      intro v
      have := congrArg (fun s : Finset V3 => v ∈ s) hs
      simpa using this
    have ha : a ≠ 0 := fun h0 => (hmem 0).2 (Or.inl h0.symm) hU0
    have hb : b ≠ 0 := fun h0 => (hmem 0).2 (Or.inr h0.symm) hU0
    refine ⟨a, b, ha, hb, hab, ?_⟩
    apply Multiplicative.toAdd.injective
    funext v
    rw [toAdd_pairV]
    by_cases h : v = a ∨ v = b
    · rw [if_pos h]
      exact H5_one_of_ne _ ((hmem v).2 h)
    · rw [if_neg h]
      exact not_not.1 (fun hh => h ((hmem v).1 hh))
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    refine ⟨mem_U0sub_pairV ha hb, ?_⟩
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hs : Finset.univ.filter (fun v : V3 => Multiplicative.toAdd (pairV a b) v ≠ 0) =
        {a, b} := by
      ext v
      rw [Finset.mem_filter, toAdd_pairV, Finset.mem_insert, Finset.mem_singleton]
      by_cases h : v = a ∨ v = b
      · rw [if_pos h]
        simp [h]
      · rw [if_neg h]
        simp [h]
    rw [hs, Finset.card_pair hab]

private theorem gl3Act_uOf_eq (g : GL (Fin 3) (ZMod 2)) (S T : Set V3)
    (h : ∀ w, w ∈ T ↔
      ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w ∈ S) :
    gl3Act g (uOf S) = uOf T := by
  rw [gl3Act_uOf]
  congr 1
  ext w
  exact (h w).symm

private theorem gl3Act_uOf_singleton (g : GL (Fin 3) (ZMod 2)) (q : V3) :
    gl3Act g (uOf ({q} : Set V3)) =
      uOf ({(g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec q} : Set V3) := by
  apply gl3Act_uOf_eq
  intro w
  rw [Set.mem_singleton_iff, Set.mem_singleton_iff, gl_inv_mulVec_eq_iff]

private theorem gl3Act_uOf_triple (g : GL (Fin 3) (ZMod 2)) (a b c : V3) :
    gl3Act g (uOf ({a, b, c} : Set V3)) =
      uOf ({(g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec a,
        (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec b,
        (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec c} : Set V3) := by
  apply gl3Act_uOf_eq
  intro w
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, gl_inv_mulVec_eq_iff]

private theorem gl_det_eq_one (g : GL (Fin 3) (ZMod 2)) :
    (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).det = 1 := by
  have hu : IsUnit (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
  have hne : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).det ≠ 0 := hu.ne_zero
  revert hne
  generalize (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).det = d
  revert d
  decide

private theorem basisM_gl (g : GL (Fin 3) (ZMod 2)) (a b c : V3) :
    basisM ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec a)
      ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec b)
      ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec c) =
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * basisM a b c := by
  ext i j
  fin_cases j <;> fin_cases i <;>
    simp [basisM, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

private theorem D3_gl (g : GL (Fin 3) (ZMod 2)) (a b c : V3) :
    D3 ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec a)
      ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec b)
      ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec c) = D3 a b c := by
  rw [← basisM_det, ← basisM_det, basisM_gl, Matrix.det_mul, gl_det_eq_one, one_mul]

private theorem H5dualVec_ne_zero (g : GL (Fin 3) (ZMod 2)) {a : V3} (ha : a ≠ 0) :
    H5dualVec g a ≠ 0 := by
  intro h0
  have h1 : gl3Act g (H5lin a) = gl3Act g 1 := by
    rw [gl3Act_H5lin, h0, H5lin_zero, map_one]
  exact ha (H5lin_inj (((gl3Act g).injective h1).trans H5lin_zero.symm))

private theorem toAdd_uOf1 (q v : V3) :
    Multiplicative.toAdd (uOf ({q} : Set V3)) v = if v ≠ 0 ∧ ¬ (v = q) then 1 else 0 := by
  unfold uOf
  simp only [toAdd_ofAdd, Set.mem_singleton_iff]

private theorem toAdd_uOf3 (a b c v : V3) :
    Multiplicative.toAdd (uOf ({a, b, c} : Set V3)) v =
      if v ≠ 0 ∧ ¬ (v = a ∨ v = b ∨ v = c) then 1 else 0 := by
  unfold uOf
  simp only [toAdd_ofAdd, Set.mem_insert_iff, Set.mem_singleton_iff]

private theorem D3_nonzero (a b c : V3) (h : D3 a b c ≠ 0) :
    a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  have key : ∀ a b c : V3, D3 a b c ≠ 0 →
      a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c := by decide
  exact key a b c h

private theorem trans_O1 (q q' : V3) (hq : q ≠ 0) (hq' : q' ≠ 0) :
    ∃ g : GL (Fin 3) (ZMod 2), gl3Act g (uOf ({q} : Set V3)) = uOf ({q'} : Set V3) := by
  obtain ⟨g, hg⟩ := gl_map_vec q q' hq hq'
  exact ⟨g, by rw [gl3Act_uOf_singleton, hg]⟩

private theorem trans_O2 (a b : V3) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ g : GL (Fin 3) (ZMod 2), gl3Act g (H5lin a) = H5lin b := by
  obtain ⟨g, hg⟩ := gl_map_dual a b ha hb
  exact ⟨g, by rw [gl3Act_H5lin, hg]⟩

private theorem trans_O3 (a b a' b' : V3) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (ha' : a' ≠ 0) (hb' : b' ≠ 0) (hab' : a' ≠ b') :
    ∃ g : GL (Fin 3) (ZMod 2), gl3Act g (pairV a b) = pairV a' b' := by
  obtain ⟨g, h1, h2⟩ := gl_map_pair a b a' b' ha hb hab ha' hb' hab'
  exact ⟨g, by rw [gl3Act_pairV, h1, h2]⟩

private theorem trans_O4 (a b c a' b' c' : V3) (h : D3 a b c ≠ 0) (h' : D3 a' b' c' ≠ 0) :
    ∃ g : GL (Fin 3) (ZMod 2), gl3Act g (uOf ({a, b, c} : Set V3)) =
      uOf ({a', b', c'} : Set V3) := by
  obtain ⟨g, h1, h2, h3⟩ := gl_map_bases a b c a' b' c' (by rw [basisM_det]; exact h)
    (by rw [basisM_det]; exact h')
  exact ⟨g, by rw [gl3Act_uOf_triple, h1, h2, h3]⟩

private theorem O1_ucore (x : PermV) (hx : x ∈ O1set) : x ∈ Ucore ∧ x ≠ 1 := by
  obtain ⟨q, hq, rfl⟩ := hx
  refine ⟨uOf_pt_mem_Ucore q hq, ?_⟩
  have key : ∀ q : V3, q ≠ 0 → ∃ w : V3, w ≠ 0 ∧ ¬ (w = q) := by decide
  obtain ⟨w, hw0, hwq⟩ := key q hq
  exact uOf_ne_one _ w ⟨hw0, by simpa using hwq⟩

private theorem O2_ucore (x : PermV) (hx : x ∈ O2set) : x ∈ Ucore ∧ x ≠ 1 := by
  rw [O2set_eq] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨H5lin_mem_Ucore a, H5lin_ne_one ha⟩

private theorem O3_ucore (x : PermV) (hx : x ∈ O3set) : x ∈ Ucore ∧ x ≠ 1 := by
  rw [O3set_eq] at hx
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hx
  have key : ∀ a b : V3, a ≠ 0 → b ≠ 0 → a ≠ b →
      ∑ v : V3, Multiplicative.toAdd (pairV a b) v = 0 := by decide
  have h0 : Multiplicative.toAdd (pairV a b) 0 = 0 := by
    rw [toAdd_pairV, if_neg]
    rintro (h | h)
    · exact ha h.symm
    · exact hb h.symm
  refine ⟨mem_Ucore'.2 ⟨h0, key a b ha hb hab⟩, ?_⟩
  intro h1
  have h2 : Multiplicative.toAdd (pairV a b) a = 1 := by
    rw [toAdd_pairV, if_pos (Or.inl rfl)]
  rw [h1, toAdd_one, Pi.zero_apply] at h2
  exact zero_ne_one h2

private theorem O4_ucore (x : PermV) (hx : x ∈ O4set) : x ∈ Ucore ∧ x ≠ 1 := by
  rw [O4set_eq] at hx
  obtain ⟨a, b, c, hD, rfl⟩ := hx
  have key : ∀ a b c : V3, D3 a b c ≠ 0 →
      ∑ v : V3, (if v ≠ 0 ∧ ¬ (v = a ∨ v = b ∨ v = c) then (1 : ZMod 2) else 0) = 0 := by
    decide
  have hsum : ∑ v : V3, Multiplicative.toAdd (uOf ({a, b, c} : Set V3)) v = 0 := by
    simp only [toAdd_uOf3]
    exact key a b c hD
  have h0 : Multiplicative.toAdd (uOf ({a, b, c} : Set V3)) 0 = 0 := by
    rw [toAdd_uOf3, if_neg]
    intro h
    exact h.1 rfl
  refine ⟨mem_Ucore'.2 ⟨h0, hsum⟩, ?_⟩
  have key2 : ∀ a b c : V3, D3 a b c ≠ 0 → ∃ w : V3, w ≠ 0 ∧ ¬ (w = a ∨ w = b ∨ w = c) := by
    decide
  obtain ⟨w, hw0, hw⟩ := key2 a b c hD
  exact uOf_ne_one _ w ⟨hw0, by simpa using hw⟩

private theorem Oset_ucore (i : Fin 4) (x : PermV) (hx : x ∈ Oset i) :
    x ∈ Ucore ∧ x ≠ 1 := by
  fin_cases i
  · exact O1_ucore x hx
  · exact O2_ucore x hx
  · exact O3_ucore x hx
  · exact O4_ucore x hx

private theorem sum_zmod2_eq_card (f : V3 → ZMod 2) :
    ∑ v : V3, f v = ((Finset.univ.filter (fun v => f v ≠ 0)).card : ZMod 2) := by
  classical
  have h : ∀ v, f v = if f v ≠ 0 then 1 else 0 := by
    intro v
    by_cases hv : f v = 0
    · simp [hv]
    · simp [hv, H5_one_of_ne _ hv]
  rw [Finset.sum_congr rfl (fun v _ => h v), Finset.sum_boole]

private theorem eq_of_toAdd_eq (x y : PermV)
    (h : ∀ v, Multiplicative.toAdd x v = Multiplicative.toAdd y v) : x = y := by
  apply Multiplicative.toAdd.injective
  funext v
  exact h v

private theorem mem_T_iff (x : PermV) (v : V3) :
    v ∈ (Finset.univ.erase (0 : V3)) \ Finset.univ.filter (fun v => Multiplicative.toAdd x v ≠ 0) ↔
      v ≠ 0 ∧ Multiplicative.toAdd x v = 0 := by
  simp [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_filter]

private theorem cover_Ucore (x : PermV) (hx : x ∈ Ucore) (hx1 : x ≠ 1) :
    x ∈ O1set ∨ x ∈ O2set ∨ x ∈ O3set ∨ x ∈ O4set := by
  classical
  obtain ⟨hU0, hsum⟩ := mem_Ucore'.1 hx
  have hS0c : (Finset.univ.erase (0 : V3)).card = 7 := by decide
  have hSsub : Finset.univ.filter (fun v => Multiplicative.toAdd x v ≠ 0) ⊆
      Finset.univ.erase (0 : V3) := by
    intro v hv
    rw [Finset.mem_filter] at hv
    rw [Finset.mem_erase]
    exact ⟨fun h0 => hv.2 (h0 ▸ hU0), Finset.mem_univ _⟩
  have hpar : ((Finset.univ.filter (fun v => Multiplicative.toAdd x v ≠ 0)).card : ZMod 2) = 0 := by
    have h : ∑ v : V3, Multiplicative.toAdd x v =
        ((Finset.univ.filter (fun v => Multiplicative.toAdd x v ≠ 0)).card : ZMod 2) :=
      sum_zmod2_eq_card (fun v => Multiplicative.toAdd x v)
    rw [hsum] at h
    exact h.symm
  have hcardle : (Finset.univ.filter (fun v => Multiplicative.toAdd x v ≠ 0)).card ≤ 7 := by
    rw [← hS0c]
    exact Finset.card_le_card hSsub
  have hcardpos : (Finset.univ.filter (fun v => Multiplicative.toAdd x v ≠ 0)).card ≠ 0 := by
    intro h0
    apply hx1
    apply eq_of_toAdd_eq
    intro v
    rw [toAdd_one, Pi.zero_apply]
    by_contra hv
    have hmem : v ∈ Finset.univ.filter (fun v => Multiplicative.toAdd x v ≠ 0) := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hv⟩
    rw [Finset.card_eq_zero.1 h0] at hmem
    exact Finset.notMem_empty _ hmem
  have key : ∀ n : ℕ, n ≤ 7 → n ≠ 0 → ((n : ℕ) : ZMod 2) = 0 → n = 2 ∨ n = 4 ∨ n = 6 := by
    decide
  rcases key _ hcardle hcardpos hpar with h2 | h4 | h6
  ·
    right; right; left
    refine ⟨mem_U0sub'.2 hU0, ?_⟩
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact h2
  ·
    have hT : (Finset.univ.erase (0 : V3) \
        Finset.univ.filter (fun v => Multiplicative.toAdd x v ≠ 0)).card = 3 := by
      rw [Finset.card_sdiff_of_subset hSsub, hS0c, h4]
    obtain ⟨a, b, c, hab, hac, hbc, hT3⟩ := Finset.card_eq_three.1 hT
    have hTiff : ∀ v : V3, (v ≠ 0 ∧ Multiplicative.toAdd x v = 0) ↔ (v = a ∨ v = b ∨ v = c) := by
      intro v
      rw [← mem_T_iff x v, hT3]
      simp
    have ha0 : a ≠ 0 := ((hTiff a).2 (Or.inl rfl)).1
    have hb0 : b ≠ 0 := ((hTiff b).2 (Or.inr (Or.inl rfl))).1
    have hc0 : c ≠ 0 := ((hTiff c).2 (Or.inr (Or.inr rfl))).1
    have hxeq : x = uOf ({a, b, c} : Set V3) := by
      apply eq_of_toAdd_eq
      intro v
      rw [toAdd_uOf3]
      by_cases hv0 : v = 0
      · rw [hv0, if_neg (fun h => h.1 rfl), hU0]
      · by_cases hvT : v = a ∨ v = b ∨ v = c
        · rw [if_neg (fun h => h.2 hvT)]
          exact ((hTiff v).2 hvT).2
        · rw [if_pos ⟨hv0, hvT⟩]
          have hne : Multiplicative.toAdd x v ≠ 0 := fun h0 => hvT ((hTiff v).1 ⟨hv0, h0⟩)
          exact H5_one_of_ne _ hne
    by_cases hD : D3 a b c ≠ 0
    · right; right; right
      rw [O4set_eq]
      exact ⟨a, b, c, hD, hxeq⟩
    · right; left
      rw [O2set_eq]
      have hD0 : D3 a b c = 0 := not_not.1 hD
      have key1 : ∀ a b c : V3, a ≠ 0 → b ≠ 0 → c ≠ 0 → a ≠ b → a ≠ c → b ≠ c →
          D3 a b c = 0 → c = a + b := by decide
      have hcab : c = a + b := key1 a b c ha0 hb0 hc0 hab hac hbc hD0
      have key3 : ∀ a b : V3, a ≠ 0 → b ≠ 0 → a ≠ b →
          ∃ α : V3, α ≠ 0 ∧ H5dot α a = 0 ∧ H5dot α b = 0 := by decide
      obtain ⟨α, hα0, hαa, hαb⟩ := key3 a b ha0 hb0 hab
      have key4 : ∀ a b α v : V3, a ≠ 0 → b ≠ 0 → a ≠ b → α ≠ 0 → H5dot α a = 0 →
          H5dot α b = 0 →
          H5dot α v = if v ≠ 0 ∧ ¬ (v = a ∨ v = b ∨ v = a + b) then 1 else 0 := by decide
      refine ⟨α, hα0, ?_⟩
      apply eq_of_toAdd_eq
      intro v
      rw [toAdd_H5lin, hxeq, toAdd_uOf3, hcab]
      exact (key4 a b α v ha0 hb0 hab hα0 hαa hαb).symm
  ·
    have hT : (Finset.univ.erase (0 : V3) \
        Finset.univ.filter (fun v => Multiplicative.toAdd x v ≠ 0)).card = 1 := by
      rw [Finset.card_sdiff_of_subset hSsub, hS0c, h6]
    obtain ⟨q, hq⟩ := Finset.card_eq_one.1 hT
    have hqiff : ∀ v : V3, (v ≠ 0 ∧ Multiplicative.toAdd x v = 0) ↔ v = q := by
      intro v
      rw [← mem_T_iff x v, hq, Finset.mem_singleton]
    have hq0 : q ≠ 0 := ((hqiff q).2 rfl).1
    left
    refine ⟨q, hq0, ?_⟩
    apply eq_of_toAdd_eq
    intro v
    rw [toAdd_uOf1]
    by_cases hv0 : v = 0
    · rw [hv0, if_neg (fun h => h.1 rfl), hU0]
    · by_cases hvq : v = q
      · rw [if_neg (fun h => h.2 hvq)]
        exact ((hqiff v).2 hvq).2
      · rw [if_pos ⟨hv0, hvq⟩]
        have hne : Multiplicative.toAdd x v ≠ 0 := fun h0 => hvq ((hqiff v).1 ⟨hv0, h0⟩)
        exact H5_one_of_ne _ hne

private theorem disj12 : Disjoint O1set O2set := by
  rw [Set.disjoint_left]
  intro x h1 h2
  obtain ⟨q, hq, rfl⟩ := h1
  rw [O2set_eq] at h2
  obtain ⟨a, ha, h⟩ := h2
  have key : ∀ q a : V3, q ≠ 0 → a ≠ 0 →
      ∃ v : V3, (if v ≠ 0 ∧ ¬ (v = q) then (1 : ZMod 2) else 0) ≠ H5dot a v := by decide
  obtain ⟨v, hv⟩ := key q a hq ha
  apply hv
  have h3 := congrArg (fun F : PermV => Multiplicative.toAdd F v) h
  rw [toAdd_uOf1, toAdd_H5lin] at h3
  exact h3

private theorem disj13 : Disjoint O1set O3set := by
  rw [Set.disjoint_left]
  intro x h1 h2
  obtain ⟨q, hq, rfl⟩ := h1
  rw [O3set_eq] at h2
  obtain ⟨a, b, ha, hb, hab, h⟩ := h2
  have key : ∀ q a b : V3, q ≠ 0 → a ≠ 0 → b ≠ 0 → a ≠ b →
      ∃ v : V3, (if v ≠ 0 ∧ ¬ (v = q) then (1 : ZMod 2) else 0) ≠
        (if v = a ∨ v = b then 1 else 0) := by decide
  obtain ⟨v, hv⟩ := key q a b hq ha hb hab
  apply hv
  have h3 := congrArg (fun F : PermV => Multiplicative.toAdd F v) h
  rw [toAdd_uOf1, toAdd_pairV] at h3
  exact h3

private theorem disj14 : Disjoint O1set O4set := by
  rw [Set.disjoint_left]
  intro x h1 h2
  obtain ⟨q, hq, rfl⟩ := h1
  rw [O4set_eq] at h2
  obtain ⟨a, b, c, hD, h⟩ := h2
  have key : ∀ q a b c : V3, q ≠ 0 → D3 a b c ≠ 0 →
      ∃ v : V3, (if v ≠ 0 ∧ ¬ (v = q) then (1 : ZMod 2) else 0) ≠
        (if v ≠ 0 ∧ ¬ (v = a ∨ v = b ∨ v = c) then 1 else 0) := by decide
  obtain ⟨v, hv⟩ := key q a b c hq hD
  apply hv
  have h3 := congrArg (fun F : PermV => Multiplicative.toAdd F v) h
  rw [toAdd_uOf1, toAdd_uOf3] at h3
  exact h3

private theorem disj23 : Disjoint O2set O3set := by
  rw [Set.disjoint_left]
  intro x h1 h2
  rw [O2set_eq] at h1
  obtain ⟨a, ha, rfl⟩ := h1
  rw [O3set_eq] at h2
  obtain ⟨b, c, hb, hc, hbc, h⟩ := h2
  have key : ∀ a b c : V3, a ≠ 0 → b ≠ 0 → c ≠ 0 → b ≠ c →
      ∃ v : V3, H5dot a v ≠ (if v = b ∨ v = c then 1 else 0) := by decide
  obtain ⟨v, hv⟩ := key a b c ha hb hc hbc
  apply hv
  have h3 := congrArg (fun F : PermV => Multiplicative.toAdd F v) h
  rw [toAdd_H5lin, toAdd_pairV] at h3
  exact h3

private theorem disj24 : Disjoint O2set O4set := by
  rw [Set.disjoint_left]
  intro x h1 h2
  rw [O2set_eq] at h1
  obtain ⟨a, ha, rfl⟩ := h1
  rw [O4set_eq] at h2
  obtain ⟨b, c, d, hD, h⟩ := h2
  have key : ∀ a b c d : V3, a ≠ 0 → D3 b c d ≠ 0 →
      ∃ v : V3, H5dot a v ≠ (if v ≠ 0 ∧ ¬ (v = b ∨ v = c ∨ v = d) then 1 else 0) := by decide
  obtain ⟨v, hv⟩ := key a b c d ha hD
  apply hv
  have h3 := congrArg (fun F : PermV => Multiplicative.toAdd F v) h
  rw [toAdd_H5lin, toAdd_uOf3] at h3
  exact h3

private theorem disj34 : Disjoint O3set O4set := by
  rw [Set.disjoint_left]
  intro x h1 h2
  rw [O3set_eq] at h1
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := h1
  rw [O4set_eq] at h2
  obtain ⟨c, d, e, hD, h⟩ := h2
  have key : ∀ a b c d e : V3, a ≠ 0 → b ≠ 0 → a ≠ b → D3 c d e ≠ 0 →
      ∃ v : V3, (if v = a ∨ v = b then (1 : ZMod 2) else 0) ≠
        (if v ≠ 0 ∧ ¬ (v = c ∨ v = d ∨ v = e) then 1 else 0) := by decide +kernel
  obtain ⟨v, hv⟩ := key a b c d e ha hb hab hD
  apply hv
  have h3 := congrArg (fun F : PermV => Multiplicative.toAdd F v) h
  rw [toAdd_pairV, toAdd_uOf3] at h3
  exact h3

private theorem Oset_disjoint (i j : Fin 4) (h : i ≠ j) : Disjoint (Oset i) (Oset j) := by
  fin_cases i <;> fin_cases j
  · exact absurd rfl h
  · exact disj12
  · exact disj13
  · exact disj14
  · exact disj12.symm
  · exact absurd rfl h
  · exact disj23
  · exact disj24
  · exact disj13.symm
  · exact disj23.symm
  · exact absurd rfl h
  · exact disj34
  · exact disj14.symm
  · exact disj24.symm
  · exact disj34.symm
  · exact absurd rfl h

private theorem gl_mulVec_injective (g : GL (Fin 3) (ZMod 2)) {a b : V3}
    (h : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec a =
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec b) : a = b := by
  have := congrArg ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec h
  rwa [inv_mulVec_mulVec, inv_mulVec_mulVec] at this

private theorem O1_inv (q : V3) (hq : q ≠ 0) (g : GL (Fin 3) (ZMod 2)) :
    gl3Act g (uOf ({q} : Set V3)) ∈ O1set :=
  ⟨_, fun h => hq ((gl_mulVec_zero_iff g q).1 h), gl3Act_uOf_singleton g q⟩

private theorem O2_inv' (x : PermV) (hx : x ∈ O2set) (g : GL (Fin 3) (ZMod 2)) :
    gl3Act g x ∈ O2set := by
  rw [O2set_eq] at hx ⊢
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨H5dualVec g a, H5dualVec_ne_zero g ha, gl3Act_H5lin g a⟩

private theorem O3_inv' (x : PermV) (hx : x ∈ O3set) (g : GL (Fin 3) (ZMod 2)) :
    gl3Act g x ∈ O3set := by
  rw [O3set_eq] at hx ⊢
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hx
  exact ⟨_, _, fun h => ha ((gl_mulVec_zero_iff g a).1 h),
    fun h => hb ((gl_mulVec_zero_iff g b).1 h), fun h => hab (gl_mulVec_injective g h),
    gl3Act_pairV g a b⟩

private theorem O4_inv' (x : PermV) (hx : x ∈ O4set) (g : GL (Fin 3) (ZMod 2)) :
    gl3Act g x ∈ O4set := by
  rw [O4set_eq] at hx ⊢
  obtain ⟨a, b, c, hD, rfl⟩ := hx
  exact ⟨_, _, _, by rw [D3_gl]; exact hD, gl3Act_uOf_triple g a b c⟩

private theorem Oset_inv (i : Fin 4) (x : PermV) (hx : x ∈ Oset i) (g : GL (Fin 3) (ZMod 2)) :
    gl3Act g x ∈ Oset i := by
  fin_cases i
  · obtain ⟨q, hq, rfl⟩ := hx
    exact O1_inv q hq g
  · exact O2_inv' x hx g
  · exact O3_inv' x hx g
  · exact O4_inv' x hx g

private theorem O1_trans' (x y : PermV) (hx : x ∈ O1set) (hy : y ∈ O1set) :
    ∃ g : GL (Fin 3) (ZMod 2), gl3Act g x = y := by
  obtain ⟨q, hq, rfl⟩ := hx
  obtain ⟨q', hq', rfl⟩ := hy
  exact trans_O1 q q' hq hq'

private theorem O2_trans' (x y : PermV) (hx : x ∈ O2set) (hy : y ∈ O2set) :
    ∃ g : GL (Fin 3) (ZMod 2), gl3Act g x = y := by
  rw [O2set_eq] at hx hy
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  exact trans_O2 a b ha hb

private theorem O3_trans' (x y : PermV) (hx : x ∈ O3set) (hy : y ∈ O3set) :
    ∃ g : GL (Fin 3) (ZMod 2), gl3Act g x = y := by
  rw [O3set_eq] at hx hy
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hx
  obtain ⟨a', b', ha', hb', hab', rfl⟩ := hy
  exact trans_O3 a b a' b' ha hb hab ha' hb' hab'

private theorem O4_trans' (x y : PermV) (hx : x ∈ O4set) (hy : y ∈ O4set) :
    ∃ g : GL (Fin 3) (ZMod 2), gl3Act g x = y := by
  rw [O4set_eq] at hx hy
  obtain ⟨a, b, c, hD, rfl⟩ := hx
  obtain ⟨a', b', c', hD', rfl⟩ := hy
  exact trans_O4 a b c a' b' c' hD hD'

private theorem Oset_trans (i : Fin 4) (x y : PermV) (hx : x ∈ Oset i) (hy : y ∈ Oset i) :
    ∃ g : GL (Fin 3) (ZMod 2), gl3Act g x = y := by
  fin_cases i
  · exact O1_trans' x y hx hy
  · exact O2_trans' x y hx hy
  · exact O3_trans' x y hx hy
  · exact O4_trans' x y hx hy

private def H5linHom : Multiplicative V3 →* PermV where
  toFun a := H5lin (Multiplicative.toAdd a)
  map_one' := by
    show H5lin (Multiplicative.toAdd 1) = 1
    rw [toAdd_one, H5lin_zero]
  map_mul' a b := by
    show H5lin (Multiplicative.toAdd (a * b)) =
      H5lin (Multiplicative.toAdd a) * H5lin (Multiplicative.toAdd b)
    rw [toAdd_mul, H5lin_mul]

private theorem H5linHom_injective : Function.Injective H5linHom := by
  intro a b h
  exact Multiplicative.toAdd.injective (H5lin_inj h)

private theorem H5linHom_apply (a : Multiplicative V3) :
    H5linHom a = H5lin (Multiplicative.toAdd a) := rfl

private def H5W : Subgroup PermV := H5linHom.range

private theorem H5W_coe : (H5W : Set PermV) = {1} ∪ O2set := by
  ext x
  rw [SetLike.mem_coe, H5W, MonoidHom.mem_range, Set.mem_union, Set.mem_singleton_iff, O2set_eq]
  constructor
  · rintro ⟨a, rfl⟩
    by_cases ha : Multiplicative.toAdd a = 0
    · left
      rw [H5linHom_apply, ha, H5lin_zero]
    · right
      exact ⟨Multiplicative.toAdd a, ha, rfl⟩
  · rintro (rfl | ⟨a, ha, rfl⟩)
    · exact ⟨1, by rw [H5linHom_apply, toAdd_one, H5lin_zero]⟩
    · exact ⟨Multiplicative.ofAdd a, by rw [H5linHom_apply, toAdd_ofAdd]⟩

private theorem H5W_le_Ucore : H5W ≤ Ucore := by
  intro x hx
  have hx' : x ∈ ({1} ∪ O2set : Set PermV) := by
    rw [← H5W_coe]; exact hx
  rcases hx' with h | h
  · rw [Set.mem_singleton_iff] at h
    rw [h]
    exact one_mem _
  · exact (O2_ucore x h).1

private theorem H5W_inv (g : GL (Fin 3) (ZMod 2)) (z : PermV) (hz : z ∈ H5W) :
    gl3Act g z ∈ H5W := by
  obtain ⟨a, rfl⟩ := hz
  refine ⟨Multiplicative.ofAdd (H5dualVec g (Multiplicative.toAdd a)), ?_⟩
  rw [H5linHom_apply, H5linHom_apply, toAdd_ofAdd, gl3Act_H5lin]

private theorem sum_reindex {M : Type*} [AddCommMonoid M] (h : GL (Fin 3) (ZMod 2))
    (F : V3 → M) :
    ∑ v : V3, F ((h : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v) = ∑ v : V3, F v := by
  refine Fintype.sum_bijective (fun v : V3 => (h : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v)
    ⟨fun x y hxy => gl_mulVec_injective h hxy, fun w =>
      ⟨((h⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w,
        mulVec_inv_mulVec h w⟩⟩ _ _ (fun v => rfl)

private def H5eps (u : PermV) : V3 := ∑ v : V3, Multiplicative.toAdd u v • v

private theorem H5eps_mul (u u' : PermV) : H5eps (u * u') = H5eps u + H5eps u' := by
  unfold H5eps
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [toAdd_mul, Pi.add_apply, add_smul]

private theorem H5eps_one : H5eps 1 = 0 := by
  unfold H5eps
  simp [toAdd_one]

private theorem H5eps_gl (g : GL (Fin 3) (ZMod 2)) (u : PermV) :
    H5eps (gl3Act g u) = (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec (H5eps u) := by
  unfold H5eps
  simp only [gl3Act_toAdd]
  rw [← sum_reindex g]
  simp only [inv_mulVec_mulVec]
  rw [Matrix.mulVec_sum]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [Matrix.mulVec_smul]

private theorem H5eps_pairV (x y : V3) (hxy : x ≠ y) : H5eps (pairV x y) = x + y := by
  unfold H5eps
  rw [Fintype.sum_eq_add x y hxy]
  · simp [toAdd_pairV]
  · intro z hz
    simp [toAdd_pairV, hz.1, hz.2]

private theorem H5eps_H5lin (a : V3) : H5eps (H5lin a) = 0 := by
  have key : ∀ a : V3, ∑ v : V3, H5dot a v • v = 0 := by decide
  unfold H5eps
  simp only [toAdd_H5lin]
  exact key a

private theorem H5_zmod2_cases : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide

private theorem functional_of_eps (u : PermV) (hU : u ∈ Ucore) (he : H5eps u = 0) : u ∈ H5W := by
  obtain ⟨h0, hsum⟩ := mem_Ucore'.1 hU
  have he' : ∑ v : V3, Multiplicative.toAdd u v • v = 0 := he
  rw [sum_V3] at hsum he'
  have hz : Multiplicative.toAdd u ![0, 0, 0] = 0 := by
    have e0 : (![0, 0, 0] : V3) = 0 := by
      funext i
      fin_cases i <;> rfl
    rw [e0]
    exact h0
  have hc0 := congrFun he' 0
  have hc1 := congrFun he' 1
  have hc2 := congrFun he' 2
  simp at hc0 hc1 hc2
  have bits : ∀ p q r b c d e : ZMod 2, p + q + r + b + c + d + e = 0 → p + b + c + e = 0 →
      q + b + d + e = 0 → r + c + d + e = 0 →
      b = p + q ∧ c = p + r ∧ d = q + r ∧ e = p + q + r := by decide
  obtain ⟨F1, F2, F3, F4⟩ := bits (Multiplicative.toAdd u ![1, 0, 0])
    (Multiplicative.toAdd u ![0, 1, 0]) (Multiplicative.toAdd u ![0, 0, 1])
    (Multiplicative.toAdd u ![1, 1, 0]) (Multiplicative.toAdd u ![1, 0, 1])
    (Multiplicative.toAdd u ![0, 1, 1]) (Multiplicative.toAdd u ![1, 1, 1])
    (by linear_combination hsum - hz) (by linear_combination hc0)
    (by linear_combination hc1) (by linear_combination hc2)
  refine ⟨Multiplicative.ofAdd ![Multiplicative.toAdd u ![1, 0, 0],
    Multiplicative.toAdd u ![0, 1, 0], Multiplicative.toAdd u ![0, 0, 1]], ?_⟩
  rw [H5linHom_apply, toAdd_ofAdd]
  apply Multiplicative.toAdd.injective
  funext v
  rw [toAdd_H5lin]
  have hall : ∀ x y z : ZMod 2, Multiplicative.toAdd u ![x, y, z] =
      H5dot ![Multiplicative.toAdd u ![1, 0, 0], Multiplicative.toAdd u ![0, 1, 0],
        Multiplicative.toAdd u ![0, 0, 1]] ![x, y, z] := by
    intro x y z
    obtain rfl | rfl := H5_zmod2_cases x
    all_goals obtain rfl | rfl := H5_zmod2_cases y
    all_goals obtain rfl | rfl := H5_zmod2_cases z
    all_goals simp [H5dot, hz, F1, F2, F3, F4]
  have hv : v = ![v 0, v 1, v 2] := by
    funext i
    fin_cases i <;> rfl
  have := hall (v 0) (v 1) (v 2)
  rw [← hv] at this
  exact this.symm

private theorem Ucore_inv (g : GL (Fin 3) (ZMod 2)) (u : PermV) (hu : u ∈ Ucore) :
    gl3Act g u ∈ Ucore := by
  obtain ⟨h0, hs⟩ := mem_Ucore'.1 hu
  rw [mem_Ucore']
  refine ⟨by rw [gl3Act_toAdd, Matrix.mulVec_zero]; exact h0, ?_⟩
  simp only [gl3Act_toAdd]
  rw [sum_mulVec_eq (g⁻¹) (fun v => Multiplicative.toAdd u v)]
  exact hs

private theorem exists_pair_sum : ∀ w : V3, w ≠ 0 →
    ∃ x y : V3, x ≠ 0 ∧ y ≠ 0 ∧ x ≠ y ∧ x + y = w := by
  decide

private def H5Uhom : Ucore →* Multiplicative V3 where
  toFun u := Multiplicative.ofAdd (H5eps (u : PermV))
  map_one' := by
    show Multiplicative.ofAdd (H5eps 1) = 1
    rw [H5eps_one]
    rfl
  map_mul' u u' := by
    show Multiplicative.ofAdd (H5eps ((u : PermV) * (u' : PermV))) =
      Multiplicative.ofAdd (H5eps u) * Multiplicative.ofAdd (H5eps u')
    rw [H5eps_mul]
    rfl

private theorem H5W_iso : IsoSec gl3Act H5W ⊥ (Multiplicative V3) modDual := by
  refine ⟨bot_le, ?_, ?_, (MonoidHom.ofInjective H5linHom_injective).symm.toMonoidHom,
    (MonoidHom.ofInjective H5linHom_injective).symm.surjective, ?_, ?_⟩
  · intro g u hu
    obtain ⟨a, ha⟩ := hu
    refine ⟨Multiplicative.ofAdd (H5dualVec g (Multiplicative.toAdd a)), ?_⟩
    rw [← ha, H5linHom_apply, H5linHom_apply, toAdd_ofAdd]
    exact (gl3Act_H5lin g _).symm
  · intro g z hz
    rw [Subgroup.mem_bot] at hz
    rw [hz, MulEquiv.map_one]
    exact Subgroup.one_mem _
  · intro u
    show (MonoidHom.ofInjective H5linHom_injective).symm u = 1 ↔ (u : PermV) ∈ (⊥ : Subgroup PermV)
    rw [Subgroup.mem_bot]
    constructor
    · intro h
      have hu1 : u = 1 := by
        apply (MonoidHom.ofInjective H5linHom_injective).symm.injective
        rw [h]
        exact (MulEquiv.map_one _).symm
      rw [hu1]
      rfl
    · intro h
      have hu1 : u = 1 := Subtype.ext h
      rw [hu1]
      exact MulEquiv.map_one _
  · intro g u u' h
    show (MonoidHom.ofInjective H5linHom_injective).symm u' =
      modDual g ((MonoidHom.ofInjective H5linHom_injective).symm u)
    have hu : (u : PermV) =
        H5lin (Multiplicative.toAdd ((MonoidHom.ofInjective H5linHom_injective).symm u)) := by
      have := congrArg Subtype.val ((MonoidHom.ofInjective H5linHom_injective).apply_symm_apply u)
      rw [MonoidHom.ofInjective_apply, H5linHom_apply] at this
      exact this.symm
    have key : (MonoidHom.ofInjective H5linHom_injective) (modDual g
        ((MonoidHom.ofInjective H5linHom_injective).symm u)) = u' := by
      apply Subtype.ext
      rw [MonoidHom.ofInjective_apply, H5linHom_apply]
      show H5lin (Multiplicative.toAdd
        (modDual g ((MonoidHom.ofInjective H5linHom_injective).symm u)))
        = (u' : PermV)
      rw [show Multiplicative.toAdd
          (modDual g ((MonoidHom.ofInjective H5linHom_injective).symm u)) =
        H5dualVec g (Multiplicative.toAdd ((MonoidHom.ofInjective H5linHom_injective).symm u))
        from rfl, ← gl3Act_H5lin, ← hu, h]
      rfl
    rw [← key, MulEquiv.symm_apply_apply]

private theorem H5U_iso : IsoSec gl3Act Ucore H5W (Multiplicative V3) modNat := by
  refine ⟨H5W_le_Ucore, fun g u hu => Ucore_inv g u hu, fun g z hz => H5W_inv g z hz,
    H5Uhom, ?_, ?_, ?_⟩
  · intro w
    by_cases hw : Multiplicative.toAdd w = 0
    · refine ⟨1, ?_⟩
      show Multiplicative.ofAdd (H5eps 1) = w
      apply Multiplicative.toAdd.injective
      rw [toAdd_ofAdd, H5eps_one, hw]
    · obtain ⟨x, y, hx, hy, hxy, hsum⟩ := exists_pair_sum _ hw
      have hmem : pairV x y ∈ Ucore := (O3_ucore (pairV x y) (by
        rw [O3set_eq]; exact ⟨x, y, hx, hy, hxy, rfl⟩)).1
      refine ⟨⟨pairV x y, hmem⟩, ?_⟩
      show Multiplicative.ofAdd (H5eps (pairV x y)) = w
      apply Multiplicative.toAdd.injective
      rw [toAdd_ofAdd, H5eps_pairV x y hxy, hsum]
  · intro u
    show Multiplicative.ofAdd (H5eps u.1) = 1 ↔ (u : PermV) ∈ H5W
    constructor
    · intro h
      exact functional_of_eps u.1 u.2 (ofAdd_eq_one.1 h)
    · intro h
      obtain ⟨a, ha⟩ := h
      rw [← ha, H5linHom_apply, H5eps_H5lin]
      rfl
  · intro g u u' h
    show Multiplicative.ofAdd (H5eps u'.1) = modNat g (Multiplicative.ofAdd (H5eps u.1))
    have h2 : H5eps u'.1 = (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec (H5eps u.1) := by
      rw [h]
      exact H5eps_gl g u.1
    rw [h2]
    rfl

private theorem uOf_triple_mul (a b c d : V3) (hD : D3 a b c ≠ 0) (hD' : D3 a b d ≠ 0)
    (hcd : c ≠ d) : uOf ({a, b, c} : Set V3) * uOf ({a, b, d} : Set V3) = pairV c d := by
  apply eq_of_toAdd_eq
  intro v
  rw [toAdd_mul, Pi.add_apply, toAdd_uOf3, toAdd_uOf3, toAdd_pairV]
  have key : ∀ a b c d v : V3, D3 a b c ≠ 0 → D3 a b d ≠ 0 → c ≠ d →
      (if v ≠ 0 ∧ ¬ (v = a ∨ v = b ∨ v = c) then (1 : ZMod 2) else 0) +
        (if v ≠ 0 ∧ ¬ (v = a ∨ v = b ∨ v = d) then 1 else 0) =
      if v = c ∨ v = d then 1 else 0 := by
    decide +kernel
  exact key a b c d v hD hD' hcd

private theorem H5lin_decomp : ∀ α : V3, α ≠ 0 →
    ∃ a b c d : V3, (a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧ c ≠ 0 ∧ d ≠ 0 ∧ c ≠ d) ∧
      H5lin α = pairV a b * pairV c d := by
  decide +kernel

private theorem O3_mem_of_pair (a b : V3) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    pairV a b ∈ O3set := by
  rw [O3set_eq]
  exact ⟨a, b, ha, hb, hab, rfl⟩

private theorem O3_sub_of_O3 (N : Subgroup PermV)
    (hN : ∀ g : GL (Fin 3) (ZMod 2), ∀ n ∈ N, gl3Act g n ∈ N)
    (x : PermV) (hx : x ∈ N) (hxO : x ∈ O3set) : ∀ y ∈ O3set, y ∈ N := by
  intro y hy
  obtain ⟨g, rfl⟩ := O3_trans' x y hxO hy
  exact hN g x hx

private theorem O2_sub (N : Subgroup PermV)
    (hN : ∀ g : GL (Fin 3) (ZMod 2), ∀ n ∈ N, gl3Act g n ∈ N)
    (x : PermV) (hx : x ∈ N) (hxO : x ∈ O2set) : ∀ y ∈ O2set, y ∈ N := by
  intro y hy
  obtain ⟨g, rfl⟩ := O2_trans' x y hxO hy
  exact hN g x hx

private theorem H5W_le_of_O3 (N : Subgroup PermV) (hO3 : ∀ y ∈ O3set, y ∈ N) : H5W ≤ N := by
  intro w hw
  have hw' : w ∈ ({1} ∪ O2set : Set PermV) := by
    rw [← H5W_coe]
    exact hw
  rcases hw' with h | h
  · rw [Set.mem_singleton_iff] at h
    rw [h]
    exact one_mem _
  · rw [O2set_eq] at h
    obtain ⟨α, hα, rfl⟩ := h
    obtain ⟨a, b, c, d, ⟨ha, hb, hab, hc, hd, hcd⟩, hdec⟩ := H5lin_decomp α hα
    rw [hdec]
    exact N.mul_mem (hO3 _ (O3_mem_of_pair a b ha hb hab)) (hO3 _ (O3_mem_of_pair c d hc hd hcd))

private theorem H5W_le_of_O2 (N : Subgroup PermV) (h2 : ∀ y ∈ O2set, y ∈ N) : H5W ≤ N := by
  intro w hw
  have hw' : w ∈ ({1} ∪ O2set : Set PermV) := by
    rw [← H5W_coe]
    exact hw
  rcases hw' with h | h
  · rw [Set.mem_singleton_iff] at h
    rw [h]
    exact one_mem _
  · exact h2 w h

private theorem O3_sub_of_O1 (N : Subgroup PermV)
    (hN : ∀ g : GL (Fin 3) (ZMod 2), ∀ n ∈ N, gl3Act g n ∈ N)
    (q : V3) (hq : q ≠ 0) (hx : uOf ({q} : Set V3) ∈ N) : ∀ y ∈ O3set, y ∈ N := by
  have key : ∀ q : V3, q ≠ 0 → ∃ q' : V3, q' ≠ 0 ∧ q' ≠ q := by decide
  obtain ⟨q', hq'0, hq'q⟩ := key q hq
  obtain ⟨g, hg⟩ := trans_O1 q q' hq hq'0
  have hy : uOf ({q'} : Set V3) ∈ N := by
    rw [← hg]
    exact hN g _ hx
  have hpair : pairV q q' ∈ N := by
    rw [← uOf_pt_mul_uOf_pt q q' hq hq'0 (Ne.symm hq'q)]
    exact N.mul_mem hx hy
  intro y hy3
  rw [O3set_eq] at hy3
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hy3
  obtain ⟨g', hg'⟩ := trans_O3 q q' a b hq hq'0 (Ne.symm hq'q) ha hb hab
  rw [← hg']
  exact hN g' _ hpair

private theorem O3_sub_of_O4 (N : Subgroup PermV)
    (hN : ∀ g : GL (Fin 3) (ZMod 2), ∀ n ∈ N, gl3Act g n ∈ N)
    (a b c : V3) (hD : D3 a b c ≠ 0) (hx : uOf ({a, b, c} : Set V3) ∈ N) :
    ∀ y ∈ O3set, y ∈ N := by
  have key : ∀ a b c : V3, D3 a b c ≠ 0 → ∃ d : V3, D3 a b d ≠ 0 ∧ d ≠ c := by decide
  obtain ⟨d, hd, hdc⟩ := key a b c hD
  obtain ⟨g, h1, h2, h3⟩ := gl_map_bases a b c a b d (by rw [basisM_det]; exact hD)
    (by rw [basisM_det]; exact hd)
  have hgt : gl3Act g (uOf ({a, b, c} : Set V3)) = uOf ({a, b, d} : Set V3) := by
    rw [gl3Act_uOf_triple, h1, h2, h3]
  have hy : uOf ({a, b, d} : Set V3) ∈ N := by
    rw [← hgt]
    exact hN g _ hx
  have hpair : pairV c d ∈ N := by
    rw [← uOf_triple_mul a b c d hD hd (Ne.symm hdc)]
    exact N.mul_mem hx hy
  have hc0 : c ≠ 0 := (D3_nonzero a b c hD).2.2.1
  have hd0 : d ≠ 0 := (D3_nonzero a b d hd).2.2.1
  intro y hy3
  rw [O3set_eq] at hy3
  obtain ⟨a', b', ha', hb', hab', rfl⟩ := hy3
  obtain ⟨g', hg'⟩ := trans_O3 c d a' b' hc0 hd0 (Ne.symm hdc) ha' hb' hab'
  rw [← hg']
  exact hN g' _ hpair

private theorem H5W_le_of_inv (N : Subgroup PermV) (hNU : N ≤ Ucore)
    (hN : ∀ g : GL (Fin 3) (ZMod 2), ∀ n ∈ N, gl3Act g n ∈ N) (hne : N ≠ ⊥) : H5W ≤ N := by
  obtain ⟨⟨x, hxN⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hxU : x ∈ Ucore := hNU hxN
  rcases cover_Ucore x hxU hx1' with h1 | h2 | h3 | h4
  · obtain ⟨q, hq, hxq⟩ := h1
    apply H5W_le_of_O3
    apply O3_sub_of_O1 N hN q hq
    rw [← hxq]
    exact hxN
  · exact H5W_le_of_O2 N (O2_sub N hN x hxN h2)
  · exact H5W_le_of_O3 N (O3_sub_of_O3 N hN x hxN h3)
  · rw [O4set_eq] at h4
    obtain ⟨a, b, c, hD, hxe⟩ := h4
    apply H5W_le_of_O3
    apply O3_sub_of_O4 N hN a b c hD
    rw [← hxe]
    exact hxN

private theorem H5_indecomposable (A B : Subgroup PermV) (hA : A ≤ Ucore) (hB : B ≤ Ucore)
    (hAi : ∀ g : GL (Fin 3) (ZMod 2), ∀ a ∈ A, gl3Act g a ∈ A)
    (hBi : ∀ g : GL (Fin 3) (ZMod 2), ∀ b ∈ B, gl3Act g b ∈ B)
    (hinf : A ⊓ B = ⊥) : A = ⊥ ∨ B = ⊥ := by
  by_contra hcon
  push Not at hcon
  have hW0 : H5W ≤ A ⊓ B := le_inf (H5W_le_of_inv A hA hAi hcon.1) (H5W_le_of_inv B hB hBi hcon.2)
  rw [hinf, le_bot_iff] at hW0
  have hmem : H5lin (![1, 0, 0] : V3) ∈ H5W := ⟨Multiplicative.ofAdd ![1, 0, 0], by
    rw [H5linHom_apply, toAdd_ofAdd]⟩
  rw [hW0] at hmem
  exact H5lin_ne_one (by decide) (Subgroup.mem_bot.1 hmem)

private theorem H5W_irred : IsIrredOn gl3Act.range H5W := by
  refine ⟨?_, ?_⟩
  · intro h
    have hmem : H5lin (![1, 0, 0] : V3) ∈ H5W := ⟨Multiplicative.ofAdd ![1, 0, 0], by
      rw [H5linHom_apply, toAdd_ofAdd]⟩
    rw [h] at hmem
    exact H5lin_ne_one (by decide) (Subgroup.mem_bot.1 hmem)
  · intro M hM hMinv
    by_cases hM0 : M = ⊥
    · exact Or.inl hM0
    · right
      apply le_antisymm hM
      exact H5W_le_of_inv M (hM.trans H5W_le_Ucore) (fun g n hn =>
        hMinv (gl3Act g) ⟨g, rfl⟩ n hn) hM0

private theorem H5W_socle : H5W = ⨆ (N : Subgroup PermV) (_ : N ≤ Ucore)
    (_ : ∀ g : GL (Fin 3) (ZMod 2), ∀ n ∈ N, gl3Act g n ∈ N)
    (_ : IsIrredOn gl3Act.range N), N := by
  apply le_antisymm
  · refine le_iSup_of_le H5W (le_iSup_of_le H5W_le_Ucore (le_iSup_of_le ?_
      (le_iSup_of_le H5W_irred le_rfl)))
    intro g n hn
    exact H5W_inv g n hn
  · refine iSup_le fun N => iSup_le fun hNU => iSup_le fun hNi => iSup_le fun hNirr => ?_
    have hWN : H5W ≤ N := H5W_le_of_inv N hNU hNi hNirr.1
    have hWinv : ∀ l ∈ gl3Act.range, ∀ u ∈ H5W, l u ∈ H5W := by
      intro l hl u hu
      obtain ⟨g, rfl⟩ := hl
      exact H5W_inv g u hu
    rcases hNirr.2 H5W hWN hWinv with h | h
    · exact absurd h H5W_irred.1
    · exact h.symm ▸ le_rfl

private theorem S0_card : (Finset.univ.erase (0 : V3)).card = 7 := by decide

private theorem H5lin_injective : Function.Injective H5lin := fun _ _ h => H5lin_inj h

private theorem uOf_pt_inj {q q' : V3} (hq : q ≠ 0) (hq' : q' ≠ 0)
    (h : uOf ({q} : Set V3) = uOf ({q'} : Set V3)) : q = q' := by
  by_contra hne
  have h1 : Multiplicative.toAdd (uOf ({q} : Set V3)) q =
      Multiplicative.toAdd (uOf ({q'} : Set V3)) q := by rw [h]
  rw [toAdd_uOf1, toAdd_uOf1, if_neg (fun hh => hh.2 rfl), if_pos ⟨hq, hne⟩] at h1
  exact zero_ne_one h1

private theorem ncard_O1 : O1set.ncard = 7 := by
  have hset : O1set = (fun q : V3 => uOf ({q} : Set V3)) '' ↑(Finset.univ.erase (0 : V3)) := by
    ext x
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q, Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hq, Finset.mem_univ _⟩), rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q, (Finset.mem_erase.1 (Finset.mem_coe.1 hq)).1, rfl⟩
  have hinj : Set.InjOn (fun q : V3 => uOf ({q} : Set V3)) ↑(Finset.univ.erase (0 : V3)) := by
    intro q hq q' hq' h
    exact uOf_pt_inj (Finset.mem_erase.1 (Finset.mem_coe.1 hq)).1
      (Finset.mem_erase.1 (Finset.mem_coe.1 hq')).1 h
  rw [hset, Set.InjOn.ncard_image hinj, Set.ncard_coe_finset, S0_card]

private theorem ncard_O2 : O2set.ncard = 7 := by
  have hset : O2set = H5lin '' ↑(Finset.univ.erase (0 : V3)) := by
    ext x
    rw [O2set_eq]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, Finset.mem_coe.2 (Finset.mem_erase.2 ⟨ha, Finset.mem_univ _⟩), rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, (Finset.mem_erase.1 (Finset.mem_coe.1 ha)).1, rfl⟩
  rw [hset, Set.ncard_image_of_injective _ H5lin_injective, Set.ncard_coe_finset, S0_card]

private def indV (s : Finset V3) : PermV :=
  Multiplicative.ofAdd fun v => if v ∈ s then (1 : ZMod 2) else 0

private theorem toAdd_indV (s : Finset V3) (v : V3) :
    Multiplicative.toAdd (indV s) v = if v ∈ s then 1 else 0 := rfl

private theorem indV_injective : Function.Injective indV := by
  intro s t h
  ext v
  have h1 := congrArg (fun F : PermV => Multiplicative.toAdd F v) h
  simp only [toAdd_indV] at h1
  by_cases hs : v ∈ s
  · rw [if_pos hs] at h1
    by_cases ht : v ∈ t
    · exact ⟨fun _ => ht, fun _ => hs⟩
    · rw [if_neg ht] at h1
      exact absurd h1 one_ne_zero
  · rw [if_neg hs] at h1
    by_cases ht : v ∈ t
    · rw [if_pos ht] at h1
      exact absurd h1.symm one_ne_zero
    · exact ⟨fun hh => absurd hh hs, fun hh => absurd hh ht⟩

private theorem O3set_image : O3set = indV '' ↑((Finset.univ.erase (0 : V3)).powersetCard 2) := by
  ext x
  rw [O3set_eq]
  constructor
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    refine ⟨{a, b}, ?_, ?_⟩
    · rw [Finset.mem_coe, Finset.mem_powersetCard]
      refine ⟨?_, Finset.card_pair hab⟩
      intro v hv
      rw [Finset.mem_insert, Finset.mem_singleton] at hv
      rw [Finset.mem_erase]
      rcases hv with rfl | rfl
      · exact ⟨ha, Finset.mem_univ _⟩
      · exact ⟨hb, Finset.mem_univ _⟩
    · apply eq_of_toAdd_eq
      intro v
      rw [toAdd_indV, toAdd_pairV]
      simp
  · rintro ⟨s, hs, rfl⟩
    rw [Finset.mem_coe, Finset.mem_powersetCard] at hs
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hs.2
    have ha : a ≠ 0 := (Finset.mem_erase.1 (hs.1 (Finset.mem_insert_self a _))).1
    have hb : b ≠ 0 :=
      (Finset.mem_erase.1 (hs.1 (Finset.mem_insert_of_mem (Finset.mem_singleton_self b)))).1
    refine ⟨a, b, ha, hb, hab, ?_⟩
    apply eq_of_toAdd_eq
    intro v
    rw [toAdd_indV, toAdd_pairV]
    simp

private theorem ncard_O3 : O3set.ncard = 21 := by
  rw [O3set_image, Set.ncard_image_of_injective _ indV_injective, Set.ncard_coe_finset,
    Finset.card_powersetCard, S0_card]
  rfl

private theorem uOf_finset_inj {s t : Finset V3} (hs : ∀ v ∈ s, v ≠ 0) (ht : ∀ v ∈ t, v ≠ 0)
    (h : uOf (↑s : Set V3) = uOf (↑t : Set V3)) : s = t := by
  ext v
  by_cases hv0 : v = 0
  · constructor
    · intro h1
      exact absurd hv0 (hs v h1)
    · intro h1
      exact absurd hv0 (ht v h1)
  · have h1 := congrArg (fun F : PermV => Multiplicative.toAdd F v) h
    unfold uOf at h1
    simp only [toAdd_ofAdd, Finset.mem_coe] at h1
    by_cases hvs : v ∈ s
    · rw [if_neg (fun hh => hh.2 hvs)] at h1
      by_cases hvt : v ∈ t
      · exact ⟨fun _ => hvt, fun _ => hvs⟩
      · rw [if_pos ⟨hv0, hvt⟩] at h1
        exact absurd h1.symm one_ne_zero
    · rw [if_pos ⟨hv0, hvs⟩] at h1
      by_cases hvt : v ∈ t
      · rw [if_neg (fun hh => hh.2 hvt)] at h1
        exact absurd h1 one_ne_zero
      · exact ⟨fun hh => absurd hh hvs, fun hh => absurd hh hvt⟩

private def F4 : Finset (Finset V3) :=
  ((Finset.univ.erase (0 : V3)).powersetCard 3).filter (fun s =>
    ∀ x ∈ s, ∀ y ∈ s, ∀ z ∈ s, x ≠ y → x ≠ z → y ≠ z → D3 x y z ≠ 0)

private theorem card_F4 : F4.card = 28 := by
  decide +kernel

private theorem D3_on_triple : ∀ a b c : V3, D3 a b c ≠ 0 →
    ∀ x ∈ ({a, b, c} : Finset V3), ∀ y ∈ ({a, b, c} : Finset V3),
      ∀ z ∈ ({a, b, c} : Finset V3), x ≠ y → x ≠ z → y ≠ z → D3 x y z ≠ 0 := by
  decide +kernel

private theorem O4set_image :
    O4set = (fun s : Finset V3 => uOf (↑s : Set V3)) '' ↑F4 := by
  ext x
  rw [O4set_eq]
  constructor
  · rintro ⟨a, b, c, hD, rfl⟩
    obtain ⟨ha, hb, hc, hab, hac, hbc⟩ := D3_nonzero a b c hD
    refine ⟨{a, b, c}, ?_, ?_⟩
    · rw [Finset.mem_coe, F4, Finset.mem_filter, Finset.mem_powersetCard]
      refine ⟨⟨?_, Finset.card_eq_three.2 ⟨a, b, c, hab, hac, hbc, rfl⟩⟩, ?_⟩
      · intro v hv
        rw [Finset.mem_erase]
        rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl | rfl
        · exact ⟨ha, Finset.mem_univ _⟩
        · exact ⟨hb, Finset.mem_univ _⟩
        · exact ⟨hc, Finset.mem_univ _⟩
      · exact D3_on_triple a b c hD
    · simp only [Finset.coe_insert, Finset.coe_singleton]
  · rintro ⟨s, hs, rfl⟩
    rw [Finset.mem_coe, F4, Finset.mem_filter, Finset.mem_powersetCard] at hs
    obtain ⟨⟨hsub, hcard⟩, hind⟩ := hs
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.1 hcard
    have hD : D3 a b c ≠ 0 := hind a (by simp) b (by simp) c (by simp) hab hac hbc
    refine ⟨a, b, c, hD, ?_⟩
    simp only [Finset.coe_insert, Finset.coe_singleton]

private theorem ncard_O4 : O4set.ncard = 28 := by
  have hsub : ∀ u ∈ F4, ∀ v ∈ u, v ≠ 0 := by
    intro u hu v hv
    rw [F4, Finset.mem_filter, Finset.mem_powersetCard] at hu
    exact (Finset.mem_erase.1 (hu.1.1 hv)).1
  have hinj : Set.InjOn (fun s : Finset V3 => uOf (↑s : Set V3)) ↑F4 := by
    intro s hs t ht h
    exact uOf_finset_inj (hsub s (Finset.mem_coe.1 hs)) (hsub t (Finset.mem_coe.1 ht)) h
  rw [O4set_image, Set.InjOn.ncard_image hinj, Set.ncard_coe_finset, card_F4]

private theorem H5_counts : O1set.ncard = 7 ∧ O2set.ncard = 7 ∧ O3set.ncard = 21 ∧
    O4set.ncard = 28 :=
  ⟨ncard_O1, ncard_O2, ncard_O3, ncard_O4⟩

end H5Lin

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
private theorem H52_line_key : ∀ a b c q : V3, a ≠ 0 → b ≠ 0 → c ≠ 0 → a ≠ b → c ≠ a → c ≠ b →
    q ≠ 0 → H5dot a q = 0 → H5dot b q = 0 → H5dot c q = 0 → a + b = c := by
  decide +kernel

private theorem H52_part1 : ∀ r s t : Submodule (ZMod 2) V3, IsLine r → IsLine s → IsLine t →
    r ≠ s → t ≠ r → t ≠ s → ∀ q : V3, q ≠ 0 → q ∈ r → q ∈ s → q ∈ t →
      uOf (r : Set V3) * uOf (s : Set V3) = uOf (t : Set V3) := by
  intro r s t hr hs ht hrs htr hts q hq hqr hqs hqt
  obtain ⟨a, ha, ma⟩ := H5line_dot r hr
  obtain ⟨b, hb, mb⟩ := H5line_dot s hs
  obtain ⟨c, hc, mc⟩ := H5line_dot t ht
  have hab : a ≠ b := fun h => hrs (Submodule.ext fun v => by rw [ma v, mb v, h])
  have hca : c ≠ a := fun h => htr (Submodule.ext fun v => by rw [mc v, ma v, h])
  have hcb : c ≠ b := fun h => hts (Submodule.ext fun v => by rw [mc v, mb v, h])
  rw [uOf_H5lin a r ma, uOf_H5lin b s mb, uOf_H5lin c t mc, ← H5lin_mul,
    H52_line_key a b c q ha hb hc hab hca hcb hq ((ma q).1 hqr) ((mb q).1 hqs)
      ((mc q).1 hqt)]

private def H52beta (u w : PermV) : ZMod 2 :=
  ∑ v : V3, Multiplicative.toAdd u v * Multiplicative.toAdd w v

private theorem H52beta_mul_left (u u' w : PermV) :
    H52beta (u * u') w = H52beta u w + H52beta u' w := by
  unfold H52beta
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [toAdd_mul, Pi.add_apply, add_mul]

private theorem H52beta_mul_right (u w w' : PermV) :
    H52beta u (w * w') = H52beta u w + H52beta u w' := by
  unfold H52beta
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [toAdd_mul, Pi.add_apply, mul_add]

private theorem H52beta_gl (g : GL (Fin 3) (ZMod 2)) (u w : PermV) :
    H52beta (gl3Act g u) (gl3Act g w) = H52beta u w := by
  unfold H52beta
  simp only [gl3Act_toAdd]
  exact sum_mulVec_eq (g⁻¹) (fun v => Multiplicative.toAdd u v * Multiplicative.toAdd w v)

private theorem H52beta_nondeg (u : PermV) (hu : u ∈ Ucore) (hu1 : u ≠ 1) :
    ∃ w ∈ Ucore, H52beta u w ≠ 0 := by
  obtain ⟨hu0, hsum⟩ := mem_Ucore'.1 hu
  obtain ⟨x, hx⟩ : ∃ x, Multiplicative.toAdd u x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hu1
    apply eq_of_toAdd_eq
    intro v
    rw [toAdd_one, Pi.zero_apply]
    exact hcon v
  have hx0 : x ≠ 0 := fun h => hx (by rw [h]; exact hu0)
  obtain ⟨y, hy0, hyv⟩ : ∃ y, y ≠ 0 ∧ Multiplicative.toAdd u y = 0 := by
    by_contra hcon
    push Not at hcon
    have h := sum_zmod2_eq_card (fun v => Multiplicative.toAdd u v)
    rw [hsum] at h
    have hfil : Finset.univ.filter (fun v => Multiplicative.toAdd u v ≠ 0) =
        Finset.univ.erase (0 : V3) := by
      ext v
      rw [Finset.mem_filter, Finset.mem_erase]
      constructor
      · intro hv
        exact ⟨fun h0 => hv.2 (by rw [h0]; exact hu0), Finset.mem_univ _⟩
      · intro hv
        exact ⟨Finset.mem_univ _, hcon v hv.1⟩
    rw [hfil, S0_card] at h
    exact absurd h (by decide)
  have hxy : x ≠ y := fun h => by
    rw [h] at hx
    exact hx hyv
  have hmem : pairV x y ∈ Ucore := O3_ucore (pairV x y) (by
    rw [O3set_eq]
    exact ⟨x, y, hx0, hy0, hxy, rfl⟩) |>.1
  refine ⟨pairV x y, hmem, ?_⟩
  unfold H52beta
  rw [Fintype.sum_eq_add x y hxy]
  · simp [toAdd_pairV, hyv, hx]
  · intro z hz
    simp [toAdd_pairV, hz.1, hz.2]

private theorem fix_const (f : PermV) (g : GL (Fin 3) (ZMod 2)) (hfix : gl3Act g f = f) (v : V3) :
    Multiplicative.toAdd f v =
      Multiplicative.toAdd f ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v) := by
  have h := congrArg (fun F : PermV => Multiplicative.toAdd F
    ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v)) hfix
  rw [gl3Act_toAdd, inv_mulVec_mulVec] at h
  exact h

private theorem sum_struct (f : V3 → ZMod 2) (p : V3) (S : Finset V3) (a c : ZMod 2)
    (h : ∀ v, f v = (if v = p then a else 0) + (if v ∈ S then c else 0)) :
    ∑ v : V3, f v = a + (S.card : ZMod 2) * c := by
  simp only [h]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_mem, Finset.univ_inter,
    Finset.sum_const, nsmul_eq_mul]
  simp

private theorem sum_two_sets (f : V3 → ZMod 2) (S₁ S₂ : Finset V3) (α β : ZMod 2)
    (h : ∀ v, f v = (if v ∈ S₁ then α else 0) + (if v ∈ S₂ then β else 0)) :
    ∑ v : V3, f v = (S₁.card : ZMod 2) * α + (S₂.card : ZMod 2) * β := by
  simp only [h]
  rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem, Finset.univ_inter,
    Finset.univ_inter, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]

private theorem Lpt_trans (p v w : V3) (hp : p ≠ 0) (hv0 : v ≠ 0) (hvp : v ≠ p) (hw0 : w ≠ 0)
    (hwp : w ≠ p) :
    ∃ g ∈ Lpt p, (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v = w := by
  have key : ∀ p v : V3, p ≠ 0 → v ≠ 0 → v ≠ p → ∃ z : V3, D3 p v z ≠ 0 := by decide
  obtain ⟨z, hz⟩ := key p v hp hv0 hvp
  obtain ⟨z', hz'⟩ := key p w hp hw0 hwp
  obtain ⟨g, h1, h2, -⟩ := gl_map_bases p v z p w z' (by rw [basisM_det]; exact hz)
    (by rw [basisM_det]; exact hz')
  refine ⟨g, ?_, h2⟩
  rw [mem_Lpt]
  intro x hx
  rw [Set.mem_singleton_iff.1 hx]
  exact h1

private theorem Lpt_fix_const (p : V3) (hp : p ≠ 0) (f : PermV)
    (hf : f ∈ fixV ((Lpt p).map gl3Act)) (v w : V3) (hv0 : v ≠ 0) (hvp : v ≠ p) (hw0 : w ≠ 0)
    (hwp : w ≠ p) : Multiplicative.toAdd f v = Multiplicative.toAdd f w := by
  obtain ⟨g, hg, hgv⟩ := Lpt_trans p v w hp hv0 hvp hw0 hwp
  have hfg : gl3Act g f = f := (mem_fixV.1 hf) (gl3Act g) (Subgroup.mem_map_of_mem gl3Act hg)
  rw [← hgv]
  exact fix_const f g hfg v

private theorem H52_Lpt_fix (p : V3) (hp : p ≠ 0) :
    Ucore ⊓ fixV ((Lpt p).map gl3Act) = Subgroup.zpowers (uOf ({p} : Set V3)) := by
  apply le_antisymm
  · intro f hf
    obtain ⟨hfU, hfix⟩ := Subgroup.mem_inf.1 hf
    obtain ⟨hf0, hfs⟩ := mem_Ucore'.1 hfU
    have key1 : ∀ p : V3, p ≠ 0 → ∃ w0 : V3, w0 ≠ 0 ∧ w0 ≠ p := by decide
    have key2 : ∀ p : V3, p ≠ 0 → (Finset.univ.filter (fun v : V3 => v ≠ 0 ∧ v ≠ p)).card = 6 := by
      decide
    obtain ⟨w0, hw0, hw0p⟩ := key1 p hp
    set c := Multiplicative.toAdd f w0 with hc
    set S := Finset.univ.filter (fun v : V3 => v ≠ 0 ∧ v ≠ p) with hS
    have hpt : ∀ v : V3, Multiplicative.toAdd f v =
        (if v = p then Multiplicative.toAdd f p else 0) + (if v ∈ S then c else 0) := by
      intro v
      by_cases hv0 : v = 0
      · have hpv : ¬ (v = p) := fun h => hp (hv0 ▸ h.symm)
        have hvS : v ∉ S := by
          rw [hS, Finset.mem_filter]
          exact fun h => h.2.1 hv0 |>.elim
        rw [if_neg hpv, if_neg hvS, add_zero, hv0, hf0]
      · by_cases hvp : v = p
        · have hvS : v ∉ S := by
            rw [hS, Finset.mem_filter]
            exact fun h => h.2.2 hvp
          rw [if_pos hvp, if_neg hvS, add_zero, hvp]
        · have hvS : v ∈ S := by
            rw [hS, Finset.mem_filter]
            exact ⟨Finset.mem_univ _, hv0, hvp⟩
          rw [if_neg hvp, if_pos hvS, zero_add, hc]
          exact Lpt_fix_const p hp f hfix v w0 hv0 hvp hw0 hw0p
    have hsum := sum_struct (fun v => Multiplicative.toAdd f v) p S (Multiplicative.toAdd f p) c hpt
    rw [hfs, key2 p hp] at hsum
    have hfp : Multiplicative.toAdd f p = 0 := by
      have h6 : ((6 : ℕ) : ZMod 2) = 0 := by decide
      rw [h6, zero_mul, add_zero] at hsum
      exact hsum.symm
    rcases H5_zmod2_cases c with hc0 | hc1
    · have hf1 : f = 1 := by
        apply eq_of_toAdd_eq
        intro v
        rw [toAdd_one, Pi.zero_apply, hpt v, hc0]
        simp [hfp, hS]
      rw [hf1]
      exact one_mem _
    · have hf1 : f = uOf ({p} : Set V3) := by
        apply eq_of_toAdd_eq
        intro v
        rw [toAdd_uOf1, hpt v, hc1]
        by_cases hvp : v = p
        · simp [hvp, hfp, hS]
        · simp [hS, hvp]
      rw [hf1]
      exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le]
    exact Subgroup.mem_inf.2 ⟨uOf_pt_mem_Ucore p hp, mem_fixV.2 fun x hx => by
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hx
      exact gl3Act_uOf_pt p g hg⟩

private theorem H52_Lln_fix (c : GL (Fin 3) (ZMod 2)) (l : Submodule (ZMod 2) V3) (hl : IsLine l)
    (hline : ∀ v : V3, (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ l ↔ v 2 = 0) :
    Ucore ⊓ fixV ((Lln l).map gl3Act) = Subgroup.zpowers (uOf (l : Set V3)) := by
  classical
  apply le_antisymm
  · intro f hf
    obtain ⟨hfU, hfix⟩ := Subgroup.mem_inf.1 hf
    obtain ⟨hf0, hfs⟩ := mem_Ucore'.1 hfU
    have hcst : ∀ v w : V3, v ∈ l → v ≠ 0 → w ∈ l → w ≠ 0 →
        Multiplicative.toAdd f v = Multiplicative.toAdd f w := by
      intro v w hv hv0 hw hw0
      obtain ⟨g, hg, hgv⟩ := Lln_trans_line54 c l hline v w hv hv0 hw hw0
      have hfg : gl3Act g f = f := (mem_fixV.1 hfix) (gl3Act g) (Subgroup.mem_map_of_mem gl3Act hg)
      rw [← hgv]
      exact fix_const f g hfg v
    have hcst' : ∀ v w : V3, v ∉ l → w ∉ l →
        Multiplicative.toAdd f v = Multiplicative.toAdd f w := by
      intro v w hv hw
      obtain ⟨g, hg, hgv⟩ := Lln_trans_compl54 c l hline v w hv hw
      have hfg : gl3Act g f = f := (mem_fixV.1 hfix) (gl3Act g) (Subgroup.mem_map_of_mem gl3Act hg)
      rw [← hgv]
      exact fix_const f g hfg v
    have hcardS1 : (Finset.univ.filter (fun v : V3 => v ∈ l ∧ v ≠ 0)).card = 3 :=
      card_mem_l_ne_zero l hl
    have hcardS2 : (Finset.univ.filter (fun v : V3 => v ∉ l)).card = 4 := card_compl_l l hl
    obtain ⟨a0, ha0⟩ : ∃ a0 : V3, a0 ∈ Finset.univ.filter (fun v : V3 => v ∈ l ∧ v ≠ 0) := by
      apply Finset.card_pos.1
      rw [hcardS1]
      norm_num
    obtain ⟨b0, hb0⟩ : ∃ b0 : V3, b0 ∈ Finset.univ.filter (fun v : V3 => v ∉ l) := by
      apply Finset.card_pos.1
      rw [hcardS2]
      norm_num
    rw [Finset.mem_filter] at ha0 hb0
    set α := Multiplicative.toAdd f a0 with hα
    set β := Multiplicative.toAdd f b0 with hβ
    have hpt : ∀ v : V3, Multiplicative.toAdd f v =
        (if v ∈ Finset.univ.filter (fun v : V3 => v ∈ l ∧ v ≠ 0) then α else 0) +
          (if v ∈ Finset.univ.filter (fun v : V3 => v ∉ l) then β else 0) := by
      intro v
      by_cases hvl : v ∈ l
      · by_cases hv0 : v = 0
        · rw [if_neg (by simp [hv0]), if_neg (by simp [hvl]), add_zero, hv0, hf0]
        · rw [if_pos (by simp [hvl, hv0]), if_neg (by simp [hvl]), add_zero]
          exact hcst v a0 hvl hv0 ha0.2.1 ha0.2.2
      · rw [if_neg (by simp [hvl]), if_pos (by simp [hvl]), zero_add]
        exact hcst' v b0 hvl hb0.2
    have hsum := sum_two_sets (fun v => Multiplicative.toAdd f v)
      (Finset.univ.filter (fun v : V3 => v ∈ l ∧ v ≠ 0))
      (Finset.univ.filter (fun v : V3 => v ∉ l)) α β hpt
    rw [hfs, hcardS1, hcardS2] at hsum
    have hα0 : α = 0 := by
      have h34 : ((3 : ℕ) : ZMod 2) * α + ((4 : ℕ) : ZMod 2) * β = α := by
        have h3 : ((3 : ℕ) : ZMod 2) = 1 := by decide
        have h4 : ((4 : ℕ) : ZMod 2) = 0 := by decide
        rw [h3, h4, zero_mul, add_zero, one_mul]
      have := hsum
      rw [h34] at this
      exact this.symm
    rcases H5_zmod2_cases β with hβ0 | hβ1
    · have hf1 : f = 1 := by
        apply eq_of_toAdd_eq
        intro v
        rw [toAdd_one, Pi.zero_apply, hpt v, hα0, hβ0]
        simp
      rw [hf1]
      exact one_mem _
    · have hf1 : f = uOf (l : Set V3) := by
        apply eq_of_toAdd_eq
        intro v
        rw [hpt v, hα0, hβ1]
        unfold uOf
        simp only [toAdd_ofAdd, SetLike.mem_coe]
        by_cases hvl : v ∈ l
        · have hnot : ¬ (v ≠ 0 ∧ v ∉ l) := fun h => h.2 hvl
          simp [hvl, hnot]
        · have hv0 : v ≠ 0 := fun h0 => hvl (h0 ▸ l.zero_mem)
          simp [hvl, hv0]
      rw [hf1]
      exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le]
    refine Subgroup.mem_inf.2 ⟨uOf_l_mem_Ucore l hl, mem_fixV.2 fun x hx => ?_⟩
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hx
    exact gl3Act_uOf_l_T (Lln l) l (fun g hg v hv => ((mem_Lln g l).1 hg v hv).1) g hg

private theorem line_pt_key : ∀ x : V3, x 2 = 0 → x ≠ 0 → x ≠ e1 → x 1 = 1 := by decide

private theorem unitri_line_key : ∀ x0 y0 : ZMod 2, x0 + (x0 + y0) = y0 := by decide

open CFSG.Quasithin.MS93 in
private theorem uniTri_mulVec_line (x y : V3) (hx1 : x 1 = 1) (hx2 : x 2 = 0) (hy1 : y 1 = 1)
    (hy2 : y 2 = 0) :
    ((slGL (uniTri (x 0 + y 0) 0 0) : GL (Fin 3) (ZMod 2)) :
      Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec x = y := by
  have hm : ((slGL (uniTri (x 0 + y 0) 0 0) : GL (Fin 3) (ZMod 2)) :
      Matrix (Fin 3) (Fin 3) (ZMod 2)) = !![1, x 0 + y 0, 0; 0, 1, 0; 0, 0, 1] := rfl
  rw [hm]
  funext i
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hx1, hx2]
    exact unitri_line_key _ _
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hx1, hx2, hy1]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hx2, hy2]

open CFSG.Quasithin.MS93 in
private theorem T_trans_line (T : Subgroup (GL (Fin 3) (ZMod 2))) (c : GL (Fin 3) (ZMod 2))
    (hconjT : ∀ y ∈ B0, c * y * c⁻¹ ∈ T) (l : Submodule (ZMod 2) V3)
    (hline : ∀ v : V3, (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ l ↔ v 2 = 0)
    (p : V3) (hpc : (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec e1 = p)
    (v w : V3) (hv : v ∈ l) (hv0 : v ≠ 0) (hvp : v ≠ p) (hw : w ∈ l) (hw0 : w ≠ 0) (hwp : w ≠ p) :
    ∃ t ∈ T, (t : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v = w := by
  obtain ⟨x, hx⟩ : ∃ x : V3,
      ((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v = x := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : V3,
      ((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w = y := ⟨_, rfl⟩
  have hcx : (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec x = v := by
    rw [← hx, mulVec_inv_mulVec]
  have hcy : (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec y = w := by
    rw [← hy, mulVec_inv_mulVec]
  have hx2 : x 2 = 0 := (hline x).1 (by rw [hcx]; exact hv)
  have hy2 : y 2 = 0 := (hline y).1 (by rw [hcy]; exact hw)
  have hx0 : x ≠ 0 := fun h => hv0 (by rw [← hcx, h, Matrix.mulVec_zero])
  have hy0 : y ≠ 0 := fun h => hw0 (by rw [← hcy, h, Matrix.mulVec_zero])
  have hxe : x ≠ e1 := fun h => hvp (by rw [← hcx, h, hpc])
  have hye : y ≠ e1 := fun h => hwp (by rw [← hcy, h, hpc])
  have hx1 : x 1 = 1 := line_pt_key x hx2 hx0 hxe
  have hy1 : y 1 = 1 := line_pt_key y hy2 hy0 hye
  have hb : slGL (uniTri (x 0 + y 0) 0 0) ∈ B0 := (mem_B0 _).2 ⟨x 0 + y 0, 0, 0, rfl⟩
  refine ⟨c * slGL (uniTri (x 0 + y 0) 0 0) * c⁻¹, hconjT _ hb, ?_⟩
  rw [mulVec_conj54, hx, uniTri_mulVec_line x y hx1 hx2 hy1 hy2, hcy]

private theorem sum_three (f : V3 → ZMod 2) (p : V3) (S₁ S₂ : Finset V3) (a β γ : ZMod 2)
    (h : ∀ v, f v = (if v = p then a else 0) + (if v ∈ S₁ then β else 0) +
      (if v ∈ S₂ then γ else 0)) :
    ∑ v : V3, f v = a + (S₁.card : ZMod 2) * β + (S₂.card : ZMod 2) * γ := by
  simp only [h]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_mem,
    Finset.sum_ite_mem, Finset.univ_inter, Finset.univ_inter, Finset.sum_const, Finset.sum_const,
    nsmul_eq_mul, nsmul_eq_mul]
  simp

open scoped Classical in
private theorem toAdd_uOf_lset (l : Submodule (ZMod 2) V3) (v : V3) :
    Multiplicative.toAdd (uOf (l : Set V3)) v = if v ≠ 0 ∧ v ∉ l then 1 else 0 := by
  unfold uOf
  simp only [toAdd_ofAdd, SetLike.mem_coe]

private theorem H52_T_elem (T : Subgroup (GL (Fin 3) (ZMod 2))) (p : V3)
    (l : Submodule (ZMod 2) V3) (hyp : HypH5 T p l) (c : GL (Fin 3) (ZMod 2))
    (hconjT : ∀ y ∈ B0, c * y * c⁻¹ ∈ T)
    (hpc : (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec e1 = p)
    (hline : ∀ v : V3, (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ l ↔ v 2 = 0)
    (f : PermV) (hf : f ∈ Ucore ⊓ fixV (T.map gl3Act)) :
    f = 1 ∨ f = uOf ({p} : Set V3) ∨ f = uOf (l : Set V3) ∨
      f = uOf ({p} : Set V3) * uOf (l : Set V3) := by
  classical
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  obtain ⟨hfU, hfix⟩ := Subgroup.mem_inf.1 hf
  obtain ⟨hf0, hfs⟩ := mem_Ucore'.1 hfU
  have hfT : ∀ t ∈ T, gl3Act t f = f := fun t ht =>
    (mem_fixV.1 hfix) (gl3Act t) (Subgroup.mem_map_of_mem gl3Act ht)
  have hpl : p ∈ l := by
    rw [← hpc]
    exact (hline e1).2 rfl
  have h0l : (0 : V3) ∈ l := l.zero_mem
  have hcstO : ∀ v w : V3, v ∉ l → w ∉ l → Multiplicative.toAdd f v = Multiplicative.toAdd f w :=
    fun v w hv hw => Z_const54 T c hconjT l hline f hfix v w hv hw
  have hcstL : ∀ v w : V3, v ∈ l → v ≠ 0 → v ≠ p → w ∈ l → w ≠ 0 → w ≠ p →
      Multiplicative.toAdd f v = Multiplicative.toAdd f w := by
    intro v w hv hv0 hvp hw hw0 hwp
    obtain ⟨t, ht, htv⟩ := T_trans_line T c hconjT l hline p hpc v w hv hv0 hvp hw hw0 hwp
    have h := fix_const f t (hfT t ht) v
    rw [htv] at h
    exact h
  set A : Finset V3 := Finset.univ.filter (fun v => v ∈ l ∧ v ≠ 0 ∧ v ≠ p) with hAdef
  set B : Finset V3 := Finset.univ.filter (fun v => v ∉ l) with hBdef
  have hA : A.card = 2 := by
    have h3 := card_mem_l_ne_zero l hyp.l_line
    have hAeq : A = (Finset.univ.filter (fun v : V3 => v ∈ l ∧ v ≠ 0)).erase p := by
      ext v
      rw [hAdef, Finset.mem_filter, Finset.mem_erase, Finset.mem_filter]
      constructor
      · rintro ⟨-, hv⟩
        exact ⟨hv.2.2, Finset.mem_univ _, hv.1, hv.2.1⟩
      · rintro ⟨hvp, -, hv⟩
        exact ⟨Finset.mem_univ _, hv.1, hv.2, hvp⟩
    rw [hAeq, Finset.card_erase_of_mem (Finset.mem_filter.2 ⟨Finset.mem_univ _, hpl, hyp.p_ne⟩), h3]
  have hB : B.card = 4 := card_compl_l l hyp.l_line
  obtain ⟨a0, ha0⟩ : A.Nonempty := Finset.card_pos.1 (by rw [hA]; norm_num)
  obtain ⟨b0, hb0⟩ : B.Nonempty := Finset.card_pos.1 (by rw [hB]; norm_num)
  have ha0' : a0 ∈ l ∧ a0 ≠ 0 ∧ a0 ≠ p := by
    rw [hAdef, Finset.mem_filter] at ha0
    exact ha0.2
  have hb0' : b0 ∉ l := by
    rw [hBdef, Finset.mem_filter] at hb0
    exact hb0.2
  set α := Multiplicative.toAdd f a0 with hα
  set β := Multiplicative.toAdd f b0 with hβ
  have hpt : ∀ v : V3, Multiplicative.toAdd f v =
      (if v = p then Multiplicative.toAdd f p else 0) + (if v ∈ A then α else 0) +
        (if v ∈ B then β else 0) := by
    intro v
    have hvA : v = p → v ∉ A := fun h hh => by
      rw [hAdef, Finset.mem_filter] at hh
      exact hh.2.2.2 h
    have hnB' : v = p → v ∉ B := fun h hh => by
      rw [hBdef, Finset.mem_filter] at hh
      exact hh.2 (h ▸ hpl)
    by_cases hvp : v = p
    · rw [if_pos hvp, if_neg (hvA hvp), if_neg (hnB' hvp), add_zero, add_zero, hvp]
    · by_cases hvl : v ∈ l
      · by_cases hv0 : v = 0
        · have hnA : v ∉ A := fun hh => by
            rw [hAdef, Finset.mem_filter] at hh
            exact hh.2.2.1 hv0
          have hnB : v ∉ B := fun hh => by
            rw [hBdef, Finset.mem_filter] at hh
            exact hh.2 hvl
          rw [if_neg hvp, if_neg hnA, if_neg hnB, add_zero, add_zero, hv0, hf0]
        · have hvA' : v ∈ A := by
            rw [hAdef, Finset.mem_filter]
            exact ⟨Finset.mem_univ _, hvl, hv0, hvp⟩
          have hnB : v ∉ B := fun hh => by
            rw [hBdef, Finset.mem_filter] at hh
            exact hh.2 hvl
          rw [if_neg hvp, if_pos hvA', if_neg hnB, zero_add, add_zero]
          exact hcstL v a0 hvl hv0 hvp ha0'.1 ha0'.2.1 ha0'.2.2
      · have hvB : v ∈ B := by
          rw [hBdef]
          exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hvl⟩
        have hnA : v ∉ A := fun hh => by
          rw [hAdef, Finset.mem_filter] at hh
          exact hvl hh.2.1
        rw [if_neg hvp, if_neg hnA, if_pos hvB, zero_add, zero_add]
        exact hcstO v b0 hvl hb0'
  have hsum : ∑ v : V3, Multiplicative.toAdd f v =
      Multiplicative.toAdd f p + ((A.card : ℕ) : ZMod 2) * α + ((B.card : ℕ) : ZMod 2) * β :=
    sum_three (fun v => Multiplicative.toAdd f v) p A B _ α β hpt
  rw [hA, hB, hfs] at hsum
  have h2 : ((2 : ℕ) : ZMod 2) = 0 := by decide
  have h4 : ((4 : ℕ) : ZMod 2) = 0 := by decide
  rw [h2, h4, zero_mul, zero_mul, add_zero, add_zero] at hsum
  have hfp : Multiplicative.toAdd f p = 0 := hsum.symm
  have hpt' : ∀ v : V3, Multiplicative.toAdd f v =
      (if v ∈ A then α else 0) + (if v ∈ B then β else 0) := by
    intro v
    rw [hpt v]
    by_cases hvp : v = p
    · rw [if_pos hvp, hfp, zero_add]
    · rw [if_neg hvp, zero_add]
  rcases H5_zmod2_cases α with hα0 | hα1 <;> rcases H5_zmod2_cases β with hβ0 | hβ1
  · left
    apply eq_of_toAdd_eq
    intro v
    rw [hpt' v, hα0, hβ0, toAdd_one, Pi.zero_apply]
    simp
  · right; right; left
    apply eq_of_toAdd_eq
    intro v
    rw [hpt' v, hα0, hβ1, toAdd_uOf_lset]
    by_cases hvl : v ∈ l
    · have hnB : v ∉ B := fun hh => by
        rw [hBdef, Finset.mem_filter] at hh
        exact hh.2 hvl
      have hn : ¬ (v ≠ 0 ∧ v ∉ l) := fun h => h.2 hvl
      rw [if_neg hnB, if_neg hn, add_zero]
      simp
    · have hvB : v ∈ B := by
        rw [hBdef]
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hvl⟩
      have hv0 : v ≠ 0 := fun h => hvl (h ▸ h0l)
      rw [if_pos hvB, if_pos (show v ≠ 0 ∧ v ∉ l from ⟨hv0, hvl⟩)]
      simp
  · right; right; right
    apply eq_of_toAdd_eq
    intro v
    rw [hpt' v, hα1, hβ0, toAdd_mul, Pi.add_apply, toAdd_uOf1, toAdd_uOf_lset]
    by_cases hvl : v ∈ l <;> by_cases hv0 : v = 0 <;> by_cases hvp : v = p <;>
      simp [hAdef, hBdef, hvl, hv0, hvp, hpl, h0l, h11]
  · right; left
    apply eq_of_toAdd_eq
    intro v
    rw [hpt' v, hα1, hβ1, toAdd_uOf1]
    by_cases hvl : v ∈ l <;> by_cases hv0 : v = 0 <;> by_cases hvp : v = p <;>
      simp [hAdef, hBdef, hvl, hv0, hvp, hpl, h0l, h11]

private theorem H52_T_closure (T : Subgroup (GL (Fin 3) (ZMod 2))) (p : V3)
    (l : Submodule (ZMod 2) V3) (hyp : HypH5 T p l) (c : GL (Fin 3) (ZMod 2))
    (hconjT : ∀ y ∈ B0, c * y * c⁻¹ ∈ T)
    (hpc : (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec e1 = p)
    (hline : ∀ v : V3, (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ l ↔ v 2 = 0) :
    Ucore ⊓ fixV (T.map gl3Act) =
      Subgroup.closure {uOf ({p} : Set V3), uOf (l : Set V3)} := by
  apply le_antisymm
  · intro f hf
    rcases H52_T_elem T p l hyp c hconjT hpc hline f hf with h | h | h | h <;> rw [h]
    · exact one_mem _
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  · rw [Subgroup.closure_le]
    intro x hx
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · refine Subgroup.mem_inf.2 ⟨uOf_pt_mem_Ucore p hyp.p_ne, mem_fixV.2 fun y hy => ?_⟩
      obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hy
      exact gl3Act_uOf_pt p t ((mem_Lpt _ _).2 fun v hv => by
        rw [Set.mem_singleton_iff.1 hv]
        exact hyp.p_fix t ht)
    · refine Subgroup.mem_inf.2 ⟨uOf_l_mem_Ucore l hyp.l_line, mem_fixV.2 fun y hy => ?_⟩
      obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hy
      exact gl3Act_uOf_l_T T l hyp.l_inv t ht

private theorem neq_one_of_toAdd (x : PermV) (v : V3)
    (h : Multiplicative.toAdd x v ≠ 0) : x ≠ 1 := by
  intro h1
  rw [h1, toAdd_one, Pi.zero_apply] at h
  exact h rfl

private theorem ne_of_toAdd (x y : PermV) (v : V3)
    (h : Multiplicative.toAdd x v ≠ Multiplicative.toAdd y v) : x ≠ y :=
  fun hxy => h (by rw [hxy])

private theorem H52_T_rk (T : Subgroup (GL (Fin 3) (ZMod 2))) (p : V3)
    (l : Submodule (ZMod 2) V3) (hyp : HypH5 T p l) (c : GL (Fin 3) (ZMod 2))
    (hconjT : ∀ y ∈ B0, c * y * c⁻¹ ∈ T)
    (hpc : (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec e1 = p)
    (hline : ∀ v : V3, (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ l ↔ v 2 = 0) :
    CFSG.Quasithin.rk ↥(Ucore ⊓ fixV (T.map gl3Act)) = 2 := by
  classical
  have hpl : p ∈ l := by
    rw [← hpc]
    exact (hline e1).2 rfl
  have h0l : (0 : V3) ∈ l := l.zero_mem
  have hA2 : 1 < (Finset.univ.filter (fun v : V3 => v ∈ l ∧ v ≠ 0)).card := by
    rw [card_mem_l_ne_zero l hyp.l_line]
    norm_num
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 hA2
  rw [Finset.mem_filter] at hx hy
  obtain ⟨a0, ha0l, ha00, ha0p⟩ : ∃ a0 : V3, a0 ∈ l ∧ a0 ≠ 0 ∧ a0 ≠ p := by
    by_cases hxp : x = p
    · exact ⟨y, hy.2.1, hy.2.2, fun h => hxy (hxp.trans h.symm)⟩
    · exact ⟨x, hx.2.1, hx.2.2, hxp⟩
  have hB1 : 0 < (Finset.univ.filter (fun v : V3 => v ∉ l)).card := by
    rw [card_compl_l l hyp.l_line]
    norm_num
  obtain ⟨b0, hb0⟩ := Finset.card_pos.1 hB1
  have hb0l : b0 ∉ l := (Finset.mem_filter.1 hb0).2
  have hb00 : b0 ≠ 0 := fun h => hb0l (h ▸ h0l)
  have hb0p : b0 ≠ p := fun h => hb0l (h ▸ hpl)
  have hAp : Multiplicative.toAdd (uOf ({p} : Set V3)) a0 = 1 := by
    rw [toAdd_uOf1, if_pos ⟨ha00, ha0p⟩]
  have hAl : Multiplicative.toAdd (uOf (l : Set V3)) a0 = 0 := by
    rw [toAdd_uOf_lset, if_neg (fun h => h.2 ha0l)]
  have hBp : Multiplicative.toAdd (uOf ({p} : Set V3)) b0 = 1 := by
    rw [toAdd_uOf1, if_pos ⟨hb00, hb0p⟩]
  have hBl : Multiplicative.toAdd (uOf (l : Set V3)) b0 = 1 := by
    rw [toAdd_uOf_lset, if_pos ⟨hb00, hb0l⟩]
  have hmulA : Multiplicative.toAdd (uOf ({p} : Set V3) * uOf (l : Set V3)) a0 = 1 := by
    rw [toAdd_mul, Pi.add_apply, hAp, hAl, add_zero]
  have hmulB : Multiplicative.toAdd (uOf ({p} : Set V3) * uOf (l : Set V3)) b0 = 0 := by
    rw [toAdd_mul, Pi.add_apply, hBp, hBl, one_add_one_eq_two]
    decide
  have hset : ((Ucore ⊓ fixV (T.map gl3Act) : Subgroup PermV) : Set PermV) =
      {1, uOf ({p} : Set V3), uOf (l : Set V3), uOf ({p} : Set V3) * uOf (l : Set V3)} := by
    ext f
    rw [SetLike.mem_coe]
    constructor
    · intro hf
      have := H52_T_elem T p l hyp c hconjT hpc hline f hf
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using this
    · intro hf
      rw [H52_T_closure T p l hyp c hconjT hpc hline]
      rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hf
      rcases hf with rfl | rfl | rfl | rfl
      · exact one_mem _
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
      · exact mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  have n1 : (1 : PermV) ∉ ({uOf ({p} : Set V3), uOf (l : Set V3),
      uOf ({p} : Set V3) * uOf (l : Set V3)} : Set PermV) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    refine ⟨(neq_one_of_toAdd _ a0 ?_).symm, (neq_one_of_toAdd _ b0 ?_).symm,
      (neq_one_of_toAdd _ a0 ?_).symm⟩
    · rw [hAp]; exact one_ne_zero
    · rw [hBl]; exact one_ne_zero
    · rw [hmulA]; exact one_ne_zero
  have n2 : uOf ({p} : Set V3) ∉ ({uOf (l : Set V3), uOf ({p} : Set V3) * uOf (l : Set V3)} :
      Set PermV) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    refine ⟨ne_of_toAdd _ _ a0 ?_, ne_of_toAdd _ _ b0 ?_⟩
    · rw [hAp, hAl]; exact one_ne_zero
    · rw [hBp, hmulB]; exact one_ne_zero
  have n3 : uOf (l : Set V3) ≠ uOf ({p} : Set V3) * uOf (l : Set V3) :=
    ne_of_toAdd _ _ a0 (by rw [hAl, hmulA]; exact zero_ne_one)
  have hcard : Nat.card ↥(Ucore ⊓ fixV (T.map gl3Act)) = 4 := by
    rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, hset, Set.ncard_insert_of_notMem n1,
      Set.ncard_insert_of_notMem n2, Set.ncard_pair n3]
  unfold CFSG.Quasithin.rk
  rw [hcard, show (4 : ℕ) = 2 ^ 2 from rfl, padicValNat.prime_pow]

private theorem H52_part2 (T : Subgroup (GL (Fin 3) (ZMod 2))) (p : V3) (l : Submodule (ZMod 2) V3)
    (hyp : HypH5 T p l) : (Ucore ⊓ fixV (T.map gl3Act) =
      Subgroup.closure {uOf ({p} : Set V3), uOf (l : Set V3)} ∧
      CFSG.Quasithin.rk ↥(Ucore ⊓ fixV (T.map gl3Act)) = 2) := by
  obtain ⟨c, hconjT, hpc, hline⟩ := conj_data54 T p l hyp
  exact ⟨H52_T_closure T p l hyp c hconjT hpc hline, H52_T_rk T p l hyp c hconjT hpc hline⟩

section H52pc

private theorem V3_add_self (v : V3) : v + v = 0 := by
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  exact CharTwo.add_self_eq_zero (v i)

private theorem V3_add_add_cancel (v p : V3) : v + p + p = v := by
  rw [add_assoc, V3_add_self, add_zero]

private def Qpt (p : V3) : Subgroup (GL (Fin 3) (ZMod 2)) where
  carrier := {g | (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec p = p ∧
    ∀ v : V3, (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v = v ∨
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v = v + p}
  one_mem' := ⟨by simp, fun v => Or.inl (by simp)⟩
  mul_mem' := fun {g h} hg hh => by
    refine ⟨?_, fun v => ?_⟩
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec, hh.1, hg.1]
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec]
      rcases hh.2 v with h1 | h1 <;> rw [h1]
      · exact hg.2 v
      · rw [Matrix.mulVec_add, hg.1]
        rcases hg.2 v with h2 | h2 <;> rw [h2]
        · exact Or.inr rfl
        · exact Or.inl (V3_add_add_cancel v p)
  inv_mem' := fun {g} hg => by
    refine ⟨?_, fun v => ?_⟩
    · conv_lhs => rw [← hg.1]
      exact inv_mulVec_mulVec g p
    · set w := ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v with hw
      have hgw : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w = v := mulVec_inv_mulVec g v
      rcases hg.2 w with h1 | h1
      · rw [h1] at hgw
        exact Or.inl hgw
      · rw [h1] at hgw
        exact Or.inr (by rw [← hgw, V3_add_add_cancel])

private def Qlln (l : Submodule (ZMod 2) V3) : Subgroup (GL (Fin 3) (ZMod 2)) where
  carrier := {g | (∀ v ∈ l, (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v = v) ∧
    ∀ v : V3, (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v - v ∈ l}
  one_mem' := ⟨fun v _ => by simp, fun v => by simp⟩
  mul_mem' := fun {g h} hg hh => by
    refine ⟨fun v hv => ?_, fun v => ?_⟩
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec, hh.1 v hv, hg.1 v hv]
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec]
      have h1 := l.add_mem (hg.2 (h.val.mulVec v)) (hh.2 v)
      rw [sub_add_sub_cancel] at h1
      exact h1
  inv_mem' := fun {g} hg => by
    refine ⟨fun v hv => ?_, fun v => ?_⟩
    · conv_lhs => rw [← hg.1 v hv]
      exact inv_mulVec_mulVec g v
    · set w := ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v with hw
      have hgw : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w = v := mulVec_inv_mulVec g v
      have h1 := hg.2 w
      rw [hgw] at h1
      have h3 : w - v = -(v - w) := by abel
      rw [h3]
      exact l.neg_mem h1

private theorem Qpt_le_Lpt (p : V3) : Qpt p ≤ Lpt p := fun g hg =>
  (mem_Lpt g p).2 fun v hv => by rw [Set.mem_singleton_iff.1 hv]; exact hg.1

private theorem inv_mulVec_fix {p : V3} {h : GL (Fin 3) (ZMod 2)} (hh : h ∈ Lpt p) :
    ((h⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec p = p :=
  (mem_Lpt _ _).1 (Subgroup.inv_mem _ hh) p (Set.mem_singleton _)

private theorem Lpt_conj_Qpt {p : V3} {h g : GL (Fin 3) (ZMod 2)} (hh : h ∈ Lpt p)
    (hg : g ∈ Qpt p) : h * g * h⁻¹ ∈ Qpt p := by
  have hp : (h : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec p = p :=
    (mem_Lpt _ _).1 hh p (Set.mem_singleton _)
  have hpi := inv_mulVec_fix hh
  refine ⟨?_, fun v => ?_⟩
  · rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hpi,
      hg.1, hp]
  · rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rcases hg.2 (((h⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v) with
      h1 | h1
    · rw [h1]
      exact Or.inl (mulVec_inv_mulVec h v)
    · rw [h1, Matrix.mulVec_add, hp, mulVec_inv_mulVec h v]
      exact Or.inr rfl

private theorem Lpt_le_normalizer_Qpt (p : V3) : Lpt p ≤ Subgroup.normalizer (Qpt p : Set _) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact Lpt_conj_Qpt hh hx
  · intro hx
    have := Lpt_conj_Qpt (Subgroup.inv_mem _ hh) hx
    have e : h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x := by group
    rwa [e] at this

private theorem Qpt_sq (p : V3) {g : GL (Fin 3) (ZMod 2)} (hg : g ∈ Qpt p) : g * g = 1 := by
  have h2 : ∀ w : V3, (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
      ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w) = w := by
    intro w
    rcases hg.2 w with h1 | h1
    · rw [h1, h1]
    · rw [h1, Matrix.mulVec_add, hg.1, h1, V3_add_add_cancel]
  apply Units.ext
  rw [Units.val_mul, Units.val_one]
  refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
  simp only [Matrix.toLin'_apply, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
  exact h2 v

private abbrev upU (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Prop :=
  M 0 0 = 1 ∧ M 1 1 = 1 ∧ M 2 2 = 1 ∧ M 1 0 = 0 ∧ M 2 0 = 0 ∧ M 2 1 = 0

private abbrev Q0M (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Prop :=
  M 0 0 = 1 ∧ M 1 1 = 1 ∧ M 2 2 = 1 ∧ M 1 0 = 0 ∧ M 2 0 = 0 ∧ M 2 1 = 0 ∧ M 1 2 = 0

private abbrev Q1M (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Prop :=
  M 0 0 = 1 ∧ M 1 1 = 1 ∧ M 2 2 = 1 ∧ M 1 0 = 0 ∧ M 2 0 = 0 ∧ M 2 1 = 0 ∧ M 0 1 = 0

private theorem Q0_decide : ∀ M : Matrix (Fin 3) (Fin 3) (ZMod 2),
    (upU M ∧ upU (!![1, 0, 0; 0, 0, 1; 0, 1, 0] * M * !![1, 0, 0; 0, 0, 1; 0, 1, 0])) ↔
      Q0M M := by
  decide +kernel

private theorem Q1_decide : ∀ M : Matrix (Fin 3) (Fin 3) (ZMod 2),
    (upU M ∧ upU (!![0, 1, 0; 1, 0, 0; 0, 0, 1] * M * !![0, 1, 0; 1, 0, 0; 0, 0, 1])) ↔
      Q1M M := by
  decide +kernel

private theorem Qpt_decide : ∀ M : Matrix (Fin 3) (Fin 3) (ZMod 2),
    (M.mulVec e1 = e1 ∧ ∀ v : V3, M.mulVec v = v ∨ M.mulVec v = v + e1) ↔ Q0M M := by
  decide +kernel

private theorem Qlln_decide : ∀ M : Matrix (Fin 3) (Fin 3) (ZMod 2),
    ((∀ v : V3, v 2 = 0 → M.mulVec v = v) ∧ ∀ v : V3, (M.mulVec v - v) 2 = 0) ↔ Q1M M := by
  decide +kernel

private theorem mem_B0_iff (x : GL (Fin 3) (ZMod 2)) :
    x ∈ B0 ↔ upU (x : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
  rw [mem_B0]
  constructor
  · rintro ⟨a, b, c, h⟩
    rw [h]
    simp [upU]
  · rintro ⟨h00, h11, h22, h10, h20, h21⟩
    refine ⟨(x : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 1, (x : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 2,
      (x : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 2, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h11, h22, h10, h20, h21]

private theorem B0_mulVec_e1 {x : GL (Fin 3) (ZMod 2)} (hx : x ∈ B0) :
    (x : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec e1 = e1 := by
  obtain ⟨h00, -, -, h10, h20, -⟩ := (mem_B0_iff x).1 hx
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, e1, h00, h10, h20]

private theorem isPGroup_B0 : IsPGroup 2 B0 := by
  have hF : Nat.card (ZMod 2) = 2 ^ 1 := by simp
  exact (CFSG.Quasithin.MS93.isPGroup_sStar hF).map slGL.toMonoidHom

private theorem not_two_dvd_index_B0 : ¬ 2 ∣ B0.index := by
  have hF : Nat.card (ZMod 2) = 2 ^ 1 := by simp
  have h1 := CFSG.Quasithin.MS93.not_two_dvd_index_sStar hF
  have h2 : (CFSG.Quasithin.MS93.sStar.map slGL.toMonoidHom).index =
      CFSG.Quasithin.MS93.sStar.index :=
    Subgroup.index_map_equiv CFSG.Quasithin.MS93.sStar slGL
  rw [B0, h2]
  exact h1

private def conjSub (c : GL (Fin 3) (ZMod 2)) (H : Subgroup (GL (Fin 3) (ZMod 2))) :
    Subgroup (GL (Fin 3) (ZMod 2)) :=
  H.map (MulAut.conj c).toMonoidHom

private theorem mem_conjSub {c : GL (Fin 3) (ZMod 2)} {H : Subgroup (GL (Fin 3) (ZMod 2))}
    {x : GL (Fin 3) (ZMod 2)} : x ∈ conjSub c H ↔ c⁻¹ * x * c ∈ H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have e : c⁻¹ * (MulAut.conj c).toMonoidHom y * c = y := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e]
    exact hy
  · intro hx
    refine ⟨c⁻¹ * x * c, hx, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

private theorem index_conjSub (c : GL (Fin 3) (ZMod 2)) (H : Subgroup (GL (Fin 3) (ZMod 2))) :
    (conjSub c H).index = H.index :=
  Subgroup.index_map_equiv H (MulAut.conj c)

private theorem isPGroup_conjSub (c : GL (Fin 3) (ZMod 2))
    {H : Subgroup (GL (Fin 3) (ZMod 2))} (hH : IsPGroup 2 H) : IsPGroup 2 (conjSub c H) :=
  hH.map (MulAut.conj c).toMonoidHom

private theorem pCoreOf_le_of_odd_index {H S : Subgroup (GL (Fin 3) (ZMod 2))} (hSH : S ≤ H)
    (hS : IsPGroup 2 S) (hodd : ¬ 2 ∣ S.index) : CFSG.Open.pCoreOf 2 H ≤ S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrel : ¬ 2 ∣ (S.subgroupOf H).index := fun h => hodd (by
    rw [← Subgroup.relIndex_mul_index hSH]
    exact Dvd.dvd.mul_right h _)
  have hS' : IsPGroup 2 (S.subgroupOf H) :=
    hS.of_equiv (Subgroup.subgroupOfEquivOfLe hSH).symm
  haveI : (CFSG.pCore 2 ↥H).Normal := CFSG.pCore_normal
  let T : Sylow 2 H := hS'.toSylow hrel
  have hpc : CFSG.pCore 2 H ≤ (T : Subgroup H) :=
    (CFSG.pCore_isPGroup (G := H) (p := 2)).le_sylow_of_normal T
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact Subgroup.mem_subgroupOf.1 (hpc hy)

private theorem pCoreOf_eq_of_two {H S₁ S₂ Q : Subgroup (GL (Fin 3) (ZMod 2))}
    (h1 : S₁ ≤ H) (h2 : S₂ ≤ H) (hS₁ : IsPGroup 2 S₁) (hS₂ : IsPGroup 2 S₂)
    (hi₁ : ¬ 2 ∣ S₁.index) (hi₂ : ¬ 2 ∣ S₂.index) (hQ : S₁ ⊓ S₂ = Q) (hQH : Q ≤ H)
    (hQn : H ≤ Subgroup.normalizer (Q : Set (GL (Fin 3) (ZMod 2))))
    (hQ2 : IsPGroup 2 Q) : CFSG.Open.pCoreOf 2 H = Q := by
  apply le_antisymm
  · rw [← hQ]
    exact le_inf (pCoreOf_le_of_odd_index h1 hS₁ hi₁) (pCoreOf_le_of_odd_index h2 hS₂ hi₂)
  · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQH hQn hQ2

private theorem swapGL_mul_self : swapGL * swapGL = 1 := by
  apply Units.ext
  rw [Units.val_mul, Units.val_one]
  decide

private theorem swapGL_mulVec_e1 :
    (swapGL : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec e1 = e1 := by
  decide

private def swap01GL : GL (Fin 3) (ZMod 2) :=
  ⟨!![0, 1, 0; 1, 0, 0; 0, 0, 1], !![0, 1, 0; 1, 0, 0; 0, 0, 1], by decide, by decide⟩

private theorem swap01GL_mul_self : swap01GL * swap01GL = 1 := by
  apply Units.ext
  rw [Units.val_mul, Units.val_one]
  decide

private theorem mem_Qpt_conj {c : GL (Fin 3) (ZMod 2)} {p : V3}
    (hc : (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec e1 = p) (x : GL (Fin 3) (ZMod 2)) :
    x ∈ Qpt p ↔ c⁻¹ * x * c ∈ Qpt e1 := by
  have hcinv : ∀ w : V3, ((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
      ((c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w) = w := fun w => inv_mulVec_mulVec c w
  have hcc : ∀ w : V3, (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
      (((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w) = w :=
    fun w => mulVec_inv_mulVec c w
  have hcp : ((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec p = e1 := by
    rw [← hc]
    exact hcinv e1
  have hy : ∀ w : V3, ((c⁻¹ * x * c : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
      w = ((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
        ((x : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec ((c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
          w)) := by
    intro w
    rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by rw [hy, hc, h1, hcp], fun v => ?_⟩
    rcases h2 ((c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v) with h | h
    · left
      rw [hy, h, hcinv]
    · right
      rw [hy, h, Matrix.mulVec_add, hcinv, hcp]
  · rintro ⟨h1, h2⟩
    have hxp : (x : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec p = p := by
      have h3 := hy e1
      rw [h1, hc] at h3
      have h4 := congrArg ((c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec) h3
      rw [hcc, hc] at h4
      exact h4.symm
    refine ⟨hxp, fun v => ?_⟩
    rcases h2 (((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v) with
      h | h
    · left
      have h3 := hy (((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v)
      rw [h, hcc] at h3
      have h4 := congrArg ((c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec) h3.symm
      rw [hcc, hcc] at h4
      exact h4
    · right
      have h3 := hy (((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v)
      rw [h, hcc] at h3
      have h4 := congrArg ((c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec) h3.symm
      rw [hcc, Matrix.mulVec_add, hcc, hc] at h4
      exact h4

private theorem mem_Qlln_conj {c : GL (Fin 3) (ZMod 2)} {l : Submodule (ZMod 2) V3}
    (hc : ∀ v : V3, (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ l ↔ v 2 = 0)
    (x : GL (Fin 3) (ZMod 2)) : x ∈ Qlln l ↔ c⁻¹ * x * c ∈ Qlln line0 := by
  have hcinv : ∀ w : V3, ((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
      ((c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w) = w := fun w => inv_mulVec_mulVec c w
  have hcc : ∀ w : V3, (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
      (((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w) = w :=
    fun w => mulVec_inv_mulVec c w
  have hy : ∀ w : V3, ((c⁻¹ * x * c : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
      w = ((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
        ((x : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec ((c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
          w)) := by
    intro w
    rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun v hv => ?_, fun v => ?_⟩
    · have hcv : (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ l :=
        (hc v).2 (mem_line0.1 hv)
      rw [hy, h1 _ hcv, hcinv]
    · rw [mem_line0]
      apply (hc _).1
      simp only [Matrix.mulVec_sub, hy, hcc]
      exact h2 _
  · rintro ⟨h1, h2⟩
    refine ⟨fun v hv => ?_, fun v => ?_⟩
    · have hw : ((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v 2 = 0 :=
        (hc (((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v)).1
          (by rw [hcc]; exact hv)
      have h3 := h1 _ (mem_line0.2 hw)
      rw [hy, hcc] at h3
      have h4 := congrArg ((c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec) h3
      rw [hcc, hcc] at h4
      exact h4
    · have h3 := (hc _).2 (mem_line0.1 (h2 (((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3)
        (ZMod 2)).mulVec v)))
      simp only [Matrix.mulVec_sub, hy, hcc] at h3
      exact h3

private theorem Qpt_eq_conj {c : GL (Fin 3) (ZMod 2)} {p : V3}
    (hc : (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec e1 = p) :
    Qpt p = conjSub c (Qpt e1) := by
  ext x
  rw [mem_conjSub]
  exact mem_Qpt_conj hc x

private theorem Qlln_eq_conj {c : GL (Fin 3) (ZMod 2)} {l : Submodule (ZMod 2) V3}
    (hc : ∀ v : V3, (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ l ↔ v 2 = 0) :
    Qlln l = conjSub c (Qlln line0) := by
  ext x
  rw [mem_conjSub]
  exact mem_Qlln_conj hc x

private theorem mem_Qpt_e1 (y : GL (Fin 3) (ZMod 2)) :
    y ∈ Qpt e1 ↔ Q0M (y : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
  rw [← Qpt_decide]
  exact Iff.rfl

private theorem mem_Qlln_line0 (y : GL (Fin 3) (ZMod 2)) :
    y ∈ Qlln line0 ↔ Q1M (y : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
  rw [← Qlln_decide]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun v hv => h1 v (mem_line0.2 hv), fun v => mem_line0.1 (h2 v)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun v hv => h1 v (mem_line0.1 hv), fun v => mem_line0.2 (h2 v)⟩

private theorem pt_mem_iff (y : GL (Fin 3) (ZMod 2)) :
    (y ∈ B0 ∧ swapGL * y * swapGL ∈ B0) ↔ y ∈ Qpt e1 := by
  rw [mem_Qpt_e1, mem_B0_iff, mem_B0_iff]
  simp only [Units.val_mul]
  exact Q0_decide (y : Matrix (Fin 3) (Fin 3) (ZMod 2))

private theorem ln_mem_iff (y : GL (Fin 3) (ZMod 2)) :
    (y ∈ B0 ∧ swap01GL * y * swap01GL ∈ B0) ↔ y ∈ Qlln line0 := by
  rw [mem_Qlln_line0, mem_B0_iff, mem_B0_iff]
  simp only [Units.val_mul]
  exact Q1_decide (y : Matrix (Fin 3) (Fin 3) (ZMod 2))

private theorem B0_conj_le_Lpt {d : GL (Fin 3) (ZMod 2)} {p : V3}
    (hd : (d : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec e1 = p) : conjSub d B0 ≤ Lpt p := by
  intro x hx
  rw [mem_conjSub] at hx
  have h1 := B0_mulVec_e1 hx
  rw [mem_Lpt]
  intro v hv
  rw [Set.mem_singleton_iff.1 hv, ← hd]
  have e : x = d * (d⁻¹ * x * d) * d⁻¹ := by group
  rw [e, mulVec_conj54, inv_mulVec_mulVec, h1]

private theorem B0_conj_le_Lln {d : GL (Fin 3) (ZMod 2)} {l : Submodule (ZMod 2) V3}
    (hd : ∀ v : V3, (d : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ l ↔ v 2 = 0) :
    conjSub d B0 ≤ Lln l := by
  intro x hx
  rw [mem_conjSub] at hx
  have h1 : d⁻¹ * x * d ∈ Lln line0 := B0_le_Lln_line0 _ hx
  have h2 := (mem_Lln_conj d l hd (d⁻¹ * x * d)).1 h1
  have e : d * (d⁻¹ * x * d) * d⁻¹ = x := by group
  rwa [e] at h2

private theorem pt_inter {c : GL (Fin 3) (ZMod 2)} :
    conjSub c B0 ⊓ conjSub (c * swapGL) B0 = conjSub c (Qpt e1) := by
  ext x
  have hswinv : swapGL⁻¹ = swapGL := inv_eq_of_mul_eq_one_right swapGL_mul_self
  have e : (c * swapGL)⁻¹ * x * (c * swapGL) = swapGL * (c⁻¹ * x * c) * swapGL := by
    rw [mul_inv_rev, hswinv]
    simp only [mul_assoc]
  rw [Subgroup.mem_inf, mem_conjSub, mem_conjSub, e, pt_mem_iff, mem_conjSub]

private theorem ln_inter {c : GL (Fin 3) (ZMod 2)} :
    conjSub c B0 ⊓ conjSub (c * swap01GL) B0 = conjSub c (Qlln line0) := by
  ext x
  have hswinv : swap01GL⁻¹ = swap01GL := inv_eq_of_mul_eq_one_right swap01GL_mul_self
  have e : (c * swap01GL)⁻¹ * x * (c * swap01GL) = swap01GL * (c⁻¹ * x * c) * swap01GL := by
    rw [mul_inv_rev, hswinv]
    simp only [mul_assoc]
  rw [Subgroup.mem_inf, mem_conjSub, mem_conjSub, e, ln_mem_iff, mem_conjSub]

private theorem isPGroup_Qpt (p : V3) : IsPGroup 2 (Qpt p) := by
  intro x
  exact ⟨1, Subtype.ext (by rw [Subgroup.coe_pow, pow_one, pow_two, Qpt_sq p x.2]; rfl)⟩

private theorem Qlln_mul_self {l : Submodule (ZMod 2) V3} {g : GL (Fin 3) (ZMod 2)}
    (hg : g ∈ Qlln l) : g * g = 1 := by
  have h2 : ∀ w : V3, (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
      ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w) = w := by
    intro w
    have hd := hg.2 w
    have hgd := hg.1 _ hd
    set d := (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w - w with hdef
    have e1' : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w = w + d := by
      rw [hdef]
      abel
    rw [e1', Matrix.mulVec_add, hgd, e1', add_assoc, V3_add_self, add_zero]
  apply Units.ext
  rw [Units.val_mul, Units.val_one]
  refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
  simp only [Matrix.toLin'_apply, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
  exact h2 v

private theorem isPGroup_Qlln (l : Submodule (ZMod 2) V3) : IsPGroup 2 (Qlln l) := by
  intro x
  exact ⟨1, Subtype.ext (by rw [Subgroup.coe_pow, pow_one, pow_two, Qlln_mul_self x.2]; rfl)⟩

private theorem Qlln_le_Lln (l : Submodule (ZMod 2) V3) : Qlln l ≤ Lln l := by
  intro g hg
  refine (mem_Lln g l).2 fun v hv => ⟨?_, ?_⟩
  · rw [hg.1 v hv]
    exact hv
  · have h1 : ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v = v := by
      conv_lhs => rw [← hg.1 v hv]
      exact inv_mulVec_mulVec g v
    rw [h1]
    exact hv

private theorem Lln_conj_Qlln {l : Submodule (ZMod 2) V3} {h g : GL (Fin 3) (ZMod 2)}
    (hh : h ∈ Lln l) (hg : g ∈ Qlln l) : h * g * h⁻¹ ∈ Qlln l := by
  refine ⟨fun v hv => ?_, fun v => ?_⟩
  · have hi : ((h⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ l :=
      ((mem_Lln h l).1 hh v hv).2
    rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      hg.1 _ hi, mulVec_inv_mulVec h v]
  · have h1 := hg.2 (((h⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v)
    have h2 := ((mem_Lln h l).1 hh _ h1).1
    rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [Matrix.mulVec_sub, mulVec_inv_mulVec h v] at h2
    exact h2

private theorem Lln_le_normalizer_Qlln (l : Submodule (ZMod 2) V3) :
    Lln l ≤ Subgroup.normalizer (Qlln l : Set (GL (Fin 3) (ZMod 2))) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact Lln_conj_Qlln hh hx
  · intro hx
    have := Lln_conj_Qlln (Subgroup.inv_mem _ hh) hx
    have e : h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x := by group
    rwa [e] at this

private theorem pCoreOf_Lpt {c : GL (Fin 3) (ZMod 2)} {p : V3}
    (hc : (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec e1 = p) :
    CFSG.Open.pCoreOf 2 (Lpt p) = Qpt p := by
  have hw : ((c * swapGL : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec e1 =
      p := by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, swapGL_mulVec_e1, hc]
  have hmain := pCoreOf_eq_of_two (H := Lpt p) (S₁ := conjSub c B0)
    (S₂ := conjSub (c * swapGL) B0) (Q := conjSub c (Qpt e1)) (B0_conj_le_Lpt hc)
    (B0_conj_le_Lpt hw) (isPGroup_conjSub c isPGroup_B0) (isPGroup_conjSub _ isPGroup_B0)
    (by rw [index_conjSub]; exact not_two_dvd_index_B0)
    (by rw [index_conjSub]; exact not_two_dvd_index_B0) pt_inter
    (by rw [← Qpt_eq_conj hc]; exact Qpt_le_Lpt p)
    (by rw [← Qpt_eq_conj hc]; exact Lpt_le_normalizer_Qpt p)
    (by rw [← Qpt_eq_conj hc]; exact isPGroup_Qpt p)
  rw [hmain, Qpt_eq_conj hc]

private theorem pCoreOf_Lln {c : GL (Fin 3) (ZMod 2)} {l : Submodule (ZMod 2) V3}
    (hc : ∀ v : V3, (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ l ↔ v 2 = 0) :
    CFSG.Open.pCoreOf 2 (Lln l) = Qlln l := by
  have hw : ∀ v : V3,
      ((c * swap01GL : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ l ↔
        v 2 = 0 := by
    intro v
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hc]
    simp [swap01GL, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have hmain := pCoreOf_eq_of_two (H := Lln l) (S₁ := conjSub c B0)
    (S₂ := conjSub (c * swap01GL) B0) (Q := conjSub c (Qlln line0)) (B0_conj_le_Lln hc)
    (B0_conj_le_Lln hw) (isPGroup_conjSub c isPGroup_B0) (isPGroup_conjSub _ isPGroup_B0)
    (by rw [index_conjSub]; exact not_two_dvd_index_B0)
    (by rw [index_conjSub]; exact not_two_dvd_index_B0) ln_inter
    (by rw [← Qlln_eq_conj hc]; exact Qlln_le_Lln l)
    (by rw [← Qlln_eq_conj hc]; exact Lln_le_normalizer_Qlln l)
    (by rw [← Qlln_eq_conj hc]; exact isPGroup_Qlln l)
  rw [hmain, Qlln_eq_conj hc]

end H52pc

section H52tr

private theorem gl3Act_cancel (c : GL (Fin 3) (ZMod 2)) (z : PermV) :
    gl3Act c⁻¹ (gl3Act c z) = z := by
  rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]

private theorem gl3Act_cancel' (c : GL (Fin 3) (ZMod 2)) (z : PermV) :
    gl3Act c (gl3Act c⁻¹ z) = z := by
  rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

private theorem gl3Act_conj_apply (c x : GL (Fin 3) (ZMod 2)) (f : PermV) :
    gl3Act (c * x * c⁻¹) f = gl3Act c (gl3Act x (gl3Act c⁻¹ f)) := by
  rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply]

private theorem mem_conjSub_map {c : GL (Fin 3) (ZMod 2)} {X : Subgroup (GL (Fin 3) (ZMod 2))}
    {y : MulAut PermV} :
    y ∈ (conjSub c X).map gl3Act ↔ ∃ x0 ∈ X, gl3Act (c * x0 * c⁻¹) = y := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨c⁻¹ * z * c, mem_conjSub.1 hz, ?_⟩
    congr 1
    group
  · rintro ⟨x0, hx0, rfl⟩
    refine ⟨c * x0 * c⁻¹, mem_conjSub.2 ?_, rfl⟩
    have e : c⁻¹ * (c * x0 * c⁻¹) * c = x0 := by group
    rw [e]
    exact hx0

private theorem H52tr_K (c : GL (Fin 3) (ZMod 2)) (X : Subgroup (GL (Fin 3) (ZMod 2))) :
    Ucore ⊓ fixV ((conjSub c X).map gl3Act) =
      (Ucore ⊓ fixV (X.map gl3Act)).map (gl3Act c).toMonoidHom := by
  ext f
  constructor
  · intro hf
    obtain ⟨hfU, hfix⟩ := Subgroup.mem_inf.1 hf
    have hfix' := mem_fixV.1 hfix
    refine Subgroup.mem_map.2 ⟨gl3Act c⁻¹ f, Subgroup.mem_inf.2 ⟨Ucore_inv _ _ hfU, ?_⟩,
      gl3Act_cancel' c f⟩
    refine mem_fixV.2 fun x hx => ?_
    obtain ⟨x0, hx0, rfl⟩ := Subgroup.mem_map.1 hx
    have h := hfix' (gl3Act (c * x0 * c⁻¹)) (mem_conjSub_map.2 ⟨x0, hx0, rfl⟩)
    have h1 : gl3Act c (gl3Act x0 (gl3Act c⁻¹ f)) = f := (gl3Act_conj_apply c x0 f).symm.trans h
    exact (gl3Act_cancel c _).symm.trans (congrArg (gl3Act c⁻¹) h1)
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨hgU, hgfix⟩ := Subgroup.mem_inf.1 hg
    refine Subgroup.mem_inf.2 ⟨Ucore_inv _ _ hgU, mem_fixV.2 fun y hy => ?_⟩
    obtain ⟨x0, hx0, rfl⟩ := mem_conjSub_map.1 hy
    have hx := (mem_fixV.1 hgfix) (gl3Act x0) (Subgroup.mem_map_of_mem _ hx0)
    show gl3Act (c * x0 * c⁻¹) (gl3Act c g) = gl3Act c g
    rw [gl3Act_conj_apply, gl3Act_cancel]
    exact congrArg (gl3Act c) hx

end H52tr

private theorem H52seven_zfix_decide : ∀ a b c d e f g h i : ZMod 2,
    (!![a, b, c; d, e, f; g, h, i] : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
        !![a, b, c; d, e, f; g, h, i] * !![a, b, c; d, e, f; g, h, i] = 1 →
    (!![a, b, c; d, e, f; g, h, i] : Matrix (Fin 3) (Fin 3) (ZMod 2)) ≠ 1 →
    ∀ q : Fin 3 → ZMod 2, q ≠ 0 →
      (!![a, b, c; d, e, f; g, h, i] : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec q = q →
      ∀ v : Fin 3 → ZMod 2,
        (!![a, b, c; d, e, f; g, h, i] : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v = v →
        v = 0 ∨ v = q := by
  decide +kernel

private theorem H52seven_zfix (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) (h3 : M * M * M = 1)
    (h1 : M ≠ 1) (q : V3) (hq : q ≠ 0) (hMq : M.mulVec q = q) (v : V3)
    (hv : M.mulVec v = v) : v = 0 ∨ v = q := by
  have hM : (!![M 0 0, M 0 1, M 0 2; M 1 0, M 1 1, M 1 2; M 2 0, M 2 1, M 2 2] :
      Matrix (Fin 3) (Fin 3) (ZMod 2)) = M := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have key := H52seven_zfix_decide (M 0 0) (M 0 1) (M 0 2) (M 1 0) (M 1 1) (M 1 2)
    (M 2 0) (M 2 1) (M 2 2)
  exact key (by rw [hM]; exact h3) (by rw [hM]; exact h1) q hq (by rw [hM]; exact hMq) v
    (by rw [hM]; exact hv)

private theorem H52seven_mat3 (z : GL (Fin 3) (ZMod 2)) (hz3 : z ^ 3 = 1) :
    (z : Matrix (Fin 3) (Fin 3) (ZMod 2)) * (z : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
      (z : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 := by
  have h := congrArg Units.val hz3
  rw [Units.val_pow_eq_pow_val, Units.val_one, pow_three'] at h
  exact h

private theorem H52seven_cube (z : GL (Fin 3) (ZMod 2)) (hz3 : z ^ 3 = 1) (v : V3) :
    (z : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
      ((z : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
        ((z : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v)) = v := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, H52seven_mat3 z hz3, Matrix.one_mulVec]

private theorem H52seven_mat1 (z : GL (Fin 3) (ZMod 2)) (hz1 : z ≠ 1) :
    (z : Matrix (Fin 3) (Fin 3) (ZMod 2)) ≠ 1 := by
  intro h
  apply hz1
  apply Units.ext
  rw [Units.val_one]
  exact h

private theorem H52seven_key3 : ∀ x y w : ZMod 2, 0 = x + y + w → x = y + w := by decide

private theorem H52seven_fresh : ∀ q : V3, q ≠ 0 → ∃ v : V3, v ≠ 0 ∧ v ≠ q := by decide

private theorem H52seven_notmem (l : Submodule (ZMod 2) V3) (hl : IsLine l) (q : V3) (hq : q ≠ 0)
    (M : Matrix (Fin 3) (Fin 3) (ZMod 2))
    (hMMM : ∀ v : V3, M.mulVec (M.mulVec (M.mulVec v)) = v)
    (hMinj : ∀ u w : V3, M.mulVec u = M.mulVec w → u = w)
    (hMfix : ∀ v : V3, M.mulVec v = v → v = 0 ∨ v = q)
    (hMq : M.mulVec q = q) (hMl : ∀ v ∈ l, M.mulVec v ∈ l)
    (hM0 : ∀ v : V3, M.mulVec v = 0 → v = 0) : q ∉ l := by
  classical
  intro hqc
  have hA2 : 1 < (Finset.univ.filter (fun v : V3 => v ∈ l ∧ v ≠ 0)).card := by
    rw [card_mem_l_ne_zero l hl]
    norm_num
  obtain ⟨s, hs, hsq⟩ := Finset.exists_mem_ne hA2 q
  obtain ⟨-, hsl, hs0⟩ := Finset.mem_filter.1 hs
  have hMs : M.mulVec s ∈ l := hMl s hsl
  have hMMs : M.mulVec (M.mulVec s) ∈ l := hMl _ hMs
  have hsfix : s ≠ M.mulVec s := fun h => (hMfix s h.symm).elim hs0 hsq
  have hsMMs : s ≠ M.mulVec (M.mulVec s) := by
    intro h
    apply hsfix
    have h2 := congrArg (fun v => M.mulVec v) h
    simp only [hMMM] at h2
    exact h2.symm
  have hMsMMs : M.mulVec s ≠ M.mulVec (M.mulVec s) := fun h => hsfix (hMinj _ _ h)
  have h0s : (0 : V3) ≠ s := fun h => hs0 h.symm
  have h0q : (0 : V3) ≠ q := fun h => hq h.symm
  have h0Ms : (0 : V3) ≠ M.mulVec s := fun h => hs0 (hM0 s h.symm)
  have h0MMs : (0 : V3) ≠ M.mulVec (M.mulVec s) := fun h => hs0 (hM0 s (hM0 _ h.symm))
  have hqs : q ≠ s := fun h => hsq h.symm
  have hqMs : q ≠ M.mulVec s := fun h => hsq (by
    have h2 := hMMM s
    simp only [← h, hMq] at h2
    exact h2.symm)
  have hqMMs : q ≠ M.mulVec (M.mulVec s) := fun h => hsq (by
    have h2 := hMMM s
    simp only [← h, hMq] at h2
    exact h2.symm)
  have n1 : (0 : V3) ∉ ({q, s, M.mulVec s, M.mulVec (M.mulVec s)} : Finset V3) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h0q, h0s, h0Ms, h0MMs⟩
  have n2 : q ∉ ({s, M.mulVec s, M.mulVec (M.mulVec s)} : Finset V3) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hqs, hqMs, hqMMs⟩
  have n3 : s ∉ ({M.mulVec s, M.mulVec (M.mulVec s)} : Finset V3) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hsfix, hsMMs⟩
  have hT5 : ({0, q, s, M.mulVec s, M.mulVec (M.mulVec s)} : Finset V3).card = 5 := by
    rw [Finset.card_insert_of_notMem n1, Finset.card_insert_of_notMem n2,
      Finset.card_insert_of_notMem n3, Finset.card_pair hMsMMs]
    all_goals norm_num
  have hsub : ({0, q, s, M.mulVec s, M.mulVec (M.mulVec s)} : Finset V3) ⊆
      Finset.univ.filter (fun v : V3 => v ∈ l) := by
    intro x hx
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h | h | h | h <;> rw [h]
    · exact l.zero_mem
    · exact hqc
    · exact hsl
    · exact hMs
    · exact hMMs
  have hle := Finset.card_le_card hsub
  rw [hT5, card_mem_l l hl] at hle
  omega

private theorem H52seven_orbit3 (M : Matrix (Fin 3) (Fin 3) (ZMod 2))
    (hMMM : ∀ v : V3, M.mulVec (M.mulVec (M.mulVec v)) = v)
    (hMinj : ∀ u w : V3, M.mulVec u = M.mulVec w → u = w) (s : V3) (hs : s ≠ M.mulVec s) :
    ({s, M.mulVec s, M.mulVec (M.mulVec s)} : Finset V3).card = 3 := by
  classical
  have h1 : M.mulVec s ≠ M.mulVec (M.mulVec s) := fun h => hs (hMinj _ _ h)
  have h2 : s ≠ M.mulVec (M.mulVec s) := by
    intro h
    apply hs
    have h3 := congrArg (fun v => M.mulVec v) h
    simp only [hMMM] at h3
    exact h3.symm
  have n3 : s ∉ ({M.mulVec s, M.mulVec (M.mulVec s)} : Finset V3) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hs, h2⟩
  rw [Finset.card_insert_of_notMem n3, Finset.card_pair h1]
  all_goals norm_num

private theorem H52seven_const (M : Matrix (Fin 3) (Fin 3) (ZMod 2))
    (hMMM : ∀ v : V3, M.mulVec (M.mulVec (M.mulVec v)) = v)
    (hMinj : ∀ u w : V3, M.mulVec u = M.mulVec w → u = w)
    (φ : V3 → ZMod 2) (hφ : ∀ v : V3, φ (M.mulVec v) = φ v)
    (A : Finset V3) (hA : A.card = 3) (hAM : ∀ v ∈ A, M.mulVec v ∈ A)
    (s : V3) (hs : s ∈ A) (hne : s ≠ M.mulVec s) : ∀ w ∈ A, φ w = φ s := by
  classical
  have hsub : ({s, M.mulVec s, M.mulVec (M.mulVec s)} : Finset V3) ⊆ A := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h | h <;> rw [h]
    · exact hs
    · exact hAM _ hs
    · exact hAM _ (hAM _ hs)
  have heq : ({s, M.mulVec s, M.mulVec (M.mulVec s)} : Finset V3) = A :=
    Finset.eq_of_subset_of_card_le hsub
      (le_of_eq (by rw [hA, H52seven_orbit3 M hMMM hMinj s hne]))
  intro w hw
  rw [← heq] at hw
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with h | h | h
  · rw [h]
  · rw [h]
    exact hφ s
  · rw [h, hφ, hφ]

open scoped Classical in
private theorem H52seven_ident (l : Submodule (ZMod 2) V3) (q : V3) (hq : q ≠ 0)
    (hql : q ∉ l) (g : PermV) (a b c : ZMod 2) (hc : c = a + b)
    (hpt : ∀ v : V3, Multiplicative.toAdd g v =
      (if v = q then c else 0) + (if v ∉ l ∧ v ≠ q then a else 0) +
        (if v ∈ l ∧ v ≠ 0 then b else 0)) :
    g = 1 ∨ g = uOf (l : Set V3) ∨ g = uOf ({q} : Set V3) ∨
      g = uOf (l : Set V3) * uOf ({q} : Set V3) := by
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  have hl0 : (0 : V3) ∈ l := l.zero_mem
  have hq0 : (0 : V3) ≠ q := fun h => hq h.symm
  have htri : ∀ v : V3, v = 0 ∨ v = q ∨ (v ∈ l ∧ v ≠ 0) ∨ (v ∉ l ∧ v ≠ q) := by
    intro v
    by_cases h0 : v = 0
    · exact Or.inl h0
    by_cases hvq : v = q
    · exact Or.inr (Or.inl hvq)
    by_cases hvl : v ∈ l
    · exact Or.inr (Or.inr (Or.inl ⟨hvl, h0⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hvl, hvq⟩))
  subst hc
  rcases H5_zmod2_cases a with rfl | rfl <;> rcases H5_zmod2_cases b with rfl | rfl
  ·
    left
    apply eq_of_toAdd_eq
    intro v
    rw [hpt v]
    simp
  ·
    right; right; right
    apply eq_of_toAdd_eq
    intro v
    rw [hpt v, toAdd_mul, Pi.add_apply, toAdd_uOf_lset, toAdd_uOf1]
    rcases htri v with rfl | rfl | ⟨hvl, hv0⟩ | ⟨hvl, hvq⟩
    · simp [hl0, hq0]
    · simp [hql, hq, h11]
    · have hvq : v ≠ q := fun h => hql (h ▸ hvl)
      simp [hvl, hv0, hvq]
    · have hv0 : v ≠ 0 := fun h => hvl (h ▸ hl0)
      simp [hvl, hvq, hv0, h11]
  ·
    right; left
    apply eq_of_toAdd_eq
    intro v
    rw [hpt v, toAdd_uOf_lset]
    rcases htri v with rfl | rfl | ⟨hvl, hv0⟩ | ⟨hvl, hvq⟩
    · simp [hl0, hq0]
    · simp [hql, hq]
    · have hvq : v ≠ q := fun h => hql (h ▸ hvl)
      simp [hvl, hv0, hvq]
    · have hv0 : v ≠ 0 := fun h => hvl (h ▸ hl0)
      simp [hvl, hvq, hv0]
  ·
    right; right; left
    apply eq_of_toAdd_eq
    intro v
    rw [hpt v, toAdd_uOf1]
    rcases htri v with rfl | rfl | ⟨hvl, hv0⟩ | ⟨hvl, hvq⟩
    · simp [hl0, hq0]
    · simp [hql, hq, h11]
    · have hvq : v ≠ q := fun h => hql (h ▸ hvl)
      simp [hvl, hv0, hvq, h11]
    · have hv0 : v ≠ 0 := fun h => hvl (h ▸ hl0)
      simp [hvl, hvq, hv0, h11]

private theorem H52seven_core (l : Submodule (ZMod 2) V3) (hl : IsLine l) (q : V3) (hq : q ≠ 0)
    (M : Matrix (Fin 3) (Fin 3) (ZMod 2))
    (hMMM : ∀ v : V3, M.mulVec (M.mulVec (M.mulVec v)) = v)
    (hMinj : ∀ u w : V3, M.mulVec u = M.mulVec w → u = w)
    (hMfix : ∀ v : V3, M.mulVec v = v → v = 0 ∨ v = q)
    (hMq : M.mulVec q = q) (hMl : ∀ v ∈ l, M.mulVec v ∈ l)
    (hM0 : ∀ v : V3, M.mulVec v = 0 → v = 0)
    (f : PermV) (hfM : ∀ v : V3, Multiplicative.toAdd f (M.mulVec v) = Multiplicative.toAdd f v)
    (hf0 : Multiplicative.toAdd f 0 = 0) (hfs : ∑ v : V3, Multiplicative.toAdd f v = 0) :
    f = 1 ∨ f = uOf (l : Set V3) ∨ f = uOf ({q} : Set V3) ∨
      f = uOf (l : Set V3) * uOf ({q} : Set V3) := by
  classical
  have hql : q ∉ l := H52seven_notmem l hl q hq M hMMM hMinj hMfix hMq hMl hM0
  obtain ⟨A1, hA1def⟩ : ∃ A : Finset V3,
      A = Finset.univ.filter (fun v : V3 => v ∉ l ∧ v ≠ q) := ⟨_, rfl⟩
  obtain ⟨A2, hA2def⟩ : ∃ A : Finset V3,
      A = Finset.univ.filter (fun v : V3 => v ∈ l ∧ v ≠ 0) := ⟨_, rfl⟩
  have hmemA1 : ∀ v : V3, v ∈ A1 ↔ v ∉ l ∧ v ≠ q := fun v => by
    rw [hA1def, Finset.mem_filter]
    simp
  have hmemA2 : ∀ v : V3, v ∈ A2 ↔ v ∈ l ∧ v ≠ 0 := fun v => by
    rw [hA2def, Finset.mem_filter]
    simp
  have hA1card : A1.card = 3 := by
    have hfe : A1 = (Finset.univ.filter (fun v : V3 => v ∉ l)).erase q := by
      ext v
      rw [hmemA1, Finset.mem_erase, Finset.mem_filter]
      simp only [Finset.mem_univ, true_and]
      exact and_comm
    have hqmem : q ∈ Finset.univ.filter (fun v : V3 => v ∉ l) :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hql⟩
    rw [hfe, Finset.card_erase_of_mem hqmem, card_compl_l l hl]
    all_goals norm_num
  have hA2card : A2.card = 3 := by
    rw [hA2def]
    exact card_mem_l_ne_zero l hl
  obtain ⟨s1, hs1⟩ : A1.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨s2, hs2⟩ : A2.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨hs1l, hs1q⟩ := (hmemA1 s1).1 hs1
  obtain ⟨hs2l, hs20⟩ := (hmemA2 s2).1 hs2
  have hs10 : s1 ≠ 0 := fun h => hs1l (by rw [h]; exact l.zero_mem)
  have hs2q : s2 ≠ q := fun h => hql (by rw [← h]; exact hs2l)
  have hs1fix : s1 ≠ M.mulVec s1 := fun h => (hMfix s1 h.symm).elim hs10 hs1q
  have hs2fix : s2 ≠ M.mulVec s2 := fun h => (hMfix s2 h.symm).elim hs20 hs2q
  have hAM1 : ∀ v ∈ A1, M.mulVec v ∈ A1 := by
    intro v hv
    obtain ⟨hvl, hvq⟩ := (hmemA1 v).1 hv
    refine (hmemA1 _).2 ⟨fun h => hvl ?_, fun h => hvq ?_⟩
    · have h3 := hMl _ (hMl _ h)
      rwa [hMMM v] at h3
    · have h2 := hMMM v
      simp only [h, hMq] at h2
      exact h2.symm
  have hAM2 : ∀ v ∈ A2, M.mulVec v ∈ A2 := by
    intro v hv
    obtain ⟨hvl, hv0⟩ := (hmemA2 v).1 hv
    exact (hmemA2 _).2 ⟨hMl v hvl, fun h => hv0 (hM0 v h)⟩
  have hc1 : ∀ w ∈ A1, Multiplicative.toAdd f w = Multiplicative.toAdd f s1 :=
    H52seven_const M hMMM hMinj (fun v => Multiplicative.toAdd f v) hfM A1 hA1card hAM1 s1
      hs1 hs1fix
  have hc2 : ∀ w ∈ A2, Multiplicative.toAdd f w = Multiplicative.toAdd f s2 :=
    H52seven_const M hMMM hMinj (fun v => Multiplicative.toAdd f v) hfM A2 hA2card hAM2 s2
      hs2 hs2fix
  have hpt : ∀ v : V3, Multiplicative.toAdd f v =
      (if v = q then Multiplicative.toAdd f q else 0) +
        (if v ∈ A1 then Multiplicative.toAdd f s1 else 0) +
        (if v ∈ A2 then Multiplicative.toAdd f s2 else 0) := by
    intro v
    by_cases hvq : v = q
    · have hnA1 : v ∉ A1 := fun h => ((hmemA1 v).1 h).2 hvq
      have hnA2 : v ∉ A2 := fun h => by
        have h' := ((hmemA2 v).1 h).1
        rw [hvq] at h'
        exact hql h'
      rw [if_pos hvq, if_neg hnA1, if_neg hnA2]
      simp only [add_zero]
      rw [hvq]
    · by_cases hvl : v ∈ l
      · by_cases hv0 : v = 0
        · have hnA1 : v ∉ A1 := fun h => ((hmemA1 v).1 h).1 hvl
          have hnA2 : v ∉ A2 := fun h => ((hmemA2 v).1 h).2 hv0
          rw [if_neg hvq, if_neg hnA1, if_neg hnA2, hv0, hf0]
          all_goals simp
        · have hvA2 : v ∈ A2 := (hmemA2 v).2 ⟨hvl, hv0⟩
          have hnA1 : v ∉ A1 := fun h => ((hmemA1 v).1 h).1 hvl
          rw [if_neg hvq, if_neg hnA1, if_pos hvA2]
          simp only [zero_add, add_zero]
          exact hc2 v hvA2
      · have hvA1 : v ∈ A1 := (hmemA1 v).2 ⟨hvl, hvq⟩
        have hnA2 : v ∉ A2 := fun h => hvl ((hmemA2 v).1 h).1
        rw [if_neg hvq, if_pos hvA1, if_neg hnA2]
        simp only [zero_add, add_zero]
        exact hc1 v hvA1
  have hsum : ∑ v : V3, Multiplicative.toAdd f v =
      Multiplicative.toAdd f q + ((A1.card : ℕ) : ZMod 2) * Multiplicative.toAdd f s1 +
        ((A2.card : ℕ) : ZMod 2) * Multiplicative.toAdd f s2 :=
    sum_three (fun v => Multiplicative.toAdd f v) q A1 A2 _ _ _ hpt
  rw [hfs, hA1card, hA2card] at hsum
  have h3 : ((3 : ℕ) : ZMod 2) = 1 := by decide
  rw [h3, one_mul, one_mul] at hsum
  have hγ : Multiplicative.toAdd f q = Multiplicative.toAdd f s1 + Multiplicative.toAdd f s2 :=
    H52seven_key3 _ _ _ hsum
  have hpt' : ∀ v : V3, Multiplicative.toAdd f v =
      (if v = q then Multiplicative.toAdd f q else 0) +
        (if v ∉ l ∧ v ≠ q then Multiplicative.toAdd f s1 else 0) +
        (if v ∈ l ∧ v ≠ 0 then Multiplicative.toAdd f s2 else 0) := by
    intro v
    rw [hpt v]
    simp only [hmemA1, hmemA2]
  exact H52seven_ident l q hq hql f _ _ _ hγ hpt'

private theorem H52_seven (l : Submodule (ZMod 2) V3) (hl : IsLine l) :
    ∀ (Y : Subgroup (GL (Fin 3) (ZMod 2))) (q : V3), IsSylowIn 3 Y (Lln l) → q ≠ 0 →
      (∀ y ∈ Y, (y : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec q = q) →
      (∀ v : V3, (∀ y ∈ Y, (y : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v = v) → v = 0 ∨ v = q) →
      Ucore ⊓ fixV (Y.map gl3Act) = Subgroup.closure {uOf (l : Set V3), uOf {q}} := by
  intro Y q hY hq hYq hYC
  classical
  unfold IsSylowIn at hY
  obtain ⟨hYle, hYp, -⟩ := hY
  apply le_antisymm
  · intro f hf
    obtain ⟨hfU, hfix⟩ := Subgroup.mem_inf.1 hf
    obtain ⟨hf0, hfs⟩ := mem_Ucore'.1 hfU
    have hfY : ∀ t ∈ Y, gl3Act t f = f := fun t ht =>
      (mem_fixV.1 hfix) (gl3Act t) (Subgroup.mem_map_of_mem gl3Act ht)
    have hYne : Y ≠ ⊥ := by
      intro hbot
      obtain ⟨v, hv0, hvq⟩ := H52seven_fresh q hq
      have hall : ∀ y ∈ Y, (y : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v = v := by
        intro y hy
        rw [hbot, Subgroup.mem_bot] at hy
        rw [hy, Units.val_one, Matrix.one_mulVec]
      rcases hYC v hall with h | h
      · exact hv0 h
      · exact hvq h
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    have hcard1 : 1 < Nat.card ↥Y := by
      haveI : Nontrivial ↥Y := (Subgroup.nontrivial_iff_ne_bot Y).2 hYne
      exact Finite.one_lt_card
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 3)).1 hYp
    have h3dvd : 3 ∣ Nat.card ↥Y := by
      rw [hn] at hcard1 ⊢
      have hn0 : n ≠ 0 := by
        rintro rfl
        simp at hcard1
      exact dvd_pow_self 3 hn0
    obtain ⟨z, hzY, hz3, hz1⟩ : ∃ z ∈ Y, z ^ 3 = 1 ∧ z ≠ 1 := by
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y) 3 h3dvd
      refine ⟨(x : GL (Fin 3) (ZMod 2)), x.2, ?_, ?_⟩
      · have h1 : x ^ 3 = 1 := by
          have h4 := pow_orderOf_eq_one x
          rwa [hx] at h4
        rw [← Subgroup.coe_pow, h1, Subgroup.coe_one]
      · intro h
        have h2 : x = 1 := Subtype.ext h
        rw [h2, orderOf_one] at hx
        norm_num at hx
    have hfz : gl3Act z f = f := hfY z hzY
    have hcore := H52seven_core l hl q hq (z : Matrix (Fin 3) (Fin 3) (ZMod 2))
      (H52seven_cube z hz3) (fun u w h => gl_mulVec_injective z h)
      (fun v hv => H52seven_zfix _ (H52seven_mat3 z hz3) (H52seven_mat1 z hz1) q hq
        (hYq z hzY) v hv)
      (hYq z hzY) (fun v hv => ((mem_Lln z l).1 (hYle hzY) v hv).1)
      (fun v hv => (gl_mulVec_zero_iff z v).1 hv) f
      (fun v => (fix_const f z hfz v).symm) hf0 hfs
    rcases hcore with h | h | h | h <;> rw [h]
    · exact one_mem _
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  · rw [Subgroup.closure_le]
    intro x hx
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · refine Subgroup.mem_inf.2 ⟨uOf_l_mem_Ucore l hl, mem_fixV.2 fun y hy => ?_⟩
      obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hy
      exact gl3Act_uOf_l_T (Lln l) l (fun g hg v hv => ((mem_Lln g l).1 hg v hv).1) t (hYle ht)
    · refine Subgroup.mem_inf.2 ⟨uOf_pt_mem_Ucore q hq, mem_fixV.2 fun y hy => ?_⟩
      obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hy
      exact gl3Act_uOf_pt q t ((mem_Lpt _ _).2 fun v hv => by
        rw [Set.mem_singleton_iff.1 hv]
        exact hYq t ht)

section H52asm

private abbrev H52B_tM (a b : ZMod 2) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  !![1, a, b; 0, 1, 0; 0, 0, 1]

private theorem H52B_tM_mul : ∀ a b : ZMod 2, H52B_tM a b * H52B_tM a b = 1 := by
  decide +kernel

private theorem H52B_tM_Q0 : ∀ a b : ZMod 2, Q0M (H52B_tM a b) := by
  decide +kernel

private theorem H52B_Q0M_eq : ∀ M : Matrix (Fin 3) (Fin 3) (ZMod 2),
    Q0M M → M = H52B_tM (M 0 1) (M 0 2) := by
  decide +kernel

private def H52B_tGL (a b : ZMod 2) : GL (Fin 3) (ZMod 2) :=
  ⟨H52B_tM a b, H52B_tM a b, H52B_tM_mul a b, H52B_tM_mul a b⟩

private theorem H52B_tGL_inv_val (a b : ZMod 2) :
    (((H52B_tGL a b)⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      H52B_tM a b := rfl

private theorem H52B_tGL_mem (a b : ZMod 2) : H52B_tGL a b ∈ Qpt e1 :=
  (mem_Qpt_e1 _).2 (H52B_tM_Q0 a b)

private theorem H52B_Qpt_form {g : GL (Fin 3) (ZMod 2)} (hg : g ∈ Qpt e1) :
    ∃ a b : ZMod 2, (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) = H52B_tM a b :=
  ⟨_, _, H52B_Q0M_eq _ ((mem_Qpt_e1 g).1 hg)⟩

private theorem H52B_tM_pair : ∀ a b : ZMod 2, ∀ y : V3,
    (H52B_tM a b).mulVec y = y ∨
      ((H52B_tM a b).mulVec y = y + e1 ∧ (y 1 ≠ 0 ∨ y 2 ≠ 0)) := by
  decide +kernel

private theorem H52B_tM_shape : ∀ a b : ZMod 2, ∀ v : V3,
    ((H52B_tM a b).mulVec v = v ∧ (H52B_tM a b).mulVec (v + e1) = v + e1) ∨
      ((H52B_tM a b).mulVec v = v + e1 ∧ (H52B_tM a b).mulVec (v + e1) = v) := by
  decide +kernel

private theorem H52B_tM_exists : ∀ v : V3, (v 1 ≠ 0 ∨ v 2 ≠ 0) →
    ∃ a b : ZMod 2, (H52B_tM a b).mulVec v = v + e1 := by
  decide +kernel

private theorem H52B_mem_A {x : MulAut PermV} (hx : x ∈ (Qpt e1).map gl3Act) :
    ∃ g ∈ Qpt e1, gl3Act g = x :=
  Subgroup.mem_map.1 hx

private theorem H52B_fix_iff (f : PermV) :
    f ∈ fixV ((Qpt e1).map gl3Act) ↔
      ∀ v : V3, (v 1 ≠ 0 ∨ v 2 ≠ 0) →
        Multiplicative.toAdd f (v + e1) = Multiplicative.toAdd f v := by
  rw [mem_fixV]
  constructor
  · intro hf v hv
    obtain ⟨a, b, hab⟩ := H52B_tM_exists v hv
    have h : gl3Act (H52B_tGL a b) f = f :=
      hf _ (Subgroup.mem_map_of_mem gl3Act (H52B_tGL_mem a b))
    have h2 : Multiplicative.toAdd (gl3Act (H52B_tGL a b) f) v = Multiplicative.toAdd f v := by
      rw [h]
    rw [gl3Act_toAdd, H52B_tGL_inv_val, hab] at h2
    exact h2
  · intro hf x hx
    obtain ⟨g, hg, hgx⟩ := H52B_mem_A hx
    subst hgx
    have key : ∀ y : V3, Multiplicative.toAdd (gl3Act g f) y = Multiplicative.toAdd f y := by
      intro y
      rw [gl3Act_toAdd]
      obtain ⟨a, b, hab⟩ := H52B_Qpt_form (Subgroup.inv_mem _ hg)
      rw [hab]
      rcases H52B_tM_pair a b y with h | ⟨h, hy⟩
      · rw [h]
      · rw [h]
        exact hf y hy
    exact Multiplicative.toAdd.injective (funext key)

private theorem H52B_ne : ∀ v : V3, v ≠ v + e1 := by decide

private theorem H52B_pair_inv : ∀ v w : V3,
    (if w + e1 = v ∨ w + e1 = v + e1 then (1 : ZMod 2) else 0) =
      if w = v ∨ w = v + e1 then 1 else 0 := by
  decide +kernel

private theorem H52B_pair_mem (v : V3) (hv : v ≠ 0) (hv' : v + e1 ≠ 0) :
    pairV v (v + e1) ∈ Ucore ⊓ fixV ((Qpt e1).map gl3Act) := by
  refine Subgroup.mem_inf.2 ⟨(O3_ucore (pairV v (v + e1)) ?_).1, (H52B_fix_iff _).2 ?_⟩
  · rw [O3set_eq]
    exact ⟨v, v + e1, hv, hv', H52B_ne v, rfl⟩
  · intro w _
    rw [toAdd_pairV, toAdd_pairV]
    exact H52B_pair_inv v w

private theorem H52B_F_mem (v : V3) (hv : v ≠ 0) (hne : v ≠ e1) : pairV v e1 ∈ Ucore :=
  (O3_ucore (pairV v e1) (by
    rw [O3set_eq]
    exact ⟨v, e1, hv, by decide, hne, rfl⟩)).1

private abbrev H52B_e2 : V3 := ![0, 1, 0]
private abbrev H52B_e3 : V3 := ![0, 0, 1]
private abbrev H52B_e23 : V3 := ![0, 1, 1]

private abbrev H52B_P2 : PermV := pairV H52B_e2 (H52B_e2 + e1)
private abbrev H52B_P3 : PermV := pairV H52B_e3 (H52B_e3 + e1)
private abbrev H52B_P23 : PermV := pairV H52B_e23 (H52B_e23 + e1)

private theorem H52B_P2_mem : H52B_P2 ∈ Ucore ⊓ fixV ((Qpt e1).map gl3Act) :=
  H52B_pair_mem H52B_e2 (by decide) (by decide)

private theorem H52B_P3_mem : H52B_P3 ∈ Ucore ⊓ fixV ((Qpt e1).map gl3Act) :=
  H52B_pair_mem H52B_e3 (by decide) (by decide)

private theorem H52B_P23_mem : H52B_P23 ∈ Ucore ⊓ fixV ((Qpt e1).map gl3Act) :=
  H52B_pair_mem H52B_e23 (by decide) (by decide)

private theorem H52B_F2_mem : pairV H52B_e2 e1 ∈ Ucore :=
  H52B_F_mem H52B_e2 (by decide) (by decide)

private theorem H52B_F3_mem : pairV H52B_e3 e1 ∈ Ucore :=
  H52B_F_mem H52B_e3 (by decide) (by decide)

private theorem H52B_F23_mem : pairV H52B_e23 e1 ∈ Ucore :=
  H52B_F_mem H52B_e23 (by decide) (by decide)

private theorem H52B_gen_P2 :
    gl3Act (H52B_tGL 1 0) (pairV H52B_e2 e1) * (pairV H52B_e2 e1)⁻¹ = H52B_P2 := by
  apply Multiplicative.toAdd.injective
  funext x
  revert x
  decide +kernel

private theorem H52B_gen_P3 :
    gl3Act (H52B_tGL 0 1) (pairV H52B_e3 e1) * (pairV H52B_e3 e1)⁻¹ = H52B_P3 := by
  apply Multiplicative.toAdd.injective
  funext x
  revert x
  decide +kernel

private theorem H52B_gen_P23 :
    gl3Act (H52B_tGL 1 0) (pairV H52B_e23 e1) * (pairV H52B_e23 e1)⁻¹ = H52B_P23 := by
  apply Multiplicative.toAdd.injective
  funext x
  revert x
  decide +kernel

private theorem H52B_gen_mem {w : PermV} (g : GL (Fin 3) (ZMod 2)) (hg : g ∈ Qpt e1)
    (hw : w ∈ Ucore) : gl3Act g w * w⁻¹ ∈ commOn Ucore ((Qpt e1).map gl3Act) := by
  unfold commOn
  apply Subgroup.subset_closure
  exact ⟨gl3Act g, Subgroup.mem_map_of_mem gl3Act hg, w, hw, rfl⟩

private theorem H52B_P2_comm : H52B_P2 ∈ commOn Ucore ((Qpt e1).map gl3Act) := by
  rw [← H52B_gen_P2]
  exact H52B_gen_mem _ (H52B_tGL_mem 1 0) H52B_F2_mem

private theorem H52B_P3_comm : H52B_P3 ∈ commOn Ucore ((Qpt e1).map gl3Act) := by
  rw [← H52B_gen_P3]
  exact H52B_gen_mem _ (H52B_tGL_mem 0 1) H52B_F3_mem

private theorem H52B_P23_comm : H52B_P23 ∈ commOn Ucore ((Qpt e1).map gl3Act) := by
  rw [← H52B_gen_P23]
  exact H52B_gen_mem _ (H52B_tGL_mem 1 0) H52B_F23_mem

private theorem H52B_gen_pair (g : GL (Fin 3) (ZMod 2)) (hg : g ∈ Qpt e1) (w : PermV)
    (v : V3) :
    Multiplicative.toAdd (gl3Act g w * w⁻¹) (v + e1) =
      Multiplicative.toAdd (gl3Act g w * w⁻¹) v := by
  obtain ⟨a, b, hab⟩ := H52B_Qpt_form (Subgroup.inv_mem _ hg)
  have hval : ∀ x : V3, Multiplicative.toAdd (gl3Act g w * w⁻¹) x =
      Multiplicative.toAdd w
          (((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec x) +
        Multiplicative.toAdd w x := by
    intro x
    rw [toAdd_mul, Pi.add_apply, gl3Act_toAdd, toAdd_inv, Pi.neg_apply]
    congr 1
    exact ZMod.neg_eq_self_mod_two _
  rw [hval, hval, hab]
  rcases H52B_tM_shape a b v with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
    simp only [CharTwo.add_self_eq_zero]
  · rw [h1, h2]
    exact add_comm _ _

private theorem H52B_comm_le : commOn Ucore ((Qpt e1).map gl3Act) ≤
    Ucore ⊓ fixV ((Qpt e1).map gl3Act) := by
  unfold commOn
  apply (Subgroup.closure_le _).2
  rintro u ⟨a, ha, w, hw, rfl⟩
  obtain ⟨g, hg, rfl⟩ := H52B_mem_A ha
  exact Subgroup.mem_inf.2 ⟨Subgroup.mul_mem _ (Ucore_inv g w hw) (Subgroup.inv_mem _ hw),
    (H52B_fix_iff _).2 fun v _ => H52B_gen_pair g hg w v⟩

private theorem H52B_ite_mem {S : Subgroup PermV} {x : PermV} {p : Prop} [Decidable p]
    (hx : x ∈ S) : (if p then x else 1) ∈ S := by
  split_ifs
  · exact hx
  · exact S.one_mem

private def H52B_Phi (c : V3) : PermV :=
  (if c 0 = 1 then H52B_P2 else 1) * (if c 1 = 1 then H52B_P3 else 1) *
    (if c 2 = 1 then H52B_P23 else 1)

private theorem H52B_Phi_at : ∀ c : V3,
    Multiplicative.toAdd (H52B_Phi c) H52B_e2 = c 0 ∧
      Multiplicative.toAdd (H52B_Phi c) H52B_e3 = c 1 ∧
      Multiplicative.toAdd (H52B_Phi c) H52B_e23 = c 2 := by
  decide +kernel

private theorem H52B_vec_ext : ∀ c d : V3, c 0 = d 0 → c 1 = d 1 → c 2 = d 2 → c = d := by
  decide +kernel

private theorem H52B_Phi_inj : Function.Injective H52B_Phi := by
  intro c d h
  have hc := H52B_Phi_at c
  have hd := H52B_Phi_at d
  rw [h] at hc
  exact H52B_vec_ext c d (hc.1.symm.trans hd.1) (hc.2.1.symm.trans hd.2.1)
    (hc.2.2.symm.trans hd.2.2)

private theorem H52B_Phi_mem_K (c : V3) :
    H52B_Phi c ∈ Ucore ⊓ fixV ((Qpt e1).map gl3Act) := by
  unfold H52B_Phi
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (H52B_ite_mem H52B_P2_mem)
    (H52B_ite_mem H52B_P3_mem)) (H52B_ite_mem H52B_P23_mem)

private theorem H52B_Phi_mem_comm (c : V3) :
    H52B_Phi c ∈ commOn Ucore ((Qpt e1).map gl3Act) := by
  unfold H52B_Phi
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (H52B_ite_mem H52B_P2_comm)
    (H52B_ite_mem H52B_P3_comm)) (H52B_ite_mem H52B_P23_comm)

private theorem H52B_parity : ∀ t s2 s3 s23 : ZMod 2,
    (0 : ZMod 2) + t + s2 + s2 + s3 + s3 + s23 + s23 = 0 → t = 0 := by
  decide

private theorem H52B_e1_zero {f : PermV} (hf : f ∈ Ucore ⊓ fixV ((Qpt e1).map gl3Act)) :
    Multiplicative.toAdd f e1 = 0 := by
  obtain ⟨h0, hs⟩ := mem_Ucore'.1 (Subgroup.mem_inf.1 hf).1
  have hp := (H52B_fix_iff f).1 (Subgroup.mem_inf.1 hf).2
  have p2 : Multiplicative.toAdd f ![1, 1, 0] = Multiplicative.toAdd f ![0, 1, 0] := by
    have h := hp ![0, 1, 0] (by decide)
    rwa [show (![0, 1, 0] + e1 : V3) = ![1, 1, 0] by decide] at h
  have p3 : Multiplicative.toAdd f ![1, 0, 1] = Multiplicative.toAdd f ![0, 0, 1] := by
    have h := hp ![0, 0, 1] (by decide)
    rwa [show (![0, 0, 1] + e1 : V3) = ![1, 0, 1] by decide] at h
  have p23 : Multiplicative.toAdd f ![1, 1, 1] = Multiplicative.toAdd f ![0, 1, 1] := by
    have h := hp ![0, 1, 1] (by decide)
    rwa [show (![0, 1, 1] + e1 : V3) = ![1, 1, 1] by decide] at h
  have h0' : Multiplicative.toAdd f ![0, 0, 0] = 0 := by
    rw [show (![0, 0, 0] : V3) = 0 by decide]
    exact h0
  rw [sum_V3, p2, p3, p23, h0'] at hs
  exact H52B_parity _ _ _ _ hs

private theorem H52B_transl {f : PermV} (hf : f ∈ Ucore ⊓ fixV ((Qpt e1).map gl3Act))
    (v : V3) : Multiplicative.toAdd f (v + e1) = Multiplicative.toAdd f v := by
  by_cases hv : v 1 ≠ 0 ∨ v 2 ≠ 0
  · exact (H52B_fix_iff f).1 (Subgroup.mem_inf.1 hf).2 v hv
  · have key : ∀ w : V3, w 1 = 0 → w 2 = 0 → w = 0 ∨ w = e1 := by decide
    push Not at hv
    have h0 := (mem_Ucore'.1 (Subgroup.mem_inf.1 hf).1).1
    rcases key v hv.1 hv.2 with rfl | rfl
    · rw [zero_add, H52B_e1_zero hf, h0]
    · rw [show (e1 + e1 : V3) = 0 by decide, h0, H52B_e1_zero hf]

private theorem H52B_cover : ∀ x : V3, ∃ v : V3,
    (v = 0 ∨ v = H52B_e2 ∨ v = H52B_e3 ∨ v = H52B_e23) ∧ (x = v ∨ x = v + e1) := by
  decide +kernel

private theorem H52B_agree {f g : PermV} (hf : f ∈ Ucore ⊓ fixV ((Qpt e1).map gl3Act))
    (hg : g ∈ Ucore ⊓ fixV ((Qpt e1).map gl3Act))
    (h2 : Multiplicative.toAdd f H52B_e2 = Multiplicative.toAdd g H52B_e2)
    (h3 : Multiplicative.toAdd f H52B_e3 = Multiplicative.toAdd g H52B_e3)
    (h23 : Multiplicative.toAdd f H52B_e23 = Multiplicative.toAdd g H52B_e23) : f = g := by
  have hf0 := (mem_Ucore'.1 (Subgroup.mem_inf.1 hf).1).1
  have hg0 := (mem_Ucore'.1 (Subgroup.mem_inf.1 hg).1).1
  apply Multiplicative.toAdd.injective
  funext x
  obtain ⟨v, hv, hx⟩ := H52B_cover x
  have hv' : Multiplicative.toAdd f v = Multiplicative.toAdd g v := by
    rcases hv with h | h | h | h <;> rw [h]
    · rw [hf0, hg0]
    · exact h2
    · exact h3
    · exact h23
  rcases hx with h | h
  · rw [h]
    exact hv'
  · rw [h, H52B_transl hf, H52B_transl hg]
    exact hv'

private theorem H52B_surj {f : PermV} (hf : f ∈ Ucore ⊓ fixV ((Qpt e1).map gl3Act)) :
    ∃ c : V3, H52B_Phi c = f := by
  refine ⟨![Multiplicative.toAdd f H52B_e2, Multiplicative.toAdd f H52B_e3,
    Multiplicative.toAdd f H52B_e23], ?_⟩
  have hA := H52B_Phi_at ![Multiplicative.toAdd f H52B_e2, Multiplicative.toAdd f H52B_e3,
    Multiplicative.toAdd f H52B_e23]
  exact H52B_agree (H52B_Phi_mem_K _) hf hA.1 hA.2.1 hA.2.2

private theorem H52B_comm_ge : Ucore ⊓ fixV ((Qpt e1).map gl3Act) ≤
    commOn Ucore ((Qpt e1).map gl3Act) := by
  intro f hf
  obtain ⟨c, rfl⟩ := H52B_surj hf
  exact H52B_Phi_mem_comm c

private theorem H52B_card : Nat.card ↥(Ucore ⊓ fixV ((Qpt e1).map gl3Act)) = 8 := by
  have hset : ∀ x : PermV, x ∈ Ucore ⊓ fixV ((Qpt e1).map gl3Act) ↔
      x ∈ Set.range H52B_Phi := by
    intro x
    constructor
    · intro hx
      obtain ⟨c, hc⟩ := H52B_surj hx
      exact ⟨c, hc⟩
    · rintro ⟨c, rfl⟩
      exact H52B_Phi_mem_K c
  rw [Nat.card_congr (Equiv.subtypeEquivRight hset),
    ← Nat.card_congr (Equiv.ofInjective H52B_Phi H52B_Phi_inj)]
  simp [Nat.card_eq_fintype_card]

private theorem H52B_pt_K : Nat.card ↥(Ucore ⊓ fixV ((Qpt e1).map gl3Act)) = 8 := H52B_card

private theorem H52B_pt_M : Nat.card ↥(commOn Ucore ((Qpt e1).map gl3Act)) = 8 := by
  rw [le_antisymm H52B_comm_le H52B_comm_ge]
  exact H52B_card

private def H52Bl_sM (b c : ZMod 2) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  !![1, 0, b; 0, 1, c; 0, 0, 1]

private theorem H52Bl_sM_mul_self : ∀ b c : ZMod 2, H52Bl_sM b c * H52Bl_sM b c = 1 := by
  decide

private def H52Bl_sGL (b c : ZMod 2) : GL (Fin 3) (ZMod 2) :=
  ⟨H52Bl_sM b c, H52Bl_sM b c, H52Bl_sM_mul_self b c, H52Bl_sM_mul_self b c⟩

private theorem H52Bl_sGL_val (b c : ZMod 2) :
    ((H52Bl_sGL b c : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = H52Bl_sM b c :=
  rfl

private theorem H52Bl_sGL_inv (b c : ZMod 2) : (H52Bl_sGL b c)⁻¹ = H52Bl_sGL b c := by
  apply inv_eq_of_mul_eq_one_right
  apply Units.ext
  rw [Units.val_mul, Units.val_one]
  exact H52Bl_sM_mul_self b c

private theorem H52Bl_sGL_mem (b c : ZMod 2) : H52Bl_sGL b c ∈ Qlln line0 := by
  have hQ : ∀ b c : ZMod 2, Q1M (H52Bl_sM b c) := by decide
  exact (mem_Qlln_line0 _).2 (hQ b c)

private theorem H52Bl_sM_mulVec (b c : ZMod 2) (v : V3) :
    (H52Bl_sM b c).mulVec v = ![v 0 + b * v 2, v 1 + c * v 2, v 2] := by
  funext i
  fin_cases i <;> simp [H52Bl_sM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

private theorem H52Bl_Qlln_fix {g : GL (Fin 3) (ZMod 2)} (hg : g ∈ Qlln line0) (v : V3)
    (hv : v 2 = 0) : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v = v :=
  hg.1 v (mem_line0.2 hv)

private theorem H52Bl_Qlln_two {g : GL (Fin 3) (ZMod 2)} (hg : g ∈ Qlln line0) (v : V3) :
    ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v) 2 = v 2 := by
  have h := mem_line0.1 (hg.2 v)
  rw [Pi.sub_apply] at h
  exact sub_eq_zero.1 h

private theorem H52Bl_inv_Qlln {f : PermV}
    (hN : ∀ v w : V3, v 2 = 1 → w 2 = 1 → Multiplicative.toAdd f v = Multiplicative.toAdd f w)
    {g : GL (Fin 3) (ZMod 2)} (hg : g ∈ Qlln line0) (v : V3) :
    Multiplicative.toAdd f ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v) =
      Multiplicative.toAdd f v := by
  rcases H5_zmod2_cases (v 2) with hv | hv
  · rw [H52Bl_Qlln_fix hg v hv]
  · exact hN _ _ (by rw [H52Bl_Qlln_two hg v, hv]) hv

private def H52Bl_psi (β x y : ZMod 2) : PermV :=
  Multiplicative.ofAdd fun v => if v 2 = 1 then β else if v = ![1, 0, 0] then x
    else if v = ![0, 1, 0] then y else if v = ![1, 1, 0] then x + y else 0

private theorem H52Bl_psi_at (β x y : ZMod 2) (v : V3) :
    Multiplicative.toAdd (H52Bl_psi β x y) v = if v 2 = 1 then β else if v = ![1, 0, 0] then x
      else if v = ![0, 1, 0] then y else if v = ![1, 1, 0] then x + y else 0 :=
  rfl

private theorem H52Bl_psi_N (β x y : ZMod 2) (v : V3) (hv : v 2 = 1) :
    Multiplicative.toAdd (H52Bl_psi β x y) v = β := by
  rw [H52Bl_psi_at, if_pos hv]

private theorem H52Bl_psi_0 (β x y : ZMod 2) :
    Multiplicative.toAdd (H52Bl_psi β x y) 0 = 0 := by
  revert β x y
  decide

private theorem H52Bl_psi_eA (β x y : ZMod 2) :
    Multiplicative.toAdd (H52Bl_psi β x y) ![1, 0, 0] = x := by
  revert β x y
  decide

private theorem H52Bl_psi_eB (β x y : ZMod 2) :
    Multiplicative.toAdd (H52Bl_psi β x y) ![0, 1, 0] = y := by
  revert β x y
  decide

private theorem H52Bl_psi_eC (β x y : ZMod 2) :
    Multiplicative.toAdd (H52Bl_psi β x y) ![1, 1, 0] = x + y := by
  revert β x y
  decide

private theorem H52Bl_psi_z0 (β x y : ZMod 2) :
    Multiplicative.toAdd (H52Bl_psi β x y) ![0, 0, 1] = β :=
  H52Bl_psi_N β x y _ (by decide)

private theorem H52Bl_psi_const_of (β x y : ZMod 2) (v w : V3) (hv : v 2 = 1) (hw : w 2 = 1) :
    Multiplicative.toAdd (H52Bl_psi β x y) v = Multiplicative.toAdd (H52Bl_psi β x y) w :=
  (H52Bl_psi_N β x y v hv).trans (H52Bl_psi_N β x y w hw).symm

private theorem H52Bl_psi_mem_U (β x y : ZMod 2) : H52Bl_psi β x y ∈ Ucore := by
  rw [mem_Ucore']
  refine ⟨H52Bl_psi_0 β x y, ?_⟩
  rw [sum_V3]
  simp only [H52Bl_psi_at]
  revert β x y
  decide

private theorem H52Bl_psi_fix (β x y : ZMod 2) {g : GL (Fin 3) (ZMod 2)}
    (hg : g ∈ Qlln line0) : gl3Act g (H52Bl_psi β x y) = H52Bl_psi β x y := by
  apply Multiplicative.toAdd.injective
  funext v
  rw [gl3Act_toAdd]
  exact H52Bl_inv_Qlln (H52Bl_psi_const_of β x y) (Subgroup.inv_mem _ hg) v

private theorem H52Bl_psi_mem_K (β x y : ZMod 2) :
    H52Bl_psi β x y ∈ Ucore ⊓ fixV ((Qlln line0).map gl3Act) := by
  refine Subgroup.mem_inf.2 ⟨H52Bl_psi_mem_U β x y, mem_fixV.2 ?_⟩
  intro a ha
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 ha
  exact H52Bl_psi_fix β x y hg

private theorem H52Bl_K_const {f : PermV} (hf : f ∈ fixV ((Qlln line0).map gl3Act)) :
    ∀ v w : V3, v 2 = 1 → w 2 = 1 → Multiplicative.toAdd f v = Multiplicative.toAdd f w := by
  intro v w hv hw
  have hgv : (H52Bl_sGL (w 0 - v 0) (w 1 - v 1) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v =
      w := by
    rw [H52Bl_sGL_val, H52Bl_sM_mulVec, hv]
    funext i
    fin_cases i <;> simp [hw] <;> ring
  have hfg : gl3Act (H52Bl_sGL (w 0 - v 0) (w 1 - v 1)) f = f :=
    (mem_fixV.1 hf) _ (Subgroup.mem_map_of_mem gl3Act (H52Bl_sGL_mem _ _))
  exact (fix_const f _ hfg v).trans (by rw [hgv])

private theorem H52Bl_char2_aux : ∀ a b c z : ZMod 2, 0 + a + b + c + z + z + z + z = 0 →
    c = a + b := by
  decide

private theorem H52Bl_char2_par : ∀ y0 y1 y2 y3 : ZMod 2, y0 + y1 + y2 + y3 = 0 →
    y0 = y1 + y2 + y3 := by
  decide

private theorem H52Bl_add_self : ∀ x : ZMod 2, x + x = 0 := by
  decide

private theorem H52Bl_neg_self : ∀ x : ZMod 2, -x = x := by
  decide

private theorem H52Bl_V3_cover : ∀ v : V3, v 2 = 1 ∨ v = 0 ∨ v = ![1, 0, 0] ∨
    v = ![0, 1, 0] ∨ v = ![1, 1, 0] := by
  decide

private theorem H52Bl_V3_coverN : ∀ v : V3, v 2 = 0 ∨ v = ![0, 0, 1] ∨ v = ![1, 0, 1] ∨
    v = ![0, 1, 1] ∨ v = ![1, 1, 1] := by
  decide

private theorem H52Bl_notN : ∀ v : V3, v 2 = 0 → v ≠ ![0, 0, 1] ∧ v ≠ ![1, 0, 1] ∧
    v ≠ ![0, 1, 1] ∧ v ≠ ![1, 1, 1] := by
  decide

private theorem H52Bl_K_eq_psi {f : PermV} (hfU : f ∈ Ucore)
    (hf : f ∈ fixV ((Qlln line0).map gl3Act)) :
    f = H52Bl_psi (Multiplicative.toAdd f ![0, 0, 1]) (Multiplicative.toAdd f ![1, 0, 0])
      (Multiplicative.toAdd f ![0, 1, 0]) := by
  have hc := H52Bl_K_const hf
  obtain ⟨h0, hsum⟩ := mem_Ucore'.1 hfU
  have hC : Multiplicative.toAdd f ![1, 1, 0] =
      Multiplicative.toAdd f ![1, 0, 0] + Multiplicative.toAdd f ![0, 1, 0] := by
    have k1 : Multiplicative.toAdd f ![1, 0, 1] = Multiplicative.toAdd f ![0, 0, 1] :=
      hc _ _ (by decide) (by decide)
    have k2 : Multiplicative.toAdd f ![0, 1, 1] = Multiplicative.toAdd f ![0, 0, 1] :=
      hc _ _ (by decide) (by decide)
    have k3 : Multiplicative.toAdd f ![1, 1, 1] = Multiplicative.toAdd f ![0, 0, 1] :=
      hc _ _ (by decide) (by decide)
    have h0' : Multiplicative.toAdd f ![0, 0, 0] = 0 := by
      have e : (![0, 0, 0] : V3) = 0 := by decide
      rw [e]
      exact h0
    simp only [sum_V3, h0', k1, k2, k3] at hsum
    exact H52Bl_char2_aux _ _ _ _ hsum
  apply Multiplicative.toAdd.injective
  funext v
  rcases H52Bl_V3_cover v with hv | rfl | rfl | rfl | rfl
  · rw [H52Bl_psi_N _ _ _ v hv]
    exact hc v _ hv (by decide)
  · rw [H52Bl_psi_0]
    exact h0
  · rw [H52Bl_psi_eA]
  · rw [H52Bl_psi_eB]
  · rw [H52Bl_psi_eC]
    exact hC

private theorem H52Bl_psi_inj : Function.Injective
    (fun p : ZMod 2 × ZMod 2 × ZMod 2 => H52Bl_psi p.1 p.2.1 p.2.2) := by
  rintro ⟨β, x, y⟩ ⟨β', x', y'⟩ h
  have h1 := congrArg (fun F : PermV => Multiplicative.toAdd F ![0, 0, 1]) h
  have h2 := congrArg (fun F : PermV => Multiplicative.toAdd F ![1, 0, 0]) h
  have h3 := congrArg (fun F : PermV => Multiplicative.toAdd F ![0, 1, 0]) h
  simp only [H52Bl_psi_z0, H52Bl_psi_eA, H52Bl_psi_eB] at h1 h2 h3
  subst h1 h2 h3
  rfl

private theorem H52Bl_card_triple : Nat.card (ZMod 2 × ZMod 2 × ZMod 2) = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide

private theorem H52Bl_ln_K : Nat.card ↥(Ucore ⊓ fixV ((Qlln line0).map gl3Act)) = 8 := by
  have hset : ((Ucore ⊓ fixV ((Qlln line0).map gl3Act) : Subgroup PermV) : Set PermV) =
      Set.range (fun p : ZMod 2 × ZMod 2 × ZMod 2 => H52Bl_psi p.1 p.2.1 p.2.2) := by
    ext f
    rw [SetLike.mem_coe]
    constructor
    · intro hf
      obtain ⟨hfU, hfix⟩ := Subgroup.mem_inf.1 hf
      exact ⟨(Multiplicative.toAdd f ![0, 0, 1], Multiplicative.toAdd f ![1, 0, 0],
        Multiplicative.toAdd f ![0, 1, 0]), (H52Bl_K_eq_psi hfU hfix).symm⟩
    · rintro ⟨⟨β, x, y⟩, rfl⟩
      exact H52Bl_psi_mem_K β x y
  have e : Nat.card ((Ucore ⊓ fixV ((Qlln line0).map gl3Act) : Subgroup PermV) : Set PermV) =
      Nat.card (Set.range (fun p : ZMod 2 × ZMod 2 × ZMod 2 => H52Bl_psi p.1 p.2.1 p.2.2)) := by
    rw [hset]
  rw [Nat.card_range_of_injective H52Bl_psi_inj, H52Bl_card_triple] at e
  exact e

private def H52Bl_R1 : Subgroup PermV where
  carrier := {h | (∀ v : V3, v 2 = 0 → Multiplicative.toAdd h v = 0) ∧
    ∑ v : V3, Multiplicative.toAdd h v = 0}
  one_mem' := ⟨fun v _ => by simp, by simp⟩
  mul_mem' := fun {h h'} hh hh' => ⟨fun v hv => by
      simp [toAdd_mul, hh.1 v hv, hh'.1 v hv],
    by simp [toAdd_mul, Finset.sum_add_distrib, hh.2, hh'.2]⟩
  inv_mem' := fun {h} hh => ⟨fun v hv => by simp [toAdd_inv, hh.1 v hv],
    by simp [toAdd_inv, hh.2]⟩

private theorem H52Bl_mem_R1 (h : PermV) : h ∈ H52Bl_R1 ↔
    (∀ v : V3, v 2 = 0 → Multiplicative.toAdd h v = 0) ∧
      ∑ v : V3, Multiplicative.toAdd h v = 0 :=
  Iff.rfl

private theorem H52Bl_pairV_mul_self (F : PermV) : F * F = 1 := by
  apply Multiplicative.toAdd.injective
  funext v
  rw [toAdd_mul, toAdd_one, Pi.add_apply, Pi.zero_apply]
  exact CharTwo.add_self_eq_zero _

private theorem H52Bl_aux_pair : ∀ b c : ZMod 2, (b = 1 ∨ c = 1) → ∀ x : V3,
    (if (H52Bl_sM b c).mulVec x = ![0, 0, 1] ∨ (H52Bl_sM b c).mulVec x = ![1, 0, 0] then
        (1 : ZMod 2) else 0) +
      (if x = ![0, 0, 1] ∨ x = ![1, 0, 0] then (1 : ZMod 2) else 0) =
    (if x = ![0, 0, 1] ∨ x = ![b, c, 1] then (1 : ZMod 2) else 0) := by
  decide

private theorem H52Bl_pair_mem (b c : ZMod 2) (hbc : b = 1 ∨ c = 1) :
    pairV ![0, 0, 1] ![b, c, 1] ∈ commOn Ucore ((Qlln line0).map gl3Act) := by
  have hF : pairV ![0, 0, 1] ![1, 0, 0] ∈ Ucore := by
    refine (O3_ucore _ ?_).1
    rw [O3set_eq]
    exact ⟨![0, 0, 1], ![1, 0, 0], by decide, by decide, by decide, rfl⟩
  have key : gl3Act (H52Bl_sGL b c) (pairV ![0, 0, 1] ![1, 0, 0]) *
      pairV ![0, 0, 1] ![1, 0, 0] = pairV ![0, 0, 1] ![b, c, 1] := by
    apply Multiplicative.toAdd.injective
    funext x
    rw [toAdd_mul, Pi.add_apply, gl3Act_toAdd, H52Bl_sGL_inv]
    simp only [toAdd_pairV, H52Bl_sGL_val]
    exact H52Bl_aux_pair b c hbc x
  have hmem : gl3Act (H52Bl_sGL b c) (pairV ![0, 0, 1] ![1, 0, 0]) *
      (pairV ![0, 0, 1] ![1, 0, 0])⁻¹ = pairV ![0, 0, 1] ![b, c, 1] := by
    rw [inv_eq_of_mul_eq_one_right (H52Bl_pairV_mul_self (pairV ![0, 0, 1] ![1, 0, 0]))]
    exact key
  unfold commOn
  apply Subgroup.subset_closure
  exact ⟨gl3Act (H52Bl_sGL b c), Subgroup.mem_map_of_mem gl3Act (H52Bl_sGL_mem b c),
    pairV ![0, 0, 1] ![1, 0, 0], hF, hmem.symm⟩

private theorem H52Bl_comm_le_R1 : commOn Ucore ((Qlln line0).map gl3Act) ≤ H52Bl_R1 := by
  unfold commOn
  refine (Subgroup.closure_le _).2 ?_
  rintro u ⟨a, ha, w, hw, rfl⟩
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 ha
  obtain ⟨-, hwsum⟩ := mem_Ucore'.1 hw
  have hterm : ∀ v : V3, Multiplicative.toAdd (gl3Act g w * w⁻¹) v =
      Multiplicative.toAdd w
        (((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v) +
        Multiplicative.toAdd w v := by
    intro v
    rw [toAdd_mul, Pi.add_apply, gl3Act_toAdd, toAdd_inv, Pi.neg_apply]
    congr 1
    exact H52Bl_neg_self _
  have hs : ∑ v : V3, Multiplicative.toAdd w
      (((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v) =
      ∑ v : V3, Multiplicative.toAdd w v :=
    sum_mulVec_eq (g⁻¹) (fun x => Multiplicative.toAdd w x)
  refine (H52Bl_mem_R1 _).2 ⟨fun v hv => ?_, ?_⟩
  · show Multiplicative.toAdd (gl3Act g w * w⁻¹) v = 0
    rw [hterm v, H52Bl_Qlln_fix (Subgroup.inv_mem _ hg) v hv]
    exact H52Bl_add_self _
  · show ∑ v : V3, Multiplicative.toAdd (gl3Act g w * w⁻¹) v = 0
    rw [Finset.sum_congr rfl (fun v _ => hterm v), Finset.sum_add_distrib, hs, hwsum] <;>
      exact H52Bl_add_self 0

private def H52Bl_Phi (a b c : ZMod 2) : PermV :=
  Multiplicative.ofAdd fun v => a * (if v = ![0, 0, 1] ∨ v = ![1, 0, 1] then 1 else 0) +
    b * (if v = ![0, 0, 1] ∨ v = ![0, 1, 1] then 1 else 0) +
    c * (if v = ![0, 0, 1] ∨ v = ![1, 1, 1] then 1 else 0)

private theorem H52Bl_Phi_z0 (a b c : ZMod 2) :
    Multiplicative.toAdd (H52Bl_Phi a b c) ![0, 0, 1] = a + b + c := by
  revert a b c
  decide

private theorem H52Bl_Phi_z1 (a b c : ZMod 2) :
    Multiplicative.toAdd (H52Bl_Phi a b c) ![1, 0, 1] = a := by
  revert a b c
  decide

private theorem H52Bl_Phi_z2 (a b c : ZMod 2) :
    Multiplicative.toAdd (H52Bl_Phi a b c) ![0, 1, 1] = b := by
  revert a b c
  decide

private theorem H52Bl_Phi_z3 (a b c : ZMod 2) :
    Multiplicative.toAdd (H52Bl_Phi a b c) ![1, 1, 1] = c := by
  revert a b c
  decide

private theorem H52Bl_Phi_of_zero (a b c : ZMod 2) (v : V3) (hv : v 2 = 0) :
    Multiplicative.toAdd (H52Bl_Phi a b c) v = 0 := by
  obtain ⟨n0, n1, n2, n3⟩ := H52Bl_notN v hv
  simp [H52Bl_Phi, n0, n1, n2, n3]

private def H52Bl_pw (P : PermV) (a : ZMod 2) : PermV := if a = 0 then 1 else P

private theorem H52Bl_toAdd_pw (P : PermV) (a : ZMod 2) (v : V3) :
    Multiplicative.toAdd (H52Bl_pw P a) v = a * Multiplicative.toAdd P v := by
  rcases H5_zmod2_cases a with rfl | rfl <;> simp [H52Bl_pw]

private theorem H52Bl_pw_mem {M : Subgroup PermV} {P : PermV} (hP : P ∈ M) (a : ZMod 2) :
    H52Bl_pw P a ∈ M := by
  unfold H52Bl_pw
  split_ifs
  · exact one_mem _
  · exact hP

private theorem H52Bl_Phi_eq (a b c : ZMod 2) :
    H52Bl_Phi a b c = H52Bl_pw (pairV ![0, 0, 1] ![1, 0, 1]) a *
      H52Bl_pw (pairV ![0, 0, 1] ![0, 1, 1]) b * H52Bl_pw (pairV ![0, 0, 1] ![1, 1, 1]) c := by
  apply Multiplicative.toAdd.injective
  funext v
  simp only [toAdd_mul, Pi.add_apply, H52Bl_toAdd_pw, H52Bl_Phi, toAdd_ofAdd, toAdd_pairV]

private theorem H52Bl_Phi_mem (a b c : ZMod 2) :
    H52Bl_Phi a b c ∈ commOn Ucore ((Qlln line0).map gl3Act) := by
  rw [H52Bl_Phi_eq]
  exact mul_mem (mul_mem (H52Bl_pw_mem (H52Bl_pair_mem 1 0 (Or.inl rfl)) a)
    (H52Bl_pw_mem (H52Bl_pair_mem 0 1 (Or.inr rfl)) b))
    (H52Bl_pw_mem (H52Bl_pair_mem 1 1 (Or.inl rfl)) c)

private theorem H52Bl_Phi_inj : Function.Injective
    (fun p : ZMod 2 × ZMod 2 × ZMod 2 => H52Bl_Phi p.1 p.2.1 p.2.2) := by
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
  have h1 := congrArg (fun F : PermV => Multiplicative.toAdd F ![1, 0, 1]) h
  have h2 := congrArg (fun F : PermV => Multiplicative.toAdd F ![0, 1, 1]) h
  have h3 := congrArg (fun F : PermV => Multiplicative.toAdd F ![1, 1, 1]) h
  simp only [H52Bl_Phi_z1, H52Bl_Phi_z2, H52Bl_Phi_z3] at h1 h2 h3
  subst h1 h2 h3
  rfl

private theorem H52Bl_R1_eq_Phi {h : PermV} (hh : h ∈ H52Bl_R1) :
    h = H52Bl_Phi (Multiplicative.toAdd h ![1, 0, 1]) (Multiplicative.toAdd h ![0, 1, 1])
      (Multiplicative.toAdd h ![1, 1, 1]) := by
  obtain ⟨hvan, hsum⟩ := (H52Bl_mem_R1 h).1 hh
  have hpar : Multiplicative.toAdd h ![0, 0, 1] = Multiplicative.toAdd h ![1, 0, 1] +
      Multiplicative.toAdd h ![0, 1, 1] + Multiplicative.toAdd h ![1, 1, 1] := by
    have q0 := hvan ![0, 0, 0] (by decide)
    have q1 := hvan ![1, 0, 0] (by decide)
    have q2 := hvan ![0, 1, 0] (by decide)
    have q3 := hvan ![1, 1, 0] (by decide)
    simp only [sum_V3, q0, q1, q2, q3, zero_add] at hsum
    exact H52Bl_char2_par _ _ _ _ hsum
  apply Multiplicative.toAdd.injective
  funext v
  rcases H52Bl_V3_coverN v with hv | rfl | rfl | rfl | rfl
  · rw [hvan v hv, H52Bl_Phi_of_zero _ _ _ v hv]
  · rw [H52Bl_Phi_z0]
    exact hpar
  · rw [H52Bl_Phi_z1]
  · rw [H52Bl_Phi_z2]
  · rw [H52Bl_Phi_z3]

private theorem H52Bl_ln_M : Nat.card ↥(commOn Ucore ((Qlln line0).map gl3Act)) = 8 := by
  have hset : ((commOn Ucore ((Qlln line0).map gl3Act) : Subgroup PermV) : Set PermV) =
      Set.range (fun p : ZMod 2 × ZMod 2 × ZMod 2 => H52Bl_Phi p.1 p.2.1 p.2.2) := by
    ext h
    rw [SetLike.mem_coe]
    constructor
    · intro hm
      exact ⟨(Multiplicative.toAdd h ![1, 0, 1], Multiplicative.toAdd h ![0, 1, 1],
        Multiplicative.toAdd h ![1, 1, 1]), (H52Bl_R1_eq_Phi (H52Bl_comm_le_R1 hm)).symm⟩
    · rintro ⟨⟨a, b, c⟩, rfl⟩
      exact H52Bl_Phi_mem a b c
  have e : Nat.card ((commOn Ucore ((Qlln line0).map gl3Act) : Subgroup PermV) : Set PermV) =
      Nat.card (Set.range (fun p : ZMod 2 × ZMod 2 × ZMod 2 => H52Bl_Phi p.1 p.2.1 p.2.2)) := by
    rw [hset]
  rw [Nat.card_range_of_injective H52Bl_Phi_inj, H52Bl_card_triple] at e
  exact e

private theorem H52tr_M (c : GL (Fin 3) (ZMod 2)) (X : Subgroup (GL (Fin 3) (ZMod 2))) :
    commOn Ucore ((conjSub c X).map gl3Act) =
      (commOn Ucore (X.map gl3Act)).map (gl3Act c).toMonoidHom := by
  apply le_antisymm
  · unfold commOn
    refine (Subgroup.closure_le _).2 fun u hu => ?_
    obtain ⟨a, ha, w, hw, rfl⟩ := hu
    obtain ⟨x0, hx0, rfl⟩ := mem_conjSub_map.1 ha
    refine Subgroup.mem_map.2 ⟨gl3Act x0 (gl3Act c⁻¹ w) * (gl3Act c⁻¹ w)⁻¹, ?_, ?_⟩
    · apply Subgroup.subset_closure
      exact ⟨gl3Act x0, Subgroup.mem_map_of_mem _ hx0, gl3Act c⁻¹ w, Ucore_inv _ _ hw, rfl⟩
    · show gl3Act c (gl3Act x0 (gl3Act c⁻¹ w) * (gl3Act c⁻¹ w)⁻¹) =
        gl3Act (c * x0 * c⁻¹) w * w⁻¹
      rw [map_mul (gl3Act c)]
      erw [map_inv (gl3Act c)]
      rw [gl3Act_conj_apply, gl3Act_cancel']
  · refine Subgroup.map_le_iff_le_comap.2 ((Subgroup.closure_le _).2 fun v hv => ?_)
    unfold commOn at hv ⊢
    obtain ⟨a, ha, w, hw, rfl⟩ := hv
    obtain ⟨x0, hx0, rfl⟩ := Subgroup.mem_map.1 ha
    refine Subgroup.mem_comap.2 (Subgroup.subset_closure ?_)
    refine ⟨gl3Act (c * x0 * c⁻¹), mem_conjSub_map.2 ⟨x0, hx0, rfl⟩, gl3Act c w,
      Ucore_inv _ _ hw, ?_⟩
    show gl3Act c (gl3Act x0 w * w⁻¹) = gl3Act (c * x0 * c⁻¹) (gl3Act c w) * (gl3Act c w)⁻¹
    rw [map_mul (gl3Act c)]
    erw [map_inv (gl3Act c)]
    rw [gl3Act_conj_apply, gl3Act_cancel]

private theorem rk_eq_three_of_card {G : Type*} [Group G] {H : Subgroup G}
    (h : Nat.card H = 8) : CFSG.Quasithin.rk ↥H = 3 := by
  unfold CFSG.Quasithin.rk
  rw [h, show (8 : ℕ) = 2 ^ 3 from rfl, padicValNat.prime_pow]

private theorem hgl3c_inj (c : GL (Fin 3) (ZMod 2)) :
    Function.Injective (gl3Act c).toMonoidHom := fun x y h => (gl3Act c).injective h

private theorem rk_eq_three_of_card_aux {K : Type*} [Group K] {f : PermV →* K}
    {L : Subgroup PermV} (hf : Function.Injective f) (h : Nat.card ↥L = 8) :
    Nat.card ↥(L.map f) = 8 :=
  (Subgroup.card_map_of_injective hf).trans h

private theorem H52_rank_pt (c : GL (Fin 3) (ZMod 2)) (p : V3)
    (hc : (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec e1 = p) :
    CFSG.Quasithin.rk ↥(Ucore ⊓ fixV ((CFSG.Open.pCoreOf 2 (Lpt p)).map gl3Act)) = 3 ∧
      CFSG.Quasithin.rk ↥(commOn Ucore ((CFSG.Open.pCoreOf 2 (Lpt p)).map gl3Act)) = 3 := by
  rw [pCoreOf_Lpt hc, Qpt_eq_conj hc]
  refine ⟨rk_eq_three_of_card ?_, rk_eq_three_of_card ?_⟩
  · rw [H52tr_K]
    exact rk_eq_three_of_card_aux (hgl3c_inj c) H52B_pt_K
  · rw [H52tr_M]
    exact rk_eq_three_of_card_aux (hgl3c_inj c) H52B_pt_M

private theorem H52_rank_ln (c : GL (Fin 3) (ZMod 2)) (l : Submodule (ZMod 2) V3)
    (hc : ∀ v : V3, (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ l ↔ v 2 = 0) :
    CFSG.Quasithin.rk ↥(Ucore ⊓ fixV ((CFSG.Open.pCoreOf 2 (Lln l)).map gl3Act)) = 3 ∧
      CFSG.Quasithin.rk ↥(commOn Ucore ((CFSG.Open.pCoreOf 2 (Lln l)).map gl3Act)) = 3 := by
  rw [pCoreOf_Lln hc, Qlln_eq_conj hc]
  refine ⟨rk_eq_three_of_card ?_, rk_eq_three_of_card ?_⟩
  · rw [H52tr_K]
    exact rk_eq_three_of_card_aux (hgl3c_inj c) H52Bl_ln_K
  · rw [H52tr_M]
    exact rk_eq_three_of_card_aux (hgl3c_inj c) H52Bl_ln_M

end H52asm

theorem as_H_5_2 : H_5_2 := by
  refine ⟨H52_part1, fun T p l hyp => ?_⟩
  obtain ⟨c, hconjT, hpc, hline⟩ := conj_data54 T p l hyp
  obtain ⟨hp3, hpm⟩ := H52_rank_pt c p hpc
  obtain ⟨hl3, hlm⟩ := H52_rank_ln c l hline
  refine ⟨H52_part2 T p l hyp, ⟨hp3, hl3⟩, ⟨hpm, hlm⟩,
    ⟨H52_Lpt_fix p hyp.p_ne, H52_Lln_fix c l hyp.l_line hline⟩,
    ⟨H52beta, fun u _ u' _ w _ => H52beta_mul_left u u' w,
      fun u _ w _ w' _ => H52beta_mul_right u w w',
      fun g u _ w _ => H52beta_gl g u w,
      fun u hu hu1 => H52beta_nondeg u hu hu1⟩, ?_⟩
  intro Y q hY hq hfix hC
  exact H52_seven l hyp.l_line Y q hY hq hfix hC

theorem as_H_5_3 : H_5_3 := by
  refine ⟨H5W, H5W_coe, ⟨H5W_le_Ucore, fun g w hw => H5W_inv g w hw, H5W_iso⟩, H5U_iso,
    ⟨fun i x hx g => Oset_inv i x hx g, fun i x hx y hy => Oset_trans i x y hx hy,
      fun i x hx => Oset_ucore i x hx, ?_, fun i j hij => Oset_disjoint i j hij⟩,
    H5_counts, fun A B hA hB hAi hBi _ hinf => H5_indecomposable A B hA hB hAi hBi hinf,
    H5W_socle⟩
  · intro x hx hx1
    rcases cover_Ucore x hx hx1 with h | h | h | h
    exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩, ⟨3, h⟩]

end CFSG.ASVolI
