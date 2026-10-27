module

public import CFSG.Quasithin.Background.P4InspOrthA8
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.EmptyFaithful.Vocabulary

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Quasithin.G11 CFSG.Quasithin.G11.P4InspOrth

namespace LRed4


@[expose] def val8 (m : ↥(FFModel.symDn 8).sec) : Fin 8 → ZMod 2 := Multiplicative.toAdd (m.1 : G6.PermMod 8)

theorem val8_mem (m : ↥(FFModel.symDn 8).sec) : val8 m ∈ permCore 8 := m.2

@[expose] noncomputable def coreToV8 : ↥(FFModel.symDn 8).sec →* Multiplicative p4insporth_V8 where
  toFun m := Multiplicative.ofAdd (Submodule.Quotient.mk (⟨val8 m, val8_mem m⟩ : ↥(permCore 8)))
  map_one' := by
    show Multiplicative.ofAdd (Submodule.Quotient.mk _) = 1
    apply Multiplicative.toAdd.injective
    show Submodule.Quotient.mk _ = (0 : p4insporth_V8)
    rw [← Submodule.Quotient.mk_zero]
    congr 1
  map_mul' a b := by
    show Multiplicative.ofAdd (Submodule.Quotient.mk _) =
      Multiplicative.ofAdd (Submodule.Quotient.mk _) * Multiplicative.ofAdd (Submodule.Quotient.mk _)
    rw [← ofAdd_add, ← Submodule.Quotient.mk_add]
    rfl

theorem coreToV8_surjective : Function.Surjective coreToV8 := by
  intro y
  obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (Multiplicative.toAdd y)
  refine ⟨⟨Multiplicative.ofAdd (x : Fin 8 → ZMod 2), x.2⟩, ?_⟩
  apply Multiplicative.toAdd.injective
  exact hx

theorem coreToV8_eq_one_iff (m : ↥(FFModel.symDn 8).sec) :
    coreToV8 m = 1 ↔ (val8 m = 0 ∨ ∀ i, val8 m i = 1) := by
  have h := p4insporth_ker8 (⟨val8 m, val8_mem m⟩ : ↥(permCore 8))
  have e : coreToV8 m = 1 ↔ p4insporth_L8.mkQ (⟨val8 m, val8_mem m⟩ : ↥(permCore 8)) = 0 := by
    rw [← Multiplicative.toAdd.injective.eq_iff]
    rfl
  rw [e, h]
  constructor
  · rintro (h0 | ⟨-, h1⟩)
    · left
      exact congrArg Subtype.val h0
    · right
      exact h1
  · rintro (h0 | h1)
    · left
      exact Subtype.ext h0
    · right
      exact ⟨by decide, h1⟩

theorem mem_zpowers_allOnes_iff (x : G6.PermMod 8) :
    x ∈ Subgroup.zpowers (G6.allOnes 8) ↔
      (Multiplicative.toAdd x = 0 ∨ ∀ i, Multiplicative.toAdd x i = 1) := by
  constructor
  · rintro ⟨k, rfl⟩
    rcases Int.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
    · left
      funext i
      subst hj
      simp [G6.allOnes, toAdd_zpow, ← two_mul, mul_comm]
      exact Or.inr (by decide)
    · right
      intro i
      subst hj
      simp [G6.allOnes, toAdd_zpow]
      exact Or.inl (by decide)
  · rintro (h0 | h1)
    · refine ⟨0, ?_⟩
      apply Multiplicative.toAdd.injective
      simpa using h0.symm
    · refine ⟨1, ?_⟩
      apply Multiplicative.toAdd.injective
      funext i
      simp [G6.allOnes, h1 i]

@[expose] noncomputable def thetaV8 : (FFModel.symDn 8).Mod →* Multiplicative p4insporth_V8 :=
  QuotientGroup.lift _ coreToV8 (by
    intro m hm
    rw [MonoidHom.mem_ker, coreToV8_eq_one_iff]
    have hm' : m.1 ∈ Subgroup.zpowers (G6.allOnes 8) ⊓ G6.coreMod 8 := hm
    exact (mem_zpowers_allOnes_iff _).1 hm'.1)

theorem thetaV8_mk (m : ↥(FFModel.symDn 8).sec) :
    thetaV8 (QuotientGroup.mk m) = coreToV8 m := rfl

theorem thetaV8_injective : Function.Injective thetaV8 := by
  rw [injective_iff_map_eq_one]
  intro d hd
  induction d using QuotientGroup.induction_on with
  | H m =>
    rw [thetaV8_mk, coreToV8_eq_one_iff] at hd
    rw [QuotientGroup.eq_one_iff]
    have h1 : m.1 ∈ Subgroup.zpowers (G6.allOnes 8) := (mem_zpowers_allOnes_iff _).2 hd
    exact ⟨h1, m.2⟩

theorem thetaV8_surjective : Function.Surjective thetaV8 := by
  intro y
  obtain ⟨m, hm⟩ := coreToV8_surjective y
  exact ⟨QuotientGroup.mk m, hm⟩

@[expose] noncomputable def thetaEquiv : (FFModel.symDn 8).Mod ≃* Multiplicative p4insporth_V8 :=
  MulEquiv.ofBijective thetaV8 ⟨thetaV8_injective, thetaV8_surjective⟩

theorem thetaEquiv_mk (m : ↥(FFModel.symDn 8).sec) :
    thetaEquiv (QuotientGroup.mk m) = coreToV8 m := rfl

theorem thetaEquiv_modAct (σ : Equiv.Perm (Fin 8)) (d : (FFModel.symDn 8).Mod) :
    thetaEquiv ((FFModel.symDn_isActionModel 8).modAct σ d) =
      Multiplicative.ofAdd (p4insporth_perm8Hom σ (Multiplicative.toAdd (thetaEquiv d))) := by
  induction d using QuotientGroup.induction_on with
  | H m =>
    show thetaEquiv (QuotientGroup.mk ((FFModel.symDn_isActionModel 8).actSec σ m)) = _
    rw [thetaEquiv_mk, thetaEquiv_mk]
    show Multiplicative.ofAdd (Submodule.Quotient.mk _) =
      Multiplicative.ofAdd (p4insporth_perm8Hom σ (Submodule.Quotient.mk _))
    rw [p4insporth_perm8Hom_mk]
    rfl


section Psi

variable {V : Type} [CommGroup V]

theorem exists_psi {X : Subgroup (MulAut V)} (h : SymmetricNatural X ⊤ ⊥ 8) :
    ∃ (π : Equiv.Perm (Fin 8) →* ↥X) (Ψ : V ≃* Multiplicative p4insporth_V8),
      Function.Surjective π ∧ ∀ (σ : Equiv.Perm (Fin 8)) (u : V),
        Ψ (((π σ : ↥X) : MulAut V) u) =
          Multiplicative.ofAdd (p4insporth_perm8Hom σ (Multiplicative.toAdd (Ψ u))) := by
  obtain ⟨π, hπs, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := h
  have hinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have h1 := (hβk u).1 hu
    exact Subtype.ext (Subgroup.mem_bot.1 h1)
  let e₀ : ↥(⊤ : Subgroup V) ≃* (FFModel.symDn 8).Mod := MulEquiv.ofBijective β ⟨hinj, hβs⟩
  let Ψ : V ≃* Multiplicative p4insporth_V8 :=
    Subgroup.topEquiv.symm.trans (e₀.trans thetaEquiv)
  refine ⟨π, Ψ, hπs, fun σ u => ?_⟩
  have hΨ : ∀ w : V, Ψ w = thetaEquiv (β ⟨w, trivial⟩) := fun w => rfl
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨u, trivial⟩)
  have hb : β ⟨((π σ : ↥X) : MulAut V) u, trivial⟩ =
      (FFModel.symDn_isActionModel 8).modAct σ (β ⟨u, trivial⟩) := by
    have := hβe σ ⟨u, trivial⟩ m trivial (by
      exact (FFModel.symDn_isActionModel 8).sec_inv σ m m.2) hm.symm
    rw [this, ← hm]
    rfl
  rw [hΨ, hΨ]
  exact (congrArg thetaEquiv hb).trans (thetaEquiv_modAct σ _)

end Psi

section Orth

variable {V : Type} [CommGroup V]

private theorem zmod_key1 : ∀ A B F : ZMod 2, A + B + F + A + B = F := by decide

private theorem zmod_key2 : ∀ A F : ZMod 2, A = A + A + F → F = 0 → A = 0 := by decide

theorem q8_zero : p4insporth_q8 0 = 0 := by
  have h := p4insporth_q8_add 0 0
  have h2 : p4insporth_f8 (0 : p4insporth_V8) 0 = 0 := by simp
  rw [add_zero, h2] at h
  exact zmod_key2 _ _ h rfl

@[expose] noncomputable def qOfPsi (Ψ : V ≃* Multiplicative p4insporth_V8) : V → ZMod 2 :=
  fun u => p4insporth_q8 (Multiplicative.toAdd (Ψ u))

theorem quadPolar_qOfPsi (Ψ : V ≃* Multiplicative p4insporth_V8) (x y : V) :
    quadPolar (qOfPsi Ψ) x y =
      p4insporth_f8 (Multiplicative.toAdd (Ψ x)) (Multiplicative.toAdd (Ψ y)) := by
  unfold quadPolar qOfPsi
  rw [map_mul, toAdd_mul, p4insporth_q8_add]
  exact zmod_key1 _ _ _

theorem isQuadraticFormOn_qOfPsi (Ψ : V ≃* Multiplicative p4insporth_V8) :
    IsQuadraticFormOn (qOfPsi Ψ) := by
  refine ⟨?_, ?_, ?_⟩
  · show p4insporth_q8 (Multiplicative.toAdd (Ψ 1)) = 0
    rw [map_one]
    exact q8_zero
  · intro x y z
    rw [quadPolar_qOfPsi, quadPolar_qOfPsi, quadPolar_qOfPsi, map_mul, toAdd_mul, map_add,
      LinearMap.add_apply]
  · intro x y z
    rw [quadPolar_qOfPsi, quadPolar_qOfPsi, quadPolar_qOfPsi, map_mul, toAdd_mul, map_add]

theorem isNondegQuadratic_qOfPsi (Ψ : V ≃* Multiplicative p4insporth_V8) :
    IsNondegQuadratic (qOfPsi Ψ) := by
  intro x hx
  have h : ∀ z : p4insporth_V8, p4insporth_f8 (Multiplicative.toAdd (Ψ x)) z = 0 := by
    intro z
    have := hx (Ψ.symm (Multiplicative.ofAdd z))
    rw [quadPolar_qOfPsi, MulEquiv.apply_symm_apply] at this
    simpa using this
  have h0 := p4insporth_symplectic8.2 _ h
  apply Ψ.injective
  rw [map_one]
  exact Multiplicative.toAdd.injective h0


theorem card_V8 : Nat.card p4insporth_V8 = 2 ^ 6 := by
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := p4insporth_V8)
  rw [p4insporth_finrank8, Nat.card_zmod] at h
  exact h

@[expose] noncomputable def singSub (Ψ : V ≃* Multiplicative p4insporth_V8) : Subgroup V :=
  (AddSubgroup.toSubgroup p4insporth_D8.sing3.toAddSubgroup).comap Ψ.toMonoidHom

theorem card_singSub (Ψ : V ≃* Multiplicative p4insporth_V8) :
    Nat.card (singSub Ψ) = 2 ^ 3 := by
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥p4insporth_D8.sing3)
  rw [p4insporth_D8.finrank_sing3, Nat.card_zmod] at h
  rw [← h]
  exact Nat.card_congr (Equiv.subtypeEquiv (Ψ.toEquiv.trans Multiplicative.toAdd) fun u => Iff.rfl)

theorem singSub_q (Ψ : V ≃* Multiplicative p4insporth_V8) : ∀ e ∈ singSub Ψ, qOfPsi Ψ e = 0 := by
  intro e he
  exact p4insporth_D8.sing3_q _ he

theorem card_of_psi (Ψ : V ≃* Multiplicative p4insporth_V8) : Nat.card V = 2 ^ 6 := by
  rw [Nat.card_congr (Ψ.toEquiv.trans Multiplicative.toAdd)]
  exact card_V8


@[expose] noncomputable def toAddHom (Ψ : V ≃* Multiplicative p4insporth_V8) (g : MulAut V) :
    p4insporth_V8 →+ p4insporth_V8 where
  toFun x := Multiplicative.toAdd (Ψ (g (Ψ.symm (Multiplicative.ofAdd x))))
  map_zero' := by simp
  map_add' x y := by simp only [ofAdd_add, map_mul, toAdd_mul]

@[expose] noncomputable def toGL (Ψ : V ≃* Multiplicative p4insporth_V8) (g : MulAut V) :
    GLV p4insporth_V8 :=
  { (toAddHom Ψ g).toZModLinearMap 2 with
    invFun := fun x => Multiplicative.toAdd (Ψ (g.symm (Ψ.symm (Multiplicative.ofAdd x))))
    left_inv := fun x => by simp [toAddHom]
    right_inv := fun x => by simp [toAddHom] }

theorem toGL_apply (Ψ : V ≃* Multiplicative p4insporth_V8) (g : MulAut V) (u : V) :
    toGL Ψ g (Multiplicative.toAdd (Ψ u)) = Multiplicative.toAdd (Ψ (g u)) := by
  show Multiplicative.toAdd (Ψ (g (Ψ.symm (Multiplicative.ofAdd (Multiplicative.toAdd (Ψ u)))))) = _
  simp


theorem exists_quad_of_symmetricNatural_eight [Finite V] {X : Subgroup (MulAut V)}
    (h : SymmetricNatural X ⊤ ⊥ 8) :
    ∃ q : V → ZMod 2, IsQuadraticFormOn q ∧ IsNondegQuadratic q ∧
      (∃ E : Subgroup V, Nat.card E = 2 ^ 3 ∧ ∀ e ∈ E, q e = 0) ∧ Nat.card V = 2 ^ 6 ∧
        X = orthogonalGroupOf q := by
  obtain ⟨π, Ψ, hπs, hΨ⟩ := exists_psi h
  refine ⟨qOfPsi Ψ, isQuadraticFormOn_qOfPsi Ψ, isNondegQuadratic_qOfPsi Ψ,
    ⟨singSub Ψ, card_singSub Ψ, singSub_q Ψ⟩, card_of_psi Ψ, ?_⟩
  ext g
  constructor
  · intro hg
    obtain ⟨σ, hσ⟩ := hπs ⟨g, hg⟩
    intro u
    have h1 : (g : MulAut V) = ((π σ : ↥X) : MulAut V) := by rw [hσ]
    show p4insporth_q8 (Multiplicative.toAdd (Ψ (g u))) = p4insporth_q8 (Multiplicative.toAdd (Ψ u))
    rw [h1, hΨ, toAdd_ofAdd]
    exact p4insporth_q8_perm σ _
  · intro hg
    have hmem : toGL Ψ g ∈ orthSub p4insporth_q8 := by
      intro x
      obtain ⟨u, rfl⟩ : ∃ u : V, Multiplicative.toAdd (Ψ u) = x :=
        ⟨Ψ.symm (Multiplicative.ofAdd x), by simp⟩
      rw [toGL_apply]
      exact hg u
    rw [← p4insporth_range_perm8] at hmem
    obtain ⟨σ, hσ⟩ := hmem
    have hg' : g = ((π σ : ↥X) : MulAut V) := by
      ext u
      apply Ψ.injective
      rw [hΨ]
      have := toGL_apply Ψ g u
      rw [← hσ] at this
      rw [this, ofAdd_toAdd]
    rw [hg']
    exact (π σ).2

end Orth

end LRed4

end CFSG.Quasithin
