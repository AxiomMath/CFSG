module

public import CFSG.Quasithin.Background.F918Z0AuxCoord
public import CFSG.LocalAnalysis.SteinbergCEIsotypicMultiplicity

public section

namespace CFSG.Quasithin.MatModel

open CFSG.LocalAnalysis.CommutingFactor

section Dictionary

variable {V : Type} [CommGroup V]

@[expose, instance_reducible] def z2Mod (hexp : ∀ v : V, v ^ 2 = 1) :
    Module (ZMod 2) (Additive V) :=
  AddCommGroup.zmodModule (fun v => by
    have h : Additive.ofMul (Additive.toMul v ^ 2) = Additive.ofMul 1 := by rw [hexp]
    rw [ofMul_pow] at h
    simpa using h)

variable [Module (ZMod 2) (Additive V)]

@[expose] noncomputable def autLin : MulAut V →* Module.End (ZMod 2) (Additive V) where
  toFun g := AddMonoidHom.toZModLinearMap 2
    (AddMonoidHom.mk' (fun v : Additive V => Additive.ofMul (g (Additive.toMul v)))
      (fun a b => by simp [map_mul]))
  map_one' := by
    ext v
    rfl
  map_mul' g h := by
    ext v
    rfl

@[expose] noncomputable def autUnit : MulAut V →* (Module.End (ZMod 2) (Additive V))ˣ :=
  autLin.toHomUnits

theorem autUnit_apply (g : MulAut V) (v : Additive V) :
    (autUnit g : Module.End (ZMod 2) (Additive V)) v = Additive.ofMul (g (Additive.toMul v)) :=
  rfl

@[expose] def ofSub (N : Submodule (ZMod 2) (Additive V)) : Subgroup V where
  carrier := {w | Additive.ofMul w ∈ N}
  mul_mem' := fun {_ _} ha hb => N.add_mem ha hb
  one_mem' := N.zero_mem
  inv_mem' := fun {_} ha => N.neg_mem ha

theorem ofSub_eq_bot {N : Submodule (ZMod 2) (Additive V)} : ofSub N = ⊥ ↔ N = ⊥ := by
  constructor
  · intro h
    rw [eq_bot_iff]
    intro v hv
    have : Additive.toMul v ∈ ofSub N := hv
    rw [h, Subgroup.mem_bot] at this
    rw [Submodule.mem_bot]
    exact Additive.toMul.injective this
  · intro h
    rw [eq_bot_iff]
    intro w hw
    have : Additive.ofMul w ∈ N := hw
    rw [h, Submodule.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact Additive.ofMul.injective this

theorem ofSub_eq_top {N : Submodule (ZMod 2) (Additive V)} : ofSub N = ⊤ ↔ N = ⊤ := by
  constructor
  · intro h
    rw [eq_top_iff]
    intro v _
    have : Additive.toMul v ∈ ofSub N := by rw [h]; trivial
    exact this
  · intro h
    rw [eq_top_iff]
    intro w _
    show Additive.ofMul w ∈ N
    rw [h]
    trivial

end Dictionary

section Hypotheses

variable {V : Type} [CommGroup V] [Module (ZMod 2) (Additive V)] {D X : Subgroup (MulAut V)}

theorem comm_units (hcomm : ∀ g ∈ D, ∀ x ∈ X, g * x = x * g) :
    ∀ x ∈ X.map (autUnit (V := V)), ∀ d ∈ D.map (autUnit (V := V)), x * d = d * x := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨g, hg, rfl⟩
  rw [← map_mul, ← map_mul, ← hcomm g hg x hx]

theorem irr_units
    (hirr : ∀ U : Subgroup V, (∀ g ∈ D ⊔ X, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤) :
    ∀ W : Submodule (ZMod 2) (Additive V),
      (∀ g ∈ X.map (autUnit (V := V)) ⊔ D.map (autUnit (V := V)), ∀ v ∈ W,
        (g : Module.End (ZMod 2) (Additive V)) v ∈ W) → W = ⊥ ∨ W = ⊤ := by
  intro W hW
  have hD : ∀ g ∈ D, ∀ u ∈ ofSub W, g u ∈ ofSub W := fun g hg u hu =>
    hW (autUnit g) (Subgroup.mem_sup_right ⟨g, hg, rfl⟩) (Additive.ofMul u) hu
  have hX : ∀ g ∈ X, ∀ u ∈ ofSub W, g u ∈ ofSub W := fun g hg u hu =>
    hW (autUnit g) (Subgroup.mem_sup_left ⟨g, hg, rfl⟩) (Additive.ofMul u) hu
  rcases hirr _ (invariant_sup_aut hD hX) with h | h
  · exact Or.inl (ofSub_eq_bot.mp h)
  · exact Or.inr (ofSub_eq_top.mp h)

end Hypotheses

section Minimal

variable {k : Type*} [Field k] {S : Type*} [AddCommGroup S] [Module k S] [Finite S] [Nontrivial S]

theorem exists_minimal_inv (D : Subgroup (Module.End k S)ˣ) :
    ∃ I : Submodule k S, I ≠ ⊥ ∧ (∀ d ∈ D, ∀ v ∈ I, (d : Module.End k S) v ∈ I) ∧
      ∀ U ≤ I, (∀ d ∈ D, ∀ v ∈ U, (d : Module.End k S) v ∈ U) → U = ⊥ ∨ U = I := by
  have hfin : Finite (Submodule k S) :=
    Finite.of_injective (fun N : Submodule k S => (N : Set S)) SetLike.coe_injective
  let P : Submodule k S → Prop :=
    fun N => N ≠ ⊥ ∧ ∀ d ∈ D, ∀ v ∈ N, (d : Module.End k S) v ∈ N
  have hP : P ⊤ := ⟨top_ne_bot, fun d _ v _ => Submodule.mem_top⟩
  obtain ⟨I, hI, hmin⟩ := (wellFounded_lt (α := Submodule k S)).has_min {N | P N} ⟨⊤, hP⟩
  refine ⟨I, hI.1, hI.2, fun U hU hUD => ?_⟩
  by_cases hU0 : U = ⊥
  · exact Or.inl hU0
  · right
    by_contra hne
    exact hmin U ⟨hU0, hUD⟩ (lt_of_le_of_ne hU hne)

end Minimal

section EndFieldSec

variable {S : Type} [AddCommGroup S] [Module (ZMod 2) S] {D : Subgroup (Module.End (ZMod 2) S)ˣ}
  {I : Submodule (ZMod 2) S} {hDI : ∀ d ∈ D, ∀ v ∈ I, (d : Module.End (ZMod 2) S) v ∈ I}

@[expose] def EndField (_hF : IsField (commutantD hDI)) : Type := ↥(commutantD hDI)

@[expose] def EndField.toEnd {hF : IsField (commutantD hDI)} (c : EndField hF) :
    Module.End (ZMod 2) ↥I :=
  (show ↥(commutantD hDI) from c).1

@[expose] def EndField.mk (hF : IsField (commutantD hDI)) (φ : Module.End (ZMod 2) ↥I)
    (h : φ ∈ commutantD hDI) : EndField hF :=
  (⟨φ, h⟩ : ↥(commutantD hDI))

theorem EndField.mem {hF : IsField (commutantD hDI)} (c : EndField hF) :
    c.toEnd ∈ commutantD hDI :=
  (show ↥(commutantD hDI) from c).2

noncomputable instance (hF : IsField (commutantD hDI)) : Field (EndField hF) :=
  (IsField.toField (R := ↥(commutantD hDI)) hF : Field ↥(commutantD hDI))

@[expose] noncomputable def endFieldHom (hF : IsField (commutantD hDI)) :
    EndField hF →+* Module.End (ZMod 2) ↥I where
  toFun c := c.toEnd
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

noncomputable instance (hF : IsField (commutantD hDI)) : Module (EndField hF) ↥I :=
  Module.compHom ↥I (endFieldHom hF)

@[expose] noncomputable def resF (hF : IsField (commutantD hDI)) (d : ↥D) :
    Module.End (EndField hF) ↥I where
  toFun w := resD hDI d w
  map_add' w w' := map_add (resD hDI d) w w'
  map_smul' c w := LinearMap.congr_fun ((mem_commutantD hDI).mp c.mem d) w

@[expose] noncomputable def resFHom (hF : IsField (commutantD hDI)) :
    ↥D →* Module.End (EndField hF) ↥I where
  toFun := resF hF
  map_one' := by
    ext w
    rfl
  map_mul' d d' := by
    ext w
    rfl

end EndFieldSec

section Main

variable {V : Type} [CommGroup V]

theorem exists_isDecomp [Finite V] [Nontrivial V] (hexp : ∀ v : V, v ^ 2 = 1)
    {D X : Subgroup (MulAut V)} (hcomm : ∀ g ∈ D, ∀ x ∈ X, g * x = x * g)
    (hirr : ∀ U : Subgroup V, (∀ g ∈ D ⊔ X, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (I : Type) (_ : AddCommGroup I)
      (_ : Module F I) (_ : Finite I) (_ : Nontrivial I) (r : ℕ) (_ : 0 < r)
      (Φ : (Fin r → I) ≃+ Additive V) (ρI : ↥D →* Module.End F I)
      (σ : ↥X →* Matrix.GeneralLinearGroup (Fin r) F), IsDecomp D X Φ ρI σ := by
  let _ : Module (ZMod 2) (Additive V) := z2Mod hexp
  have : Finite (Additive V) := ‹Finite V›
  have : Nontrivial (Additive V) := ‹Nontrivial V›
  obtain ⟨I, hI0, hDI, hIirr⟩ := exists_minimal_inv (D.map (autUnit (V := V)))
  obtain ⟨r, Φ, hr, hΦ, -, hF, hFfin, hXC, ⟨ψ, hψ⟩, -⟩ :=
    commuting_factor_irreducible_modules_have_isotypic_multiplicity (comm_units hcomm)
      (irr_units hirr) hDI hI0 hIirr
  have hFfin' : Finite (EndField hF) := hFfin
  have hnt : Nontrivial ↥I := Submodule.nontrivial_iff_ne_bot.mpr hI0
  have hchar : CharP (EndField hF) 2 := by
    have : CharP (Module.End (ZMod 2) ↥I) 2 :=
      charP_of_injective_algebraMap (algebraMap (ZMod 2) (Module.End (ZMod 2) ↥I)).injective 2
    exact ((endFieldHom hF).charP_iff_charP 2).mpr this
  let ρI : ↥D →* Module.End (EndField hF) ↥I := (resFHom hF).comp (autUnit.subgroupMap D)
  let σ₀ : ↥X →* (Matrix (Fin r) (Fin r) ↥(commutantD hDI))ˣ :=
    ψ.toMonoidHom.comp ((Subgroup.inclusion hXC).comp (autUnit.subgroupMap X))
  let σ : ↥X →* Matrix.GeneralLinearGroup (Fin r) (EndField hF) := σ₀
  refine ⟨EndField hF, inferInstance, hFfin', hchar, ↥I, inferInstance, inferInstance,
    inferInstance, hnt, r, hr, Φ.toAddEquiv, ρI, σ, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g f
    exact hΦ ⟨autUnit g, g, g.2, rfl⟩ f
  · intro x f i
    have hΦf : Φ f = ∑ j, Φ (Pi.single j (f j)) := by
      rw [← map_sum, Finset.univ_sum_single]
    have key : ∀ j, Φ.symm ((autUnit (x : MulAut V) : Module.End (ZMod 2) (Additive V))
        (Φ (Pi.single j (f j)))) i =
        ((σ x : Matrix.GeneralLinearGroup (Fin r) (EndField hF)) :
          Matrix (Fin r) (Fin r) (EndField hF)) i j • f j := fun j =>
      (hψ ⟨autUnit (x : MulAut V), hXC ⟨x, x.2, rfl⟩⟩ i j (f j)).symm
    show Φ.symm ((autUnit (x : MulAut V) : Module.End (ZMod 2) (Additive V)) (Φ f)) i = _
    rw [hΦf, map_sum, map_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun j _ => key j
  · intro W hW
    let U : Submodule (ZMod 2) (Additive V) := (AddSubgroup.toZModSubmodule 2 W).map I.subtype
    have hUI : U ≤ I := Submodule.map_subtype_le _ _
    have hUD : ∀ d ∈ D.map (autUnit (V := V)), ∀ v ∈ U,
        (d : Module.End (ZMod 2) (Additive V)) v ∈ U := by
      rintro _ ⟨g, hg, rfl⟩ _ ⟨w, hw, rfl⟩
      exact ⟨resD hDI ⟨autUnit g, g, hg, rfl⟩ w, hW ⟨g, hg⟩ w hw, rfl⟩
    rcases hIirr U hUI hUD with h | h
    · left
      rw [eq_bot_iff]
      intro w hw
      have h1 : (w : Additive V) ∈ U := ⟨w, hw, rfl⟩
      rw [h, Submodule.mem_bot] at h1
      exact (AddSubgroup.mem_bot).mpr (Subtype.ext h1)
    · right
      rw [eq_top_iff]
      intro w _
      have h1 : (w : Additive V) ∈ U := by rw [h]; exact w.2
      obtain ⟨w', hw', hww'⟩ := h1
      rw [← Subtype.ext hww']
      exact hw'
  · intro φ hφ
    have hmem : AddMonoidHom.toZModLinearMap 2 φ ∈ commutantD hDI := by
      rw [mem_commutantD]
      rintro ⟨_, g, hg, rfl⟩
      refine LinearMap.ext fun w => ?_
      exact (hφ ⟨g, hg⟩ w).symm
    exact ⟨EndField.mk hF _ hmem, fun w => rfl⟩

end Main

end CFSG.Quasithin.MatModel
