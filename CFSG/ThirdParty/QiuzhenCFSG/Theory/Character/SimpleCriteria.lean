module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.ClassFunction
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.ConjClassFunction
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.RepEquiv
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.Induction
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.Maschke
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RepresentationTheory.FinGroupCharZero
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped BigOperators

namespace CFSG.Theory.Character

open _root_.Representation
open Theory.Representation

open Theory.Character

attribute [local instance] Fintype.ofFinite

variable {G V : Type*} [Group G] [Finite G]
variable [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- Unbundled simplicity criterion: an irreducible complex representation has one-dimensional endomorphism algebra, and conversely when `|G|` is invertible. -/
public theorem irreducible_iff_end_dimension_one
    (ρ : Representation ℂ G V) :
    Representation.IsIrreducible ρ ↔
      Module.finrank ℂ (Representation.IntertwiningMap ρ ρ) = 1 := by
  classical
  have : NeZero (Nat.card G : ℂ) := ⟨by
    exact_mod_cast (Nat.card_pos (α := G)).ne'⟩
  constructor
  · intro hρ
    let : Representation.IsIrreducible ρ := hρ
    exact Representation.IsIrreducible.finrank_intertwiningMap_self (ρ := ρ)
  · intro hend
    have hpos : 0 < Module.finrank ℂ (Representation.IntertwiningMap ρ ρ) := by
      omega
    have : Nontrivial (Representation.IntertwiningMap ρ ρ) :=
      (Module.finrank_pos_iff (R := ℂ) (M := Representation.IntertwiningMap ρ ρ)).mp hpos
    have hV_nontrivial : Nontrivial V := by
      by_contra hV
      have hsub : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
      have hzero : (1 : Representation.IntertwiningMap ρ ρ) = 0 := by
        ext v
        exact hsub.elim _ _
      exact one_ne_zero hzero
    have : Nontrivial V := hV_nontrivial
    let : Nontrivial ρ.asModule := hV_nontrivial
    rw [Representation.irreducible_iff_isSimpleModule_asModule, isSimpleModule_iff]
    change IsSimpleOrder (Submodule (MonoidAlgebra ℂ G) ρ.asModule)
    refine
      { toNontrivial := ?_
        eq_bot_or_eq_top := ?_ }
    · exact ⟨⟨⊥, ⊤, bot_ne_top⟩⟩
    · intro N
      by_cases hNbot : N = ⊥
      · exact Or.inl hNbot
      · by_cases hNtop : N = ⊤
        · exact Or.inr hNtop
        · exfalso
          have hcompl :
              ∃ P : Submodule (MonoidAlgebra ℂ G) ρ.asModule, IsCompl N P :=
            MonoidAlgebra.Submodule.exists_isCompl'
              (k := ℂ) (G := G) (V := ρ.asModule) N
          obtain ⟨P, hPcompl⟩ := hcompl
          let eEnd : Module.End (MonoidAlgebra ℂ G) ρ.asModule :=
            Submodule.projection N P hPcompl
          let e : Representation.IntertwiningMap ρ ρ :=
            (Representation.IntertwiningMap.equivAlgEnd (ρ := ρ)).symm eEnd
          have heEnd_ne_zero : eEnd ≠ 0 := by
            obtain ⟨x, hxN, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hNbot
            have hxproj : eEnd x = x := by
              simpa [eEnd] using Submodule.projection_apply_left hPcompl (⟨x, hxN⟩ : N)
            intro he0
            exact hx0 (by simpa [he0] using hxproj.symm)
          have he_ne_zero : e ≠ 0 := by
            intro he0
            apply heEnd_ne_zero
            simpa [e] using
              congrArg (Representation.IntertwiningMap.equivAlgEnd (ρ := ρ)) he0
          have hP_nonbot : P ≠ ⊥ := by
            intro hPbot
            apply hNtop
            calc
              N = N ⊔ P := by rw [hPbot, sup_bot_eq]
              _ = ⊤ := hPcompl.sup_eq_top
          have heEnd_ne_one : eEnd ≠ 1 := by
            obtain ⟨y, hyP, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP_nonbot
            have hyproj : eEnd y = 0 := by
              simpa [eEnd] using
                (Submodule.projection_apply_eq_zero_iff hPcompl (x := y)).2 hyP
            intro he1
            exact hy0 (by simpa [he1] using hyproj)
          have he_ne_one : e ≠ 1 := by
            intro he1
            apply heEnd_ne_one
            simpa [e] using
              congrArg (Representation.IntertwiningMap.equivAlgEnd (ρ := ρ)) he1
          have he_idem : e * e = e := by
            apply (Representation.IntertwiningMap.equivAlgEnd (ρ := ρ)).injective
            simpa [e] using (Submodule.isIdempotentElem_projection hPcompl).eq
          obtain ⟨c, hc⟩ :
              ∃ c : ℂ, c • (1 : Representation.IntertwiningMap ρ ρ) = e := by
            exact
              (finrank_eq_one_iff_of_nonzero'
                (K := ℂ) (V := Representation.IntertwiningMap ρ ρ)
                (1 : Representation.IntertwiningMap ρ ρ) one_ne_zero).mp hend e
          obtain ⟨v0, hv0⟩ := exists_ne (0 : V)
          have hcv : e v0 = c • v0 := by
            simpa using (congrArg (fun f : Representation.IntertwiningMap ρ ρ => f v0) hc).symm
          have hsqv : (c * c) • v0 = c • v0 := by
            calc
              (c * c) • v0 = c • (c • v0) := by rw [smul_smul]
              _ = c • e v0 := by rw [hcv.symm]
              _ = e (c • v0) := by rw [map_smul]
              _ = e (e v0) := by rw [hcv.symm]
              _ = e v0 := by
                    simpa using congrArg
                      (fun f : Representation.IntertwiningMap ρ ρ => f v0) he_idem
              _ = c • v0 := hcv
          have hscalar : (c * c - c) • v0 = 0 := by
            rw [sub_smul, hsqv, sub_self]
          have hc_zero_or_one : c = 0 ∨ c = 1 := by
            have hquad : c * c - c = 0 :=
              (smul_eq_zero.mp hscalar).resolve_right hv0
            have hfactor : c * (c - 1) = 0 := by
              rw [mul_sub, mul_one]
              exact hquad
            rcases mul_eq_zero.mp hfactor with hc0 | hc1
            · exact Or.inl hc0
            · exact Or.inr (sub_eq_zero.mp hc1)
          rcases hc_zero_or_one with rfl | rfl
          · exact he_ne_zero (by simpa using hc.symm)
          · exact he_ne_one (by simpa using hc.symm)

/-- Unbundled character-norm criterion for irreducibility. -/
public theorem irreducible_iff_character_norm_one
    (ρ : Representation ℂ G V) :
    Representation.IsIrreducible ρ ↔
      classFunctionInner (characterClassFunction ρ) (characterClassFunction ρ) = 1 := by
  classical
  have hcard_ne : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := G)).ne'
  let : Invertible (Nat.card G : ℂ) := invertibleOfNonzero hcard_ne
  have hinner :
      classFunctionInner (characterClassFunction ρ) (characterClassFunction ρ) =
        (Nat.card G : ℂ)⁻¹ * ∑ g : G, ρ.character g * star (ρ.character g) := by
    change
      (Nat.card G : ℂ)⁻¹ * ∑ g : G, ρ.character g * star (ρ.character g) =
      (Nat.card G : ℂ)⁻¹ * ∑ g : G, ρ.character g * star (ρ.character g)
    rfl
  have hsumSelf :
      (Nat.card G : ℂ)⁻¹ * ∑ g : G, ρ.character g * star (ρ.character g) =
        (Module.finrank ℂ (Representation.IntertwiningMap ρ ρ) : ℂ) := by
    calc
      (Nat.card G : ℂ)⁻¹ * ∑ g : G, ρ.character g * star (ρ.character g)
          = (Nat.card G : ℂ)⁻¹ * ∑ g : G, ρ.character g * ρ.character g⁻¹ := by
              congr 1
              refine Finset.sum_congr rfl ?_
              intro g _hg
              rw [(representation_character_inv_eq_star_character ρ g).symm]
      _ = (Module.finrank ℂ (Representation.IntertwiningMap ρ ρ) : ℂ) := by
            simpa using
              (Representation.card_inv_mul_sum_char_mul_char_eq_finrank
                (ρ := ρ) (σ := ρ))
  rw [hinner, hsumSelf]
  constructor
  · intro h
    exact_mod_cast (irreducible_iff_end_dimension_one (ρ := ρ)).1 h
  · intro h
    apply (irreducible_iff_end_dimension_one (ρ := ρ)).2
    exact_mod_cast h


/-- The class function of an irreducible finite-dimensional complex representation is
an irreducible character, independently of the chosen coefficient-space model. -/
public theorem isIrreducibleCharacter_characterClassFunction
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (hρ : Representation.IsIrreducible ρ) :
    IsIrreducibleConjCharacter (characterClassFunction ρ) := by
  constructor
  · let b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V := Module.finBasis ℂ V
    let e : V ≃ₗ[ℂ] (Fin (Module.finrank ℂ V) → ℂ) := b.equivFun
    let σ : Representation ℂ G (Fin (Module.finrank ℂ V) → ℂ) :=
      { toFun := fun g => e.conj (ρ g)
        map_one' := by
          ext x
          simp [LinearEquiv.conj_apply]
        map_mul' := by
          intro g h
          ext x
          simp [LinearEquiv.conj_apply, map_mul] }
    refine ⟨Module.finrank ℂ V, σ, ?_⟩
    ext c
    rcases ConjClasses.exists_rep c with ⟨g, rfl⟩
    change ρ.character g = σ.character g
    symm
    dsimp [σ, Representation.character]
    exact LinearMap.trace_conj' (R := ℂ) (M := V)
      (N := Fin (Module.finrank ℂ V) → ℂ) (ρ g)
      (Module.Basis.equivFun (Module.finBasis ℂ V))
  · exact (irreducible_iff_character_norm_one ρ).1 hρ

/-- Irreducible representations over an algebraically closed nonmodular field with
the same character are equivalent. -/
public theorem equiv_of_irreducible_char_eq
    {G : Type*} [Group G] [Finite G]
    {F : Type*} [Field F] [IsAlgClosed F]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    {ρ : Representation F G V} {σ : Representation F G W}
    [IsIrreducible ρ] [IsIrreducible σ]
    (hc : ¬ ringChar F ∣ Nat.card G)
    (hchar : ρ.character = σ.character) :
    Nonempty (Equiv σ ρ) := by
  let : Fintype G := Fintype.ofFinite G
  have hcard_ne_zero : (Nat.card G : F) ≠ 0 := by
    intro hzero
    exact hc ((ringChar.spec F (Nat.card G)).1 hzero)
  let : Invertible (Nat.card G : F) := invertibleOfNonzero hcard_ne_zero
  by_cases hE : Nonempty (Equiv σ ρ)
  · exact hE
  · have horth := Representation.char_orthonormal (ρ := ρ) (σ := σ)
    have hself := Representation.char_orthonormal (ρ := ρ) (σ := ρ)
    rw [hchar] at horth
    have horth' :
        (Nat.card G : F)⁻¹ * ∑ g : G, ρ.character g * ρ.character g⁻¹ = (0 : F) := by
      have horthσ :
          (Nat.card G : F)⁻¹ * ∑ g : G, σ.character g * σ.character g⁻¹ = (0 : F) := by
        simpa [hE] using horth
      simpa [hchar] using horthσ
    have hself' :
        (Nat.card G : F)⁻¹ * ∑ g : G, ρ.character g * ρ.character g⁻¹ = (1 : F) := by
      simpa [show Nonempty (Equiv ρ ρ) from ⟨Representation.Equiv.refl ρ⟩] using hself
    exact False.elim (zero_ne_one (horth'.symm.trans hself'))
set_option backward.isDefEq.respectTransparency false in
/-- The one-dimensional trivial complex representation is irreducible. -/
public theorem trivial_complex_irreducible
    {G : Type*} [Group G] [Finite G] :
    Representation.IsIrreducible (Representation.trivial ℂ G ℂ) := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule, isSimpleModule_iff]
  exact is_simple_module_of_finrank_eq_one
    (K := ℂ) (A := MonoidAlgebra ℂ G)
    (V := (Representation.trivial ℂ G ℂ).asModule) (CommSemiring.finrank_self ℂ)
/-- Custom bundled form of the equal-character irreducible equivalence theorem. -/
public theorem repEquiv_of_irreducible_char_eq
    {G : Type*} [Group G] [Finite G]
    {F : Type*} [Field F] [IsAlgClosed F]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    {ρ : Representation F G V} {σ : Representation F G W}
    [IsIrreducible ρ] [IsIrreducible σ]
    (hc : ¬ ringChar F ∣ Nat.card G)
    (hchar : ρ.character = σ.character) :
    Nonempty (σ ≃ₗ ρ) := by
  rcases equiv_of_irreducible_char_eq (ρ := ρ) (σ := σ) hc hchar with ⟨e⟩
  exact ⟨RepEquiv.ofRepresentationEquiv e⟩
end CFSG.Theory.Character
