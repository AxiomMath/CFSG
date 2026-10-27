module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7SecGroup
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aGLTwist
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aSelfDualRank
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

namespace B45SL3

open CFSG.QuasithinUnique.Setup.X7a
open CFSG.QuasithinUnique.Setup.X7 (matRep matRep_apply matMap matMap_apply MatIso)
open CFSG.QuasithinUnique.Setup.X7b (toMatRep)
open scoped MatrixGroups Matrix

section Move

variable {F : Type} [Field F] {U : Type} [AddCommGroup U] [Module (ZMod 2) U]

theorem toMatrix_mul_toMatRep {n : ℕ} (ρ : Representation (ZMod 2) SL(3, F) U)
    (bas : Module.Basis (Fin n) (ZMod 2) U) (a : U ≃ₗ[ZMod 2] U) (ψ : SL(3, F) →* SL(3, F))
    (hint : ∀ x u, a (ρ x u) = ρ (ψ x) (a u)) (x : SL(3, F)) :
    LinearMap.toMatrix bas bas a.toLinearMap * toMatRep ρ bas x =
      toMatRep ρ bas (ψ x) * LinearMap.toMatrix bas bas a.toLinearMap := by
  show LinearMap.toMatrix bas bas a.toLinearMap * LinearMap.toMatrix bas bas (ρ x) =
    LinearMap.toMatrix bas bas (ρ (ψ x)) * LinearMap.toMatrix bas bas a.toLinearMap
  rw [← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_mul]
  congr 1
  exact LinearMap.ext fun u => hint x u

variable [CharP F 2] [Finite U]

theorem card_le_rank_of_moved {n : ℕ} (ρ : Representation (ZMod 2) SL(3, F) U)
    (bas : Module.Basis (Fin n) (ZMod 2) U)
    (W₀ : Subrepresentation (matRep (matMap (ZMod.castHom (dvd_refl 2) F) (toMatRep ρ bas))))
    (hW : W₀.toRepresentation.IsIrreducible)
    {κ : Type} [Fintype κ] [DecidableEq κ] {T : SL(3, F) →* Matrix κ κ F}
    (e₀ : W₀.toRepresentation.Equiv (matRep T)) (a : U ≃ₗ[ZMod 2] U) (ψ : MulAut SL(3, F))
    (hint : ∀ x u, a (ρ x u) = ρ (ψ x) (a u))
    (hmove : ¬ Nonempty ((matRep T).Equiv (matRep (T.comp ψ.toMonoidHom)))) :
    Fintype.card κ ≤ Module.finrank (ZMod 2) (LinearMap.range (a.toLinearMap - 1)) := by
  classical
  have hfinU : Module.Finite (ZMod 2) U := Module.Finite.of_finite
  let φ : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F
  let PF := matMap φ (toMatRep ρ bas)
  let A₀ := LinearMap.toMatrix bas bas a.toLinearMap
  let B₀ := LinearMap.toMatrix bas bas a.symm.toLinearMap
  let AF := A₀.map φ
  let BF := B₀.map φ
  have hAB₀ : A₀ * B₀ = 1 := by
    show LinearMap.toMatrix bas bas a.toLinearMap * LinearMap.toMatrix bas bas a.symm.toLinearMap
      = 1
    rw [← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_one bas]
    congr 1
    exact LinearMap.ext fun u => a.apply_symm_apply u
  have hBA₀ : B₀ * A₀ = 1 := by
    show LinearMap.toMatrix bas bas a.symm.toLinearMap * LinearMap.toMatrix bas bas a.toLinearMap
      = 1
    rw [← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_one bas]
    congr 1
    exact LinearMap.ext fun u => a.symm_apply_apply u
  have hAB : AF * BF = 1 := by
    show A₀.map φ * B₀.map φ = 1
    rw [← Matrix.map_mul, hAB₀, Matrix.map_one φ (map_zero φ) (map_one φ)]
  have hBA : BF * AF = 1 := by
    show B₀.map φ * A₀.map φ = 1
    rw [← Matrix.map_mul, hBA₀, Matrix.map_one φ (map_zero φ) (map_one φ)]
  have hcomm : ∀ x, AF * PF x = PF (ψ x) * AF := by
    intro x
    show A₀.map φ * (toMatRep ρ bas x).map φ = (toMatRep ρ bas (ψ x)).map φ * A₀.map φ
    rw [← Matrix.map_mul, ← Matrix.map_mul]
    exact congrArg (fun M => M.map φ) (toMatrix_mul_toMatRep ρ bas a ψ.toMonoidHom hint x)
  have hcomm' : ∀ x, PF x * AF = AF * PF (ψ⁻¹ x) := by
    intro x
    rw [hcomm (ψ⁻¹ x), MulAut.apply_inv_self]
  let L : (Fin n → F) ≃ₗ[F] (Fin n → F) :=
    LinearEquiv.ofLinearMap (Matrix.mulVecLin AF) (Matrix.mulVecLin BF)
      (by rw [← Matrix.mulVecLin_mul, hAB, Matrix.mulVecLin_one])
      (by rw [← Matrix.mulVecLin_mul, hBA, Matrix.mulVecLin_one])
  have hL : ∀ v, L v = AF *ᵥ v := fun v => rfl
  have hfix : ∀ w ∈ W₀.toSubmodule, AF *ᵥ w = w → w = 0 := by
    intro w hw hAw
    by_contra hw0
    set W' : Submodule F (Fin n → F) := W₀.toSubmodule.map L.toLinearMap with hW'
    have hW'inv : ∀ g, ∀ v ∈ W', PF g *ᵥ v ∈ W' := by
      rintro g _ ⟨u, hu, rfl⟩
      refine ⟨PF (ψ⁻¹ g) *ᵥ u, ?_, ?_⟩
      · have := W₀.apply_mem_toSubmodule (ψ⁻¹ g) hu
        simpa [matRep_apply] using this
      · show AF *ᵥ (PF (ψ⁻¹ g) *ᵥ u) = PF g *ᵥ (AF *ᵥ u)
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hcomm' g]
    let Z : Submodule F W₀.toSubmodule := W'.comap W₀.toSubmodule.subtype
    have hZinv : ∀ g, ∀ u ∈ Z, W₀.toRepresentation g u ∈ Z := by
      intro g u hu
      have h1 : PF g *ᵥ (u : Fin n → F) ∈ W' := hW'inv g u hu
      exact h1
    have hwZ : (⟨w, hw⟩ : W₀.toSubmodule) ∈ Z := by
      show w ∈ W'
      refine ⟨w, hw, ?_⟩
      show AF *ᵥ w = w
      exact hAw
    rcases ((CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff _).mp hW).2 Z hZinv with h0 | htop
    · rw [h0, Submodule.mem_bot] at hwZ
      exact hw0 (congrArg Subtype.val hwZ)
    ·
      have hle : W₀.toSubmodule ≤ W' := by
        intro v hv
        have : (⟨v, hv⟩ : W₀.toSubmodule) ∈ Z := by rw [htop]; exact Submodule.mem_top
        exact this
      have hfr : Module.finrank F W' = Module.finrank F W₀.toSubmodule :=
        LinearEquiv.finrank_map_eq L W₀.toSubmodule
      have heq : W₀.toSubmodule = W' := Submodule.eq_of_le_of_finrank_eq hle hfr.symm
      have hmapsto : ∀ v ∈ W₀.toSubmodule, AF *ᵥ v ∈ W₀.toSubmodule := by
        intro v hv
        rw [heq]
        exact ⟨v, hv, rfl⟩
      let J₀ : W₀.toSubmodule →ₗ[F] W₀.toSubmodule :=
        (Matrix.mulVecLin AF).restrict hmapsto
      have hJinj : Function.Injective J₀ := by
        intro x y hxy
        apply Subtype.ext
        have h1 : AF *ᵥ (x : Fin n → F) = AF *ᵥ (y : Fin n → F) := congrArg Subtype.val hxy
        exact L.injective h1
      let J : W₀.toSubmodule ≃ₗ[F] W₀.toSubmodule :=
        LinearEquiv.ofInjectiveEndo J₀ hJinj
      have hJ : ∀ x, (J x : Fin n → F) = AF *ᵥ (x : Fin n → F) := fun x => rfl
      apply hmove
      let E : (κ → F) ≃ₗ[F] (κ → F) := (e₀.symm.toLinearEquiv.trans J).trans e₀.toLinearEquiv
      refine ⟨Representation.Equiv.mk E (fun g => LinearMap.ext fun v => ?_)⟩
      obtain ⟨x, rfl⟩ := e₀.surjective v
      have he1 : ∀ (h : SL(3, F)) (y : W₀.toSubmodule),
          e₀ (W₀.toRepresentation h y) = matRep T h (e₀ y) := fun h y =>
        Representation.IntertwiningMap.isIntertwining _ _ e₀.toIntertwiningMap h y
      have hJrep : J (W₀.toRepresentation g x) = W₀.toRepresentation (ψ g) (J x) := by
        apply Subtype.ext
        rw [hJ]
        show AF *ᵥ (PF g *ᵥ (x : Fin n → F)) = PF (ψ g) *ᵥ (AF *ᵥ (x : Fin n → F))
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hcomm g]
      show E (matRep T g (e₀ x)) = matRep T (ψ g) (E (e₀ x))
      have hE : ∀ y : W₀.toSubmodule, E (e₀ y) = e₀ (J y) := by
        intro y
        show e₀ (J (e₀.symm (e₀ y))) = e₀ (J y)
        rw [Representation.Equiv.symm_apply_apply]
      rw [← he1, hE, hE, hJrep, he1]
  have hdimW : Module.finrank F W₀.toSubmodule = Fintype.card κ := by
    rw [LinearEquiv.finrank_eq e₀.toLinearEquiv, Module.finrank_fintype_fun_eq_card]
  have hrkF : Module.finrank F W₀.toSubmodule ≤ (AF - 1).rank := by
    let D : W₀.toSubmodule →ₗ[F] (Fin n → F) :=
      (Matrix.mulVecLin (AF - 1)).comp W₀.toSubmodule.subtype
    have hDinj : Function.Injective D := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro x hx
      have h1 : (AF - 1) *ᵥ (x : Fin n → F) = 0 := hx
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h1
      exact Subtype.ext (hfix x x.2 h1)
    have h1 := LinearMap.finrank_range_of_inj hDinj
    have h2 : LinearMap.range D ≤ LinearMap.range (Matrix.mulVecLin (AF - 1)) :=
      LinearMap.range_comp_le_range _ _
    rw [Matrix.rank, ← h1]
    exact Submodule.finrank_mono h2
  have hmap : AF - 1 = (A₀ - 1).map φ := by
    show A₀.map φ - 1 = (A₀ - 1).map φ
    rw [Matrix.map_sub _ (map_sub φ), Matrix.map_one φ (map_zero φ) (map_one φ)]
  have hrk2 : (A₀ - 1).rank = Module.finrank (ZMod 2) (LinearMap.range (a.toLinearMap - 1)) := by
    have e3 : A₀ - 1 = LinearMap.toMatrix bas bas (a.toLinearMap - 1) := by
      rw [map_sub, LinearMap.toMatrix_one]
      rfl
    rw [e3, Matrix.rank_eq_finrank_range_toLin _ bas bas, Matrix.toLin_toMatrix]
  calc Fintype.card κ = Module.finrank F W₀.toSubmodule := hdimW.symm
    _ ≤ (AF - 1).rank := hrkF
    _ = ((A₀ - 1).map φ).rank := by rw [hmap]
    _ ≤ (A₀ - 1).rank := CFSG.QuasithinUnique.Setup.X7b.rank_map_ringHom_le φ _
    _ = _ := hrk2

end Move

section Period

variable {f : ℕ}

theorem finRotate_iterate_val (s : ℕ) (y : Fin f) :
    ((finRotate f)^[s] y : ℕ) = ((y : ℕ) + s) % f := by
  obtain ⟨m, rfl⟩ : ∃ m, f = m + 1 := ⟨f - 1, by have := Fin.pos y; omega⟩
  have hrot1 : ∀ y : Fin (m + 1), (finRotate (m + 1) y).val = (y.val + 1) % (m + 1) := by
    intro y
    rw [coe_finRotate]
    split_ifs with h
    · subst h
      simp [Fin.val_last]
    · have : y.val < m := by
        have h1 := y.isLt
        have h2 : y.val ≠ m := fun hh => h (Fin.ext (by simpa [Fin.val_last] using hh))
        omega
      rw [Nat.mod_eq_of_lt (by omega)]
  induction s generalizing y with
  | zero => simp [Nat.mod_eq_of_lt y.isLt]
  | succ s ih =>
    rw [Function.iterate_succ_apply', hrot1, ih]
    rw [Nat.add_mod _ 1 (m + 1), Nat.mod_mod, ← Nat.add_mod, add_assoc]

theorem finRotate_iterate_card (y : Fin f) : (finRotate f)^[f] y = y := by
  apply Fin.ext
  rw [finRotate_iterate_val, Nat.add_mod_right, Nat.mod_eq_of_lt y.isLt]

theorem shiftBits_iterate_eq (s : ℕ) (a : Fin f → Bool) :
    (shiftBits f)^[s] a = a ∘ ((finRotate f).symm)^[s] := by
  induction s generalizing a with
  | zero => rfl
  | succ s ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ]
    rfl

theorem shiftBits_iterate_card (a : Fin f → Bool) : (shiftBits f)^[f] a = a := by
  rw [shiftBits_iterate_eq]
  funext i
  show a (((finRotate f).symm)^[f] i) = a i
  congr 1
  have h := finRotate_iterate_card (f := f) (((finRotate f).symm)^[f] i)
  have hl : Function.LeftInverse ((finRotate f).symm)^[f] (finRotate f)^[f] :=
    Function.LeftInverse.iterate (Equiv.symm_apply_apply (finRotate f)) f
  have hr : Function.RightInverse ((finRotate f).symm)^[f] (finRotate f)^[f] :=
    Function.RightInverse.iterate (Equiv.apply_symm_apply (finRotate f)) f
  calc ((finRotate f).symm)^[f] i = (finRotate f)^[f] (((finRotate f).symm)^[f] i) := h.symm
    _ = i := hr i

theorem shiftBits_iterate_mod (j : ℕ) (a : Fin f → Bool) :
    (shiftBits f)^[j] a = (shiftBits f)^[j % f] a := by
  conv_lhs => rw [← Nat.mod_add_div j f, Function.iterate_add_apply]
  congr 1
  induction j / f with
  | zero => rfl
  | succ q ih => rw [Nat.mul_succ, Function.iterate_add_apply, shiftBits_iterate_card, ih]

theorem card_pairOrbit_le_of_fixed (c : (Fin f → Bool) × (Fin f → Bool)) {r : ℕ} (hr : 1 ≤ r)
    (h : (shiftBits f)^[r] c.1 = c.1 ∧ (shiftBits f)^[r] c.2 = c.2) :
    (pairOrbit f c).card ≤ r := by
  classical
  have hper : ∀ s, (shiftPair f)^[s] c = (shiftPair f)^[s % r] c := by
    intro s
    have hfix : (shiftPair f)^[r] c = c := by
      rw [show c = (c.1, c.2) from rfl, shiftPair_iterate, h.1, h.2]
    conv_lhs => rw [← Nat.mod_add_div s r, Function.iterate_add_apply]
    congr 1
    induction s / r with
    | zero => rfl
    | succ q ih => rw [Nat.mul_succ, Function.iterate_add_apply, hfix, ih]
  have hsub : pairOrbit f c ⊆ (Finset.range r).image fun s => (shiftPair f)^[s] c := by
    intro x hx
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨s % r, Finset.mem_range.mpr (Nat.mod_lt s (by omega)),
      (hper s).symm⟩
  calc (pairOrbit f c).card ≤ ((Finset.range r).image fun s => (shiftPair f)^[s] c).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.range r).card := Finset.card_image_le
    _ = r := Finset.card_range r

end Period

section Field

variable {F : Type} [Field F] [Fintype F] [CharP F 2] {f : ℕ}

open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)
open CFSG.QuasithinUnique.K1 (stdAut)

theorem exists_matIso_comp_stdAut (hF : Fintype.card F = 2 ^ f) (M : GL (Fin 3) F)
    (σ : F ≃+* F) {j : ℕ} (hσ : ∀ x, σ x = x ^ 2 ^ j) (a b : Fin f → Bool) :
    ∃ P Q, MatIso ((tensorRep (F := F) F a b).comp (stdAut M σ 0).toMonoidHom)
      (tensorRep (F := F) F ((shiftBits f)^[j] a) ((shiftBits f)^[j] b)) P Q := by
  have h₁ := (tensorRep_comp_conj (F := F) F M a b).comp
    (CFSG.QuasithinUnique.Setup.X7a.frobPow F j)
  obtain ⟨P₃, Q₃, h₃⟩ := tensorRep_comp_frobPow (F := F) F hF j a b
  have heq : (tensorRep (F := F) F a b).comp (stdAut M σ 0).toMonoidHom =
      ((tensorRep (F := F) F a b).comp (slConjugation 3 F M).toMonoidHom).comp
        (CFSG.QuasithinUnique.Setup.X7a.frobPow F j) := by
    refine MonoidHom.ext fun x => ?_
    show tensorRep (F := F) F a b (stdAut M σ 0 x) =
      tensorRep (F := F) F a b (slConjugation 3 F M (CFSG.QuasithinUnique.Setup.X7a.frobPow F j x))
    congr 1
    simp only [stdAut, pow_zero, mul_one, MulAut.mul_apply]
    congr 1
    apply Subtype.ext
    rw [CFSG.QuasithinUnique.Setup.X7Sec.frobPow_coe]
    ext i k
    show σ ((x : Matrix (Fin 3) (Fin 3) F) i k) = (x : Matrix (Fin 3) (Fin 3) F) i k ^ 2 ^ j
    exact hσ _
  rw [heq]
  exact ⟨_, _, h₁.trans h₃⟩

theorem not_equiv_comp_of_shift_ne (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f)
    (M : GL (Fin 3) F) (σ : F ≃+* F) {j : ℕ} (hσ : ∀ x, σ x = x ^ 2 ^ j) (a b : Fin f → Bool)
    (hne : ¬ ((shiftBits f)^[j] a = a ∧ (shiftBits f)^[j] b = b)) :
    ¬ Nonempty ((matRep (tensorRep (F := F) F a b)).Equiv
      (matRep ((tensorRep (F := F) F a b).comp (stdAut M σ 0).toMonoidHom))) := by
  rintro ⟨e⟩
  obtain ⟨P, Q, h⟩ := exists_matIso_comp_stdAut hF M σ hσ a b
  obtain ⟨e'⟩ := h.equiv
  have := (tensorRep_absolutely_irreducible_and_distinct F hF hf).2 _ _ _ _ ⟨e.trans e'⟩
  exact hne ⟨this.1.symm, this.2.symm⟩

omit [CharP F 2] in
theorem shift_ne_of_card_eq (hF : Fintype.card F = 2 ^ f) (a b : Fin f → Bool)
    (hcard : (pairOrbit f (a, b)).card = f) {σ : F ≃+* F} (hσ1 : σ ≠ 1) {j : ℕ}
    (hσ : ∀ x, σ x = x ^ 2 ^ j) :
    ¬ ((shiftBits f)^[j] a = a ∧ (shiftBits f)^[j] b = b) := by
  intro h
  have hf0 : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · subst h0
      have := Fintype.one_lt_card (α := F)
      rw [hF] at this
      norm_num at this
    · exact h0
  rw [shiftBits_iterate_mod j a, shiftBits_iterate_mod j b] at h
  by_cases hr : 1 ≤ j % f
  · have hle := card_pairOrbit_le_of_fixed (a, b) hr h
    have hlt : j % f < f := Nat.mod_lt j hf0
    omega
  · have hdvd : j = f * (j / f) := by
      have := Nat.mod_add_div j f
      omega
    apply hσ1
    refine RingEquiv.ext fun x => ?_
    rw [hσ, hdvd]
    show x ^ 2 ^ (f * (j / f)) = x
    induction j / f with
    | zero => simp
    | succ q ih =>
      rw [Nat.mul_succ, pow_add, pow_mul, ih, ← hF, FiniteField.pow_card]

end Field

end B45SL3

end CFSG.Quasithin
