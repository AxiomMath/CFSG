module

public import CFSG.Quasithin.Background.F918V2Defs2
public import CFSG.Quasithin.Background.SmithB51LnModel
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.Z391

open CFSG.Assembly.LowTwoRank CFSG.Quasithin.B5.Ln Matrix
open scoped Matrix

section Model

variable {n : ℕ}

theorem v2gd_dmat_injective : Function.Injective (dmat (n := n)) := by
  intro g h hgh
  have h1 : mat g⁻¹ = mat h⁻¹ := by
    have := congrArg Matrix.transpose hgh
    rwa [dmat, dmat, transpose_transpose, transpose_transpose] at this
  exact inv_injective (mat_injective h1)

theorem v2gd_eq_of_mulVec_eq {M₀ : ↥(StatedSL n (ZMod 2)) → Matrix (Fin n) (Fin n) (ZMod 2)}
    (hM : M₀ = mat ∨ M₀ = dmat) {g h : ↥(StatedSL n (ZMod 2))}
    (hgh : ∀ x, M₀ g *ᵥ x = M₀ h *ᵥ x) : g = h := by
  rcases hM with rfl | rfl
  · exact eq_of_mulVec_eq hgh
  · exact v2gd_dmat_injective (Matrix.toLin'.injective (LinearMap.ext hgh))

theorem v2gd_schur_core {M₀ : ↥(StatedSL n (ZMod 2)) → Matrix (Fin n) (Fin n) (ZMod 2)}
    (hM : M₀ = mat ∨ M₀ = dmat) (φ : (Fin n → ZMod 2) →+ (Fin n → ZMod 2)) (hφ0 : φ ≠ 0)
    (h : ∀ g x, φ (M₀ g *ᵥ x) = M₀ g *ᵥ φ x) : ∀ x, φ x = x := by
  have hB : ∀ g : ↥(StatedSL n (ZMod 2)), ∃ g', M₀ g' = mat g := by
    rcases hM with rfl | rfl
    · exact fun g => ⟨g, rfl⟩
    · intro g
      obtain ⟨g', hg'⟩ := exists_dmat_eq (g : GL (Fin n) (ZMod 2))
      exact ⟨g', hg'⟩
  obtain ⟨P, hP1, hP2⟩ := exists_conj_of_intertwine hφ0 hB h
  have hP : (P : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := by
    rcases hM with rfl | rfl
    · have hz : ∀ g : ↥(StatedSL n (ZMod 2)), ofGL P * g = g * ofGL P := fun g =>
        mat_injective (by rw [mat_mul, mat_mul, mat_ofGL, hP2 g])
      have h1 := congrArg mat (eq_one_of_forall_commute hz)
      rwa [mat_ofGL, mat_one] at h1
    · obtain ⟨g₀, hg₀⟩ := exists_dmat_eq P
      have hz : ∀ g : ↥(StatedSL n (ZMod 2)), g₀ * g = g * g₀ := fun g =>
        v2gd_dmat_injective (by rw [dmat_mul, dmat_mul, hg₀, hP2 g])
      rw [← hg₀, eq_one_of_forall_commute hz, dmat_one]
  intro x
  rw [← hP1, hP, one_mulVec]

theorem v2gd_model_end (hn : 1 ≤ n)
    {M₀ : ↥(StatedSL n (ZMod 2)) → Matrix (Fin n) (Fin n) (ZMod 2)} (hM : M₀ = mat ∨ M₀ = dmat)
    (f : Multiplicative (Fin n → ZMod 2) ≃* Multiplicative (Fin n → ZMod 2))
    (h : ∀ g x, f (Multiplicative.ofAdd (M₀ g *ᵥ Multiplicative.toAdd x)) =
      Multiplicative.ofAdd (M₀ g *ᵥ Multiplicative.toAdd (f x))) : f = MulEquiv.refl _ := by
  set φ : (Fin n → ZMod 2) →+ (Fin n → ZMod 2) := AddMonoidHom.toMultiplicative.symm f.toMonoidHom
    with hφ
  have hφapp : ∀ x, φ x = Multiplicative.toAdd (f (Multiplicative.ofAdd x)) := fun x => rfl
  have hφ0 : φ ≠ 0 := by
    intro h0
    have hx : (Pi.single ⟨0, by omega⟩ 1 : Fin n → ZMod 2) ≠ 0 := by
      intro h'
      have := congrFun h' ⟨0, by omega⟩
      simp at this
    apply hx
    have h1 := hφapp (Pi.single ⟨0, by omega⟩ 1)
    rw [h0, AddMonoidHom.zero_apply] at h1
    have h2 : f (Multiplicative.ofAdd (Pi.single ⟨0, by omega⟩ 1)) = f 1 := by
      rw [map_one]
      exact Multiplicative.toAdd.injective h1.symm
    exact Multiplicative.ofAdd.injective (f.injective h2)
  have hφx := v2gd_schur_core hM φ hφ0 fun g x =>
    congrArg Multiplicative.toAdd (h g (Multiplicative.ofAdd x))
  exact MulEquiv.ext fun x => Multiplicative.toAdd.injective (hφx (Multiplicative.toAdd x))

theorem v2gd_model_aut {M₀ : ↥(StatedSL n (ZMod 2)) → Matrix (Fin n) (Fin n) (ZMod 2)}
    (hM : M₀ = mat ∨ M₀ = dmat)
    (f : Multiplicative (Fin n → ZMod 2) ≃* Multiplicative (Fin n → ZMod 2)) :
    ∃ g : ↥(StatedSL n (ZMod 2)),
      ∀ x, f x = Multiplicative.ofAdd (M₀ g *ᵥ Multiplicative.toAdd x) := by
  set φ : (Fin n → ZMod 2) →+ (Fin n → ZMod 2) := AddMonoidHom.toMultiplicative.symm f.toMonoidHom
    with hφ
  have hφapp : ∀ x, φ x = Multiplicative.toAdd (f (Multiplicative.ofAdd x)) := fun x => rfl
  have hinj : Function.Injective φ := fun a b hab =>
    Multiplicative.ofAdd.injective (f.injective (Multiplicative.toAdd.injective (by
      rw [← hφapp, ← hφapp]
      exact hab)))
  have hsurj : Function.Surjective φ := fun y => by
    obtain ⟨x, hx⟩ := f.surjective (Multiplicative.ofAdd y)
    refine ⟨Multiplicative.toAdd x, ?_⟩
    rw [hφapp, ofAdd_toAdd, hx, toAdd_ofAdd]
  set ψ := AddMonoidHom.toZModLinearMap 2 φ with hψ
  have hP₀ : ∀ x, LinearMap.toMatrix' ψ *ᵥ x = φ x := fun x => by
    rw [LinearMap.toMatrix'_mulVec]
    rfl
  have hu : IsUnit (LinearMap.toMatrix' ψ) := by
    rw [Matrix.isUnit_iff_isUnit_det, LinearMap.det_toMatrix']
    exact LinearEquiv.isUnit_det' (LinearEquiv.ofBijective ψ ⟨hinj, hsurj⟩)
  set P : GL (Fin n) (ZMod 2) := hu.unit with hPdef
  have hP : ∀ x, (P : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x = φ x := fun x => by
    rw [hPdef, IsUnit.unit_spec, hP₀]
  have key : ∀ x, f x = Multiplicative.ofAdd
      ((P : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ Multiplicative.toAdd x) := fun x => by
    rw [hP, hφapp, ofAdd_toAdd, ofAdd_toAdd]
  rcases hM with rfl | rfl
  · exact ⟨ofGL P, fun x => by rw [key, mat_ofGL]⟩
  · obtain ⟨g, hg⟩ := exists_dmat_eq P
    exact ⟨g, fun x => by rw [key, hg]⟩

end Model

section NatRep

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

@[expose] def V2gdNatRep (Λ : Subgroup Γ) (P : Subgroup Q) (n : ℕ)
    (M₀ : ↥(StatedSL n (ZMod 2)) → Matrix (Fin n) (Fin n) (ZMod 2))
    (σ : ↥Λ →* ↥(StatedSL n (ZMod 2))) : Prop :=
  (∀ l : ↥Λ, ∀ p ∈ P, l • p ∈ P) ∧
    ∃ β : ↥P ≃* Multiplicative (Fin n → ZMod 2), ∀ (l : ↥Λ) (p : ↥P) (hp : l • (p : Q) ∈ P),
      Multiplicative.toAdd (β ⟨l • (p : Q), hp⟩) = M₀ (σ l) *ᵥ Multiplicative.toAdd (β p)

variable {Λ : Subgroup Γ} {P : Subgroup Q} {n : ℕ}
  {M₀ : ↥(StatedSL n (ZMod 2)) → Matrix (Fin n) (Fin n) (ZMod 2)}
  {σ : ↥Λ →* ↥(StatedSL n (ZMod 2))}

theorem v2gd_endUnitsTrivial (hn : 1 ≤ n) (hM : M₀ = mat ∨ M₀ = dmat)
    (hσ : Function.Surjective σ) (hP : V2gdNatRep Λ P n M₀ σ) : EndUnitsTrivial Λ P := by
  obtain ⟨hinv, β, hβ⟩ := hP
  intro φ hφ
  let f : Multiplicative (Fin n → ZMod 2) ≃* Multiplicative (Fin n → ZMod 2) :=
    β.symm.trans (φ.trans β)
  have hfβ : ∀ p : ↥P, f (β p) = β (φ p) := fun p => by simp [f]
  have hf : ∀ g x, f (Multiplicative.ofAdd (M₀ g *ᵥ Multiplicative.toAdd x)) =
      Multiplicative.ofAdd (M₀ g *ᵥ Multiplicative.toAdd (f x)) := by
    intro g x
    obtain ⟨l, rfl⟩ := hσ g
    obtain ⟨p, rfl⟩ := β.surjective x
    have hlp : l • (p : Q) ∈ P := hinv l p p.2
    have hlφ : l • ((φ p : ↥P) : Q) ∈ P := hinv l _ (φ p).2
    have e1 : Multiplicative.ofAdd (M₀ (σ l) *ᵥ Multiplicative.toAdd (β p)) =
        β ⟨l • (p : Q), hlp⟩ := by
      rw [← hβ l p hlp, ofAdd_toAdd]
    have e2 : φ ⟨l • (p : Q), hlp⟩ = ⟨l • ((φ p : ↥P) : Q), hlφ⟩ :=
      Subtype.ext (hφ l p ⟨l • (p : Q), hlp⟩ rfl).symm
    rw [e1, hfβ, e2, hfβ, ← ofAdd_toAdd (β ⟨l • ((φ p : ↥P) : Q), hlφ⟩), hβ l (φ p) hlφ]
  have hf1 := v2gd_model_end hn hM f hf
  refine MulEquiv.ext fun p => β.injective ?_
  rw [← hfβ, hf1]
  rfl

theorem v2gd_autFromGroup (hM : M₀ = mat ∨ M₀ = dmat) (hσ : Function.Surjective σ)
    (hP : V2gdNatRep Λ P n M₀ σ) : AutFromGroup Λ P := by
  obtain ⟨hinv, β, hβ⟩ := hP
  intro h
  let f : Multiplicative (Fin n → ZMod 2) ≃* Multiplicative (Fin n → ZMod 2) :=
    β.symm.trans (h.trans β)
  have hfβ : ∀ p : ↥P, f (β p) = β (h p) := fun p => by simp [f]
  obtain ⟨g, hg⟩ := v2gd_model_aut hM f
  obtain ⟨l, rfl⟩ := hσ g
  refine ⟨(l : Γ), l.2, fun x => ?_⟩
  have hlp : l • (x : Q) ∈ P := hinv l x x.2
  have : h x = ⟨l • (x : Q), hlp⟩ := by
    apply β.injective
    rw [← hfβ, hg, ← hβ l x hlp, ofAdd_toAdd]
  rw [this]
  rfl

theorem v2gd_faithfulOn (hM : M₀ = mat ∨ M₀ = dmat) (hσ : Function.Injective σ)
    (hP : V2gdNatRep Λ P n M₀ σ) : FaithfulOn Λ P := by
  obtain ⟨hinv, β, hβ⟩ := hP
  intro l hl hfix
  have hall : ∀ x, M₀ (σ ⟨l, hl⟩) *ᵥ x = x := by
    intro x
    obtain ⟨p, hp⟩ := β.surjective (Multiplicative.ofAdd x)
    have h1 := hβ ⟨l, hl⟩ p (hinv ⟨l, hl⟩ p p.2)
    have h2 : (⟨(⟨l, hl⟩ : ↥Λ) • (p : Q), hinv ⟨l, hl⟩ p p.2⟩ : ↥P) = p :=
      Subtype.ext (hfix p p.2)
    rw [h2, hp] at h1
    exact h1.symm
  have h3 : σ ⟨l, hl⟩ = σ 1 := v2gd_eq_of_mulVec_eq hM fun x => by
    rw [hall, map_one]
    rcases hM with rfl | rfl
    · rw [mat_one, one_mulVec]
    · rw [dmat_one, one_mulVec]
  exact congrArg Subtype.val (hσ h3)

end NatRep

end CFSG.Quasithin.Z391
