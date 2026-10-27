module

public import CFSG.Quasithin.Background.C124YLA7Woff
public import CFSG.Quasithin.Background.C124YLInd
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C123Alt7B

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

public section

namespace CFSG.Quasithin.C124.YL.A7

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique.L246.C123

theorem card_range_rhoA
    (α : ↥(alternatingGroup (Fin 8)) ≃* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) :
    Nat.card ↥(rhoA α).range = 2520 := by
  rw [← card_A7]
  exact (Nat.card_congr (MonoidHom.ofInjective (rhoA_injective α)).toEquiv).symm

section Ind

variable {W : Type*} [CommGroup W] {U Z : Subgroup W} {c : ↥U →* Q7} (hc : IsCoord U Z c)
  (Xs : Subgroup (MulAut W)) (hU : ∀ x ∈ Xs, ∀ u, u ∈ U ↔ x u ∈ U)
  (hZ : ∀ x ∈ Xs, ∀ z, z ∈ Z ↔ x z ∈ Z)

theorem indHom_inv_apply (x : ↥Xs) (q : Q7) :
    indHom hc Xs hU hZ x⁻¹ (indHom hc Xs hU hZ x q) = q := by
  have h : indHom hc Xs hU hZ x⁻¹ * indHom hc Xs hU hZ x = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  exact congrArg (fun f : Monoid.End Q7 => f q) h

theorem indHom_apply_inv (x : ↥Xs) (q : Q7) :
    indHom hc Xs hU hZ x (indHom hc Xs hU hZ x⁻¹ q) = q := by
  have h : indHom hc Xs hU hZ x * indHom hc Xs hU hZ x⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  exact congrArg (fun f : Monoid.End Q7 => f q) h

@[expose] noncomputable def indAut : ↥Xs →* MulAut Q7 where
  toFun x :=
    { toFun := fun q => indHom hc Xs hU hZ x q
      invFun := fun q => indHom hc Xs hU hZ x⁻¹ q
      left_inv := fun q => indHom_inv_apply hc Xs hU hZ x q
      right_inv := fun q => indHom_apply_inv hc Xs hU hZ x q
      map_mul' := fun a b => map_mul (indHom hc Xs hU hZ x) a b }
  map_one' := MulEquiv.ext fun q => congrArg (fun f : Monoid.End Q7 => f q)
    (map_one (indHom hc Xs hU hZ))
  map_mul' x y := MulEquiv.ext fun q => congrArg (fun f : Monoid.End Q7 => f q)
    (map_mul (indHom hc Xs hU hZ) x y)

end Ind

namespace A7Ctx

variable {W : Type*} [CommGroup W] [Finite W] {Ls : Subgroup (MulAut W)} {U Z : Subgroup W}
  (C : A7Ctx Ls U Z)

include C in
theorem le_Ls_of_normalizes {Xs : Subgroup (MulAut W)} (hLX : Ls ≤ Xs)
    (hnorm : ∀ x ∈ Xs, x ∈ Subgroup.normalizer (Ls : Set (MulAut W)))
    (hF : quasithinGenFitting Xs = Ls)
    (hU : ∀ x ∈ Xs, ∀ u, u ∈ U ↔ x u ∈ U) (hZ : ∀ x ∈ Xs, ∀ z, z ∈ Z ↔ x z ∈ Z) :
    Xs ≤ Ls := by
  obtain ⟨c, hc, hequiv⟩ := C.coord
  have hρ := rhoA_injective C.α
  have hind : ∀ σ : A7, indAut hc Xs hU hZ ⟨C.phi σ, hLX (C.phi_mem σ)⟩ = rhoA C.α σ := by
    intro σ
    refine MulEquiv.ext fun q => ?_
    obtain ⟨u, rfl⟩ := hc.surj q
    exact (indHom_apply hc Xs hU hZ _ u).trans (hequiv σ u (C.phi_stab σ u u.2))
  have hLfaith : ∀ l : ↥Ls, indHom hc Xs hU hZ ⟨l, hLX l.2⟩ = 1 → l = 1 := by
    intro l hl
    obtain ⟨σ, hσ⟩ : (l : MulAut W) ∈ C.phi.range := C.phi_range.ge l.2
    have e : (⟨C.phi σ, hLX (C.phi_mem σ)⟩ : ↥Xs) = ⟨l, hLX l.2⟩ := Subtype.ext hσ
    have h1 : rhoA C.α σ = 1 := by
      rw [← hind σ, e]
      exact MulEquiv.ext fun q => congrArg (fun f : Monoid.End Q7 => f q) hl
    have hσ1 : σ = 1 := hρ (by rw [h1, map_one])
    apply Subtype.ext
    rw [← hσ, hσ1, map_one]
    rfl
  have key : ∀ (y : MulAut W) (hy : y ∈ Xs) (σ : A7), ∃ σ' : A7,
      indAut hc Xs hU hZ ⟨y, hy⟩ * rhoA C.α σ * (indAut hc Xs hU hZ ⟨y, hy⟩)⁻¹ = rhoA C.α σ' := by
    intro y hy σ
    have hyL : y * C.phi σ * y⁻¹ ∈ Ls :=
      (Subgroup.mem_normalizer_iff.1 (hnorm y hy) _).1 (C.phi_mem σ)
    obtain ⟨σ', hσ'⟩ : y * C.phi σ * y⁻¹ ∈ C.phi.range := C.phi_range.ge hyL
    refine ⟨σ', ?_⟩
    have e : (⟨y, hy⟩ : ↥Xs) * ⟨C.phi σ, hLX (C.phi_mem σ)⟩ * (⟨y, hy⟩ : ↥Xs)⁻¹ =
        ⟨C.phi σ', hLX (C.phi_mem σ')⟩ := Subtype.ext hσ'.symm
    rw [← hind σ, ← hind σ', ← e, map_mul, map_mul, map_inv]
  intro x hx
  set t : MulAut Q7 := indAut hc Xs hU hZ ⟨x, hx⟩ with ht
  have htnorm : t ∈ Subgroup.normalizer ((rhoA C.α).range : Set (MulAut Q7)) := by
    refine Subgroup.mem_normalizer_iff.2 fun h => ⟨?_, ?_⟩
    · rintro ⟨σ, rfl⟩
      obtain ⟨σ', hσ'⟩ := key x hx σ
      exact ⟨σ', hσ'.symm⟩
    · rintro ⟨σ', hσ'⟩
      have hx' : x⁻¹ ∈ Xs := Xs.inv_mem hx
      obtain ⟨σ'', hσ''⟩ := key x⁻¹ hx' σ'
      have hinv : indAut hc Xs hU hZ ⟨x⁻¹, hx'⟩ = t⁻¹ := by
        have : (⟨x⁻¹, hx'⟩ : ↥Xs) = (⟨x, hx⟩ : ↥Xs)⁻¹ := rfl
        rw [this, map_inv]
      rw [hinv, hσ'] at hσ''
      have h2 : t⁻¹ * (t * h * t⁻¹) * t⁻¹⁻¹ = h := by group
      exact ⟨σ'', hσ''.symm.trans h2⟩
  have htin : t ∈ (rhoA C.α).range :=
    (normalizer_eq_of_card_2520 sq_Q7 card_Q7 (card_range_rhoA C.α)).le htnorm
  obtain ⟨σ, hσ⟩ := htin
  have hyX : (C.phi σ)⁻¹ * x ∈ Xs := Xs.mul_mem (Xs.inv_mem (hLX (C.phi_mem σ))) hx
  have hy1 : indHom hc Xs hU hZ ⟨(C.phi σ)⁻¹ * x, hyX⟩ = 1 := by
    have e : (⟨(C.phi σ)⁻¹ * x, hyX⟩ : ↥Xs) =
        (⟨C.phi σ, hLX (C.phi_mem σ)⟩ : ↥Xs)⁻¹ * ⟨x, hx⟩ := rfl
    have h1 : indAut hc Xs hU hZ ((⟨C.phi σ, hLX (C.phi_mem σ)⟩ : ↥Xs)⁻¹ * ⟨x, hx⟩) = 1 := by
      rw [map_mul, map_inv, hind σ, hσ, inv_mul_cancel]
    rw [e]
    exact MonoidHom.ext fun q => congrArg (fun f : MulAut Q7 => f q) h1
  have h3 := faithful_of_fstar hc hLX hnorm hF hU hZ hLfaith ⟨(C.phi σ)⁻¹ * x, hyX⟩ hy1
  have h4 : (C.phi σ)⁻¹ * x = 1 := congrArg Subtype.val h3
  have h5 : x = C.phi σ := by
    have := congrArg (fun z => C.phi σ * z) h4
    simpa using this
  rw [h5]
  exact C.phi_mem σ

end A7Ctx

end CFSG.Quasithin.C124.YL.A7
