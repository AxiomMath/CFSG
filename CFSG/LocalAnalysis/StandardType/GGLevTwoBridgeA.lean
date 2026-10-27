module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoRoots
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMPrimeInputs
import CFSG.LocalAnalysis.StandardType.GGLevTwoS4aAuxA

public section

namespace CFSG.StandardType.LevTwo

open CFSG CFSG.Assembly CFSG.LieType.RootSystem LevTwoType

section Bridge

variable {G : Type} [Group G] [Finite G]

theorem levTwoPairModel (T : LevTwoType) (hT : T.Valid) (p : ℕ) (Bs : Subgroup G)
    (hp : p.Prime) (hp2 : p ≠ 2) (hEl : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs)
    (A : Subgroup (MulAut ↥Bs)) (hA : A ≤ ggInduced ⊤ Bs)
    (f : T.coxeter.Group ≃* ↥A)
    (hf : ∀ i : Fin T.n, GGIsReflection p ((f (T.coxeter.simple i) : ↥A) : MulAut ↥Bs))
    (x : ↥Bs) :
    ∃ (c : Fin T.n → ZMod p) (ρ : Wg T.rootFT ≃* ↥A),
      (∀ a : MulAut ↥Bs, (a ∈ A ∧ GGIsReflection p a) ↔
        ∃ g ∈ Refl T.rootFT, ((ρ g : ↥A) : MulAut ↥Bs) = a) ∧
      (∀ β, IsRt T.rootFT β →
        (((ρ (rRefl T.rootFT β) : ↥A) : MulAut ↥Bs) x = x ↔ lam c β = 0)) ∧
      (∀ m : ℕ, Nat.card ↥Bs ≤ p ^ m → Matrix.rank (T.pair.map (Int.castRingHom (ZMod p))) ≤ m) := by
  have : Fact p.Prime := ⟨hp⟩
  have _ := hT
  obtain ⟨hC, hent, htree⟩ := levTwoS4a_data T hT
  have hCtrans : GGIntCartan T.coxeter (Matrix.transpose T.pair) :=
    levTwoS4a_ggIntCartan_transpose hC
  have hcoex : coxeterMatrix T.rootFT = T.coxeter :=
    coxeterMatrix_eq_of_ggIntCartan T.rootFT hCtrans
  obtain ⟨V, iadd, imod, ⟨ιV⟩⟩ := exists_ggLinData (p := p) hEl
  let _ : AddCommGroup V := iadd
  let _ : Module (ZMod p) V := imod
  have : Finite V := Finite.of_equiv (Additive ↥Bs) ιV.toEquiv
  obtain ⟨hh, α, hα, hrefl, hP⟩ :=
    SecFiveRootRefl.exists_cartan_pairing_of_iso (p := p) hp2 hNT hC hent htree f hf
      (fun φ hφ => hA hφ) ιV
  let castρ : Wg T.rootFT ≃* T.coxeter.Group := MulEquiv.cast hcoex
  let ρ : Wg T.rootFT ≃* ↥A := castρ.trans f
  have hρsimple : ∀ i : Fin T.n, ρ (sg T.rootFT i) = f (T.coxeter.simple i) := by
    intro i
    show castρ.trans f (sg T.rootFT i) = f (T.coxeter.simple i)
    rw [MulEquiv.trans_apply]
    change f ((MulEquiv.cast hcoex) ((coxeterMatrix T.rootFT).simple i)) =
      f (T.coxeter.simple i)
    rw [levTwoS4a_cast_simple hcoex i]
  let R : Wg T.rootFT →* (V ≃ₗ[ZMod p] V) :=
    (ggLin (p := p) ιV).comp ((Subgroup.subtype A).comp ρ.toMonoidHom)
  have hRsimple : ∀ i : Fin T.n, R (sg T.rootFT i) = Module.reflection (hα i) := by
    intro i
    show ggLin (p := p) ιV (((ρ (sg T.rootFT i) : ↥A) : MulAut ↥Bs)) = Module.reflection (hα i)
    rw [show ((ρ (sg T.rootFT i) : ↥A) : MulAut ↥Bs) =
        ((f (T.coxeter.simple i) : ↥A) : MulAut ↥Bs) from
      congrArg (fun z : ↥A => (z : MulAut ↥Bs)) (hρsimple i)]
    exact hrefl i
  let xv : V := ιV (Additive.ofMul x)
  let c : Fin T.n → ZMod p := fun j => α j xv
  refine ⟨c, ρ, ?_, ?_, ?_⟩
  · intro a
    constructor
    · rintro ⟨haA, haR⟩
      obtain ⟨i, g, hgi⟩ :=
        SecFiveRootRefl.rootRefl_of_cartan (p := p) hp2 hNT hC T.pairFT hent htree
          (fun φ hφ => hA hφ) f hf ιV ⟨a, haA⟩ haR
      refine ⟨castρ.symm (g * T.coxeter.simple i * g⁻¹), ?_, ?_⟩
      · have hw : castρ.symm (g * T.coxeter.simple i * g⁻¹) =
            castρ.symm g * sg T.rootFT i * (castρ.symm g)⁻¹ := by
          rw [map_mul, map_mul, map_inv, levTwoS4a_cast_symm_simple hcoex i]
          rfl
        rw [hw]
        exact ⟨castρ.symm g, i, rfl⟩
      · have hρg : ρ (castρ.symm (g * T.coxeter.simple i * g⁻¹)) = ⟨a, haA⟩ := by
          show f (castρ (castρ.symm (g * T.coxeter.simple i * g⁻¹))) = ⟨a, haA⟩
          rw [MulEquiv.apply_symm_apply, ← hgi]
        exact congrArg (fun z : ↥A => (z : MulAut ↥Bs)) hρg
    · rintro ⟨g, hg, hga⟩
      rw [← hga]
      obtain ⟨w, i, rfl⟩ := hg
      constructor
      · exact (ρ (w * sg T.rootFT i * w⁻¹)).2
      · have hconj : ((ρ (w * sg T.rootFT i * w⁻¹) : ↥A) : MulAut ↥Bs) =
            ((ρ w : ↥A) : MulAut ↥Bs) * ((ρ (sg T.rootFT i) : ↥A) : MulAut ↥Bs) *
              (((ρ w : ↥A) : MulAut ↥Bs))⁻¹ := by
          simp only [map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
        rw [hconj]
        refine (levTwoS4a_isReflection_conj (((ρ w : ↥A) : MulAut ↥Bs))
          (((ρ (sg T.rootFT i) : ↥A) : MulAut ↥Bs))).mpr ?_
        rw [show ((ρ (sg T.rootFT i) : ↥A) : MulAut ↥Bs) =
            ((f (T.coxeter.simple i) : ↥A) : MulAut ↥Bs) from
          congrArg (fun z : ↥A => (z : MulAut ↥Bs)) (hρsimple i)]
        exact hf i
  · intro β hβ
    obtain ⟨w, j, hwj⟩ := hβ
    rw [rRefl_eq_conj T.rootFT hwj]
    have hlin : (((ρ (w * sg T.rootFT j * w⁻¹) : ↥A) : MulAut ↥Bs) x = x) ↔
        ggLin (p := p) ιV ((ρ (w * sg T.rootFT j * w⁻¹) : ↥A) : MulAut ↥Bs) xv = xv := by
      simpa [xv] using
        (ggLin_fix_iff (p := p) ιV ((ρ (w * sg T.rootFT j * w⁻¹) : ↥A) : MulAut ↥Bs) x)
    have hell_single : ∀ i : Fin T.n, levTwoS4a_ell α (Pi.single i (1 : ℤ)) = α i := by
      intro i
      simp [levTwoS4a_ell, Pi.single_apply]
    have hdual := congrArg (fun L : Module.Dual (ZMod p) V => L xv)
      (levTwoS4a_ell_weylAction (p := p) (V := V) (A := T.root) (hA := T.rootFT)
        (C := T.pair) (hAC := rfl) (h := hh) (α := α) hα hP R hRsimple w
        (Pi.single j (1 : ℤ)))
    have hdual' := congrArg (fun v => (levTwoS4a_ell α v) xv) hwj
    have hellβ : levTwoS4a_ell α β xv = α j ((R w)⁻¹ xv) := by
      rw [← hdual']
      simpa [LinearMap.comp_apply, hell_single] using hdual
    have hlam : lam c β = levTwoS4a_ell α β xv := by
      simp only [lam, levTwoS4a_ell, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
        c, xv]
    have hj0 : hh j ≠ 0 := by
      intro h0
      have h2 := hα j
      rw [h0, map_zero] at h2
      exact (zmod_two_ne_zero hp2) h2.symm
    have hrefl_fix : ∀ v : V, Module.reflection (hα j) v = v ↔ α j v = 0 := by
      intro v
      rw [Module.reflection_apply, sub_eq_self, smul_eq_zero]
      exact ⟨fun h => h.resolve_right hj0, fun h => Or.inl h⟩
    have hact : ggLin (p := p) ιV ((ρ (w * sg T.rootFT j * w⁻¹) : ↥A) : MulAut ↥Bs) xv = xv ↔
        α j ((R w)⁻¹ xv) = 0 := by
      have hR : R (w * sg T.rootFT j * w⁻¹) =
          R w * Module.reflection (hα j) * (R w)⁻¹ := by
        rw [map_mul, map_mul, map_inv, hRsimple j]
      rw [show ggLin (p := p) ιV ((ρ (w * sg T.rootFT j * w⁻¹) : ↥A) : MulAut ↥Bs) =
          R (w * sg T.rootFT j * w⁻¹) from rfl, hR]
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
      constructor
      · intro h
        have h' := congrArg (fun z => (R w)⁻¹ z) h
        have : Module.reflection (hα j) ((R w)⁻¹ xv) = (R w)⁻¹ xv := by
          simpa using h'
        exact (hrefl_fix ((R w)⁻¹ xv)).mp this
      · intro h
        have : Module.reflection (hα j) ((R w)⁻¹ xv) = (R w)⁻¹ xv :=
          (hrefl_fix ((R w)⁻¹ xv)).mpr h
        rw [this]
        exact LinearEquiv.apply_symm_apply (R w) xv
    simp only [hlin, hact, ← hellβ, hlam]
  · intro m hm
    have hrank := levTwoS4a_rank_core (p := p) (V := V) (C := T.pair) (h := hh) (α := α) hP
    have hcardV : Nat.card V = p ^ Module.finrank (ZMod p) V := by
      have : Fintype V := Fintype.ofFinite V
      rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p), ZMod.card p]
    have hcard : Nat.card ↥Bs = p ^ Module.finrank (ZMod p) V := by
      rw [card_eq_of_ggLin ιV, hcardV]
    have hm' : p ^ Module.finrank (ZMod p) V ≤ p ^ m := by
      rw [← hcard]; exact hm
    have hfin : Module.finrank (ZMod p) V ≤ m :=
      (Nat.pow_le_pow_iff_right hp.one_lt).mp hm'
    exact le_trans hrank hfin

end Bridge

end CFSG.StandardType.LevTwo
