module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeCompanion1632Lang
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcRoots
public import CFSG.RankThree.PartOne.Q1327T.Item7D4W
public import CFSG.RankThree.PartOne.KE.CTLangData

public section

namespace CFSG.StandardType.S2MathAs1E6Companion1625

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.StandardType.E6Centralizer1585
open CFSG.StandardType.GGK0MarkedKacIface1587
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private noncomputable def ltrb1f0a_frobHom {Omega : Type} [Field Omega] [IsAlgClosed Omega]
    [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi) :
    (Fin ρ.tau.rank → ℤ) →+ (Fin ρ.tau.rank → ℤ) where
  toFun := fun v => ρ.frobLinear v
  map_zero' := ρ.frobLinear.map_zero
  map_add' := fun a b => ρ.frobLinear.map_add a b

private theorem ltrb1f0a_rho_add {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    {p : ℕ} (S : LangSetup τ L p) (x y : Fin τ.rank → ℤ) :
    S.ρ (x + y) = S.ρ x + S.ρ y := by
  have hρform := S.frob.iform_eq
  by_contra hne
  have hd : S.ρ (x + y) - S.ρ x - S.ρ y ≠ 0 := by
    intro h
    apply hne
    have h' : S.ρ (x + y) - (S.ρ x + S.ρ y) = 0 := by
      simpa only [sub_sub] using h
    exact sub_eq_zero.mp h'
  have hpos := CFSG.LieType.Steinberg.Adjoint.iform_self_pos hd
  have hR := CFSG.LieType.Steinberg.Adjoint.iform_add_right (x + y) x y
  have hP : CFSG.LieType.Steinberg.Adjoint.iform (x + y) x =
      CFSG.LieType.Steinberg.Adjoint.iform x x +
        CFSG.LieType.Steinberg.Adjoint.iform x y := by
    rw [CFSG.LieType.Steinberg.Adjoint.iform_add_left,
      CFSG.LieType.Steinberg.Adjoint.iform_comm y x]
  have hQ : CFSG.LieType.Steinberg.Adjoint.iform (x + y) y =
      CFSG.LieType.Steinberg.Adjoint.iform x y +
        CFSG.LieType.Steinberg.Adjoint.iform y y := by
    rw [CFSG.LieType.Steinberg.Adjoint.iform_add_left]
  have hzero : CFSG.LieType.Steinberg.Adjoint.iform
      (S.ρ (x + y) - S.ρ x - S.ρ y) (S.ρ (x + y) - S.ρ x - S.ρ y) = 0 := by
    have hexp : CFSG.LieType.Steinberg.Adjoint.iform
        (S.ρ (x + y) - S.ρ x - S.ρ y) (S.ρ (x + y) - S.ρ x - S.ρ y)
        = CFSG.LieType.Steinberg.Adjoint.iform (x + y) (x + y)
          + CFSG.LieType.Steinberg.Adjoint.iform x x
          + CFSG.LieType.Steinberg.Adjoint.iform y y
          - 2 * CFSG.LieType.Steinberg.Adjoint.iform (x + y) x
          - 2 * CFSG.LieType.Steinberg.Adjoint.iform (x + y) y
          + 2 * CFSG.LieType.Steinberg.Adjoint.iform x y := by
      simp only [CFSG.LieType.Steinberg.Adjoint.iform_sub_left,
        CFSG.LieType.Steinberg.Adjoint.iform_sub_right, hρform]
      rw [CFSG.LieType.Steinberg.Adjoint.iform_comm x (x + y),
        CFSG.LieType.Steinberg.Adjoint.iform_comm y (x + y),
        CFSG.LieType.Steinberg.Adjoint.iform_comm y x]
      ring
    rw [hexp, hR, hP, hQ]
    ring
  exact absurd hpos (by rw [hzero]; exact lt_irrefl 0)

private noncomputable def ltrb1f0a_rhoAddHom {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    {p : ℕ} (S : LangSetup τ L p) :
    (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ) :=
  AddMonoidHom.mk' S.ρ (ltrb1f0a_rho_add S)

private theorem ltrb1f0a_rhoHom_eq_frobHom {Omega : Type} [Field Omega] [IsAlgClosed Omega]
    [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi) :
    ltrb1f0a_rhoAddHom ρ.setup = ltrb1f0a_frobHom ρ := by
  refine AddMonoidHom.ext fun x => ?_
  have hx : x = ∑ i, x i • (Pi.single i 1 : Fin ρ.tau.rank → ℤ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx]
  conv_rhs => rw [hx]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, map_zsmul]
  congr 1
  exact (ρ.frob_roots (Pi.single i 1) (isRoot_single ρ.tau i)).symm

private theorem ltrb1f0a_rho_eq_smul {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    {p : ℕ} (S : LangSetup τ L p) {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q)
    (hΦ : S.D.Φ = Units.map (entrywiseHom Fr)) {w : WeylGroup τ}
    (hn : S.D.n = canonicalRep (coxeterSystem τ) L w) :
    ltrb1f0a_rhoAddHom S = DistribSMul.toAddMonoidHom (Fin τ.rank → ℤ) w := by
  refine AddMonoidHom.ext fun x => ?_
  have hx : x = ∑ i, x i • (Pi.single i 1 : Fin τ.rank → ℤ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx]
  conv_rhs => rw [hx]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, map_zsmul]
  congr 1
  exact S.rho_eq_smul_of_frob hFr hΦ hn (isRoot_single τ i)

theorem rootActionAgreeAt_holds {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi) : RootActionAgreeAt ρ := by
  intro v
  exact DFunLike.congr_fun (ltrb1f0a_rhoHom_eq_frobHom ρ) v

theorem weylStepAt_split
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi) (hA : RootActionAgreeAt ρ)
    (htw : ρ.row.tw = false) : WeylStepAt ρ := by
  have hFr : ∀ c, ρ.fr c = c ^ ρ.setup.D.q := by
    intro c
    rw [ρ.fr_eq c, ← ρ.q_eq]
  have hΦ : ρ.setup.D.Φ = Units.map (entrywiseHom ρ.fr) := MonoidHom.ext (ρ.phi_split htw)
  obtain ⟨v, hv⟩ := ρ.setup.D.n_weyl
  refine ⟨v, ?_, ?_⟩
  · intro x
    have hρ : ρ.setup.ρ x = v • x :=
      DFunLike.congr_fun (ltrb1f0a_rho_eq_smul ρ.setup hFr hΦ hv) x
    have h1 : v • x = ρ.frobLinear x := hρ.symm.trans (hA x)
    simpa [htw] using h1
  · intro w
    have hfix : Units.map (entrywiseHom ρ.fr)
        (canonicalRep (coxeterSystem ρ.tau) Omega w) =
        canonicalRep (coxeterSystem ρ.tau) Omega w :=
      CFSG.RankThree.PartOne.KE.frobenius_canonicalRep (L := Omega) ρ.fr w
    have hstep : ρ.setup.D.step (canonicalRep (coxeterSystem ρ.tau) Omega w) =
        ρ.setup.D.n * ρ.setup.D.Φ (canonicalRep (coxeterSystem ρ.tau) Omega w) *
          ρ.setup.D.n⁻¹ := rfl
    have hinv : (canonicalRep (coxeterSystem ρ.tau) Omega v)⁻¹ =
        canonicalRep (coxeterSystem ρ.tau) Omega v⁻¹ := by
      rw [inv_eq_iff_mul_eq_one,
        ← CFSG.RankThree.PartOne.Q1327T.canonicalRep_mul_charTwo (w := v) (v := v⁻¹),
        mul_inv_cancel, canonicalRep_one]
    rw [hstep, hΦ, hfix, hv]
    rw [CFSG.RankThree.PartOne.Q1327T.canonicalRep_mul_charTwo (w := v * w) (v := v⁻¹),
      CFSG.RankThree.PartOne.Q1327T.canonicalRep_mul_charTwo (w := v) (v := w), hinv]

end CFSG.StandardType.S2MathAs1E6Companion1625

end
