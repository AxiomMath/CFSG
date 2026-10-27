module

public import CFSG.LocalAnalysis.StandardType.ExcPos.E7RootSL2Normalizer
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcE6
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.SplitRootAction
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcRoots
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwoDHighAssembly
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeTw6LongLevi
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.OrbitSelectionPart1
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Conjugation

public noncomputable section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE6
  CFSG.HardMathSupport.Timmesfeld.LangTorus

open scoped CFSG.ConvolutionPoints


variable {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]

theorem rationalComponent_eq_rootSpan_inf_step_of_e6
    {p : ℕ} (S : LangSetup .E7 Omega p)
    (sigma : Omega ≃+* Omega) (hPhi : S.D.Φ = frobGL sigma)
    (hRho : ∀ alpha, IsRoot .E7 alpha → S.ρ alpha = -alpha)
    (a : Fin Tag.E7.rank → Omegaˣ) (c : KernelComponent (rootCharHom a))
    (w : WeylGroup .E7) (hPsi : componentRoots (rootCharHom a) c =
      (fun alpha => w • alpha) '' parabolicRoots .E7 (e6Nodes .E7)) :
    rationalComponent S.ρ S.Γ (rootCharHom a) c =
      rootSpan .E7 Omega (componentRoots (rootCharHom a) c) ⊓
        S.D.step.eqLocus (MonoidHom.id _) := by
  have hkerEq := kernelRoots_eq_componentRoots_of_E7_e6 (rootCharHom a) c w hPsi
  have hneg : ∀ alpha ∈ componentRoots (rootCharHom a) c,
      -alpha ∈ componentRoots (rootCharHom a) c := by
    intro alpha halpha
    rw [← hkerEq] at halpha ⊢
    refine ⟨IsRoot.neg halpha.1, ?_⟩
    have hh := (rootCharHom a).map_inv (Multiplicative.ofAdd alpha)
    change (rootCharHom a) (Multiplicative.ofAdd (-alpha)) =
      ((rootCharHom a) (Multiplicative.ofAdd alpha))⁻¹ at hh
    rw [hh, halpha.2, inv_one]
  have hstable : ∀ alpha ∈ componentRoots (rootCharHom a) c,
      S.ρ alpha ∈ componentRoots (rootCharHom a) c := by
    intro alpha halpha
    have hk : alpha ∈ kernelRoots (rootCharHom a) := by rwa [hkerEq]
    rw [hRho alpha hk.1]
    exact hneg alpha halpha
  obtain ⟨nW, hn⟩ := S.D.n_weyl
  have hw : ∀ alpha ∈ componentRoots (rootCharHom a) c,
      nW • alpha ∈ componentRoots (rootCharHom a) c := by
    intro alpha halpha
    have hk : alpha ∈ kernelRoots (rootCharHom a) := by rwa [hkerEq]
    rw [S.frob.weyl_smul_eq sigma hPhi nW hn hk.1]
    exact hstable alpha halpha
  obtain ⟨_, hqs⟩ := rootSpan_inf_model_quasisimple
    (τ := .E7) (by intro t; cases t <;> decide) S hn w (by
      intro alpha halpha
      rw [← hPsi] at halpha ⊢
      exact hw alpha halpha)
  have hqsActual : CFSG.IsQuasisimple
      ↥(rootSpan .E7 Omega (componentRoots (rootCharHom a) c) ⊓ S.D.model) := by
    rw [hPsi]
    exact hqs
  have hcompEq := rationalComponent_eq_rootSpan_inf_model_of_layer S c hstable hqsActual
  have hAdj : rootSpan .E7 Omega (componentRoots (rootCharHom a) c) ≤
      adjointGroup .E7 Omega := by
    unfold rootSpan
    exact iSup_le fun alpha => iSup_le fun _ => rootSubgroup_le_adjointGroup alpha
  rw [hcompEq, LangDatum.model, ← inf_assoc, inf_eq_left.mpr hAdj]

theorem map_rootSpan_pair_step_eq_of_neg
    {p : ℕ} (S : LangSetup .E7 Omega p)
    (sigma : Omega ≃+* Omega) (hPhi : S.D.Φ = frobGL sigma)
    (hRho : ∀ alpha, IsRoot .E7 alpha → S.ρ alpha = -alpha)
    {beta : Fin Tag.E7.rank → ℤ} (hbeta : IsRoot .E7 beta) :
    (rootSpan .E7 Omega {beta, -beta}).map S.D.step =
      rootSpan .E7 Omega {beta, -beta} := by
  obtain ⟨w, hn⟩ := S.D.n_weyl
  have hPhi' : S.D.Φ = Units.map (entrywiseHom sigma.toRingHom) := hPhi
  have hp := S.D.map_step_rootSubgroup (Fr := sigma.toRingHom) sigma.surjective hPhi' hn hbeta
  have hm := S.D.map_step_rootSubgroup (Fr := sigma.toRingHom) sigma.surjective hPhi' hn
    (IsRoot.neg hbeta)
  have hwb : w • beta = -beta :=
    (S.frob.weyl_smul_eq sigma hPhi w hn hbeta).trans (hRho beta hbeta)
  rw [rootSpan, iSup_insert, iSup_singleton, Subgroup.map_sup, hp, hm, smul_neg,
    hwb, neg_neg, sup_comm]

theorem map_conj_rootSpan_pair_step_eq
    {p : ℕ} (S : LangSetup .E7 Omega p) (sigma : Omega ≃+* Omega)
    (z : ModGL .E7 Omega) {gamma : Fin Tag.E7.rank → ℤ}
    (hstep : ∀ g ∈ rootSpan .E7 Omega ({gamma, -gamma} : Set (Fin Tag.E7.rank → ℤ)),
      S.D.step (z * g * z⁻¹) = z * frobGL sigma g * z⁻¹) :
    ((rootSpan .E7 Omega {gamma, -gamma}).map (MulAut.conj z).toMonoidHom).map S.D.step =
      (rootSpan .E7 Omega {gamma, -gamma}).map (MulAut.conj z).toMonoidHom := by
  have hmap : (rootSpan .E7 Omega {gamma, -gamma}).map
      (S.D.step.comp (MulAut.conj z).toMonoidHom) =
      (rootSpan .E7 Omega {gamma, -gamma}).map
        ((MulAut.conj z).toMonoidHom.comp (frobGL sigma)) := by
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine ⟨g, hg, ?_⟩
      simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        using (hstep g hg).symm
    · rintro ⟨g, hg, rfl⟩
      refine ⟨g, hg, ?_⟩
      simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        using hstep g hg
  rw [Subgroup.map_map, hmap, ← Subgroup.map_map]
  rw [map_rootSpan_of_forall (fun alpha _ => map_entrywise_rootSubgroup sigma alpha)]

variable [Algebra (ZMod 2) Omega] [Algebra.IsAlgebraic (ZMod 2) Omega]

theorem exists_rational_e6_root_pair_conj
    {p : ℕ} (S : LangSetup .E7 Omega p)
    (sigma : Omega ≃+* Omega) (hPhi : S.D.Φ = frobGL sigma)
    (hRho : ∀ alpha, IsRoot .E7 alpha → S.ρ alpha = -alpha)
    (q : ℕ) (hq0 : 1 ≤ q) (hq : S.D.q = 2 ^ q)
    (a : Fin Tag.E7.rank → Omegaˣ) (c : KernelComponent (rootCharHom a))
    (w : WeylGroup .E7) (hPsi : componentRoots (rootCharHom a) c =
      (fun alpha => w • alpha) '' parabolicRoots .E7 (e6Nodes .E7))
    {beta gamma : Fin Tag.E7.rank → ℤ} (hbeta : beta ∈ componentRoots (rootCharHom a) c)
    (hgamma : gamma ∈ componentRoots (rootCharHom a) c)
    (z : ModGL .E7 Omega) (hz : z ∈ rootSpan .E7 Omega (componentRoots (rootCharHom a) c))
    (hstep : ∀ g ∈ rootSpan .E7 Omega ({gamma, -gamma} : Set (Fin Tag.E7.rank → ℤ)),
      S.D.step (z * g * z⁻¹) = z * frobGL sigma g * z⁻¹) :
    ∃ u ∈ rationalComponent S.ρ S.Γ (rootCharHom a) c,
      ((rootSpan .E7 Omega {gamma, -gamma}).map (MulAut.conj z).toMonoidHom ⊓
        S.D.step.eqLocus (MonoidHom.id _)) =
      (rootSpan .E7 Omega {beta, -beta} ⊓ S.D.step.eqLocus (MonoidHom.id _)).map
        (MulAut.conj u).toMonoidHom := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Psi := componentRoots (rootCharHom a) c
  let H := rootSpan .E7 Omega Psi
  let A := rootSpan .E7 Omega {beta, -beta}
  let B := (rootSpan .E7 Omega {gamma, -gamma}).map (MulAut.conj z).toMonoidHom
  have hkerEq : kernelRoots (rootCharHom a) = Psi :=
    kernelRoots_eq_componentRoots_of_E7_e6 (rootCharHom a) c w hPsi
  have hRoot : ∀ alpha ∈ Psi, IsRoot .E7 alpha := by
    intro alpha halpha
    have hk : alpha ∈ kernelRoots (rootCharHom a) := by rwa [hkerEq]
    exact hk.1
  have hNeg : ∀ alpha ∈ Psi, -alpha ∈ Psi := by
    intro alpha halpha
    rw [← hkerEq] at halpha ⊢
    refine ⟨IsRoot.neg halpha.1, ?_⟩
    have hh := (rootCharHom a).map_inv (Multiplicative.ofAdd alpha)
    change (rootCharHom a) (Multiplicative.ofAdd (-alpha)) =
      ((rootCharHom a) (Multiplicative.ofAdd alpha))⁻¹ at hh
    rw [hh, halpha.2, inv_one]
  have hFH : ∀ x ∈ H, S.D.step x ∈ H := by
    intro x hx
    apply F4ExplicitPos.OrbitSelection.orbit_step_mem_rootSpan S.D S.frob hRoot _ hx
    intro alpha halpha
    rw [hRho alpha (hRoot alpha halpha)]
    exact hNeg alpha halpha
  have hFA : A.map S.D.step = A := map_rootSpan_pair_step_eq_of_neg S sigma hPhi hRho (hRoot beta hbeta)
  have hFB : B.map S.D.step = B := map_conj_rootSpan_pair_step_eq S sigma z hstep
  have hN := LieKnownR2.ExcPos.isConnectedAlgebraicSubgroup_e6_rootSL2_normalizer
    (Omega := Omega) w Psi hPsi (hRoot beta hbeta) hbeta (hNeg beta hbeta)
  have hAspan : (rootSL2 .E7 Omega beta).range = A := by
    change (rootSL2 .E7 Omega beta).range = rootSpan .E7 Omega {beta, -beta}
    rw [range_rootSL2_of_isRoot (hRoot beta hbeta), rootSpan, iSup_insert, iSup_singleton]
  rw [hAspan] at hN
  obtain ⟨g, hg, hAg⟩ := LieKnownR2.ExcPos.exists_conj_e6_rootSpan_pair
    (Omega := Omega) w Psi hPsi hbeta hgamma
  have hzg : z * g ∈ H := H.mul_mem hz hg
  have hConj : A.map (MulAut.conj (z * g)).toMonoidHom = B := by
    have hcomp : (MulAut.conj (z * g)).toMonoidHom =
        (MulAut.conj z).toMonoidHom.comp (MulAut.conj g).toMonoidHom := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [hcomp, ← Subgroup.map_map, hAg]
  obtain ⟨Q, _, _, hQ⟩ := S.exists_step_frobTwist_adjoint (r := 2) (e := q) hq
  have hDstep : S.D.step = frobTwistGL .E7 Omega 2 q Q := MonoidHom.ext hQ
  obtain ⟨u, huH, huF, huConj⟩ := LieKnownR2.ExcPos.exists_fixed_conj_of_connected_normalizer
    q hq0 Q H A B (by rw [← hDstep]; exact hFH) (by rw [← hDstep]; exact hFA)
      (by rw [← hDstep]; exact hFB) hN hzg hConj
  have huStep : S.D.step u = u := by rwa [← hDstep] at huF
  refine ⟨u, ?_, ?_⟩
  · rw [rationalComponent_eq_rootSpan_inf_step_of_e6 S sigma hPhi hRho a c w hPsi]
    exact ⟨huH, huStep⟩
  · change B ⊓ S.D.step.eqLocus (MonoidHom.id _) =
      (A ⊓ S.D.step.eqLocus (MonoidHom.id _)).map (MulAut.conj u).toMonoidHom
    rw [← huConj, F4ExplicitPos.AmbientPairDescent.map_conj_fixed_eq S.D.step huStep A]

end CFSG.StandardType.LieKnownR2.ExcPos
