module

public import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.T173UniOmega
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CRankWitt
import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
import CFSG.GroupTheory.WeirSylow.OrthogonalTypes
import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
import CFSG.Holt.Fixed
import CFSG.LieType.SeitzGeneration.HyperLinear
import CFSG.LieType.SeitzGeneration.OrthCubeBlocks
import CFSG.LieType.SeitzGeneration.OrthExLift
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLInner
import CFSG.LocalAnalysis.ComponentClassification.BurgoyneProjSlice
import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentLayer
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBaseIso
import CFSG.LocalAnalysis.GLTheoremA.P51.Quaternion
import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral
import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16
import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim
import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
import CFSG.LocalAnalysis.SignalizerFunctor
import CFSG.Quasithin.Background.A3ComponentsAmbient
import CFSG.RankThree.PartOne.CTP.SeitzLinear
import CFSG.RankThree.PartOne.FOC.CompCommutator
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.OmNsRootGen

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.GLTheoremA.S172C.Cent CFSG.LocalAnalysis.GLTheoremA.S172C.Rank
  CFSG.LocalAnalysis.GLTheoremA.T173U

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ} {k : ℕ} {U : Fin k → Submodule F V}
  {e : Fin k → ↥(orthDerived Q)} {E : Subgroup ↥(orthDerived Q)} {u : Fin k → V} {c t : F}
  {a b : Fin k}

@[expose] noncomputable def signedSwap (Q : QuadraticForm F V) (e : Fin k → ↥(orthDerived Q))
    (u : Fin k → V) (c t : F) (a b : Fin k) : V ≃ₗ[F] V :=
  reflect Q (u a) * reflect Q (u b) * frameSwap Q e u c t a b

@[expose] noncomputable def signChange (Q : QuadraticForm F V) (u : Fin k → V) (v : V)
    (a : Fin k) : V ≃ₗ[F] V :=
  reflect Q (u a) * reflect Q v

private noncomputable abbrev eu (e : Fin k → ↥(orthDerived Q)) (u : Fin k → V) (a : Fin k) : V :=
  (e a : V ≃ₗ[F] V) (u a)

private theorem eu_mem (hF : IsCoherentFrame Q p U e E u c t) (a : Fin k) :
    eu e u a ∈ U a :=
  hF.maps_to a (u a) (hF.mem a)

private theorem quad_eu (hF : IsCoherentFrame Q p U e E u c t) (a : Fin k) : Q (eu e u a) = c := by
  rw [eu, map_of_mem (Subgroup.commutator_le_self (TauCeti.QuadraticMap.orthogonalGroup Q)
    (e a).2), hF.quad_eq]

private theorem polar_u_eu (hF : IsCoherentFrame Q p U e E u c t) (a : Fin k) :
    polar Q (u a) (eu e u a) = t * c :=
  hF.polar_eq a

private theorem polar_eu_u (hF : IsCoherentFrame Q p U e E u c t) (a : Fin k) :
    polar Q (eu e u a) (u a) = t * c := by
  rw [polar_comm, hF.polar_eq]

private theorem polar_u_u_of_ne (hF : IsCoherentFrame Q p U e E u c t) (hab : a ≠ b) :
    polar Q (u a) (u b) = 0 :=
  hF.toIsPlaneSystem.perp a b hab (u a) (hF.mem a) (u b) (hF.mem b)

private theorem polar_u_eu_of_ne (hF : IsCoherentFrame Q p U e E u c t)
    (hab : a ≠ b) : polar Q (u a) (eu e u b) = 0 :=
  hF.toIsPlaneSystem.perp a b hab (u a) (hF.mem a) (eu e u b) (eu_mem hF b)

private theorem polar_eu_u_of_ne (hF : IsCoherentFrame Q p U e E u c t)
    (hab : a ≠ b) : polar Q (eu e u a) (u b) = 0 :=
  hF.toIsPlaneSystem.perp a b hab (eu e u a) (eu_mem hF a) (u b) (hF.mem b)

private theorem polar_eu_eu_of_ne (hF : IsCoherentFrame Q p U e E u c t)
    (hab : a ≠ b) : polar Q (eu e u a) (eu e u b) = 0 :=
  hF.toIsPlaneSystem.perp a b hab (eu e u a) (eu_mem hF a) (eu e u b) (eu_mem hF b)

private theorem quad_u_add (hF : IsCoherentFrame Q p U e E u c t) (hab : a ≠ b) :
    Q (u a + u b) = 0 := by
  rw [QuadraticMap.map_add Q, hF.quad_eq a, hF.quad_eq b, polar_u_u_of_ne hF hab]
  simp [CharTwo.add_self_eq_zero]

private theorem quad_eu_add (hF : IsCoherentFrame Q p U e E u c t) (hab : a ≠ b) :
    Q (eu e u a + eu e u b) = 0 := by
  rw [QuadraticMap.map_add Q, quad_eu hF a, quad_eu hF b, polar_eu_eu_of_ne hF hab]
  simp [CharTwo.add_self_eq_zero]

private theorem polar_u_add_center (hF : IsCoherentFrame Q p U e E u c t)
    (hab : a ≠ b) :
    polar Q (u a + u b) (eu e u a + eu e u b) = 0 := by
  rw [polar_add_left, polar_add_right, polar_add_right, polar_u_eu hF a, polar_u_eu_of_ne hF hab,
    polar_u_eu_of_ne (a := b) (b := a) hF hab.symm, polar_u_eu hF b]
  simp [CharTwo.add_self_eq_zero]

private theorem polar_u_add_swapParam (hF : IsCoherentFrame Q p U e E u c t) (hab : a ≠ b) :
    polar Q (u a + u b) ((t * c)⁻¹ • (eu e u a + eu e u b)) = 0 := by
  rw [polar_smul_right_eq, polar_u_add_center hF hab, mul_zero]

private theorem quad_swapParam (hF : IsCoherentFrame Q p U e E u c t)
    (hab : a ≠ b) :
    Q ((t * c)⁻¹ • (eu e u a + eu e u b)) = 0 := by
  rw [map_smul_eq_sq, quad_eu_add hF hab, mul_zero]

private theorem polar_u_swapParam_left (hF : IsCoherentFrame Q p U e E u c t)
    (hab : a ≠ b) : polar Q (u a) ((t * c)⁻¹ • (eu e u a + eu e u b)) = 1 := by
  rw [polar_smul_right_eq, polar_add_right, polar_u_eu hF a, polar_u_eu_of_ne hF hab, add_zero,
    inv_mul_cancel₀ (mul_ne_zero hF.t_ne_zero hF.c_ne_zero)]

private theorem polar_u_swapParam_right (hF : IsCoherentFrame Q p U e E u c t)
    (hab : a ≠ b) : polar Q (u b) ((t * c)⁻¹ • (eu e u a + eu e u b)) = 1 := by
  rw [polar_smul_right_eq, polar_add_right, polar_u_eu_of_ne hF hab.symm, polar_u_eu hF b,
    zero_add, inv_mul_cancel₀ (mul_ne_zero hF.t_ne_zero hF.c_ne_zero)]

private theorem polar_eu_swapParam_left (hF : IsCoherentFrame Q p U e E u c t)
    (hab : a ≠ b) : polar Q (eu e u a) ((t * c)⁻¹ • (eu e u a + eu e u b)) = 0 := by
  rw [polar_smul_right_eq, polar_add_right, polar_self_eq_two_mul, quad_eu hF a,
    CharTwo.two_eq_zero, zero_mul, polar_eu_eu_of_ne hF hab, add_zero, mul_zero]

private theorem polar_eu_swapParam_right (hF : IsCoherentFrame Q p U e E u c t)
    (hab : a ≠ b) : polar Q (eu e u b) ((t * c)⁻¹ • (eu e u a + eu e u b)) = 0 := by
  rw [polar_smul_right_eq, polar_add_right, polar_eu_eu_of_ne hF hab.symm,
    polar_self_eq_two_mul, quad_eu hF b, CharTwo.two_eq_zero, zero_mul, zero_add, mul_zero]

private theorem span_u_eu (hF : IsCoherentFrame Q p U e E u c t) (a : Fin k) :
    Submodule.span F {u a, eu e u a} = U a := by
  have hu0 : u a ≠ 0 := by
    intro h0
    apply hF.c_ne_zero
    rw [← hF.quad_eq a, h0, QuadraticMap.map_zero]
  have hli : LinearIndependent F ![u a, eu e u a] := by
    rw [LinearIndependent.pair_iff]
    intro s r h
    have h1 : polar Q (u a) (s • u a + r • eu e u a) = 0 := by
      rw [h]; simp
    rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, polar_self_eq_two_mul,
      hF.quad_eq a, CharTwo.two_eq_zero, zero_mul, hF.polar_eq a] at h1
    simp only [mul_zero, zero_add] at h1
    have htc : t * c ≠ 0 := mul_ne_zero hF.t_ne_zero hF.c_ne_zero
    have hr : r = 0 := (mul_eq_zero.mp h1).resolve_right htc
    subst hr
    rw [zero_smul, add_zero] at h
    exact ⟨(smul_eq_zero.mp h).resolve_right hu0, rfl⟩
  have hrange : Set.range ![u a, eu e u a] = {u a, eu e u a} := Matrix.range_cons_cons_empty _ _ _
  have hspan2 : Module.finrank F (Submodule.span F {u a, eu e u a}) = 2 := by
    rw [← hrange, finrank_span_eq_card hli, Fintype.card_fin]
  have hle : Submodule.span F {u a, eu e u a} ≤ U a := by
    rw [Submodule.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hF.mem a
    · exact eu_mem hF a
  exact Submodule.eq_of_le_of_finrank_eq hle (by rw [hspan2, hF.finrank_eq a])

private theorem nondeg_sup (hF : IsCoherentFrame Q p U e E u c t) :
    (QuadraticMap.polarBilin (Q.comp (U a ⊔ U b).subtype)).Nondegenerate := by
  have h := hF.toIsPlaneSystem.nondeg_biSup ({a, b} : Finset (Fin k))
  have hsup : (⨆ j ∈ ({a, b} : Finset (Fin k)), U j) = U a ⊔ U b := by
    rw [Finset.insert_eq, Finset.iSup_union, Finset.iSup_singleton, Finset.iSup_singleton]
  rwa [hsup] at h

private theorem add_self_eq_zero_v {F : Type} [Field F] [CharP F 2] {V : Type} [AddCommGroup V]
    [Module F V] (x : V) : x + x = 0 := by
  have h : x + x = ((1 : F) + 1) • x := by rw [add_smul, one_smul]
  rw [h, one_add_one_eq_two, CharTwo.two_eq_zero, zero_smul]

private theorem neg_eq_v {F : Type} [Field F] [CharP F 2] {V : Type} [AddCommGroup V]
    [Module F V] (x : V) : -x = x :=
  neg_eq_of_add_eq_zero_right (add_self_eq_zero_v (F := F) x)

theorem frameSwap_mem_orthDerived (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {ℓ : ℕ}
    (hdim : Module.finrank F V = 2 * ℓ) (hℓ : 3 ≤ ℓ) :
    frameSwap Q e u c t a b ∈ orthDerived Q := by
  rw [orthDerived_eq_elementaryGroup_of_three_le hQ hℓ hdim]
  exact eichler_mem_elementaryGroup Q _ _

theorem frameSwap_mem_orthogonalGroup :
    frameSwap Q e u c t a b ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  eichler_mem_orthogonalGroup Q _ _

theorem frameSwap_apply_left (hF : IsCoherentFrame Q p U e E u c t) (hab : a ≠ b) :
    frameSwap Q e u c t a b (u a) = u b := by
  rw [frameSwap, eichler_apply (quad_u_add hF hab) (polar_u_add_swapParam hF hab)]
  have h1 : polar Q (u a) (u a + u b) = 0 := by
    rw [polar_add_right, polar_self_eq_two_mul, hF.quad_eq a, CharTwo.two_eq_zero, zero_mul,
      polar_u_u_of_ne hF hab, add_zero]
  rw [h1, polar_u_swapParam_left hF hab, quad_swapParam hF hab]
  simp only [zero_smul, zero_mul, add_zero, one_smul]
  rw [sub_eq_add_neg, neg_add_rev, neg_eq_v (F := F), neg_eq_v (F := F)]
  calc u a + (u b + u a) = (u a + u a) + u b := by abel
    _ = u b := by rw [add_self_eq_zero_v (F := F), zero_add]

theorem frameSwap_apply_right (hF : IsCoherentFrame Q p U e E u c t) (hab : a ≠ b) :
    frameSwap Q e u c t a b (u b) = u a := by
  rw [frameSwap, eichler_apply (quad_u_add hF hab) (polar_u_add_swapParam hF hab)]
  have h1 : polar Q (u b) (u a + u b) = 0 := by
    rw [polar_add_right, polar_u_u_of_ne (a := b) (b := a) hF hab.symm, polar_self_eq_two_mul,
      hF.quad_eq b, CharTwo.two_eq_zero, zero_mul, zero_add]
  rw [h1, polar_u_swapParam_right hF hab, quad_swapParam hF hab]
  simp only [zero_smul, zero_mul, add_zero, one_smul]
  rw [sub_eq_add_neg, neg_add_rev, neg_eq_v (F := F), neg_eq_v (F := F)]
  calc u b + (u b + u a) = (u b + u b) + u a := by abel
    _ = u a := by rw [add_self_eq_zero_v (F := F), zero_add]

theorem frameSwap_apply_e_left (hF : IsCoherentFrame Q p U e E u c t) (hab : a ≠ b) :
    frameSwap Q e u c t a b ((e a : V ≃ₗ[F] V) (u a)) = (e b : V ≃ₗ[F] V) (u b) := by
  change frameSwap Q e u c t a b (eu e u a) = eu e u b
  rw [frameSwap, eichler_apply (quad_u_add hF hab) (polar_u_add_swapParam hF hab)]
  have h1 : polar Q (eu e u a) (u a + u b) = t * c := by
    rw [polar_add_right, polar_eu_u hF a, polar_eu_u_of_ne hF hab, add_zero]
  rw [h1, polar_eu_swapParam_left hF hab, quad_swapParam hF hab]
  simp only [zero_smul, zero_mul, add_zero, sub_zero]
  rw [smul_smul, mul_inv_cancel₀ (mul_ne_zero hF.t_ne_zero hF.c_ne_zero), one_smul]
  calc eu e u a + (eu e u a + eu e u b) = (eu e u a + eu e u a) + eu e u b := by abel
    _ = eu e u b := by rw [add_self_eq_zero_v (F := F), zero_add]

theorem frameSwap_apply_e_right (hF : IsCoherentFrame Q p U e E u c t) (hab : a ≠ b) :
    frameSwap Q e u c t a b ((e b : V ≃ₗ[F] V) (u b)) = (e a : V ≃ₗ[F] V) (u a) := by
  change frameSwap Q e u c t a b (eu e u b) = eu e u a
  rw [frameSwap, eichler_apply (quad_u_add hF hab) (polar_u_add_swapParam hF hab)]
  have h1 : polar Q (eu e u b) (u a + u b) = t * c := by
    rw [polar_add_right, polar_eu_u_of_ne (a := b) (b := a) hF hab.symm, polar_eu_u hF b,
      zero_add]
  rw [h1, polar_eu_swapParam_right hF hab, quad_swapParam hF hab]
  simp only [zero_smul, zero_mul, add_zero, sub_zero]
  rw [smul_smul, mul_inv_cancel₀ (mul_ne_zero hF.t_ne_zero hF.c_ne_zero), one_smul]
  calc eu e u b + (eu e u a + eu e u b) = (eu e u b + eu e u b) + eu e u a := by abel
    _ = eu e u a := by rw [add_self_eq_zero_v (F := F), zero_add]

theorem frameSwap_apply_of_mem_polarPerp (hF : IsCoherentFrame Q p U e E u c t) {x : V}
    (hx : x ∈ polarPerp Q (U a ⊔ U b)) : frameSwap Q e u c t a b x = x := by
  rw [frameSwap]
  refine eichler_apply_of_polar_eq_zero ?_ ?_
  · rw [polar_add_right]
    have h1 : polar Q x (u a) = 0 := by
      rw [polar_comm]
      exact mem_polarPerp_iff.1 hx (u a) (Submodule.mem_sup_left (hF.mem a))
    have h2 : polar Q x (u b) = 0 := by
      rw [polar_comm]
      exact mem_polarPerp_iff.1 hx (u b) (Submodule.mem_sup_right (hF.mem b))
    rw [h1, h2, add_zero]
  · rw [polar_smul_right_eq, polar_add_right]
    have h1 : polar Q x ((e a : V ≃ₗ[F] V) (u a)) = 0 := by
      rw [polar_comm]
      exact mem_polarPerp_iff.1 hx (eu e u a) (Submodule.mem_sup_left (eu_mem hF a))
    have h2 : polar Q x ((e b : V ≃ₗ[F] V) (u b)) = 0 := by
      rw [polar_comm]
      exact mem_polarPerp_iff.1 hx (eu e u b) (Submodule.mem_sup_right (eu_mem hF b))
    rw [h1, h2, add_zero, mul_zero]

theorem frameSwap_mul_self (hF : IsCoherentFrame Q p U e E u c t) (hab : a ≠ b) :
    frameSwap Q e u c t a b * frameSwap Q e u c t a b = 1 := by
  rw [frameSwap, eichler_mul (polar_u_add_swapParam hF hab) (polar_u_add_swapParam hF hab)]
  have hz : ((t * c)⁻¹ • (eu e u a + eu e u b)) + ((t * c)⁻¹ • (eu e u a + eu e u b)) = 0 := by
    rw [← add_smul, CharTwo.add_self_eq_zero, zero_smul]
  rw [hz, eichler_zero_right]

private theorem frameSwap_mapsTo_left (hF : IsCoherentFrame Q p U e E u c t) (hab : a ≠ b)
    {x : V} (hx : x ∈ U a) : frameSwap Q e u c t a b x ∈ U b := by
  rw [← span_u_eu hF a] at hx
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · rw [frameSwap_apply_left hF hab]; exact hF.mem b
    · rw [frameSwap_apply_e_left hF hab]; exact eu_mem hF b
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro y z _ _ ihy ihz
    rw [map_add]; exact Submodule.add_mem _ ihy ihz
  · intro r y _ ihy
    rw [map_smul]; exact Submodule.smul_mem _ r ihy

private theorem frameSwap_mapsTo_right (hF : IsCoherentFrame Q p U e E u c t) (hab : a ≠ b)
    {x : V} (hx : x ∈ U b) : frameSwap Q e u c t a b x ∈ U a := by
  rw [← span_u_eu hF b] at hx
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · rw [frameSwap_apply_right hF hab]; exact hF.mem a
    · rw [frameSwap_apply_e_right hF hab]; exact eu_mem hF a
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro y z _ _ ihy ihz
    rw [map_add]; exact Submodule.add_mem _ ihy ihz
  · intro r y _ ihy
    rw [map_smul]; exact Submodule.smul_mem _ r ihy

private theorem frameSwap_mapsTo_apply_left (hF : IsCoherentFrame Q p U e E u c t) (hab : a ≠ b)
    {x : V} (hx : x ∈ U a) :
    (frameSwap Q e u c t a b * (e a : V ≃ₗ[F] V) * frameSwap Q e u c t a b) x =
      (e b : V ≃ₗ[F] V) x := by
  have hxW : frameSwap Q e u c t a b x ∈ U b := frameSwap_mapsTo_left hF hab hx
  have hperp : frameSwap Q e u c t a b x ∈ polarPerp Q (U a) :=
    mem_polarPerp_iff.2 fun y hy => hF.perp a b hab y hy _ hxW
  have hea : (e a : V ≃ₗ[F] V) (frameSwap Q e u c t a b x) = frameSwap Q e u c t a b x :=
    hF.apply_of_perp a _ hperp
  have hperpb : x ∈ polarPerp Q (U b) :=
    mem_polarPerp_iff.2 fun y hy => hF.perp b a hab.symm y hy x hx
  have heb : (e b : V ≃ₗ[F] V) x = x := hF.apply_of_perp b x hperpb
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hea, heb, ← LinearEquiv.mul_apply,
    frameSwap_mul_self hF hab]
  rfl

private theorem frameSwap_mapsTo_apply_right (hF : IsCoherentFrame Q p U e E u c t) (hab : a ≠ b)
    {x : V} (hx : x ∈ U b) :
    (frameSwap Q e u c t a b * (e a : V ≃ₗ[F] V) * frameSwap Q e u c t a b) x =
      (e b : V ≃ₗ[F] V) x := by
  rw [← span_u_eu hF b] at hx
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, frameSwap_apply_right hF hab,
        frameSwap_apply_e_left hF hab]
    · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, frameSwap_apply_e_right hF hab,
        hF.rot a, map_add, map_smul, frameSwap_apply_e_left hF hab,
        frameSwap_apply_left hF hab, hF.rot b]
  · simp
  · intro y z _ _ ihy ihz
    rw [map_add, map_add, ihy, ihz]
  · intro r y _ ihy
    rw [map_smul, map_smul, ihy]

theorem frameSwap_conj_left (hF : IsCoherentFrame Q p U e E u c t) (hab : a ≠ b) :
    frameSwap Q e u c t a b * (e a : V ≃ₗ[F] V) * frameSwap Q e u c t a b =
      (e b : V ≃ₗ[F] V) := by
  have hW : IsCompl (U a ⊔ U b) (polarPerp Q (U a ⊔ U b)) :=
    isCompl_polarPerp (nondeg_sup hF)
  refine LinearMap.ext_on_codisjoint hW.codisjoint ?_ ?_
  · refine LinearMap.eqOn_sup (S := U a) (T := U b) ?_ ?_
    · intro x hx
      exact frameSwap_mapsTo_apply_left hF hab hx
    · intro x hx
      exact frameSwap_mapsTo_apply_right hF hab hx
  · intro x hx
    have hsw : frameSwap Q e u c t a b x = x := frameSwap_apply_of_mem_polarPerp hF hx
    have hea : (e a : V ≃ₗ[F] V) x = x :=
      hF.apply_of_perp a x (mem_polarPerp_iff.2 fun y hy =>
        mem_polarPerp_iff.1 hx y (Submodule.mem_sup_left hy))
    have heb : (e b : V ≃ₗ[F] V) x = x :=
      hF.apply_of_perp b x (mem_polarPerp_iff.2 fun y hy =>
        mem_polarPerp_iff.1 hx y (Submodule.mem_sup_right hy))
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hsw, hea, hsw, heb]

theorem frameSwap_conj_right (hF : IsCoherentFrame Q p U e E u c t) (hab : a ≠ b) :
    frameSwap Q e u c t a b * (e b : V ≃ₗ[F] V) * frameSwap Q e u c t a b =
      (e a : V ≃ₗ[F] V) := by
  have hW : IsCompl (U a ⊔ U b) (polarPerp Q (U a ⊔ U b)) :=
    isCompl_polarPerp (nondeg_sup hF)
  refine LinearMap.ext_on_codisjoint hW.codisjoint ?_ ?_
  · refine LinearMap.eqOn_sup (S := U a) (T := U b) ?_ ?_
    · intro x hx
      rw [← span_u_eu hF a] at hx
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
      · intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl
        · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, frameSwap_apply_left hF hab,
            frameSwap_apply_e_right hF hab]
        · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, frameSwap_apply_e_left hF hab,
            hF.rot b, map_add, map_smul, frameSwap_apply_e_right hF hab,
            frameSwap_apply_right hF hab, hF.rot a]
      · simp
      · intro y z _ _ ihy ihz
        rw [map_add, map_add, ihy, ihz]
      · intro r y _ ihy
        rw [map_smul, map_smul, ihy]
    · intro x hx
      have hxW : frameSwap Q e u c t a b x ∈ U a := frameSwap_mapsTo_right hF hab hx
      have hperp : frameSwap Q e u c t a b x ∈ polarPerp Q (U b) :=
        mem_polarPerp_iff.2 fun y hy => hF.perp b a hab.symm y hy _ hxW
      have heb : (e b : V ≃ₗ[F] V) (frameSwap Q e u c t a b x) = frameSwap Q e u c t a b x :=
        hF.apply_of_perp b _ hperp
      have hperpa : x ∈ polarPerp Q (U a) :=
        mem_polarPerp_iff.2 fun y hy => hF.perp a b hab y hy x hx
      have hea : (e a : V ≃ₗ[F] V) x = x := hF.apply_of_perp a x hperpa
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, heb, hea, ← LinearEquiv.mul_apply,
        frameSwap_mul_self hF hab]
      rfl
  · intro x hx
    have hsw : frameSwap Q e u c t a b x = x := frameSwap_apply_of_mem_polarPerp hF hx
    have hea : (e a : V ≃ₗ[F] V) x = x :=
      hF.apply_of_perp a x (mem_polarPerp_iff.2 fun y hy =>
        mem_polarPerp_iff.1 hx y (Submodule.mem_sup_left hy))
    have heb : (e b : V ≃ₗ[F] V) x = x :=
      hF.apply_of_perp b x (mem_polarPerp_iff.2 fun y hy =>
        mem_polarPerp_iff.1 hx y (Submodule.mem_sup_right hy))
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hsw, heb, hsw, hea]

theorem frameSwap_conj_of_ne (hF : IsCoherentFrame Q p U e E u c t) (hab : a ≠ b) {j : Fin k}
    (hja : j ≠ a) (hjb : j ≠ b) :
    frameSwap Q e u c t a b * (e j : V ≃ₗ[F] V) * frameSwap Q e u c t a b =
      (e j : V ≃ₗ[F] V) := by
  have hejO : (e j : V ≃ₗ[F] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    Subgroup.commutator_le_self (TauCeti.QuadraticMap.orthogonalGroup Q) (e j).2
  have hej_a : ∀ y ∈ U a, (e j : V ≃ₗ[F] V) y = y := by
    intro y hy
    exact hF.apply_of_perp j y (mem_polarPerp_iff.2 fun z hz => hF.perp j a hja z hz y hy)
  have hej_b : ∀ y ∈ U b, (e j : V ≃ₗ[F] V) y = y := by
    intro y hy
    exact hF.apply_of_perp j y (mem_polarPerp_iff.2 fun z hz => hF.perp j b hjb z hz y hy)
  have hW : IsCompl (U a ⊔ U b) (polarPerp Q (U a ⊔ U b)) :=
    isCompl_polarPerp (nondeg_sup hF)
  refine LinearMap.ext_on_codisjoint hW.codisjoint ?_ ?_
  · refine LinearMap.eqOn_sup (S := U a) (T := U b) ?_ ?_
    · intro x hx
      have hxW : frameSwap Q e u c t a b x ∈ U b := frameSwap_mapsTo_left hF hab hx
      have hfix : (e j : V ≃ₗ[F] V) (frameSwap Q e u c t a b x) = frameSwap Q e u c t a b x :=
        hej_b _ hxW
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hfix, ← LinearEquiv.mul_apply,
        frameSwap_mul_self hF hab]
      exact (hej_a x hx).symm
    · intro x hx
      have hxW : frameSwap Q e u c t a b x ∈ U a := frameSwap_mapsTo_right hF hab hx
      have hfix : (e j : V ≃ₗ[F] V) (frameSwap Q e u c t a b x) = frameSwap Q e u c t a b x :=
        hej_a _ hxW
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hfix, ← LinearEquiv.mul_apply,
        frameSwap_mul_self hF hab]
      exact (hej_b x hx).symm
  · intro x hx
    have hsw : frameSwap Q e u c t a b x = x := frameSwap_apply_of_mem_polarPerp hF hx
    have hfixW : ∀ y ∈ U a ⊔ U b, (e j : V ≃ₗ[F] V) y = y := by
      intro y hy
      obtain ⟨ya, hya, yb, hyb, rfl⟩ := Submodule.mem_sup.1 hy
      rw [map_add, hej_a ya hya, hej_b yb hyb]
    have hejx : (e j : V ≃ₗ[F] V) x ∈ polarPerp Q (U a ⊔ U b) := by
      rw [mem_polarPerp_iff]
      intro y hy
      have hfix : (e j : V ≃ₗ[F] V) y = y := hfixW y hy
      rw [← hfix, polar_map_of_mem hejO]
      exact mem_polarPerp_iff.1 hx y hy
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hsw,
      frameSwap_apply_of_mem_polarPerp hF hejx]

theorem reflect_conj_self (hF : IsCoherentFrame Q p U e E u c t) :
    reflect Q (u a) * (e a : V ≃ₗ[F] V) * reflect Q (u a) = ↑((e a)⁻¹) := by
  rw [Subgroup.coe_inv]
  have hρu : reflect Q (u a) (u a) = u a :=
    reflect_apply_of_polar_eq_zero (by
      rw [polar_self_eq_two_mul, hF.quad_eq a, CharTwo.two_eq_zero, zero_mul])
  have hρeu : reflect Q (u a) (eu e u a) = eu e u a + t • u a := by
    rw [reflect_apply (by rw [hF.quad_eq a]; exact hF.c_ne_zero), hF.polar_eq a, hF.quad_eq a,
      mul_div_cancel_right₀ t hF.c_ne_zero, sub_eq_add_neg, neg_eq_v (F := F)]
  have hsum : (t • eu e u a + u a) + t • eu e u a = u a := by
    calc (t • eu e u a + u a) + t • eu e u a = (t • eu e u a + t • eu e u a) + u a := by abel
      _ = u a := by rw [add_self_eq_zero_v (F := F), zero_add]
  have hea : (↑(e a) : V ≃ₗ[F] V) (eu e u a + t • u a) = u a := by
    rw [map_add, map_smul, hF.rot a, hsum]
  have hinv : (↑((e a)⁻¹) : V ≃ₗ[F] V) (u a) = eu e u a + t • u a := by
    rw [Subgroup.coe_inv]
    conv_lhs => rw [← hea]
    exact LinearEquiv.inv_apply_apply' _ _
  have hW : IsCompl (U a) (polarPerp Q (U a)) :=
    isCompl_polarPerp (hF.toIsPlaneSystem.nondeg a)
  refine LinearMap.ext_on_codisjoint hW.codisjoint ?_ ?_
  · intro x hx
    rw [← span_u_eu hF a] at hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hρu, hρeu]
        exact hinv.symm
      · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hρeu, map_add, map_smul, hF.rot a,
          hsum, hρu]
        change u a = ((e a : V ≃ₗ[F] V))⁻¹ ((e a : V ≃ₗ[F] V) (u a))
        rw [LinearEquiv.inv_apply_apply']
    · simp
    · intro y z _ _ ihy ihz
      rw [map_add, map_add, ihy, ihz]
    · intro r y _ ihy
      rw [map_smul, map_smul, ihy]
  · intro x hx
    have hρx : reflect Q (u a) x = x :=
      reflect_apply_of_polar_eq_zero (mem_polarPerp_iff.1 hx (u a) (hF.mem a))
    have hea : (e a : V ≃ₗ[F] V) x = x := hF.apply_of_perp a x hx
    have hinvx : (↑((e a)⁻¹) : V ≃ₗ[F] V) x = x := by
      rw [Subgroup.coe_inv]
      conv_lhs => rw [← hea]
      exact LinearEquiv.inv_apply_apply' _ _
    simp only [LinearEquiv.mul_apply, hρx, hea]
    exact hinvx.symm

theorem reflect_commute_of_ne (hF : IsCoherentFrame Q p U e E u c t) {j : Fin k} (hj : j ≠ a) :
    reflect Q (u a) * (e j : V ≃ₗ[F] V) = (e j : V ≃ₗ[F] V) * reflect Q (u a) := by
  have hρO : reflect Q (u a) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    reflect_mem_orthogonalGroup Q (u a)
  have hW : IsCompl (U j) (polarPerp Q (U j)) :=
    isCompl_polarPerp (hF.toIsPlaneSystem.nondeg j)
  refine LinearMap.ext_on_codisjoint hW.codisjoint ?_ ?_
  · intro x hx
    have hρx : reflect Q (u a) x = x :=
      reflect_apply_of_polar_eq_zero (by
        rw [polar_comm]; exact hF.perp j a hj x hx (u a) (hF.mem a))
    have hρej : reflect Q (u a) ((e j : V ≃ₗ[F] V) x) = (e j : V ≃ₗ[F] V) x :=
      reflect_apply_of_polar_eq_zero (by
        rw [polar_comm]
        exact hF.perp j a hj ((e j : V ≃ₗ[F] V) x) (hF.maps_to j x hx) (u a) (hF.mem a))
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hρx, hρej]
  · intro x hx
    have hejx : (e j : V ≃ₗ[F] V) x = x := hF.apply_of_perp j x hx
    have hρx : reflect Q (u a) x ∈ polarPerp Q (U j) := by
      rw [mem_polarPerp_iff]
      intro y hy
      have hyρ : reflect Q (u a) y = y :=
        reflect_apply_of_polar_eq_zero (by
          rw [polar_comm]; exact hF.perp j a hj y hy (u a) (hF.mem a))
      rw [← hyρ, polar_map_of_mem hρO]
      exact mem_polarPerp_iff.1 hx y hy
    have hfix : (e j : V ≃ₗ[F] V) (reflect Q (u a) x) = reflect Q (u a) x :=
      hF.apply_of_perp j _ hρx
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hejx, hfix]

theorem frameSwap_mul_reflect (hF : IsCoherentFrame Q p U e E u c t) (hab : a ≠ b) :
    frameSwap Q e u c t a b * reflect Q (u a) =
      reflect Q (u b) * frameSwap Q e u c t a b := by
  have h := reflect_conj (frameSwap_mem_orthogonalGroup (Q := Q) (e := e) (u := u) (c := c)
    (t := t) (a := a) (b := b)) (u a)
  have hsinv : (frameSwap Q e u c t a b)⁻¹ = frameSwap Q e u c t a b :=
    inv_eq_of_mul_eq_one_left (frameSwap_mul_self hF hab)
  rw [frameSwap_apply_left hF hab, hsinv] at h
  calc frameSwap Q e u c t a b * reflect Q (u a)
      = frameSwap Q e u c t a b * reflect Q (u a) * 1 := by rw [mul_one]
    _ = frameSwap Q e u c t a b * reflect Q (u a) *
        (frameSwap Q e u c t a b * frameSwap Q e u c t a b) := by
        rw [frameSwap_mul_self hF hab]
    _ = (frameSwap Q e u c t a b * reflect Q (u a) * frameSwap Q e u c t a b) *
        frameSwap Q e u c t a b := by group
    _ = reflect Q (u b) * frameSwap Q e u c t a b := by rw [h]

theorem frameSwap_mul_reflect_symm (hF : IsCoherentFrame Q p U e E u c t) (hab : a ≠ b) :
    frameSwap Q e u c t a b * reflect Q (u b) =
      reflect Q (u a) * frameSwap Q e u c t a b := by
  have h := reflect_conj (frameSwap_mem_orthogonalGroup (Q := Q) (e := e) (u := u) (c := c)
    (t := t) (a := a) (b := b)) (u b)
  have hsinv : (frameSwap Q e u c t a b)⁻¹ = frameSwap Q e u c t a b :=
    inv_eq_of_mul_eq_one_left (frameSwap_mul_self hF hab)
  rw [frameSwap_apply_right hF hab, hsinv] at h
  calc frameSwap Q e u c t a b * reflect Q (u b)
      = frameSwap Q e u c t a b * reflect Q (u b) * 1 := by rw [mul_one]
    _ = frameSwap Q e u c t a b * reflect Q (u b) *
        (frameSwap Q e u c t a b * frameSwap Q e u c t a b) := by
        rw [frameSwap_mul_self hF hab]
    _ = (frameSwap Q e u c t a b * reflect Q (u b) * frameSwap Q e u c t a b) *
        frameSwap Q e u c t a b := by group
    _ = reflect Q (u a) * frameSwap Q e u c t a b := by rw [h]

theorem signedSwap_mem_orthDerived (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {ℓ : ℕ}
    (hdim : Module.finrank F V = 2 * ℓ) (hℓ : 3 ≤ ℓ)
    (hF : IsCoherentFrame Q p U e E u c t) : signedSwap Q e u c t a b ∈ orthDerived Q := by
  have hQa : Q (u a) ≠ 0 := by rw [hF.quad_eq a]; exact hF.c_ne_zero
  have hQb : Q (u b) ≠ 0 := by rw [hF.quad_eq b]; exact hF.c_ne_zero
  have hρ : reflect Q (u a) * reflect Q (u b) ∈ orthDerived Q :=
    reflect_mul_reflect_mem_orthDerived hQ hQa hQb
  have hsw : frameSwap Q e u c t a b ∈ orthDerived Q := by
    rw [orthDerived_eq_elementaryGroup_of_three_le hQ hℓ hdim]
    exact eichler_mem_elementaryGroup Q _ _
  exact Subgroup.mul_mem _ hρ hsw

theorem signedSwap_mul_self (hF : IsCoherentFrame Q p U e E u c t) (hab : a ≠ b) :
    signedSwap Q e u c t a b * signedSwap Q e u c t a b = 1 := by
  have hρab : reflect Q (u a) * reflect Q (u b) = reflect Q (u b) * reflect Q (u a) := by
    have hfix : reflect Q (u b) (u a) = u a :=
      reflect_apply_of_polar_eq_zero (by
        rw [polar_comm]; exact polar_u_u_of_ne hF hab)
    have hconj : reflect Q (u b) * reflect Q (u a) * reflect Q (u b) = reflect Q (u a) := by
      have h := reflect_conj (reflect_mem_orthogonalGroup Q (u b)) (u a)
      rwa [reflect_inv, hfix] at h
    calc reflect Q (u a) * reflect Q (u b)
        = (reflect Q (u b) * reflect Q (u b)) * (reflect Q (u a) * reflect Q (u b)) := by
          rw [reflect_mul_self, one_mul]
      _ = reflect Q (u b) * (reflect Q (u b) * reflect Q (u a) * reflect Q (u b)) := by group
      _ = reflect Q (u b) * reflect Q (u a) := by rw [hconj]
  have h1 : frameSwap Q e u c t a b * reflect Q (u a) =
      reflect Q (u b) * frameSwap Q e u c t a b := frameSwap_mul_reflect hF hab
  have h2 : frameSwap Q e u c t a b * reflect Q (u b) =
      reflect Q (u a) * frameSwap Q e u c t a b := frameSwap_mul_reflect_symm hF hab
  rw [signedSwap]
  calc (reflect Q (u a) * reflect Q (u b) * frameSwap Q e u c t a b) *
        (reflect Q (u a) * reflect Q (u b) * frameSwap Q e u c t a b)
      = reflect Q (u a) * reflect Q (u b) * (frameSwap Q e u c t a b * reflect Q (u a)) *
          reflect Q (u b) * frameSwap Q e u c t a b := by group
    _ = reflect Q (u a) * reflect Q (u b) *
          (reflect Q (u b) * frameSwap Q e u c t a b) * reflect Q (u b) *
          frameSwap Q e u c t a b := by rw [h1]
    _ = reflect Q (u a) * (reflect Q (u b) * reflect Q (u b)) *
          frameSwap Q e u c t a b * reflect Q (u b) * frameSwap Q e u c t a b := by group
    _ = reflect Q (u a) * frameSwap Q e u c t a b * reflect Q (u b) *
          frameSwap Q e u c t a b := by rw [reflect_mul_self]; group
    _ = reflect Q (u a) *
          (frameSwap Q e u c t a b * reflect Q (u b)) * frameSwap Q e u c t a b := by group
    _ = reflect Q (u a) * (reflect Q (u a) * frameSwap Q e u c t a b) *
          frameSwap Q e u c t a b := by rw [h2]
    _ = (reflect Q (u a) * reflect Q (u a)) *
          (frameSwap Q e u c t a b * frameSwap Q e u c t a b) := by group
    _ = 1 := by rw [reflect_mul_self, frameSwap_mul_self hF hab, one_mul]

private theorem frameSwap_reflect_mul_reflect (hF : IsCoherentFrame Q p U e E u c t) (hab : a ≠ b) :
    reflect Q (u a) * reflect Q (u b) * frameSwap Q e u c t a b =
      frameSwap Q e u c t a b * reflect Q (u b) * reflect Q (u a) := by
  have hsinv : (frameSwap Q e u c t a b)⁻¹ = frameSwap Q e u c t a b :=
    inv_eq_of_mul_eq_one_left (frameSwap_mul_self hF hab)
  have h := inv_eq_of_mul_eq_one_left (signedSwap_mul_self hF hab)
  rw [signedSwap, mul_inv_rev, mul_inv_rev, reflect_inv, reflect_inv, hsinv] at h
  exact h.symm

theorem signedSwap_conj_left (hF : IsCoherentFrame Q p U e E u c t) (hab : a ≠ b) :
    signedSwap Q e u c t a b * (e a : V ≃ₗ[F] V) * signedSwap Q e u c t a b =
      ↑((e b)⁻¹) := by
  have hcomm : reflect Q (u a) * (e b : V ≃ₗ[F] V) =
      (e b : V ≃ₗ[F] V) * reflect Q (u a) := reflect_commute_of_ne hF hab.symm
  have hcomm' : reflect Q (u a) * (↑((e b)⁻¹) : V ≃ₗ[F] V) =
      (↑((e b)⁻¹) : V ≃ₗ[F] V) * reflect Q (u a) := by
    rw [Subgroup.coe_inv]
    have h := congrArg Inv.inv hcomm
    simpa [mul_inv_rev, reflect_inv] using h.symm
  rw [signedSwap]
  calc (reflect Q (u a) * reflect Q (u b) * frameSwap Q e u c t a b) *
        (e a : V ≃ₗ[F] V) *
        (reflect Q (u a) * reflect Q (u b) * frameSwap Q e u c t a b)
      = reflect Q (u a) * reflect Q (u b) *
          (frameSwap Q e u c t a b * (e a : V ≃ₗ[F] V) * frameSwap Q e u c t a b) *
          reflect Q (u b) * reflect Q (u a) := by
          nth_rewrite 2 [frameSwap_reflect_mul_reflect hF hab]
          group
    _ = reflect Q (u a) * reflect Q (u b) * (e b : V ≃ₗ[F] V) *
          reflect Q (u b) * reflect Q (u a) := by rw [frameSwap_conj_left hF hab]
    _ = reflect Q (u a) * (reflect Q (u b) * (e b : V ≃ₗ[F] V) * reflect Q (u b)) *
          reflect Q (u a) := by group
    _ = reflect Q (u a) * (↑((e b)⁻¹) : V ≃ₗ[F] V) * reflect Q (u a) := by
        rw [reflect_conj_self hF]
    _ = ↑((e b)⁻¹) := by
        rw [hcomm', mul_assoc, reflect_mul_self, mul_one]

theorem signedSwap_conj_right (hF : IsCoherentFrame Q p U e E u c t) (hab : a ≠ b) :
    signedSwap Q e u c t a b * (e b : V ≃ₗ[F] V) * signedSwap Q e u c t a b =
      ↑((e a)⁻¹) := by
  have hcomm : reflect Q (u b) * (e a : V ≃ₗ[F] V) =
      (e a : V ≃ₗ[F] V) * reflect Q (u b) :=
    reflect_commute_of_ne (a := b) (j := a) hF hab
  rw [signedSwap]
  calc (reflect Q (u a) * reflect Q (u b) * frameSwap Q e u c t a b) *
        (e b : V ≃ₗ[F] V) *
        (reflect Q (u a) * reflect Q (u b) * frameSwap Q e u c t a b)
      = reflect Q (u a) * reflect Q (u b) *
          (frameSwap Q e u c t a b * (e b : V ≃ₗ[F] V) * frameSwap Q e u c t a b) *
          reflect Q (u b) * reflect Q (u a) := by
          nth_rewrite 2 [frameSwap_reflect_mul_reflect hF hab]
          group
    _ = reflect Q (u a) * reflect Q (u b) * (e a : V ≃ₗ[F] V) *
          reflect Q (u b) * reflect Q (u a) := by rw [frameSwap_conj_right hF hab]
    _ = reflect Q (u a) * (reflect Q (u b) * (e a : V ≃ₗ[F] V) * reflect Q (u b)) *
          reflect Q (u a) := by group
    _ = reflect Q (u a) * (e a : V ≃ₗ[F] V) * reflect Q (u a) := by
        rw [show reflect Q (u b) * (e a : V ≃ₗ[F] V) * reflect Q (u b) =
          (e a : V ≃ₗ[F] V) from by
          rw [hcomm, mul_assoc, reflect_mul_self, mul_one]]
    _ = ↑((e a)⁻¹) := reflect_conj_self hF

theorem signedSwap_conj_of_ne (hF : IsCoherentFrame Q p U e E u c t) (hab : a ≠ b) {j : Fin k}
    (hja : j ≠ a) (hjb : j ≠ b) :
    signedSwap Q e u c t a b * (e j : V ≃ₗ[F] V) * signedSwap Q e u c t a b =
      (e j : V ≃ₗ[F] V) := by
  have hb : reflect Q (u b) * (e j : V ≃ₗ[F] V) * reflect Q (u b) = (e j : V ≃ₗ[F] V) := by
    rw [reflect_commute_of_ne (a := b) (j := j) hF hjb, mul_assoc, reflect_mul_self, mul_one]
  have ha : reflect Q (u a) * (e j : V ≃ₗ[F] V) * reflect Q (u a) = (e j : V ≃ₗ[F] V) := by
    rw [reflect_commute_of_ne hF hja, mul_assoc, reflect_mul_self, mul_one]
  rw [signedSwap]
  calc (reflect Q (u a) * reflect Q (u b) * frameSwap Q e u c t a b) *
        (e j : V ≃ₗ[F] V) *
        (reflect Q (u a) * reflect Q (u b) * frameSwap Q e u c t a b)
      = reflect Q (u a) * reflect Q (u b) *
          (frameSwap Q e u c t a b * (e j : V ≃ₗ[F] V) * frameSwap Q e u c t a b) *
          reflect Q (u b) * reflect Q (u a) := by
          nth_rewrite 2 [frameSwap_reflect_mul_reflect hF hab]
          group
    _ = reflect Q (u a) * reflect Q (u b) * (e j : V ≃ₗ[F] V) *
          reflect Q (u b) * reflect Q (u a) := by rw [frameSwap_conj_of_ne hF hab hja hjb]
    _ = reflect Q (u a) * (reflect Q (u b) * (e j : V ≃ₗ[F] V) * reflect Q (u b)) *
          reflect Q (u a) := by group
    _ = reflect Q (u a) * (e j : V ≃ₗ[F] V) * reflect Q (u a) := by rw [hb]
    _ = (e j : V ≃ₗ[F] V) := ha

theorem signedSwap_apply_of_mem_polarPerp (hF : IsCoherentFrame Q p U e E u c t) {x : V}
    (hx : x ∈ polarPerp Q (U a ⊔ U b)) : signedSwap Q e u c t a b x = x := by
  have hsw : frameSwap Q e u c t a b x = x := frameSwap_apply_of_mem_polarPerp hF hx
  have hb : reflect Q (u b) x = x :=
    reflect_apply_of_polar_eq_zero
      (mem_polarPerp_iff.1 hx (u b) (Submodule.mem_sup_right (hF.mem b)))
  have ha : reflect Q (u a) x = x :=
    reflect_apply_of_polar_eq_zero
      (mem_polarPerp_iff.1 hx (u a) (Submodule.mem_sup_left (hF.mem a)))
  rw [signedSwap, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hsw, hb, ha]

private theorem reflect_commute_of_polar_eq_zero {x y : V} (h : polar Q x y = 0) :
    reflect Q x * reflect Q y = reflect Q y * reflect Q x := by
  have hy : reflect Q y x = x :=
    reflect_apply_of_polar_eq_zero (by rw [polar_comm]; exact h)
  have hconj : reflect Q y * reflect Q x * reflect Q y = reflect Q x := by
    have hc := reflect_conj (reflect_mem_orthogonalGroup Q y) x
    rwa [reflect_inv, hy] at hc
  calc reflect Q x * reflect Q y
      = (reflect Q y * reflect Q y) * (reflect Q x * reflect Q y) := by
          rw [reflect_mul_self, one_mul]
    _ = reflect Q y * (reflect Q y * reflect Q x * reflect Q y) := by group
    _ = reflect Q y * reflect Q x := by rw [hconj]

theorem signChange_mem_orthDerived (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hF : IsCoherentFrame Q p U e E u c t) {v : V} (hQv : Q v ≠ 0) :
    signChange Q u v a ∈ orthDerived Q := by
  rw [signChange]
  exact reflect_mul_reflect_mem_orthDerived hQ (by rw [hF.quad_eq a]; exact hF.c_ne_zero) hQv

theorem signChange_mul_self (hF : IsCoherentFrame Q p U e E u c t) {v : V}
    (hv : v ∈ polarPerp Q (⨆ j, U j)) :
    signChange Q u v a * signChange Q u v a = 1 := by
  have hB : polar Q (u a) v = 0 :=
    mem_polarPerp_iff.1 hv (u a) (le_iSup U a (hF.mem a))
  have hvfix : reflect Q v (u a) = u a :=
    reflect_apply_of_polar_eq_zero (by rw [polar_comm]; exact hB)
  have hconj : reflect Q v * reflect Q (u a) * reflect Q v = reflect Q (u a) := by
    have h := reflect_conj (reflect_mem_orthogonalGroup Q v) (u a)
    rwa [reflect_inv, hvfix] at h
  rw [signChange]
  calc (reflect Q (u a) * reflect Q v) * (reflect Q (u a) * reflect Q v)
      = reflect Q (u a) * (reflect Q v * reflect Q (u a) * reflect Q v) := by group
    _ = reflect Q (u a) * reflect Q (u a) := by rw [hconj]
    _ = 1 := reflect_mul_self Q (u a)

theorem signChange_conj_self (hF : IsCoherentFrame Q p U e E u c t) {v : V}
    (hv : v ∈ polarPerp Q (⨆ j, U j)) :
    signChange Q u v a * (e a : V ≃ₗ[F] V) * signChange Q u v a = ↑((e a)⁻¹) := by
  have heaO : (e a : V ≃ₗ[F] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    Subgroup.commutator_le_self (TauCeti.QuadraticMap.orthogonalGroup Q) (e a).2
  have hav : (e a : V ≃ₗ[F] V) v = v :=
    hF.toIsPlaneFrame.apply_eq_of_mem_polarPerp_iSup (IsPlaneFrame.mem hF.toIsPlaneFrame a) hv
  have hcomm : (e a : V ≃ₗ[F] V) * reflect Q v = reflect Q v * (e a : V ≃ₗ[F] V) := by
    have h := reflect_conj heaO v
    rw [hav] at h
    calc (e a : V ≃ₗ[F] V) * reflect Q v
        = (e a : V ≃ₗ[F] V) * reflect Q v * 1 := by rw [mul_one]
      _ = (e a : V ≃ₗ[F] V) * reflect Q v *
          ((e a : V ≃ₗ[F] V)⁻¹ * (e a : V ≃ₗ[F] V)) := by rw [inv_mul_cancel, mul_one]
      _ = ((e a : V ≃ₗ[F] V) * reflect Q v * (e a : V ≃ₗ[F] V)⁻¹) *
          (e a : V ≃ₗ[F] V) := by group
      _ = reflect Q v * (e a : V ≃ₗ[F] V) := by rw [h]
  have hvea : reflect Q v * (e a : V ≃ₗ[F] V) * reflect Q v = (e a : V ≃ₗ[F] V) := by
    rw [hcomm.symm, mul_assoc, reflect_mul_self, mul_one]
  have hB : polar Q (u a) v = 0 :=
    mem_polarPerp_iff.1 hv (u a) (le_iSup U a (hF.mem a))
  have hρaρv : reflect Q (u a) * reflect Q v = reflect Q v * reflect Q (u a) :=
    reflect_commute_of_polar_eq_zero hB
  rw [signChange]
  calc (reflect Q (u a) * reflect Q v) * (e a : V ≃ₗ[F] V) *
        (reflect Q (u a) * reflect Q v)
      = reflect Q (u a) * (reflect Q v * (e a : V ≃ₗ[F] V) * reflect Q v) *
          reflect Q (u a) := by
          nth_rewrite 2 [hρaρv]
          group
    _ = reflect Q (u a) * (e a : V ≃ₗ[F] V) * reflect Q (u a) := by rw [hvea]
    _ = ↑((e a)⁻¹) := reflect_conj_self hF

theorem signChange_conj_of_ne (hF : IsCoherentFrame Q p U e E u c t) {v : V}
    (hv : v ∈ polarPerp Q (⨆ j, U j)) {j : Fin k} (hj : j ≠ a) :
    signChange Q u v a * (e j : V ≃ₗ[F] V) * signChange Q u v a = (e j : V ≃ₗ[F] V) := by
  have hejO : (e j : V ≃ₗ[F] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    Subgroup.commutator_le_self (TauCeti.QuadraticMap.orthogonalGroup Q) (e j).2
  have hejv : (e j : V ≃ₗ[F] V) v = v :=
    hF.toIsPlaneFrame.apply_eq_of_mem_polarPerp_iSup (IsPlaneFrame.mem hF.toIsPlaneFrame j) hv
  have hcomm : (e j : V ≃ₗ[F] V) * reflect Q v = reflect Q v * (e j : V ≃ₗ[F] V) := by
    have h := reflect_conj hejO v
    rw [hejv] at h
    calc (e j : V ≃ₗ[F] V) * reflect Q v
        = (e j : V ≃ₗ[F] V) * reflect Q v * 1 := by rw [mul_one]
      _ = (e j : V ≃ₗ[F] V) * reflect Q v *
          ((e j : V ≃ₗ[F] V)⁻¹ * (e j : V ≃ₗ[F] V)) := by rw [inv_mul_cancel, mul_one]
      _ = ((e j : V ≃ₗ[F] V) * reflect Q v * (e j : V ≃ₗ[F] V)⁻¹) *
          (e j : V ≃ₗ[F] V) := by group
      _ = reflect Q v * (e j : V ≃ₗ[F] V) := by rw [h]
  have hvej : reflect Q v * (e j : V ≃ₗ[F] V) * reflect Q v = (e j : V ≃ₗ[F] V) := by
    rw [hcomm.symm, mul_assoc, reflect_mul_self, mul_one]
  have haej : reflect Q (u a) * (e j : V ≃ₗ[F] V) * reflect Q (u a) = (e j : V ≃ₗ[F] V) := by
    rw [reflect_commute_of_ne hF hj, mul_assoc, reflect_mul_self, mul_one]
  have hB : polar Q (u a) v = 0 := mem_polarPerp_iff.1 hv (u a) (le_iSup U a (hF.mem a))
  have hρaρv : reflect Q (u a) * reflect Q v = reflect Q v * reflect Q (u a) :=
    reflect_commute_of_polar_eq_zero hB
  rw [signChange]
  calc (reflect Q (u a) * reflect Q v) * (e j : V ≃ₗ[F] V) *
        (reflect Q (u a) * reflect Q v)
      = reflect Q (u a) * (reflect Q v * (e j : V ≃ₗ[F] V) * reflect Q v) *
          reflect Q (u a) := by
          nth_rewrite 2 [hρaρv]
          group
    _ = reflect Q (u a) * (e j : V ≃ₗ[F] V) * reflect Q (u a) := by rw [hvej]
    _ = (e j : V ≃ₗ[F] V) := haej

end CFSG.StandardType.OmNsRootGen

end
