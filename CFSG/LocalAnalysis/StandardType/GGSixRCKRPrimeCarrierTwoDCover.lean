module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCarrierTwoDSetup
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCarrierTwoDFixed
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCarrierTwoDFrames
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcShapeFourKac
public import CFSG.LocalAnalysis.StandardType.GGPinnedReturnDefs

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.StandardType.GGFinModel
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.WeakCT CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.LocalAnalysis.GLTheoremA.T171Sh CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups


structure RCKTwoDCanonicalData {τ : Tag} {p₀ : ℕ} (S : LangSetup τ GGL p₀)
    (a : Fin τ.rank → GGLˣ) (i : KernelComponent (rootCharHom a)) (h : ℕ) where
  rank_four_le : 4 ≤ compRank (componentRoots (rootCharHom a) i)
  field_pos : 1 ≤ h
  D : CFSG.RankThree.Lattice.GenFixedRootDatum τ 2 GGL (SpanQuot (componentRoots (rootCharHom a) i))
  field_eq : D.e = h
  ε : simpleRoots (componentRoots (rootCharHom a) i) ≃ Fin (compRank (componentRoots (rootCharHom a) i))
  z : ModGL τ GGL
  κ : GaloisField 2 h ≃+* ↥(frobeniusFixedField GGL 2 D.e)
  φ : (ggU .POmegaMinus (compRank (componentRoots (rootCharHom a) i)) h).K →* ModGL τ GGL
  range_eq : φ.range = rationalComponent S.ρ S.Γ (rootCharHom a) i
  ker_le_center : φ.ker ≤ Subgroup.center (ggU .POmegaMinus (compRank (componentRoots (rootCharHom a) i)) h).K
  z_mem : z ∈ torusGroup τ GGL ⊔ rootSpan τ GGL (kernelRoots (rootCharHom a))
  simple_eq : D.simpleRootsJ = ((simpleRoots (componentRoots (rootCharHom a) i) : Finset (Fin τ.rank → ℤ)) : Set (Fin τ.rank → ℤ))
  fix_long : ∀ j, j.val + 2 < compRank (componentRoots (rootCharHom a) i) →
    D.θ (toReal (ε.symm j)) = toReal (ε.symm j)
  frob_eq : ∀ x : adjointGroup τ GGL,
    S.D.step (z * (x : ModGL τ GGL) * z⁻¹) = z * (D.F x : ModGL τ GGL) * z⁻¹
  long_param : ∀ (k : Fin (compRank (componentRoots (rootCharHom a) i) - 1))
      (hk : k.val + 1 < compRank (componentRoots (rootCharHom a) i) - 1),
    φ.comp (rLong _ (minusCoeffs 2 h).1 (minusCoeffs 2 h).2 hk) =
      (MulAut.conj z).toMonoidHom.comp ((rootSL2 τ GGL (ε.symm ⟨k.val, by omega⟩)).comp
        (Matrix.SpecialLinearGroup.map ((frobeniusFixedField GGL 2 D.e).subtype.comp κ.toRingHom)))

noncomputable def rckTwoD_canonicalData
    {τ : Tag} {p₀ p h : ℕ} (S : LangSetup τ GGL p₀) {a : Fin τ.rank → GGLˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hp : p.Prime) (hp2 : p ≠ 2)
    (hTp : rootDiagUnit τ a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (hq : S.D.q = 2 ^ h) (hk : twistKind S.ρ (rootCharHom a) i = .twoD) :
    RCKTwoDCanonicalData S a i h := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : CharP GGL 2 := by
    change CharP (AlgebraicClosure (ZMod 2)) 2
    infer_instance
  apply Classical.choice
  obtain ⟨hτ, -⟩ := rckTwoD_graph_labelled S hT i hk
  obtain ⟨m, hm, ε, z, D, hDe, hrank, hRC, hDs, hCart, hfix, hswap, hzZ, hF⟩ :=
    rckTwoD_pinned_setup S hT i hq hk
  subst m
  have hh : 1 ≤ h := hDe ▸ D.one_le_e
  have hpos : 0 < D.e := D.one_le_e
  haveI : Finite ↥(frobeniusFixedField GGL 2 D.e) := Nat.finite_of_card_ne_zero (by
    rw [card_frobeniusFixedField hpos]
    exact (pow_pos (by decide : 0 < (2 : ℕ)) _).ne')
  letI : Fintype ↥(frobeniusFixedField GGL 2 D.e) := Fintype.ofFinite _
  letI : Fintype (GaloisField 2 h) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 2 h) = Fintype.card ↥(frobeniusFixedField GGL 2 D.e) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      GaloisField.card 2 h (by omega), card_frobeniusFixedField hpos, hDe]
  let κ : GaloisField 2 h ≃+* ↥(frobeniusFixedField GGL 2 D.e) :=
    FiniteField.ringEquivOfCardEq hcard
  have hΨ : IsRootComponent (componentRoots (rootCharHom a) i) := isRootComponent_componentRoots i
  have hsl : ∀ β ∈ componentRoots (rootCharHom a) i, iform β β = 2 := by
    intro β hβ
    rw [← dotProduct_mulVec_eq_iform]
    exact rootForm_self hτ (hΨ.isRoot β hβ)
  have hG : ∀ j k, iform (ε.symm j : Fin τ.rank → ℤ) (ε.symm k) = cartanD _ j k := by
    intro j k
    have hc := hCart (ε.symm j) (ε.symm k)
    simp only [Equiv.apply_symm_apply] at hc
    rw [← hc]
    exact (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPTwoDBase.corootPair_eq_iform
      (simpleRoots_isRoot (ε.symm j).2) (hsl _ (simpleRoots_subset (ε.symm j).2)) _).symm
  have hrange : Set.range (fun j => (ε.symm j : Fin τ.rank → ℤ)) =
      (simpleRoots (componentRoots (rootCharHom a) i) : Set (Fin τ.rank → ℤ)) := by
    ext β
    constructor
    · rintro ⟨j, rfl⟩; exact (ε.symm j).2
    · intro hβ; exact ⟨ε ⟨β, hβ⟩, by simp⟩
  have hframe := rckTwoD_dFrames hτ S hp (rck_natCast_ne_zero_GGL hp hp2) hTp i hm
    (shape_of_twistKind_twoD hk).2 ε hCart
  have hsw := hswap ⟨compRank (componentRoots (rootCharHom a) i) - 2, by omega⟩
    ⟨compRank (componentRoots (rootCharHom a) i) - 1, by omega⟩ (by simp only [Fin.val_mk]; omega)
    (by simp only [Fin.val_mk]; omega)
  haveI := CFSG.LieType.Universal.Spin.Twisted.fact_shortField (minusCoeffs_irr 2 h)
  obtain ⟨φ₀, hφ₀, hker₀, hlong⟩ := rckTwoD_exists_cover_of_datum_field hτ D hm
    (fun j => (ε.symm j : Fin τ.rank → ℤ)) (fun j => simpleRoots_isRoot (ε.symm j).2)
    (fun j k h => ε.symm.injective (Subtype.ext h)) hG (hDs.trans hrange.symm) hfix hsw.1 hsw.2
    hframe κ (minusCoeffs 2 h).1 (minusCoeffs 2 h).2 (minusCoeffs_irr 2 h)
  let φ := (MulAut.conj z).toMonoidHom.comp φ₀
  have hφ : φ.range = rationalComponent S.ρ S.Γ (rootCharHom a) i := by
    rw [MonoidHom.range_comp, hφ₀, ← hRC, Subgroup.map_map]
    have hid : (MulAut.conj z).toMonoidHom.comp (MulAut.conj z⁻¹).toMonoidHom = MonoidHom.id _ := by
      ext x : 1
      change z * (z⁻¹ * x * (z⁻¹)⁻¹) * z⁻¹ = x
      group
    rw [hid, Subgroup.map_id]
  refine ⟨⟨hm, hh, D, hDe, ε, z, κ, φ, hφ, ?_, hzZ, hDs, hfix, hF, ?_⟩⟩
  · intro x hx
    apply hker₀
    change φ₀ x = 1
    apply (MulAut.conj z).injective
    change (MulAut.conj z) (φ₀ x) = 1 at hx
    exact hx.trans (map_one (MulAut.conj z)).symm
  · intro k hk
    have h := congrArg (fun f => (MulAut.conj z).toMonoidHom.comp f) (hlong k hk)
    exact h

end CFSG.StandardType.RCKRP
