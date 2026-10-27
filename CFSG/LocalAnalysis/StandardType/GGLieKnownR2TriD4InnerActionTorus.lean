module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TriD4InnerAction
public import CFSG.LieType.Steinberg.CentralExt.TrialityTorus

public section

namespace CFSG.StandardType.LieKnownR2.TriD4.Inner

open CFSG.Open CFSG.StandardType CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.TwistedD4 CFSG.SeitzReduction
  CFSG.LieType.Steinberg.CentralExt.TrialityClosed

private theorem ttorus_chi_highRoot {K : Type} [Field K] (σ : K →+* K) (s : Kˣ) :
    chi σ s 1 (highRoot d4) = s := by
  obtain ⟨hp0, hp1, hp2, hp3⟩ := pr_eq (highRoot d4 : Fin d4.rank → ℤ)
  have h0 : (highRoot d4 : Fin d4.rank → ℤ) (nd 0) = 1 := rfl
  have h1 : (highRoot d4 : Fin d4.rank → ℤ) (nd 1) = 1 := rfl
  have h2 : (highRoot d4 : Fin d4.rank → ℤ) (nd 2) = 2 := rfl
  have h3 : (highRoot d4 : Fin d4.rank → ℤ) (nd 3) = 1 := rfl
  rw [chi, hp0, hp1, hp2, hp3, h0, h1, h2, h3]
  simp

theorem triD4_exists_torus_action
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K) (hσ3 : ∀ c, σ (σ (σ c)) = c)
    {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    (γ : (fixedField σ.toRingHom)ˣ) :
    ∃ n ∈ Subgroup.normalizer (Bridge.triD4C0HighRoot K σ.toRingHom :
        Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
      ∀ t : fixedField σ.toRingHom,
        n * triD4C0Xtheta σ t * n⁻¹ = triD4C0Xtheta σ (γ * t) := by
  have hσ' : ∀ c : K, σ.toRingHom c = c ^ (2 ^ f) := fun c => by simpa using hσ c
  let s : fixedUnits σ.toRingHom :=
    ⟨Units.map (fixedField σ.toRingHom).subtype γ, by
      rw [mem_fixedUnits (σ := σ.toRingHom)]
      change σ.toRingHom (↑↑γ) = ↑↑γ
      exact (γ.1).2⟩
  let w : twistedGroup σ.toRingHom := tor hσ3 s 1
  have hw : w ∈ hHat σ.toRingHom (ng 0) := by
    rw [hHat, Subgroup.mem_subgroupOf]
    change (w : adjointGroup d4 K) ∈ (hLongHom σ.toRingHom).range
    refine ⟨s, ?_⟩
    rw [hLongHom]
    change torusElement d4 K (nd 2) (s : Kˣ) = (w : adjointGroup d4 K)
    rw [show (w : adjointGroup d4 K) = torE σ.toRingHom (s : Kˣ) 1 from tor_val hσ3 s 1]
    rw [torE, map_one, mul_one]
  refine ⟨Bridge.triD4BridgeEquiv σ.toRingHom hf hK hσ' w, ?_, ?_⟩
  ·
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [← Bridge.triD4BridgeEquiv_twistedRootGroup_highRoot (σ := σ.toRingHom) hf hK
      hσ']
    constructor
    · intro hx
      rcases Subgroup.mem_map.1 hx with ⟨y, hy, rfl⟩
      change (Bridge.triD4BridgeEquiv σ.toRingHom hf hK hσ').toMonoidHom w *
          (Bridge.triD4BridgeEquiv σ.toRingHom hf hK hσ').toMonoidHom y *
          ((Bridge.triD4BridgeEquiv σ.toRingHom hf hK hσ').toMonoidHom w)⁻¹ ∈
        ((twistedDatum σ.toRingHom).rootGroup (highRoot .G2)).map
          (Bridge.triD4BridgeEquiv σ.toRingHom hf hK hσ').toMonoidHom
      rw [← map_inv, ← map_mul, ← map_mul]
      exact Subgroup.mem_map_of_mem _
        (hHat_conj_mem (σ := σ.toRingHom) (ng 0) (isRoot_highRoot .G2) hw hy)
    · intro hx
      rcases Subgroup.mem_map.1 hx with ⟨y, hy, hxy⟩
      refine Subgroup.mem_map.2 ⟨w⁻¹ * y * w, ?_, ?_⟩
      · exact hHat_conj_mem (σ := σ.toRingHom) (ng 0) (isRoot_highRoot .G2)
          (Subgroup.inv_mem _ hw) hy
      · rw [map_mul, map_mul, map_inv]
        rw [hxy]
        change (Bridge.triD4BridgeEquiv σ.toRingHom hf hK hσ' w)⁻¹ *
            (Bridge.triD4BridgeEquiv σ.toRingHom hf hK hσ' w * x *
              (Bridge.triD4BridgeEquiv σ.toRingHom hf hK hσ' w)⁻¹) *
            Bridge.triD4BridgeEquiv σ.toRingHom hf hK hσ' w = x
        group
  ·
    intro t
    apply Subtype.ext
    change ((Bridge.triD4BridgeEquiv σ.toRingHom hf hK hσ' w :
          graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL d4 K) *
        ((triD4C0Xtheta σ t : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL d4 K) *
        (((Bridge.triD4BridgeEquiv σ.toRingHom hf hK hσ' w :
          graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL d4 K))⁻¹ =
      ((triD4C0Xtheta σ (γ * t) : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
        ModGL d4 K)
    have hn : ((Bridge.triD4BridgeEquiv σ.toRingHom hf hK hσ' w :
        graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL d4 K) =
        (torE σ.toRingHom (s : Kˣ) 1 : ModGL d4 K) :=
      (Bridge.triD4BridgeEquiv_coe (σ := σ.toRingHom) hf hK hσ' w).trans
        (congrArg (fun g : adjointGroup d4 K => (g : ModGL d4 K)) (tor_val hσ3 s 1))
    rw [hn]
    change ((torE σ.toRingHom (s : Kˣ) 1 : adjointGroup d4 K) : ModGL d4 K) *
        ((triD4C0Xtheta σ t : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL d4 K) *
        (((torE σ.toRingHom (s : Kˣ) 1 : adjointGroup d4 K) : ModGL d4 K))⁻¹ =
      ((triD4C0Xtheta σ (γ * t) : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
        ModGL d4 K)
    change ((torE σ.toRingHom (s : Kˣ) 1 : adjointGroup d4 K) : ModGL d4 K) *
        (((xPar (rootOperatorFamily d4) (highRoot d4) (t : K)) : adjointGroup d4 K) :
          ModGL d4 K) *
        (((torE σ.toRingHom (s : Kˣ) 1 : adjointGroup d4 K) : ModGL d4 K))⁻¹ =
      (((xPar (rootOperatorFamily d4) (highRoot d4)
        ((γ * t : fixedField σ.toRingHom) : K)) : adjointGroup d4 K) : ModGL d4 K)
    change ((torE σ.toRingHom (s : Kˣ) 1 * xPar (rootOperatorFamily d4) (highRoot d4)
        (t : K) * (torE σ.toRingHom (s : Kˣ) 1)⁻¹ : adjointGroup d4 K) : ModGL d4 K) =
      ((xPar (rootOperatorFamily d4) (highRoot d4)
        ((γ * t : fixedField σ.toRingHom) : K) : adjointGroup d4 K) : ModGL d4 K)
    exact congrArg (fun g : adjointGroup d4 K => (g : ModGL d4 K)) (by
      rw [torE_conj_xPar σ.toRingHom (s : Kˣ) 1 (isRoot_highRoot d4) (t : K)]
      congr 1
      rw [ttorus_chi_highRoot]
      rfl)

end CFSG.StandardType.LieKnownR2.TriD4.Inner
