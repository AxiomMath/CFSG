module

public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergRoot
public import CFSG.LocalAnalysis.StandardType.PhanEStdFrob
public import CFSG.LieType.Steinberg.BruhatTwist
public import CFSG.LieType.Steinberg.Adjoint.Datum
public import CFSG.ClassicalInvolution.Models.TwistedPairs.Unitary
import CFSG.LieType.Chevalley.OddF4CosetDescent
public import CFSG.ClassicalInvolution.WeakCT.StandardPair

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.StandardType.AutSt
open CFSG.ClassicalInvolution.Models.TwistedPairs (involEquiv)

variable {τ : Tag} {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)

theorem adj_phi_xPar (γ : Fin τ.rank → ℤ) (c : k) :
    entrywiseAdjointAut τ (involEquiv θ hθ) (xPar (rootOperatorFamily τ) γ c) =
      xPar (rootOperatorFamily τ) γ (θ c) :=
  entrywiseAdjointAut_xPar _ _ _

private theorem q2nPE_entrywiseAdjointAut_steinberg (i : Fin τ.rank) (t : kˣ) :
    entrywiseAdjointAut τ (involEquiv θ hθ)
        (CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily τ)) i t) =
      CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily τ)) i
        (Units.map (θ : k →* k) t) := by
  unfold CFSG.LieType.Steinberg.weylElement
  simp only [map_mul, adj_phi_xPar θ hθ]
  simp [map_neg, map_inv₀, Units.coe_map, Units.val_neg, Units.val_inv_eq_inv_val]

theorem adj_phi_nm (i : Fin τ.rank) :
    entrywiseAdjointAut τ (involEquiv θ hθ) (weylElement τ k i) = weylElement τ k i := by
  rw [weylElement_eq_xPar (rootOperatorFamily τ) i,
    q2nPE_entrywiseAdjointAut_steinberg θ hθ i 1]
  simp only [map_one]

theorem adj_phi_torusElement (i : Fin τ.rank) (t : kˣ) :
    entrywiseAdjointAut τ (involEquiv θ hθ) (torusElement τ k i t) =
      torusElement τ k i (Units.map (θ : k →* k) t) := by
  have key : ∀ u : kˣ, torusElement τ k i u =
      CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily τ)) i u *
        (CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily τ)) i 1)⁻¹ := by
    intro u
    have h1 := weylElement_xPar (F := rootOperatorFamily τ) (K := k) i u
    have h2 := weylElement_xPar (F := rootOperatorFamily τ) (K := k) i 1
    have h3 : torusElement τ k i 1 = 1 := (torusHom (τ := τ) k i).map_one
    rw [h3, one_mul] at h2
    rw [h1, h2]
    group
  rw [key t, key (Units.map (θ : k →* k) t), map_mul, map_inv,
    q2nPE_entrywiseAdjointAut_steinberg θ hθ i t,
    q2nPE_entrywiseAdjointAut_steinberg θ hθ i 1]
  simp

theorem adj_phi_involutive (g : adjointGroup τ k) :
    entrywiseAdjointAut τ (involEquiv θ hθ) (entrywiseAdjointAut τ (involEquiv θ hθ) g) = g := by
  have hs : involEquiv θ hθ * involEquiv θ hθ = 1 :=
    RingEquiv.ext fun c => hθ c
  have hcomp : entrywiseAdjointAut τ (involEquiv θ hθ) *
      entrywiseAdjointAut τ (involEquiv θ hθ) = 1 := by
    rw [← entrywiseAdjointAut_mul, hs, entrywiseAdjointAut_one]
  have h := congrArg (fun f : MulAut (adjointGroup τ k) => f g) hcomp
  simpa only [MulAut.mul_apply, MulAut.one_apply] using h

theorem adj_isTwist :
    IsTwist (adjDatum (rootOperatorFamily τ) k) (weylElement τ k) (Adjoint.torus (τ := τ) k) 1
      (entrywiseAdjointAut τ (involEquiv θ hθ)).toMonoidHom where
  cartan_perm _ _ := rfl
  divisible_perm _ h := h
  map_rootGroup γ hγ x hx := by
    rw [mem_adjDatum_roots] at hγ
    change x ∈ rootGroup (rootOperatorFamily τ) k γ at hx
    change entrywiseAdjointAut τ (involEquiv θ hθ) x ∈
      rootGroup (rootOperatorFamily τ) k (permVec 1 γ)
    obtain ⟨c, rfl⟩ := (mem_rootGroup_iff hγ x).1 hx
    rw [adj_phi_xPar θ hθ]
    exact xPar_mem hγ (θ c)
  map_n i := by
    change entrywiseAdjointAut τ (involEquiv θ hθ) (weylElement τ k i) = weylElement τ k i
    exact adj_phi_nm θ hθ i
  map_torus i h hh := by
    obtain ⟨t, rfl⟩ := mem_torus.1 hh
    change entrywiseAdjointAut τ (involEquiv θ hθ) (torusElement τ k i t) ∈
      Adjoint.torus (τ := τ) k i
    rw [adj_phi_torusElement θ hθ]
    exact mem_torus.2 ⟨Units.map (θ : k →* k) t, rfl⟩

@[expose] noncomputable def adjFrobData
    {w₀ : (coxeterMatrix (adjDatum (rootOperatorFamily τ) k).isFiniteType).Group}
    (hop : ∀ i, w₀ *
      (coxeterMatrix (adjDatum (rootOperatorFamily τ) k).isFiniteType).toCoxeterSystem.simple i *
        w₀ = (coxeterMatrix (adjDatum (rootOperatorFamily τ) k).isFiniteType).toCoxeterSystem.simple
          i) :
    FrobData (adjDatum (rootOperatorFamily τ) k) (weylElement τ k) (Adjoint.torus (τ := τ) k)
      w₀ where
  φ := (entrywiseAdjointAut τ (involEquiv θ hθ)).toMonoidHom
  invol := adj_phi_involutive θ hθ
  op := id
  hop := hop
  pos := by
    rintro _ ⟨u, hu, rfl⟩
    exact (adj_isTwist θ hθ).map_posUnipotent hu
  torus := by
    rintro _ ⟨t, ht, rfl⟩
    exact (adj_isTwist θ hθ).map_iSup_torus ht
  n_map i := (adj_isTwist θ hθ).map_n i

end CFSG.ClassicalInvolution.Phan.PhanE
