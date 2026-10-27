module

public import CFSG.LocalAnalysis.StandardType.GGTBTorRelDNsTorus
public import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenWeyl

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType

namespace RelDNs

open Polynomial QuadraticMap Module
open CFSG.RankThree.Classical2 CFSG.LocalAnalysis.GLTheoremA.S172C.Cent CFSG.Open
open CFSG.StandardType.OmNsRootGen
open CFSG.ClassicalGroups.Orthogonal

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p k : ℕ} {U : Fin k → Submodule F V}
  {e : Fin k → ↥(orthDerived Q)} {E : Subgroup ↥(orthDerived Q)} {u : Fin k → V} {c t : F}
  {a b : Fin k}

variable [Fact (Irreducible (OmNsRootGen.framePoly t))]

private theorem frameSwap_mapsTo_left (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t)
    (hab : a ≠ b) {x : V} (hx : x ∈ U a) :
    frameSwap Q e u c t a b x ∈ U b := by
  classical
  obtain ⟨r, s, hcoord⟩ := exists_coord hF a ⟨x, hx⟩
  have hx' : x = r • u a + s • (e a : V ≃ₗ[F] V) (u a) := by
    have h := congrArg Subtype.val hcoord
    simpa [frameU, frameEU] using h
  rw [hx', map_add, map_smul, map_smul, frameSwap_apply_left hF hab,
    frameSwap_apply_e_left hF hab]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (hF.mem b))
    (Submodule.smul_mem _ _ (frameEU hF b).2)

private theorem frameSwap_mapsTo_right (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t)
    (hab : a ≠ b) {x : V} (hx : x ∈ U b) :
    frameSwap Q e u c t a b x ∈ U a := by
  classical
  obtain ⟨r, s, hcoord⟩ := exists_coord hF b ⟨x, hx⟩
  have hx' : x = r • u b + s • (e b : V ≃ₗ[F] V) (u b) := by
    have h := congrArg Subtype.val hcoord
    simpa [frameU, frameEU] using h
  rw [hx', map_add, map_smul, map_smul, frameSwap_apply_right hF hab,
    frameSwap_apply_e_right hF hab]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (hF.mem a))
    (Submodule.smul_mem _ _ (frameEU hF a).2)

private theorem frameSwap_fixes (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t)
    (hab : a ≠ b) {j : Fin k} (hja : j ≠ a) (hjb : j ≠ b) {x : V} (hx : x ∈ U j) :
    frameSwap Q e u c t a b x = x := by
  refine frameSwap_apply_of_mem_polarPerp hF ?_
  rw [mem_polarPerp_iff]
  intro y hy
  obtain ⟨ya, hya, yb, hyb, rfl⟩ := Submodule.mem_sup.1 hy
  rw [polar_add_left]
  have h1 : polar Q ya x = 0 := hF.perp a j hja.symm ya hya x hx
  have h2 : polar Q yb x = 0 := hF.perp b j hjb.symm yb hyb x hx
  rw [h1, h2, add_zero]

private theorem frameSwap_mapsTo_swap (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t)
    (hab : a ≠ b) (j : Fin k) {x : V} (hx : x ∈ U j) :
    frameSwap Q e u c t a b x ∈ U (Equiv.swap a b j) := by
  by_cases hja : j = a
  · subst hja
    rw [Equiv.swap_apply_left]
    exact frameSwap_mapsTo_left hF hab hx
  · by_cases hjb : j = b
    · subst hjb
      rw [Equiv.swap_apply_right]
      exact frameSwap_mapsTo_right hF hab hx
    · rw [Equiv.swap_apply_of_ne_of_ne hja hjb, frameSwap_fixes hF hab hja hjb hx]
      exact hx

private theorem planeEnd_mul_add (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t)
    (a : Fin k) : planeEnd hF a * (planeEnd hF a + t • 1) = 1 := by
  have ht : planeAlg hF a ((AdjoinRoot.of (OmNsRootGen.framePoly t)) t) = t • 1 := by
    rw [← AdjoinRoot.algebraMap_eq, AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
  have h := congrArg (planeAlg hF a) (root_mul_add (F := F) (t := t))
  rw [map_mul, planeAlg_root, map_add, planeAlg_root, map_one] at h
  simpa [ht] using h

private theorem planeEquiv_inv_apply (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t)
    (a : Fin k) (x : ↥(U a)) :
    ((planeEquiv hF a)⁻¹) x = (planeEnd hF a + t • 1) x := by
  have hrel := planeEnd_mul_add hF a
  refine (LinearEquiv.symm_apply_eq (planeEquiv hF a)).2 ?_
  show x = planeEquiv hF a ((planeEnd hF a + t • 1) x)
  rw [show (planeEquiv hF a) ((planeEnd hF a + t • 1) x) =
      planeEnd hF a ((planeEnd hF a + t • 1) x) from rfl]
  rw [← Module.End.mul_apply, hrel, Module.End.one_apply]

private theorem e_inv_apply_mem (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t)
    (a : Fin k) {x : V} (hx : x ∈ U a) :
    ((e a : V ≃ₗ[F] V)⁻¹) x = (((planeEnd hF a + t • 1) ⟨x, hx⟩ : ↥(U a)) : V) := by
  rw [show ((e a : V ≃ₗ[F] V)⁻¹) x =
      (((planeEquiv hF a)⁻¹ ⟨x, hx⟩ : ↥(U a)) : V) from by
    refine (LinearEquiv.symm_apply_eq (e a : V ≃ₗ[F] V)).2 ?_
    show x = (e a : V ≃ₗ[F] V) (((planeEquiv hF a)⁻¹ ⟨x, hx⟩ : ↥(U a)) : V)
    rw [← planeEquiv_apply hF a]
    exact (congrArg Subtype.val ((planeEquiv hF a).apply_symm_apply ⟨x, hx⟩)).symm]
  rw [planeEquiv_inv_apply]

private theorem frameSwap_planeAlg (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t)
    (hab : a ≠ b) (z : normOne t) {x : V} (hx : x ∈ U a) :
    frameSwap Q e u c t a b ((planeAlg hF a (normOneVal (F := F) (t := t) z)
        ⟨x, hx⟩ : ↥(U a)) : V) =
      ((planeAlg hF b (normOneVal (F := F) (t := t) z)
        ⟨frameSwap Q e u c t a b x, frameSwap_mapsTo_left hF hab hx⟩ : ↥(U b)) : V) := by
  classical
  obtain ⟨α, β, hz⟩ := exists_coord_field (F := F) (t := t)
    (normOneVal (F := F) (t := t) z)
  have hcoeff_a : planeAlg hF a (normOneVal (F := F) (t := t) z) =
      α • 1 + β • planeEnd hF a := by
    rw [hz, map_add, map_smul, map_smul, map_one, planeAlg_root]
  have hcoeff_b : planeAlg hF b (normOneVal (F := F) (t := t) z) =
      α • 1 + β • planeEnd hF b := by
    rw [hz, map_add, map_smul, map_smul, map_one, planeAlg_root]
  have hss : frameSwap Q e u c t a b (frameSwap Q e u c t a b x) = x := by
    have h := congrArg (fun f : V ≃ₗ[F] V => f x)
      (frameSwap_mul_self (Q := Q) (e := e) (u := u) (c := c) (t := t) (a := a) (b := b) hF hab)
    simpa [LinearEquiv.mul_apply] using h
  have hconj : frameSwap Q e u c t a b ((e a : V ≃ₗ[F] V) x) =
      (e b : V ≃ₗ[F] V) (frameSwap Q e u c t a b x) := by
    have h := congrArg (fun f : V ≃ₗ[F] V => f (frameSwap Q e u c t a b x))
      (frameSwap_conj_left (Q := Q) (e := e) (u := u) (c := c) (t := t) (a := a) (b := b)
        hF hab)
    rwa [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hss] at h
  have hL : ((α • 1 + β • planeEnd hF a) ⟨x, hx⟩ : V) =
      α • x + β • (e a : V ≃ₗ[F] V) x := by
    simp [planeEnd_apply]
  have hR : ((α • 1 + β • planeEnd hF b)
      ⟨frameSwap Q e u c t a b x, frameSwap_mapsTo_left hF hab hx⟩ : V) =
      α • frameSwap Q e u c t a b x + β • (e b : V ≃ₗ[F] V) (frameSwap Q e u c t a b x) := by
    simp [planeEnd_apply]
  rw [hcoeff_a, hcoeff_b, hL, hR, map_add, map_smul, map_smul, hconj]

private theorem planeRot_eq_extU (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t)
    (a : Fin k) (z : normOne t) :
    planeRot hF a z =
      CFSG.LieType.SeitzGeneration.OrthNS.extU (planeNondeg hF a) (planeLinEquiv hF a z) := by
  refine (CFSG.LieType.SeitzGeneration.OrthNS.extU_eq_of_agree (planeNondeg hF a) ?_ ?_).symm
  · intro w
    rw [planeRot_apply_mem hF a z w.2, planeLinEquiv_apply]
  · intro r hr
    rw [mem_orthBlk_perp_iff] at hr
    rw [planeRot_apply_perp hF a z hr]

theorem frameSwap_conj_planeRot (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t)
    (hab : a ≠ b) (z : normOne t) :
    frameSwap Q e u c t a b * planeRot hF a z * (frameSwap Q e u c t a b)⁻¹ =
      planeRot hF b z := by
  classical
  have hs2 : frameSwap Q e u c t a b * frameSwap Q e u c t a b = 1 :=
    frameSwap_mul_self (Q := Q) (e := e) (u := u) (c := c) (t := t) (a := a) (b := b) hF hab
  have hsinv : (frameSwap Q e u c t a b)⁻¹ = frameSwap Q e u c t a b :=
    (eq_inv_of_mul_eq_one_left hs2).symm
  have hsO : frameSwap Q e u c t a b ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    frameSwap_mem_orthogonalGroup (Q := Q) (e := e) (u := u) (c := c) (t := t) (a := a) (b := b)
  rw [planeRot_eq_extU hF b z]
  refine (CFSG.LieType.SeitzGeneration.OrthNS.extU_eq_of_agree (planeNondeg hF b) ?_ ?_).symm
  · intro x
    rw [hsinv, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    have hsx : frameSwap Q e u c t a b (x : V) ∈ U a := frameSwap_mapsTo_right hF hab x.2
    rw [planeRot_apply_mem hF a z hsx]
    rw [show ((planeLinEquiv hF b z x : ↥(U b)) : V) =
      ((planeAlg hF b (normOneVal (F := F) (t := t) z) x : ↥(U b)) : V) from by
        rw [planeLinEquiv_apply]]
    rw [frameSwap_planeAlg hF hab z hsx]
    have hss : frameSwap Q e u c t a b (frameSwap Q e u c t a b (x : V)) = (x : V) := by
      have h := congrArg (fun f : V ≃ₗ[F] V => f (x : V)) hs2
      simpa [LinearEquiv.mul_apply] using h
    rw [show (⟨frameSwap Q e u c t a b (frameSwap Q e u c t a b (x : V)),
        frameSwap_mapsTo_left hF hab hsx⟩ : ↥(U b)) = x from Subtype.ext hss]
  · intro r hr
    rw [mem_orthBlk_perp_iff] at hr
    rw [hsinv, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    have hsr : frameSwap Q e u c t a b r ∈ polarPerp Q (U a) := by
      rw [mem_polarPerp_iff]
      intro y hy
      have hsy : frameSwap Q e u c t a b y ∈ U b := frameSwap_mapsTo_left hF hab hy
      have hssy : frameSwap Q e u c t a b (frameSwap Q e u c t a b y) = y := by
        have h := congrArg (fun f : V ≃ₗ[F] V => f y) hs2
        simpa [LinearEquiv.mul_apply] using h
      calc polar Q y (frameSwap Q e u c t a b r)
          = polar Q (frameSwap Q e u c t a b (frameSwap Q e u c t a b y))
              (frameSwap Q e u c t a b r) := by rw [hssy]
        _ = polar Q (frameSwap Q e u c t a b y) r :=
              TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hsO _ _
        _ = 0 := mem_polarPerp_iff.1 hr _ hsy
    rw [planeRot_apply_perp hF a z hsr]
    have hss : frameSwap Q e u c t a b (frameSwap Q e u c t a b r) = r := by
      have h := congrArg (fun f : V ≃ₗ[F] V => f r) hs2
      simpa [LinearEquiv.mul_apply] using h
    exact hss

theorem frameSwap_conj_planeRot_right (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t)
    (hab : a ≠ b) (z : normOne t) :
    frameSwap Q e u c t a b * planeRot hF b z * (frameSwap Q e u c t a b)⁻¹ =
      planeRot hF a z := by
  rw [show frameSwap Q e u c t a b = frameSwap Q e u c t b a from by
    rw [frameSwap, frameSwap, add_comm (u a), add_comm ((e a : V ≃ₗ[F] V) (u a))]]
  exact frameSwap_conj_planeRot hF hab.symm z

theorem frameSwap_conj_planeRot_of_ne (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t)
    (hab : a ≠ b) {j : Fin k} (hja : j ≠ a) (hjb : j ≠ b) (z : normOne t) :
    frameSwap Q e u c t a b * planeRot hF j z * (frameSwap Q e u c t a b)⁻¹ =
      planeRot hF j z := by
  have hs2 : frameSwap Q e u c t a b * frameSwap Q e u c t a b = 1 :=
    frameSwap_mul_self (Q := Q) (e := e) (u := u) (c := c) (t := t) (a := a) (b := b) hF hab
  have hsinv : (frameSwap Q e u c t a b)⁻¹ = frameSwap Q e u c t a b :=
    (eq_inv_of_mul_eq_one_left hs2).symm
  have hsO : frameSwap Q e u c t a b ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    frameSwap_mem_orthogonalGroup (Q := Q) (e := e) (u := u) (c := c) (t := t) (a := a) (b := b)
  have hfix : ∀ x ∈ U j, frameSwap Q e u c t a b x = x := fun x hx =>
    frameSwap_fixes hF hab hja hjb hx
  have hcomm := extU_commute_of_fixes (hU := planeNondeg hF j) hsO hfix (planeLinEquiv hF j z)
  rw [hsinv, planeRot_eq_extU hF j z]
  rw [← hcomm, mul_assoc, hs2, mul_one]

private theorem frameSwap_conj_planeRot_swap (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t)
    (hab : a ≠ b) (j : Fin k) (z : normOne t) :
    frameSwap Q e u c t a b * planeRot hF j z * (frameSwap Q e u c t a b)⁻¹ =
      planeRot hF (Equiv.swap a b j) z := by
  by_cases hja : j = a
  · subst hja
    rw [Equiv.swap_apply_left]
    exact frameSwap_conj_planeRot hF hab z
  · by_cases hjb : j = b
    · subst hjb
      rw [Equiv.swap_apply_right]
      exact frameSwap_conj_planeRot_right hF hab z
    · rw [Equiv.swap_apply_of_ne_of_ne hja hjb]
      exact frameSwap_conj_planeRot_of_ne hF hab hja hjb z

private theorem signChange_mapsTo_self (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t)
    {v : V} (hv : v ∈ polarPerp Q (⨆ j, U j)) {x : V} (hx : x ∈ U a) :
    signChange Q u v a x ∈ U a := by
  have hvx : polar Q v x = 0 := by
    rw [polar_comm]
    exact mem_polarPerp_iff.1 hv x (le_iSup U a hx)
  have hρv : reflect Q v x = x := reflect_apply_of_polar_eq_zero hvx
  rw [signChange, LinearEquiv.mul_apply, hρv,
    reflect_apply (by rw [hF.quad_eq a]; exact hF.c_ne_zero)]
  exact Submodule.sub_mem _ hx (Submodule.smul_mem _ _ (hF.mem a))

private theorem signChange_fixes_of_ne (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t)
    {v : V} (hv : v ∈ polarPerp Q (⨆ j, U j)) {j : Fin k} (hja : j ≠ a) {x : V}
    (hx : x ∈ U j) : signChange Q u v a x = x := by
  have hvx : polar Q v x = 0 := by
    rw [polar_comm]
    exact mem_polarPerp_iff.1 hv x (le_iSup U j hx)
  have hρv : reflect Q v x = x := reflect_apply_of_polar_eq_zero hvx
  have huax : polar Q (u a) x = 0 := by
    rw [polar_comm]
    exact hF.perp j a hja x hx (u a) (hF.mem a)
  have hρu : reflect Q (u a) x = x := reflect_apply_of_polar_eq_zero huax
  rw [signChange, LinearEquiv.mul_apply, hρv, hρu]

private theorem signChange_mapsTo (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t)
    {v : V} (hv : v ∈ polarPerp Q (⨆ j, U j)) (j : Fin k) {x : V} (hx : x ∈ U j) :
    signChange Q u v a x ∈ U j := by
  by_cases hja : j = a
  · subst hja
    exact signChange_mapsTo_self hF hv hx
  · rw [signChange_fixes_of_ne hF hv hja hx]
    exact hx

private theorem signChange_mapsTo_perp (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t)
    {v : V} (hv : v ∈ polarPerp Q (⨆ j, U j)) {z : V}
    (hz : z ∈ polarPerp Q (⨆ j, U j)) :
    signChange Q u v a z ∈ polarPerp Q (⨆ j, U j) := by
  have hvfix : ∀ y ∈ (⨆ j, U j), reflect Q v y = y := by
    intro y hy
    refine Submodule.iSup_induction U (motive := fun y => reflect Q v y = y) hy ?_ ?_ ?_
    · intro j y hy
      exact reflect_apply_of_polar_eq_zero (by
        rw [polar_comm]
        exact mem_polarPerp_iff.1 hv y (le_iSup U j hy))
    · simp
    · intro x y hx hy
      rw [map_add, hx, hy]
  have hρv_perp : reflect Q v z ∈ polarPerp Q (⨆ j, U j) := by
    rw [mem_polarPerp_iff]
    intro y hy
    calc polar Q y (reflect Q v z)
        = polar Q (reflect Q v y) (reflect Q v z) := by rw [hvfix y hy]
      _ = polar Q y z := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup
            (reflect_mem_orthogonalGroup Q v) y z
      _ = 0 := mem_polarPerp_iff.1 hz y hy
  have hρu : reflect Q (u a) (reflect Q v z) = reflect Q v z :=
    reflect_apply_of_polar_eq_zero
      (mem_polarPerp_iff.1 hρv_perp (u a) (le_iSup U a (hF.mem a)))
  rw [signChange, LinearEquiv.mul_apply, hρu]
  exact hρv_perp

private theorem normOneVal_inv_coord (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t)
    (a : Fin k) {z : normOne t} {α β : F}
    (hz : normOneVal (F := F) (t := t) z = α • (1 : FrameField t) +
      β • AdjoinRoot.root (OmNsRootGen.framePoly t)) :
    normOneVal (F := F) (t := t) z⁻¹ =
      (α + t * β) • (1 : FrameField t) +
        β • AdjoinRoot.root (OmNsRootGen.framePoly t) := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  let K := FrameField t
  let θ : K := AdjoinRoot.root (OmNsRootGen.framePoly t)
  have hval : normOneVal (F := F) (t := t) z⁻¹ =
      (normOneVal (F := F) (t := t) z)⁻¹ := by
    simp [normOneVal]
  have hpow : (α • (1 : K) + β • θ) ^ Nat.card F =
      α • (1 : K) + β • (θ + t) := by
    let φ : K →ₐ[F] K := FiniteField.frobeniusAlgHom F K
    have hφ : ∀ w : K, φ w = w ^ Nat.card F := by
      intro w
      rw [FiniteField.frobeniusAlgHom_apply, Nat.card_eq_fintype_card]
    have hφθ : φ θ = θ + t := by
      rw [hφ θ]
      exact root_pow_card_eq_add (F := F) (t := t)
    rw [← hφ, map_add, map_smul, map_smul, map_one, hφθ]
  have hprod : (α • (1 : K) + β • θ) * (α • (1 : K) + β • (θ + t)) = 1 := by
    have h := mul_pow_card_coord (F := F) (t := t) α β
    rw [hpow, norm_coord_eq_one hF a z hz, map_one] at h
    exact h
  have hfin : α • (1 : K) + β • (θ + t) = (α • (1 : K) + β • θ)⁻¹ :=
    eq_inv_of_mul_eq_one_right hprod
  rw [hval, hz, ← hfin, smul_add, add_smul]
  have hbt : β • (t : K) = (t * β) • (1 : K) := by
    rw [Algebra.smul_def, Algebra.smul_def, mul_one,
      show (t : K) = algebraMap F K t from rfl, ← map_mul, mul_comm]
  rw [hbt]
  abel

private theorem signChange_planeAlg (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t)
    {v : V} (hv : v ∈ polarPerp Q (⨆ j, U j)) (z : normOne t) {y : V} (hy : y ∈ U a) :
    signChange Q u v a ((planeAlg hF a (normOneVal (F := F) (t := t) z)
        ⟨y, hy⟩ : ↥(U a)) : V) =
      ((planeAlg hF a (normOneVal (F := F) (t := t) z⁻¹)
        ⟨signChange Q u v a y, signChange_mapsTo_self hF hv hy⟩ : ↥(U a)) : V) := by
  classical
  obtain ⟨α, β, hz⟩ := exists_coord_field (F := F) (t := t)
    (normOneVal (F := F) (t := t) z)
  have hcoeff : planeAlg hF a (normOneVal (F := F) (t := t) z) =
      α • 1 + β • planeEnd hF a := by
    rw [hz, map_add, map_smul, map_smul, map_one, planeAlg_root]
  have hcoeff_inv : planeAlg hF a (normOneVal (F := F) (t := t) z⁻¹) =
      α • 1 + β • (planeEnd hF a + t • 1) := by
    rw [normOneVal_inv_coord hF a hz, map_add, map_smul, map_smul, map_one, planeAlg_root]
    rw [smul_add, smul_smul, add_smul, mul_comm t β]
    abel
  have hσσ : signChange Q u v a (signChange Q u v a y) = y := by
    have h := congrArg (fun f : V ≃ₗ[F] V => f y)
      (signChange_mul_self (hF := hF) (hv := hv) (a := a))
    simpa [LinearEquiv.mul_apply] using h
  have hconj : signChange Q u v a ((e a : V ≃ₗ[F] V) y) =
      (e a : V ≃ₗ[F] V)⁻¹ (signChange Q u v a y) := by
    have h := congrArg (fun f : V ≃ₗ[F] V => f (signChange Q u v a y))
      (signChange_conj_self (hF := hF) (hv := hv) (a := a))
    rwa [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hσσ] at h
  have hL : ((α • 1 + β • planeEnd hF a) ⟨y, hy⟩ : V) =
      α • y + β • (e a : V ≃ₗ[F] V) y := by
    simp [planeEnd_apply]
  have hR : ((α • 1 + β • (planeEnd hF a + t • 1))
      ⟨signChange Q u v a y, signChange_mapsTo_self hF hv hy⟩ : V) =
      α • signChange Q u v a y +
        β • ((e a : V ≃ₗ[F] V)⁻¹ (signChange Q u v a y)) := by
    have h1 : (((planeEnd hF a + t • 1)
        ⟨signChange Q u v a y, signChange_mapsTo_self hF hv hy⟩ : ↥(U a)) : V) =
        (e a : V ≃ₗ[F] V)⁻¹ (signChange Q u v a y) := by
      rw [e_inv_apply_mem hF a (signChange_mapsTo_self hF hv hy)]
    calc ((α • 1 + β • (planeEnd hF a + t • 1))
          ⟨signChange Q u v a y, signChange_mapsTo_self hF hv hy⟩ : V)
        = α • (signChange Q u v a y) +
            β • (((planeEnd hF a + t • 1)
              ⟨signChange Q u v a y, signChange_mapsTo_self hF hv hy⟩ : ↥(U a)) : V) := by
          simp [planeEnd_apply]
      _ = α • signChange Q u v a y +
            β • ((e a : V ≃ₗ[F] V)⁻¹ (signChange Q u v a y)) := by rw [h1]
  rw [hcoeff, hcoeff_inv, hL, hR, map_add, map_smul, map_smul, hconj]

theorem signChange_conj_planeRot (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t)
    {v : V} (hv : v ∈ polarPerp Q (⨆ j, U j)) (hQv : Q v ≠ 0) (z : normOne t) :
    signChange Q u v a * planeRot hF a z * (signChange Q u v a)⁻¹ =
      planeRot hF a z⁻¹ := by
  classical
  have hσ2 : signChange Q u v a * signChange Q u v a = 1 := signChange_mul_self hF hv
  have hσinv : (signChange Q u v a)⁻¹ = signChange Q u v a :=
    (eq_inv_of_mul_eq_one_left hσ2).symm
  rw [planeRot_eq_extU hF a z⁻¹]
  refine (CFSG.LieType.SeitzGeneration.OrthNS.extU_eq_of_agree (planeNondeg hF a) ?_ ?_).symm
  · intro x
    rw [hσinv, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    have hσx : signChange Q u v a (x : V) ∈ U a := signChange_mapsTo_self hF hv x.2
    rw [planeRot_apply_mem hF a z hσx]
    rw [show ((planeLinEquiv hF a z⁻¹ x : ↥(U a)) : V) =
      ((planeAlg hF a (normOneVal (F := F) (t := t) z⁻¹) x : ↥(U a)) : V) from by
        rw [planeLinEquiv_apply]]
    rw [signChange_planeAlg hF hv z hσx]
    have hσσ : signChange Q u v a (signChange Q u v a (x : V)) = (x : V) := by
      have h := congrArg (fun f : V ≃ₗ[F] V => f (x : V)) hσ2
      simpa [LinearEquiv.mul_apply] using h
    rw [show (⟨signChange Q u v a (signChange Q u v a (x : V)),
        signChange_mapsTo_self hF hv hσx⟩ : ↥(U a)) = x from Subtype.ext hσσ]
  · intro r hr
    rw [mem_orthBlk_perp_iff] at hr
    rw [hσinv, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    have hσr : signChange Q u v a r ∈ polarPerp Q (U a) := by
      rw [mem_polarPerp_iff]
      intro y hy
      have hσy : signChange Q u v a y ∈ U a := signChange_mapsTo_self hF hv hy
      have hσσy : signChange Q u v a (signChange Q u v a y) = y := by
        have h := congrArg (fun f : V ≃ₗ[F] V => f y) hσ2
        simpa [LinearEquiv.mul_apply] using h
      have hσO : signChange Q u v a ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
        rw [signChange]
        exact Subgroup.mul_mem _ (reflect_mem_orthogonalGroup Q (u a))
          (reflect_mem_orthogonalGroup Q v)
      calc polar Q y (signChange Q u v a r)
          = polar Q (signChange Q u v a (signChange Q u v a y))
              (signChange Q u v a r) := by rw [hσσy]
        _ = polar Q (signChange Q u v a y) r :=
              TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hσO _ _
        _ = 0 := mem_polarPerp_iff.1 hr _ hσy
    rw [planeRot_apply_perp hF a z hσr]
    have hσσ : signChange Q u v a (signChange Q u v a r) = r := by
      have h := congrArg (fun f : V ≃ₗ[F] V => f r) hσ2
      simpa [LinearEquiv.mul_apply] using h
    exact hσσ

theorem signChange_conj_planeRot_of_ne (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t)
    {v : V} (hv : v ∈ polarPerp Q (⨆ j, U j)) {j : Fin k} (hj : j ≠ a) (z : normOne t) :
    signChange Q u v a * planeRot hF j z * (signChange Q u v a)⁻¹ = planeRot hF j z := by
  have hσ2 : signChange Q u v a * signChange Q u v a = 1 := signChange_mul_self hF hv
  have hσinv : (signChange Q u v a)⁻¹ = signChange Q u v a :=
    (eq_inv_of_mul_eq_one_left hσ2).symm
  have hσO : signChange Q u v a ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [signChange]
    exact Subgroup.mul_mem _ (reflect_mem_orthogonalGroup Q (u a))
      (reflect_mem_orthogonalGroup Q v)
  have hfix : ∀ x ∈ U j, signChange Q u v a x = x := fun x hx =>
    signChange_fixes_of_ne hF hv hj hx
  have hcomm := extU_commute_of_fixes (hU := planeNondeg hF j) hσO hfix (planeLinEquiv hF j z)
  rw [hσinv, planeRot_eq_extU hF j z]
  rw [← hcomm, mul_assoc, hσ2, mul_one]

theorem frameSwap_conj_frameTorusFull (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule F V, Module.finrank F T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {ℓ : ℕ} (hdim : Module.finrank F V = 2 * ℓ) (hℓ : 3 ≤ ℓ) (hab : a ≠ b)
    (x : Fin k → normOne t) :
    (⟨frameSwap Q e u c t a b, frameSwap_mem_orthDerived hQ hdim hℓ⟩ :
        ↥(orthDerived Q)) *
      frameTorusFull hF hQ hT x *
      (⟨frameSwap Q e u c t a b, frameSwap_mem_orthDerived hQ hdim hℓ⟩ :
        ↥(orthDerived Q))⁻¹ =
      frameTorusFull hF hQ hT (x ∘ Equiv.swap a b) := by
  classical
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  let s : V ≃ₗ[F] V := frameSwap Q e u c t a b
  let T : V ≃ₗ[F] V := (frameTorusFull hF hQ hT x : ↥(orthDerived Q))
  let R : V ≃ₗ[F] V := (frameTorusFull hF hQ hT (x ∘ Equiv.swap a b) : ↥(orthDerived Q))
  change s * T * (frameSwap Q e u c t a b)⁻¹ = R
  have hs2 : s * s = 1 := frameSwap_mul_self hF hab
  have hsinv : s⁻¹ = s := (eq_inv_of_mul_eq_one_left hs2).symm
  rw [hsinv]
  have hss : ∀ y : V, s (s y) = y := fun y => by
    have h := congrArg (fun f : V ≃ₗ[F] V => f y) hs2
    simpa [LinearEquiv.mul_apply] using h
  have hU : ∀ (j : Fin k) (w : V), w ∈ U j → (s * T * s) w = R w := by
    intro j w hw
    have hsw : s w ∈ U (Equiv.swap a b j) := frameSwap_mapsTo_swap hF hab j hw
    have hTsw : T (s w) = planeRot hF (Equiv.swap a b j) (x (Equiv.swap a b j)) (s w) := by
      have h := frameTorusFull_apply_mem hF hQ hT x (Equiv.swap a b j) hsw
      simpa [T] using h
    have hRw : R w = planeRot hF j (x (Equiv.swap a b j)) w := by
      have h := frameTorusFull_apply_mem hF hQ hT (x ∘ Equiv.swap a b) j hw
      simpa [R] using h
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hTsw]
    have hstep : s (planeRot hF (Equiv.swap a b j) (x (Equiv.swap a b j)) (s w)) =
        (s * planeRot hF (Equiv.swap a b j) (x (Equiv.swap a b j)) * s) w := by
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    rw [hstep]
    have hconj := frameSwap_conj_planeRot_swap hF hab (Equiv.swap a b j)
      (x (Equiv.swap a b j))
    rw [Equiv.swap_apply_self] at hconj
    rw [hsinv] at hconj
    rw [hconj, hRw]
  have hall : ∀ u ∈ (⨆ j, U j), (s * T * s) u = R u := by
    intro u hu
    refine Submodule.iSup_induction U (motive := fun u => (s * T * s) u = R u) hu
      (fun j w hw => hU j w hw) ?_ ?_
    · rw [map_zero, map_zero]
    · intro y z hy hz
      rw [map_add, map_add, hy, hz]
  have hfixL : ∀ z ∈ polarPerp Q (⨆ j, U j), (s * T * s) z = z := by
    intro z hz
    have hsz : s z = z := by
      refine frameSwap_apply_of_mem_polarPerp hF ?_
      rw [mem_polarPerp_iff]
      intro y hy
      obtain ⟨ya, hya, yb, hyb, rfl⟩ := Submodule.mem_sup.1 hy
      rw [polar_add_left]
      have h1 : polar Q ya z = 0 := mem_polarPerp_iff.1 hz ya (le_iSup U a hya)
      have h2 : polar Q yb z = 0 := mem_polarPerp_iff.1 hz yb (le_iSup U b hyb)
      rw [h1, h2, add_zero]
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hsz,
      frameTorusFull_apply_perp hF hQ hT x hz, hsz]
  have hfixR : ∀ z ∈ polarPerp Q (⨆ j, U j), R z = z := by
    intro z hz
    have h := frameTorusFull_apply_perp hF hQ hT (x ∘ Equiv.swap a b) hz
    simpa [R] using h
  ext w
  obtain ⟨u, hu, z, hz, rfl⟩ := Submodule.mem_sup.1
    (hF.isCompl_iSup.sup_eq_top ▸ Submodule.mem_top (x := w))
  rw [map_add, map_add, hall u hu, hfixL z hz, hfixR z hz]

theorem signChange_conj_frameTorusFull (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule F V, Module.finrank F T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {v : V} (hv : v ∈ polarPerp Q (⨆ j, U j)) (hQv : Q v ≠ 0) (a : Fin k)
    (x : Fin k → normOne t) :
    (⟨signChange Q u v a, signChange_mem_orthDerived hQ hF hQv⟩ : ↥(orthDerived Q)) *
      frameTorusFull hF hQ hT x *
      (⟨signChange Q u v a, signChange_mem_orthDerived hQ hF hQv⟩ :
        ↥(orthDerived Q))⁻¹ =
      frameTorusFull hF hQ hT (Function.update x a (x a)⁻¹) := by
  classical
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  let σ : V ≃ₗ[F] V := signChange Q u v a
  let T : V ≃ₗ[F] V := (frameTorusFull hF hQ hT x : ↥(orthDerived Q))
  let R : V ≃ₗ[F] V :=
    (frameTorusFull hF hQ hT (Function.update x a (x a)⁻¹) : ↥(orthDerived Q))
  change σ * T * (signChange Q u v a)⁻¹ = R
  have hσ2 : σ * σ = 1 := signChange_mul_self hF hv
  have hσinv : σ⁻¹ = σ := (eq_inv_of_mul_eq_one_left hσ2).symm
  rw [hσinv]
  have hσσ : ∀ y : V, σ (σ y) = y := fun y => by
    have h := congrArg (fun f : V ≃ₗ[F] V => f y) hσ2
    simpa [LinearEquiv.mul_apply] using h
  have hU : ∀ (j : Fin k) (w : V), w ∈ U j → (σ * T * σ) w = R w := by
    intro j w hw
    have hσw : σ w ∈ U j := signChange_mapsTo hF hv j hw
    have hTσw : T (σ w) = planeRot hF j (x j) (σ w) := by
      have h := frameTorusFull_apply_mem hF hQ hT x j hσw
      simpa [T] using h
    have hRw : R w = planeRot hF j ((Function.update x a (x a)⁻¹) j) w := by
      have h := frameTorusFull_apply_mem hF hQ hT (Function.update x a (x a)⁻¹) j hw
      simpa [R] using h
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hTσw]
    have hstep : σ (planeRot hF j (x j) (σ w)) =
        (σ * planeRot hF j (x j) * σ) w := by
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    rw [hstep]
    by_cases hja : j = a
    · rw [hja] at hRw ⊢
      have hconj := signChange_conj_planeRot (hF := hF) (hv := hv) (hQv := hQv)
        (a := a) (x a)
      rw [hσinv] at hconj
      rw [hconj, hRw, Function.update_self a ((x a)⁻¹) x]
    · have hconj := signChange_conj_planeRot_of_ne (hF := hF) (hv := hv)
        (a := a) (j := j) hja (x j)
      rw [hσinv] at hconj
      rw [hconj, hRw, Function.update_of_ne hja ((x a)⁻¹) x]
  have hall : ∀ u ∈ (⨆ j, U j), (σ * T * σ) u = R u := by
    intro u hu
    refine Submodule.iSup_induction U (motive := fun u => (σ * T * σ) u = R u) hu
      (fun j w hw => hU j w hw) ?_ ?_
    · rw [map_zero, map_zero]
    · intro y z hy hz
      rw [map_add, map_add, hy, hz]
  have hfixL : ∀ z ∈ polarPerp Q (⨆ j, U j), (σ * T * σ) z = z := by
    intro z hz
    have hσz : σ z ∈ polarPerp Q (⨆ j, U j) := signChange_mapsTo_perp hF hv hz
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      frameTorusFull_apply_perp hF hQ hT x hσz]
    exact hσσ z
  have hfixR : ∀ z ∈ polarPerp Q (⨆ j, U j), R z = z := by
    intro z hz
    have h := frameTorusFull_apply_perp hF hQ hT (Function.update x a (x a)⁻¹) hz
    simpa [R] using h
  ext w
  obtain ⟨u, hu, z, hz, rfl⟩ := Submodule.mem_sup.1
    (hF.isCompl_iSup.sup_eq_top ▸ Submodule.mem_top (x := w))
  rw [map_add, map_add, hall u hu, hfixL z hz, hfixR z hz]

end RelDNs

end CFSG.StandardType

end
