module

public import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenWeyl
public import CFSG.LocalAnalysis.StandardType.GGRealKGOmegaFrame

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.TorDNs

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.GLTheoremA.S172C.Cent CFSG.StandardType.OmNsRootGen
  CFSG.StandardType.RealKGOmega

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p k : ℕ} {U : Fin k → Submodule F V}
  {e : Fin k → ↥(orthDerived Q)} {E : Subgroup ↥(orthDerived Q)} {u : Fin k → V} {c t : F}
  {a b : Fin k}

abbrev rotE (e : Fin k → ↥(orthDerived Q)) (a : Fin k) : Module.End F V :=
  ((e a : V ≃ₗ[F] V) : V →ₗ[F] V)

private theorem dnsRot_add_self {F : Type} [Field F] [CharP F 2] {V : Type} [AddCommGroup V]
    [Module F V] (x : V) : x + x = 0 := by
  have h : x + x = ((1 : F) + 1) • x := by rw [add_smul, one_smul]
  rw [h, one_add_one_eq_two, CharTwo.two_eq_zero, zero_smul]

private theorem dnsRot_neg {F : Type} [Field F] [CharP F 2] {V : Type} [AddCommGroup V]
    [Module F V] (x : V) : -x = x :=
  neg_eq_of_add_eq_zero_right (dnsRot_add_self (F := F) x)

private theorem dnsRot_sub_eq_add {F : Type} [Field F] [CharP F 2] {V : Type}
    [AddCommGroup V] [Module F V] (x y : V) : x - y = x + y := by
  rw [sub_eq_add_neg, dnsRot_neg (F := F)]

omit [Finite F] [CharP F 2] [FiniteDimensional F V] in
private theorem dnsRot_u_ne_zero (hF : IsCoherentFrame Q p U e E u c t) (a : Fin k) :
    u a ≠ 0 := by
  intro h0
  exact hF.c_ne_zero (by rw [← hF.quad_eq a, h0, QuadraticMap.map_zero])

omit [Finite F] [CharP F 2] [FiniteDimensional F V] in
private theorem dnsRot_e_mem_orthogonalGroup (j : Fin k) :
    (e j : V ≃ₗ[F] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  Subgroup.commutator_le_self (TauCeti.QuadraticMap.orthogonalGroup Q) (e j).2

omit [Finite F] [CharP F 2] [FiniteDimensional F V] in
private theorem dnsRot_apply_of_perp (hF : IsCoherentFrame Q p U e E u c t) (j : Fin k)
    {x : V} (hx : x ∈ polarPerp Q (U j)) : rotE e j x = x :=
  hF.apply_of_perp j x hx

omit [Finite F] [CharP F 2] [FiniteDimensional F V] in
private theorem dnsRot_quad_apply (j : Fin k) (x : V) :
    Q (rotE e j x) = Q x := by
  have h := map_of_mem (dnsRot_e_mem_orthogonalGroup (Q := Q) (e := e) j) x
  simpa [rotE] using h

omit [Finite F] [CharP F 2] [FiniteDimensional F V] in
private theorem dnsRot_rot (hF : IsCoherentFrame Q p U e E u c t) (j : Fin k) :
    rotE e j (rotE e j (u j)) = t • rotE e j (u j) + u j :=
  hF.rot j

omit [Finite F] [CharP F 2] in
private theorem dnsRot_ext_on_plane (hF : IsCoherentFrame Q p U e E u c t)
    {φ ψ : Module.End F V} (hU : Set.EqOn φ ψ (U a))
    (hP : Set.EqOn φ ψ (polarPerp Q (U a))) : φ = ψ :=
  LinearMap.ext_on_codisjoint (isCompl_polarPerp (hF.nondeg a)).codisjoint hU hP

omit [Finite F] [CharP F 2] [FiniteDimensional F V] in
private theorem dnsRot_commute_coe {g h : V ≃ₗ[F] V} (hgh : g * h = h * g) :
    Commute ((g : V →ₗ[F] V)) ((h : V →ₗ[F] V)) := by
  show (g : V →ₗ[F] V) * (h : V →ₗ[F] V) = (h : V →ₗ[F] V) * (g : V →ₗ[F] V)
  rw [← LinearEquiv.coe_toLinearMap_mul, ← LinearEquiv.coe_toLinearMap_mul, hgh]

theorem rotE_rotE_apply_of_mem (hF : IsCoherentFrame Q p U e E u c t) (hp : p.Prime)
    (hpq : ¬ p ∣ Nat.card F - 1) {x : V} (hx : x ∈ U a) :
    rotE e a (rotE e a x) = t • rotE e a x + x := by
  have hu0 : u a ≠ 0 := dnsRot_u_ne_zero hF a
  have hspan : x ∈ Submodule.span F (Set.range ![u a, rotE e a (u a)]) :=
    mem_span_pair hF.toIsPlaneFrame hp hpq (hF.mem a) hu0 hx
  have hgen : ∀ y ∈ Submodule.span F (Set.range ![u a, rotE e a (u a)]),
      rotE e a (rotE e a y) = t • rotE e a y + y := by
    intro y hy
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · intro z hz
      obtain ⟨i, rfl⟩ := hz
      fin_cases i
      · simpa [rotE] using hF.rot a
      · have h := congrArg (fun z : V => rotE e a z) (hF.rot a)
        rw [map_add, map_smul] at h
        simpa [rotE] using h
    · simp
    · intro y z _ _ ihy ihz
      rw [map_add, map_add, smul_add, ihy, ihz]
      abel
    · intro r y _ ih
      rw [map_smul, map_smul, ih, smul_add, smul_smul, smul_smul, mul_comm]
  exact hgen x hspan

theorem polar_rotE_of_mem (hF : IsCoherentFrame Q p U e E u c t) (hp : p.Prime)
    (hpq : ¬ p ∣ Nat.card F - 1) {x : V} (hx : x ∈ U a) :
    polar Q x (rotE e a x) = t * Q x := by
  have heO := dnsRot_e_mem_orthogonalGroup (Q := Q) (e := e) a
  have hQ2 : Q (rotE e a (rotE e a x)) = Q x := by
    rw [dnsRot_quad_apply (Q := Q) (e := e) a (rotE e a x), dnsRot_quad_apply (Q := Q) (e := e) a x]
  have hexp : Q (rotE e a (rotE e a x)) =
      t ^ 2 * Q x + Q x + t * polar Q x (rotE e a x) := by
    rw [rotE_rotE_apply_of_mem hF hp hpq hx, QuadraticMap.map_add Q, map_smul_eq_sq,
      polar_smul_left_eq, dnsRot_quad_apply (Q := Q) (e := e) a x, polar_comm]
  have hzero : t ^ 2 * Q x + t * polar Q x (rotE e a x) = 0 := by
    have h := hexp
    rw [hQ2] at h
    have h1 := congrArg (fun z : F => z + Q x) h
    rw [CharTwo.add_self_eq_zero (Q x)] at h1
    have h2 : t ^ 2 * Q x + Q x + t * polar Q x (rotE e a x) + Q x =
        t ^ 2 * Q x + t * polar Q x (rotE e a x) := by
      rw [show t ^ 2 * Q x + Q x + t * polar Q x (rotE e a x) + Q x =
          t ^ 2 * Q x + t * polar Q x (rotE e a x) + (Q x + Q x) by abel,
        CharTwo.add_self_eq_zero (Q x), add_zero]
    rw [h2] at h1
    exact h1.symm
  have h3 : t * polar Q x (rotE e a x) = t ^ 2 * Q x :=
    (CharTwo.add_eq_zero.mp hzero).symm
  have h4 : t * polar Q x (rotE e a x) = t * (t * Q x) := by
    rw [h3, pow_two, mul_assoc]
  exact mul_left_cancel₀ hF.t_ne_zero h4

theorem quad_add_smul_rotE (hF : IsCoherentFrame Q p U e E u c t) (hp : p.Prime)
    (hpq : ¬ p ∣ Nat.card F - 1) {x : V} (hx : x ∈ U a) (α β : F) :
    Q (α • x + β • rotE e a x) = (α ^ 2 + t * α * β + β ^ 2) * Q x := by
  rw [QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq,
    dnsRot_quad_apply (Q := Q) (e := e) a x, polar_smul_left_eq, polar_smul_right_eq,
    polar_rotE_of_mem hF hp hpq hx]
  ring

@[expose] noncomputable def planeProj (e : Fin k → ↥(orthDerived Q)) (t : F) (a : Fin k) :
    Module.End F V :=
  t⁻¹ • ((rotE e a - 1) * (rotE e a + (1 + t) • 1))

private theorem dnsRot_planeProj_aux (hF : IsCoherentFrame Q p U e E u c t) (hp : p.Prime)
    (hpq : ¬ p ∣ Nat.card F - 1) {x : V} (hx : x ∈ U a) :
    ((rotE e a - 1) * (rotE e a + (1 + t) • 1)) x = t • x := by
  have h2 := rotE_rotE_apply_of_mem hF hp hpq hx
  have hz : (rotE e a + (1 + t) • 1) x = rotE e a x + (1 + t) • x := by
    rw [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
  have hz2 : rotE e a (rotE e a x + (1 + t) • x) =
      (t • rotE e a x + x) + (1 + t) • rotE e a x := by
    rw [map_add, map_smul, h2]
  have hmain : ((rotE e a - 1) * (rotE e a + (1 + t) • 1)) x =
      (t • rotE e a x + x) + (1 + t) • rotE e a x -
        (rotE e a x + (1 + t) • x) := by
    rw [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply, hz, hz2]
  rw [hmain, dnsRot_sub_eq_add (F := F)]
  simp only [add_smul, one_smul]
  calc (t • rotE e a x + x) + (rotE e a x + t • rotE e a x) +
        (rotE e a x + (x + t • x))
      = (t • rotE e a x + t • rotE e a x) + (rotE e a x + rotE e a x) +
          (x + x) + t • x := by abel
    _ = t • x := by
        rw [dnsRot_add_self (F := F) (t • rotE e a x), dnsRot_add_self (F := F) (rotE e a x),
          dnsRot_add_self (F := F) x]
        simp

theorem planeProj_apply_of_mem (hF : IsCoherentFrame Q p U e E u c t) (hp : p.Prime)
    (hpq : ¬ p ∣ Nat.card F - 1) {x : V} (hx : x ∈ U a) : planeProj e t a x = x := by
  have h := dnsRot_planeProj_aux hF hp hpq hx
  change t⁻¹ • (((rotE e a - 1) * (rotE e a + (1 + t) • 1)) x) = x
  rw [h, smul_smul, inv_mul_cancel₀ hF.t_ne_zero, one_smul]

omit [Finite F] [CharP F 2] [FiniteDimensional F V] in
theorem planeProj_apply_of_perp (hF : IsCoherentFrame Q p U e E u c t) {x : V}
    (hx : x ∈ polarPerp Q (U a)) : planeProj e t a x = 0 := by
  have hx' : rotE e a x = x := hF.apply_of_perp a x hx
  change t⁻¹ • (((rotE e a - 1) * (rotE e a + (1 + t) • 1)) x) = 0
  have hz : (rotE e a + (1 + t) • 1) x = x + (1 + t) • x := by
    rw [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, hx']
  have hfix : rotE e a (x + (1 + t) • x) = x + (1 + t) • x := by
    rw [map_add, map_smul, hx']
  rw [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply, hz, hfix, sub_self,
    smul_zero]

@[expose] noncomputable def planeRotLin (e : Fin k → ↥(orthDerived Q)) (t : F) (a : Fin k)
    (α β : F) : Module.End F V :=
  1 + (α + β - 1) • planeProj e t a + β • (rotE e a - 1)

theorem planeRotLin_apply_of_mem (hF : IsCoherentFrame Q p U e E u c t) (hp : p.Prime)
    (hpq : ¬ p ∣ Nat.card F - 1) {x : V} (hx : x ∈ U a) (α β : F) :
    planeRotLin e t a α β x = α • x + β • rotE e a x := by
  have hpj : planeProj e t a x = x := planeProj_apply_of_mem hF hp hpq hx
  change (1 + (α + β - 1) • planeProj e t a + β • (rotE e a - 1)) x =
    α • x + β • rotE e a x
  rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply,
    LinearMap.sub_apply, Module.End.one_apply, hpj, smul_sub]
  have h1 : x + (α + β - 1) • x - β • x = α • x := by
    calc x + (α + β - 1) • x - β • x
        = (1 : F) • x + (α + β - 1) • x - β • x := by rw [one_smul]
      _ = ((1 : F) + (α + β - 1)) • x - β • x := by rw [add_smul]
      _ = ((1 : F) + (α + β - 1) - β) • x := by rw [sub_smul]
      _ = α • x := by rw [show (1 : F) + (α + β - 1) - β = α by ring]
  rw [← h1]
  abel

omit [Finite F] [CharP F 2] [FiniteDimensional F V] in
theorem planeRotLin_apply_of_perp (hF : IsCoherentFrame Q p U e E u c t) {x : V}
    (hx : x ∈ polarPerp Q (U a)) (α β : F) : planeRotLin e t a α β x = x := by
  have hpj : planeProj e t a x = 0 := planeProj_apply_of_perp hF hx
  have hx' : rotE e a x = x := dnsRot_apply_of_perp hF a hx
  change (1 + (α + β - 1) • planeProj e t a + β • (rotE e a - 1)) x = x
  rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply,
    LinearMap.sub_apply, Module.End.one_apply, hpj, hx', sub_self, smul_zero, smul_zero,
    add_zero, add_zero]

theorem planeRotLin_mem (hF : IsCoherentFrame Q p U e E u c t) (hp : p.Prime)
    (hpq : ¬ p ∣ Nat.card F - 1) {x : V} (hx : x ∈ U a) (α β : F) :
    planeRotLin e t a α β x ∈ U a := by
  rw [planeRotLin_apply_of_mem hF hp hpq hx α β]
  exact add_mem (Submodule.smul_mem _ α hx) (Submodule.smul_mem _ β (hF.maps_to a x hx))

theorem planeRotLin_mul (hF : IsCoherentFrame Q p U e E u c t) (hp : p.Prime)
    (hpq : ¬ p ∣ Nat.card F - 1) (α β γ δ : F) :
    planeRotLin e t a α β * planeRotLin e t a γ δ =
      planeRotLin e t a (α * γ + β * δ) (α * δ + β * γ + t * β * δ) := by
  refine dnsRot_ext_on_plane (a := a) hF ?_ ?_
  · intro x hx
    rw [Module.End.mul_apply,
      planeRotLin_apply_of_mem hF hp hpq (planeRotLin_mem hF hp hpq hx γ δ) α β,
      planeRotLin_apply_of_mem hF hp hpq hx γ δ,
      planeRotLin_apply_of_mem hF hp hpq hx (α * γ + β * δ) (α * δ + β * γ + t * β * δ),
      map_add, map_smul, map_smul, rotE_rotE_apply_of_mem hF hp hpq hx]
    module
  · intro x hx
    rw [Module.End.mul_apply, planeRotLin_apply_of_perp hF hx,
      planeRotLin_apply_of_perp hF hx, planeRotLin_apply_of_perp hF hx]

omit [Finite F] [CharP F 2] [FiniteDimensional F V] in
theorem planeRotLin_one_zero : planeRotLin e t a 1 0 = 1 := by
  change 1 + ((1 : F) + 0 - 1) • planeProj e t a + (0 : F) • (rotE e a - 1) = 1
  rw [add_zero, sub_self, zero_smul, zero_smul, add_zero, add_zero]

omit [Finite F] [CharP F 2] [FiniteDimensional F V] in
theorem planeRotLin_zero_one : planeRotLin e t a 0 1 = rotE e a := by
  change 1 + ((0 : F) + 1 - 1) • planeProj e t a + (1 : F) • (rotE e a - 1) = rotE e a
  rw [zero_add, sub_self, zero_smul, one_smul, add_zero]
  abel

theorem quad_planeRotLin (hF : IsCoherentFrame Q p U e E u c t) (hp : p.Prime)
    (hpq : ¬ p ∣ Nat.card F - 1) {α β : F} (hdet : α ^ 2 + t * α * β + β ^ 2 = 1) (x : V) :
    Q (planeRotLin e t a α β x) = Q x := by
  have hcompl := isCompl_polarPerp (hF.nondeg a)
  have hmem : x ∈ U a ⊔ polarPerp Q (U a) := by
    rw [hcompl.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hmem
  have hyz : polar Q y z = 0 := mem_polarPerp_iff.1 hz y hy
  have hstep : planeRotLin e t a α β (y + z) = (α • y + β • rotE e a y) + z := by
    rw [map_add, planeRotLin_apply_of_mem hF hp hpq hy, planeRotLin_apply_of_perp hF hz]
  rw [hstep]
  have hpz : polar Q (α • y + β • rotE e a y) z = 0 := by
    rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq, hyz,
      mem_polarPerp_iff.1 hz (rotE e a y) (hF.maps_to a y hy), mul_zero, mul_zero, add_zero]
  calc Q ((α • y + β • rotE e a y) + z)
      = Q (α • y + β • rotE e a y) + Q z +
          polar Q (α • y + β • rotE e a y) z := QuadraticMap.map_add Q _ _
    _ = (α ^ 2 + t * α * β + β ^ 2) * Q y + Q z + 0 := by
        rw [quad_add_smul_rotE hF hp hpq hy α β, hpz]
    _ = Q y + Q z := by rw [hdet, one_mul, add_zero]
    _ = Q y + Q z + polar Q y z := by rw [hyz, add_zero]
    _ = Q (y + z) := (QuadraticMap.map_add Q y z).symm

omit [Finite F] [CharP F 2] [FiniteDimensional F V] in
private theorem dnsRot_comm_planeRotLin {g : Module.End F V} (h : Commute (rotE e a) g)
    (α β : F) : Commute (planeRotLin e t a α β) g := by
  change Commute (1 + (α + β - 1) • (t⁻¹ • ((rotE e a - 1) * (rotE e a + (1 + t) • 1)))
    + β • (rotE e a - 1)) g
  have h1 : Commute (rotE e a - 1) g := h.sub_left (Commute.one_left g)
  have h2 : Commute (rotE e a + (1 + t) • 1) g :=
    h.add_left (Commute.smul_left (Commute.one_left g) (1 + t))
  have h3 : Commute (t⁻¹ • ((rotE e a - 1) * (rotE e a + (1 + t) • 1))) g :=
    Commute.smul_left (h1.mul_left h2) t⁻¹
  exact Commute.add_left
    (Commute.add_left (Commute.one_left g) (Commute.smul_left h3 (α + β - 1)))
    (Commute.smul_left h1 β)

omit [Finite F] [CharP F 2] [FiniteDimensional F V] in
private theorem dnsRot_commute_rotE (hF : IsCoherentFrame Q p U e E u c t) (i j : Fin k) :
    Commute (rotE e i) (rotE e j) := by
  have hi : e i ∈ E := hF.closure_eq ▸ Subgroup.subset_closure (Set.mem_range_self i)
  have hj : e j ∈ E := hF.closure_eq ▸ Subgroup.subset_closure (Set.mem_range_self j)
  have hcomm : (e i : V ≃ₗ[F] V) * (e j : V ≃ₗ[F] V) =
      (e j : V ≃ₗ[F] V) * (e i : V ≃ₗ[F] V) := by
    have h : (⟨e i, hi⟩ : E) * ⟨e j, hj⟩ = ⟨e j, hj⟩ * ⟨e i, hi⟩ :=
      hF.isElemAbelian.1.is_comm.comm _ _
    exact congrArg (fun z : E => ((z : ↥(orthDerived Q)) : V ≃ₗ[F] V)) h
  exact dnsRot_commute_coe hcomm

omit [Finite F] [CharP F 2] [FiniteDimensional F V] in
theorem planeRotLin_comm_rotE (hF : IsCoherentFrame Q p U e E u c t) (j : Fin k) (α β : F) :
    planeRotLin e t a α β * rotE e j = rotE e j * planeRotLin e t a α β :=
  dnsRot_comm_planeRotLin (dnsRot_commute_rotE hF a j) α β

omit [Finite F] [CharP F 2] [FiniteDimensional F V] in
theorem planeRotLin_comm (hF : IsCoherentFrame Q p U e E u c t) (α β γ δ : F) :
    planeRotLin e t a α β * planeRotLin e t b γ δ =
      planeRotLin e t b γ δ * planeRotLin e t a α β :=
  dnsRot_comm_planeRotLin (a := a)
    ((dnsRot_comm_planeRotLin (a := b) (dnsRot_commute_rotE hF b a) γ δ).symm) α β

private theorem dnsRot_nondeg_sup (hF : IsCoherentFrame Q p U e E u c t) :
    (QuadraticMap.polarBilin (Q.comp (U a ⊔ U b).subtype)).Nondegenerate := by
  have h := hF.toIsPlaneSystem.nondeg_biSup ({a, b} : Finset (Fin k))
  have hsup : (⨆ j ∈ ({a, b} : Finset (Fin k)), U j) = U a ⊔ U b := by
    rw [Finset.insert_eq, Finset.iSup_union, Finset.iSup_singleton, Finset.iSup_singleton]
  rwa [hsup] at h

private theorem dnsRot_mul_eq_of_conj {G : Type} [Group G] {S g h : G} (hS : S * S = 1)
    (hc : S * g * S = h) : S * g = h * S := by
  calc S * g = S * g * 1 := by rw [mul_one]
    _ = S * g * (S * S) := by rw [hS]
    _ = (S * g * S) * S := by group
    _ = h * S := by rw [hc]

omit [Finite F] [CharP F 2] [FiniteDimensional F V] in
private theorem dnsRot_coe_mul_cancel {S f g : V ≃ₗ[F] V} (h : S * f = g * S) :
    (S : V →ₗ[F] V) * (f : V →ₗ[F] V) = (g : V →ₗ[F] V) * (S : V →ₗ[F] V) := by
  rw [← LinearEquiv.coe_toLinearMap_mul, ← LinearEquiv.coe_toLinearMap_mul, h]

private theorem dnsRot_span_mem (hF : IsCoherentFrame Q p U e E u c t) (hp : p.Prime)
    (hpq : ¬ p ∣ Nat.card F - 1) {x : V} (hx : x ∈ U a) :
    x ∈ Submodule.span F (Set.range ![u a, rotE e a (u a)]) :=
  mem_span_pair hF.toIsPlaneFrame hp hpq (hF.mem a) (dnsRot_u_ne_zero hF a) hx

private theorem dnsRot_frameSwap_mapsTo_left (hF : IsCoherentFrame Q p U e E u c t)
    (hp : p.Prime) (hpq : ¬ p ∣ Nat.card F - 1) (hab : a ≠ b) {x : V} (hx : x ∈ U a) :
    frameSwap Q e u c t a b x ∈ U b := by
  have hspan := dnsRot_span_mem hF hp hpq (a := a) hx
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hspan
  · intro z hz
    obtain ⟨i, rfl⟩ := hz
    fin_cases i
    · show frameSwap Q e u c t a b (u a) ∈ U b
      rw [frameSwap_apply_left hF hab]
      exact hF.mem b
    · show frameSwap Q e u c t a b (rotE e a (u a)) ∈ U b
      rw [show rotE e a (u a) = (e a : V ≃ₗ[F] V) (u a) from rfl,
        frameSwap_apply_e_left hF hab]
      exact hF.maps_to b (u b) (hF.mem b)
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro y z _ _ ihy ihz
    rw [map_add]
    exact Submodule.add_mem _ ihy ihz
  · intro r y _ ihy
    rw [map_smul]
    exact Submodule.smul_mem _ r ihy

private theorem dnsRot_frameSwap_mapsTo_right (hF : IsCoherentFrame Q p U e E u c t)
    (hp : p.Prime) (hpq : ¬ p ∣ Nat.card F - 1) (hab : a ≠ b) {x : V} (hx : x ∈ U b) :
    frameSwap Q e u c t a b x ∈ U a := by
  have hspan : x ∈ Submodule.span F (Set.range ![u b, rotE e b (u b)]) :=
    mem_span_pair hF.toIsPlaneFrame hp hpq (hF.mem b) (dnsRot_u_ne_zero hF b) hx
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hspan
  · intro z hz
    obtain ⟨i, rfl⟩ := hz
    fin_cases i
    · show frameSwap Q e u c t a b (u b) ∈ U a
      rw [frameSwap_apply_right hF hab]
      exact hF.mem a
    · show frameSwap Q e u c t a b (rotE e b (u b)) ∈ U a
      rw [show rotE e b (u b) = (e b : V ≃ₗ[F] V) (u b) from rfl,
        frameSwap_apply_e_right hF hab]
      exact hF.maps_to a (u a) (hF.mem a)
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro y z _ _ ihy ihz
    rw [map_add]
    exact Submodule.add_mem _ ihy ihz
  · intro r y _ ihy
    rw [map_smul]
    exact Submodule.smul_mem _ r ihy

private theorem dnsRot_frameSwap_mul_rotE_left (hF : IsCoherentFrame Q p U e E u c t)
    (hab : a ≠ b) :
    (frameSwap Q e u c t a b : V →ₗ[F] V) * rotE e a =
      rotE e b * (frameSwap Q e u c t a b : V →ₗ[F] V) :=
  dnsRot_coe_mul_cancel (dnsRot_mul_eq_of_conj (frameSwap_mul_self hF hab)
    (frameSwap_conj_left hF hab))

private theorem dnsRot_frameSwap_mul_rotE_right (hF : IsCoherentFrame Q p U e E u c t)
    (hab : a ≠ b) :
    (frameSwap Q e u c t a b : V →ₗ[F] V) * rotE e b =
      rotE e a * (frameSwap Q e u c t a b : V →ₗ[F] V) :=
  dnsRot_coe_mul_cancel (dnsRot_mul_eq_of_conj (frameSwap_mul_self hF hab)
    (frameSwap_conj_right hF hab))

private theorem dnsRot_frameSwap_apply_rotE_left (hF : IsCoherentFrame Q p U e E u c t)
    (hab : a ≠ b) (x : V) :
    (frameSwap Q e u c t a b : V →ₗ[F] V) (rotE e a x) =
      rotE e b ((frameSwap Q e u c t a b : V →ₗ[F] V) x) := by
  have h := dnsRot_frameSwap_mul_rotE_left hF hab
  simpa only [Module.End.mul_apply] using congrArg (fun z : V →ₗ[F] V => z x) h

private theorem dnsRot_frameSwap_apply_rotE_right (hF : IsCoherentFrame Q p U e E u c t)
    (hab : a ≠ b) (x : V) :
    (frameSwap Q e u c t a b : V →ₗ[F] V) (rotE e b x) =
      rotE e a ((frameSwap Q e u c t a b : V →ₗ[F] V) x) := by
  have h := dnsRot_frameSwap_mul_rotE_right hF hab
  simpa only [Module.End.mul_apply] using congrArg (fun z : V →ₗ[F] V => z x) h

private theorem dnsRot_frameSwap_apply_of_mem_polarPerp (hF : IsCoherentFrame Q p U e E u c t)
    {x : V} (hx : x ∈ polarPerp Q (U a ⊔ U b)) :
    (frameSwap Q e u c t a b : V →ₗ[F] V) x = x :=
  frameSwap_apply_of_mem_polarPerp hF hx

theorem frameSwap_comp_planeRotLin_left (hF : IsCoherentFrame Q p U e E u c t) (hp : p.Prime)
    (hpq : ¬ p ∣ Nat.card F - 1) (hab : a ≠ b) (α β : F) :
    (frameSwap Q e u c t a b : V →ₗ[F] V) * planeRotLin e t a α β =
      planeRotLin e t b α β * (frameSwap Q e u c t a b : V →ₗ[F] V) := by
  have hW : IsCompl (U a ⊔ U b) (polarPerp Q (U a ⊔ U b)) :=
    isCompl_polarPerp (dnsRot_nondeg_sup hF)
  refine LinearMap.ext_on_codisjoint hW.codisjoint ?_ ?_
  · refine LinearMap.eqOn_sup (S := U a) (T := U b) ?_ ?_
    · intro x hx
      have hSx : (frameSwap Q e u c t a b : V →ₗ[F] V) x ∈ U b :=
        dnsRot_frameSwap_mapsTo_left hF hp hpq hab hx
      calc ((frameSwap Q e u c t a b : V →ₗ[F] V) * planeRotLin e t a α β) x
          = (frameSwap Q e u c t a b : V →ₗ[F] V) (planeRotLin e t a α β x) := by
              rw [Module.End.mul_apply]
        _ = (frameSwap Q e u c t a b : V →ₗ[F] V) (α • x + β • rotE e a x) := by
              rw [planeRotLin_apply_of_mem hF hp hpq hx α β]
        _ = α • (frameSwap Q e u c t a b : V →ₗ[F] V) x +
              β • (frameSwap Q e u c t a b : V →ₗ[F] V) (rotE e a x) := by
              rw [map_add, map_smul, map_smul]
        _ = α • (frameSwap Q e u c t a b : V →ₗ[F] V) x +
              β • rotE e b ((frameSwap Q e u c t a b : V →ₗ[F] V) x) := by
              rw [dnsRot_frameSwap_apply_rotE_left hF hab]
        _ = planeRotLin e t b α β ((frameSwap Q e u c t a b : V →ₗ[F] V) x) :=
              (planeRotLin_apply_of_mem hF hp hpq hSx α β).symm
        _ = (planeRotLin e t b α β * (frameSwap Q e u c t a b : V →ₗ[F] V)) x := by
              rw [Module.End.mul_apply]
    · intro x hx
      have hSx : (frameSwap Q e u c t a b : V →ₗ[F] V) x ∈ U a :=
        dnsRot_frameSwap_mapsTo_right hF hp hpq hab hx
      have hxa : x ∈ polarPerp Q (U a) :=
        mem_polarPerp_iff.2 fun y hy => hF.perp a b hab y hy x hx
      have hSxp : (frameSwap Q e u c t a b : V →ₗ[F] V) x ∈ polarPerp Q (U b) :=
        mem_polarPerp_iff.2 fun y hy => hF.perp b a hab.symm y hy _ hSx
      calc ((frameSwap Q e u c t a b : V →ₗ[F] V) * planeRotLin e t a α β) x
          = (frameSwap Q e u c t a b : V →ₗ[F] V) (planeRotLin e t a α β x) := by
              rw [Module.End.mul_apply]
        _ = (frameSwap Q e u c t a b : V →ₗ[F] V) x := by
              rw [planeRotLin_apply_of_perp hF hxa]
        _ = planeRotLin e t b α β ((frameSwap Q e u c t a b : V →ₗ[F] V) x) :=
              (planeRotLin_apply_of_perp hF hSxp α β).symm
        _ = (planeRotLin e t b α β * (frameSwap Q e u c t a b : V →ₗ[F] V)) x := by
              rw [Module.End.mul_apply]
  · intro x hx
    have hxa : x ∈ polarPerp Q (U a) :=
      mem_polarPerp_iff.2 fun y hy => mem_polarPerp_iff.1 hx y (Submodule.mem_sup_left hy)
    have hxb : x ∈ polarPerp Q (U b) :=
      mem_polarPerp_iff.2 fun y hy => mem_polarPerp_iff.1 hx y (Submodule.mem_sup_right hy)
    calc ((frameSwap Q e u c t a b : V →ₗ[F] V) * planeRotLin e t a α β) x
        = (frameSwap Q e u c t a b : V →ₗ[F] V) (planeRotLin e t a α β x) := by
            rw [Module.End.mul_apply]
      _ = (frameSwap Q e u c t a b : V →ₗ[F] V) x := by
            rw [planeRotLin_apply_of_perp hF hxa]
      _ = x := by rw [dnsRot_frameSwap_apply_of_mem_polarPerp hF hx]
      _ = planeRotLin e t b α β x := (planeRotLin_apply_of_perp hF hxb α β).symm
      _ = planeRotLin e t b α β ((frameSwap Q e u c t a b : V →ₗ[F] V) x) := by
            rw [dnsRot_frameSwap_apply_of_mem_polarPerp hF hx]
      _ = (planeRotLin e t b α β * (frameSwap Q e u c t a b : V →ₗ[F] V)) x := by
            rw [Module.End.mul_apply]

theorem frameSwap_comp_planeRotLin_right (hF : IsCoherentFrame Q p U e E u c t) (hp : p.Prime)
    (hpq : ¬ p ∣ Nat.card F - 1) (hab : a ≠ b) (α β : F) :
    (frameSwap Q e u c t a b : V →ₗ[F] V) * planeRotLin e t b α β =
      planeRotLin e t a α β * (frameSwap Q e u c t a b : V →ₗ[F] V) := by
  have hW : IsCompl (U a ⊔ U b) (polarPerp Q (U a ⊔ U b)) :=
    isCompl_polarPerp (dnsRot_nondeg_sup hF)
  refine LinearMap.ext_on_codisjoint hW.codisjoint ?_ ?_
  · refine LinearMap.eqOn_sup (S := U a) (T := U b) ?_ ?_
    · intro x hx
      have hSx : (frameSwap Q e u c t a b : V →ₗ[F] V) x ∈ U b :=
        dnsRot_frameSwap_mapsTo_left hF hp hpq hab hx
      have hxa : x ∈ polarPerp Q (U b) :=
        mem_polarPerp_iff.2 fun y hy => hF.perp b a hab.symm y hy x hx
      have hSxp : (frameSwap Q e u c t a b : V →ₗ[F] V) x ∈ polarPerp Q (U a) :=
        mem_polarPerp_iff.2 fun y hy => hF.perp a b hab y hy _ hSx
      calc ((frameSwap Q e u c t a b : V →ₗ[F] V) * planeRotLin e t b α β) x
          = (frameSwap Q e u c t a b : V →ₗ[F] V) (planeRotLin e t b α β x) := by
              rw [Module.End.mul_apply]
        _ = (frameSwap Q e u c t a b : V →ₗ[F] V) x := by
              rw [planeRotLin_apply_of_perp hF hxa]
        _ = planeRotLin e t a α β ((frameSwap Q e u c t a b : V →ₗ[F] V) x) :=
              (planeRotLin_apply_of_perp hF hSxp α β).symm
        _ = (planeRotLin e t a α β * (frameSwap Q e u c t a b : V →ₗ[F] V)) x := by
              rw [Module.End.mul_apply]
    · intro x hx
      have hSx : (frameSwap Q e u c t a b : V →ₗ[F] V) x ∈ U a :=
        dnsRot_frameSwap_mapsTo_right hF hp hpq hab hx
      calc ((frameSwap Q e u c t a b : V →ₗ[F] V) * planeRotLin e t b α β) x
          = (frameSwap Q e u c t a b : V →ₗ[F] V) (planeRotLin e t b α β x) := by
              rw [Module.End.mul_apply]
        _ = (frameSwap Q e u c t a b : V →ₗ[F] V) (α • x + β • rotE e b x) := by
              rw [planeRotLin_apply_of_mem hF hp hpq hx α β]
        _ = α • (frameSwap Q e u c t a b : V →ₗ[F] V) x +
              β • (frameSwap Q e u c t a b : V →ₗ[F] V) (rotE e b x) := by
              rw [map_add, map_smul, map_smul]
        _ = α • (frameSwap Q e u c t a b : V →ₗ[F] V) x +
              β • rotE e a ((frameSwap Q e u c t a b : V →ₗ[F] V) x) := by
              rw [dnsRot_frameSwap_apply_rotE_right hF hab]
        _ = planeRotLin e t a α β ((frameSwap Q e u c t a b : V →ₗ[F] V) x) :=
              (planeRotLin_apply_of_mem hF hp hpq hSx α β).symm
        _ = (planeRotLin e t a α β * (frameSwap Q e u c t a b : V →ₗ[F] V)) x := by
              rw [Module.End.mul_apply]
  · intro x hx
    have hxa : x ∈ polarPerp Q (U a) :=
      mem_polarPerp_iff.2 fun y hy => mem_polarPerp_iff.1 hx y (Submodule.mem_sup_left hy)
    have hxb : x ∈ polarPerp Q (U b) :=
      mem_polarPerp_iff.2 fun y hy => mem_polarPerp_iff.1 hx y (Submodule.mem_sup_right hy)
    calc ((frameSwap Q e u c t a b : V →ₗ[F] V) * planeRotLin e t b α β) x
        = (frameSwap Q e u c t a b : V →ₗ[F] V) (planeRotLin e t b α β x) := by
            rw [Module.End.mul_apply]
      _ = (frameSwap Q e u c t a b : V →ₗ[F] V) x := by
            rw [planeRotLin_apply_of_perp hF hxb]
      _ = x := by rw [dnsRot_frameSwap_apply_of_mem_polarPerp hF hx]
      _ = planeRotLin e t a α β x := (planeRotLin_apply_of_perp hF hxa α β).symm
      _ = planeRotLin e t a α β ((frameSwap Q e u c t a b : V →ₗ[F] V) x) := by
            rw [dnsRot_frameSwap_apply_of_mem_polarPerp hF hx]
      _ = (planeRotLin e t a α β * (frameSwap Q e u c t a b : V →ₗ[F] V)) x := by
            rw [Module.End.mul_apply]

omit [Finite F] [FiniteDimensional F V] in
private theorem dnsRot_reflect_apply_u (hF : IsCoherentFrame Q p U e E u c t) :
    (reflect Q (u a) : V →ₗ[F] V) (u a) = u a :=
  reflect_apply_of_polar_eq_zero (by
    rw [polar_self_eq_two_mul, hF.quad_eq a, CharTwo.two_eq_zero, zero_mul])

omit [Finite F] [FiniteDimensional F V] in
private theorem dnsRot_reflect_apply_eu (hF : IsCoherentFrame Q p U e E u c t) :
    (reflect Q (u a) : V →ₗ[F] V) (rotE e a (u a)) = rotE e a (u a) + t • u a := by
  have h := reflect_apply (Q := Q) (v := u a) (by rw [hF.quad_eq a]; exact hF.c_ne_zero)
    ((e a : V ≃ₗ[F] V) (u a))
  rw [hF.polar_eq a, hF.quad_eq a, mul_div_cancel_right₀ t hF.c_ne_zero,
    sub_eq_add_neg, dnsRot_neg (F := F)] at h
  exact h

private theorem dnsRot_reflect_planeRotLin_u (hF : IsCoherentFrame Q p U e E u c t)
    (hp : p.Prime) (hpq : ¬ p ∣ Nat.card F - 1) (α β : F) :
    (reflect Q (u a) : V →ₗ[F] V) (planeRotLin e t a α β (u a)) =
      planeRotLin e t a (α + t * β) β ((reflect Q (u a) : V →ₗ[F] V) (u a)) := by
  have hρu : (reflect Q (u a) : V →ₗ[F] V) (u a) = u a := dnsRot_reflect_apply_u hF
  have hρeu : (reflect Q (u a) : V →ₗ[F] V) (rotE e a (u a)) = rotE e a (u a) + t • u a :=
    dnsRot_reflect_apply_eu hF
  calc (reflect Q (u a) : V →ₗ[F] V) (planeRotLin e t a α β (u a))
      = (reflect Q (u a) : V →ₗ[F] V) (α • u a + β • rotE e a (u a)) := by
          rw [planeRotLin_apply_of_mem hF hp hpq (hF.mem a) α β]
    _ = α • (reflect Q (u a) : V →ₗ[F] V) (u a) +
          β • (reflect Q (u a) : V →ₗ[F] V) (rotE e a (u a)) := by
          rw [map_add, map_smul, map_smul]
    _ = α • u a + β • (rotE e a (u a) + t • u a) := by rw [hρu, hρeu]
    _ = (α + t * β) • u a + β • rotE e a (u a) := by module
    _ = planeRotLin e t a (α + t * β) β ((reflect Q (u a) : V →ₗ[F] V) (u a)) := by
          rw [hρu, planeRotLin_apply_of_mem hF hp hpq (hF.mem a) (α + t * β) β]

private theorem dnsRot_reflect_planeRotLin_eu (hF : IsCoherentFrame Q p U e E u c t)
    (hp : p.Prime) (hpq : ¬ p ∣ Nat.card F - 1) (α β : F) :
    (reflect Q (u a) : V →ₗ[F] V) (planeRotLin e t a α β (rotE e a (u a))) =
      planeRotLin e t a (α + t * β) β
        ((reflect Q (u a) : V →ₗ[F] V) (rotE e a (u a))) := by
  have hmem : rotE e a (u a) ∈ U a := hF.maps_to a (u a) (hF.mem a)
  have hρeu : (reflect Q (u a) : V →ₗ[F] V) (rotE e a (u a)) = rotE e a (u a) + t • u a :=
    dnsRot_reflect_apply_eu hF
  have hρeumem : (reflect Q (u a) : V →ₗ[F] V) (rotE e a (u a)) ∈ U a := by
    rw [hρeu]
    exact add_mem hmem (Submodule.smul_mem _ t (hF.mem a))
  have hefix : rotE e a ((reflect Q (u a) : V →ₗ[F] V) (rotE e a (u a))) = u a := by
    rw [hρeu, map_add, map_smul, dnsRot_rot hF a]
    rw [show t • rotE e a (u a) + u a + t • rotE e a (u a) =
        (t • rotE e a (u a) + t • rotE e a (u a)) + u a by abel,
      dnsRot_add_self (F := F) (t • rotE e a (u a)), zero_add]
  calc (reflect Q (u a) : V →ₗ[F] V) (planeRotLin e t a α β (rotE e a (u a)))
      = (reflect Q (u a) : V →ₗ[F] V)
          (α • rotE e a (u a) + β • rotE e a (rotE e a (u a))) := by
          rw [planeRotLin_apply_of_mem hF hp hpq hmem α β]
    _ = α • (reflect Q (u a) : V →ₗ[F] V) (rotE e a (u a)) +
          β • (reflect Q (u a) : V →ₗ[F] V) (rotE e a (rotE e a (u a))) := by
          rw [map_add, map_smul, map_smul]
    _ = α • (reflect Q (u a) : V →ₗ[F] V) (rotE e a (u a)) +
          β • (reflect Q (u a) : V →ₗ[F] V) (t • rotE e a (u a) + u a) := by
          rw [dnsRot_rot hF a]
    _ = α • (reflect Q (u a) : V →ₗ[F] V) (rotE e a (u a)) +
          β • (t • (reflect Q (u a) : V →ₗ[F] V) (rotE e a (u a)) +
            (reflect Q (u a) : V →ₗ[F] V) (u a)) := by
          rw [map_add, map_smul]
    _ = α • (rotE e a (u a) + t • u a) +
          β • (t • (rotE e a (u a) + t • u a) + u a) := by
          rw [hρeu, dnsRot_reflect_apply_u hF]
    _ = (α + t * β) • (rotE e a (u a) + t • u a) + β • u a := by module
    _ = (α + t * β) • (reflect Q (u a) : V →ₗ[F] V) (rotE e a (u a)) + β • u a := by
          rw [hρeu]
    _ = (α + t * β) • (reflect Q (u a) : V →ₗ[F] V) (rotE e a (u a)) +
          β • rotE e a ((reflect Q (u a) : V →ₗ[F] V) (rotE e a (u a))) := by
          rw [hefix]
    _ = planeRotLin e t a (α + t * β) β
          ((reflect Q (u a) : V →ₗ[F] V) (rotE e a (u a))) := by
          rw [planeRotLin_apply_of_mem hF hp hpq hρeumem (α + t * β) β]

theorem reflect_comp_planeRotLin (hF : IsCoherentFrame Q p U e E u c t) (hp : p.Prime)
    (hpq : ¬ p ∣ Nat.card F - 1) (α β : F) :
    (reflect Q (u a) : V →ₗ[F] V) * planeRotLin e t a α β =
      planeRotLin e t a (α + t * β) β * (reflect Q (u a) : V →ₗ[F] V) := by
  refine dnsRot_ext_on_plane (a := a) hF ?_ ?_
  · intro x hx
    have hspan := dnsRot_span_mem hF hp hpq (a := a) hx
    have hgen : ∀ y ∈ Submodule.span F (Set.range ![u a, rotE e a (u a)]),
        (reflect Q (u a) : V →ₗ[F] V) (planeRotLin e t a α β y) =
          planeRotLin e t a (α + t * β) β ((reflect Q (u a) : V →ₗ[F] V) y) := by
      intro y hy
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
      · intro z hz
        obtain ⟨i, rfl⟩ := hz
        fin_cases i
        · show (reflect Q (u a) : V →ₗ[F] V) (planeRotLin e t a α β (u a)) =
            planeRotLin e t a (α + t * β) β ((reflect Q (u a) : V →ₗ[F] V) (u a))
          exact dnsRot_reflect_planeRotLin_u hF hp hpq α β
        · show (reflect Q (u a) : V →ₗ[F] V) (planeRotLin e t a α β (rotE e a (u a))) =
            planeRotLin e t a (α + t * β) β
              ((reflect Q (u a) : V →ₗ[F] V) (rotE e a (u a)))
          exact dnsRot_reflect_planeRotLin_eu hF hp hpq α β
      · simp
      · intro y z _ _ ihy ihz
        simp only [map_add, ihy, ihz]
      · intro r y _ ih
        simp only [map_smul, ih]
    exact hgen x hspan
  · intro x hx
    have hpx : polar Q (u a) x = 0 := mem_polarPerp_iff.1 hx (u a) (hF.mem a)
    have hρx : (reflect Q (u a) : V →ₗ[F] V) x = x :=
      reflect_apply_of_polar_eq_zero hpx
    calc ((reflect Q (u a) : V →ₗ[F] V) * planeRotLin e t a α β) x
        = (reflect Q (u a) : V →ₗ[F] V) (planeRotLin e t a α β x) := by
            rw [Module.End.mul_apply]
      _ = (reflect Q (u a) : V →ₗ[F] V) x := by
            rw [planeRotLin_apply_of_perp hF hx]
      _ = x := hρx
      _ = planeRotLin e t a (α + t * β) β x :=
            (planeRotLin_apply_of_perp hF hx (α + t * β) β).symm
      _ = planeRotLin e t a (α + t * β) β ((reflect Q (u a) : V →ₗ[F] V) x) := by
            rw [hρx]
      _ = (planeRotLin e t a (α + t * β) β * (reflect Q (u a) : V →ₗ[F] V)) x := by
            rw [Module.End.mul_apply]

theorem reflect_comp_planeRotLin_of_ne (hF : IsCoherentFrame Q p U e E u c t) {j : Fin k}
    (hja : j ≠ a) (α β : F) :
    (reflect Q (u a) : V →ₗ[F] V) * planeRotLin e t j α β =
      planeRotLin e t j α β * (reflect Q (u a) : V →ₗ[F] V) := by
  have h := reflect_commute_of_ne hF (a := a) (j := j) hja
  exact (dnsRot_comm_planeRotLin (a := j) (dnsRot_commute_coe h).symm α β).symm

end CFSG.StandardType.TorDNs

end
