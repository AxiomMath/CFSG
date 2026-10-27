module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalSpSC
public import CFSG.LocalAnalysis.StandardType.GGTorusGenSpTwoCentBlock

public section

open CFSG CFSG.Assembly Polynomial Module Multiplicative CFSG.LocalAnalysis.ComponentInitial

namespace CFSG.StandardType

namespace SpNS

structure FrameData (K : Type) [Field K] [Finite K] [CharP K 2]
    (V : Type) [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (E : Subgroup ↥(sesqUnitaryGroup B)) where
  g : K[X]
  hg : Irreducible g
  hgd : g ∣ cyclotomic 3 K
  s : ℕ
  κ : Type
  Φ : ((Fin s → AdjoinRoot g) × (κ → K)) ≃ₗ[K] V
  b : Basis (Fin 2) K (AdjoinRoot g)
  ζ : AdjoinRoot g
  hζ : ζ = AdjoinRoot.root g
  hζp : ζ ^ 3 = 1
  hζ1 : ζ ≠ 1
  hζω : ∀ ω : LinearMap.BilinForm K (AdjoinRoot g), ω.IsAlt → ∀ u v,
    ω (ζ * u) (ζ * v) = ω u v
  τ : (Fin s → Multiplicative (ZMod 3)) →* ↥(sesqUnitaryGroup B)
  hτapp : ∀ (f : Fin s → Multiplicative (ZMod 3)) (x : (Fin s → AdjoinRoot g) × (κ → K)),
    (((τ f : ↥(sesqUnitaryGroup B)) : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) (Φ x) =
      Φ (fun i => ζ ^ (toAdd (f i)).val * x.1 i, x.2)
  hact : ∀ e ∈ E, ∃ k : Fin s → ℕ, ∀ d w,
    (((e : ↥(sesqUnitaryGroup B)) : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V)
      (Φ (d, w)) = Φ (fun i => ζ ^ k i * d i, w)
  β : LinearMap.BilinForm K (AdjoinRoot g)
  hdec : ∀ d d' w w', B (Φ (d, w)) (Φ (d', w')) =
    ∑ i, β (d i) (d' i) + B (Φ (0, w)) (Φ (0, w'))

private def HCommutes {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V]
    {B : LinearMap.BilinForm K V} {E : Subgroup ↥(sesqUnitaryGroup B)}
    (F : FrameData K V B E) (H : V →ₗ[K] V) : Prop :=
  ∀ (f : Fin F.s → Multiplicative (ZMod 3)) (v : V),
    H ((((F.τ f : ↥(sesqUnitaryGroup B)) : LinearMap.GeneralLinearGroup K V) :
      V →ₗ[K] V) v) = ((((F.τ f : ↥(sesqUnitaryGroup B)) :
        LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) (H v))

private def BlockMaps {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V]
    {B : LinearMap.BilinForm K V} {E : Subgroup ↥(sesqUnitaryGroup B)}
    (F : FrameData K V B E) (H : V →ₗ[K] V) : Prop :=
  ∀ (i : Fin F.s) (u : AdjoinRoot F.g),
    ∃ c : AdjoinRoot F.g, H (F.Φ (Pi.single i u, 0)) = F.Φ (Pi.single i c, 0)

theorem exists_frame_data
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {B : LinearMap.BilinForm K V} (hAlt : B.IsAlt) (hnd : B.Nondegenerate)
    (E : Subgroup ↥(sesqUnitaryGroup B)) (hE : IsElemAbelian 3 E) :
    Nonempty (FrameData K V B E) := by
  classical
  have hp : (3 : ℕ).Prime := by norm_num
  have hp2 : 3 ≠ 2 := by norm_num
  have hpK : (3 : K) ≠ 0 := TableBSymp.natCast_ne_zero_of_charTwo hp hp2
  have hpq : 3 ∣ Nat.card K + 1 := by rw [hK]
  have hne : ¬ IsUnit (cyclotomic 3 K) := by
    rw [Polynomial.isUnit_iff_degree_eq_zero, degree_eq_natDegree (cyclotomic_ne_zero 3 _),
      natDegree_cyclotomic, Nat.totient_prime hp]
    have := hp.two_le; norm_cast
  obtain ⟨g, hg, hgd⟩ := WfDvdMonoid.exists_irreducible_factor hne (cyclotomic_ne_zero 3 _)
  have : Fact (Irreducible g) := ⟨hg⟩
  have hζo := NSFrame.root_isPrimitiveRoot (g := g) hp hpK hgd
  set ζ := AdjoinRoot.root g
  have hζp : ζ ^ 3 = 1 := hζo.pow_eq_one
  have hζ1 : ζ ≠ 1 := hζo.ne_one hp.one_lt
  set S : Set (Module.End K V) := {x | ∃ e ∈ E,
    (((e : ↥(sesqUnitaryGroup B)) : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) = x}
  have hSc : ∀ x ∈ S, ∀ x' ∈ S, Commute x x' := by
    rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩
    have h2 := congrArg (fun y : ↥(sesqUnitaryGroup B) =>
      ((y : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V)) (TableB.IsElemAbelian.comm hE he he')
    simp only [Subgroup.coe_mul, Units.val_mul] at h2; exact h2
  have hSp : ∀ x ∈ S, x ^ 3 = 1 := by
    rintro _ ⟨e, he, rfl⟩
    simpa using congrArg (fun y : ↥(sesqUnitaryGroup B) =>
      ((y : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V)) (hE.2 e he)
  have hSB : ∀ x ∈ S, ∀ u w, B (x u) (x w) = B u w := by
    rintro _ ⟨e, -, rfl⟩ u w; exact mem_sesqUnitaryGroup.mp e.2 u w
  obtain ⟨s, κ, _, Φ, β, hβ, hact, hdec⟩ := exists_nframe hp hp2 hpK hgd
    (rootPB_dim_eq_two hp hp2 hpK hgd hpq) (aeval_root_pow_pred hp hpK hgd hpq) hAlt hnd S hSc hSp
    hSB
  set b : Basis (Fin 2) K (AdjoinRoot g) :=
    (CoordSL.rootPB g).basis.reindex (finCongr (rootPB_dim_eq_two hp hp2 hpK hgd hpq))
  have hζω : ∀ ω : LinearMap.BilinForm K (AdjoinRoot g), ω.IsAlt → ∀ u v,
      ω (ζ * u) (ζ * v) = ω u v := fun ω hω u v => by
    have h1 := bilin_apply_det b hω (Algebra.lmul K (AdjoinRoot g) ζ) u v
    rw [← Algebra.norm_apply, norm_root_eq_one hp hp2 hpK hgd hpq, one_mul] at h1
    exact h1
  have hζβ : ∀ u v, β (ζ * u) (ζ * v) = β u v := hζω β hβ
  set τ := torHom (K := K) hζp hdec hζβ
  have hτapp : ∀ f x, (((τ f : ↥(sesqUnitaryGroup B)) : LinearMap.GeneralLinearGroup K V) :
      V →ₗ[K] V) (Φ x) = Φ (fun i => ζ ^ (toAdd (f i)).val * x.1 i, x.2) := fun f x => by
    rw [show (((τ f : ↥(sesqUnitaryGroup B)) : LinearMap.GeneralLinearGroup K V) :
      V →ₗ[K] V) (Φ x) = Φ (torEquiv hζp f x) from frameUnit_apply Φ _ x, torEquiv_apply]
  have hact' : ∀ e ∈ E, ∃ k : Fin s → ℕ, ∀ d w,
      (((e : ↥(sesqUnitaryGroup B)) : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V)
        (Φ (d, w)) = Φ (fun i => ζ ^ k i * d i, w) := by
    intro e he; exact hact _ ⟨e, he, rfl⟩
  exact ⟨FrameData.mk g hg hgd s κ Φ b ζ rfl hζp hζ1 hζω τ hτapp hact' β hdec⟩

theorem torus_range {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V]
    {B : LinearMap.BilinForm K V} {E : Subgroup ↥(sesqUnitaryGroup B)}
    (F : FrameData K V B E)
    (hsc : ∀ g : ↥(sesqUnitaryGroup B), (∀ e ∈ E, g * e = e * g) → g ^ 3 = 1 → g ∈ E) :
    (∀ e ∈ E, ∃ f, F.τ f = e) ∧ (∀ f, F.τ f ∈ E) := by
  have hEτ : ∀ e ∈ E, ∃ f, F.τ f = e := by
    intro e he
    obtain ⟨k, hk⟩ := F.hact e he
    refine ⟨fun i => ofAdd (k i : ZMod 3), Subtype.ext (Units.ext (LinearMap.ext fun v => ?_))⟩
    obtain ⟨⟨d, w⟩, rfl⟩ := F.Φ.surjective v
    rw [F.hτapp, hk]
    congr 2; funext i
    rw [toAdd_ofAdd, ZMod.val_natCast, ← pow_eq_pow_mod _ F.hζp]
  refine ⟨hEτ, fun f => ?_⟩
  refine hsc _ (fun e he => ?_) ?_
  · obtain ⟨f', rfl⟩ := hEτ e he
    rw [← map_mul, ← map_mul, mul_comm]
  · rw [← map_pow]; convert map_one F.τ
    funext i
    rw [Pi.pow_apply, Pi.one_apply, ← ofAdd_toAdd (f i ^ 3), toAdd_pow, nsmul_eq_mul,
      ZMod.natCast_self, zero_mul, ofAdd_zero]

theorem kappa_empty {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V]
    {B : LinearMap.BilinForm K V} {E : Subgroup ↥(sesqUnitaryGroup B)}
    (F : FrameData K V B E) (hAlt : B.IsAlt) (hnd : B.Nondegenerate)
    (hsc : ∀ g : ↥(sesqUnitaryGroup B), (∀ e ∈ E, g * e = e * g) → g ^ 3 = 1 → g ∈ E) :
    IsEmpty F.κ := by
  classical
  have : Fact (Irreducible F.g) := ⟨F.hg⟩
  have hEfix : ∀ e ∈ E, ∀ w, (((e : ↥(sesqUnitaryGroup B)) :
      LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) (F.Φ (0, w)) = F.Φ (0, w) := by
    intro e he w; obtain ⟨k, hk⟩ := F.hact e he
    rw [hk]; congr 2; funext i; simp
  by_contra hne'
  rw [not_isEmpty_iff] at hne'
  obtain ⟨k₀⟩ := hne'
  set a := F.Φ (0, Pi.single k₀ 1) with ha
  have ha0 : a ≠ 0 := by
    intro h0
    have h1 : ((0 : Fin F.s → AdjoinRoot F.g), (Pi.single k₀ (1 : K) : F.κ → K)) = 0 :=
      F.Φ.injective (by rw [← ha, h0, map_zero])
    have h2 := congrArg (fun z : (Fin F.s → AdjoinRoot F.g) × (F.κ → K) => z.2 k₀) h1
    simp at h2
  obtain ⟨w', hw'⟩ : ∃ w', B a (F.Φ (0, w')) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply ha0
    refine hnd.1 a fun y => ?_
    obtain ⟨⟨d', w''⟩, rfl⟩ := F.Φ.surjective y
    rw [ha, F.hdec]
    simp only [Pi.zero_apply, map_zero, LinearMap.zero_apply, Finset.sum_const_zero, zero_add]
    exact hcon w''
  set b' := (B a (F.Φ (0, w')))⁻¹ • F.Φ (0, w') with hb'
  have hab : B a b' = 1 := by rw [hb', map_smul, smul_eq_mul, inv_mul_cancel₀ hw']
  have hEb : ∀ e ∈ E, (((e : ↥(sesqUnitaryGroup B)) : LinearMap.GeneralLinearGroup K V) :
      V →ₗ[K] V) b' = b' := fun e he => by rw [hb', map_smul, hEfix e he]
  obtain ⟨h, hiso, hhp, hha, hcomm⟩ :=
    exists_isom_hypPair (L := AdjoinRoot F.g) hAlt F.b F.hζp F.hζ1 F.hζω hab
  set u : LinearMap.GeneralLinearGroup K V := Units.ofPowEqOne h 3 hhp (by norm_num)
  have huval : (u : V →ₗ[K] V) = h := Units.val_ofPowEqOne h 3 hhp (by norm_num)
  have huU : u ∈ sesqUnitaryGroup B := mem_sesqUnitaryGroup.mpr fun x y => by
    rw [huval]; exact hiso x y
  have hgE : (⟨u, huU⟩ : ↥(sesqUnitaryGroup B)) ∈ E := by
    refine hsc _ (fun e he => Subtype.ext (Units.ext ?_)) (Subtype.ext ?_)
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul]
      change (u : V →ₗ[K] V) * _ = _ * (u : V →ₗ[K] V)
      rw [huval]
      exact hcomm _ (mem_sesqUnitaryGroup.mp e.2) (hEfix e he _) (hEb e he)
    · rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact Units.pow_ofPowEqOne hhp (by norm_num)
  apply hha; have h1 := hEfix _ hgE (Pi.single k₀ 1)
  change (u : V →ₗ[K] V) a = a at h1; rwa [huval] at h1

private theorem block_preserve {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V]
    {B : LinearMap.BilinForm K V} {E : Subgroup ↥(sesqUnitaryGroup B)}
    (F : FrameData K V B E) (G : ↥(sesqUnitaryGroup B))
    (hGτ : ∀ f, G * F.τ f = F.τ f * G)
    (H : V →ₗ[K] V) (hH : H = ((G : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V)) :
    HCommutes F H ∧ BlockMaps F H := by
  have : Fact (Irreducible F.g) := ⟨F.hg⟩
  have hτapp' : ∀ (f : Fin F.s → Multiplicative (ZMod 3))
      (x : (Fin F.s → AdjoinRoot F.g) × (F.κ → K)),
      (((F.τ f : ↥(sesqUnitaryGroup B)) : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V)
        (F.Φ x) = F.Φ (torEquiv F.hζp f x) := by
    intro f x; rw [F.hτapp, torEquiv_apply]
  have hHτ : HCommutes F H := by
    intro f v
    have h1 : (G : LinearMap.GeneralLinearGroup K V) *
        (F.τ f : LinearMap.GeneralLinearGroup K V) =
        (F.τ f : LinearMap.GeneralLinearGroup K V) *
          (G : LinearMap.GeneralLinearGroup K V) := by
      simpa using congrArg (fun y : ↥(sesqUnitaryGroup B) =>
        (y : LinearMap.GeneralLinearGroup K V)) (hGτ f)
    rw [hH]
    simpa only [Units.val_mul, Module.End.mul_apply] using
      congrArg (fun (y : V →ₗ[K] V) => y v)
        (congrArg (fun y : LinearMap.GeneralLinearGroup K V => (y : V →ₗ[K] V)) h1)
  have hval1 : (1 : ZMod 3).val = 1 := ZMod.val_one 3
  set δ : Fin F.s → Fin F.s → Multiplicative (ZMod 3) :=
    fun i => Pi.mulSingle i (ofAdd (1 : ZMod 3)) with hδ
  have hblock : BlockMaps F H := by
    intro i u
    set u' := (F.ζ - 1)⁻¹ * u with hu'
    have e1 : F.Φ (Pi.single i u, 0) =
        (((F.τ (δ i) : ↥(sesqUnitaryGroup B)) : LinearMap.GeneralLinearGroup K V) :
          V →ₗ[K] V) (F.Φ (Pi.single i u', 0)) - F.Φ (Pi.single i u', 0) := by
      rw [hτapp', torEquiv_single, ← map_sub, Prod.mk_sub_mk, sub_zero, ← Pi.single_sub]
      congr 3; simp only [hδ, Pi.mulSingle_eq_same, toAdd_ofAdd, hval1, pow_one]
      rw [← sub_one_mul, hu', ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr F.hζ1), one_mul]
    obtain ⟨⟨d', w'⟩, hdw⟩ := F.Φ.surjective (H (F.Φ (Pi.single i u', 0)))
    have hf1 : ∀ j', j' ≠ i → δ i j' = 1 := fun j' hj' => by
      rw [hδ]; exact Pi.mulSingle_eq_of_ne (M := fun _ => Multiplicative (ZMod 3)) hj' (ofAdd 1)
    refine ⟨(F.ζ ^ (toAdd (δ i i)).val - 1) * d' i, ?_⟩
    rw [e1, map_sub, hHτ, ← hdw, hτapp', ← map_sub, torEquiv_sub_self_of_single F.hζp hf1]
  exact ⟨hHτ, hblock⟩

private theorem block_linear {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V]
    {B : LinearMap.BilinForm K V} {E : Subgroup ↥(sesqUnitaryGroup B)}
    (F : FrameData K V B E) (H : V →ₗ[K] V)
    (hHτ : HCommutes F H) (hblock : BlockMaps F H) :
    ∃ T : Fin F.s → (AdjoinRoot F.g →ₗ[K] AdjoinRoot F.g),
      (∀ i u, H (F.Φ (Pi.single i u, 0)) = F.Φ (Pi.single i (T i u), 0)) ∧
      (∀ i u, T i (F.ζ * u) = F.ζ * T i u) ∧
      (∀ i u, T i u = T i 1 * u) := by
  have : Fact (Irreducible F.g) := ⟨F.hg⟩
  have hτapp' : ∀ (f : Fin F.s → Multiplicative (ZMod 3))
      (x : (Fin F.s → AdjoinRoot F.g) × (F.κ → K)),
      (((F.τ f : ↥(sesqUnitaryGroup B)) : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V)
        (F.Φ x) = F.Φ (torEquiv F.hζp f x) := by
    intro f x; rw [F.hτapp, torEquiv_apply]
  choose c hc using hblock
  have hval1 : (1 : ZMod 3).val = 1 := ZMod.val_one 3
  set δ : Fin F.s → Fin F.s → Multiplicative (ZMod 3) :=
    fun i => Pi.mulSingle i (ofAdd (1 : ZMod 3)) with hδ
  set T : Fin F.s → (AdjoinRoot F.g →ₗ[K] AdjoinRoot F.g) := fun i =>
    (LinearMap.proj i) ∘ₗ (LinearMap.fst K (Fin F.s → AdjoinRoot F.g) (F.κ → K)) ∘ₗ
      F.Φ.symm.toLinearMap ∘ₗ H ∘ₗ F.Φ.toLinearMap ∘ₗ
        (LinearMap.inl K (Fin F.s → AdjoinRoot F.g) (F.κ → K)) ∘ₗ
          (LinearMap.single K (fun _ => AdjoinRoot F.g) i) with hT
  have hTc : ∀ i u, H (F.Φ (Pi.single i u, 0)) = F.Φ (Pi.single i (T i u), 0) := by
    intro i u
    have e : T i u = c i u := by
      change (F.Φ.symm (H (F.Φ (Pi.single i u, 0)))).1 i = c i u
      rw [hc, LinearEquiv.symm_apply_apply]; simp
    rw [e, hc]
  have hTζ : ∀ i u, T i (F.ζ * u) = F.ζ * T i u := by
    intro i u
    have e1 : F.Φ (Pi.single i (F.ζ * u), 0) =
        (((F.τ (δ i) : ↥(sesqUnitaryGroup B)) : LinearMap.GeneralLinearGroup K V) :
          V →ₗ[K] V) (F.Φ (Pi.single i u, 0)) := by
      rw [hτapp', torEquiv_single]
      simp only [hδ, Pi.mulSingle_eq_same, toAdd_ofAdd, hval1, pow_one]
    have e2 := hTc i (F.ζ * u)
    rw [e1, hHτ, hTc i u, hτapp', torEquiv_single] at e2
    have e3 := congrArg (fun x : (Fin F.s → AdjoinRoot F.g) × (F.κ → K) => x.1 i)
      (F.Φ.injective e2)
    simpa only [Pi.single_eq_same, hδ, Pi.mulSingle_eq_same, toAdd_ofAdd, hval1, pow_one]
      using e3.symm
  have hTmul : ∀ i u, T i u = T i 1 * u := fun i =>
    linearMap_eq_mul_one_of_commute_root (T i) (by simpa only [F.hζ] using hTζ i)
  exact ⟨T, hTc, hTζ, hTmul⟩

private theorem lam_cube_H3 {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V]
    {B : LinearMap.BilinForm K V} {E : Subgroup ↥(sesqUnitaryGroup B)}
    (F : FrameData K V B E) (H : V →ₗ[K] V) (hK : Nat.card K = 2)
    (hnd : B.Nondegenerate) (hHiso : ∀ u v, B (H u) (H v) = B u v)
    (lam : Fin F.s → AdjoinRoot F.g)
    (hH_block : ∀ i u, H (F.Φ (Pi.single i u, 0)) =
      F.Φ (Pi.single i (lam i * u), 0))
    (hH_pow : ∀ (n : ℕ) (i : Fin F.s) (u : AdjoinRoot F.g),
      (H ^ n) (F.Φ (Pi.single i u, 0)) = F.Φ (Pi.single i (lam i ^ n * u), 0))
    (hκ : IsEmpty F.κ) :
    (∀ i, lam i ≠ 0) ∧ (∀ i, lam i ^ 3 = 1) ∧ H ^ 3 = 1 := by
  have : Fact (Irreducible F.g) := ⟨F.hg⟩
  have hHinj : Function.Injective H :=
    TauCeti.BilinForm.IsIsometry.injective hnd.1 (TauCeti.BilinForm.isIsometry_iff.mpr hHiso)
  have hlamne : ∀ i, lam i ≠ 0 := by
    intro i h0
    have hx : H (F.Φ (Pi.single i (1 : AdjoinRoot F.g), 0)) = 0 := by
      rw [hH_block, h0, zero_mul, Pi.single_zero, Prod.mk_zero_zero, map_zero]
    have hx0 : F.Φ (Pi.single i (1 : AdjoinRoot F.g), 0) = 0 :=
      hHinj (hx.trans (map_zero H).symm)
    have h1 : ((Pi.single i (1 : AdjoinRoot F.g) : Fin F.s → AdjoinRoot F.g),
        (0 : F.κ → K)) = 0 :=
      F.Φ.injective (by rw [hx0, map_zero])
    have h2 := congrArg (fun z : (Fin F.s → AdjoinRoot F.g) × (F.κ → K) => z.1 i) h1
    simp only [Pi.single_eq_same] at h2
    exact one_ne_zero h2
  have hlamcube : ∀ i, lam i ^ 3 = 1 := fun i =>
    adjoinRoot_pow_three_eq_one hK F.hgd (hlamne i)
  refine ⟨hlamne, hlamcube, LinearMap.ext fun v => ?_⟩
  obtain ⟨⟨d, w⟩, rfl⟩ := F.Φ.surjective v
  obtain rfl : w = 0 := Subsingleton.elim w 0
  have hd : ((d, 0) : (Fin F.s → AdjoinRoot F.g) × (F.κ → K)) =
      ∑ i, ((Pi.single i (d i), 0) :
        (Fin F.s → AdjoinRoot F.g) × (F.κ → K)) := by
    have h1 : d = ∑ i, Pi.single i (d i) := by
      conv_lhs => rw [pi_eq_sum_univ' d]
      refine Finset.sum_congr rfl fun i _ => ?_
      ext j
      by_cases hj : j = i <;> simp [hj]
    rw [h1]
    ext j <;> simp [Prod.fst_sum, Prod.snd_sum]
  rw [hd, map_sum, map_sum]
  simp only [Module.End.one_apply]
  rw [show (∑ i, (H ^ 3) (F.Φ (Pi.single i (d i), 0))) =
      ∑ i, F.Φ (Pi.single i (d i), 0) from by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hH_pow 3 i (d i), hlamcube i, one_mul]]

theorem centralizer_le_of_selfCent_spForm
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {B : LinearMap.BilinForm K V} (hAlt : B.IsAlt) (hnd : B.Nondegenerate)
    (E : Subgroup ↥(sesqUnitaryGroup B)) (hE : IsElemAbelian 3 E)
    (hsc : ∀ g : ↥(sesqUnitaryGroup B), (∀ e ∈ E, g * e = e * g) → g ^ 3 = 1 → g ∈ E) :
    Subgroup.centralizer (E : Set ↥(sesqUnitaryGroup B)) ≤ E := by
  let F : FrameData K V B E := Classical.choice (exists_frame_data hK hAlt hnd E hE)
  obtain ⟨hEτ, hτE⟩ := torus_range F hsc
  have hκ : IsEmpty F.κ := kappa_empty F hAlt hnd hsc
  intro G hG
  have hGτ : ∀ f, G * F.τ f = F.τ f * G := fun f => (hG (F.τ f) (hτE f)).symm
  set H : V →ₗ[K] V := ((G : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) with hH
  have hHiso : ∀ u v, B (H u) (H v) = B u v := fun u v => mem_sesqUnitaryGroup.mp G.2 u v
  obtain ⟨hHτ, hblock⟩ := block_preserve F G hGτ H hH
  obtain ⟨T, hTc, hTζ, hTmul⟩ := block_linear F H hHτ hblock
  set lam : Fin F.s → AdjoinRoot F.g := fun i => T i 1
  have hH_block : ∀ i u, H (F.Φ (Pi.single i u, 0)) =
      F.Φ (Pi.single i (lam i * u), 0) := by
    intro i u; rw [hTc, hTmul]
  have hH_pow : ∀ (n : ℕ) (i : Fin F.s) (u : AdjoinRoot F.g),
      (H ^ n) (F.Φ (Pi.single i u, 0)) = F.Φ (Pi.single i (lam i ^ n * u), 0) := by
    intro n
    induction n with
    | zero => intro i u; simp
    | succ n ih =>
        intro i u
        rw [pow_succ', Module.End.mul_apply, ih, hH_block, ← mul_assoc, ← pow_succ']
  obtain ⟨hlamne, hlamcube, hH3⟩ := lam_cube_H3 F H hK hnd hHiso lam hH_block hH_pow hκ
  have hG3 : G ^ 3 = 1 := by
    apply Subtype.ext; apply Units.ext
    have h1 : (((G ^ 3 : ↥(sesqUnitaryGroup B)) : LinearMap.GeneralLinearGroup K V) :
        V →ₗ[K] V) = H ^ 3 := by
      rw [Subgroup.coe_pow]
      change (((G : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) ^ 3) = H ^ 3
      rw [hH]
    rw [h1, hH3]; rfl
  exact hsc G (fun e he => (Subgroup.mem_centralizer_iff.mp hG e he).symm) hG3

end SpNS

end CFSG.StandardType
