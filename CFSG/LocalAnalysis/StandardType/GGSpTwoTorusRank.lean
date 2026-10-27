module

public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameTorus
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthExcEven

public section

open Polynomial Module Multiplicative CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalGroups.Alternating CFSG.Assembly

namespace CFSG.StandardType

namespace SpNS

private theorem symplecticTransvection_mul_comm_of_fix {K V : Type} [Field K] [AddCommGroup V]
    [Module K V] {B : LinearMap.BilinForm K V} (hB : B.IsAlt) {a : V}
    {g : LinearMap.GeneralLinearGroup K V}
    (hg : ∀ x y, B ((g : V →ₗ[K] V) x) ((g : V →ₗ[K] V) y) = B x y)
    (hga : (g : V →ₗ[K] V) a = a) :
    symplecticTransvection B hB a 1 * g = g * symplecticTransvection B hB a 1 := by
  refine Units.ext (LinearMap.ext fun x => ?_)
  rw [Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply,
    symplecticTransvection_apply, symplecticTransvection_apply, map_add, map_smul, hga,
    ← hg x a, hga]

private theorem symplecticTransvection_mul_pow_three {K V : Type} [Field K] [CharP K 2]
    [AddCommGroup V] [Module K V] {B : LinearMap.BilinForm K V} (hB : B.IsAlt) {u v : V}
    (huv : B u v = 1) :
    (symplecticTransvection B hB u 1 * symplecticTransvection B hB v 1) ^ 3 = 1 := by
  have hvu : B v u = 1 := by rw [← hB.neg_eq, huv, CharTwo.neg_eq]
  set T := symplecticTransvection B hB u 1 * symplecticTransvection B hB v 1 with hT
  have hTx : ∀ x, (T : V →ₗ[K] V) x = x + (B x u + B x v) • u + B x v • v := by
    intro x
    rw [hT, Units.val_mul, Module.End.mul_apply, symplecticTransvection_apply,
      symplecticTransvection_apply]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hvu,
      one_mul, mul_one]
    abel
  have hTu : ∀ x, B ((T : V →ₗ[K] V) x) u = B x u + B x v := by
    intro x
    rw [hTx]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hB.self_eq_zero, hvu]
    ring
  have hTv : ∀ x, B ((T : V →ₗ[K] V) x) v = B x u := by
    intro x
    rw [hTx]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hB.self_eq_zero, huv]
    linear_combination (B x v) * (CharTwo.two_eq_zero : (2 : K) = 0)
  refine Units.ext (LinearMap.ext fun x => ?_)
  rw [pow_succ, pow_succ, pow_one, Units.val_mul, Units.val_mul, Module.End.mul_apply,
    Module.End.mul_apply, Units.val_one, Module.End.one_apply]
  rw [hTx ((T : V →ₗ[K] V) ((T : V →ₗ[K] V) x)), hTu, hTv, hTu, hTv,
    hTx ((T : V →ₗ[K] V) x), hTu, hTv, hTx x]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  calc _ = x + (2 * (3 * B x u + 2 * B x v)) • u + (2 * (B x u + B x v)) • v := by module
    _ = x := by rw [h2, zero_mul, zero_mul, zero_smul, zero_smul, add_zero, add_zero]

private theorem card_eq_pow_of_selfCent_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {B : LinearMap.BilinForm K V} (hAlt : B.IsAlt) (hnd : B.Nondegenerate)
    (E : Subgroup ↥(sesqUnitaryGroup B)) (hE : IsElemAbelian 3 E)
    (hsc : ∀ g : ↥(sesqUnitaryGroup B), (∀ e ∈ E, g * e = e * g) → g ^ 3 = 1 → g ∈ E) :
    ∃ s : ℕ, Nat.card E = 3 ^ s ∧ finrank K V = 2 * s := by
  classical
  have : CharP K 2 :=
    finite_field_prime_power_characteristic Nat.prime_two le_rfl (hK.trans (pow_one 2).symm)
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hpq : 3 ∣ Nat.card K + 1 := by rw [hK]
  have : Fact (3 : ℕ).Prime := ⟨hp⟩
  have hpK : ((3 : ℕ) : K) ≠ 0 := TableBSymp.natCast_ne_zero_of_charTwo hp hp2
  have hne : ¬ IsUnit (cyclotomic 3 K) := by
    rw [Polynomial.isUnit_iff_degree_eq_zero, degree_eq_natDegree (cyclotomic_ne_zero 3 _),
      natDegree_cyclotomic, Nat.totient_prime hp]
    norm_num
  obtain ⟨g, hg, hgd⟩ := WfDvdMonoid.exists_irreducible_factor hne (cyclotomic_ne_zero 3 _)
  have : Fact (Irreducible g) := ⟨hg⟩
  have : Module.Finite K (AdjoinRoot g) := (CoordSL.rootPB g).finite
  have : Finite (AdjoinRoot g) := Module.finite_of_finite K
  have hζo := NSFrame.root_isPrimitiveRoot (g := g) hp hpK hgd
  set ζ := AdjoinRoot.root g
  have hζp : ζ ^ 3 = 1 := hζo.pow_eq_one
  set S : Set (Module.End K V) :=
    {x | ∃ e ∈ E, (((e : ↥(sesqUnitaryGroup B)) : LinearMap.GeneralLinearGroup K V) :
      V →ₗ[K] V) = x}
  have hSc : ∀ x ∈ S, ∀ x' ∈ S, Commute x x' := by
    rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩
    have h1 := TableB.IsElemAbelian.comm hE he he'
    have h2 := congrArg (fun y : ↥(sesqUnitaryGroup B) =>
      ((y : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V)) h1
    simp only [Subgroup.coe_mul, Units.val_mul] at h2
    exact h2
  have hSp : ∀ x ∈ S, x ^ 3 = 1 := by
    rintro _ ⟨e, he, rfl⟩
    have h1 := hE.2 e he
    have h2 := congrArg (fun y : ↥(sesqUnitaryGroup B) =>
      ((y : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V)) h1
    simpa using h2
  have hSB : ∀ x ∈ S, ∀ u w, B (x u) (x w) = B u w := by
    rintro _ ⟨e, -, rfl⟩ u w
    exact mem_sesqUnitaryGroup.mp e.2 u w
  have hdim := rootPB_dim_eq_two hp hp2 hpK hgd hpq
  obtain ⟨s, κ, _, Φ, β, hβ, hact, hdec⟩ := exists_nframe hp hp2 hpK hgd hdim
    (aeval_root_pow_pred hp hpK hgd hpq) hAlt hnd S hSc hSp hSB
  set b : Basis (Fin 2) K (AdjoinRoot g) := (CoordSL.rootPB g).basis.reindex (finCongr hdim)
  have hζβ : ∀ u v, β (ζ * u) (ζ * v) = β u v := fun u v => by
    have h1 := bilin_apply_det b hβ (Algebra.lmul K (AdjoinRoot g) ζ) u v
    rw [← Algebra.norm_apply, norm_root_eq_one hp hp2 hpK hgd hpq, one_mul] at h1
    exact h1
  set τ := torHom (K := K) hζp hdec hζβ
  have hτinj : Function.Injective τ := torHom_injective hζp hdec hζβ hζo
  have hτapp : ∀ f x, (((τ f : ↥(sesqUnitaryGroup B)) : LinearMap.GeneralLinearGroup K V) :
      V →ₗ[K] V) (Φ x) = Φ (torEquiv hζp f x) := fun f x => frameUnit_apply Φ _ x
  have hEτ : ∀ e ∈ E, ∃ f, τ f = e := by
    intro e he
    obtain ⟨k, hk⟩ := hact _ ⟨e, he, rfl⟩
    refine ⟨fun i => ofAdd (k i : ZMod 3), Subtype.ext (Units.ext (LinearMap.ext fun v => ?_))⟩
    obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective v
    rw [hτapp, torEquiv_apply, hk]
    congr 2
    funext i
    rw [toAdd_ofAdd, ZMod.val_natCast, ← pow_eq_pow_mod _ hζp]
  have hτE : ∀ f, τ f ∈ E := by
    intro f
    refine hsc _ (fun e he => ?_) ?_
    · obtain ⟨f', rfl⟩ := hEτ e he
      rw [← map_mul, ← map_mul, mul_comm]
    · rw [← map_pow]
      convert map_one τ
      funext i
      rw [Pi.pow_apply, Pi.one_apply, ← ofAdd_toAdd (f i ^ 3), toAdd_pow, nsmul_eq_mul,
        ZMod.natCast_self, zero_mul, ofAdd_zero]
  have hrange : τ.range = E := by
    ext e
    constructor
    · rintro ⟨f, rfl⟩
      exact hτE f
    · intro he
      obtain ⟨f, hf⟩ := hEτ e he
      exact ⟨f, hf⟩
  have hfix : ∀ x ∈ S, ∀ w, x (Φ (0, w)) = Φ (0, w) := by
    intro x hx w
    obtain ⟨k, hk⟩ := hact x hx
    rw [hk]
    congr 2
    funext i
    simp
  have hκ : IsEmpty κ := by
    by_contra hne
    rw [not_isEmpty_iff] at hne
    obtain ⟨i₀⟩ := hne
    set u := Φ (0, Pi.single i₀ 1) with hu
    have hu0 : u ≠ 0 := by
      intro h0
      have h1 : ((0 : Fin s → AdjoinRoot g), (Pi.single i₀ (1 : K) : κ → K)) = 0 :=
        Φ.injective (h0.trans (map_zero Φ).symm)
      have h2 := congrArg (fun x : (Fin s → AdjoinRoot g) × (κ → K) => x.2 i₀) h1
      simp at h2
    obtain ⟨y, hy⟩ : ∃ y, B u y ≠ 0 := by
      by_contra h
      push Not at h
      exact hu0 (hnd.1 u h)
    obtain ⟨⟨d', w'⟩, rfl⟩ := Φ.surjective y
    have hy' : B u (Φ (0, w')) ≠ 0 := by
      rw [hu, hdec] at hy
      simpa using hy
    set v := (B u (Φ (0, w')))⁻¹ • Φ (0, w') with hv
    have huv : B u v = 1 := by rw [hv, map_smul, smul_eq_mul, inv_mul_cancel₀ hy']
    have hfixu : ∀ x ∈ S, x u = u := fun x hx => hfix x hx _
    have hfixv : ∀ x ∈ S, x v = v := fun x hx => by rw [hv, map_smul, hfix x hx]
    set T := symplecticTransvection B hAlt u 1 * symplecticTransvection B hAlt v 1 with hT
    have hTmem : T ∈ sesqUnitaryGroup B := mem_sesqUnitaryGroup.mpr
      (mem_bilinIsometryGroup.mp ((bilinIsometryGroup B).mul_mem
        (symplecticTransvection_mem_bilinIsometryGroup hAlt u 1)
        (symplecticTransvection_mem_bilinIsometryGroup hAlt v 1)))
    have hTE : (⟨T, hTmem⟩ : ↥(sesqUnitaryGroup B)) ∈ E := by
      refine hsc _ (fun e he => Subtype.ext ?_) (Subtype.ext ?_)
      · have hiso := mem_sesqUnitaryGroup.mp e.2
        change T * (e : LinearMap.GeneralLinearGroup K V) =
          (e : LinearMap.GeneralLinearGroup K V) * T
        rw [hT, mul_assoc,
          symplecticTransvection_mul_comm_of_fix hAlt hiso (hfixv _ ⟨e, he, rfl⟩), ← mul_assoc,
          symplecticTransvection_mul_comm_of_fix hAlt hiso (hfixu _ ⟨e, he, rfl⟩), mul_assoc]
      · rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact symplecticTransvection_mul_pow_three hAlt huv
    have hTu : (T : V →ₗ[K] V) u = u := hfixu _ ⟨_, hTE, rfl⟩
    have hvu : B v u = 1 := by rw [← hAlt.neg_eq, huv, CharTwo.neg_eq]
    have hTu' : (T : V →ₗ[K] V) u = v := by
      rw [hT, Units.val_mul, Module.End.mul_apply, symplecticTransvection_apply,
        symplecticTransvection_apply, huv, one_mul, one_smul, map_add, LinearMap.add_apply,
        hAlt.self_eq_zero, hvu, zero_add, one_mul, one_smul, add_comm u v, add_assoc,
        ← two_smul K u, CharTwo.two_eq_zero, zero_smul, add_zero]
    have h1 : v = u := hTu'.symm.trans hTu
    rw [h1, hAlt.self_eq_zero] at huv
    exact zero_ne_one huv
  refine ⟨s, ?_, ?_⟩
  · rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hτinj).toEquiv, Nat.card_fun,
      Nat.card_fin, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  · rw [← Φ.finrank_eq, Module.finrank_prod, Module.finrank_pi_fintype,
      Module.finrank_fintype_fun_eq_card, Fintype.card_eq_zero, add_zero, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, (CoordSL.rootPB g).finrank, hdim,
      mul_comm]

end SpNS

open CFSG.Assembly.LowTwoRank

theorem spTwo_scRank {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) (m : ℕ) (hm : 2 ≤ m) :
    GGTorusEvenSignedPermEltSC 3 (LargeEvenProj (LargeEvenSpGroup K m)) fun k => k = m := by
  have : CharP K 2 :=
    finite_field_prime_power_characteristic Nat.prime_two le_rfl (hK.trans (pow_one 2).symm)
  have h := ggTorusEvenSignedPermEltSC_of_signedEltSC
    (ggSpNonsplitSignedEltInput_holds K m 3 hm Nat.prime_three (by rw [hK]))
  intro E hE h3 hsc
  obtain ⟨k, τ, hinj, hrange, -, hd, hP, hN⟩ := h E hE h3 hsc
  refine ⟨k, τ, hinj, hrange, ?_, hd, hP, hN⟩
  have : NeZero m := ⟨by omega⟩
  have hinjP : Function.Injective (LargeEvenProjMk (LargeEvenSpGroup K m)) :=
    AutPSp.proj_injective (n := m) (K := K)
  set e₁ : ↥(LargeEvenSpGroup K m) ≃* LargeEvenProj (LargeEvenSpGroup K m) :=
    MulEquiv.ofBijective (LargeEvenProjMk (LargeEvenSpGroup K m))
      ⟨hinjP, QuotientGroup.mk'_surjective _⟩
  set e₂ : ↥(StatedSp m K) ≃*
      ↥(sesqUnitaryGroup (CFSG.RankThree.Classical.spForm m K)) :=
    (MonoidHom.ofInjective CFSG.RankThree.Classical.spLin_injective).trans
      (MulEquiv.subgroupCongr CFSG.RankThree.Classical.range_spLin)
  have hLS : LargeEvenSpGroup K m = StatedSp m K := rfl
  set e := e₁.symm.trans ((MulEquiv.subgroupCongr hLS).trans e₂)
  have hmem : ∀ x : LargeEvenProj (LargeEvenSpGroup K m),
      e x ∈ E.map e.toMonoidHom ↔ x ∈ E := fun x =>
    ⟨fun ⟨y, hy, hyx⟩ => e.injective hyx ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
  have hsc' : ∀ g, (∀ x ∈ E.map e.toMonoidHom, g * x = x * g) → g ^ 3 = 1 →
      g ∈ E.map e.toMonoidHom := by
    intro g hg hgp
    obtain ⟨y, rfl⟩ := e.surjective g
    rw [hmem]
    refine hsc y (fun x hx => e.injective ?_) ?_
    · rw [map_mul, map_mul]
      exact hg _ ((hmem x).mpr hx)
    · apply e.injective
      rw [map_pow, hgp, map_one]
  obtain ⟨s, hs, hfr⟩ := SpNS.card_eq_pow_of_selfCent_two hK
    CFSG.RankThree.Classical.spForm_isAlt CFSG.RankThree.Classical.spForm_nondegenerate
    (E.map e.toMonoidHom) (TableB.isElemAbelian_map hE e.toMonoidHom) hsc'
  have hcE : Nat.card E = 3 ^ k := by
    rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_fun,
      Nat.card_fin, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hcard : Nat.card (E.map e.toMonoidHom) = Nat.card E :=
    (Nat.card_congr (E.equivMapOfInjective _ e.injective).toEquiv).symm
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin] at hfr
  rw [hcard, hcE] at hs
  have hsm : s = m := by omega
  rw [hsm] at hs
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) hs

end CFSG.StandardType

end
