module

public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOrthNsTorus
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalOrthogonalShearCModel
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelOmMvBasic
public import CFSG.RankThree.OrthogonalInvolutions.Witt

public section

open Polynomial Module Multiplicative Matrix
open scoped commutatorElement

namespace CFSG.StandardType

namespace OrthNs

open CFSG.Assembly SpNS NbrOrth SpCoord CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.SeitzReduction.OrthogonalShearC

structure FrameData {K : Type} [Field K] {d : ℕ}
    (Q : QuadraticForm K (Fin d → K)) (g : K[X]) [Fact (Irreducible g)]
    (p : ℕ) (X : Subgroup (GL (Fin d) K)) where
  s : ℕ
  κ : Type
  fintype : Fintype κ
  Φ : ((Fin s → AdjoinRoot g) × (κ → K)) ≃ₗ[K] (Fin d → K)
  β : LinearMap.BilinForm K (AdjoinRoot g)
  hβ : β.IsAlt
  hdec : ∀ d d' w w', QuadraticMap.polarBilin Q (Φ (d, w)) (Φ (d', w')) =
    ∑ i, β (d i) (d' i) + QuadraticMap.polarBilin Q (Φ (0, w)) (Φ (0, w'))
  act : Fin s → Prop
  hβnd : ∀ i, act i → ∀ u, (∀ v, β u v = 0) → u = 0
  hact : ∀ x ∈ X, ∃ k : Fin s → ℕ, ∀ d w,
    glin x (Φ (d, w)) = Φ (fun i => AdjoinRoot.root g ^ k i * d i, w)
  hQadd : ∀ i u v, Q (Φ (Pi.single i (u + v), 0)) =
    Q (Φ (Pi.single i u, 0)) + Q (Φ (Pi.single i v, 0)) + β u v
  hQζ : ∀ i, act i → ∀ u, Q (Φ (Pi.single i (AdjoinRoot.root g * u), 0)) =
    Q (Φ (Pi.single i u, 0))
  hfix : ∀ x ∈ X, ∀ k : Fin s → ℕ, (∀ d w,
    glin x (Φ (d, w)) = Φ (fun i => AdjoinRoot.root g ^ k i * d i, w)) →
    ∀ i, ¬ act i → AdjoinRoot.root g ^ k i = 1

structure FrameTorus {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    (Q : QuadraticForm K (Fin d → K)) (g : K[X]) [Fact (Irreducible g)]
    (p : ℕ) (X : Subgroup (GL (Fin d) K)) : Type 1 where
  s : ℕ
  κ : Type
  fintype : Fintype κ
  Φ : ((Fin s → AdjoinRoot g) × (κ → K)) ≃ₗ[K] (Fin d → K)
  β : LinearMap.BilinForm K (AdjoinRoot g)
  hβ : β.IsAlt
  hdec : ∀ d d' w w', QuadraticMap.polarBilin Q (Φ (d, w)) (Φ (d', w')) =
    ∑ i, β (d i) (d' i) + QuadraticMap.polarBilin Q (Φ (0, w)) (Φ (0, w'))
  act : Fin s → Prop
  hβnd : ∀ i, act i → ∀ u, (∀ v, β u v = 0) → u = 0
  hact : ∀ x ∈ X, ∃ k : Fin s → ℕ, ∀ d w,
    glin x (Φ (d, w)) = Φ (fun i => AdjoinRoot.root g ^ k i * d i, w)
  hQadd : ∀ i u v, Q (Φ (Pi.single i (u + v), 0)) =
    Q (Φ (Pi.single i u, 0)) + Q (Φ (Pi.single i v, 0)) + β u v
  hQζ : ∀ i, act i → ∀ u, Q (Φ (Pi.single i (AdjoinRoot.root g * u), 0)) =
    Q (Φ (Pi.single i u, 0))
  hfix : ∀ x ∈ X, ∀ k : Fin s → ℕ, (∀ d w,
    glin x (Φ (d, w)) = Φ (fun i => AdjoinRoot.root g ^ k i * d i, w)) →
    ∀ i, ¬ act i → AdjoinRoot.root g ^ k i = 1
  T : Subgroup (GL (Fin d) K)
  hTder : T ≤ matrixDerived Q
  hTcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a
  hTpow : ∀ a ∈ T, a ^ p = 1
  hXT : X ≤ T
  hTcard : Nat.card T = p ^ Nat.card {i : Fin s // act i}
  hTtor : ∀ k : Fin s → ℕ, (∀ i, ¬ act i → k i = 0) →
    ∃ t ∈ T, ∀ d w, glin t (Φ (d, w)) = Φ (fun i => AdjoinRoot.root g ^ k i * d i, w)

private structure FrameSetup {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    (Q : QuadraticForm K (Fin d → K)) (g : K[X]) [Fact (Irreducible g)] (p : ℕ)
    (X : Subgroup (GL (Fin d) K)) where
  hp2 : p ≠ 2
  hpK : (p : K) ≠ 0
  hζo : IsPrimitiveRoot (AdjoinRoot.root g) p
  hζp : AdjoinRoot.root g ^ p = 1
  hiso : ∀ x ∈ X, ∀ v, Q (glin x v) = Q v
  hAlt : (QuadraticMap.polarBilin Q).IsAlt
  hSc : ∀ x ∈ glin '' (X : Set (GL (Fin d) K)),
    ∀ x' ∈ glin '' (X : Set (GL (Fin d) K)), Commute x x'
  hSp : ∀ x ∈ glin '' (X : Set (GL (Fin d) K)), x ^ p = 1
  hSB : ∀ x ∈ glin '' (X : Set (GL (Fin d) K)), ∀ u w,
    QuadraticMap.polarBilin Q (x u) (x w) = QuadraticMap.polarBilin Q u w

private theorem exists_frameSetup {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {g : K[X]} [Fact (Irreducible g)] {p : ℕ}
    (hp : p.Prime) (hpq : p ∣ Nat.card K + 1) (hgd : g ∣ cyclotomic p K)
    {X : Subgroup (GL (Fin d) K)} (hX : X ≤ matrixDerived Q)
    (hXc : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a)
    (hXp : ∀ a ∈ X, a ^ p = 1) : Nonempty (FrameSetup Q g p X) := by
  classical
  have hp2 : p ≠ 2 := ne_two_of_dvd_card_add_one hpq
  have hpK : (p : K) ≠ 0 := TableBSymp.natCast_ne_zero_of_charTwo hp hp2
  have hζo := NSFrame.root_isPrimitiveRoot (g := g) hp hpK hgd
  have hζp : AdjoinRoot.root g ^ p = 1 := hζo.pow_eq_one
  have hAlt : (QuadraticMap.polarBilin Q).IsAlt := fun x => by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, two_nsmul,
      CharTwo.add_self_eq_zero]
  have hiso : ∀ x ∈ X, ∀ v, Q (glin x v) = Q v := fun x hx v => by
    rw [glin_apply]
    exact (mem_matrixIsometries_iff Q x).mp (matrixDerived_le_isometries Q (hX hx)) v
  set S : Set (Module.End K (Fin d → K)) := glin '' (X : Set (GL (Fin d) K)) with hS
  have hSc : ∀ x ∈ S, ∀ x' ∈ S, Commute x x' := by
    rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩
    have h1 := hXc e he e' he'
    show glin e * glin e' = glin e' * glin e
    rw [← glin_mul, ← glin_mul, h1]
  have hSp : ∀ x ∈ S, x ^ p = 1 := by
    rintro _ ⟨e, he, rfl⟩
    show glin e ^ p = 1
    rw [← glin_pow, hXp e he, glin_one]
  have hSB : ∀ x ∈ S, ∀ u w, QuadraticMap.polarBilin Q (x u) (x w) =
      QuadraticMap.polarBilin Q u w := by
    rintro _ ⟨e, he, rfl⟩ u w
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
    rw [← map_add, hiso e he, hiso e he, hiso e he]
  exact ⟨FrameSetup.mk hp2 hpK hζo hζp hiso hAlt hSc hSp hSB⟩

private theorem frameData_hQζ {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {g : K[X]} [Fact (Irreducible g)] {p : ℕ}
    (hp : p.Prime) {s : ℕ} {κ : Type}
    {Φ : ((Fin s → AdjoinRoot g) × (κ → K)) ≃ₗ[K] (Fin d → K)}
    {X : Subgroup (GL (Fin d) K)}
    (hiso : ∀ x ∈ X, ∀ v, Q (glin x v) = Q v)
    (hexp : ∀ x ∈ X, ∃ k : Fin s → ℕ, ∀ d w,
      glin x (Φ (d, w)) = Φ (fun i => AdjoinRoot.root g ^ k i * d i, w))
    (hsingle : ∀ (k : Fin s → ℕ) (i : Fin s) (u : AdjoinRoot g),
      (fun j => AdjoinRoot.root g ^ k j * (Pi.single i u : Fin s → AdjoinRoot g) j) =
        Pi.single i (AdjoinRoot.root g ^ k i * u))
    (hζo : IsPrimitiveRoot (AdjoinRoot.root g) p)
    (hζp : AdjoinRoot.root g ^ p = 1) :
    ∀ i, (∃ x ∈ X, ∃ u : AdjoinRoot g,
      glin x (Φ (Pi.single i u, 0)) ≠ Φ (Pi.single i u, 0)) →
      ∀ u, Q (Φ (Pi.single i (AdjoinRoot.root g * u), 0)) =
        Q (Φ (Pi.single i u, 0)) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rintro i ⟨x, hx, u₀, hu₀⟩ u
  obtain ⟨k, hk⟩ := hexp x hx
  have hinv : ∀ v, Q (Φ (Pi.single i (AdjoinRoot.root g ^ k i * v), 0)) =
      Q (Φ (Pi.single i v, 0)) := fun v => by
    have h1 := hiso x hx (Φ (Pi.single i v, 0))
    rw [hk, hsingle] at h1
    exact h1
  have hk1 : AdjoinRoot.root g ^ k i ≠ 1 := by
    intro h1
    apply hu₀
    rw [hk, hsingle, h1, one_mul]
  have hcop : (k i).Coprime p := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    rintro ⟨c, hc⟩
    apply hk1
    rw [hc, pow_mul, hζp, one_pow]
  obtain ⟨m, -, hm⟩ := (hζo.pow_of_coprime (k i) hcop).eq_pow_of_pow_eq_one hζp
  have hpowinv : ∀ (m : ℕ) v, Q (Φ (Pi.single i ((AdjoinRoot.root g ^ k i) ^ m * v), 0)) =
      Q (Φ (Pi.single i v, 0)) := by
    intro m
    induction m with
    | zero => intro v; rw [pow_zero, one_mul]
    | succ m ih => intro v; rw [pow_succ', mul_assoc, hinv, ih]
  rw [← hm, hpowinv]

private theorem frameData_hfix {K : Type} [Field K] {d : ℕ}
    {g : K[X]} [Fact (Irreducible g)]
    {s : ℕ} {κ : Type} {Φ : ((Fin s → AdjoinRoot g) × (κ → K)) ≃ₗ[K] (Fin d → K)}
    {X : Subgroup (GL (Fin d) K)}
    (hsingle : ∀ (k : Fin s → ℕ) (i : Fin s) (u : AdjoinRoot g),
      (fun j => AdjoinRoot.root g ^ k j * (Pi.single i u : Fin s → AdjoinRoot g) j) =
        Pi.single i (AdjoinRoot.root g ^ k i * u))
    :
    ∀ x ∈ X, ∀ k : Fin s → ℕ, (∀ d w,
      glin x (Φ (d, w)) = Φ (fun i => AdjoinRoot.root g ^ k i * d i, w)) →
      ∀ i, ¬ (∃ x ∈ X, ∃ u : AdjoinRoot g,
        glin x (Φ (Pi.single i u, 0)) ≠ Φ (Pi.single i u, 0)) →
      AdjoinRoot.root g ^ k i = 1 := by
  intro x hx k hk i hi
  by_contra h1
  apply hi
  refine ⟨x, hx, 1, fun h2 => h1 ?_⟩
  rw [hk, hsingle, mul_one] at h2
  have h3 := congrArg (fun y : (Fin s → AdjoinRoot g) × (κ → K) => y.1 i) (Φ.injective h2)
  simpa using h3

private theorem frameData_hβnd {K : Type} [Field K] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {g : K[X]} [Fact (Irreducible g)]
    {s : ℕ} {κ : Type} {Φ : ((Fin s → AdjoinRoot g) × (κ → K)) ≃ₗ[K] (Fin d → K)}
    {β : LinearMap.BilinForm K (AdjoinRoot g)}
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdec : ∀ d d' w w', QuadraticMap.polarBilin Q (Φ (d, w)) (Φ (d', w')) =
      ∑ i, β (d i) (d' i) + QuadraticMap.polarBilin Q (Φ (0, w)) (Φ (0, w')))
    (act : Fin s → Prop) :
    ∀ i, act i → ∀ u, (∀ v, β u v = 0) → u = 0 := by
  intro i _ u hu
  have h1 : Φ (Pi.single i u, (0 : κ → K)) = 0 := by
    apply hnd.1
    intro y
    obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective y
    rw [hdec, Finset.sum_eq_single i]
    · have h0 : Φ ((0 : Fin s → AdjoinRoot g), (0 : κ → K)) = 0 := map_zero Φ
      simp [Pi.single_eq_same, hu (d i), h0, LinearMap.map_zero₂]
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have h2 : (Pi.single i u, (0 : κ → K)) = 0 := Φ.injective (by simpa using h1)
  have h3 := congrArg (fun z : (Fin s → AdjoinRoot g) × (κ → K) => z.1 i) h2
  simpa using h3

theorem exists_frameData {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} (hnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    {p : ℕ} (hp : p.Prime) (hpq : p ∣ Nat.card K + 1)
    {g : K[X]} [Fact (Irreducible g)] (hgd : g ∣ cyclotomic p K)
    {X : Subgroup (GL (Fin d) K)} (hX : X ≤ matrixDerived Q)
    (hXc : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a)
    (hXp : ∀ a ∈ X, a ^ p = 1) : Nonempty (FrameData Q g p X) := by
  classical
  obtain ⟨SS⟩ := exists_frameSetup hp hpq hgd hX hXc hXp
  obtain ⟨s, κ, hκ, Φ, β, hβ, hact, hdec⟩ := exists_nframe hp SS.hp2 SS.hpK hgd
    (rootPB_dim_eq_two hp SS.hp2 SS.hpK hgd hpq)
    (aeval_root_pow_pred hp SS.hpK hgd hpq) SS.hAlt hnd
    (glin '' (X : Set (GL (Fin d) K))) SS.hSc SS.hSp SS.hSB
  have hQadd : ∀ i u v, Q (Φ (Pi.single i (u + v), 0)) =
      Q (Φ (Pi.single i u, 0)) + Q (Φ (Pi.single i v, 0)) + β u v := fun i u v =>
    quad_single_add hdec i u v
  have hsingle : ∀ (k : Fin s → ℕ) (i : Fin s) (u : AdjoinRoot g),
      (fun j => AdjoinRoot.root g ^ k j * (Pi.single i u : Fin s → AdjoinRoot g) j) =
        Pi.single i (AdjoinRoot.root g ^ k i * u) := by
    intro k i u
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [Pi.single_eq_of_ne hj]
  have hexp : ∀ x ∈ X, ∃ k : Fin s → ℕ, ∀ d w,
      glin x (Φ (d, w)) = Φ (fun i => AdjoinRoot.root g ^ k i * d i, w) := fun x hx =>
    hact (glin x) ⟨x, hx, rfl⟩
  let act : Fin s → Prop := fun i => ∃ x ∈ X, ∃ u : AdjoinRoot g,
    glin x (Φ (Pi.single i u, 0)) ≠ Φ (Pi.single i u, 0)
  have hQζ : ∀ i, act i → ∀ u, Q (Φ (Pi.single i (AdjoinRoot.root g * u), 0)) =
      Q (Φ (Pi.single i u, 0)) :=
    frameData_hQζ (X := X) hp SS.hiso hexp hsingle SS.hζo SS.hζp
  have hfix : ∀ x ∈ X, ∀ k : Fin s → ℕ, (∀ d w,
      glin x (Φ (d, w)) = Φ (fun i => AdjoinRoot.root g ^ k i * d i, w)) →
      ∀ i, ¬ act i → AdjoinRoot.root g ^ k i = 1 :=
    frameData_hfix (X := X) hsingle
  have hβnd := frameData_hβnd (β := β) hnd hdec act
  exact ⟨FrameData.mk s κ hκ Φ β hβ hdec act hβnd hexp hQadd hQζ hfix⟩

private theorem torus_hζβ {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {g : K[X]} [Fact (Irreducible g)] {p : ℕ}
    {X : Subgroup (GL (Fin d) K)} (hp : p.Prime) (hpq : p ∣ Nat.card K + 1)
    (hgd : g ∣ cyclotomic p K) (D : FrameData Q g p X) :
    ∃ b : Basis (Fin 2) K (AdjoinRoot g),
      ∀ u v, D.β (AdjoinRoot.root g * u) (AdjoinRoot.root g * v) = D.β u v := by
  have hp2 : p ≠ 2 := ne_two_of_dvd_card_add_one hpq
  have hpK : (p : K) ≠ 0 := TableBSymp.natCast_ne_zero_of_charTwo hp hp2
  let b : Basis (Fin 2) K (AdjoinRoot g) :=
    (CoordSL.rootPB g).basis.reindex (finCongr (rootPB_dim_eq_two hp hp2 hpK hgd hpq))
  refine ⟨b, ?_⟩
  intro u v
  have h1 := bilin_apply_det b D.hβ (Algebra.lmul K (AdjoinRoot g) (AdjoinRoot.root g)) u v
  rw [← Algebra.norm_apply, norm_root_eq_one hp hp2 hpK hgd hpq, one_mul] at h1
  exact h1

private theorem exists_torusExt {K : Type} [Field K] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {g : K[X]} [Fact (Irreducible g)] {p : ℕ}
    {X : Subgroup (GL (Fin d) K)} (D : FrameData Q g p X) :
    ∃ (k : ℕ) (eJ : Fin k ≃ {i : Fin D.s // D.act i})
      (ext : (Fin k → Multiplicative (ZMod p)) →* (Fin D.s → Multiplicative (ZMod p))),
      (∀ f i (h : D.act i), ext f i = f (eJ.symm ⟨i, h⟩)) ∧
      (∀ f i, ¬ D.act i → ext f i = 1) ∧ Function.Injective ext := by
  classical
  haveI : Fintype {i : Fin D.s // D.act i} := Fintype.ofFinite _
  obtain ⟨k, ⟨eJ⟩⟩ : ∃ k : ℕ, Nonempty (Fin k ≃ {i : Fin D.s // D.act i}) :=
    ⟨_, ⟨(Fintype.equivFin {i : Fin D.s // D.act i}).symm⟩⟩
  obtain ⟨ext, hext_act, hext_nact⟩ : ∃ ext : (Fin k → Multiplicative (ZMod p)) →*
      (Fin D.s → Multiplicative (ZMod p)),
      (∀ f i (h : D.act i), ext f i = f (eJ.symm ⟨i, h⟩)) ∧
        (∀ f i, ¬ D.act i → ext f i = 1) := by
    refine ⟨{ toFun := fun f i => if h : D.act i then f (eJ.symm ⟨i, h⟩) else 1
              map_one' := ?_
              map_mul' := ?_ }, fun f i h => ?_, fun f i h => ?_⟩
    · funext i
      by_cases h : D.act i <;> simp [h]
    · intro f f'
      funext i
      by_cases h : D.act i <;> simp [h]
    · simp [h]
    · simp [h]
  refine ⟨k, eJ, ext, hext_act, hext_nact, ?_⟩
  intro f f' h
  funext a
  have h1 := congrFun h (eJ a : Fin D.s)
  rw [hext_act f _ (eJ a).2, hext_act f' _ (eJ a).2] at h1
  simpa using h1

private theorem exists_torusGL {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {g : K[X]} [Fact (Irreducible g)] {p : ℕ} [NeZero p]
    {X : Subgroup (GL (Fin d) K)} (hp : p.Prime) (hpq : p ∣ Nat.card K + 1)
    (hgd : g ∣ cyclotomic p K) (hζp : AdjoinRoot.root g ^ p = 1)
    (hζo : IsPrimitiveRoot (AdjoinRoot.root g) p) (D : FrameData Q g p X) :
    ∃ (b : Basis (Fin 2) K (AdjoinRoot g))
      (hζβ : ∀ u v, D.β (AdjoinRoot.root g * u) (AdjoinRoot.root g * v) = D.β u v)
      (torGL : (Fin D.s → Multiplicative (ZMod p)) →* GL (Fin d) K),
      (∀ F, torGL F = frameGL D.Φ (torEquiv hζp F)) ∧ Function.Injective torGL := by
  obtain ⟨b, hζβ⟩ := torus_hζβ hp hpq hgd D
  refine ⟨b, hζβ, (Matrix.GeneralLinearGroup.toLin.symm.toMonoidHom).comp
    ((sesqUnitaryGroup (QuadraticMap.polarBilin Q)).subtype.comp
      (torHom (K := K) hζp D.hdec hζβ)), fun F => rfl, ?_⟩
  rw [MonoidHom.coe_comp, MonoidHom.coe_comp]
  exact Matrix.GeneralLinearGroup.toLin.symm.injective.comp
    (Subtype.val_injective.comp (torHom_injective hζp D.hdec hζβ hζo))

private structure TorusSetup {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {g : K[X]} [Fact (Irreducible g)] {p : ℕ} [NeZero p]
    {X : Subgroup (GL (Fin d) K)} (hζp : AdjoinRoot.root g ^ p = 1)
    (D : FrameData Q g p X) where
  k : ℕ
  eJ : Fin k ≃ {i : Fin D.s // D.act i}
  ext : (Fin k → Multiplicative (ZMod p)) →* (Fin D.s → Multiplicative (ZMod p))
  hext_act : ∀ f i (h : D.act i), ext f i = f (eJ.symm ⟨i, h⟩)
  hext_nact : ∀ f i, ¬ D.act i → ext f i = 1
  hext_inj : Function.Injective ext
  b : Basis (Fin 2) K (AdjoinRoot g)
  hζβ : ∀ u v, D.β (AdjoinRoot.root g * u) (AdjoinRoot.root g * v) = D.β u v
  torGL : (Fin D.s → Multiplicative (ZMod p)) →* GL (Fin d) K
  htorGL : ∀ F, torGL F = frameGL D.Φ (torEquiv hζp F)
  htorGL_inj : Function.Injective torGL

private def torusT {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {g : K[X]} [Fact (Irreducible g)] {p : ℕ} [NeZero p]
    {X : Subgroup (GL (Fin d) K)} {hζp : AdjoinRoot.root g ^ p = 1}
    {D : FrameData Q g p X} (TS : TorusSetup hζp D) : Subgroup (GL (Fin d) K) :=
  (TS.torGL.comp TS.ext).range

private theorem exists_torusSetup {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {g : K[X]} [Fact (Irreducible g)] {p : ℕ} [NeZero p]
    {X : Subgroup (GL (Fin d) K)} (hp : p.Prime) (hpq : p ∣ Nat.card K + 1)
    (hgd : g ∣ cyclotomic p K) (hζp : AdjoinRoot.root g ^ p = 1)
    (hζo : IsPrimitiveRoot (AdjoinRoot.root g) p) (D : FrameData Q g p X) :
    Nonempty (TorusSetup hζp D) := by
  obtain ⟨k, eJ, ext, hext_act, hext_nact, hext_inj⟩ := exists_torusExt D
  obtain ⟨b, hζβ, torGL, htorGL, htorGL_inj⟩ := exists_torusGL hp hpq hgd hζp hζo D
  exact ⟨TorusSetup.mk k eJ ext hext_act hext_nact hext_inj b hζβ torGL htorGL htorGL_inj⟩

private theorem torus_hτQ {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {g : K[X]} [Fact (Irreducible g)] {p : ℕ} [NeZero p]
    {X : Subgroup (GL (Fin d) K)} {hζp : AdjoinRoot.root g ^ p = 1}
    {D : FrameData Q g p X} (TS : TorusSetup hζp D) :
    ∀ f x, Q (D.Φ (torEquiv hζp (TS.ext f) x)) = Q (D.Φ x) := by
  intro f x
  refine quad_mono D.hdec 1 (fun i u => ?_) x
  show Q (D.Φ (Pi.single i (AdjoinRoot.root g ^ (toAdd (TS.ext f i)).val * u), 0)) =
    Q (D.Φ (Pi.single i u, 0))
  by_cases hi : D.act i
  · have hpow : ∀ m : ℕ, Q (D.Φ (Pi.single i
        (AdjoinRoot.root g ^ m * u), 0)) = Q (D.Φ (Pi.single i u, 0)) := by
      intro m
      induction m with
      | zero => rw [pow_zero, one_mul]
      | succ m ih => rw [pow_succ', mul_assoc]; exact (D.hQζ i hi _).trans ih
    exact hpow _
  · rw [TS.hext_nact f i hi, toAdd_one, ZMod.val_zero, pow_zero, one_mul]

private theorem torus_hτiso {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {g : K[X]} [Fact (Irreducible g)] {p : ℕ} [NeZero p]
    {X : Subgroup (GL (Fin d) K)} {hζp : AdjoinRoot.root g ^ p = 1}
    {D : FrameData Q g p X} (TS : TorusSetup hζp D)
    (hτQ : ∀ f x, Q (D.Φ (torEquiv hζp (TS.ext f) x)) = Q (D.Φ x)) :
    ∀ f, TS.torGL (TS.ext f) ∈ matrixIsometries Q := fun f =>
  (mem_matrixIsometries_iff Q _).mpr fun v => by
    rw [matrixLinearEquiv_apply, TS.htorGL]
    exact TableBOrth.isometry_of_mem_orthGroup (frameGL_mem_orth D.Φ (hτQ f)) v

private theorem torus_hτp {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {g : K[X]} [Fact (Irreducible g)] {p : ℕ} [NeZero p]
    {X : Subgroup (GL (Fin d) K)} {hζp : AdjoinRoot.root g ^ p = 1}
    {D : FrameData Q g p X} (TS : TorusSetup hζp D) :
    ∀ f, TS.torGL (TS.ext f) ^ p = 1 := fun f => by
  rw [← map_pow, ← map_pow, ReflInner.pow_eq_one_of_zmod, map_one, map_one]

private theorem torus_Tder {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {g : K[X]} [Fact (Irreducible g)] {p : ℕ} [NeZero p]
    {X : Subgroup (GL (Fin d) K)} {hζp : AdjoinRoot.root g ^ p = 1}
    {D : FrameData Q g p X} (TS : TorusSetup hζp D)
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hp : p.Prime) (hpq : p ∣ Nat.card K + 1)
    (hτiso : ∀ f, TS.torGL (TS.ext f) ∈ matrixIsometries Q) :
    torusT TS ≤ matrixDerived Q := by
  rintro _ ⟨f, rfl⟩
  exact mem_matrixDerived_of_odd hnd hT (hτiso f)
    (Odd.of_dvd_nat (hp.odd_of_ne_two (ne_two_of_dvd_card_add_one hpq))
      (orderOf_dvd_of_pow_eq_one (torus_hτp TS f)))

private theorem torus_Tcomm {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {g : K[X]} [Fact (Irreducible g)] {p : ℕ} [NeZero p]
    {X : Subgroup (GL (Fin d) K)} {hζp : AdjoinRoot.root g ^ p = 1}
    {D : FrameData Q g p X} (TS : TorusSetup hζp D) :
    ∀ a ∈ torusT TS, ∀ b ∈ torusT TS, a * b = b * a := by
  rintro _ ⟨f, rfl⟩ _ ⟨f', rfl⟩
  change TS.torGL (TS.ext f) * TS.torGL (TS.ext f') =
    TS.torGL (TS.ext f') * TS.torGL (TS.ext f)
  calc TS.torGL (TS.ext f) * TS.torGL (TS.ext f') =
        TS.torGL (TS.ext f * TS.ext f') := (map_mul TS.torGL _ _).symm
    _ = TS.torGL (TS.ext f' * TS.ext f) := by rw [mul_comm]
    _ = TS.torGL (TS.ext f') * TS.torGL (TS.ext f) := map_mul TS.torGL _ _

private theorem torus_Tpow {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {g : K[X]} [Fact (Irreducible g)] {p : ℕ} [NeZero p]
    {X : Subgroup (GL (Fin d) K)} {hζp : AdjoinRoot.root g ^ p = 1}
    {D : FrameData Q g p X} (TS : TorusSetup hζp D) :
    ∀ a ∈ torusT TS, a ^ p = 1 := by
  rintro _ ⟨f, rfl⟩
  simpa only [MonoidHom.comp_apply] using torus_hτp TS f

private theorem torus_XT {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {g : K[X]} [Fact (Irreducible g)] {p : ℕ} [NeZero p]
    {X : Subgroup (GL (Fin d) K)} {hζp : AdjoinRoot.root g ^ p = 1}
    {D : FrameData Q g p X} (TS : TorusSetup hζp D)
    (hζo : IsPrimitiveRoot (AdjoinRoot.root g) p) :
    X ≤ torusT TS := by
  intro x hx
  obtain ⟨kx, hkx⟩ := D.hact x hx
  let f0 : Fin TS.k → Multiplicative (ZMod p) := fun a =>
    ofAdd ((kx (TS.eJ a : Fin D.s) : ℕ) : ZMod p)
  refine ⟨f0, ?_⟩
  change TS.torGL (TS.ext f0) = x
  apply eq_of_glin
  intro v
  obtain ⟨⟨d, w⟩, rfl⟩ := D.Φ.surjective v
  rw [TS.htorGL, glin_apply, frameGL_mulVec, hkx, torEquiv_apply]
  congr 2
  funext i
  congr 1
  by_cases hi : D.act i
  · rw [TS.hext_act _ i hi]
    simp only [f0, Equiv.apply_symm_apply]
    rw [toAdd_ofAdd, ZMod.val_natCast, ← pow_eq_pow_mod _ hζp]
  · rw [TS.hext_nact _ i hi, D.hfix x hx kx hkx i hi, toAdd_one, ZMod.val_zero, pow_zero]

private theorem torus_card {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {g : K[X]} [Fact (Irreducible g)] {p : ℕ} [NeZero p]
    {X : Subgroup (GL (Fin d) K)} {hζp : AdjoinRoot.root g ^ p = 1}
    {D : FrameData Q g p X} (TS : TorusSetup hζp D) :
    Nat.card (torusT TS) = p ^ Nat.card {i : Fin D.s // D.act i} := by
  let τ : (Fin TS.k → Multiplicative (ZMod p)) →* GL (Fin d) K := TS.torGL.comp TS.ext
  have hτinj : Function.Injective τ := TS.htorGL_inj.comp TS.hext_inj
  let eT : (Fin TS.k → Multiplicative (ZMod p)) ≃ torusT TS := Equiv.ofInjective τ hτinj
  have hcard : Nat.card (torusT TS) = p ^ TS.k := by
    rw [← Nat.card_congr eT, Nat.card_fun, Nat.card_fin,
      Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hkcard : Nat.card {i : Fin D.s // D.act i} = TS.k := by
    rw [← Nat.card_congr TS.eJ, Nat.card_fin]
  rw [hcard, hkcard]

private theorem torus_tor {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {g : K[X]} [Fact (Irreducible g)] {p : ℕ} [NeZero p]
    {X : Subgroup (GL (Fin d) K)} {hζp : AdjoinRoot.root g ^ p = 1}
    {D : FrameData Q g p X} (TS : TorusSetup hζp D) :
    ∀ kk : Fin D.s → ℕ, (∀ i, ¬ D.act i → kk i = 0) →
      ∃ t ∈ torusT TS, ∀ dvec w, glin t (D.Φ (dvec, w)) =
        D.Φ (fun i => AdjoinRoot.root g ^ kk i * dvec i, w) := by
  intro kk hk0
  let f0 : Fin TS.k → Multiplicative (ZMod p) := fun a =>
    ofAdd ((kk (TS.eJ a : Fin D.s) : ℕ) : ZMod p)
  refine ⟨TS.torGL (TS.ext f0), ⟨f0, rfl⟩, fun dvec w => ?_⟩
  change glin (TS.torGL (TS.ext f0)) (D.Φ (dvec, w)) =
    D.Φ (fun i => AdjoinRoot.root g ^ kk i * dvec i, w)
  rw [TS.htorGL, glin_apply, frameGL_mulVec, torEquiv_apply]
  congr 2
  funext i
  congr 1
  by_cases hi : D.act i
  · rw [TS.hext_act _ i hi]
    simp only [f0, Equiv.apply_symm_apply]
    rw [toAdd_ofAdd, ZMod.val_natCast, ← pow_eq_pow_mod (kk i) hζp]
  · rw [TS.hext_nact _ i hi, hk0 i hi, toAdd_one, ZMod.val_zero, pow_zero]

theorem exists_frameTorus {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} (hnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {p : ℕ} (hp : p.Prime) (hpq : p ∣ Nat.card K + 1)
    {g : K[X]} [Fact (Irreducible g)] (hgd : g ∣ cyclotomic p K)
    {X : Subgroup (GL (Fin d) K)} (hX : X ≤ matrixDerived Q)
    (hXc : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a)
    (hXp : ∀ a ∈ X, a ^ p = 1) : Nonempty (FrameTorus Q g p X) := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨D⟩ := exists_frameData hnd hp hpq hgd hX hXc hXp
  letI := D.fintype
  have hp2 : p ≠ 2 := ne_two_of_dvd_card_add_one hpq
  have hpK : (p : K) ≠ 0 := TableBSymp.natCast_ne_zero_of_charTwo hp hp2
  have hζo := NSFrame.root_isPrimitiveRoot (g := g) hp hpK hgd
  have hζp : AdjoinRoot.root g ^ p = 1 := hζo.pow_eq_one
  obtain ⟨TS⟩ := exists_torusSetup hp hpq hgd hζp hζo D
  have hτQ := torus_hτQ TS
  have hτiso := torus_hτiso TS hτQ
  exact ⟨FrameTorus.mk D.s D.κ D.fintype D.Φ D.β D.hβ D.hdec D.act D.hβnd D.hact
    D.hQadd D.hQζ D.hfix (torusT TS) (torus_Tder TS hnd hT hp hpq hτiso)
    (torus_Tcomm TS) (torus_Tpow TS) (torus_XT TS hζo) (torus_card TS) (torus_tor TS)⟩

theorem linearEquiv_frame_block {K : Type} [Field K] {d : ℕ} {L : Type} [Field L]
    [Algebra K L] {s s' : ℕ} {κ κ' : Type}
    (Φ : ((Fin s → L) × (κ → K)) ≃ₗ[K] (Fin d → K))
    (Φ' : ((Fin s' → L) × (κ' → K)) ≃ₗ[K] (Fin d → K))
    (γ : (Fin d → K) ≃ₗ[K] (Fin d → K)) (b : Basis (Fin 2) K L)
    (i : Fin s) (i' : Fin s') (lam : L)
    (h : ∀ j : Fin 2, γ (Φ (Pi.single i (b j), 0)) =
      Φ' (Pi.single i' (lam * b j), 0)) :
    ∀ y : L, γ (Φ (Pi.single i y, 0)) = Φ' (Pi.single i' (lam * y), 0) := by
  intro y
  let f : L →ₗ[K] (Fin d → K) :=
    { toFun := fun z => γ (Φ (Pi.single i z, 0))
      map_add' := by
        intro x z
        rw [Pi.single_add]
        conv_lhs => rw [show (0 : κ → K) = 0 + 0 from (add_zero _).symm]
        rw [← Prod.mk_add_mk, map_add, map_add]
      map_smul' := by
        intro c x
        rw [Pi.single_smul]
        conv_lhs => rw [show (0 : κ → K) = c • (0 : κ → K) from (smul_zero c).symm]
        rw [← Prod.smul_mk, map_smul, map_smul]
        rfl }
  let g : L →ₗ[K] (Fin d → K) :=
    { toFun := fun z => Φ' (Pi.single i' (lam * z), 0)
      map_add' := by
        intro x z
        rw [mul_add, Pi.single_add]
        conv_lhs => rw [show (0 : κ' → K) = 0 + 0 from (add_zero _).symm]
        rw [← Prod.mk_add_mk, map_add]
      map_smul' := by
        intro c x
        rw [show lam * (c • x) = c • (lam * x) from by
            rw [Algebra.smul_def, Algebra.smul_def, mul_left_comm],
          Pi.single_smul]
        conv_lhs => rw [show (0 : κ' → K) = c • (0 : κ' → K) from (smul_zero c).symm]
        rw [← Prod.smul_mk, map_smul]
        rfl }
  have hfg : f = g := b.ext fun j => h j
  exact congrFun (congrArg (fun h : L →ₗ[K] (Fin d → K) =>
    (h : L → (Fin d → K))) hfg) y

private theorem exists_cyclotomic_factor {K : Type} [Field K] {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ Nat.card K + 1) :
    ∃ g : K[X], Irreducible g ∧ g ∣ cyclotomic p K := by
  have hne : ¬ IsUnit (cyclotomic p K) := by
    rw [Polynomial.isUnit_iff_degree_eq_zero, degree_eq_natDegree (cyclotomic_ne_zero p _),
      natDegree_cyclotomic, Nat.totient_prime hp]
    have := hp.two_le
    norm_cast
    omega
  exact WfDvdMonoid.exists_irreducible_factor hne (cyclotomic_ne_zero p _)

private theorem eq_T_of_maxCard {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {g : K[X]} [Fact (Irreducible g)] {p : ℕ}
    {E F : Subgroup (GL (Fin d) K)} {DE : FrameTorus Q g p E} {DF : FrameTorus Q g p F}
    (hEmax : ∀ F' : Subgroup (GL (Fin d) K), F' ≤ matrixDerived Q →
      (∀ a ∈ F', ∀ b ∈ F', a * b = b * a) → (∀ a ∈ F', a ^ p = 1) →
      Nat.card F' ≤ Nat.card E) (hp : p.Prime) :
    E = DE.T ∧ Nat.card {i : Fin DF.s // DF.act i} ≤
      Nat.card {i : Fin DE.s // DE.act i} := by
  have hTE_le : Nat.card DE.T ≤ Nat.card E :=
    hEmax DE.T DE.hTder DE.hTcomm DE.hTpow
  have hE_eq : E = DE.T := Subgroup.eq_of_le_of_card_ge DE.hXT hTE_le
  have hEcard : Nat.card E = p ^ Nat.card {i : Fin DE.s // DE.act i} := by
    conv_lhs => rw [hE_eq]
    exact DE.hTcard
  have hTF_le : Nat.card DF.T ≤ Nat.card E :=
    hEmax DF.T DF.hTder DF.hTcomm DF.hTpow
  refine ⟨hE_eq, (Nat.pow_le_pow_iff_right hp.one_lt).mp ?_⟩
  calc p ^ Nat.card {i : Fin DF.s // DF.act i} = Nat.card DF.T := DF.hTcard.symm
    _ ≤ Nat.card E := hTF_le
    _ = p ^ Nat.card {i : Fin DE.s // DE.act i} := hEcard

private structure ScaleForms {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {g : K[X]} [Fact (Irreducible g)] {p : ℕ}
    {E F : Subgroup (GL (Fin d) K)} (DE : FrameTorus Q g p E) (DF : FrameTorus Q g p F)
    (π : {i : Fin DF.s // DF.act i} ↪ {i : Fin DE.s // DE.act i})
    (b : Basis (Fin 2) K (AdjoinRoot g)) where
  i0 : Fin DF.s
  hi0 : DF.act i0
  c : K
  lam : AdjoinRoot g
  hc_ne : c ≠ 0
  hlamne : lam ≠ 0
  hβscale : ∀ u v, DE.β (lam * u) (lam * v) = DF.β u v

private theorem exists_scaleForms {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {g : K[X]} [Fact (Irreducible g)] {p : ℕ}
    {E F : Subgroup (GL (Fin d) K)} {DE : FrameTorus Q g p E} {DF : FrameTorus Q g p F}
    {π : {i : Fin DF.s // DF.act i} ↪ {i : Fin DE.s // DE.act i}}
    {b : Basis (Fin 2) K (AdjoinRoot g)} (hFne : ∃ i : Fin DF.s, DF.act i)
    (hp : p.Prime) (hpq : p ∣ Nat.card K + 1) (hgd : g ∣ cyclotomic p K) :
    Nonempty (ScaleForms DE DF π b) := by
  obtain ⟨i0, hi0⟩ := hFne
  have hp2 : p ≠ 2 := ne_two_of_dvd_card_add_one hpq
  have hpK : (p : K) ≠ 0 := TableBSymp.natCast_ne_zero_of_charTwo hp hp2
  have hiE0 : DE.act (π ⟨i0, hi0⟩ : {i : Fin DE.s // DE.act i}) := (π ⟨i0, hi0⟩).2
  have hβE_ne : DE.β (b 0) (b 1) ≠ 0 :=
    alt_two_ne_zero b DE.hβ fun u hu => DE.hβnd (π ⟨i0, hi0⟩) hiE0 u hu
  have hβF_ne : DF.β (b 0) (b 1) ≠ 0 :=
    alt_two_ne_zero b DF.hβ fun u hu => DF.hβnd i0 hi0 u hu
  set c : K := DF.β (b 0) (b 1) / DE.β (b 0) (b 1) with hc
  have hc_ne : c ≠ 0 := div_ne_zero hβF_ne hβE_ne
  have hβF_eq : DF.β = c • DE.β := by
    rw [alt_two_eq_smul b DF.hβ DE.hβ hβE_ne, hc]
  have hβF_apply : ∀ u v, DF.β u v = c * DE.β u v := fun u v => by
    rw [hβF_eq]
    simp
  obtain ⟨lam, hlamnorm⟩ := FiniteField.norm_surjective K (AdjoinRoot g) c
  have hlamne : lam ≠ 0 := by
    intro h0
    apply hc_ne
    rw [← hlamnorm, h0]
    simp
  have hβscale : ∀ u v, DE.β (lam * u) (lam * v) = DF.β u v := fun u v => by
    have h1 := bilin_apply_det b DE.hβ (Algebra.lmul K (AdjoinRoot g) lam) u v
    rw [← Algebra.norm_apply, hlamnorm] at h1
    have h1' : DE.β (lam * u) (lam * v) = c * DE.β u v := by
      simpa only [Algebra.coe_lmul_eq_mul, LinearMap.mul_apply'] using h1
    exact h1'.trans (hβF_apply u v).symm
  exact ⟨ScaleForms.mk i0 hi0 c lam hc_ne hlamne hβscale⟩

private theorem scale_block {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {g : K[X]} [Fact (Irreducible g)] {p : ℕ}
    {E F : Subgroup (GL (Fin d) K)} {DE : FrameTorus Q g p E} {DF : FrameTorus Q g p F}
    {π : {i : Fin DF.s // DF.act i} ↪ {i : Fin DE.s // DE.act i}}
    {b : Basis (Fin 2) K (AdjoinRoot g)} (S : ScaleForms DE DF π b)
    (hζ1 : AdjoinRoot.root g ≠ 1) :
    ∀ (a : {i : Fin DF.s // DF.act i}) (u : AdjoinRoot g),
      Q (DE.Φ (Pi.single (π a : {i : Fin DE.s // DE.act i}) (S.lam * u), 0)) =
        Q (DF.Φ (Pi.single (a : Fin DF.s) u, 0)) := by
  intro a u
  have hqE : ∀ x y, Q (DE.Φ (Pi.single (π a : {i : Fin DE.s // DE.act i})
      (S.lam * (x + y)), 0)) =
      Q (DE.Φ (Pi.single (π a : {i : Fin DE.s // DE.act i}) (S.lam * x), 0)) +
      Q (DE.Φ (Pi.single (π a : {i : Fin DE.s // DE.act i}) (S.lam * y), 0)) +
        DF.β x y := by
    intro x y
    rw [mul_add, DE.hQadd]
    congr 1
    exact S.hβscale x y
  have hqF : ∀ x y, Q (DF.Φ (Pi.single (a : Fin DF.s) (x + y), 0)) =
      Q (DF.Φ (Pi.single (a : Fin DF.s) x, 0)) +
      Q (DF.Φ (Pi.single (a : Fin DF.s) y, 0)) + DF.β x y :=
    fun x y => DF.hQadd _ x y
  have hqEζ : ∀ x, Q (DE.Φ (Pi.single (π a : {i : Fin DE.s // DE.act i})
      (S.lam * (AdjoinRoot.root g * x)), 0)) =
      Q (DE.Φ (Pi.single (π a : {i : Fin DE.s // DE.act i}) (S.lam * x), 0)) := by
    intro x
    rw [show S.lam * (AdjoinRoot.root g * x) =
      AdjoinRoot.root g * (S.lam * x) from by ring, DE.hQζ _ (π a).2]
  have hqFζ : ∀ x, Q (DF.Φ (Pi.single (a : Fin DF.s) (AdjoinRoot.root g * x), 0)) =
      Q (DF.Φ (Pi.single (a : Fin DF.s) x, 0)) := fun x => DF.hQζ _ a.2 x
  exact congrFun (eq_of_add_of_mul (ζ := AdjoinRoot.root g)
    (q₁ := fun u => Q (DE.Φ (Pi.single (π a : {i : Fin DE.s // DE.act i})
      (S.lam * u), 0)))
    (q₂ := fun u => Q (DF.Φ (Pi.single (a : Fin DF.s) u, 0)))
    (β := fun u v => DF.β u v) hζ1 hqE hqF hqEζ hqFζ) u

private structure ScaleData {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {g : K[X]} [Fact (Irreducible g)] {p : ℕ}
    {E F : Subgroup (GL (Fin d) K)} (DE : FrameTorus Q g p E) (DF : FrameTorus Q g p F)
    (π : {i : Fin DF.s // DF.act i} ↪ {i : Fin DE.s // DE.act i})
    (b : Basis (Fin 2) K (AdjoinRoot g)) where
  i0 : Fin DF.s
  hi0 : DF.act i0
  c : K
  lam : AdjoinRoot g
  hc_ne : c ≠ 0
  hlamne : lam ≠ 0
  hβscale : ∀ u v, DE.β (lam * u) (lam * v) = DF.β u v
  hblock : ∀ (a : {i : Fin DF.s // DF.act i}) (u : AdjoinRoot g),
    Q (DE.Φ (Pi.single (π a : {i : Fin DE.s // DE.act i}) (lam * u), 0)) =
      Q (DF.Φ (Pi.single (a : Fin DF.s) u, 0))

private theorem exists_scaleData {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {g : K[X]} [Fact (Irreducible g)] {p : ℕ}
    {E F : Subgroup (GL (Fin d) K)} {DE : FrameTorus Q g p E} {DF : FrameTorus Q g p F}
    {π : {i : Fin DF.s // DF.act i} ↪ {i : Fin DE.s // DE.act i}}
    {b : Basis (Fin 2) K (AdjoinRoot g)} (hFne : ∃ i : Fin DF.s, DF.act i)
    (hp : p.Prime) (hpq : p ∣ Nat.card K + 1) (hgd : g ∣ cyclotomic p K)
    (hζ1 : AdjoinRoot.root g ≠ 1) : Nonempty (ScaleData DE DF π b) := by
  obtain ⟨S⟩ := exists_scaleForms (π := π) (b := b) hFne hp hpq hgd
  exact ⟨ScaleData.mk S.i0 S.hi0 S.c S.lam S.hc_ne S.hlamne S.hβscale
    (scale_block S hζ1)⟩

private structure WittInd {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {g : K[X]} [Fact (Irreducible g)] {p : ℕ}
    {E F : Subgroup (GL (Fin d) K)} (DE : FrameTorus Q g p E) (DF : FrameTorus Q g p F) where
  kk : ℕ
  eIdx : Fin kk ≃ (Σ a : {i : Fin DF.s // DF.act i}, Fin 2)

private theorem exists_wittInd {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {g : K[X]} [Fact (Irreducible g)] {p : ℕ}
    {E F : Subgroup (GL (Fin d) K)} (DE : FrameTorus Q g p E) (DF : FrameTorus Q g p F) :
    Nonempty (WittInd DE DF) := by
  haveI : Fintype (Σ a : {i : Fin DF.s // DF.act i}, Fin 2) := Fintype.ofFinite _
  exact ⟨WittInd.mk (Fintype.card (Σ a : {i : Fin DF.s // DF.act i}, Fin 2))
    (Fintype.equivFin _).symm⟩

private theorem witt_li_F {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {g : K[X]} [Fact (Irreducible g)] {p : ℕ}
    {E F : Subgroup (GL (Fin d) K)} {DE : FrameTorus Q g p E} {DF : FrameTorus Q g p F}
    (I : WittInd DE DF) (b : Basis (Fin 2) K (AdjoinRoot g)) :
    LinearIndependent K (fun t : Fin I.kk =>
      DF.Φ (Pi.single ((I.eIdx t).1 : Fin DF.s) (b (I.eIdx t).2), 0)) := by
  classical
  letI := DF.fintype
  haveI : Finite DF.κ := Finite.of_fintype _
  let bsrcF : Basis (((i : Fin DF.s) × Fin 2) ⊕ DF.κ) K
      ((Fin DF.s → AdjoinRoot g) × (DF.κ → K)) :=
    (Pi.basis (fun _ : Fin DF.s => b)).prod (Pi.basisFun K DF.κ)
  let bVF : Basis (((i : Fin DF.s) × Fin 2) ⊕ DF.κ) K (Fin d → K) := bsrcF.map DF.Φ
  have hbVF : ∀ x : ((i : Fin DF.s) × Fin 2),
      bVF (Sum.inl x) = DF.Φ (Pi.single x.1 (b x.2), 0) := by
    intro x
    obtain ⟨i, j⟩ := x
    simp [bVF, bsrcF, Module.Basis.map_apply, Pi.basis_apply, Module.Basis.prod_apply,
      Pi.basisFun_apply]
  let f : (Σ a : {i : Fin DF.s // DF.act i}, Fin 2) →
      ((i : Fin DF.s) × Fin 2) ⊕ DF.κ := fun t => Sum.inl ⟨(t.1 : Fin DF.s), t.2⟩
  have hf : Function.Injective f := by
    intro x y h
    obtain ⟨a, j⟩ := x
    obtain ⟨a', j'⟩ := y
    simp only [f, Sum.inl.injEq, Sigma.mk.injEq] at h
    have hj : j = j' := eq_of_heq h.2
    have ha : a = a' := Subtype.ext h.1
    subst ha hj
    rfl
  have hliF : LinearIndependent K (fun t : (Σ a : {i : Fin DF.s // DF.act i}, Fin 2) =>
      bVF (f t)) :=
    bVF.linearIndependent.comp f hf
  have h1 : LinearIndependent K (fun t : Fin I.kk =>
      bVF (Sum.inl ⟨((I.eIdx t).1 : Fin DF.s), (I.eIdx t).2⟩)) :=
    hliF.comp I.eIdx I.eIdx.injective
  simpa only [hbVF] using h1

private theorem witt_li_E {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {g : K[X]} [Fact (Irreducible g)] {p : ℕ}
    {E F : Subgroup (GL (Fin d) K)} {DE : FrameTorus Q g p E} {DF : FrameTorus Q g p F}
    {π : {i : Fin DF.s // DF.act i} ↪ {i : Fin DE.s // DE.act i}}
    (I : WittInd DE DF) (b : Basis (Fin 2) K (AdjoinRoot g)) (lam : AdjoinRoot g)
    (hlamne : lam ≠ 0) :
    LinearIndependent K (fun t : Fin I.kk =>
      DE.Φ (Pi.single (((π (I.eIdx t).1 : {i : Fin DE.s // DE.act i}) : Fin DE.s))
        (lam * b (I.eIdx t).2), 0)) := by
  classical
  letI := DE.fintype
  haveI : Finite DE.κ := Finite.of_fintype _
  let b' : Basis (Fin 2) K (AdjoinRoot g) := b.map (SpNS.mulEquivL lam hlamne)
  have hb' : ∀ j, b' j = lam * b j := fun j => by simp [b', SpNS.mulEquivL_apply]
  let bsrcE : Basis (((i : Fin DE.s) × Fin 2) ⊕ DE.κ) K
      ((Fin DE.s → AdjoinRoot g) × (DE.κ → K)) :=
    (Pi.basis (fun _ : Fin DE.s => b')).prod (Pi.basisFun K DE.κ)
  let bVE : Basis (((i : Fin DE.s) × Fin 2) ⊕ DE.κ) K (Fin d → K) := bsrcE.map DE.Φ
  have hbVE : ∀ x : ((i : Fin DE.s) × Fin 2),
      bVE (Sum.inl x) = DE.Φ (Pi.single x.1 (b' x.2), 0) := by
    intro x
    obtain ⟨i, j⟩ := x
    simp [bVE, bsrcE, Module.Basis.map_apply, Pi.basis_apply, Module.Basis.prod_apply,
      Pi.basisFun_apply]
  let f : (Σ a : {i : Fin DF.s // DF.act i}, Fin 2) →
      ((i : Fin DE.s) × Fin 2) ⊕ DE.κ := fun t =>
    Sum.inl ⟨((π t.1 : {i : Fin DE.s // DE.act i}) : Fin DE.s), t.2⟩
  have hf : Function.Injective f := by
    intro x y h
    obtain ⟨a, j⟩ := x
    obtain ⟨a', j'⟩ := y
    simp only [f, Sum.inl.injEq, Sigma.mk.injEq] at h
    have hj : j = j' := eq_of_heq h.2
    have ha : a = a' := π.injective (Subtype.ext h.1)
    subst ha hj
    rfl
  have hliE : LinearIndependent K (fun t : (Σ a : {i : Fin DF.s // DF.act i}, Fin 2) =>
      bVE (f t)) :=
    bVE.linearIndependent.comp f hf
  have h1 : LinearIndependent K (fun t : Fin I.kk =>
      bVE (Sum.inl ⟨((π (I.eIdx t).1 : {i : Fin DE.s // DE.act i}) : Fin DE.s),
        (I.eIdx t).2⟩)) :=
    hliE.comp I.eIdx I.eIdx.injective
  simpa only [hbVE, hb'] using h1

private noncomputable def wittU {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {g : K[X]} [Fact (Irreducible g)] {p : ℕ}
    {E F : Subgroup (GL (Fin d) K)} {DE : FrameTorus Q g p E} {DF : FrameTorus Q g p F}
    (I : WittInd DE DF) (b : Basis (Fin 2) K (AdjoinRoot g)) : Fin I.kk → (Fin d → K) :=
  fun t => DF.Φ (Pi.single ((I.eIdx t).1 : Fin DF.s) (b (I.eIdx t).2), 0)

private noncomputable def wittU' {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {g : K[X]} [Fact (Irreducible g)] {p : ℕ}
    {E F : Subgroup (GL (Fin d) K)} {DE : FrameTorus Q g p E} {DF : FrameTorus Q g p F}
    {π : {i : Fin DF.s // DF.act i} ↪ {i : Fin DE.s // DE.act i}}
    (I : WittInd DE DF) (b : Basis (Fin 2) K (AdjoinRoot g)) (lam : AdjoinRoot g) :
    Fin I.kk → (Fin d → K) :=
  fun t => DE.Φ (Pi.single (((π (I.eIdx t).1 : {i : Fin DE.s // DE.act i}) : Fin DE.s))
    (lam * b (I.eIdx t).2), 0)

private structure WittFamPre {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {g : K[X]} [Fact (Irreducible g)] {p : ℕ}
    {E F : Subgroup (GL (Fin d) K)} (DE : FrameTorus Q g p E) (DF : FrameTorus Q g p F)
    (π : {i : Fin DF.s // DF.act i} ↪ {i : Fin DE.s // DE.act i})
    (b : Basis (Fin 2) K (AdjoinRoot g)) (lam : AdjoinRoot g) where
  I : WittInd DE DF
  hli : LinearIndependent K (wittU I b)
  hli' : LinearIndependent K (wittU' (π := π) I b lam)

private theorem exists_wittFamPre {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {g : K[X]} [Fact (Irreducible g)] {p : ℕ}
    {E F : Subgroup (GL (Fin d) K)} {DE : FrameTorus Q g p E} {DF : FrameTorus Q g p F}
    {π : {i : Fin DF.s // DF.act i} ↪ {i : Fin DE.s // DE.act i}}
    (b : Basis (Fin 2) K (AdjoinRoot g)) (lam : AdjoinRoot g) (hlamne : lam ≠ 0) :
    Nonempty (WittFamPre DE DF π b lam) := by
  obtain ⟨I⟩ := exists_wittInd DE DF
  refine ⟨WittFamPre.mk I ?_ ?_⟩
  · change LinearIndependent K (fun t : Fin I.kk =>
      DF.Φ (Pi.single ((I.eIdx t).1 : Fin DF.s) (b (I.eIdx t).2), 0))
    exact witt_li_F I b
  · change LinearIndependent K (fun t : Fin I.kk =>
      DE.Φ (Pi.single (((π (I.eIdx t).1 : {i : Fin DE.s // DE.act i}) : Fin DE.s))
        (lam * b (I.eIdx t).2), 0))
    exact witt_li_E I b lam hlamne

private theorem witt_values {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {g : K[X]} [Fact (Irreducible g)] {p : ℕ}
    {E F : Subgroup (GL (Fin d) K)} {DE : FrameTorus Q g p E} {DF : FrameTorus Q g p F}
    {π : {i : Fin DF.s // DF.act i} ↪ {i : Fin DE.s // DE.act i}}
    {b : Basis (Fin 2) K (AdjoinRoot g)} {S : ScaleData DE DF π b}
    (P : WittFamPre DE DF π b S.lam) :
    (∀ t, Q (wittU' (π := π) P.I b S.lam t) = Q (wittU P.I b t)) ∧
    (∀ t t', QuadraticMap.polar Q (wittU' (π := π) P.I b S.lam t)
        (wittU' (π := π) P.I b S.lam t') =
      QuadraticMap.polar Q (wittU P.I b t) (wittU P.I b t')) := by
  constructor
  · intro t
    simp only [wittU, wittU']
    obtain ⟨a, j⟩ := P.I.eIdx t
    exact S.hblock a (b j)
  · intro t t'
    simp only [wittU, wittU']
    obtain ⟨a, j⟩ := P.I.eIdx t
    obtain ⟨a', j'⟩ := P.I.eIdx t'
    change QuadraticMap.polar Q
        (DE.Φ (Pi.single ((π a : {i : Fin DE.s // DE.act i}) : Fin DE.s)
          (S.lam * b j), 0))
        (DE.Φ (Pi.single ((π a' : {i : Fin DE.s // DE.act i}) : Fin DE.s)
          (S.lam * b j'), 0)) =
      QuadraticMap.polar Q (DF.Φ (Pi.single (a : Fin DF.s) (b j), 0))
        (DF.Φ (Pi.single (a' : Fin DF.s) (b j'), 0))
    rw [OmMv.polar_frame_single (Φ := DE.Φ) (ω := DE.β) DE.hdec (π a) (S.lam * b j)
          (Pi.single (π a') (S.lam * b j')) 0,
      OmMv.polar_frame_single (Φ := DF.Φ) (ω := DF.β) DF.hdec (a : Fin DF.s) (b j)
          (Pi.single (a' : Fin DF.s) (b j')) 0]
    by_cases h : a = a'
    · subst h
      simpa using S.hβscale (b j) (b j')
    · have ha : (a : Fin DF.s) ≠ (a' : Fin DF.s) := fun hh => h (Subtype.ext hh)
      have hπ' : ((π a : {i : Fin DE.s // DE.act i}) : Fin DE.s) ≠
          ((π a' : {i : Fin DE.s // DE.act i}) : Fin DE.s) :=
        fun hh => h (π.injective (Subtype.ext hh))
      simp [Pi.single_eq_of_ne ha, Pi.single_eq_of_ne hπ']

private structure WittFam {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {g : K[X]} [Fact (Irreducible g)] {p : ℕ}
    {E F : Subgroup (GL (Fin d) K)} (DE : FrameTorus Q g p E) (DF : FrameTorus Q g p F)
    (π : {i : Fin DF.s // DF.act i} ↪ {i : Fin DE.s // DE.act i})
    (b : Basis (Fin 2) K (AdjoinRoot g)) (S : ScaleData DE DF π b) where
  P : WittFamPre DE DF π b S.lam
  hQval : ∀ t, Q (wittU' (π := π) P.I b S.lam t) = Q (wittU P.I b t)
  hpol : ∀ t t', QuadraticMap.polar Q (wittU' (π := π) P.I b S.lam t)
      (wittU' (π := π) P.I b S.lam t') =
    QuadraticMap.polar Q (wittU P.I b t) (wittU P.I b t')

private theorem exists_wittFam {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {g : K[X]} [Fact (Irreducible g)] {p : ℕ}
    {E F : Subgroup (GL (Fin d) K)} {DE : FrameTorus Q g p E} {DF : FrameTorus Q g p F}
    {π : {i : Fin DF.s // DF.act i} ↪ {i : Fin DE.s // DE.act i}}
    {b : Basis (Fin 2) K (AdjoinRoot g)} (S : ScaleData DE DF π b) :
    Nonempty (WittFam DE DF π b S) := by
  obtain ⟨P⟩ := exists_wittFamPre (π := π) b S.lam S.hlamne
  obtain ⟨hQval, hpol⟩ := witt_values P
  exact ⟨WittFam.mk P hQval hpol⟩

private structure WittData {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {g : K[X]} [Fact (Irreducible g)] {p : ℕ}
    {E F : Subgroup (GL (Fin d) K)} (DE : FrameTorus Q g p E) (DF : FrameTorus Q g p F)
    (π : {i : Fin DF.s // DF.act i} ↪ {i : Fin DE.s // DE.act i})
    (b : Basis (Fin 2) K (AdjoinRoot g)) (S : ScaleData DE DF π b) where
  W : WittFam DE DF π b S
  γ : (Fin d → K) ≃ₗ[K] (Fin d → K)
  hγ : γ ∈ TauCeti.QuadraticMap.orthogonalGroup Q
  hγu : ∀ t, γ (wittU W.P.I b t) = wittU' (π := π) W.P.I b S.lam t
  γm : GL (Fin d) K
  hγm : γm ∈ matrixIsometries Q
  hγm_apply : matrixLinearIso γm = γ
  hγ_block : ∀ (a : {i : Fin DF.s // DF.act i}) (j : Fin 2),
    γ (DF.Φ (Pi.single (a : Fin DF.s) (b j), 0)) =
      DE.Φ (Pi.single (π a : {i : Fin DE.s // DE.act i}) (S.lam * b j), 0)

private theorem exists_wittData {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {g : K[X]} [Fact (Irreducible g)] {p : ℕ}
    {E F : Subgroup (GL (Fin d) K)} {DE : FrameTorus Q g p E} {DF : FrameTorus Q g p F}
    {π : {i : Fin DF.s // DF.act i} ↪ {i : Fin DE.s // DE.act i}}
    {b : Basis (Fin 2) K (AdjoinRoot g)} (S : ScaleData DE DF π b)
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate) :
    Nonempty (WittData DE DF π b S) := by
  obtain ⟨W⟩ := exists_wittFam S
  obtain ⟨γ, hγ, hγu⟩ := CFSG.RankThree.OrthogonalInvolutions.exists_mem_orthogonalGroup_apply_eq
    hnd (wittU W.P.I b) (wittU' (π := π) W.P.I b S.lam)
    W.P.hli W.P.hli' W.hQval W.hpol
  let γm : GL (Fin d) K := (matrixLinearIso).symm γ
  have hγm_apply : matrixLinearIso γm = γ := MulEquiv.apply_symm_apply _ _
  have hγm : γm ∈ matrixIsometries Q := by
    change matrixLinearIso γm ∈ TauCeti.QuadraticMap.orthogonalGroup Q
    rw [hγm_apply]
    exact hγ
  have hγ_block : ∀ (a : {i : Fin DF.s // DF.act i}) (j : Fin 2),
      γ (DF.Φ (Pi.single (a : Fin DF.s) (b j), 0)) =
        DE.Φ (Pi.single (π a : {i : Fin DE.s // DE.act i}) (S.lam * b j), 0) := by
    intro a j
    have h := hγu (W.P.I.eIdx.symm ⟨a, j⟩)
    simpa only [wittU, wittU', Equiv.apply_symm_apply] using h
  exact ⟨WittData.mk W γ hγ hγu γm hγm hγm_apply hγ_block⟩

private structure KEImage {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {g : K[X]} [Fact (Irreducible g)] {p : ℕ}
    {E F : Subgroup (GL (Fin d) K)} (DE : FrameTorus Q g p E) (DF : FrameTorus Q g p F)
    (π : {i : Fin DF.s // DF.act i} ↪ {i : Fin DE.s // DE.act i})
    (kx : Fin DF.s → ℕ) where
  kE : Fin DE.s → ℕ
  hkE0 : ∀ i, ¬ DE.act i → kE i = 0
  hkE_nimage : ∀ i, (¬ ∃ a : {i : Fin DF.s // DF.act i}, (π a : Fin DE.s) = i) → kE i = 0
  hkE_image : ∀ a : {i : Fin DF.s // DF.act i},
    kE ((π a : {i : Fin DE.s // DE.act i}) : Fin DE.s) = kx (a : Fin DF.s)

private theorem exists_kE {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {g : K[X]} [Fact (Irreducible g)] {p : ℕ}
    {E F : Subgroup (GL (Fin d) K)} {DE : FrameTorus Q g p E} {DF : FrameTorus Q g p F}
    {π : {i : Fin DF.s // DF.act i} ↪ {i : Fin DE.s // DE.act i}}
    {kx : Fin DF.s → ℕ} : Nonempty (KEImage DE DF π kx) := by
  classical
  let kE : Fin DE.s → ℕ := fun i =>
    if h : ∃ a : {i : Fin DF.s // DF.act i}, (π a : Fin DE.s) = i then
      kx ((Classical.choose h : {i : Fin DF.s // DF.act i}) : Fin DF.s) else 0
  have hkE0 : ∀ i, ¬ DE.act i → kE i = 0 := by
    intro i hi
    simp only [kE]
    rw [dif_neg]
    rintro ⟨a, ha⟩
    exact hi (ha ▸ (π a).2)
  have hkE_nimage : ∀ i, (¬ ∃ a : {i : Fin DF.s // DF.act i},
      (π a : Fin DE.s) = i) → kE i = 0 := by
    intro i hi
    simp only [kE]
    rw [dif_neg hi]
  have hkE_image : ∀ a : {i : Fin DF.s // DF.act i},
      kE ((π a : {i : Fin DE.s // DE.act i}) : Fin DE.s) = kx (a : Fin DF.s) := by
    intro a
    have hwit : (π (Classical.choose (⟨a, rfl⟩ : ∃ b : {i : Fin DF.s // DF.act i},
        (π b : Fin DE.s) = (π a : Fin DE.s))) : {i : Fin DE.s // DE.act i}) = π a :=
      Subtype.ext (Classical.choose_spec (⟨a, rfl⟩ : ∃ b : {i : Fin DF.s // DF.act i},
        (π b : Fin DE.s) = (π a : Fin DE.s)))
    have hchoose : Classical.choose (⟨a, rfl⟩ : ∃ b : {i : Fin DF.s // DF.act i},
        (π b : Fin DE.s) = (π a : Fin DE.s)) = a := π.injective hwit
    simp only [kE]
    rw [dif_pos ⟨a, rfl⟩, hchoose]
  exact ⟨KEImage.mk kE hkE0 hkE_nimage hkE_image⟩

private structure KEData {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {g : K[X]} [Fact (Irreducible g)] {p : ℕ}
    {E F : Subgroup (GL (Fin d) K)} (DE : FrameTorus Q g p E) (DF : FrameTorus Q g p F)
    (π : {i : Fin DF.s // DF.act i} ↪ {i : Fin DE.s // DE.act i})
    (kx : Fin DF.s → ℕ) (hE_eq : E = DE.T) where
  kE : Fin DE.s → ℕ
  hkE0 : ∀ i, ¬ DE.act i → kE i = 0
  hkE_nimage : ∀ i, (¬ ∃ a : {i : Fin DF.s // DF.act i}, (π a : Fin DE.s) = i) → kE i = 0
  hkE_image : ∀ a : {i : Fin DF.s // DF.act i},
    kE ((π a : {i : Fin DE.s // DE.act i}) : Fin DE.s) = kx (a : Fin DF.s)
  t : GL (Fin d) K
  htT : t ∈ DE.T
  htE : t ∈ E
  ht_single : ∀ (i : Fin DE.s) (u : AdjoinRoot g),
    glin t (DE.Φ (Pi.single i u, 0)) =
      DE.Φ (Pi.single i (AdjoinRoot.root g ^ kE i * u), 0)
  ht_kappa : ∀ w : DE.κ → K, glin t (DE.Φ (0, w)) = DE.Φ (0, w)

private theorem exists_KEData {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {g : K[X]} [Fact (Irreducible g)] {p : ℕ}
    {E F : Subgroup (GL (Fin d) K)} {DE : FrameTorus Q g p E} {DF : FrameTorus Q g p F}
    {π : {i : Fin DF.s // DF.act i} ↪ {i : Fin DE.s // DE.act i}}
    {kx : Fin DF.s → ℕ} (hE_eq : E = DE.T) : Nonempty (KEData DE DF π kx hE_eq) := by
  obtain ⟨KE⟩ := exists_kE (DE := DE) (DF := DF) (π := π) (kx := kx)
  obtain ⟨t, htT, htact⟩ := DE.hTtor KE.kE KE.hkE0
  have htE : t ∈ E := by
    rw [hE_eq]
    exact htT
  have ht_single : ∀ (i : Fin DE.s) (u : AdjoinRoot g),
      glin t (DE.Φ (Pi.single i u, 0)) =
        DE.Φ (Pi.single i (AdjoinRoot.root g ^ KE.kE i * u), 0) := by
    intro i u
    have h := htact (Pi.single i u) 0
    have hfun : (fun j => AdjoinRoot.root g ^ KE.kE j *
        (Pi.single i u : Fin DE.s → AdjoinRoot g) j) =
        Pi.single i (AdjoinRoot.root g ^ KE.kE i * u) := by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Pi.single_eq_of_ne hj]
    rw [h, hfun]
  have ht_kappa : ∀ w : DE.κ → K, glin t (DE.Φ (0, w)) = DE.Φ (0, w) := by
    intro w
    have h := htact (0 : Fin DE.s → AdjoinRoot g) w
    rw [h]
    congr 2
    funext i
    simp
  exact ⟨KEData.mk KE.kE KE.hkE0 KE.hkE_nimage KE.hkE_image t htT htE ht_single ht_kappa⟩

private theorem hx_fix {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {g : K[X]} [Fact (Irreducible g)] {p : ℕ}
    {F : Subgroup (GL (Fin d) K)} {DF : FrameTorus Q g p F} {x : GL (Fin d) K}
    {kx : Fin DF.s → ℕ} (hx : x ∈ F)
    (hkx : ∀ d w, glin x (DF.Φ (d, w)) =
      DF.Φ (fun i => AdjoinRoot.root g ^ kx i * d i, w)) :
    ∀ v : Fin d → K, (∀ a : {i : Fin DF.s // DF.act i}, ∀ u' : AdjoinRoot g,
      QuadraticMap.polarBilin Q v (DF.Φ (Pi.single (a : Fin DF.s) u', 0)) = 0) →
      glin x v = v := by
  intro v hv
  obtain ⟨⟨d, w⟩, rfl⟩ := DF.Φ.surjective v
  have hd : ∀ a : {i : Fin DF.s // DF.act i}, d (a : Fin DF.s) = 0 := by
    intro a
    apply DF.hβnd (a : Fin DF.s) a.2 (d (a : Fin DF.s))
    intro u'
    have h := hv a u'
    rw [DF.hdec, Finset.sum_eq_single (a : Fin DF.s)] at h
    · have hz : (QuadraticMap.polarBilin Q (DF.Φ ((0 : Fin DF.s → AdjoinRoot g), w)))
          (DF.Φ ((0 : Fin DF.s → AdjoinRoot g), (0 : DF.κ → K))) = 0 := by
        have h0 : DF.Φ ((0 : Fin DF.s → AdjoinRoot g), (0 : DF.κ → K)) = 0 :=
          map_zero DF.Φ
        rw [h0]
        exact map_zero _
      rw [Pi.single_eq_same, hz, add_zero] at h
      exact h
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  rw [hkx]
  congr 2
  funext i
  by_cases hi : DF.act i
  · rw [hd ⟨i, hi⟩, mul_zero]
  · rw [DF.hfix x hx kx hkx i hi, one_mul]

private theorem hx_active {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {g : K[X]} [Fact (Irreducible g)] {p : ℕ}
    {F : Subgroup (GL (Fin d) K)} {DF : FrameTorus Q g p F} {x : GL (Fin d) K}
    {kx : Fin DF.s → ℕ}
    (hkx : ∀ d w, glin x (DF.Φ (d, w)) =
      DF.Φ (fun i => AdjoinRoot.root g ^ kx i * d i, w)) :
    ∀ (a : {i : Fin DF.s // DF.act i}) (u : AdjoinRoot g),
      glin x (DF.Φ (Pi.single (a : Fin DF.s) u, 0)) =
        DF.Φ (Pi.single (a : Fin DF.s) (AdjoinRoot.root g ^ kx (a : Fin DF.s) * u), 0) := by
  intro a u
  rw [hkx]
  congr 2
  funext j
  by_cases hj : j = (a : Fin DF.s)
  · subst hj
    rw [Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hj, mul_zero, Pi.single_eq_of_ne hj]

private theorem hsingle_image {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {g : K[X]} [Fact (Irreducible g)] {p : ℕ}
    {E F : Subgroup (GL (Fin d) K)} {DE : FrameTorus Q g p E} {DF : FrameTorus Q g p F}
    {π : {i : Fin DF.s // DF.act i} ↪ {i : Fin DE.s // DE.act i}}
    {b : Basis (Fin 2) K (AdjoinRoot g)} {S : ScaleData DE DF π b}
    (W : WittData DE DF π b S) {kx : Fin DF.s → ℕ} {hE_eq : E = DE.T}
    (KD : KEData DE DF π kx hE_eq) {x : GL (Fin d) K}
    (hkx : ∀ d w, glin x (DF.Φ (d, w)) =
      DF.Φ (fun i => AdjoinRoot.root g ^ kx i * d i, w))
    {i : Fin DE.s} {u : AdjoinRoot g}
    (hi : ∃ a : {i : Fin DF.s // DF.act i}, (π a : Fin DE.s) = i) :
    W.γ (glin x (W.γ.symm (DE.Φ (Pi.single i u, 0)))) =
      glin KD.t (DE.Φ (Pi.single i u, 0)) := by
  obtain ⟨a, ha⟩ := hi
  rw [← ha]
  have hγL : ∀ y : AdjoinRoot g,
      W.γ (DF.Φ (Pi.single (a : Fin DF.s) y, 0)) =
        DE.Φ (Pi.single (π a : {i : Fin DE.s // DE.act i}) (S.lam * y), 0) :=
    linearEquiv_frame_block DF.Φ DE.Φ W.γ b (a : Fin DF.s)
      (π a : Fin DE.s) S.lam (fun j => W.hγ_block a j)
  have hγinv : W.γ.symm (DE.Φ (Pi.single
      (π a : {i : Fin DE.s // DE.act i}) u, 0)) =
      DF.Φ (Pi.single (a : Fin DF.s) (S.lam⁻¹ * u), 0) := by
    have h1 : W.γ (DF.Φ (Pi.single (a : Fin DF.s) (S.lam⁻¹ * u), 0)) =
        DE.Φ (Pi.single (π a : {i : Fin DE.s // DE.act i}) u, 0) := by
      rw [hγL (S.lam⁻¹ * u)]
      congr 2
      rw [← mul_assoc, mul_inv_cancel₀ S.hlamne, one_mul]
    rw [← h1, LinearEquiv.symm_apply_apply]
  rw [hγinv, hx_active hkx a (S.lam⁻¹ * u)]
  rw [hγL (AdjoinRoot.root g ^ kx (a : Fin DF.s) * (S.lam⁻¹ * u))]
  rw [KD.ht_single, KD.hkE_image a]
  congr 2
  field_simp [S.hlamne]

private theorem hsingle_nonimage {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {g : K[X]} [Fact (Irreducible g)] {p : ℕ}
    {E F : Subgroup (GL (Fin d) K)} {DE : FrameTorus Q g p E} {DF : FrameTorus Q g p F}
    {π : {i : Fin DF.s // DF.act i} ↪ {i : Fin DE.s // DE.act i}}
    {b : Basis (Fin 2) K (AdjoinRoot g)} {S : ScaleData DE DF π b}
    (W : WittData DE DF π b S) {kx : Fin DF.s → ℕ} {hE_eq : E = DE.T}
    (KD : KEData DE DF π kx hE_eq) {x : GL (Fin d) K} (hx : x ∈ F)
    (hkx : ∀ d w, glin x (DF.Φ (d, w)) =
      DF.Φ (fun i => AdjoinRoot.root g ^ kx i * d i, w))
    {i : Fin DE.s} {u : AdjoinRoot g}
    (hi : ¬ ∃ a : {i : Fin DF.s // DF.act i}, (π a : Fin DE.s) = i) :
    W.γ (glin x (W.γ.symm (DE.Φ (Pi.single i u, 0)))) =
      glin KD.t (DE.Φ (Pi.single i u, 0)) := by
  have horth : ∀ a : {i : Fin DF.s // DF.act i}, ∀ u' : AdjoinRoot g,
      QuadraticMap.polarBilin Q (W.γ.symm (DE.Φ (Pi.single i u, 0)))
        (DF.Φ (Pi.single (a : Fin DF.s) u', 0)) = 0 := by
    intro a u'
    have hiso := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup W.hγ
      (W.γ.symm (DE.Φ (Pi.single i u, 0))) (DF.Φ (Pi.single (a : Fin DF.s) u', 0))
    rw [LinearEquiv.apply_symm_apply] at hiso
    have hγLa : ∀ y : AdjoinRoot g,
        W.γ (DF.Φ (Pi.single (a : Fin DF.s) y, 0)) =
          DE.Φ (Pi.single (π a : {i : Fin DE.s // DE.act i}) (S.lam * y), 0) :=
      linearEquiv_frame_block DF.Φ DE.Φ W.γ b (a : Fin DF.s)
        (π a : Fin DE.s) S.lam (fun j => W.hγ_block a j)
    change QuadraticMap.polar Q (W.γ.symm (DE.Φ (Pi.single i u, 0)))
      (DF.Φ (Pi.single (a : Fin DF.s) u', 0)) = 0
    rw [← hiso, hγLa u']
    change QuadraticMap.polar Q (DE.Φ (Pi.single i u, 0))
      (DE.Φ (Pi.single (π a) (S.lam * u'), 0)) = 0
    rw [OmMv.polar_frame_single (Φ := DE.Φ) (ω := DE.β) DE.hdec i u
      (Pi.single (π a) (S.lam * u')) 0]
    rw [Pi.single_eq_of_ne (fun h => hi ⟨a, h.symm⟩)]
    exact map_zero _
  have hfixi := hx_fix (DF := DF) hx hkx (W.γ.symm (DE.Φ (Pi.single i u, 0))) horth
  rw [hfixi, LinearEquiv.apply_symm_apply, KD.ht_single]
  rw [show KD.kE i = 0 from KD.hkE_nimage i hi]
  simp

private theorem hsingle_block {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {g : K[X]} [Fact (Irreducible g)] {p : ℕ}
    {E F : Subgroup (GL (Fin d) K)} {DE : FrameTorus Q g p E} {DF : FrameTorus Q g p F}
    {π : {i : Fin DF.s // DF.act i} ↪ {i : Fin DE.s // DE.act i}}
    {b : Basis (Fin 2) K (AdjoinRoot g)} {S : ScaleData DE DF π b}
    (W : WittData DE DF π b S) {kx : Fin DF.s → ℕ} {hE_eq : E = DE.T}
    (KD : KEData DE DF π kx hE_eq) {x : GL (Fin d) K} (hx : x ∈ F)
    (hkx : ∀ d w, glin x (DF.Φ (d, w)) =
      DF.Φ (fun i => AdjoinRoot.root g ^ kx i * d i, w)) :
    ∀ (i : Fin DE.s) (u : AdjoinRoot g),
      W.γ (glin x (W.γ.symm (DE.Φ (Pi.single i u, 0)))) =
        glin KD.t (DE.Φ (Pi.single i u, 0)) := by
  intro i u
  by_cases hi : ∃ a : {i : Fin DF.s // DF.act i}, (π a : Fin DE.s) = i
  · exact hsingle_image W KD hkx hi
  · exact hsingle_nonimage W KD hx hkx hi

private theorem hkappa_block {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {g : K[X]} [Fact (Irreducible g)] {p : ℕ}
    {E F : Subgroup (GL (Fin d) K)} {DE : FrameTorus Q g p E} {DF : FrameTorus Q g p F}
    {π : {i : Fin DF.s // DF.act i} ↪ {i : Fin DE.s // DE.act i}}
    {b : Basis (Fin 2) K (AdjoinRoot g)} {S : ScaleData DE DF π b}
    (W : WittData DE DF π b S) {kx : Fin DF.s → ℕ} {hE_eq : E = DE.T}
    (KD : KEData DE DF π kx hE_eq) {x : GL (Fin d) K} (hx : x ∈ F)
    (hkx : ∀ d w, glin x (DF.Φ (d, w)) =
      DF.Φ (fun i => AdjoinRoot.root g ^ kx i * d i, w)) :
    ∀ w : DE.κ → K,
      W.γ (glin x (W.γ.symm (DE.Φ (0, w)))) = glin KD.t (DE.Φ (0, w)) := by
  intro w
  have horth : ∀ a : {i : Fin DF.s // DF.act i}, ∀ u' : AdjoinRoot g,
      QuadraticMap.polarBilin Q (W.γ.symm (DE.Φ (0, w)))
        (DF.Φ (Pi.single (a : Fin DF.s) u', 0)) = 0 := by
    intro a u'
    have hiso := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup W.hγ
      (W.γ.symm (DE.Φ (0, w))) (DF.Φ (Pi.single (a : Fin DF.s) u', 0))
    rw [LinearEquiv.apply_symm_apply] at hiso
    have hγLa : ∀ y : AdjoinRoot g,
        W.γ (DF.Φ (Pi.single (a : Fin DF.s) y, 0)) =
          DE.Φ (Pi.single (π a : {i : Fin DE.s // DE.act i}) (S.lam * y), 0) :=
      linearEquiv_frame_block DF.Φ DE.Φ W.γ b (a : Fin DF.s)
        (π a : Fin DE.s) S.lam (fun j => W.hγ_block a j)
    change QuadraticMap.polar Q (W.γ.symm (DE.Φ (0, w)))
      (DF.Φ (Pi.single (a : Fin DF.s) u', 0)) = 0
    rw [← hiso, hγLa u']
    change QuadraticMap.polarBilin Q (DE.Φ (0, w))
      (DE.Φ (Pi.single (π a) (S.lam * u'), 0)) = 0
    rw [DE.hdec]
    have hsum : (∑ k : Fin DE.s, DE.β ((0 : Fin DE.s → AdjoinRoot g) k)
        ((Pi.single (π a) (S.lam * u') : Fin DE.s → AdjoinRoot g) k)) = 0 := by
      simp
    rw [hsum, zero_add]
    have h0 : DE.Φ ((0 : Fin DE.s → AdjoinRoot g), (0 : DE.κ → K)) = 0 :=
      map_zero DE.Φ
    rw [h0]
    exact map_zero _
  have hfixk := hx_fix (DF := DF) hx hkx (W.γ.symm (DE.Φ (0, w))) horth
  rw [hfixk, LinearEquiv.apply_symm_apply, KD.ht_kappa]

private theorem conj_eq {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {g : K[X]} [Fact (Irreducible g)] {p : ℕ}
    {E F : Subgroup (GL (Fin d) K)} {DE : FrameTorus Q g p E} {DF : FrameTorus Q g p F}
    {π : {i : Fin DF.s // DF.act i} ↪ {i : Fin DE.s // DE.act i}}
    {b : Basis (Fin 2) K (AdjoinRoot g)} {S : ScaleData DE DF π b}
    (W : WittData DE DF π b S) {kx : Fin DF.s → ℕ} {hE_eq : E = DE.T}
    (KD : KEData DE DF π kx hE_eq) {x : GL (Fin d) K} (hx : x ∈ F)
    (hkx : ∀ d w, glin x (DF.Φ (d, w)) =
      DF.Φ (fun i => AdjoinRoot.root g ^ kx i * d i, w)) :
    W.γm * x * W.γm⁻¹ = KD.t := by
  let M : GL (Fin d) K ≃* ((Fin d → K) ≃ₗ[K] (Fin d → K)) := matrixLinearIso
  have hMγm : M W.γm = W.γ := W.hγm_apply
  have hconj : M (W.γm * x * W.γm⁻¹) = M W.γm * M x * (M W.γm)⁻¹ := by
    rw [map_mul, map_mul, map_inv]
  have hsingle := hsingle_block W KD hx hkx
  have hkappa := hkappa_block W KD hx hkx
  apply M.injective
  rw [hconj, hMγm]
  apply LinearEquiv.ext
  intro v
  change W.γ (glin x (W.γ.symm v)) = glin KD.t v
  obtain ⟨⟨d, w⟩, rfl⟩ := DE.Φ.surjective v
  have hdecomp : DE.Φ (d, w) = ∑ i, DE.Φ (Pi.single i (d i), 0) + DE.Φ (0, w) := by
    have hpair : (d, w) = ∑ i, (Pi.single i (d i), (0 : DE.κ → K)) +
        ((0 : Fin DE.s → AdjoinRoot g), w) := by
      refine Prod.ext ?_ ?_
      · funext j
        simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
      · simp [Prod.snd_sum]
    rw [hpair, map_add, map_sum]
  calc W.γ (glin x (W.γ.symm (DE.Φ (d, w))))
      = ∑ i, W.γ (glin x (W.γ.symm (DE.Φ (Pi.single i (d i), 0)))) +
          W.γ (glin x (W.γ.symm (DE.Φ (0, w)))) := by
        rw [hdecomp]
        simp only [map_add, map_sum]
    _ = ∑ i, glin KD.t (DE.Φ (Pi.single i (d i), 0)) + glin KD.t (DE.Φ (0, w)) := by
        congr 1
        · apply Finset.sum_congr rfl
          intro i _
          exact hsingle i (d i)
        · exact hkappa w
    _ = glin KD.t (DE.Φ (d, w)) := by
        rw [hdecomp]
        simp only [map_add, map_sum]

private theorem conj_positive {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {g : K[X]} [Fact (Irreducible g)] {p : ℕ}
    {E F : Subgroup (GL (Fin d) K)} (DE : FrameTorus Q g p E) (DF : FrameTorus Q g p F)
    (hE_eq : E = DE.T) (hFne : ∃ i : Fin DF.s, DF.act i)
    (π : {i : Fin DF.s // DF.act i} ↪ {i : Fin DE.s // DE.act i})
    (b : Basis (Fin 2) K (AdjoinRoot g))
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hp : p.Prime) (hpq : p ∣ Nat.card K + 1) (hgd : g ∣ cyclotomic p K)
    (hζ1 : AdjoinRoot.root g ≠ 1) :
    ∃ γm ∈ matrixIsometries Q, ∀ x ∈ F, γm * x * γm⁻¹ ∈ E := by
  obtain ⟨S⟩ := exists_scaleData (π := π) (b := b) hFne hp hpq hgd hζ1
  obtain ⟨W⟩ := exists_wittData S hnd
  refine ⟨W.γm, W.hγm, ?_⟩
  intro x hx
  obtain ⟨kx, hkx⟩ := DF.hact x hx
  obtain ⟨KD⟩ := exists_KEData (π := π) (kx := kx) hE_eq
  rw [conj_eq W KD hx hkx]
  exact KD.htE

private theorem conj_inactive {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {g : K[X]} [Fact (Irreducible g)] {p : ℕ}
    {E F : Subgroup (GL (Fin d) K)} (DF : FrameTorus Q g p F)
    (hFne : ¬ ∃ i : Fin DF.s, DF.act i) :
    ∃ γm ∈ matrixIsometries Q, ∀ x ∈ F, γm * x * γm⁻¹ ∈ E := by
  have hFbot : F = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨kx, hkx⟩ := DF.hact x hx
    have hk1 : ∀ i, AdjoinRoot.root g ^ kx i = 1 := fun i =>
      DF.hfix x hx kx hkx i fun hi => hFne ⟨i, hi⟩
    apply eq_of_glin
    intro v
    obtain ⟨⟨d, w⟩, rfl⟩ := DF.Φ.surjective v
    rw [hkx, glin_one, Module.End.one_apply]
    congr 2
    funext i
    rw [hk1 i, one_mul]
  refine ⟨1, one_mem _, fun x hx => ?_⟩
  rw [(Subgroup.eq_bot_iff_forall F).mp hFbot x hx]
  simp

theorem exists_conj_le_of_maxCard {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} (hnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {p : ℕ} (hp : p.Prime) (hpq : p ∣ Nat.card K + 1)
    {E F : Subgroup (GL (Fin d) K)} (hE : E ≤ matrixDerived Q)
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hEp : ∀ a ∈ E, a ^ p = 1)
    (hEmax : ∀ F' : Subgroup (GL (Fin d) K), F' ≤ matrixDerived Q →
      (∀ a ∈ F', ∀ b ∈ F', a * b = b * a) → (∀ a ∈ F', a ^ p = 1) →
      Nat.card F' ≤ Nat.card E)
    (hF : F ≤ matrixDerived Q) (hFc : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a)
    (hFp : ∀ a ∈ F, a ^ p = 1) :
    ∃ g ∈ matrixIsometries Q, ∀ x ∈ F, g * x * g⁻¹ ∈ E := by
  classical
  have hp2 : p ≠ 2 := SpNS.ne_two_of_dvd_card_add_one hpq
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Fintype K := Fintype.ofFinite K
  have hpK : (p : K) ≠ 0 := TableBSymp.natCast_ne_zero_of_charTwo hp hp2
  obtain ⟨g, hg, hgd⟩ := exists_cyclotomic_factor hp hpq
  haveI : Fact (Irreducible g) := ⟨hg⟩
  have : Module.Finite K (AdjoinRoot g) := (CoordSL.rootPB g).finite
  have : Finite (AdjoinRoot g) := Module.finite_of_finite K
  have hζo := NSFrame.root_isPrimitiveRoot (g := g) hp hpK hgd
  have hζ1 : AdjoinRoot.root g ≠ 1 := hζo.ne_one hp.one_lt
  obtain ⟨DE⟩ := exists_frameTorus (Q := Q) hnd hT hp hpq hgd hE hEc hEp
  obtain ⟨DF⟩ := exists_frameTorus (Q := Q) hnd hT hp hpq hgd hF hFc hFp
  letI := DE.fintype
  letI := DF.fintype
  obtain ⟨hE_eq, ha_le⟩ := eq_T_of_maxCard (DE := DE) (DF := DF) hEmax hp
  haveI : Fintype {i : Fin DF.s // DF.act i} := Fintype.ofFinite _
  haveI : Fintype {i : Fin DE.s // DE.act i} := Fintype.ofFinite _
  obtain ⟨π⟩ := Function.Embedding.nonempty_of_card_le (by
    simpa [Nat.card_eq_fintype_card] using ha_le)
  let b : Basis (Fin 2) K (AdjoinRoot g) :=
    (CoordSL.rootPB g).basis.reindex (finCongr
      (rootPB_dim_eq_two hp hp2 hpK hgd hpq))
  by_cases hFne : ∃ i : Fin DF.s, DF.act i
  · exact conj_positive DE DF hE_eq hFne π b hnd hp hpq hgd hζ1
  · exact conj_inactive (E := E) DF hFne

end OrthNs

end CFSG.StandardType

end
