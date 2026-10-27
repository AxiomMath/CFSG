module

public import CFSG.LocalAnalysis.StandardType.GGTypeADefs
public import CFSG.LocalAnalysis.StandardType.GGTPNThmRACore
public import CFSG.LocalAnalysis.StandardType.GGTPNThmRAC1
public import CFSG.LocalAnalysis.StandardType.GGTPNThmRADescent
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGNbrLangTorARankBound
public import CFSG.LocalAnalysis.StandardType.GGBlockScalar

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Polynomial Matrix CFSG.RankThree.PartOne.KCPrimary
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

@[expose] def GGRARankTwo : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (X : Type) [Group X] [Finite X]
    (A : Subgroup (MulAut X)) (σ : MulAut X) (J : Subgroup X) (labX : LargeEvenLabel),
    GGTPNLocalCore p A σ J → GGTPNOnlyComp p σ J → GGTPNKernel A σ J →
    GGTPNSelfCent p A → GGKacRA labX p → labX.tag = .A →
    GGTPNMarked p (fun _ lab => lab = labX) A →
    ∀ (a : ℕ) (ds : List ℕ), labX.rank + 1 = a + ds.sum → ds ≠ [] → ds.length < p →
      (∀ x ∈ ds, x = 1 ∨ (labX.tag = .twA ∧ labX.n = 1 ∧ (x = 2 ∨ x = 3))) →
      ((LargeEvenInLambda2 ⟨labX.tag, a - 1, labX.n⟩ ∧
          GGHasLabel ⟨labX.tag, a - 1, labX.n⟩ (↥J ⧸ Subgroup.center ↥J)) ∨
        (labX.tag = .twA ∧ a = 2 ∧ LargeEvenInLambda2 ⟨.A, 1, labX.n⟩ ∧
          GGHasLabel ⟨.A, 1, labX.n⟩ (↥J ⧸ Subgroup.center ↥J))) →
      ds.length ≤ 2

@[expose] def GGRAPrimaryCount : Prop :=
  ∀ (p N : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (K : Type) [Field K] [Finite K]
    (X : Type) [Group X] [Finite X] (A : Subgroup (MulAut X)) (σ : MulAut X) (J : Subgroup X)
    (θ : X ⧸ Subgroup.center X ≃* projectiveSL N K) (g : GL (Fin N) K) (ε : K),
    (p : K) ≠ 0 →
    5 ≤ N → g ^ p = 1 → commutator X = ⊤ → orderOf σ = p →
    GGTPNKernel A σ J → GGTPNSelfCent p A →
    (∀ a ∈ A, ∃ B : GL (Fin N) K,
      (∀ l : X, conjAut N K B (θ (l : X ⧸ Subgroup.center X)) =
        θ ((a l : X) : X ⧸ Subgroup.center X)) ∧ B * g * B⁻¹ = g) →
    (Polynomial.X - Polynomial.C ε) ∈ primaryFactors (glA g : Module.End K (Fin N → K)) →
    (∀ h ∈ primaryFactors (glA g : Module.End K (Fin N → K)),
      h ≠ (Polynomial.X - Polynomial.C ε) →
      primaryMultiplicity (glA g : Module.End K (Fin N → K)) h = 1) →
    J.map (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))) =
      (specialFactor g (Polynomial.X - Polynomial.C ε)).map (proj N K) →
    (primaryFactors (glA g : Module.End K (Fin N → K))).card ≤ 3

theorem tara_le_twoLocalRank_of_torusLift {X R : Type} [Group X] [Finite X] [Group R]
    {p r : ℕ} (hp : p.Prime) (hT : GGTorusLift p r R) (e : X ⧸ Subgroup.center X ≃* R)
    (hcomm : commutator X = ⊤) : r ≤ LargeEvenTwoLocalRank p X := by
  let ψ : X →* R := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
  have hψs : Function.Surjective ψ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ψ.ker = Subgroup.center X := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      change e (QuotientGroup.mk' (Subgroup.center X) x) = 1 at hx
      rw [QuotientGroup.mk'_apply] at hx
      have h1 : QuotientGroup.mk x = 1 := e.injective (by rw [hx, map_one])
      rwa [QuotientGroup.eq_one_iff] at h1
    · intro hx
      have h1 : QuotientGroup.mk' (Subgroup.center X) x = 1 := by
        rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      show e (QuotientGroup.mk' (Subgroup.center X) x) = 1
      rw [h1, map_one]
  obtain ⟨U, E, hUne, hU2, hEU, hEab, hEcard, -⟩ := hT X ψ hψs hker.le hcomm
  exact TableB.le_twoLocalRank (p := p) hp.one_lt ⟨U, hUne, hU2, rfl⟩
    (TableB.le_pRank_of_le hp.one_lt hEU hEab hEcard)

private theorem tara_nonsplit_rank_bound {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Type}
    [Group X] [Finite X] {A Ab : Subgroup (MulAut X)} {labX : LargeEvenLabel} {b : ℕ}
    (hperf : commutator X = ⊤) (hAb : Ab ≤ A) (hrank : GGTPNRank p X Ab)
    (hΛX : LargeEvenInLambda2 labX) (htag : labX.tag = .A) (hpn : p ∣ 2 ^ labX.n - 1)
    (hNb : p * b = labX.rank + 1) (hcardA : Nat.card A ≤ p ^ (b + 1))
    (hhX : GGHasLabel labX (X ⧸ Subgroup.center X)) : b ≤ 2 := by
  by_contra hb
  have hb3 : 3 ≤ b := by omega
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hr4 : 4 ≤ labX.rank := by
    have h9 : 9 ≤ p * b := by
      calc 9 = 3 * 3 := by norm_num
        _ ≤ p * b := Nat.mul_le_mul hp3 hb3
    omega
  have hAll := largeEvenLabelAll_torusLift_typeA (p := p) hp htag hr4 hpn
  have hRaw := hAll (fun R _ _ _ => Nonempty (X ⧸ Subgroup.center X ≃* R)) hhX
  obtain ⟨R, hR, I, F, ⟨⟨e⟩, hT⟩⟩ := largeEvenRawDatum_exists hRaw
  letI := hR
  have hlift : labX.rank + 1 - 2 ≤ LargeEvenTwoLocalRank p X :=
    tara_le_twoLocalRank_of_torusLift hp hT e hperf
  obtain ⟨m, hcardAb, hrankle⟩ := hrank
  have hε : (if p ∣ Nat.card (Subgroup.center X) then 1 else 0) ≤ 1 := by
    split <;> omega
  have hrm : labX.rank + 1 - 2 ≤ m + 1 := by omega
  have hmle : m ≤ b + 1 := by
    have hpm : p ^ m ≤ p ^ (b + 1) := by
      calc p ^ m = Nat.card Ab := hcardAb.symm
        _ ≤ Nat.card A := Subgroup.card_le_of_le hAb
        _ ≤ p ^ (b + 1) := hcardA
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hpm
  have hpb : p * b ≤ b + 4 := by omega
  have h3b : 3 * b ≤ p * b := Nat.mul_le_mul_right b hp3
  omega

private theorem tara_sum_eq_length (ds : List ℕ) (h : ∀ x ∈ ds, x = 1) :
    ds.sum = ds.length := by
  induction ds with
  | nil => simp
  | cons x xs ih =>
    have hx : x = 1 := h x (by simp)
    have hxs : ∀ y ∈ xs, y = 1 := fun y hy => h y (by simp [hy])
    simp [hx, ih hxs, Nat.add_comm]

private theorem tara_row_split_tagA {p : ℕ} {tJ tX : LargeEvenLieTag} {rJ nJ rX nX a : ℕ}
    {ds : List ℕ} (hJA : tJ = .A) (htX : tX = .A) (hpJ : p ∣ 2 ^ nJ - 1) (hJ2 : 2 ≤ rJ)
    (hdvdX : p ∣ rX + 1) (hsum : rX + 1 = a + ds.sum) (hds1 : ∀ x ∈ ds, x = 1)
    (hlen2 : ds.length ≤ 2) (hne : ds ≠ [])
    (ha1 : a - 1 = rJ) (hnX : nX = nJ) :
    GGTablePRow p (⟨tJ, rJ, nJ⟩ : LargeEvenLabel) (⟨tX, rX, nX⟩ : LargeEvenLabel) := by
  have hsum_eq : ds.sum = ds.length := tara_sum_eq_length ds hds1
  have hpos : 0 < ds.length := List.length_pos_iff.mpr hne
  have hk12 : ds.length = 1 ∨ ds.length = 2 := by omega
  have ha : a = rJ + 1 := by omega
  have hrX : rX = rJ + ds.length := by omega
  refine Or.inl ⟨hJA, hpJ, hJ2, ?_⟩
  rcases hk12 with hk1 | hk2
  · left
    rw [htX, hrX, hk1, hnX]
  · right; left
    refine ⟨?_, ?_⟩
    · rw [htX, hrX, hk2, hnX]
    · obtain ⟨c, hc⟩ := hdvdX
      refine ⟨c, ?_⟩
      dsimp only
      omega

private theorem tara_scalar_of_conjAut_eq_one {n : ℕ} {K : Type} [Field K] [Finite K]
    (hn : 2 ≤ n) (hpar : 3 ≤ n ∨ 5 ≤ Nat.card K) {A : GL (Fin n) K}
    (hA : conjAut n K A = 1) :
    ∃ c : Kˣ, A = Matrix.GeneralLinearGroup.scalar (Fin n) c := by
  have h1 :
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.innerDiagonalAction n K A = 1 := by
    have hc := congrArg (MulAut.congr
      (CFSG.ComponentClassification.CatalogueBLinearHigherB.nativeEquiv n K)) hA
    rw [CFSG.ComponentClassification.CatalogueBLinearHigherB.congr_conjAut, map_one] at hc
    exact hc
  open CFSG.ComponentClassification.CatalogueBHigherLinearInner in
  obtain ⟨c, hc⟩ := unit_scalar_of_innerDiagonalAction_eq_one n K hn hpar A h1
  exact ⟨c, hc.symm⟩

private theorem tara_conjAut_commute_scalar {N : ℕ} {K : Type} [Field K] [Finite K]
    (hN : 2 ≤ N) (hpar : 3 ≤ N ∨ 5 ≤ Nat.card K) {B g : GL (Fin N) K}
    (hcomm : conjAut N K B * conjAut N K g = conjAut N K g * conjAut N K B) :
    ∃ c : Kˣ, B * g * B⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin N) c * g := by
  have h1 : conjAut N K (B * g * B⁻¹ * g⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    rw [hcomm]
    group
  obtain ⟨c, hc⟩ := tara_scalar_of_conjAut_eq_one hN hpar h1
  refine ⟨c, ?_⟩
  rw [← hc]
  group

private theorem tara_glA_scalar {N : ℕ} {K : Type} [Field K] (c : Kˣ) :
    (Matrix.diagonal (fun _ : Fin N => (c : K))).mulVecLin = (c : K) • 1 := by
  ext v i
  simp [Matrix.mulVec_diagonal]

private theorem tara_map_primaryComponent_le {N : ℕ} {K : Type} [Field K]
    {B g : GL (Fin N) K} {c : Kˣ} {ε : K}
    (hB : B * g * B⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin N) c * g) :
    (primaryComponent (glA g : Module.End K (Fin N → K)) (X - C ε)).map (glA B : Module.End K (Fin
      N → K)) ≤
      primaryComponent (glA g : Module.End K (Fin N → K)) (X - C ((c : K)⁻¹ * ε)) := by
  intro w hw
  obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hw
  let P : (Module.End K (Fin N → K))ˣ := glA B
  let x : Module.End K (Fin N → K) := glA g
  have hPcoe : (↑P : Module.End K (Fin N → K)) = (glA B : Module.End K (Fin N → K)) := rfl
  have hxcoe : x = (glA g : Module.End K (Fin N → K)) := rfl
  have h1 : (↑P : Module.End K (Fin N → K)) * x * ↑P⁻¹ = (c : K) • x := by
    have h := congrArg (fun T : GL (Fin N) K => (glA T : Module.End K (Fin N → K))) hB
    simpa [P, x, map_mul, tara_glA_scalar] using h
  have hQ : ↑P⁻¹ * (↑P : Module.End K (Fin N → K)) = 1 := by simp
  have h2 : (↑P : Module.End K (Fin N → K)) * x * ↑P⁻¹ * ↑P = ↑P * x := by
    rw [mul_assoc, hQ, mul_one]
  have hPx : (↑P : Module.End K (Fin N → K)) * x = (c : K) • (x * ↑P) := by
    calc (↑P : Module.End K (Fin N → K)) * x
        = (↑P : Module.End K (Fin N → K)) * x * ↑P⁻¹ * ↑P := h2.symm
      _ = ((↑P : Module.End K (Fin N → K)) * x * ↑P⁻¹) * ↑P := by rw [mul_assoc]
      _ = ((c : K) • x) * (↑P : Module.End K (Fin N → K)) := by rw [h1]
      _ = (c : K) • (x * (↑P : Module.End K (Fin N → K))) := by rw [smul_mul_assoc]
  have hPx' : (↑P : Module.End K (Fin N → K)) (x v) =
      (c : K) • (x ((↑P : Module.End K (Fin N → K)) v)) := by
    have := congrArg (fun T : Module.End K (Fin N → K) => T v) hPx
    simpa only [Module.End.mul_apply, LinearMap.smul_apply] using this
  have hxPv : x ((↑P : Module.End K (Fin N → K)) v) =
      (c : K)⁻¹ • ((↑P : Module.End K (Fin N → K)) (x v)) := by
    rw [hPx', smul_smul, inv_mul_cancel₀ c.ne_zero, one_smul]
  have hv' : x v = ε • v := by
    have := mem_primaryComponent.mp hv
    simpa [sub_eq_zero, x] using this
  rw [mem_primaryComponent]
  calc aeval x (X - C ((c : K)⁻¹ * ε)) ((↑P : Module.End K (Fin N → K)) v)
      = x ((↑P : Module.End K (Fin N → K)) v) -
          ((c : K)⁻¹ * ε) • ((↑P : Module.End K (Fin N → K)) v) := by
        simp only [Polynomial.aeval_X, Polynomial.aeval_C, map_sub, map_mul,
          Algebra.algebraMap_eq_smul_one, LinearMap.sub_apply, LinearMap.smul_apply,
          Module.End.one_apply, smul_mul_assoc, one_mul, smul_smul]
    _ = (c : K)⁻¹ • ((↑P : Module.End K (Fin N → K)) (x v)) -
          ((c : K)⁻¹ * ε) • ((↑P : Module.End K (Fin N → K)) v) := by rw [hxPv]
    _ = (c : K)⁻¹ • ((↑P : Module.End K (Fin N → K)) (ε • v)) -
          ((c : K)⁻¹ * ε) • ((↑P : Module.End K (Fin N → K)) v) := by rw [hv']
    _ = (c : K)⁻¹ • (ε • ((↑P : Module.End K (Fin N → K)) v)) -
          ((c : K)⁻¹ * ε) • ((↑P : Module.End K (Fin N → K)) v) := by rw [map_smul]
    _ = 0 := by rw [smul_smul, mul_comm, sub_self]

private theorem tara_c_eq_one {N : ℕ} {K : Type} [Field K] [Finite K]
    {g B : GL (Fin N) K} {c : Kˣ} {ε : K}
    (hB : B * g * B⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin N) c * g)
    (hε0 : ε ≠ 0)
    (huniq_mult : ∀ a ∈ primaryFactors (glA g : Module.End K (Fin N → K)), a ≠ X - C ε →
      primaryMultiplicity (glA g : Module.End K (Fin N → K)) a = 1)
    (h2 : 2 ≤ primaryMultiplicity (glA g : Module.End K (Fin N → K)) (X - C ε))
    (hc1 : c ≠ 1) : False := by
  classical
  have hle : (primaryComponent (glA g : Module.End K (Fin N → K)) (X - C ε)).map (glA B :
    Module.End K (Fin N → K)) ≤
      primaryComponent (glA g : Module.End K (Fin N → K)) (X - C ((c : K)⁻¹ * ε)) :=
        tara_map_primaryComponent_le hB
  have hfinV : Module.finrank K (primaryComponent (glA g : Module.End K (Fin N → K)) (X - C ε)) =
      primaryMultiplicity (glA g : Module.End K (Fin N → K)) (X - C ε) := by
    haveI : Fact (Irreducible (X - C ε : K[X])) := ⟨irreducible_X_sub_C ε⟩
    rw [finrank_primaryComponent, show (X - C ε : K[X]).natDegree = 1 by simp, one_mul]
  have hfinW : Module.finrank K (primaryComponent (glA g : Module.End K (Fin N → K)) (X - C ε)) ≤
      Module.finrank K (primaryComponent (glA g : Module.End K (Fin N → K))
        (X - C ((c : K)⁻¹ * ε))) := by
    have hle' : primaryComponent (glA g : Module.End K (Fin N → K)) (X - C ε) ≤
        (primaryComponent (glA g : Module.End K (Fin N → K)) (X - C ((c : K)⁻¹ * ε))).comap
          (glA B : Module.End K (Fin N → K)) :=
      Submodule.map_le_iff_le_comap.mp hle
    let φ : (primaryComponent (glA g : Module.End K (Fin N → K)) (X - C ε)) →ₗ[K]
        (primaryComponent (glA g : Module.End K (Fin N → K)) (X - C ((c : K)⁻¹ * ε))) :=
      { toFun := fun v => ⟨(glA B : Module.End K (Fin N → K)) v.1, hle' v.2⟩
        map_add' := fun v w => Subtype.ext (map_add _ _ _)
        map_smul' := fun a v => Subtype.ext (map_smul _ _ _) }
    have hφinj : Function.Injective φ := by
      intro v w h
      have h2 : (glA B : Module.End K (Fin N → K)) v.1 =
          (glA B : Module.End K (Fin N → K)) w.1 := congrArg Subtype.val h
      have h3 : v.1 = w.1 := by
        have h4 := congrArg (fun z => (↑((glA B)⁻¹) : Module.End K (Fin N → K)) z) h2
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, Units.inv_mul,
          Module.End.one_apply, Module.End.one_apply] at h4
        exact h4
      exact Subtype.ext h3
    exact LinearMap.finrank_le_finrank_of_injective (f := φ) hφinj
  have hW2 : 2 ≤ Module.finrank K (primaryComponent (glA g : Module.End K (Fin N → K)) (X - C ((c :
    K)⁻¹ * ε))) := by
    rw [← hfinV] at h2
    omega
  have hWne : primaryComponent (glA g : Module.End K (Fin N → K)) (X - C ((c : K)⁻¹ * ε)) ≠ ⊥ := by
    intro hbot
    rw [hbot] at hW2
    simp at hW2
  have hmemW : X - C ((c : K)⁻¹ * ε) ∈ primaryFactors (glA g : Module.End K (Fin N → K)) :=
    CFSG.RankThree.PartOne.KCOrthogonal.mem_primaryFactors_of_primaryComponent_ne_bot
      (irreducible_X_sub_C _) (monic_X_sub_C _) hWne
  have hne : X - C ((c : K)⁻¹ * ε) ≠ X - C ε := by
    intro heq
    have hcoeff : (c : K)⁻¹ * ε = ε := by
      have := congrArg (fun p : K[X] => p.coeff 0) heq
      simpa using this
    have hc : (c : K)⁻¹ = 1 := mul_right_cancel₀ hε0 (by rw [hcoeff, one_mul])
    exact hc1 (Units.ext (inv_eq_one.mp hc))
  have hmultW : primaryMultiplicity (glA g : Module.End K (Fin N → K))
      (X - C ((c : K)⁻¹ * ε)) = 1 := huniq_mult _ hmemW hne
  have hfinW1 : Module.finrank K (primaryComponent (glA g : Module.End K (Fin N → K)) (X - C ((c :
    K)⁻¹ * ε))) = 1 := by
    haveI : Fact (Irreducible (X - C ((c : K)⁻¹ * ε) : K[X])) := ⟨irreducible_X_sub_C _⟩
    rw [finrank_primaryComponent,
      show (X - C ((c : K)⁻¹ * ε) : K[X]).natDegree = 1 from Polynomial.natDegree_X_sub_C _,
      one_mul]
    exact hmultW
  omega

private theorem tara_exists_sl_section {N : ℕ} {K : Type} [Field K] [Finite K]
    {X : Type} [Group X] [Finite X]
    {θ : X ⧸ Subgroup.center X ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL N K}
    (hN : 5 ≤ N) (hperf : commutator X = ⊤) :
    ∃ φ : SpecialLinearGroup (Fin N) K →* X,
      ∀ g, θ ((φ g : X) : X ⧸ Subgroup.center X) =
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj N K g := by
  let ψ : X →* projectiveSL N K :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
  have hψ : Function.Surjective ψ := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ψ.ker ≤ Subgroup.center X := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : θ (QuotientGroup.mk' (Subgroup.center X) x) = θ 1 := by
      rw [map_one]
      exact hx
    have h2 := θ.injective h1
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
  have hsec : TypeA.SLHasSections N K := TypeA.slHasSections_of_five_le (d := N) (K := K) hN
  obtain ⟨φ, -, hφ⟩ := TypeA.exists_sl_cover hsec ψ hψ hker hperf
  exact ⟨φ, hφ⟩

private theorem tara_section_centralizes {N : ℕ} {K : Type} [Field K] [Finite K]
    {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)}
    {θ : X ⧸ Subgroup.center X ≃* projectiveSL N K} (hN : 5 ≤ N)
    {φ : SpecialLinearGroup (Fin N) K →* X}
    (hφ : ∀ g, θ ((φ g : X) : X ⧸ Subgroup.center X) = proj N K g)
    {a : MulAut X} {B : GL (Fin N) K}
    (hB : ∀ l : X, conjAut N K B (θ (l : X ⧸ Subgroup.center X)) =
      θ ((a l : X) : X ⧸ Subgroup.center X))
    {t : SpecialLinearGroup (Fin N) K}
    (ht : CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation N K B t = t) :
    a (φ t) = φ t := by
  let ψ : X →* projectiveSL N K :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
  have hψφ : ∀ s : SpecialLinearGroup (Fin N) K, ψ (φ s) = proj N K s := fun s => hφ s
  let α : SpecialLinearGroup (Fin N) K →* X := a.toMonoidHom.comp φ
  let β : SpecialLinearGroup (Fin N) K →* X :=
    φ.comp (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation N K
      B).toMonoidHom
  have hker : ψ.ker = Subgroup.center X := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have h1 : θ (QuotientGroup.mk' (Subgroup.center X) x) = θ 1 := by
        rw [map_one]
        exact hx
      have h2 := θ.injective h1
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    · intro hx
      have h1 : QuotientGroup.mk' (Subgroup.center X) x = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hx
      show θ (QuotientGroup.mk' (Subgroup.center X) x) = 1
      rw [h1, map_one]
  have hcenter : ∀ s, (α s)⁻¹ * β s ∈ Subgroup.center X := by
    intro s
    have h1 : ψ (α s) = ψ (β s) := by
      change θ ((a (φ s) : X) : X ⧸ Subgroup.center X) =
        θ ((φ (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation N K B s) :
          X) :
          X ⧸ Subgroup.center X)
      rw [← hB (φ s), hφ s, hφ
        (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation N K B s),
        conjAut_proj]
    have h2 : ψ ((α s)⁻¹ * β s) = 1 := by
      rw [map_mul, map_inv, h1, inv_mul_cancel]
    show (α s)⁻¹ * β s ∈ Subgroup.center X
    rw [← hker]
    exact h2
  have hperf_sl : Group.IsPerfect (SpecialLinearGroup (Fin N) K) :=
    CFSG.ComponentClassification.CatalogueBHigherLinearInner.sl_perfect N K (by omega) (Or.inl (by
      omega))
  have hperf_sl' : commutator (SpecialLinearGroup (Fin N) K) = ⊤ := Group.isPerfect_def.mp hperf_sl
  have heq : α = β := TypeA.eq_of_inv_mul_mem_center hperf_sl' α β hcenter
  have ht' := congrArg (fun f : SpecialLinearGroup (Fin N) K →* X => f t) heq
  change a (φ t) = φ (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation N K B
    t) at ht'
  rwa [ht] at ht'

private theorem tara_J_trivial_of_blockScalar {N : ℕ} {K : Type} [Field K] [Finite K]
    {X : Type} [Group X] [Finite X] {J : Subgroup X}
    {θ : X ⧸ Subgroup.center X ≃* projectiveSL N K}
    {φ : SpecialLinearGroup (Fin N) K →* X}
    (hφ : ∀ g, θ ((φ g : X) : X ⧸ Subgroup.center X) = proj N K g)
    {g : GL (Fin N) K} {ε : K}
    (hTeq : J.map (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))) =
      (specialFactor g (Polynomial.X - Polynomial.C ε)).map (proj N K))
    {τ : SpecialLinearGroup (Fin N) K}
    (hτ : ∀ B : GL (Fin N) K, B * g * B⁻¹ = g →
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation N K B τ = τ) :
    ∀ j ∈ J, MulAut.conj (φ τ) j = j := by
  intro j hj
  have hjbar : θ (QuotientGroup.mk' (Subgroup.center X) j) ∈
      (specialFactor g (Polynomial.X - Polynomial.C ε)).map (proj N K) := by
    rw [← hTeq]
    exact Subgroup.mem_map_of_mem _ hj
  obtain ⟨s, hs, hsj⟩ := Subgroup.mem_map.mp hjbar
  have hsg : (s : GL (Fin N) K) * g * (s : GL (Fin N) K)⁻¹ = g := by
    have h1 :
        CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation N K g s = s := by
      have hs' := specialFactor_le_fixSubgroup g (Polynomial.X - Polynomial.C ε) hs
      rwa [mem_fixSubgroup] at hs'
    have h2 : g * (s : GL (Fin N) K) * g⁻¹ = (s : GL (Fin N) K) := by
      have := congrArg (fun x : SpecialLinearGroup (Fin N) K => Matrix.SpecialLinearGroup.toGL x) h1
      simpa [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation] using
        this
    have h2' : g * (s : GL (Fin N) K) = (s : GL (Fin N) K) * g := by
      have := congrArg (fun x => x * g) h2
      simpa [mul_assoc] using this
    rw [← h2', mul_assoc, mul_inv_cancel, mul_one]
  have hsτ : τ * s * τ⁻¹ = s := by
    have h1 := hτ (s : GL (Fin N) K) hsg
    have h2 : (s : GL (Fin N) K) * (τ : GL (Fin N) K) * (s : GL (Fin N) K)⁻¹ =
        (τ : GL (Fin N) K) := by
      have := congrArg (fun x : SpecialLinearGroup (Fin N) K => Matrix.SpecialLinearGroup.toGL x) h1
      simpa [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation] using
        this
    have h2' : (s : GL (Fin N) K) * (τ : GL (Fin N) K) =
        (τ : GL (Fin N) K) * (s : GL (Fin N) K) := by
      have := congrArg (fun x => x * (s : GL (Fin N) K)) h2
      simpa [mul_assoc] using this
    have h3 : s * τ = τ * s := Matrix.SpecialLinearGroup.toGL_injective (by
      rw [map_mul, map_mul]
      exact h2')
    rw [← h3]; group
  have hw : (φ s)⁻¹ * j ∈ Subgroup.center X := by
    rw [← QuotientGroup.eq]
    exact θ.injective ((hφ s).trans hsj)
  have hw' : ∀ x : X, x * ((φ s)⁻¹ * j) = ((φ s)⁻¹ * j) * x :=
    fun x => Subgroup.mem_center_iff.mp hw x
  have hj_eq : j = φ s * ((φ s)⁻¹ * j) := by group
  have hτs : (φ τ) * (φ s) * (φ τ)⁻¹ = φ s := by
    simpa [map_mul] using congrArg φ hsτ
  rw [hj_eq, map_mul, MulAut.conj_apply, MulAut.conj_apply, hτs]
  congr 1
  show (φ τ) * ((φ s)⁻¹ * j) * (φ τ)⁻¹ = (φ s)⁻¹ * j
  rw [hw' (φ τ)]
  group

private theorem tara_split_structure_rankTwo {p N : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hpk : (p : K) ≠ 0) (hpq : p ∣ Nat.card K - 1)
    {g : GL (Fin N) K} (hg : g ^ p = 1) (hgne : conjAut N K g ≠ 1)
    {T : Subgroup (projectiveSL N K)}
    (hT : CFSG.Open.IsComponentOf T (fixSubgroup (conjAut N K g)))
    (hTonly : ∀ Q : Subgroup (projectiveSL N K),
      CFSG.Open.IsComponentOf Q (fixSubgroup (conjAut N K g)) → p ∣ Nat.card Q → Q = T)
    (hcard3 : (primaryFactors (glA g : Module.End K (Fin N → K))).card ≤ 3) :
    ∃ (a : ℕ) (ds : List ℕ) (E : Type) (_ : Field E) (_ : Fintype E),
      Nat.card E = Nat.card K ∧ 2 ≤ a ∧ N = a + ds.sum ∧ ds ≠ [] ∧ ds.length ≤ 2 ∧
      (∀ x ∈ ds, x = 1) ∧
      Nonempty (↥T ⧸ Subgroup.center ↥T ≃* projectiveSL a E) := by
  classical
  have hsq : Squarefree (minpoly K (glA g : Module.End K (Fin N → K))) :=
    squarefree_minpoly_glA hpk (c := 1) (by simpa using hg)
  obtain ⟨h, ε, hh, hgood, hform, hε0, hdeg, hdegS, -, hK4, -, hTeq⟩ :=
    raLin_split_factor hp hp2 hpk hpq hg hT
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  obtain ⟨hEcard, hm2, ⟨eT⟩⟩ := raLin_split_centralQuot hpk hg hh hgood hdeg hTeq
  have hmult1 := raLin_split_mult_one hp hpq hsq hTonly hh hgood hTeq hdegS hK4
  have hN := raLin_split_finrank hsq hh hdeg hdegS hmult1
  have hcard2 := raLin_split_card_ge_two hsq hh hform hε0 hgne
  haveI hEfin : Finite (AdjoinRoot h) := Module.finite_of_finite K
  refine ⟨primaryMultiplicity (glA g : Module.End K (Fin N → K)) h,
    List.replicate ((primaryFactors (glA g : Module.End K (Fin N → K))).card - 1) 1,
    AdjoinRoot h, inferInstance, Fintype.ofFinite (AdjoinRoot h), hEcard, hm2, ?_, ?_, ?_, ?_,
    ⟨eT⟩⟩
  · rw [List.sum_replicate, smul_eq_mul, mul_one]
    exact hN
  · intro hnil
    have h0 : (primaryFactors (glA g : Module.End K (Fin N → K))).card - 1 = 0 := by
      simpa using congrArg List.length hnil
    omega
  · rw [List.length_replicate]
    omega
  · intro x hx
    simp only [List.mem_replicate] at hx
    exact hx.2

private theorem tara_primaryCount_of_core : GGRAPrimaryCount := by
  have hcore := ggBlockScalarCore_holds
  intro p N hp hp2 K _ _ X _ _ A σ J θ g ε hpk hN5 hg hperf hord hk hself hT8 hgood huniq hTeq
  by_contra hcard
  push Not at hcard
  obtain ⟨U, hUcard, hUpow, hUcomm, hUgood⟩ := hcore p N hp hp2 K g ε hg hgood huniq hcard
  obtain ⟨φ, hφ⟩ := tara_exists_sl_section (N := N) (K := K) (X := X) (θ := θ) hN5 hperf
  have hsq : Squarefree (minpoly K (glA g : Module.End K (Fin N → K))) :=
    squarefree_minpoly_glA hpk (c := 1) (by simpa using hg)
  have hVne : primaryComponent (glA g : Module.End K (Fin N → K))
      (Polynomial.X - Polynomial.C ε) ≠ ⊥ := primaryComponent_ne_bot hsq hgood
  have hmemA : ∀ τ : U, MulAut.conj (φ τ) ∈ A := by
    intro τ
    have hcent : ∀ a ∈ A, a (φ τ) = φ τ := by
      intro a ha
      obtain ⟨B, hB, hBg⟩ := hT8 a ha
      exact tara_section_centralizes (N := N) (K := K) (X := X) (A := A) hN5 hφ hB
        (hUcomm τ τ.2 B hBg)
    have hp1 : (φ τ) ^ p = 1 := by rw [← map_pow, hUpow τ τ.2, map_one]
    exact hself (φ τ) hcent hp1
  have hmemσ : ∀ τ : U, MulAut.conj (φ τ) ∈ Subgroup.zpowers σ := by
    intro τ
    have hJ : ∀ j ∈ J, MulAut.conj (φ τ) j = j :=
      tara_J_trivial_of_blockScalar (N := N) (K := K) (X := X) (J := J) (θ := θ) hφ hTeq
        (fun B hB => hUcomm τ τ.2 B hB)
    exact hk (MulAut.conj (φ τ)) (hmemA τ) hJ
  let f : U → Subgroup.zpowers σ := fun τ => ⟨MulAut.conj (φ τ), hmemσ τ⟩
  let ψ : X →* projectiveSL N K := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
  have hψker : ψ.ker = Subgroup.center X := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have h1 : θ (QuotientGroup.mk' (Subgroup.center X) x) = θ 1 := by rw [map_one]; exact hx
      have h2 := θ.injective h1
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    · intro hx
      have h1 : QuotientGroup.mk' (Subgroup.center X) x = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact hx
      show θ (QuotientGroup.mk' (Subgroup.center X) x) = 1
      rw [h1, map_one]
  have hψφ : ∀ s, ψ (φ s) = proj N K s := fun s => hφ s
  have hfinj : Function.Injective f := by
    intro τ τ' h
    have hconj : MulAut.conj (φ τ) = MulAut.conj (φ τ') := congrArg Subtype.val h
    have hker : φ τ * (φ τ')⁻¹ ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro x
      have h1 : MulAut.conj (φ τ * (φ τ')⁻¹) = 1 := by
        rw [map_mul, map_inv, hconj, mul_inv_cancel]
      have h2 := congrArg (fun e : MulAut X => e x) h1
      rw [MulAut.conj_apply, MulAut.one_apply] at h2
      have h3 : (φ τ * (φ τ')⁻¹) * x = x * (φ τ * (φ τ')⁻¹) := by
        have := congrArg (fun y => y * (φ τ * (φ τ')⁻¹)) h2
        simpa [mul_assoc] using this
      exact h3.symm
    have hproj : proj N K τ = proj N K τ' := by
      have h1 : ψ (φ τ * (φ τ')⁻¹) = 1 := MonoidHom.mem_ker.mp (by rwa [hψker])
      rw [map_mul, map_inv] at h1
      have h2 : ψ (φ τ) = ψ (φ τ') := mul_inv_eq_one.mp h1
      rwa [hψφ τ, hψφ τ'] at h2
    obtain ⟨c, hc, hcmat⟩ := mem_scalars.mp ((proj_eq_proj_iff).mp hproj)
    have hc' : τ⁻¹ * τ' = scalarElement c hc := Subtype.ext hcmat
    have hτ'eq : τ' = τ * scalarElement c hc := by
      rw [← hc']
      simp
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hVne
    have hs : (glA ((scalarElement c hc : SpecialLinearGroup (Fin N) K) : GL (Fin N) K) :
        Module.End K (Fin N → K)) v = v := by
      have h1 : (glA (τ' : GL (Fin N) K) : Module.End K (Fin N → K)) v = v :=
        hUgood τ' τ'.2 v hv
      have h2 : (glA (τ' : GL (Fin N) K) : Module.End K (Fin N → K)) v =
          (glA (τ : GL (Fin N) K) : Module.End K (Fin N → K))
            ((glA ((scalarElement c hc : SpecialLinearGroup (Fin N) K) : GL (Fin N) K) :
              Module.End K (Fin N → K)) v) := by
        rw [hτ'eq]
        simp only [map_mul, Units.val_mul, Module.End.mul_apply]
      have hinj : Function.Injective (glA (τ : GL (Fin N) K) : Module.End K (Fin N → K)) := by
        intro a b hab
        have h := congrArg (fun w => (↑((glA (τ : GL (Fin N) K))⁻¹) :
          Module.End K (Fin N → K)) w) hab
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, Units.inv_mul,
          Module.End.one_apply, Module.End.one_apply] at h
        exact h
      rw [h2] at h1
      exact hinj (h1.trans (hUgood τ τ.2 v hv).symm)
    have h2 : (c : K) • v = v := by
      have h := congrArg (fun T : Module.End K (Fin N → K) => T v) (tara_glA_scalar c)
      simpa using h.symm.trans hs
    have h3 : (c : K) = 1 := by
      have h4 : ((c : K) - 1) • v = 0 := by rw [sub_smul, one_smul, h2, sub_self]
      rcases (smul_eq_zero.mp h4) with h5 | h5
      · exact sub_eq_zero.mp h5
      · exact absurd h5 hv0
    have hc1 : c = 1 := Units.ext h3
    have hs1 : scalarElement c hc = 1 := by
      apply Subtype.ext
      show (scalar (Fin N) (c : K)) = (1 : Matrix (Fin N) (Fin N) K)
      rw [h3]
      simp
    have h4 : τ⁻¹ * τ' = 1 := Subtype.ext (hc'.trans hs1)
    exact inv_mul_eq_one.mp h4
  have hle : Nat.card U ≤ Nat.card (Subgroup.zpowers σ) := Nat.card_le_card_of_injective f hfinj
  rw [Nat.card_zpowers, hord] at hle
  have h1 : p * p ≤ p := by
    simpa [pow_two] using le_trans hUcard hle
  nlinarith [hp.two_le]

private theorem tara_descent {p : ℕ} [Fact p.Prime] {X : Type} [Group X] [Finite X]
    {σ : MulAut X} {J : Subgroup X}
    (hcomm : commutator X = ⊤) (hJ : IsComponentOf J (ggAutFixedSubgroup σ))
    (h8 : GGTPNOnlyComp p σ J) {N : ℕ} {K : Type} [Field K] [Finite K]
    {θ : X ⧸ Subgroup.center X ≃* projectiveSL N K} {g : GL (Fin N) K}
    (hσbar : ggInducedAut θ σ = conjAut N K g) :
    ∃ Jbar : Subgroup (projectiveSL N K),
      Jbar = J.map (TablePThreeKG.proj θ) ∧
      CFSG.Open.IsComponentOf Jbar (fixSubgroup (conjAut N K g)) ∧
      (∀ Q : Subgroup (projectiveSL N K),
        CFSG.Open.IsComponentOf Q (fixSubgroup (conjAut N K g)) → p ∣ Nat.card Q → Q = Jbar) ∧
      Nonempty (↥J ⧸ Subgroup.center ↥J ≃* ↥Jbar ⧸ Subgroup.center ↥Jbar) := by
  obtain ⟨hJbar, huniq, hequiv⟩ :=
    ggTPNOnlyComp_map_proj (p := p) hcomm hJ h8 (R := projectiveSL N K) θ
  refine ⟨J.map (TablePThreeKG.proj θ), rfl, ?_, ?_, hequiv⟩
  · have h1 : CFSG.Assembly.IsComponentOf (J.map (TablePThreeKG.proj θ))
        (ggAutFixedSubgroup (ggInducedAut θ σ)) := hJbar
    have h2 := CFSG.Assembly.isComponentOf_iff_open.mp h1
    rwa [hσbar] at h2
  · intro Q hQ hpQ
    refine huniq Q ?_ hpQ
    have h2 : CFSG.Assembly.IsComponentOf Q (ggAutFixedSubgroup (ggInducedAut θ σ)) := by
      rw [hσbar]
      exact CFSG.Assembly.isComponentOf_iff_open.mpr hQ
    exact h2

private theorem tara_labelIso_A_A {r1 n1 r2 n2 : ℕ}
    (h : GGLabelIso (⟨.A, r1, n1⟩ : LargeEvenLabel) ⟨.A, r2, n2⟩) :
    (⟨.A, r1, n1⟩ : LargeEvenLabel) = ⟨.A, r2, n2⟩ := by
  rcases h with h | h | h | h | h | h | h | h
  · exact h
  · rcases h.1 with h1 | h1 <;> exact absurd h1 (by simp)
  · exact absurd (congrArg LargeEvenLabel.tag h.1) (by simp)
  · exact absurd (congrArg LargeEvenLabel.tag h.2) (by simp)
  · exact absurd (congrArg LargeEvenLabel.tag h.1) (by simp)
  · exact absurd (congrArg LargeEvenLabel.tag h.1) (by simp)
  · exact absurd (congrArg LargeEvenLabel.tag h.1) (by simp)
  · exact absurd (congrArg LargeEvenLabel.tag h.1) (by simp)

private theorem tara_rankTwo_of_primaryCount
    (hC : GGRAPrimaryCount) : GGRARankTwo := by
  intro p hp hp2 X _ _ A σ J labX hloc honly hk hself hRA htag hm
  intro a ds hsum hne hlen hmem hbr
  obtain ⟨tX, rX, nX⟩ := labX
  dsimp only at htag hRA hm hsum hmem hbr
  by_cases hp3 : p = 3
  · rw [hp3] at hlen
    exact Nat.le_of_lt_succ hlen
  · have hp5 : 5 ≤ p := by
      have h3 : 3 ≤ p := by have := hp.two_le; omega
      have hodd : p % 2 = 1 := (hp.eq_two_or_odd).resolve_left hp2
      omega
    have hpN : p ∣ rX + 1 := by
      rcases hRA with ⟨-, hd, -⟩ | ⟨hbad, -⟩
      · exact hd
      · exact absurd (hbad.symm.trans htag) (by simp)
    have hpq2 : p ∣ 2 ^ nX - 1 := by
      rcases hRA with ⟨-, -, hd⟩ | ⟨hbad, -⟩
      · exact hd
      · exact absurd (hbad.symm.trans htag) (by simp)
    have hds1 : ∀ x ∈ ds, x = 1 := by
      intro x hx
      rcases hmem x hx with h1 | ⟨hbad, -, -⟩
      · exact h1
      · exact absurd (hbad.symm.trans htag) (by simp)
    obtain ⟨K, hFld, hFin, hKcard, θ, hAll, g, ⟨u, hgu⟩, hgl, hcomm⟩ :=
      raLin_model hp hloc htag hm
    letI : Field K := hFld
    haveI : Finite K := hFin
    dsimp only at hKcard θ hAll g hgu hgl hcomm
    obtain ⟨hp2', hpk, hn1, hpq⟩ := raLin_arith (K := K) hp hKcard hpq2
    have hn2 := raLin_two_le_n hp hn1 hpq2
    have hN5 : 5 ≤ rX + 1 := by
      have hle : p ≤ rX + 1 := Nat.le_of_dvd (by omega) hpN
      omega
    haveI : Fact p.Prime := ⟨hp⟩
    have hJcomp : IsComponentOf J (ggAutFixedSubgroup σ) := hloc.2.2.2.1
    have hσbar : ggInducedAut θ σ = conjAut (rX + 1) K g := by
      ext x
      obtain ⟨z, rfl⟩ := θ.surjective x
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective z
      rw [ggInducedAut_apply, hgl]
    have hgne := raLin_conjAut_ne_one hloc hcomm hσbar
    obtain ⟨Jbar, hJbar_id, hJbarOpen, huniq, hequiv⟩ :=
      tara_descent (p := p) hcomm hJcomp honly hσbar
    have hσp : orderOf σ = p := by
      have h1 : orderOf σ ∣ p := orderOf_dvd_of_pow_eq_one (hloc.1.2 σ hloc.2.1)
      rcases (Nat.dvd_prime hp).mp h1 with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hloc.2.2.1
      · exact h
    by_cases hsplit : ∃ b : K, b ^ p = (u : K)
    · obtain ⟨g', hg', hconj'⟩ := raLin_rescale (N := rX + 1) hp hgu hsplit
      have hgne' : conjAut (rX + 1) K g' ≠ 1 := by rw [hconj']; exact hgne
      have hJbarOpen' : CFSG.Open.IsComponentOf Jbar (fixSubgroup (conjAut (rX + 1) K g')) := by
        rw [hconj']; exact hJbarOpen
      have huniq' : ∀ Q : Subgroup (projectiveSL (rX + 1) K),
          CFSG.Open.IsComponentOf Q (fixSubgroup (conjAut (rX + 1) K g')) →
            p ∣ Nat.card Q → Q = Jbar := by
        intro Q hQ hpQ
        rw [hconj'] at hQ
        exact huniq Q hQ hpQ
      obtain ⟨h, ε, hh, hgood, hform, hε0, hdeg, hdegS, hEcard, hK4, hm2, hTeq⟩ :=
        raLin_split_factor (N := rX + 1) hp hp2 hpk hpq hg' hJbarOpen'
      haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
      have hmult1 := raLin_split_mult_one (N := rX + 1) hp hpq
        (squarefree_minpoly_glA hpk (c := 1) (by simpa using hg')) huniq' hh hgood hTeq hdegS hK4
      have hgood' : (Polynomial.X - Polynomial.C ε) ∈
          primaryFactors (glA g' : Module.End K (Fin (rX + 1) → K)) := by
        rw [← hform]; exact hh
      have hmult1' : ∀ a ∈ primaryFactors (glA g' : Module.End K (Fin (rX + 1) → K)),
          a ≠ (Polynomial.X - Polynomial.C ε) → primaryMultiplicity
            (glA g' : Module.End K (Fin (rX + 1) → K)) a = 1 :=
        fun a ha hne => hmult1 a ha (fun hh' => hne (hh'.trans hform))
      have hm2' : 2 ≤ primaryMultiplicity (glA g' : Module.End K (Fin (rX + 1) → K))
          (Polynomial.X - Polynomial.C ε) := by rw [← hform]; exact hm2
      have hab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
        intro x hx y hy
        exact congrArg Subtype.val (hloc.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
      have hT8 : ∀ a' ∈ A, ∃ B : GL (Fin (rX + 1)) K,
          (∀ l : X, conjAut (rX + 1) K B (θ (l : X ⧸ Subgroup.center X)) =
            θ ((a' l : X) : X ⧸ Subgroup.center X)) ∧ B * g' * B⁻¹ = g' := by
        intro a' ha'
        obtain ⟨B, hB⟩ := hAll a' ha'
        have hB' : conjAut (rX + 1) K B = ggInducedAut θ a' := by
          ext x
          obtain ⟨z, rfl⟩ := θ.surjective x
          obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective z
          rw [ggInducedAut_apply, hB l]
        have hgl' : conjAut (rX + 1) K g = ggInducedAut θ σ := by
          ext x
          obtain ⟨z, rfl⟩ := θ.surjective x
          obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective z
          rw [ggInducedAut_apply, hgl]
        have hcommB : conjAut (rX + 1) K B * conjAut (rX + 1) K g' =
            conjAut (rX + 1) K g' * conjAut (rX + 1) K B := by
          rw [hB', hconj', hgl']
          ext x
          obtain ⟨z, rfl⟩ := θ.surjective x
          obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective z
          have h1 : a' (σ l) = σ (a' l) :=
            congrArg (fun f : MulAut X => f l) (hab a' ha' σ hloc.2.1)
          simp only [MulAut.mul_apply]
          rw [ggInducedAut_apply, ggInducedAut_apply, ggInducedAut_apply, ggInducedAut_apply, h1]
        obtain ⟨c, hc⟩ := tara_conjAut_commute_scalar (N := rX + 1) (by omega) (Or.inl (by omega))
          hcommB
        refine ⟨B, hB, ?_⟩
        have hc1 : c = 1 := by
          by_contra hc1
          exact tara_c_eq_one (N := rX + 1) hc hε0 hmult1' hm2' hc1
        rw [hc, hc1, map_one, one_mul]
      have hTeq' : J.map (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))) =
          (specialFactor g' (Polynomial.X - Polynomial.C ε)).map (proj (rX + 1) K) := by
        rw [show J.map (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))) = Jbar from
          hJbar_id.symm, ← hform]
        exact hTeq
      have hcard3 : (primaryFactors (glA g' : Module.End K (Fin (rX + 1) → K))).card ≤ 3 :=
        hC p (rX + 1) hp hp2 K X A σ J θ g' ε hpk hN5 hg' hcomm hσp hk hself hT8 hgood' hmult1'
          hTeq'
      obtain ⟨a0, ds0, E, hEfld, hEfin, hEcardE, ha0, hN0, hds0ne, hds0le, hds0one, heT⟩ :=
        tara_split_structure_rankTwo (N := rX + 1) hp hp2 hpk hpq hg' hgne' hJbarOpen' huniq'
          hcard3
      letI : Field E := hEfld
      haveI : Fintype E := hEfin
      have hEcardE' : Nat.card E = 2 ^ nX := by rw [hEcardE, hKcard]
      obtain ⟨eJZ⟩ := hequiv
      obtain ⟨eT⟩ := heT
      obtain ⟨hΛ0, hlab0⟩ := raLin_split_label (J := J) (Jbar := Jbar) (labX := ⟨.A, rX, nX⟩)
        hn1 hn2 ha0 hEcardE' eJZ eT
      have hbrA : GGHasLabel (⟨.A, a - 1, nX⟩ : LargeEvenLabel)
          (↥J ⧸ Subgroup.center ↥J) := by
        rcases hbr with ⟨-, hha⟩ | ⟨hbad, -⟩
        · simpa [htag] using hha
        · exact absurd (hbad.symm.trans htag) (by simp)
      have hΛa : LargeEvenInLambda2 (⟨.A, a - 1, nX⟩ : LargeEvenLabel) := by
        rcases hbr with ⟨hΛa, -⟩ | ⟨hbad, -⟩
        · simpa [htag] using hΛa
        · exact absurd (hbad.symm.trans htag) (by simp)
      have heq := tara_labelIso_A_A
        (ggLabelRigidInput_holds _ _ _ hΛa hΛ0 hbrA hlab0)
      have haa0 : a = a0 := by
        have := congrArg LargeEvenLabel.rank heq
        simp only at this
        omega
      have hsum_eq : ds.sum = ds.length := tara_sum_eq_length ds hds1
      have hsum0 : ds0.sum = ds0.length := tara_sum_eq_length ds0 hds0one
      omega
    · have hc : ∀ b : K, b ^ p ≠ (u : K) := fun b hb => hsplit ⟨b, hb⟩
      obtain ⟨-, -, hΛns, hlabns⟩ :=
        raLin_nonSplit_case (N := rX + 1) (A := A) (J := J) (labX := ⟨.A, rX, nX⟩)
          hn1 hKcard hloc hp hp2 (Nat.succ_pos rX) hpk hpq hgu hc hAll hcomm hσbar hJbarOpen hequiv
      have hbrA : GGHasLabel (⟨.A, a - 1, nX⟩ : LargeEvenLabel)
          (↥J ⧸ Subgroup.center ↥J) := by
        rcases hbr with ⟨-, hha⟩ | ⟨hbad, -⟩
        · simpa [htag] using hha
        · exact absurd (hbad.symm.trans htag) (by simp)
      have hΛa : LargeEvenInLambda2 (⟨.A, a - 1, nX⟩ : LargeEvenLabel) := by
        rcases hbr with ⟨hΛa, -⟩ | ⟨hbad, -⟩
        · simpa [htag] using hΛa
        · exact absurd (hbad.symm.trans htag) (by simp)
      have heq := tara_labelIso_A_A
        (ggLabelRigidInput_holds _ _ _ hΛa hΛns hbrA hlabns)
      have hnX : nX = p * nX := by
        have := congrArg LargeEvenLabel.n heq
        simpa using this
      have hpos : 0 < nX := by have := hn1; omega
      have hp1 : 1 < p := hp.one_lt
      nlinarith

theorem ggTypeAClRARK_of_rankTwo
    (hB : GGRARankTwo) : GGTypeAClRARK := by
  intro p hp hp2 X _ _ A Ab σ J n hd hk labJ labX hΛJ hΛX hr hhJ hhX
  obtain ⟨⟨hJA, hJ2, hJn, hpJ⟩, hRA⟩ := hr
  rcases labJ with ⟨tJ, rJ, nJ⟩
  rcases labX with ⟨tX, rX, nX⟩
  dsimp only at hJA hJ2 hJn hpJ hRA hΛJ hΛX hhJ hhX
  obtain ⟨⟨hloc, hflat, hcard, hrank, hnum, hself, honly, hmark⟩, hcor⟩ := hd
  obtain ⟨hAb, -, -, -⟩ := hflat
  have hperf : commutator X = ⊤ := by
    have hm0 := hmark
    unfold GGTPNMarked at hm0
    exact hm0.1
  have hrig : GGLabelRigidInput := ggLabelRigidInput_holds
  have hm' : GGTPNMarked p (fun _ lab => lab = (⟨tX, rX, nX⟩ : LargeEvenLabel)) A :=
    ggTPNMarked_eq_of_ggKacRA hrig hp hmark hΛX hRA hhX
  have hcore := split_or_fieldType_of_ggKacRA hp hloc honly hRA hm'
  dsimp only at hcore
  have htagX : tX = .A ∨ tX = .twA := by
    rcases hRA with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  rcases hcore with ⟨a, ds, hsum, hne, hlen, hmem, hbr⟩ | ⟨hge, hcardA, hbr⟩
  ·
    rcases htagX with htA | htT
    ·
      have hdvdX : p ∣ rX + 1 := by
        rcases hRA with ⟨-, hd, -⟩ | ⟨hbad, -⟩
        · exact hd
        · exact absurd (hbad.symm.trans htA) (by simp)
      have hds1 : ∀ x ∈ ds, x = 1 := by
        intro x hx
        rcases hmem x hx with h1 | ⟨hbad, -, -⟩
        · exact h1
        · exact absurd (hbad.symm.trans htA) (by simp)
      have hlen2 : ds.length ≤ 2 :=
        hB p hp hp2 X A σ J (⟨tX, rX, nX⟩ : LargeEvenLabel) hloc honly hk hself hRA htA hm'
          a ds hsum hne hlen hmem hbr
      rcases hbr with ⟨hΛ', hhJ'⟩ | ⟨hbad, -⟩
      · rcases ggLabelIso_typeA_cases hrig hJ2 hΛ' (by simpa [hJA] using hΛJ) hhJ'
          (by simpa [hJA] using hhJ) with heq | ⟨-, hbad2⟩
        · have ha1 : a - 1 = rJ := congrArg LargeEvenLabel.rank heq
          have hnX : nX = nJ := congrArg LargeEvenLabel.n heq
          exact ⟨⟨tJ, rJ, nJ⟩, ⟨tX, rX, nX⟩, hΛJ, hΛX,
            tara_row_split_tagA hJA htA hpJ hJ2 hdvdX hsum hds1 hlen2 hne ha1 hnX, hhJ, hhX⟩
        · exact absurd (congrArg LargeEvenLabel.tag hbad2) (by simp [htA])
      · exact absurd (hbad.symm.trans htA) (by simp)
    ·
      rcases hbr with ⟨hΛ', hhJ'⟩ | ⟨-, ha2, hΛ', hhJ'⟩
      · rcases ggLabelIso_typeA_cases hrig hJ2 hΛ' (by simpa [hJA] using hΛJ) hhJ'
          (by simpa [hJA] using hhJ) with heq | ⟨-, hbad2⟩
        · exact absurd (htT.symm.trans (congrArg LargeEvenLabel.tag heq)) (by simp)
        · exact absurd (htT.symm.trans (congrArg LargeEvenLabel.tag hbad2)) (by simp)
      · rcases ggLabelIso_typeA_cases hrig hJ2 hΛ' (by simpa [hJA] using hΛJ) hhJ'
          (by simpa [hJA] using hhJ) with heq | ⟨-, hbad2⟩
        · have h1 : (1 : ℕ) = rJ := congrArg LargeEvenLabel.rank heq
          omega
        · exact absurd (congrArg LargeEvenLabel.tag hbad2) (by simp)
  ·
    rcases htagX with htA | htT
    ·
      have hpdvd : p ∣ rX + 1 := by
        rcases hRA with ⟨-, hd, -⟩ | ⟨hbad, -⟩
        · exact hd
        · exact absurd (hbad.symm.trans htA) (by simp)
      have hpnX : p ∣ 2 ^ nX - 1 := by
        rcases hRA with ⟨-, -, hd⟩ | ⟨hbad, -⟩
        · exact hd
        · exact absurd (hbad.symm.trans htA) (by simp)
      have hNb : p * ((rX + 1) / p) = rX + 1 := Nat.mul_div_cancel' hpdvd
      rcases hbr with ⟨hAor, hΛ', hhJ'⟩ | ⟨hbadT, -, -, -⟩
      · rcases ggLabelIso_typeA_cases hrig hJ2 hΛ' (by simpa [hJA] using hΛJ) hhJ'
          (by simpa [hJA] using hhJ) with heq | ⟨-, hbad2⟩
        · have hb1 : (rX + 1) / p - 1 = rJ := congrArg LargeEvenLabel.rank heq
          have hb3 : 3 ≤ (rX + 1) / p := by omega
          have hble : (rX + 1) / p ≤ 2 :=
            tara_nonsplit_rank_bound hp hp2 (labX := (⟨tX, rX, nX⟩ : LargeEvenLabel))
              (b := (rX + 1) / p) hperf hAb hrank hΛX htA hpnX hNb hcardA hhX
          omega
        · exact absurd (congrArg LargeEvenLabel.tag hbad2) (by simp)
      · exact absurd (hbadT.symm.trans htA) (by simp)
    ·
      rcases hbr with ⟨hAor, hΛ', hhJ'⟩ | ⟨-, -, hΛ', hhJ'⟩
      · have hb2 : (rX + 1) / p = 2 := by
          rcases hAor with hA | hb2
          · exact absurd (hA.symm.trans htT) (by simp)
          · exact hb2
        have hΛ'' : LargeEvenInLambda2 (⟨.A, 1, p * nX⟩ : LargeEvenLabel) := by
          simpa [hb2] using hΛ'
        have hhJ'' : GGHasLabel (⟨.A, 1, p * nX⟩ : LargeEvenLabel)
            (↥J ⧸ Subgroup.center ↥J) := by
          simpa [hb2] using hhJ'
        rcases ggLabelIso_typeA_cases hrig hJ2 hΛ'' (by simpa [hJA] using hΛJ) hhJ''
          (by simpa [hJA] using hhJ) with heq | ⟨-, hbad2⟩
        · have h1 : (1 : ℕ) = rJ := congrArg LargeEvenLabel.rank heq
          omega
        · exact absurd (congrArg LargeEvenLabel.tag hbad2) (by simp)
      · rcases ggLabelIso_typeA_cases hrig hJ2 hΛ' (by simpa [hJA] using hΛJ) hhJ'
          (by simpa [hJA] using hhJ) with heq | ⟨-, hbad2⟩
        · exact absurd (congrArg LargeEvenLabel.tag heq) (by simp)
        · exact absurd (congrArg LargeEvenLabel.tag hbad2) (by simp)

theorem ggTypeAClRARK_holds :
    GGTypeAClRARK :=
  ggTypeAClRARK_of_rankTwo
    (tara_rankTwo_of_primaryCount tara_primaryCount_of_core)

end CFSG.StandardType

end
