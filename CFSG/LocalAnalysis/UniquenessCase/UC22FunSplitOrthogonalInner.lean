module

public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitTraceInner
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitSmallInner

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Matrix Subgroup CFSG.Open
open CFSG.ClassicalInvolution.Models
open CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.ClassicalInvolution.ModelFacts
open CFSG.LieType.Universal CFSG.LieType.Universal.Spin
open scoped MatrixGroups BigOperators

private theorem trace_mulLeft_fin_two {K : Type*} [Field K]
    (A : Matrix (Fin 2) (Fin 2) K) :
    LinearMap.trace K (Matrix (Fin 2) (Fin 2) K) (LinearMap.mulLeft K A) =
      2 * Matrix.trace A := by
  classical
  let b := Matrix.stdBasis K (Fin 2) (Fin 2)
  rw [LinearMap.trace_eq_matrix_trace K b]
  have hdiag : ∀ i j : Fin 2,
      ((LinearMap.toMatrix b b) (LinearMap.mulLeft K A)) (i, j) (i, j) = A i i := by
    intro i j
    rw [LinearMap.toMatrix_apply]
    have hb : b (i, j) = Matrix.single i j (1 : K) := Matrix.stdBasis_eq_single K i j
    rw [hb, LinearMap.mulLeft_apply]
    have hrepr : (b.repr (A * Matrix.single i j (1 : K))) (i, j) =
        (A * Matrix.single i j (1 : K)) i j := by
      simp [b, Matrix.stdBasis]
    rw [hrepr, Matrix.mul_single_apply_same, mul_one]
  change (∑ ij : Fin 2 × Fin 2,
      ((LinearMap.toMatrix b b) (LinearMap.mulLeft K A)) ij ij) =
    2 * ∑ i : Fin 2, A i i
  rw [Fintype.sum_prod_type]
  simp only [hdiag]
  simp [Finset.sum_const, two_mul]
  ring


private theorem trace_La
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (F : Frame Q) (A : SL(2, K)) :
    LinearMap.trace K V (F.La A : V →ₗ[K] V) =
      2 * (A : Matrix (Fin 2) (Fin 2) K).trace + (Module.finrank K V - 4 : ℕ) := by
  classical
  let f : V →ₗ[K] V := F.La A
  let E : Bool → Submodule K V := fun b => match b with | false => F.span | true => F.perp
  have hint : DirectSum.IsInternal E := by
    rw [DirectSum.isInternal_submodule_iff_isCompl E (i := false) (j := true) (by simp)
      (by ext b; cases b <;> simp)]
    exact F.isCompl_span_perp
  have hf : ∀ b, Set.MapsTo f (E b) (E b) := by
    intro b
    cases b
    · intro x hx
      change x ∈ F.span at hx
      change f x ∈ F.span
      rw [F.mem_span_iff] at hx ⊢
      rw [hx]
      change (F.La A) (F.incl (F.coords x)) =
        F.incl (F.coords ((F.La A) (F.incl (F.coords x))))
      rw [F.La_apply_incl, F.coords_incl]
    · intro x hx
      change x ∈ F.perp at hx
      change f x ∈ F.perp
      rw [F.mem_perp_iff] at hx ⊢
      rw [show f x = x from F.La_apply_of_coords_eq_zero A hx, hx]
  let e : Matrix (Fin 2) (Fin 2) K ≃ₗ[K] F.span :=
    { toFun := fun X => ⟨F.incl X, ⟨X, rfl⟩⟩
      invFun := fun x => F.coords x
      left_inv := fun X => by simp [F.coords_incl]
      right_inv := fun x => by
        apply Subtype.ext
        exact ((F.mem_span_iff).mp x.2).symm
      map_add' := fun X Y => by apply Subtype.ext; simp
      map_smul' := fun c X => by apply Subtype.ext; simp }
  have hspan : f.restrict (fun x hx => hf false hx) =
      e.conj (LinearMap.mulLeft K (A : Matrix (Fin 2) (Fin 2) K)) := by
    refine LinearMap.ext fun x => ?_
    apply Subtype.ext
    rw [LinearMap.restrict_apply, LinearEquiv.conj_apply]
    change (F.La A) (x : V) =
      F.incl ((A : Matrix (Fin 2) (Fin 2) K) * F.coords (x : V))
    rw [show (x : V) = F.incl (F.coords (x : V)) from (F.mem_span_iff).mp x.2,
      F.La_apply_incl, F.coords_incl]
  have hperp : f.restrict (fun x hx => hf true hx) = LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    apply Subtype.ext
    change f x = (x : V)
    exact F.La_apply_of_coords_eq_zero A (F.mem_perp_iff.mp x.2)
  have hspanTrace : (LinearMap.trace K F.span) (f.restrict (fun x hx => hf false hx)) =
      2 * (A : Matrix (Fin 2) (Fin 2) K).trace := by
    rw [hspan, LinearMap.trace_conj']
    exact trace_mulLeft_fin_two (A : Matrix (Fin 2) (Fin 2) K)
  have hdim : Module.finrank K F.perp = Module.finrank K V - 4 := by
    have h := Submodule.finrank_add_eq_of_isCompl F.isCompl_span_perp
    rw [F.finrank_span] at h
    omega
  have hperpTrace : (LinearMap.trace K F.perp) (f.restrict (fun x hx => hf true hx)) =
      (Module.finrank K V - 4 : ℕ) := by
    rw [hperp, LinearMap.trace_id, hdim]
  change LinearMap.trace K V f = _
  rw [LinearMap.trace_eq_sum_trace_restrict hint hf, Fintype.sum_bool]
  rw [hperpTrace, hspanTrace]
  ring

private theorem exists_inner_normalizer_La_of_odd
    {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} (F : Frame Q)
    (hodd : Odd (Nat.card K))
    {h : V ≃ₗ[K] V}
    (hh : h ∈ Subgroup.normalizer (F.La.range : Set (V ≃ₗ[K] V)))
    (hho : Odd (orderOf h)) :
    ∃ x ∈ F.La.range, ∀ y ∈ F.La.range, h * y * h⁻¹ = x * y * x⁻¹ := by
  classical
  let e : SL(2, K) ≃* F.La.range := MonoidHom.ofInjective F.La_injective
  let act : MulAut F.La.range := F.La.range.normalizerMonoidHom ⟨h, hh⟩
  let α : MulAut (SL(2, K)) := e.trans (act.trans e.symm)
  have hact_dvd : orderOf act ∣ orderOf h := by
    have h := orderOf_map_dvd F.La.range.normalizerMonoidHom
      (⟨h, hh⟩ : Subgroup.normalizer (F.La.range : Set (V ≃ₗ[K] V)))
    rw [Subgroup.orderOf_mk] at h
    simpa [act] using h
  have hact_odd : Odd (orderOf act) := Odd.of_dvd_nat hho hact_dvd
  have hα_eq : α = (MulAut.congr e).symm act := (MulAut.congr_symm_apply e act).symm
  have hα_order : orderOf α = orderOf act := by
    rw [hα_eq]
    exact MulEquiv.orderOf_eq ((MulAut.congr e).symm) act
  have hα_odd : Odd (orderOf α) := by
    rw [hα_order]
    exact hact_odd
  have hα_apply : ∀ A : SL(2, K), e (α A) = act (e A) := by
    intro A
    simp [α]
  have hLa_alpha : ∀ A : SL(2, K), F.La (α A) = h * F.La A * h⁻¹ := by
    intro A
    have h := congrArg Subtype.val (hα_apply A)
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h
    have h1 : ((e (α A) : F.La.range) : V ≃ₗ[K] V) = F.La (α A) :=
      MonoidHom.ofInjective_apply F.La_injective
    have h2 : ((e A : F.La.range) : V ≃ₗ[K] V) = F.La A :=
      MonoidHom.ofInjective_apply F.La_injective
    rw [h1, h2] at h
    exact h
  by_cases h3 : 3 < Nat.card K
  · have hα_trace : ∀ A : SL(2, K),
        (α A : Matrix (Fin 2) (Fin 2) K).trace =
          (A : Matrix (Fin 2) (Fin 2) K).trace := by
      intro A
      have htr : LinearMap.trace K V (F.La (α A) : V →ₗ[K] V) =
          LinearMap.trace K V (F.La A : V →ₗ[K] V) := by
        calc
          LinearMap.trace K V (F.La (α A) : V →ₗ[K] V)
              = LinearMap.trace K V ((h * F.La A * h⁻¹ : V ≃ₗ[K] V) :
                  V →ₗ[K] V) := by rw [hLa_alpha A]
          _ = LinearMap.trace K V (F.La A : V →ₗ[K] V) := by
                exact LinearMap.trace_conj' (F.La A : V →ₗ[K] V) h
      have h1 := trace_La F (α A)
      have h2 := trace_La F A
      have hEq : 2 * (α A : Matrix (Fin 2) (Fin 2) K).trace +
            (Module.finrank K V - 4 : ℕ) =
          2 * (A : Matrix (Fin 2) (Fin 2) K).trace +
            (Module.finrank K V - 4 : ℕ) := by
        rw [← h1, ← h2]
        exact htr
      have h2K : (2 : K) ≠ 0 :=
        CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
      exact mul_left_cancel₀ h2K (add_right_cancel hEq)
    obtain ⟨r, hr⟩ :=
      mem_range_conj_of_odd_of_trace hodd h3 α hα_odd hα_trace
    refine ⟨F.La r, ⟨r, rfl⟩, ?_⟩
    rintro _ ⟨A, rfl⟩
    calc
      h * F.La A * h⁻¹ = F.La (α A) := (hLa_alpha A).symm
      _ = F.La ((MulAut.conj r) A) := by rw [hr]
      _ = F.La r * F.La A * (F.La r)⁻¹ := by
            simp only [MulAut.conj_apply, map_mul, map_inv]
  · have hcard3 : Nat.card K = 3 := by
      have h1 : 1 < Nat.card K := Finite.one_lt_card
      obtain ⟨k, hk⟩ := hodd
      omega
    obtain ⟨r, hr⟩ := mem_range_conj_of_odd_of_card_three hcard3 α hα_odd
    refine ⟨F.La r, ⟨r, rfl⟩, ?_⟩
    rintro _ ⟨A, rfl⟩
    calc
      h * F.La A * h⁻¹ = F.La (α A) := (hLa_alpha A).symm
      _ = F.La ((MulAut.conj r) A) := by rw [hr]
      _ = F.La r * F.La A * (F.La r)⁻¹ := by
            simp only [MulAut.conj_apply, map_mul, map_inv]


private theorem spinAction_injective_on_longSL2_range
    {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {m : ℕ} (F : HypFrame Q m)
    {i j : Fin m} (hij : i ≠ j) (s t : Bool) :
    ∀ a ∈ (F.longSL2 hij s t).range, ∀ b ∈ (F.longSL2 hij s t).range,
      spinAction Q a = spinAction Q b → a = b := by
  intro a ha b hb hab
  obtain ⟨A, rfl⟩ := ha
  obtain ⟨B, rfl⟩ := hb
  have hA : spinAction Q (F.longSL2 hij s t A) = (F.toFrame hij s t).La A :=
    DFunLike.congr_fun (spinAction_comp_longSL2 F hij s t) A
  have hB : spinAction Q (F.longSL2 hij s t B) = (F.toFrame hij s t).La B :=
    DFunLike.congr_fun (spinAction_comp_longSL2 F hij s t) B
  have hEq : (F.toFrame hij s t).La A = (F.toFrame hij s t).La B := by
    rw [← hA, ← hB]
    exact hab
  exact congrArg (F.longSL2 hij s t) ((F.toFrame hij s t).La_injective hEq)

private theorem exists_inner_normalizer_longSL2_of_frame
    {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} {m : ℕ} (F : HypFrame Q m)
    {i j : Fin m} (hij : i ≠ j) (s t : Bool) (hodd : Odd (Nat.card K))
    {g : spinGroup Q}
    (hg : g ∈ Subgroup.normalizer ((F.longSL2 hij s t).range : Set (spinGroup Q)))
    (hgo : Odd (orderOf g)) :
    ∃ r ∈ (F.longSL2 hij s t).range,
      ∀ x ∈ (F.longSL2 hij s t).range, g * x * g⁻¹ = r * x * r⁻¹ := by
  classical
  let fr := F.toFrame hij s t
  let ψ := F.longSL2 hij s t
  have hgN : spinAction Q g ∈ Subgroup.normalizer (fr.La.range : Set (V ≃ₗ[K] V)) := by
    have h := CFSG.ClassicalInvolution.Models.Transfer.map_mem_normalizer (spinAction Q) hg
    rwa [map_longSL2_range] at h
  have hgoN : Odd (orderOf (spinAction Q g)) :=
    Odd.of_dvd_nat hgo (orderOf_map_dvd (spinAction Q) g)
  obtain ⟨x, hx, hconj⟩ := exists_inner_normalizer_La_of_odd fr hodd hgN hgoN
  rcases hx with ⟨A, hA⟩
  subst x
  refine ⟨ψ A, ⟨A, rfl⟩, ?_⟩
  intro y hy
  rcases hy with ⟨B, rfl⟩
  have hleft : g * ψ B * g⁻¹ ∈ ψ.range := by
    rw [Subgroup.mem_normalizer_iff] at hg
    exact (hg (ψ B)).mp ⟨B, rfl⟩
  have hright : ψ A * ψ B * (ψ A)⁻¹ ∈ ψ.range :=
    ψ.range.mul_mem (ψ.range.mul_mem ⟨A, rfl⟩ ⟨B, rfl⟩) (ψ.range.inv_mem ⟨A, rfl⟩)
  refine spinAction_injective_on_longSL2_range F hij s t
    (g * ψ B * g⁻¹) hleft (ψ A * ψ B * (ψ A)⁻¹) hright ?_
  have hAt : spinAction Q (ψ A) = fr.La A := DFunLike.congr_fun (spinAction_comp_longSL2 F hij s t) A
  have hBt : spinAction Q (ψ B) = fr.La B := DFunLike.congr_fun (spinAction_comp_longSL2 F hij s t) B
  have hc := hconj (fr.La B) ⟨B, rfl⟩
  simp only [map_mul, map_inv]
  rw [hAt, hBt]
  exact hc


private theorem mem_normalizer_conj_iff
    {G : Type*} [Group G] {P : Subgroup G} {g c : G} :
    g ∈ Subgroup.normalizer (P.map (MulAut.conj c).toMonoidHom : Set G) ↔
      c⁻¹ * g * c ∈ Subgroup.normalizer (P : Set G) := by
  constructor
  · intro hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change CFSG.ClassicalInvolution.Generic.conjSub (c⁻¹ * g * c) P = P
    have h : CFSG.ClassicalInvolution.Generic.conjSub g
        (CFSG.ClassicalInvolution.Generic.conjSub c P) =
        CFSG.ClassicalInvolution.Generic.conjSub c P := by
      simpa [CFSG.ClassicalInvolution.Generic.conjSub] using
        (Subgroup.mem_normalizer_iff_map_conj_eq.mp hg)
    rw [CFSG.ClassicalInvolution.Generic.conjSub_mul,
      CFSG.ClassicalInvolution.Generic.conjSub_mul, h,
      CFSG.ClassicalInvolution.Generic.conjSub_inv_conjSub]
  · intro hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hg ⊢
    have h1 : CFSG.ClassicalInvolution.Generic.conjSub c
        (CFSG.ClassicalInvolution.Generic.conjSub (c⁻¹ * g * c) P) =
        CFSG.ClassicalInvolution.Generic.conjSub c P := by
      simpa [CFSG.ClassicalInvolution.Generic.conjSub] using
        congrArg (CFSG.ClassicalInvolution.Generic.conjSub c) hg
    rwa [CFSG.ClassicalInvolution.Generic.conjSub_mul,
      CFSG.ClassicalInvolution.Generic.conjSub_mul,
      CFSG.ClassicalInvolution.Generic.conjSub_conjSub_inv] at h1

private theorem exists_inner_conj_range
    {G : Type*} [Group G] {P : Subgroup G} {g c : G}
    (h : ∃ r ∈ P, ∀ x ∈ P,
      (c⁻¹ * g * c) * x * (c⁻¹ * g * c)⁻¹ = r * x * r⁻¹) :
    ∃ r ∈ P.map (MulAut.conj c).toMonoidHom,
      ∀ x ∈ P.map (MulAut.conj c).toMonoidHom,
        g * x * g⁻¹ = r * x * r⁻¹ := by
  obtain ⟨r, hr, hconj⟩ := h
  refine ⟨c * r * c⁻¹, ⟨r, hr, rfl⟩, ?_⟩
  intro x hx
  rcases hx with ⟨y, hy, rfl⟩
  calc
    g * (c * y * c⁻¹) * g⁻¹ =
        c * ((c⁻¹ * g * c) * y * (c⁻¹ * g * c)⁻¹) * c⁻¹ := by group
    _ = c * (r * y * r⁻¹) * c⁻¹ := by rw [hconj y hy]
    _ = (c * r * c⁻¹) * (c * y * c⁻¹) * (c * r * c⁻¹)⁻¹ := by group

private theorem orthogonal_inner_of_standard
    {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} {m : ℕ} {t : StatedLieTag}
    {D : CFSG.LieType.Universal.UniversalRootDatum (spinGroup Q)} {F : HypFrame Q m}
    {i j : Fin m} (hij : i ≠ j) (s t' : Bool) (γ : Fin D.rank → ℤ)
    (hodd : Odd (Nat.card K))
    (hR0mem : (D.rootGroup γ ⊔ D.rootGroup (-γ)) ∈ fundamentalSubgroups t D)
    (hR0eq : (D.rootGroup γ ⊔ D.rootGroup (-γ)) = (F.longSL2 hij s t').range)
    (hsingle : FundamentalSingleClass t D)
    {R : Subgroup (spinGroup Q)} (hR : R ∈ fundamentalSubgroups t D)
    {g : spinGroup Q} (hg : g ∈ Subgroup.normalizer (R : Set (spinGroup Q)))
    (hgo : Odd (orderOf g)) :
    ∃ r ∈ R, ∀ x ∈ R, g * x * g⁻¹ = r * x * r⁻¹ := by
  classical
  let P : Subgroup (spinGroup Q) := (F.longSL2 hij s t').range
  let R0 : Subgroup (spinGroup Q) := D.rootGroup γ ⊔ D.rootGroup (-γ)
  have hR0eq' : R0 = P := hR0eq
  obtain ⟨c, hc⟩ := hsingle R0 hR0mem R hR
  have hg0 : g ∈ Subgroup.normalizer
      (P.map (MulAut.conj c).toMonoidHom : Set (spinGroup Q)) := by
    rw [hc] at hg
    simpa [R0, hR0eq'] using hg
  have hg' : c⁻¹ * g * c ∈ Subgroup.normalizer (P : Set (spinGroup Q)) :=
    (mem_normalizer_conj_iff.mp hg0)
  have hgo' : Odd (orderOf (c⁻¹ * g * c)) := by
    have h : orderOf (c⁻¹ * g * c) = orderOf g := by
      rw [show c⁻¹ * g * c = (MulAut.conj c⁻¹) g by simp]
      exact MulEquiv.orderOf_eq (MulAut.conj c⁻¹) g
    rwa [h]
  obtain ⟨r0, hr0, hconj⟩ :=
    exists_inner_normalizer_longSL2_of_frame F hij s t' hodd hg' hgo'
  have hinner : ∃ r ∈ P.map (MulAut.conj c).toMonoidHom,
      ∀ x ∈ P.map (MulAut.conj c).toMonoidHom,
        g * x * g⁻¹ = r * x * r⁻¹ :=
    exists_inner_conj_range ⟨r0, hr0, hconj⟩
  simpa [R0, hR0eq', hc] using hinner



private theorem orthogonal_odd_inner
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {n e : ℕ}
    (hadm : StatedLieAdmissible .POmegaOdd n p e)
    (R : Subgroup (spinGroup (quadOdd n (GaloisField p e))))
    (hR : R ∈ fundamentalSubgroups .POmegaOdd
      (CFSG.ClassicalInvolution.ModelFacts.modelUniv .POmegaOdd n p e Fact.out).D)
    (g : spinGroup (quadOdd n (GaloisField p e)))
    (hg : g ∈ Subgroup.normalizer (R : Set (spinGroup (quadOdd n (GaloisField p e)))))
    (hgo : Odd (orderOf g)) :
    ∃ r ∈ R, ∀ x ∈ R, g * x * g⁻¹ = r * x * r⁻¹ := by
  classical
  let K := GaloisField p e
  let Q := quadOdd n K
  have hn3 : 3 ≤ n := hadm.2.2.1
  have hodd : Odd (Nat.card K) := by
    rw [GaloisField.card p e (by have := hadm.2.1; omega)]
    exact ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  let k0 : Fin n := ⟨0, by omega⟩
  let j0 : Fin n := ⟨1, by omega⟩
  have hij : k0 ≠ j0 := Fin.ne_of_val_ne (by simp [k0, j0])
  let F : HypFrame Q n := (oddFrame n K).toHypFrame
  let D0 : CFSG.LieType.Universal.UniversalRootDatum (spinGroup Q) :=
    (CFSG.ClassicalInvolution.ModelFacts.modelUniv .POmegaOdd n p e Fact.out).D
  have hlong : IsLongestRoot D0 (Pi.single k0 1) := by
    change IsLongestRoot (oddDatum n K) (Pi.single k0 1)
    exact isLongestRoot_single .POmegaOdd n p e Fact.out trivial hadm k0
      (by show 0 + 1 < n; omega)
  have hR0mem : (D0.rootGroup (Pi.single k0 1) ⊔
      D0.rootGroup (-Pi.single k0 1)) ∈ fundamentalSubgroups .POmegaOdd D0 := by
    refine ⟨1, Pi.single k0 1, Or.inl hlong, ?_⟩
    exact (CFSG.ClassicalInvolution.ModelFacts.map_conj_one _).symm
  have hR0eq : (D0.rootGroup (Pi.single k0 1) ⊔
      D0.rootGroup (-Pi.single k0 1)) = (F.longSL2 hij true false).range := by
    have h := CFSG.LieType.Universal.Spin.OddCT.rankOne_le_range (K := K) (n := n) k0
    have h' : CFSG.LieType.CurtisTits.rankOne (oddRootGroup n K) k0 =
        (rankOneB K k0).range :=
      le_antisymm h (by
        rintro _ ⟨M, rfl⟩
        exact CFSG.LieType.Universal.Spin.OddCT.rankOneB_mem_rankOne k0 M)
    rw [CFSG.LieType.Universal.Spin.rankOneB_of_lt K (k := k0)
      (by show 0 + 1 < n; omega) (j := j0) rfl hij] at h'
    change (D0.rootGroup (Pi.single k0 1) ⊔
      D0.rootGroup (-Pi.single k0 1)) = (F.longSL2 hij true false).range
    exact h'
  have hsingle := fundamentalSingleClass .POmegaOdd n p e Fact.out trivial hadm
    (by decide) (by decide)
  exact orthogonal_inner_of_standard (D := D0) (g := g) hij true false (Pi.single k0 1) hodd
    hR0mem hR0eq hsingle hR hg hgo

private theorem orthogonal_plus_inner
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {n e : ℕ}
    (hadm : StatedLieAdmissible .POmegaPlus n p e)
    (R : Subgroup (spinGroup (quadPlus n (GaloisField p e))))
    (hR : R ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum n (GaloisField p e) (by have := hadm.2.2; omega)))
    (g : spinGroup (quadPlus n (GaloisField p e)))
    (hg : g ∈ Subgroup.normalizer (R : Set (spinGroup (quadPlus n (GaloisField p e)))))
    (hgo : Odd (orderOf g)) :
    ∃ r ∈ R, ∀ x ∈ R, g * x * g⁻¹ = r * x * r⁻¹ := by
  classical
  let K := GaloisField p e
  let Q := quadPlus n K
  have hn3 : 3 ≤ n := by have := hadm.2.2; omega
  have hodd : Odd (Nat.card K) := by
    rw [GaloisField.card p e (by have := hadm.2.1; omega)]
    exact ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  let k0 : Fin n := ⟨0, by omega⟩
  have hij : rootIdxD n k0 ≠ rootIdxD' n k0 := rootIdxD_ne n (by omega) k0
  let F : HypFrame Q n := plusFrame n K hn3
  let D0 : CFSG.LieType.Universal.UniversalRootDatum (spinGroup Q) := plusDatum n K hn3
  have hlong : IsLongestRoot D0 (Pi.single k0 1) :=
    isLongest_single_cartanD hn3 rfl (plusDatum n K hn3).isFiniteType k0
  have hR0mem : (D0.rootGroup (Pi.single k0 1) ⊔
      D0.rootGroup (-Pi.single k0 1)) ∈ fundamentalSubgroups .POmegaPlus D0 := by
    refine ⟨1, Pi.single k0 1, Or.inl hlong, ?_⟩
    exact (CFSG.ClassicalInvolution.ModelFacts.map_conj_one _).symm
  have hR0eq : (D0.rootGroup (Pi.single k0 1) ⊔
      D0.rootGroup (-Pi.single k0 1)) =
        (F.longSL2 hij true (rootSignD n k0)).range := by
    have h := CFSG.LieType.Universal.Spin.PlusCT.rankOne_plusRootGroup (K := K) (n := n)
      hn3 k0
    change (D0.rootGroup (Pi.single k0 1) ⊔
      D0.rootGroup (-Pi.single k0 1)) =
        (F.longSL2 hij true (rootSignD n k0)).range
    exact h
  have hsingle := fundamentalSingleClass .POmegaPlus n p e Fact.out trivial hadm
    (by decide) (by decide)
  have hsingle' : FundamentalSingleClass .POmegaPlus D0 := by
    rw [show (CFSG.ClassicalInvolution.ModelFacts.modelUniv .POmegaPlus n p e Fact.out) =
        ⟨spinGroup (quadPlus n K), plusDatum n K hn3⟩ from
        CFSG.ClassicalInvolution.ModelFacts.modelUniv_POmegaPlus (n := n) (p := p) (f := e) hn3]
      at hsingle
    exact hsingle
  exact orthogonal_inner_of_standard (Q := Q) (D := D0) (g := g) hij true
    (rootSignD n k0) (Pi.single k0 1) hodd hR0mem hR0eq hsingle' hR hg hgo

private theorem orthogonal_minus_inner
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {n e : ℕ}
    (hadm : StatedLieAdmissible .POmegaMinus n p e)
    (R : Subgroup (spinGroup (quadMinus n (GaloisField p e)
      (minusCoeffs p e).1 (minusCoeffs p e).2)))
    (hR : R ∈ fundamentalSubgroups .POmegaMinus
      (CFSG.ClassicalInvolution.ModelFacts.modelUniv .POmegaMinus n p e Fact.out).D)
    (g : spinGroup (quadMinus n (GaloisField p e)
      (minusCoeffs p e).1 (minusCoeffs p e).2))
    (hg : g ∈ Subgroup.normalizer (R : Set (spinGroup (quadMinus n (GaloisField p e)
      (minusCoeffs p e).1 (minusCoeffs p e).2))))
    (hgo : Odd (orderOf g)) :
    ∃ r ∈ R, ∀ x ∈ R, g * x * g⁻¹ = r * x * r⁻¹ := by
  classical
  let K := GaloisField p e
  let b := (minusCoeffs p e).1
  let c := (minusCoeffs p e).2
  let Q := quadMinus n K b c
  have hn4 : 4 ≤ n := hadm.2.2
  have hodd : Odd (Nat.card K) := by
    rw [GaloisField.card p e (by have := hadm.2.1; omega)]
    exact ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  let k0 : Fin (n - 1) := ⟨0, by omega⟩
  have hk : k0.val + 1 < n - 1 := by show 0 + 1 < n - 1; omega
  have hij := Twisted.succ_ne_of_lt n (k := k0) hk
  let F : HypFrame Q (n - 1) := (Twisted.minusFrame n b c).toHypFrame
  let D0 : CFSG.LieType.Universal.UniversalRootDatum (spinGroup Q) :=
    (CFSG.ClassicalInvolution.ModelFacts.modelUniv .POmegaMinus n p e Fact.out).D
  have hlong : IsLongestRoot D0 (Pi.single k0 1) :=
    isLongestRoot_single .POmegaMinus n p e Fact.out trivial hadm k0
      (by show 0 + 2 < n; omega)
  have hR0mem : (D0.rootGroup (Pi.single k0 1) ⊔
      D0.rootGroup (-Pi.single k0 1)) ∈ fundamentalSubgroups .POmegaMinus D0 := by
    refine ⟨1, Pi.single k0 1, Or.inl hlong, ?_⟩
    exact (CFSG.ClassicalInvolution.ModelFacts.map_conj_one _).symm
  have hR0eq : (D0.rootGroup (Pi.single k0 1) ⊔
      D0.rootGroup (-Pi.single k0 1)) =
        (F.longSL2 hij true false).range := by
    have h := Twisted.rankOne_minusRootGroup_of_lt (n := n) (b := b) (c := c)
      (minusCoeffs_irr p e) (k := k0) hk
    change (D0.rootGroup (Pi.single k0 1) ⊔
      D0.rootGroup (-Pi.single k0 1)) = (F.longSL2 hij true false).range at h ⊢
    exact h
  have hsingle := fundamentalSingleClass .POmegaMinus n p e Fact.out trivial hadm
    (by decide) (by decide)
  exact orthogonal_inner_of_standard (Q := Q) (D := D0) (g := g) hij true false
    (Pi.single k0 1) hodd hR0mem hR0eq hsingle hR hg hgo

theorem odd_normalizer_inner_fundamental_orthogonal_model
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {t : StatedLieTag} (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus)
    {n e : ℕ} (hadm : StatedLieAdmissible t n p e)
    (R : Subgroup (modelUniv t n p e Fact.out).K)
    (hR : R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D)
    (g : (modelUniv t n p e Fact.out).K)
    (hg : g ∈ Subgroup.normalizer (R : Set (modelUniv t n p e Fact.out).K))
    (hgo : Odd (orderOf g)) :
    ∃ r ∈ R, ∀ x ∈ R, g * x * g⁻¹ = r * x * r⁻¹ := by
  rcases ht with rfl | rfl | rfl
  · exact orthogonal_odd_inner hp2 hadm R hR g hg hgo
  · have hn3 : 3 ≤ n := by have := hadm.2.2; omega
    let M₂ : CFSG.LieType.Universal.LieUniversal :=
      ⟨spinGroup (quadPlus n (GaloisField p e)), plusDatum n (GaloisField p e) hn3⟩
    let P : (M : CFSG.LieType.Universal.LieUniversal) → Prop := fun M =>
      ∀ (R : Subgroup M.K) (hR : R ∈ fundamentalSubgroups .POmegaPlus M.D)
        (g : M.K) (hg : g ∈ Subgroup.normalizer (R : Set M.K))
        (hgo : Odd (orderOf g)),
        ∃ r ∈ R, ∀ x ∈ R, g * x * g⁻¹ = r * x * r⁻¹
    have hplusP : P M₂ := by
      intro R hR g hg hgo
      exact orthogonal_plus_inner hp2 hadm R hR g hg hgo
    have hM : CFSG.ClassicalInvolution.ModelFacts.modelUniv .POmegaPlus n p e Fact.out = M₂ :=
      CFSG.ClassicalInvolution.ModelFacts.modelUniv_POmegaPlus (n := n) (p := p) (f := e) hn3
    have hP : P (CFSG.ClassicalInvolution.ModelFacts.modelUniv .POmegaPlus n p e Fact.out) :=
      hM ▸ hplusP
    exact hP R hR g hg hgo
  · exact orthogonal_minus_inner hp2 hadm R hR g hg hgo


end CFSG.LocalAnalysis.UniquenessCase.UC22
