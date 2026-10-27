module

public import CFSG.Quasithin.Vol2.Ch8Sec2L827XLBCaseAGK
public import CFSG.Quasithin.Vol2.Ch8Sec2L827XLBCoreB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.L827X.LBCaseBG

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13.L827X.LBDefs
  CFSG.Quasithin.H13.L827X.LBGroupAbs CFSG.Quasithin.H13.L827X.LBCaseAGBase
  CFSG.Quasithin.H13.L827X.LBCaseAGK
open scoped commutatorElement

variable {G : Type} [Group G]

private theorem bg_actN_pow_eq_one {X H : Subgroup G} [Finite G] {p : ℕ} [Fact p.Prime]
    (hHN : H ≤ Subgroup.normalizer (X : Set G))
    (hS : IsXiShape p ((pCoreOf 2 X).subgroupOf X)) (s : ↥H)
    (hα : ∀ x : ↥X, conjXEquiv X (hHN s.2) x * x⁻¹ ∈ Yof ((pCoreOf 2 X).subgroupOf X)) :
    (actHom hHN ((pCoreOf 2 X).subgroupOf X) (N_map_conj X) s) ^ p = 1 := by
  have hgN : (s : G) ∈ Subgroup.normalizer (X : Set G) := hHN s.2
  have hαN : ∀ x : ↥X, conjXEquiv X hgN x ∈ (pCoreOf 2 X).subgroupOf X ↔
      x ∈ (pCoreOf 2 X).subgroupOf X := fun x => N_conj_iff X hgN x
  have hf : ∀ y : ↥X, (actHom hHN ((pCoreOf 2 X).subgroupOf X) (N_map_conj X) s)
      (y : ↥X ⧸ (pCoreOf 2 X).subgroupOf X)
      = ((conjXEquiv X hgN y : ↥X) : ↥X ⧸ (pCoreOf 2 X).subgroupOf X) :=
    fun y => actQuot_mk _ (hHN s.2) (N_map_conj X _ (hHN s.2)) y
  apply MulEquiv.ext
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  rw [MulAut.one_apply, pow_apply_mk_of_apply _ hgN _ hf p x]
  have key := pow_fix_mod hS (α := conjXEquiv X hgN) hαN hα x
  exact (quot_eq_iff_mul_inv_mem _).mpr key

private theorem bg_solvable_of_fixXiY {X H : Subgroup G} [Finite G] {p : ℕ} [Fact p.Prime]
    (hHN : H ≤ Subgroup.normalizer (X : Set G))
    (hS : IsXiShape p ((pCoreOf 2 X).subgroupOf X))
    (hK5 : ∀ K' : Subgroup G, K' ≤ H → ⁅K', X⁆ ≤ pCoreOf 2 X → Group.IsSolvable ↥K')
    (hall : ∀ s : ↥H, ∀ x : ↥X,
      conjXEquiv X (hHN s.2) x * x⁻¹ ∈ Yof ((pCoreOf 2 X).subgroupOf X)) :
    Group.IsSolvable ↥H := by
  classical
  let actN := actHom hHN ((pCoreOf 2 X).subgroupOf X) (N_map_conj X)
  haveI : Finite (MulAut (↥X ⧸ (pCoreOf 2 X).subgroupOf X)) :=
    Finite.of_injective (fun f : MulAut (↥X ⧸ (pCoreOf 2 X).subgroupOf X) =>
      (f : (↥X ⧸ (pCoreOf 2 X).subgroupOf X) → (↥X ⧸ (pCoreOf 2 X).subgroupOf X)))
      (fun f g h => MulEquiv.ext (fun x => congrFun h x))
  have hRP : IsPGroup p ↥actN.range := by
    show ∀ g : ↥actN.range, ∃ k : ℕ, g ^ p ^ k = 1
    intro g
    obtain ⟨s, hs⟩ := MonoidHom.mem_range.mp g.2
    refine ⟨1, ?_⟩
    rw [pow_one]
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, ← hs]
    exact bg_actN_pow_eq_one hHN hS s (hall s)
  haveI : Group.IsNilpotent ↥actN.range := IsPGroup.isNilpotent hRP
  haveI : Group.IsSolvable ↥actN.range := inferInstance
  have hKer : Group.IsSolvable ↥actN.ker := by
    have hK'H : actN.ker.map H.subtype ≤ H := Subgroup.map_subtype_le _
    have hcomm : ⁅actN.ker.map H.subtype, X⁆ ≤ pCoreOf 2 X := by
      rw [Subgroup.commutator_le]
      intro k hk x hx
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hk
      have hs1 : actN s = 1 := hs
      have h1 : ((conjXEquiv X (hHN s.2) ⟨x, hx⟩ : ↥X) : ↥X ⧸ (pCoreOf 2 X).subgroupOf X) =
          ((⟨x, hx⟩ : ↥X) : ↥X ⧸ (pCoreOf 2 X).subgroupOf X) := by
        have h2 := congrArg (fun f : MulAut (↥X ⧸ (pCoreOf 2 X).subgroupOf X) =>
          f ((⟨x, hx⟩ : ↥X) : ↥X ⧸ (pCoreOf 2 X).subgroupOf X)) hs1
        rw [MulAut.one_apply] at h2
        exact h2
      have h3 := (quot_eq_iff_mul_inv_mem _).mp h1
      rw [Subgroup.mem_subgroupOf] at h3
      have h4 : ((conjXEquiv X (hHN s.2) ⟨x, hx⟩ * (⟨x, hx⟩ : ↥X)⁻¹ : ↥X) : G) =
          (s : G) * x * (s : G)⁻¹ * x⁻¹ := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, conjXEquiv_coe]
      rw [h4] at h3
      show ⁅(s : G), x⁆ ∈ pCoreOf 2 X
      rw [commutatorElement_def]
      exact h3
    have hK' : Group.IsSolvable ↥(actN.ker.map H.subtype) := hK5 _ hK'H hcomm
    haveI := hK'
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.equivMapOfInjective actN.ker H.subtype H.subtype_injective).toMonoidHom)
      (Subgroup.equivMapOfInjective actN.ker H.subtype H.subtype_injective).injective
  have hmap : actN.rangeRestrict.ker ≤ actN.ker.subtype.range := by
    rw [MonoidHom.ker_rangeRestrict, Subgroup.range_subtype]
  exact Group.isSolvable_of_ker_le_range actN.ker.subtype actN.rangeRestrict hmap

private theorem bg_index_Yof {X : Subgroup G} {p : ℕ} [Fact p.Prime] {E : Type}
    [AddCommGroup E] [Module (ZMod p) E] [Finite E] (hE : Module.finrank (ZMod p) E = 2)
    (q : X → E) (hq_add : ∀ x y : X, q (x * y) = q x + q y) (hq_surj : Function.Surjective q)
    (hq_ker : ∀ x y : X, q x = q y ↔ (x : G)⁻¹ * (y : G) ∈ XiY X) :
    (Yof ((pCoreOf 2 X).subgroupOf X)).index = p ^ 2 := by
  have hq1 : q 1 = 0 := by
    have h := hq_add 1 1
    rw [mul_one] at h
    simpa using h
  let ψ : ↥X →* Multiplicative E :=
    { toFun := fun x => Multiplicative.ofAdd (q x)
      map_one' := by
        show Multiplicative.ofAdd (q 1) = 1
        rw [hq1]
        rfl
      map_mul' := fun x y => by
        show Multiplicative.ofAdd (q (x * y)) = Multiplicative.ofAdd (q x) * Multiplicative.ofAdd (q y)
        rw [hq_add]
        rfl }
  have hker : ψ.ker = Yof ((pCoreOf 2 X).subgroupOf X) := by
    ext x
    rw [MonoidHom.mem_ker, mem_Yof_iff]
    show Multiplicative.ofAdd (q x) = 1 ↔ _
    rw [ofAdd_eq_one]
    have h := hq_ker x 1
    rw [hq1] at h
    rw [h]
    simp
  have hsurj : Function.Surjective ψ := fun e => by
    obtain ⟨x, hx⟩ := hq_surj (Multiplicative.toAdd e)
    exact ⟨x, by show Multiplicative.ofAdd (q x) = e; rw [hx]; rfl⟩
  haveI : Module.Finite (ZMod p) E := (Module.finite_iff_finite (R := ZMod p)).mpr inferInstance
  rw [← hker, Subgroup.index_ker, ψ.range_eq_top_of_surjective hsurj, Subgroup.card_top]
  show Nat.card E = p ^ 2
  rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := E), Nat.card_zmod, hE]

theorem not_solvable_range_K {G : Type} [Group G] [Finite G] {T X K U V X₁ W₀ W₁ : Subgroup G}
    {v : G}
    (h : CFSG.Quasithin.H13.L827X.LBDefs.XiHyp T X K U V X₁ W₀ W₁ v) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2)
    {E : Type} [AddCommGroup E] [Module (ZMod p) E] [Finite E]
    (hE : Module.finrank (ZMod p) E = 2)
    (q : X → E) (hq_add : ∀ x y : X, q (x * y) = q x + q y) (hq_surj : Function.Surjective q)
    (hq_ker : ∀ x y : X, q x = q y ↔ (x : G)⁻¹ * (y : G) ∈ CFSG.Quasithin.H13.L827X.LBDefs.XiY X)
    (φ : K →* (E ≃ₗ[ZMod p] E))
    (hφ : ∀ (k : K) (x x' : X), (x' : G) = (k : G) * (x : G) * (k : G)⁻¹ → φ k (q x) = q x') :
    ¬ Group.IsSolvable φ.range := by
  intro hR
  obtain ⟨-, hXi, -, hK, hXK, hNK, hKs, -⟩ := h
  obtain ⟨-, -, -, p', hp', -, -, hidx, -⟩ := hXi
  obtain ⟨hKne, hKperf, -⟩ := hK
  have hKN : K ≤ Subgroup.normalizer (X : Set G) := Subgroup.le_normalizer.trans hNK
  have hNY : (pCoreOf 2 X).subgroupOf X ≤ Yof ((pCoreOf 2 X).subgroupOf X) := by
    unfold Yof
    exact le_sup_right
  have hYidx : (Yof ((pCoreOf 2 X).subgroupOf X)).index = p ^ 2 :=
    bg_index_Yof hE q hq_add hq_surj hq_ker
  have hpdvd : p ∣ (pCoreOf 2 X).relIndex X := by
    have h1 := Subgroup.index_dvd_of_le hNY
    rw [hYidx] at h1
    exact dvd_trans (dvd_pow_self p two_ne_zero) h1
  have hpp : p = p' := by
    have hpd : p ∣ p' := by
      rcases hidx with h2 | ⟨h3, -⟩
      · rw [h2] at hpdvd
        exact Nat.Prime.dvd_of_dvd_pow (Fact.out : p.Prime) hpdvd
      · rw [h3] at hpdvd
        exact Nat.Prime.dvd_of_dvd_pow (Fact.out : p.Prime) hpdvd
    exact (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) hp').mp hpd
  rw [← hpp] at hidx
  have hS : IsXiShape p ((pCoreOf 2 X).subgroupOf X) := by
    unfold IsXiShape
    rcases hidx with h2 | ⟨h3, hnc⟩
    · exact Or.inl h2
    · exact Or.inr ⟨h3, fun hh => hnc ((commutator_top_le_subgroupOf_iff X).mp hh)⟩
  have hCgK : (φ.ker).map K.subtype ≤ K := Subgroup.map_subtype_le _
  have hCgN : (φ.ker).map K.subtype ≤ Subgroup.normalizer (X : Set G) := hCgK.trans hKN
  have hK5 : ∀ K' : Subgroup G, K' ≤ (φ.ker).map K.subtype →
      ⁅K', X⁆ ≤ pCoreOf 2 X → Group.IsSolvable ↥K' :=
    fun K' h1 h2 => hKs K' (h1.trans hCgK) h2
  have hall : ∀ s : ↥((φ.ker).map K.subtype), ∀ x : ↥X,
      conjXEquiv X (hCgN s.2) x * x⁻¹ ∈ Yof ((pCoreOf 2 X).subgroupOf X) := by
    rintro ⟨s, hs⟩ x
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hs
    have hφk : φ k = 1 := hk
    have hkN : (k : G) ∈ Subgroup.normalizer (X : Set G) := hKN k.2
    have hq' : q x = q (conjXEquiv X hkN x) := by
      have h := hφ k x (conjXEquiv X hkN x) (conjXEquiv_coe X hkN x)
      rw [hφk] at h
      exact h
    have hmem := (hq_ker x (conjXEquiv X hkN x)).mp hq'
    have hconj := conj_mem_XiY (Subgroup.le_normalizer x.2) hmem
    have e : (x : G) * ((x : G)⁻¹ * ((conjXEquiv X hkN x : ↥X) : G)) * (x : G)⁻¹
        = ((conjXEquiv X hkN x : ↥X) : G) * (x : G)⁻¹ := by
      group
    rw [e] at hconj
    rw [mem_Yof_iff, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hconj
  have hCgSolv : Group.IsSolvable ↥((φ.ker).map K.subtype) :=
    bg_solvable_of_fixXiY hCgN hS hK5 hall
  have hkerSolv : Group.IsSolvable ↥(φ.ker) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.equivMapOfInjective φ.ker K.subtype K.subtype_injective).toMonoidHom)
      (Subgroup.equivMapOfInjective φ.ker K.subtype K.subtype_injective).injective
  have hmap : φ.rangeRestrict.ker ≤ φ.ker.subtype.range := by
    rw [MonoidHom.ker_rangeRestrict, Subgroup.range_subtype]
  have hKsolv : Group.IsSolvable ↥K :=
    Group.isSolvable_of_ker_le_range φ.ker.subtype φ.rangeRestrict hmap
  haveI : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hKperf
  haveI : Nontrivial ↥K := (Subgroup.nontrivial_iff_ne_bot K).mpr hKne
  exact Group.IsPerfect.not_isSolvable ↥K hKsolv

private noncomputable def bgDualHom (p : ℕ) {E : Type} [AddCommGroup E] [Module (ZMod p) E] :
    (E ≃ₗ[ZMod p] E) →* (Module.Dual (ZMod p) E ≃ₗ[ZMod p] Module.Dual (ZMod p) E) where
  toFun e := e.symm.dualMap
  map_one' := LinearEquiv.ext fun _ => LinearMap.ext fun _ => rfl
  map_mul' _ _ := LinearEquiv.ext fun _ => LinearMap.ext fun _ => rfl

private theorem bgDualHom_injective (p : ℕ) [Fact p.Prime] {E : Type} [AddCommGroup E]
    [Module (ZMod p) E] : Function.Injective (bgDualHom p (E := E)) := by
  rw [injective_iff_map_eq_one]
  intro e he
  have h1 : ∀ (g : Module.Dual (ZMod p) E) (y : E), g (e.symm y) = g y := fun g y => by
    have h := congrArg (fun L : Module.Dual (ZMod p) E ≃ₗ[ZMod p] Module.Dual (ZMod p) E =>
      L g y) he
    exact h
  have hfix : ∀ x : E, e.symm x = x := fun x => by
    have h0 : ∀ g : Module.Dual (ZMod p) E, g (e.symm x - x) = 0 := fun g => by
      rw [map_sub, h1 g x]
      exact sub_self _
    exact sub_eq_zero.mp ((Module.forall_dual_apply_eq_zero_iff (ZMod p) _).mp h0)
  apply LinearEquiv.ext
  intro x
  have h2 := hfix (e x)
  rw [LinearEquiv.symm_apply_apply] at h2
  exact h2.symm

private theorem bg_orbit_eq_dual {p : ℕ} {E : Type} [AddCommGroup E] [Module (ZMod p) E]
    {Γ : Type} [Group Γ] (σ : Γ →* (E ≃ₗ[ZMod p] E)) (f : Module.Dual (ZMod p) E) :
    {g | ∃ γ : Γ, CFSG.Quasithin.H13.L827X.LBCoreB.dualAct (σ γ) f = g} =
      {y | ∃ g ∈ σ.range.map (bgDualHom p), g f = y} := by
  ext y
  constructor
  · rintro ⟨γ, rfl⟩
    exact ⟨bgDualHom p (σ γ), Subgroup.mem_map_of_mem _ (MonoidHom.mem_range.mpr ⟨γ, rfl⟩), rfl⟩
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg
    obtain ⟨γ, rfl⟩ := MonoidHom.mem_range.mp hx
    exact ⟨γ, rfl⟩

private def bgEval (p : ℕ) {E : Type} [AddCommGroup E] [Module (ZMod p) E] (y : E) :
    Module.Dual (ZMod p) E →ₗ[ZMod p] ZMod p where
  toFun g := g y
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem bg_finrank_ker_eval {p : ℕ} [Fact p.Prime] {E : Type} [AddCommGroup E]
    [Module (ZMod p) E] [Finite E] (hE : Module.finrank (ZMod p) E = 2) {y : E} (hy : y ≠ 0) :
    Module.finrank (ZMod p) (LinearMap.ker (bgEval p y)) = 1 := by
  haveI : Module.Finite (ZMod p) E := (Module.finite_iff_finite (R := ZMod p)).mpr inferInstance
  have hdual : Module.finrank (ZMod p) (Module.Dual (ZMod p) E) = 2 := by
    rw [Subspace.dual_finrank_eq, hE]
  obtain ⟨f0, hf0⟩ : ∃ f0 : Module.Dual (ZMod p) E, f0 y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hy ((Module.forall_dual_apply_eq_zero_iff (ZMod p) y).mp hcon)
  have hrange : LinearMap.range (bgEval p y) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    refine ⟨(c * (f0 y)⁻¹) • f0, ?_⟩
    show (c * (f0 y)⁻¹) • f0 y = c
    rw [smul_eq_mul, mul_assoc, inv_mul_cancel₀ hf0, mul_one]
  have hfr := LinearMap.finrank_range_add_finrank_ker (K := ZMod p) (bgEval p y)
  rw [hrange, finrank_top, Module.finrank_self, hdual] at hfr
  omega

theorem dual_orbit_facts {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hSL : CFSG.Quasithin.H13.L827X.SL2OrbitFacts)
    {E : Type} [AddCommGroup E] [Module (ZMod p) E] [Finite E]
    (hE : Module.finrank (ZMod p) E = 2)
    {Γ : Type} [Group Γ] (σ : Γ →* (E ≃ₗ[ZMod p] E))
    (hP : Group.IsPerfect σ.range) (hN : ¬ Group.IsSolvable σ.range) :
    5 ≤ p ∧
    (∀ f : Module.Dual (ZMod p) E, f ≠ 0 →
      24 ≤ Set.ncard {g | ∃ γ : Γ, CFSG.Quasithin.H13.L827X.LBCoreB.dualAct (σ γ) f = g}) ∧
    (∀ f : Module.Dual (ZMod p) E, f ≠ 0 → ∀ y : E, y ≠ 0 →
      3 * Set.ncard ({g | ∃ γ : Γ, CFSG.Quasithin.H13.L827X.LBCoreB.dualAct (σ γ) f = g} ∩
        {g | g y = 0}) ≤
        Set.ncard {g | ∃ γ : Γ, CFSG.Quasithin.H13.L827X.LBCoreB.dualAct (σ γ) f = g}) := by
  haveI : Module.Finite (ZMod p) E := (Module.finite_iff_finite (R := ZMod p)).mpr inferInstance
  haveI : Finite (Module.Dual (ZMod p) E) := Module.finite_of_finite (ZMod p)
  have hDinj : Function.Injective (bgDualHom p (E := E)) := bgDualHom_injective p
  let e := Subgroup.equivMapOfInjective σ.range (bgDualHom p (E := E)) hDinj
  have hPerf : Group.IsPerfect ↥(σ.range.map (bgDualHom p (E := E))) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hNs : ¬ Group.IsSolvable ↥(σ.range.map (bgDualHom p (E := E))) := by
    intro hs
    exact hN (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)
  have hfin : Module.finrank (ZMod p) (Module.Dual (ZMod p) E) = 2 := by
    rw [Subspace.dual_finrank_eq, hE]
  obtain ⟨h5, h24, h3⟩ := hSL p hp2 (Module.Dual (ZMod p) E) hfin _ hPerf hNs
  refine ⟨h5, fun f hf => ?_, fun f hf y hy => ?_⟩
  · rw [bg_orbit_eq_dual σ f]
    exact h24 f hf
  · rw [bg_orbit_eq_dual σ f]
    have hlin := h3 f hf (LinearMap.ker (bgEval p y)) (bg_finrank_ker_eval hE hy)
    have hset : ((LinearMap.ker (bgEval p y) : Submodule (ZMod p) (Module.Dual (ZMod p) E)) :
        Set (Module.Dual (ZMod p) E)) = {g | g y = 0} := rfl
    rw [hset] at hlin
    exact hlin

end CFSG.Quasithin.H13.L827X.LBCaseBG

end
