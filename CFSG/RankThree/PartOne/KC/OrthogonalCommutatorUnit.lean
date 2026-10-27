module

public import CFSG.RankThree.PartOne.KC.OrthogonalCommutatorSemilin
public import CFSG.RankThree.PartOne.KC.OrthogonalCommutatorBlock
public import CFSG.RankThree.PartOne.KC.OrthogonalCommutatorScalar
public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedScalar
public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedScalarFixed

public section

namespace CFSG.RankThree.PartOne.KCOrthComm

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear CFSG.RankThree.Classical2
  CFSG.ClassicalGroups.Orthogonal

section Generic

variable {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem semilin_symm_sim {σ : K ≃+* K} {F : V ≃+ V} {μ : K} (hμ : μ ≠ 0)
    (hFQ : ∀ v, Q (F v) = μ * σ (Q v)) :
    ∀ v, Q (F.symm v) = (σ.symm μ)⁻¹ * σ.symm (Q v) := by
  intro v
  have h1 := hFQ (F.symm v)
  rw [AddEquiv.apply_symm_apply] at h1
  have h2 := congrArg σ.symm h1
  rw [map_mul, RingEquiv.symm_apply_apply] at h2
  have hne : σ.symm μ ≠ 0 := by
    intro h0
    apply hμ
    have := congrArg σ h0
    simpa using this
  rw [h2, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

end Generic

theorem hom_eq_one_of_perfect_of_comm {G A : Type*} [Group G] [Group A] (hP : Group.IsPerfect G)
    (hA : ∀ a b : A, a * b = b * a) (φ : G →* A) : ∀ g, φ g = 1 := by
  have hφ : (⊤ : Subgroup G) ≤ φ.ker := by
    rw [← hP.commutator_eq_top]
    refine Subgroup.commutator_le.mpr fun a _ b _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def, hA (φ a) (φ b),
      mul_inv_cancel_right, mul_inv_cancel]
  intro g
  exact MonoidHom.mem_ker.mp (hφ (Subgroup.mem_top g))

theorem hom_eq_one_of_perfect_of_commMonoid {G A : Type*} [Group G] [CommMonoid A]
    (hP : Group.IsPerfect G) (φ : G →* A) (g : G) : φ g = 1 := by
  have h := hom_eq_one_of_perfect_of_comm hP (A := Aˣ) (fun a b => mul_comm a b) φ.toHomUnits g
  have h2 := congrArg (fun u : Aˣ => (u : A)) h
  simpa using h2

section Pairs

variable {K : Type} [Field K] {d : ℕ} (Q : QuadraticForm K (Fin d → K))

theorem pairMap_one (v : Fin d → K) : pairMap Q 1 v = v := coordinateSemilinearMap_one v

theorem pairMap_mul (g h : similarityPairs Q) (v : Fin d → K) :
    pairMap Q (g * h) v = pairMap Q g (pairMap Q h v) :=
  coordinateSemilinearMap_mul g.val h.val v

theorem pairMap_inv (g : similarityPairs Q) : pairMap Q g⁻¹ = (pairMap Q g).symm :=
  coordinateSemilinearMap_inv g.val

theorem pair_mul_right (g h : similarityPairs Q) : (g * h).val.right = g.val.right * h.val.right :=
  rfl

theorem pair_inv_right (g : similarityPairs Q) : (g⁻¹).val.right = g.val.right⁻¹ := rfl

theorem kappa_congr {g g' : similarityPairs Q} (h : ∀ v, pairMap Q g v = pairMap Q g' v) :
    kappa Q g = kappa Q g' := by
  have hE : pairMap Q g = pairMap Q g' := AddEquiv.ext h
  ext y
  obtain ⟨ω, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨ω', hω', hk⟩ := kappa_apply_conj Q g ω
  rw [hk]
  symm
  refine kappa_apply Q g' ω ω' fun v => ?_
  rw [hω' v, hE]

end Pairs


section Unit

variable {K : Type} [Field K] {d : ℕ} (Q : QuadraticForm K (Fin d → K))

@[expose] noncomputable def linOf (g : similarityPairs Q) (hg : g.val.right = 1) :
    (Fin d → K) ≃ₗ[K] (Fin d → K) where
  toFun := pairMap Q g
  map_add' := map_add (pairMap Q g)
  map_smul' c v := by
    rw [pairMap_smul, hg]
    rfl
  invFun := (pairMap Q g).symm
  left_inv := (pairMap Q g).symm_apply_apply
  right_inv := (pairMap Q g).apply_symm_apply

theorem linOf_apply (g : similarityPairs Q) (hg : g.val.right = 1) (v : Fin d → K) :
    linOf Q g hg v = pairMap Q g v := rfl

def commFam (xe : (Fin d → K) ≃ₗ[K] (Fin d → K)) : Set ((Fin d → K) ≃ₗ[K] (Fin d → K)) :=
  {f | f = xe ∨ ∃ h ∈ primaryFactors xe.toLinearMap, h ≠ X - 1 ∧ f ∈ specialBlock Q xe h}

@[expose] def UP (xe : (Fin d → K) ≃ₗ[K] (Fin d → K)) : Subgroup (similarityPairs Q) where
  carrier := {g | g.val.right = 1 ∧
    (∀ f ∈ commFam Q xe, ∀ v, pairMap Q g (f v) = f (pairMap Q g v)) ∧
    (3 ≤ finrank K (fixedSpace xe) → ∃ c : K, ∀ w ∈ fixedSpace xe, pairMap Q g w = c • w)}
  one_mem' := ⟨rfl, fun f _ v => by rw [pairMap_one, pairMap_one], fun _ => ⟨1, fun w _ => by
    rw [pairMap_one, one_smul]⟩⟩
  mul_mem' := by
    rintro g h ⟨hg1, hgc, hgs⟩ ⟨hh1, hhc, hhs⟩
    refine ⟨by rw [pair_mul_right, hg1, hh1, mul_one], fun f hf v => ?_, fun h3 => ?_⟩
    · rw [pairMap_mul, pairMap_mul, hhc f hf v, hgc f hf]
    · obtain ⟨c, hc⟩ := hgs h3
      obtain ⟨c', hc'⟩ := hhs h3
      refine ⟨c * c', fun w hw => ?_⟩
      rw [pairMap_mul, hc' w hw, pairMap_smul, hg1, hc w hw, smul_smul]
      show (c' * c) • w = (c * c') • w
      rw [mul_comm]
  inv_mem' := by
    rintro g ⟨hg1, hgc, hgs⟩
    refine ⟨by rw [pair_inv_right, hg1, inv_one], fun f hf v => ?_, fun h3 => ?_⟩
    · rw [pairMap_inv]
      apply (pairMap Q g).injective
      rw [AddEquiv.apply_symm_apply, hgc f hf, AddEquiv.apply_symm_apply]
    · obtain ⟨c, hc⟩ := hgs h3
      have hc0 : c ≠ 0 := by
        rintro rfl
        have hW : fixedSpace xe = ⊥ := by
          refine (Submodule.eq_bot_iff _).mpr fun w hw => ?_
          have := hc w hw
          rw [zero_smul] at this
          exact (pairMap Q g).injective (by rw [this, map_zero])
        rw [hW, finrank_bot] at h3
        omega
      refine ⟨c⁻¹, fun w hw => ?_⟩
      rw [pairMap_inv]
      apply (pairMap Q g).injective
      rw [AddEquiv.apply_symm_apply, pairMap_smul, hg1, hc w hw, smul_smul]
      show w = (c⁻¹ * c) • w
      rw [inv_mul_cancel₀ hc0, one_smul]

theorem mem_UP_right {xe : (Fin d → K) ≃ₗ[K] (Fin d → K)} {g : similarityPairs Q}
    (hg : g ∈ UP Q xe) : g.val.right = 1 := hg.1

theorem mem_commFam_of_specialBlock {xe : (Fin d → K) ≃ₗ[K] (Fin d → K)} {h : K[X]}
    (hh : h ∈ primaryFactors xe.toLinearMap) (hne1 : h ≠ X - 1) {f : (Fin d → K) ≃ₗ[K] (Fin d → K)}
    (hf : f ∈ specialBlock Q xe h) : f ∈ commFam Q xe := Or.inr ⟨h, hh, hne1, hf⟩

theorem UP_comm_xe {xe : (Fin d → K) ≃ₗ[K] (Fin d → K)} {g : similarityPairs Q}
    (hg : g ∈ UP Q xe) (v : Fin d → K) : pairMap Q g (xe v) = xe (pairMap Q g v) :=
  hg.2.1 xe (Or.inl rfl) v

end Unit


section Conj

variable {K : Type} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {xe : V ≃ₗ[K] V}

theorem isPerfect_specialBlock (hx : OddOrderIsometry Q p xe) (hp : p.Prime) (hp3 : 3 < p)
    {h : K[X]} (hh : h ∈ primaryFactors xe.toLinearMap) (hne1 : h ≠ X - 1) :
    Group.IsPerfect ↥(specialBlock Q xe h) := by
  by_cases hm : 2 ≤ primaryMultiplicity xe.toLinearMap h
  · exact (hx.quasisimple_specialBlock hp hp3 hh hne1 hm).1
  · have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
    have hpos : 1 ≤ primaryMultiplicity xe.toLinearMap h := by
      have hne : primaryComponent xe.toLinearMap h ≠ ⊥ :=
        primaryComponent_ne_bot hx.squarefree_minpoly hh
      have : Nontrivial (primaryComponent xe.toLinearMap h) :=
        Submodule.nontrivial_iff_ne_bot.mpr hne
      exact Module.finrank_pos
    have h1 : primaryMultiplicity xe.toLinearMap h = 1 := by omega
    have hbot := hx.specialBlock_eq_bot_of_finrank_eq_one hh h1
    have : Subsingleton ↥(specialBlock Q xe h) := by
      rw [hbot]
      infer_instance
    infer_instance

theorem conj_mem_specialBlock (hx : OddOrderIsometry Q p xe) (hp : p.Prime) (hp3 : 3 < p)
    {σ : K ≃+* K} {F : V ≃+ V} (hF : ∀ (c : K) (v : V), F (c • v) = σ c • F v) {μ : K}
    (hμ : μ ≠ 0) (hFQ : ∀ v, Q (F v) = μ * σ (Q v)) (hFx : ∀ v, F (xe v) = xe (F v))
    (hfix : ∀ k ∈ primaryFactors xe.toLinearMap, k.map (σ : K →+* K) = k) {h : K[X]}
    (hh : h ∈ primaryFactors xe.toLinearMap) (hne1 : h ≠ X - 1) {f : V ≃ₗ[K] V}
    (hf : f ∈ specialBlock Q xe h) :
    semilinConj F.symm σ.symm (semilin_symm_smul F σ hF) f ∈ specialBlock Q xe h := by
  classical
  have hF' := semilin_symm_smul F σ hF
  have hFx' : ∀ v, F.symm (xe v) = xe (F.symm v) := fun v => by
    apply F.injective
    rw [AddEquiv.apply_symm_apply, hFx, AddEquiv.apply_symm_apply]
  have hFQ' := semilin_symm_sim hμ hFQ
  have hμ' : (σ.symm μ)⁻¹ ≠ 0 := by
    refine inv_ne_zero fun h0 => hμ ?_
    have := congrArg σ h0
    simpa using this
  have hFk : ∀ k ∈ primaryFactors xe.toLinearMap, ∀ v ∈ primaryComponent xe.toLinearMap k,
      F v ∈ primaryComponent xe.toLinearMap k := by
    intro k hk v hv
    have := F_mem_primaryComponent σ F hF hFx hv
    rwa [hfix k hk] at this
  set φ := semilinConj F.symm σ.symm hF' with hφ
  have hmapS : ∀ g ∈ supportedBlock Q xe h, φ g ∈ supportedBlock Q xe h := by
    intro g hg
    rw [mem_supportedBlock] at hg ⊢
    obtain ⟨hgI, hgo⟩ := hg
    obtain ⟨hgQ, hgx⟩ := mem_isometryCentralizer.mp hgI
    have hgQ' : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hgQ
    refine ⟨mem_isometryCentralizer.mpr ⟨?_, fun v => ?_⟩, ?_⟩
    · exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
        (semilinConj_mem_orthogonalGroup F.symm σ.symm hF' ((σ.symm μ)⁻¹) hFQ' hgQ')
    · change F.symm (g (F (xe v))) = xe (F.symm (g (F v)))
      rw [hFx v, hgx, hFx']
    · refine fixes_othersSpace_iff.mpr fun k hk hkh hkh' v hv => ?_
      have h1 := (fixes_othersSpace_iff.mp hgo) k hk hkh hkh' (F v) (hFk k hk v hv)
      change F.symm (g (F v)) = v
      rw [h1, AddEquiv.symm_apply_apply]
  have hP'S : (specialBlock Q xe h).map φ ≤ supportedBlock Q xe h := by
    rintro _ ⟨g, hg, rfl⟩
    exact hmapS g (specialBlock_le_supportedBlock h hg)
  have hP'perf : Group.IsPerfect ↥((specialBlock Q xe h).map φ) := by
    have := isPerfect_specialBlock hx hp hp3 hh hne1
    exact Group.IsPerfect.map (H := specialBlock Q xe h) φ
  have hdet : ∀ z (hz : z ∈ (specialBlock Q xe h).map φ),
      blockDet Q xe h ⟨z, hP'S hz⟩ = 1 := by
    intro z hz
    let ψ : ↥((specialBlock Q xe h).map φ) →* AdjoinRoot h :=
      (blockDet Q xe h).comp (Subgroup.inclusion hP'S)
    exact hom_eq_one_of_perfect_of_commMonoid hP'perf ψ ⟨z, hz⟩
  have hfm : φ f ∈ (specialBlock Q xe h).map φ := ⟨f, hf, rfl⟩
  exact mem_specialBlock.mpr ⟨hP'S hfm, hdet _ hfm⟩

end Conj


section ModelConj

variable {K : Type} [Field K] [Finite K] {d : ℕ} (Q : QuadraticForm K (Fin d → K)) {p : ℕ}
  {xe : (Fin d → K) ≃ₗ[K] (Fin d → K)}

theorem conj_mem_UP (hx : OddOrderIsometry Q p xe) (hp : p.Prime) (hp3 : 3 < p)
    (gα : similarityPairs Q) (hFx : ∀ v, pairMap Q gα (xe v) = xe (pairMap Q gα v))
    (hfix : ∀ k ∈ primaryFactors xe.toLinearMap, k.map (gα.val.right : K →+* K) = k)
    {g : similarityPairs Q} (hg : g ∈ UP Q xe) : gα * g * gα⁻¹ ∈ UP Q xe := by
  obtain ⟨μ, hμ⟩ := exists_pairMap_sim Q gα
  obtain ⟨hg1, hgc, hgs⟩ := hg
  have hF' := semilin_symm_smul (pairMap Q gα) gα.val.right (pairMap_smul Q gα)
  have hμ0 : (μ : K) ≠ 0 := μ.ne_zero
  have hpm : ∀ v, pairMap Q (gα * g * gα⁻¹) v =
      pairMap Q gα (pairMap Q g ((pairMap Q gα).symm v)) := fun v => by
    rw [pairMap_mul, pairMap_mul, pairMap_inv]
  refine ⟨?_, fun f hf v => ?_, fun h3 => ?_⟩
  · rw [pair_mul_right, pair_mul_right, pair_inv_right, hg1, mul_one, mul_inv_cancel]
  ·
    set F := pairMap Q gα with hF
    have hf'mem : semilinConj F.symm gα.val.right.symm hF' f ∈ commFam Q xe := by
      rcases hf with rfl | ⟨h, hh, hne1, hfh⟩
      · left
        refine LinearEquiv.ext fun w => ?_
        change F.symm (f (F w)) = f w
        rw [← hFx w, AddEquiv.symm_apply_apply]
      · right
        exact ⟨h, hh, hne1, conj_mem_specialBlock hx hp hp3 (pairMap_smul Q gα) hμ0 hμ hFx hfix hh
          hne1 hfh⟩
    have hconj : ∀ w, F (semilinConj F.symm gα.val.right.symm hF' f w) = f (F w) := fun w => by
      change F (F.symm (f (F w))) = f (F w)
      rw [AddEquiv.apply_symm_apply]
    have hsymm : F.symm (f v) = semilinConj F.symm gα.val.right.symm hF' f (F.symm v) := by
      apply F.injective
      rw [AddEquiv.apply_symm_apply, hconj, AddEquiv.apply_symm_apply]
    rw [hpm, hpm, hsymm, hgc _ hf'mem, hconj]
  · obtain ⟨c, hc⟩ := hgs h3
    refine ⟨gα.val.right c, fun w hw => ?_⟩
    rw [hpm]
    have hw' : (pairMap Q gα).symm w ∈ fixedSpace xe := by
      rw [mem_fixedSpace] at hw ⊢
      have : (pairMap Q gα).symm (xe w) = xe ((pairMap Q gα).symm w) := by
        apply (pairMap Q gα).injective
        rw [AddEquiv.apply_symm_apply, hFx, AddEquiv.apply_symm_apply]
      rw [← this, hw]
    rw [hc _ hw', pairMap_smul, AddEquiv.apply_symm_apply]

end ModelConj

section Good

variable {K : Type} [Field K] [Finite K] {d : ℕ} (Q : QuadraticForm K (Fin d → K)) {p : ℕ}
  {xe : (Fin d → K) ≃ₗ[K] (Fin d → K)}

theorem pair_good {x : orthDerived Q} (hxe : (x : (Fin d → K) ≃ₗ[K] (Fin d → K)) = xe)
    (hx : OddOrderIsometry Q p xe) (hp : p.Prime) (hp2 : Odd p) (hQ0 : ∃ v, Q v ≠ 0)
    (hG : GateData Q p) {g : similarityPairs Q} (hfixa : kappa Q g (QuotientGroup.mk x) =
      QuotientGroup.mk x) {j : ℕ} (hj : kappa Q g ^ p ^ j = 1) :
    (∀ v, pairMap Q g (xe v) = xe (pairMap Q g v)) ∧ g.val.right ^ p ^ j = 1 ∧
      (∃ c : K, ∀ v, (pairMap Q g)^[p ^ j] v = c • v) ∧
      ∀ k ∈ primaryFactors xe.toLinearMap, k.map (g.val.right : K →+* K) = k := by
  have hFx : ∀ v, pairMap Q g (xe v) = xe (pairMap Q g v) := by
    intro v
    rw [← hxe]
    exact pairMap_comm_of_fixes Q hp2 (by rw [hxe]; exact hx.pow_eq_one) hQ0 g hfixa v
  obtain ⟨hσ, hc⟩ := pair_pow_scalar Q hG g (p ^ j) hj
  have hmin := map_minpoly_eq g.val.right (pairMap Q g) (pairMap_smul Q g) hFx
  exact ⟨hFx, hσ, hc, fun k hk => map_eq_self_of_pow_eq_one hp hx.squarefree_minpoly
    (by rw [← toLinearMap_pow, hx.pow_eq_one]; rfl) hσ hmin hk⟩

omit [Finite K] in
theorem linOf_pow_apply (g : similarityPairs Q) (hg : g.val.right = 1) (n : ℕ) (v : Fin d → K) :
    (linOf Q g hg ^ n) v = (pairMap Q g)^[n] v := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, LinearEquiv.mul_apply, ih, Function.iterate_succ_apply]
    rfl

theorem blockScalar_of_mem_UP (hx : OddOrderIsometry Q p xe) (hp : p.Prime) (hp3 : 3 < p)
    (hW2 : finrank K (fixedSpace xe) ≠ 2) {g : similarityPairs Q} (hg : g ∈ UP Q xe) :
    ∀ h ∈ primaryFactors xe.toLinearMap, BlockScalar xe (linOf Q g hg.1) h := by
  intro h hh
  obtain ⟨hg1, hgc, hgs⟩ := hg
  have hMx : ∀ v, linOf Q g hg1 (xe v) = xe (linOf Q g hg1 v) := fun v => hgc xe (Or.inl rfl) v
  by_cases hne1 : h = X - 1
  · subst hne1
    have : Fact (Irreducible (X - 1 : K[X])) := ⟨irreducible_of_mem_primaryFactors hh⟩
    have hWeq := fixedSpace_eq_primaryComponent (x := xe)
    have hrank := finrank_primaryComponent (x := xe.toLinearMap) (a := (X - 1 : K[X]))
    have hdeg : (X - 1 : K[X]).natDegree = 1 := by simpa using natDegree_X_sub_C (1 : K)
    have h1 : finrank K ↥(fixedSpace xe) =
        finrank K ↥(primaryComponent xe.toLinearMap (X - 1)) := by rw [hWeq]
    have hm : finrank K ↥(fixedSpace xe) = primaryMultiplicity xe.toLinearMap (X - 1) := by
      rw [h1, hrank, hdeg, one_mul]
    have hpos : 1 ≤ finrank K ↥(fixedSpace xe) := by
      have hne : primaryComponent xe.toLinearMap (X - 1) ≠ ⊥ :=
        primaryComponent_ne_bot hx.squarefree_minpoly hh
      have : Nontrivial (primaryComponent xe.toLinearMap (X - 1)) :=
        Submodule.nontrivial_iff_ne_bot.mpr hne
      rw [h1]
      exact Module.finrank_pos
    rcases Nat.lt_or_ge (finrank K ↥(fixedSpace xe)) 3 with h3 | h3
    · have h1' : primaryMultiplicity xe.toLinearMap (X - 1) = 1 := by omega
      exact exists_blockScalar_of_mult_one h1' hMx
    · obtain ⟨c, hc⟩ := hgs h3
      refine ⟨C c, fun v hv => ?_⟩
      have hvW : v ∈ fixedSpace xe := by rw [hWeq]; exact hv
      rw [linOf_apply, hc v hvW, aeval_C, Module.algebraMap_end_apply]
  · exact exists_blockScalar hx hp hp3 hh hne1 hMx fun f hf v => hgc f (Or.inr ⟨h, hh, hne1, hf⟩) v

end Good

section Torsion

variable {K : Type} [Field K] [Finite K] {d : ℕ} (Q : QuadraticForm K (Fin d → K)) {p : ℕ}
  {xe : (Fin d → K) ≃ₗ[K] (Fin d → K)}

theorem kappa_conj_eq_of_pow_two_pow (hx : OddOrderIsometry Q p xe) (hp : p.Prime)
    (hp3 : 3 < p) (hW2 : finrank K (fixedSpace xe) ≠ 2) {gα : similarityPairs Q}
    (hFx : ∀ v, pairMap Q gα (xe v) = xe (pairMap Q gα v)) {N : ℕ} (hN : Odd N)
    (hσN : gα.val.right ^ N = 1)
    (hfix : ∀ k ∈ primaryFactors xe.toLinearMap, k.map (gα.val.right : K →+* K) = k)
    {u : similarityPairs Q} (hu : u ∈ UP Q xe) {s : ℕ} (hus : u ^ 2 ^ s = 1) :
    kappa Q (gα * u * gα⁻¹) = kappa Q u := by
  have hM := blockScalar_of_mem_UP Q hx hp hp3 hW2 hu
  have hMs : linOf Q u hu.1 ^ 2 ^ s = 1 := by
    refine LinearEquiv.ext fun v => ?_
    rw [linOf_pow_apply, ← pairMap_pow, hus, pairMap_one]
    rfl
  have hconj := semilinConj_eq_of_blockScalar hx.squarefree_minpoly (pairMap_smul Q gα) hFx hN
    hσN hfix hM hMs
  refine kappa_congr Q fun v => ?_
  rw [pairMap_mul, pairMap_mul, pairMap_inv]
  have := LinearEquiv.congr_fun hconj v
  rw [semilinConj_apply] at this
  exact this

end Torsion

section Generic2

theorem commute_of_projective_fixed {K : Type*} [Field K] {V : Type*} [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} (G : Subgroup (V ≃ₗ[K] V))
    (hperf : Group.IsPerfect ↥G) (hle : G ≤ orthDerived Q) (σ : K ≃+* K) (F : V ≃+ V)
    (hF : ∀ (c : K) (v : V), F (c • v) = σ c • F v) (μ : K) (hFQ : ∀ v, Q (F v) = μ * σ (Q v))
    (hκ : ∀ g g' : ↥(orthDerived Q), (g : V ≃ₗ[K] V) ∈ G →
      (∀ v, (g' : V ≃ₗ[K] V) v = F ((g : V ≃ₗ[K] V) (F.symm v))) →
      (QuotientGroup.mk g' : ProjOrthDerived Q) = QuotientGroup.mk g) :
    ∀ g ∈ G, ∀ v, F (g v) = g (F v) := by
  set φ := semilinConj F σ hF with hφ
  have hsc : ∀ g : ↥G, (g : V ≃ₗ[K] V)⁻¹ * φ g ∈ scalars K V := by
    intro g
    have hgΩ := hle g.2
    have h1 := hκ ⟨g, hgΩ⟩ ⟨φ g, semilinConj_mem_orthDerived F σ hF μ hFQ hgΩ⟩ g.2
      (fun v => rfl)
    exact Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp h1.symm)
  let θ : ↥G →* ↥(scalars K V) :=
    MonoidHom.mk' (fun g => ⟨(g : V ≃ₗ[K] V)⁻¹ * φ g, hsc g⟩) (by
      intro g h
      apply Subtype.ext
      have hc := commute_of_mem_scalars (hsc g) (h : V ≃ₗ[K] V)⁻¹
      simp only [Subgroup.coe_mul, map_mul, mul_inv_rev]
      calc (h : V ≃ₗ[K] V)⁻¹ * (g : V ≃ₗ[K] V)⁻¹ * (φ g * φ h)
          = (h : V ≃ₗ[K] V)⁻¹ * ((g : V ≃ₗ[K] V)⁻¹ * φ g) * φ h := by simp only [mul_assoc]
        _ = ((g : V ≃ₗ[K] V)⁻¹ * φ g) * (h : V ≃ₗ[K] V)⁻¹ * φ h := by rw [← hc]
        _ = ((g : V ≃ₗ[K] V)⁻¹ * φ g) * ((h : V ≃ₗ[K] V)⁻¹ * φ h) := by simp only [mul_assoc])
  have hker : ∀ g : ↥G, θ g = 1 := by
    have hle' : commutator ↥G ≤ θ.ker := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact Subtype.ext (commute_of_mem_scalars (θ a).2 (θ b))
    intro g
    have htop : commutator ↥G = ⊤ := hperf.commutator_eq_top
    exact hle' (htop ▸ Subgroup.mem_top g)
  intro g hg w
  have h1 := congrArg Subtype.val (hker ⟨g, hg⟩)
  have h2 : (g : V ≃ₗ[K] V)⁻¹ * φ g = 1 := h1
  have h3 : φ g = g := by
    have := congrArg (g * ·) h2
    simpa using this
  have h4 := LinearEquiv.congr_fun h3 (F w)
  rw [semilinConj_apply, AddEquiv.symm_apply_apply] at h4
  exact h4

theorem exists_two_pow_lift {U G : Type*} [Group U] [Finite U] [Group G] (κ : U →* G) {z : G}
    (hz : z ∈ κ.range) {k : ℕ} (hzk : z ^ 2 ^ k = 1) :
    ∃ (u : U) (a : ℕ), κ u = z ∧ u ^ 2 ^ a = 1 := by
  obtain ⟨u₀, rfl⟩ := hz
  obtain ⟨a, b, hb, hn⟩ := Nat.exists_eq_two_pow_mul_odd (n := Nat.card U) Nat.card_pos.ne'
  have hcop : IsCoprime ((2 ^ k : ℕ) : ℤ) (b : ℤ) :=
    Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hb))
  obtain ⟨m, n, hmn⟩ := hcop
  have hmn' : (b : ℤ) * n + ((2 ^ k : ℕ) : ℤ) * m = 1 := by linarith
  have hu₁ : (u₀ ^ b) ^ 2 ^ a = 1 := by
    rw [← pow_mul, mul_comm, ← hn]
    exact pow_card_eq_one'
  refine ⟨(u₀ ^ b) ^ n, a, ?_, ?_⟩
  · rw [map_zpow, map_pow]
    calc (κ u₀ ^ b) ^ n = (κ u₀) ^ ((b : ℤ) * n) := by
          rw [zpow_mul, zpow_natCast]
      _ = κ u₀ := by
          have : (κ u₀) ^ ((b : ℤ) * n + ((2 ^ k : ℕ) : ℤ) * m) = κ u₀ := by
            rw [hmn', zpow_one]
          rw [zpow_add, zpow_mul (κ u₀) ((2 ^ k : ℕ) : ℤ) m, zpow_natCast, hzk, one_zpow,
            mul_one] at this
          exact this
  · rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu₁, one_zpow]

end Generic2

section FromFixes

variable {K : Type} [Field K] [Finite K] {d : ℕ} (Q : QuadraticForm K (Fin d → K)) {p : ℕ}
  {xe : (Fin d → K) ≃ₗ[K] (Fin d → K)}

theorem mem_UP_of_fixes (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K (Fin d → K), finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (hq : 3 < Nat.card K) (hx : OddOrderIsometry Q p xe) (hp : p.Prime) (hp3 : 3 < p)
    {x : orthDerived Q} (hxe : (x : (Fin d → K) ≃ₗ[K] (Fin d → K)) = xe)
    (hQ0 : ∃ v, Q v ≠ 0) {u : similarityPairs Q} (hu1 : u.val.right = 1)
    (hfx : kappa Q u (QuotientGroup.mk x) = QuotientGroup.mk x)
    (hfF : ∀ h ∈ primaryFactors xe.toLinearMap, h ≠ X - 1 → ∀ g : orthDerived Q,
      (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) ∈ specialBlock Q xe h →
        kappa Q u (QuotientGroup.mk g) = QuotientGroup.mk g)
    (hfW : 3 ≤ finrank K (fixedSpace xe) → ∀ g : orthDerived Q,
      (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) ∈ supportedFixedDerived Q xe →
        kappa Q u (QuotientGroup.mk g) = QuotientGroup.mk g)
    (hperfW : 3 ≤ finrank K (fixedSpace xe) → Group.IsPerfect ↥(supportedFixedDerived Q xe)) :
    u ∈ UP Q xe := by
  have hp2 : Odd p := hp.odd_of_ne_two (by omega)
  obtain ⟨μ, hμ⟩ := exists_pairMap_sim Q u
  have hμ' : ∀ v, Q (pairMap Q u v) = (μ : K) * (RingEquiv.refl K) (Q v) := fun v => by
    rw [hμ v, hu1]
    rfl
  have hkey : ∀ (g g' : orthDerived Q), (∀ v, (g' : (Fin d → K) ≃ₗ[K] (Fin d → K)) v =
      pairMap Q u ((g : (Fin d → K) ≃ₗ[K] (Fin d → K)) ((pairMap Q u).symm v))) →
      kappa Q u (QuotientGroup.mk g) = QuotientGroup.mk g' := fun g g' h =>
    kappa_apply Q u g g' h
  refine ⟨hu1, fun f hf v => ?_, fun h3 => ?_⟩
  · rcases hf with rfl | ⟨h, hh, hne1, hfh⟩
    · rw [← hxe]
      exact pairMap_comm_of_fixes Q hp2 (by rw [hxe]; exact hx.pow_eq_one) hQ0 u hfx v
    · by_cases hm : 2 ≤ primaryMultiplicity xe.toLinearMap h
      · have hle := hx.specialBlock_le_orthDerived hp hp3 hh hne1 hm
        have := commute_of_projective_fixed (Q := Q) (specialBlock Q xe h)
          (isPerfect_specialBlock hx hp hp3 hh hne1) hle (1 : K ≃+* K) (pairMap Q u)
          (fun c w => by rw [pairMap_smul, hu1]) (μ : K) hμ' (fun g g' hg hg' => by
            have h1 := hfF h hh hne1 g hg
            rw [hkey g g' hg'] at h1
            exact h1) f hfh v
        exact this
      · have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
        have hpos : 1 ≤ primaryMultiplicity xe.toLinearMap h := by
          have hne : primaryComponent xe.toLinearMap h ≠ ⊥ :=
            primaryComponent_ne_bot hx.squarefree_minpoly hh
          have : Nontrivial (primaryComponent xe.toLinearMap h) :=
            Submodule.nontrivial_iff_ne_bot.mpr hne
          exact Module.finrank_pos
        have h1 : primaryMultiplicity xe.toLinearMap h = 1 := by omega
        have hbot := hx.specialBlock_eq_bot_of_finrank_eq_one hh h1
        rw [hbot, Subgroup.mem_bot] at hfh
        subst hfh
        rfl
  ·
    have hperf := hperfW h3
    have hQW := hx.polarBilin_fixed_nondegenerate
    have hperf' : Group.IsPerfect ↥(supportedDerived Q (fixedSpace xe)) := by
      rw [hx.supportedDerived_fixedSpace]
      exact hperf
    obtain ⟨-, -, -, ⟨c, hc⟩, -, -⟩ :=
      supported_orthogonal_derived_semilinear_centralizer_scalar_restriction Q hQ hT
        (fixedSpace xe) hQW h3 hperf' (fun h2 => absurd h2 (by omega)) (RingEquiv.refl K)
        (pairMap Q u) (fun c w => by rw [pairMap_smul, hu1]; rfl) (μ : K) μ.ne_zero hμ'
        (fun g g' hg hg' => by
          rw [hx.supportedDerived_fixedSpace] at hg
          have h1 := hfW h3 g hg
          rw [hkey g g' hg'] at h1
          exact h1)
    exact ⟨(c : K), fun w hw => hc w hw⟩

end FromFixes

end CFSG.RankThree.PartOne.KCOrthComm
