module

public import CFSG.RankThree.PartTwo.Sec6.BThreeCensusLinear

public section

namespace CFSG.RankThree.PartTwo.Sec16.SuzukiSectionProof

open Matrix Polynomial Module

variable {K : Type} [Field K] [Finite K]

theorem eq_bot_of_invariant (J : Subgroup (GL (Fin 3) K))
    (hJp : Group.IsPerfect J) (hJ3 : ¬ 3 ∣ Nat.card J) (W : Submodule K (Fin 3 → K))
    (hW : ∀ g ∈ J, ∀ v ∈ W, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W) (hW0 : W ≠ ⊥)
    (hWt : W ≠ ⊤) : J = ⊥ := by
  have hWdim : Module.finrank K W ≤ 2 := by
    have h1 := Submodule.finrank_lt hWt
    rw [Module.finrank_fin_fun] at h1
    omega
  have hQdim : Module.finrank K ((Fin 3 → K) ⧸ W) ≤ 2 := by
    have h1 := Submodule.finrank_quotient_add_finrank W
    rw [Module.finrank_fin_fun] at h1
    have h2 : Module.finrank K W ≠ 0 := fun h => hW0 (Submodule.finrank_eq_zero.mp h)
    omega
  have hinv : ∀ g ∈ J, ∀ v ∈ W, Matrix.toLin' (g : Matrix (Fin 3) (Fin 3) K) v ∈ W :=
    fun g hg v hv => by rw [Matrix.toLin'_apply]; exact hW g hg v hv
  let baseW : J →* Module.End K W :=
    { toFun := fun g => (Matrix.toLin' ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)).restrict
        (hinv g g.2)
      map_one' := by
        ext v
        simp
      map_mul' := fun a b => by
        ext v
        simp [Matrix.mulVec_mulVec] }
  have hfixW : ∀ g ∈ J, ∀ v ∈ W, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v := by
    intro g hg v hv
    have h1 := Sec6.BThreeCensus.eq_one_of_finrank_le_two hWdim hJp hJ3 baseW.toHomUnits ⟨g, hg⟩
    have h2 := congrArg (fun u : (Module.End K W)ˣ => ((u : Module.End K W) ⟨v, hv⟩ : Fin 3 → K))
      h1
    simpa [baseW] using h2
  let baseQ : J →* Module.End K ((Fin 3 → K) ⧸ W) :=
    { toFun := fun g => W.mapQ W (Matrix.toLin' ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
        (fun v hv => hinv g g.2 v hv)
      map_one' := by
        ext v
        simp
      map_mul' := fun a b => by
        ext v
        simp }
  have hfixQ : ∀ g ∈ J, ∀ v : Fin 3 → K, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v - v ∈ W := by
    intro g hg v
    have h1 := Sec6.BThreeCensus.eq_one_of_finrank_le_two hQdim hJp hJ3 baseQ.toHomUnits ⟨g, hg⟩
    have h2 := congrArg (fun u : (Module.End K ((Fin 3 → K) ⧸ W))ˣ =>
      ((u : Module.End K ((Fin 3 → K) ⧸ W)) (W.mkQ v))) h1
    simp only [MonoidHom.toHomUnits, baseQ, Units.val_one, Module.End.one_apply] at h2
    change W.mkQ (Matrix.toLin' ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) v) = W.mkQ v at h2
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq,
      Matrix.toLin'_apply] at h2
    exact h2
  have hcomm : ∀ a b : J, a * b = b * a := by
    intro a b
    apply Subtype.ext
    apply Units.ext
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    simp only [Matrix.toLin'_apply, Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec]
    have h1 := hfixW a a.2 _ (hfixQ b b.2 v)
    have h2 := hfixW b b.2 _ (hfixQ a a.2 v)
    rw [Matrix.mulVec_sub, sub_eq_iff_eq_add] at h1 h2
    rw [h1, h2]
    abel
  have hsolv : Group.IsSolvable J := Group.isSolvable_of_comm hcomm
  exact Sec6.BThreeCensus.eq_bot_of_isPerfect_of_isSolvable hJp hsolv

theorem exists_invariant_of_isPGroup {p : ℕ} [hp : Fact p.Prime] [CharP K p]
    {J P : Subgroup (GL (Fin 3) K)} (hP : IsPGroup p P) (hP1 : P ≠ ⊥)
    (hJP : J ≤ Subgroup.normalizer (P : Set (GL (Fin 3) K))) :
    ∃ W : Submodule K (Fin 3 → K),
      (∀ g ∈ J, ∀ v ∈ W, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W) ∧ W ≠ ⊥ ∧ W ≠ ⊤ := by
  classical
  set W : Submodule K (Fin 3 → K) :=
    ⨅ g : P, LinearMap.ker (Matrix.toLin' ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) -
      LinearMap.id) with hWdef
  have hmem : ∀ v, v ∈ W ↔ ∀ g ∈ P, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v := by
    intro v
    rw [hWdef, Submodule.mem_iInf]
    constructor
    · intro h g hg
      have := h ⟨g, hg⟩
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Matrix.toLin'_apply, LinearMap.id_apply,
        sub_eq_zero] at this
      exact this
    · intro h g
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Matrix.toLin'_apply, LinearMap.id_apply,
        sub_eq_zero]
      exact h g g.2
  refine ⟨W, ?_, ?_, ?_⟩
  ·
    intro g hg v hv
    rw [hmem] at hv ⊢
    intro h hh
    have hginv : (g⁻¹ : GL (Fin 3) K) * h * g ∈ P := by
      have := (Subgroup.mem_normalizer_iff.mp (hJP (J.inv_mem hg)) h).mp hh
      simpa [mul_assoc] using this
    have h1 := hv _ hginv
    have h2 : (h : Matrix (Fin 3) (Fin 3) K) * g = g * (((g⁻¹ : GL (Fin 3) K) * h * g :
        GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      rw [← Units.val_mul, ← Units.val_mul]
      congr 1
      group
    rw [Matrix.mulVec_mulVec, h2, ← Matrix.mulVec_mulVec, h1]
  ·
    have : Fintype K := Fintype.ofFinite K
    let _ : MulAction P (Fin 3 → K) :=
      { smul := fun g v => ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v
        one_smul := fun v => by
          change ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v
          simp
        mul_smul := fun g h v => by
          change (((g * h : P) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v =
            ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
              (((h : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v)
          simp [Matrix.mulVec_mulVec] }
    have hmod := hP.card_modEq_card_fixedPoints (Fin 3 → K)
    obtain ⟨n, -, hn⟩ := FiniteField.card K p
    have hV : p ∣ Nat.card (Fin 3 → K) := by
      rw [Nat.card_fun, Nat.card_eq_fintype_card, hn, Nat.card_fin]
      exact dvd_pow (dvd_pow_self p n.ne_zero) (by norm_num)
    have hfix0 : (0 : Fin 3 → K) ∈ MulAction.fixedPoints P (Fin 3 → K) := fun g => by
      change ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ 0 = 0
      exact Matrix.mulVec_zero _
    have hcard : 1 < Nat.card (MulAction.fixedPoints P (Fin 3 → K)) := by
      have hpos : 0 < Nat.card (MulAction.fixedPoints P (Fin 3 → K)) :=
        Nat.card_pos_iff.mpr ⟨⟨⟨0, hfix0⟩⟩, inferInstance⟩
      have hdvd : p ∣ Nat.card (MulAction.fixedPoints P (Fin 3 → K)) := by
        have h := (Nat.modEq_zero_iff_dvd.mpr hV).symm.trans hmod
        exact (Nat.modEq_zero_iff_dvd.mp h.symm)
      have := Nat.le_of_dvd hpos hdvd
      have := hp.out.two_le
      omega
    have := Finite.one_lt_card_iff_nontrivial.mp hcard
    obtain ⟨⟨v, hv⟩, hv0⟩ := exists_ne (⟨0, hfix0⟩ : MulAction.fixedPoints P (Fin 3 → K))
    have hv0' : v ≠ 0 := fun h => hv0 (Subtype.ext h)
    intro hbot
    have hvW : v ∈ W := (hmem v).mpr fun g hg => hv ⟨g, hg⟩
    rw [hbot, Submodule.mem_bot] at hvW
    exact hv0' hvW
  ·
    intro htop
    obtain ⟨⟨g, hgP⟩, hg1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hP1
    have hg1' : g ≠ 1 := fun h => hg1 (Subtype.ext h)
    apply hg1'
    apply Units.ext
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    have hv : v ∈ W := htop ▸ Submodule.mem_top
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Units.val_one, Matrix.one_mulVec]
    exact (hmem v).mp hv g hgP

theorem eq_bot_of_commute_of_not_scalar (J : Subgroup (GL (Fin 3) K))
    (hJp : Group.IsPerfect J) (hJ3 : ¬ 3 ∣ Nat.card J) (m : Matrix (Fin 3) (Fin 3) K)
    (hm : ∀ c : K, m ≠ c • (1 : Matrix (Fin 3) (Fin 3) K))
    (hcomm : ∀ g ∈ J, (g : Matrix (Fin 3) (Fin 3) K) * m = m * g) : J = ⊥ := by
  classical
  set T : Module.End K (Fin 3 → K) := Matrix.toLin' m with hT
  have hgT : ∀ g ∈ J, ∀ v, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ T v =
      T ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ v) := by
    intro g hg v
    rw [hT, Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, hcomm g hg]
  set μ := minpoly K T with hμ
  by_cases hroot : ∃ α, μ.IsRoot α
  ·
    obtain ⟨α, hα⟩ := hroot
    have hev : T.HasEigenvalue α := Module.End.hasEigenvalue_of_isRoot hα
    refine eq_bot_of_invariant J hJp hJ3 (T.eigenspace α) ?_
      (Module.End.hasEigenvalue_iff.mp hev) ?_
    · intro g hg v hv
      rw [Module.End.mem_eigenspace_iff] at hv ⊢
      rw [← hgT g hg v, hv, Matrix.mulVec_smul]
    · intro htop
      apply hm α
      apply Matrix.toLin'.injective
      apply LinearMap.ext
      intro v
      have hv : v ∈ T.eigenspace α := htop ▸ Submodule.mem_top
      rw [Module.End.mem_eigenspace_iff] at hv
      rw [← hT, hv, Matrix.toLin'_apply, Matrix.smul_mulVec, Matrix.one_mulVec]
  · push Not at hroot
    have hint : IsIntegral K T := LinearMap.isIntegral T
    have hdeg3 : μ.natDegree ≤ 3 := by
      have h1 := Polynomial.natDegree_le_of_dvd (LinearMap.minpoly_dvd_charpoly T)
        (LinearMap.charpoly_monic T).ne_zero
      rwa [LinearMap.charpoly_natDegree, Module.finrank_fin_fun] at h1
    have hdeg1 : 1 ≤ μ.natDegree := (minpoly.natDegree_pos hint)
    have hirr : Irreducible μ :=
      Polynomial.irreducible_of_degree_le_three_of_not_isRoot (Finset.mem_Icc.mpr ⟨hdeg1, hdeg3⟩)
        hroot
    have : Fact (Irreducible μ) := ⟨hirr⟩
    let φ : AdjoinRoot μ →ₐ[K] Module.End K (Fin 3 → K) :=
      Ideal.Quotient.liftₐ (Ideal.span {μ}) (aeval T) fun a ha => by
        obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 ha
        rw [map_mul, minpoly.aeval, mul_zero]
    have hφmk : ∀ q : K[X], φ (AdjoinRoot.mk μ q) = aeval T q := fun q => rfl
    let _ : Module (AdjoinRoot μ) (Fin 3 → K) := Module.compHom (Fin 3 → K) φ.toRingHom
    have : IsScalarTower K (AdjoinRoot μ) (Fin 3 → K) := ⟨fun a e v => by
      change φ (a • e) v = a • φ e v
      rw [map_smul, LinearMap.smul_apply]⟩
    have : Module.Finite (AdjoinRoot μ) (Fin 3 → K) :=
      Module.Finite.of_restrictScalars_finite K _ _
    have hE : finrank K (AdjoinRoot μ) = μ.natDegree := by
      rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim]
    have hfr := Module.finrank_mul_finrank K (AdjoinRoot μ) (Fin 3 → K)
    rw [hE, Module.finrank_fin_fun] at hfr
    have hdeg2 : μ.natDegree ≠ 1 := by
      intro h1
      obtain ⟨x, hx⟩ := Polynomial.exists_root_of_degree_eq_one
        (by rw [Polynomial.degree_eq_natDegree hirr.ne_zero, h1]; rfl)
      exact hroot x hx
    have hF1 : finrank (AdjoinRoot μ) (Fin 3 → K) = 1 := by
      have hpos : 0 < finrank (AdjoinRoot μ) (Fin 3 → K) := by
        rcases Nat.eq_zero_or_pos (finrank (AdjoinRoot μ) (Fin 3 → K)) with h | h
        · rw [h, mul_zero] at hfr
          norm_num at hfr
        · exact h
      have hle : μ.natDegree * finrank (AdjoinRoot μ) (Fin 3 → K) = 3 := hfr
      interval_cases hd : μ.natDegree
      · exact absurd rfl hdeg2
      · omega
      · omega
    have hlin : ∀ g ∈ J, ∀ (x : AdjoinRoot μ) (v : Fin 3 → K),
        (g : Matrix (Fin 3) (Fin 3) K) *ᵥ (x • v) = x • ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ v) := by
      intro g hg x v
      obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective x
      change (g : Matrix (Fin 3) (Fin 3) K) *ᵥ (φ (AdjoinRoot.mk μ q) v) =
        φ (AdjoinRoot.mk μ q) ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ v)
      rw [hφmk]
      revert v
      induction q using Polynomial.induction_on with
      | C a =>
        intro v
        rw [aeval_C, Module.algebraMap_end_apply, Module.algebraMap_end_apply,
          Matrix.mulVec_smul]
      | add p q hp hq =>
        intro v
        simp only [map_add, LinearMap.add_apply, Matrix.mulVec_add, hp, hq]
      | monomial n c h =>
        intro v
        rw [pow_succ, ← mul_assoc, map_mul, aeval_X, Module.End.mul_apply, Module.End.mul_apply,
          h, hgT g hg]
    let lin : J → (Fin 3 → K) →ₗ[AdjoinRoot μ] (Fin 3 → K) := fun g =>
      { toFun := fun v => ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v
        map_add' := fun v w => Matrix.mulVec_add _ v w
        map_smul' := fun x v => hlin g g.2 x v }
    have hcommJ : ∀ a b : J, a * b = b * a := by
      intro a b
      obtain ⟨ca, hca, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hF1 (lin a)
      obtain ⟨cb, hcb, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hF1 (lin b)
      apply Subtype.ext
      apply Units.ext
      apply Matrix.toLin'.injective
      apply LinearMap.ext
      intro v
      simp only [Matrix.toLin'_apply, Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec]
      have ha : ∀ w, ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w = ca • w := fun w => by
        have := congrArg (fun f : (Fin 3 → K) →ₗ[AdjoinRoot μ] (Fin 3 → K) => f w) hca
        rw [LinearMap.smul_apply, LinearMap.id_apply] at this
        exact this
      have hb : ∀ w, ((b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w = cb • w := fun w => by
        have := congrArg (fun f : (Fin 3 → K) →ₗ[AdjoinRoot μ] (Fin 3 → K) => f w) hcb
        rw [LinearMap.smul_apply, LinearMap.id_apply] at this
        exact this
      rw [ha, hb, hb, ha, smul_smul, smul_smul, mul_comm]
    have hsolv : Group.IsSolvable J := Group.isSolvable_of_comm hcommJ
    exact Sec6.BThreeCensus.eq_bot_of_isPerfect_of_isSolvable hJp hsolv

end CFSG.RankThree.PartTwo.Sec16.SuzukiSectionProof
