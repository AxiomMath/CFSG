module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitarySixThreeFieldAlg
public import CFSG.RankThree.PartOne.KC.UnitaryGoodSpecial
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeTorus
public import CFSG.RankThree.CentralLift.DefiningUnitary
public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeAbstract
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.StandardType

namespace TableBU63

open Polynomial Module Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCUnitaryModel

section Twist

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem comp_aeval_twist {x Y : Module.End K V} {t : K} (hYx : Y * x = t • (x * Y)) (p : K[X]) :
    Y * aeval x p = aeval x (p.comp (C t * X)) * Y := by
  have hpow : ∀ k : ℕ, Y * x ^ k = t ^ k • (x ^ k * Y) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← mul_assoc, ih, smul_mul_assoc, mul_assoc, hYx, mul_smul_comm, smul_smul,
        ← mul_assoc, pow_succ t]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, mul_add, hp, hq, add_comp, map_add, add_mul]
  | monomial k a =>
    rw [monomial_comp, aeval_monomial, map_mul, map_pow, map_mul, aeval_C, aeval_C, aeval_X,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    simp only [smul_mul_assoc, one_mul, mul_smul_comm, _root_.smul_pow, smul_smul]
    rw [hpow, smul_smul, mul_comm a]

end Twist

section Twisted

variable {K : Type} [Field K] {n : ℕ} {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem cubeTwist_mk {c : K} {f : K[X]} [Fact (Irreducible f)] (hf : f = X ^ 3 - C c) {t : K}
    (ht : t ^ 3 = 1) (p : K[X]) :
    cubeTwist hf t ht (AdjoinRoot.mk f p) = AdjoinRoot.mk f (p.comp (C t * X)) := by
  rw [← AdjoinRoot.aeval_eq, ← aeval_algHom_apply, cubeTwist_root, ← AdjoinRoot.aeval_eq,
    aeval_comp, map_mul, aeval_C, aeval_X]

theorem not_commute_specialBlock_of_twist {hK : UnitaryFieldData 2 n K}
    (hKc : Nat.card K = (2 ^ n) ^ 2) {B : V →ₛₗ[hK.bar] V →ₗ[K] K}
    {x : LinearMap.GeneralLinearGroup K V} (H0 : UnitaryPrimaryData hK.bar B x) {c : K}
    (a : primaryFactors (x : Module.End K V)) (hac : (a : K[X]) = X ^ 3 - C c)
    (hself : dualPoly hK.bar (a : K[X]) = a)
    (htop : primaryComponent (x : Module.End K V) (a : K[X]) = ⊤)
    (hmult : Module.finrank (AdjoinRoot (a : K[X]))
      (primaryComponent (x : Module.End K V) (a : K[X])) = 2)
    {Y : LinearMap.GeneralLinearGroup K V} {t : K} (ht3 : t ^ 3 = 1) (ht1 : t ≠ 1)
    (hYx : (Y : Module.End K V) * (x : Module.End K V) =
      t • ((x : Module.End K V) * (Y : Module.End K V)))
    (hcomm : ∀ g ∈ specialBlock B x (a : K[X]), Y * g = g * Y) : False := by
  classical
  have hn : 1 ≤ n := hK.one_le
  have := hK.finite
  obtain ⟨hE, Hf, hHf, hHfl, φ, hφ, -⟩ :=
    exists_selfDualFactor (a := a) hself (selfDualPrimaryBlock H0 a hself)
  obtain ⟨e, he⟩ := hE.exists_orthonormal_basis hHf hHfl
  set e₂ := e.reindex (finCongr hmult) with he₂def
  have he₂ : ∀ i j, Hf (e₂ i) (e₂ j) = (1 : Matrix (Fin 2) (Fin 2) _) i j := by
    intro i j
    rw [he₂def, Module.Basis.reindex_apply, Module.Basis.reindex_apply, he, Matrix.one_apply]
    simp only [EmbeddingLike.apply_eq_iff_eq]
  obtain ⟨μ, hμ1, hμK⟩ := exists_pow_eq_one_not_mem hac (q := 2 ^ n)
    (by have := Nat.one_lt_two_pow (n := n) (by omega); omega) hKc
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by positivity)] at hμ1
    exact zero_ne_one hμ1
  set μu : (AdjoinRoot (a : K[X]))ˣ := Units.mk0 μ hμ0 with hμu
  set τ : Fin 2 → (AdjoinRoot (a : K[X]))ˣ := ![μu, μu⁻¹] with hτ
  set Dm := CFSG.SectionRank.OddCover.diagHom 2 τ with hDm
  have hdeg : (a : K[X]).natDegree = 3 := by rw [hac]; exact natDegree_X_pow_sub_C
  have hbar : hE.bar μ * μ = 1 := by
    rw [UnitaryFieldData.bar_apply, ← pow_succ, hdeg, pow_mul]
    exact hμ1
  have hbar' : hE.bar μ⁻¹ * μ⁻¹ = 1 := by
    rw [map_inv₀, ← mul_inv, hbar, inv_one]
  have hDmSU : Dm ∈ gramSU hE (1 : Matrix (Fin 2) (Fin 2) _) := by
    rw [mem_gramSU, hDm, CFSG.SectionRank.OddCover.coe_diagHom, Matrix.mul_one,
      Matrix.det_diagonal, Fin.prod_univ_two]
    refine ⟨?_, ?_⟩
    · rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
        ← Matrix.diagonal_one]
      congr 1
      funext i
      fin_cases i
      · simpa [hτ, hμu] using hbar
      · simpa [hτ, hμu] using hbar'
    · simp [hτ, hμu, hμ0]
  set δ := Matrix.GeneralLinearGroup.toLin' e₂ Dm with hδ
  have hδSU : δ ∈ sesqSpecialUnitaryGroup Hf :=
    (CFSG.RankThree.CentralLift.toLin'_mem_sesqSpecialUnitaryGroup_iff_gramSU hE e₂ he₂ Dm).mpr
      hDmSU
  set g := φ.symm ⟨δ, (mem_sesqSpecialUnitaryGroup.mp hδSU).1⟩ with hg
  have hφg : ((φ g : sesqUnitaryGroup Hf) : blockGL (x : Module.End K V) (a : K[X])) = δ := by
    rw [hg, MulEquiv.apply_symm_apply]
  have hgapply : ∀ (v : V) (hv : v ∈ primaryComponent (x : Module.End K V) (a : K[X])),
      (((g : orbitFactor B x (a : K[X])) : LinearMap.GeneralLinearGroup K V) :
        Module.End K V) v = blockApply δ v hv := fun v hv => by
    rw [← hφ g v hv, hφg]
  have hgS : ((g : orbitFactor B x (a : K[X])) : LinearMap.GeneralLinearGroup K V) ∈
      specialBlock B x (a : K[X]) := by
    refine mem_specialBlock.mpr ⟨g.2, orbitFactor_le_gl_centralizer g.2, ?_⟩
    have hres : blockRestrict x (a : K[X]) ⟨_, orbitFactor_le_gl_centralizer g.2⟩ = δ :=
      blockGL_ext fun v hv => by rw [blockApply_blockRestrict, hgapply v hv]
    change blockGLDet _ _ (blockRestrict x (a : K[X]) ⟨_, orbitFactor_le_gl_centralizer g.2⟩) = 1
    rw [hres]
    apply Units.ext
    rw [blockGLDet, Units.coe_map, Units.val_one]
    exact (CFSG.RankThree.CentralLift.det_toLin'_basis e₂ Dm).trans hDmSU.2
  have hYg := hcomm _ hgS
  set gL := (((g : orbitFactor B x (a : K[X])) : LinearMap.GeneralLinearGroup K V) :
    Module.End K V) with hgL
  have hYgL : (Y : Module.End K V) * gL = gL * (Y : Module.End K V) := by
    have := congrArg (fun u : LinearMap.GeneralLinearGroup K V => (u : Module.End K V)) hYg
    simpa only [Units.val_mul] using this
  have hmem : ∀ v : V, v ∈ primaryComponent (x : Module.End K V) (a : K[X]) := fun v =>
    htop ▸ Submodule.mem_top
  set v₀ : V := ((e₂ 0 : primaryComponent (x : Module.End K V) (a : K[X])) : V) with hv₀
  have hDmc : (Dm : Matrix (Fin 2) (Fin 2) (AdjoinRoot (a : K[X]))) =
      Matrix.diagonal ![μ, μ⁻¹] := by
    rw [hDm, CFSG.SectionRank.OddCover.coe_diagHom]
    congr 1
    funext i
    fin_cases i
    · simp only [hτ, hμu, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Units.val_mk0]
    · simp only [hτ, hμu, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Units.val_inv_eq_inv_val, Units.val_mk0]
  have hδe : δ.val (e₂ 0) = μ • e₂ 0 := by
    apply e₂.equivFun.injective
    rw [hδ, CFSG.RankThree.CentralLift.equivFun_toLin'_basis_apply, LinearEquiv.map_smul, hDmc]
    funext i
    rw [Matrix.mulVec_diagonal, Pi.smul_apply, Module.Basis.equivFun_self, smul_eq_mul]
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, ite_true]
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [ite_eq_right (by decide), mul_zero, mul_zero]
  obtain ⟨p, hp⟩ := AdjoinRoot.mk_surjective μ
  have hgv₀ : gL v₀ = aeval (x : Module.End K V) p v₀ := by
    rw [hgL, hgapply v₀ (hmem v₀)]
    have e0 : (⟨v₀, hmem v₀⟩ : primaryComponent (x : Module.End K V) (a : K[X])) = e₂ 0 := rfl
    change ((δ.val ⟨v₀, hmem v₀⟩ : primaryComponent _ _) : V) = _
    rw [e0, hδe, ← hp, coe_mk_smul_primaryComponent]
  set w := (Y : Module.End K V) v₀ with hw
  have hgw : gL w = aeval (x : Module.End K V) (p.comp (C t * X)) w := by
    have e1 : gL w = (Y : Module.End K V) (gL v₀) := by
      rw [hw, ← Module.End.mul_apply, ← hYgL, Module.End.mul_apply]
    rw [e1, hgv₀, ← Module.End.mul_apply, comp_aeval_twist hYx, Module.End.mul_apply]
  obtain ⟨w', hw'⟩ : ∃ w' : primaryComponent (x : Module.End K V) (a : K[X]),
      (w' : V) = w := ⟨⟨w, hmem w⟩, rfl⟩
  have hδw : δ.val w' = cubeTwist hac t ht3 μ • w' := by
    apply Subtype.ext
    have e2 : gL w = ((δ.val w' : primaryComponent _ _) : V) := by
      rw [← hw']
      exact hgapply (w' : V) w'.2
    rw [← e2, hgw, ← hw', ← hp, cubeTwist_mk, coe_mk_smul_primaryComponent]
  have hcoord : ∀ i, (τ i : AdjoinRoot (a : K[X])) * e₂.equivFun w' i =
      cubeTwist hac t ht3 μ * e₂.equivFun w' i := by
    intro i
    have e3 := congrArg (fun u => e₂.equivFun u i) hδw
    rw [hδ, CFSG.RankThree.CentralLift.equivFun_toLin'_basis_apply, LinearEquiv.map_smul,
      hDm, CFSG.SectionRank.OddCover.coe_diagHom, Matrix.mulVec_diagonal, Pi.smul_apply,
      smul_eq_mul] at e3
    exact e3
  have hw0 : w' ≠ 0 := by
    intro h0
    have h1 : w = 0 := by rw [← hw', h0]; rfl
    have hv₀0 : v₀ = 0 := by
      have e4 := congrArg
        (fun u => ((Y⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) u) h1
      simp only [hw, map_zero] at e4
      rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Module.End.one_apply] at e4
      exact e4
    exact e₂.ne_zero 0 (Subtype.ext hv₀0)
  have hne : e₂.equivFun w' ≠ 0 := fun h0 => hw0 (e₂.equivFun.map_eq_zero_iff.mp h0)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  have hσ : cubeTwist hac t ht3 μ = (τ i : AdjoinRoot (a : K[X])) :=
    (mul_right_cancel₀ hi (hcoord i)).symm
  have ht2 : t * t ≠ 1 := fun h2 => ht1 (by
    have e5 : t ^ 3 = t * (t * t) := by ring
    rw [e5, h2, mul_one] at ht3
    exact ht3)
  fin_cases i
  · have hσ' : cubeTwist hac t ht3 μ = μ := by
      rw [hσ]
      simp only [hτ, hμu, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Units.val_mk0]
    obtain ⟨k, hk⟩ := eq_algebraMap_of_cubeTwist hac ht3 ht1 hσ'
    exact hμK k hk.symm
  · have hσ' : cubeTwist hac t ht3 μ = μ⁻¹ := by
      rw [hσ]
      simp only [hτ, hμu, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Units.val_inv_eq_inv_val, Units.val_mk0]
    have h2 : cubeTwist hac (t * t) (by rw [mul_pow, ht3, one_mul]) μ = μ := by
      rw [← cubeTwist_cubeTwist hac t t ht3 ht3, hσ', map_inv₀, hσ', inv_inv]
    obtain ⟨k, hk⟩ := eq_algebraMap_of_cubeTwist hac _ ht2 h2
    exact hμK k hk.symm

end Twisted

section Block

variable {K : Type} [Field K] {n : ℕ} (h : UnitaryFieldData 2 n K)

theorem toLinU_apply_mulVec (A : primeFormUnitary h (idGram K 6)) (v : Fin 6 → K) :
    ((toLinU h 6 A : LinearMap.GeneralLinearGroup K (Fin 6 → K)) : Module.End K (Fin 6 → K)) v =
      ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ v := rfl

theorem toLinU_pow_apply (A : primeFormUnitary h (idGram K 6)) (k : ℕ) (v : Fin 6 → K) :
    (((toLinU h 6 A : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
      Module.End K (Fin 6 → K)) ^ k) v =
      (((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) ^ k) *ᵥ v := by
  induction k generalizing v with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih, toLinU_apply_mulVec, mulVec_mulVec, ← pow_succ]

omit [Field K] in
theorem scalar_mul_eq_smul' [Field K] (c : K) (N : Matrix (Fin 6) (Fin 6) K) :
    Matrix.scalar (Fin 6) c * N = c • N := by
  rw [Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]

include h in
theorem three_dvd_card_sub_one (hpq : 3 ∣ 2 ^ n + 1) : 3 ∣ Nat.card K - 1 := by
  rw [h.card, pow_mul', sq]
  have e := Nat.mul_self_sub_mul_self_eq (2 ^ n) 1
  rw [mul_one] at e
  rw [e]
  exact Dvd.dvd.mul_right hpq _

include h in
theorem exists_fieldBlock (hpq : 3 ∣ 2 ^ n + 1) {M : primeFormUnitary h (idGram K 6)} {l : Kˣ}
    (hM3 : (M : GL (Fin 6) K) ^ 3 = GeneralLinearGroup.scalar (Fin 6) l)
    (hl : ∀ c : Kˣ, c ^ 3 ≠ l) :
    ∃ J : Subgroup (primeFormUnitary h (idGram K 6)),
      CFSG.IsQuasisimple J ∧
      (∀ g ∈ J, ((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1) ∧
      (∀ g ∈ J, g * M = M * g) ∧
      (∀ g g' : primeFormUnitary h (idGram K 6), g * M = M * g → g' * M = M * g' →
        g * g' * g⁻¹ * g'⁻¹ ∈ J) ∧
      (∀ Y : primeFormUnitary h (idGram K 6), (∀ g ∈ J, Y * g = g * Y) →
        ∀ t : Kˣ, (Y : GL (Fin 6) K) * M = GeneralLinearGroup.scalar (Fin 6) t * (M * Y) →
        (∃ k : Kˣ, (Y : GL (Fin 6) K) ^ 3 = GeneralLinearGroup.scalar (Fin 6) k) →
        ∃ (d : Kˣ) (j : ℕ), (Y : GL (Fin 6) K) =
          GeneralLinearGroup.scalar (Fin 6) d * (M : GL (Fin 6) K) ^ j) := by
  classical
  have hn : 1 ≤ n := h.one_le
  have := h.finite
  have hKc : Nat.card K = (2 ^ n) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  set x := toLinU h 6 M with hx
  have hc : ∀ d : K, d ^ 3 ≠ (l : K) := fun d hd => by
    have hd0 : d ≠ 0 := by
      rintro rfl
      rw [zero_pow (by norm_num)] at hd
      exact l.ne_zero hd.symm
    exact hl (Units.mk0 d hd0) (Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hd]))
  have hirr := irreducible_X_pow_three_sub_C hc
  have hx3 : (x : Module.End K (Fin 6 → K)) ^ 3 = algebraMap K _ (l : K) := by
    refine LinearMap.ext fun v => ?_
    rw [hx, toLinU_pow_apply, ← Units.val_pow_eq_pow_val, hM3, GeneralLinearGroup.coe_scalar,
      Module.algebraMap_end_apply, Matrix.scalar_apply]
    funext i
    rw [Matrix.mulVec_diagonal]
    rfl
  have hPx : aeval (x : Module.End K (Fin 6 → K)) (X ^ 3 - C (l : K)) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, hx3, sub_self]
  have hmon : (X ^ 3 - C (l : K) : K[X]).Monic := monic_X_pow_sub_C _ (by norm_num)
  have hmin : minpoly K (x : Module.End K (Fin 6 → K)) = X ^ 3 - C (l : K) :=
    (minpoly.eq_of_irreducible_of_monic hirr hPx hmon).symm
  have H0 : UnitaryPrimaryData h.bar (idForm h 6) x :=
    ⟨h.bar_bar, idForm_isSymm h 6, idForm_separatingLeft h 6, toLinU_mem M,
      hmin ▸ hirr.squarefree⟩
  have ha : (X ^ 3 - C (l : K) : K[X]) ∈ primaryFactors (x : Module.End K (Fin 6 → K)) :=
    mem_primaryFactors.mpr ⟨hirr, hmon, hmin.symm ▸ dvd_rfl⟩
  have honly : ∀ b ∈ primaryFactors (x : Module.End K (Fin 6 → K)), b = X ^ 3 - C (l : K) := by
    intro b hb
    obtain ⟨hbirr, hbmon, hbdvd⟩ := mem_primaryFactors.mp hb
    rw [hmin] at hbdvd
    exact eq_of_monic_of_associated hbmon hmon (hbirr.associated_of_dvd hirr hbdvd)
  obtain ⟨a, hac⟩ : ∃ a : primaryFactors (x : Module.End K (Fin 6 → K)),
      (a : K[X]) = X ^ 3 - C (l : K) := ⟨⟨_, ha⟩, rfl⟩
  have hself : dualPoly h.bar (a : K[X]) = a := by
    rw [honly _ (dualPoly_mem_primaryFactors H0 a.2), hac]
  have htop : primaryComponent (x : Module.End K (Fin 6 → K)) (a : K[X]) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    rw [mem_primaryComponent, hac, hPx, LinearMap.zero_apply]
  have hmult : primaryMultiplicity (x : Module.End K (Fin 6 → K)) (a : K[X]) = 2 := by
    have hfr := finrank_primaryComponent (x : Module.End K (Fin 6 → K)) (a : K[X])
    have hn' :
        Module.finrank K (primaryComponent (x : Module.End K (Fin 6 → K)) (a : K[X])) = 6 := by
      rw [htop, finrank_top, Module.finrank_fin_fun]
    have hdeg : (a : K[X]).natDegree = 3 := by rw [hac]; exact natDegree_X_pow_sub_C
    rw [hn', hdeg] at hfr
    unfold primaryMultiplicity
    omega
  have hgood : IsGoodBlock h x a := by
    have hdeg : (a : K[X]).natDegree = 3 := by rw [hac]; exact natDegree_X_pow_sub_C
    refine ⟨by rw [hmult], fun _ => ?_⟩
    rw [hmult, hdeg]
    have h8 : 8 ≤ 2 ^ (n * 3) := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (n * 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq, not_or]
    omega
  have hq2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have SBF := specialBlockFacts_of_good H0 hq2 a hgood
  have horb : orbitFactor (idForm h 6) x (a : K[X]) = unitaryCentralizer (idForm h 6) x := by
    refine le_antisymm orbitFactor_le_unitaryCentralizer fun g hg => ⟨hg, fun b hb hbS => ?_⟩
    exact absurd (Or.inl (by rw [honly b hb, hac])) hbS
  set J := (specialBlock (idForm h 6) x (a : K[X])).comap (toLinU h 6) with hJ
  have hJmap : J.map (toLinU h 6) = specialBlock (idForm h 6) x (a : K[X]) := by
    rw [hJ, Subgroup.map_comap_eq, range_toLinU]
    exact inf_of_le_right (specialBlock_le_unitaryCentralizer.trans fun g hg => hg.1)
  have hcent : ∀ g : primeFormUnitary h (idGram K 6),
      toLinU h 6 g ∈ unitaryCentralizer (idForm h 6) x ↔ g * M = M * g := by
    intro g
    rw [mem_unitaryCentralizer]
    constructor
    · rintro ⟨-, hc'⟩
      apply toLinU_injective
      rw [map_mul, map_mul]
      exact Units.ext hc'.eq
    · intro hgM
      refine ⟨toLinU_mem g, ?_⟩
      have e := congrArg (fun u => ((toLinU h 6 u : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
        Module.End K (Fin 6 → K))) hgM
      simp only [map_mul, Units.val_mul] at e
      exact e
  refine ⟨J, ?_, ?_, ?_, ?_, ?_⟩
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((J.equivMapOfInjective (toLinU h 6) toLinU_injective).trans
        (MulEquiv.subgroupCongr hJmap)).symm (SBF.quasisimple (by rw [hmult]))
  · intro g hg
    have e := SBF.detK _ hg
    rwa [show ((toLinU h 6 g : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
      Module.End K (Fin 6 → K)) = Matrix.toLin' ((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)
        from rfl, LinearMap.det_toLin'] at e
  · intro g hg
    exact (hcent g).mp (specialBlock_le_unitaryCentralizer hg)
  · intro g g' hg hg'
    have h1 : toLinU h 6 g ∈ orbitFactor (idForm h 6) x (a : K[X]) := horb ▸ (hcent g).mpr hg
    have h2 : toLinU h 6 g' ∈ orbitFactor (idForm h 6) x (a : K[X]) := horb ▸ (hcent g').mpr hg'
    have h3 := Subgroup.commutator_mem_commutator h1 h2
    rw [SBF.commutator_eq (by rw [hmult])] at h3
    show toLinU h 6 (g * g' * g⁻¹ * g'⁻¹) ∈ specialBlock (idForm h 6) x (a : K[X])
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    exact h3
  · intro Y hYJ t hYM ⟨k, hk⟩
    set yL := toLinU h 6 Y with hyL
    have hYx : (yL : Module.End K (Fin 6 → K)) * (x : Module.End K (Fin 6 → K)) =
        (t : K) • ((x : Module.End K (Fin 6 → K)) * (yL : Module.End K (Fin 6 → K))) := by
      have e := congrArg (fun u : GL (Fin 6) K => (u : Matrix (Fin 6) (Fin 6) K)) hYM
      simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, scalar_mul_eq_smul'] at e
      refine LinearMap.ext fun v => ?_
      rw [Module.End.mul_apply, LinearMap.smul_apply, Module.End.mul_apply, hyL, hx,
        toLinU_apply_mulVec, toLinU_apply_mulVec, toLinU_apply_mulVec, toLinU_apply_mulVec,
        mulVec_mulVec, mulVec_mulVec, e, smul_mulVec]
    have hcommS : ∀ g ∈ specialBlock (idForm h 6) x (a : K[X]), yL * g = g * yL := by
      intro g hg
      rw [← hJmap] at hg
      obtain ⟨g', hg', rfl⟩ := hg
      rw [hyL, ← map_mul, ← map_mul, hYJ g' hg']
    have ht3 : (t : K) ^ 3 = 1 := by
      have e1 := TypeA.PGLTor.mul_pow_eq_of_mul_eq (TypeA.PGLTor.commute_scalar t _) hYM 3
      rw [hM3, ← map_pow, ← mul_assoc, ← map_mul, ← TypeA.PGLTor.scalar_mul_comm] at e1
      have e2 := mul_right_cancel e1
      have e3 := TypeA.PGLTor.scalar_injective e2
      have e4 : (l : K) = (t : K) ^ 3 * (l : K) := by
        have := congrArg Units.val e3
        simpa using this
      have hl0 : (l : K) ≠ 0 := l.ne_zero
      field_simp at e4
      linear_combination -e4
    by_cases ht1 : (t : K) = 1
    ·
      have hYU : yL ∈ unitaryCentralizer (idForm h 6) x := by
        refine ⟨toLinU_mem Y, mem_gl_centralizer.mpr ?_⟩
        show (yL : Module.End K (Fin 6 → K)) * x = x * yL
        rw [hYx, ht1, one_smul]
      obtain ⟨cE, hcE⟩ := SBF.scalar yL hYU (fun _ g hg => hcommS g hg)
      have hpowE : ∀ (m : ℕ) (v : primaryComponent (x : Module.End K (Fin 6 → K)) (a : K[X])),
          ((yL : Module.End K (Fin 6 → K)) ^ m) (v : Fin 6 → K) =
            ((cE ^ m • v : primaryComponent _ _) : Fin 6 → K) := by
        intro m
        induction m with
        | zero => intro v; simp
        | succ m ih =>
          intro v
          rw [pow_succ, Module.End.mul_apply, hcE v, ih, pow_succ, mul_smul]
      have hmemA :
          ∀ v : Fin 6 → K, v ∈ primaryComponent (x : Module.End K (Fin 6 → K)) (a : K[X]) :=
        fun v => htop ▸ Submodule.mem_top
      set v₀ : Fin 6 → K := Pi.single 0 1 with hv₀
      have hv₀0 :
          (⟨v₀, hmemA v₀⟩ : primaryComponent (x : Module.End K (Fin 6 → K)) (a : K[X])) ≠ 0 :=
        fun h0 => by
          have e := congrFun (congrArg Subtype.val h0) 0
          simp [hv₀] at e
      have hcE3 : cE ^ 3 = algebraMap K (AdjoinRoot (a : K[X])) (k : K) := by
        have e1 : ((cE ^ 3 • (⟨v₀, hmemA v₀⟩ :
            primaryComponent (x : Module.End K (Fin 6 → K)) (a : K[X])) :
              primaryComponent _ _) : Fin 6 → K) = (k : K) • v₀ := by
          rw [← hpowE 3 ⟨v₀, hmemA v₀⟩, hyL, toLinU_pow_apply, ← Units.val_pow_eq_pow_val, hk,
            GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
          funext i
          rw [Matrix.mulVec_diagonal]
          rfl
        have e2 : ((cE ^ 3 - algebraMap K (AdjoinRoot (a : K[X])) (k : K)) •
            (⟨v₀, hmemA v₀⟩ : primaryComponent (x : Module.End K (Fin 6 → K)) (a : K[X]))) = 0 := by
          apply Subtype.ext
          rw [sub_smul, Submodule.coe_sub, e1, coe_algebraMap_smul_primaryComponent, sub_self]
          rfl
        rcases smul_eq_zero.mp e2 with h0 | h0
        · exact sub_eq_zero.mp h0
        · exact absurd h0 hv₀0
      obtain ⟨d, j, hdj⟩ := exists_eq_mul_root_pow hac hc (three_dvd_card_sub_one h hpq) hcE3
      have hYv : ∀ v : Fin 6 → K, ((Y : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ v =
          (d • ((M : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) ^ j) *ᵥ v := by
        intro v
        have e1 := hcE ⟨v, hmemA v⟩
        rw [hdj, show algebraMap K (AdjoinRoot (a : K[X])) d * AdjoinRoot.root (a : K[X]) ^ j =
          AdjoinRoot.mk (a : K[X]) (C d * X ^ j) by
            rw [map_mul, AdjoinRoot.mk_C, map_pow, AdjoinRoot.mk_X]; rfl,
          coe_mk_smul_primaryComponent, map_mul, aeval_C, map_pow, aeval_X,
          Module.End.mul_apply, Module.algebraMap_end_apply, toLinU_pow_apply] at e1
        rw [← toLinU_apply_mulVec, ← hyL, e1, smul_mulVec]
      have hYmat : ((Y : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
          d • ((M : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) ^ j :=
        Matrix.toLin'.injective (LinearMap.ext fun v => by
          rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hYv])
      have hd0 : d ≠ 0 := by
        have hdetY : ((Y : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det ≠ 0 :=
          ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)).ne_zero
        intro hd
        apply hdetY
        rw [hYmat, hd, zero_smul, Matrix.det_zero]
      refine ⟨Units.mk0 d hd0, j, Units.ext ?_⟩
      rw [hYmat, Units.val_mul, GeneralLinearGroup.coe_scalar, scalar_mul_eq_smul',
        Units.val_pow_eq_pow_val, Units.val_mk0]
    · exact (not_commute_specialBlock_of_twist hKc H0 a hac hself htop hmult ht3 ht1 hYx
        hcommS).elim

end Block

end TableBU63

end CFSG.StandardType
