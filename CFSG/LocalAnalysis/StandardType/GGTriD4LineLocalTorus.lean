module

public import CFSG.LocalAnalysis.StandardType.GGTriD4LineModel
public import Mathlib

public section

namespace CFSG.StandardType

open Polynomial IntermediateField Matrix

private lemma triD4LineMk_congr (k K : Type) [Field k] [Field K] [Algebra k K]
    {g : GL (Fin 3) k} {c : Kˣ}
    (h h' : Matrix.GeneralLinearGroup.det g = Units.map (Algebra.norm k (S := K)) c) :
    triD4LineMk k K g c h = triD4LineMk k K g c h' := by
  simp [triD4LineMk]

private lemma triD4LineMk_eq_of_eq (k K : Type) [Field k] [Field K] [Algebra k K]
    {g g' : GL (Fin 3) k} {c c' : Kˣ} (hg : g = g') (hc : c = c')
    (h : Matrix.GeneralLinearGroup.det g = Units.map (Algebra.norm k (S := K)) c)
    (h' : Matrix.GeneralLinearGroup.det g' = Units.map (Algebra.norm k (S := K)) c') :
    triD4LineMk k K g c h = triD4LineMk k K g' c' h' := by
  subst hg
  subst hc
  exact triD4LineMk_congr k K h h'

private lemma triD4Line_algHom_det_eq_norm (k K : Type) [Field k] [Field K] [Algebra k K]
    [Finite K] (hdeg : Module.finrank k K = 3) (φ : K →ₐ[k] Matrix (Fin 3) (Fin 3) k) (t : K) :
    (φ t).det = Algebra.norm k t := by
  let v₀ : Fin 3 → k := Pi.single 0 1
  have hv₀ : v₀ ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    simp [v₀] at h0
  let Ψ : K →ₗ[k] (Fin 3 → k) :=
    { toFun := fun x => φ x *ᵥ v₀
      map_add' := by intro x y; rw [map_add, Matrix.add_mulVec]
      map_smul' := by
        intro a x
        rw [map_smul, Matrix.smul_mulVec]
        rfl }
  have hΨ_apply : ∀ x, Ψ x = φ x *ᵥ v₀ := fun x => rfl
  have hΨinj : Function.Injective Ψ := by
    intro x y hxy
    rw [← sub_eq_zero]
    by_contra hne
    have hz : Ψ (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hzv : φ (x - y) *ᵥ v₀ = 0 := by rw [← hΨ_apply]; exact hz
    have hzφ : φ ((x - y)⁻¹) * φ (x - y) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hne, map_one]
    have : v₀ = 0 := by
      calc v₀ = (1 : Matrix (Fin 3) (Fin 3) k) *ᵥ v₀ := by rw [Matrix.one_mulVec]
        _ = (φ ((x - y)⁻¹) * φ (x - y)) *ᵥ v₀ := by rw [hzφ]
        _ = φ ((x - y)⁻¹) *ᵥ (φ (x - y) *ᵥ v₀) := by rw [Matrix.mulVec_mulVec]
        _ = 0 := by rw [hzv, Matrix.mulVec_zero]
    exact hv₀ this
  haveI : FiniteDimensional k K := inferInstance
  have hdim : Module.finrank k K = Module.finrank k (Fin 3 → k) := by
    rw [hdeg, Module.finrank_fintype_fun_eq_card]
    simp
  have hΨsurj : Function.Surjective Ψ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hΨinj
  let Ψe : K ≃ₗ[k] (Fin 3 → k) := LinearEquiv.ofBijective Ψ ⟨hΨinj, hΨsurj⟩
  have hΨe_apply : ∀ x, Ψe x = φ x *ᵥ v₀ := by
    intro x
    change Ψ x = φ x *ᵥ v₀
    exact hΨ_apply x
  let b : Module.Basis (Fin 3) k K := Module.Basis.ofEquivFun Ψe
  have hb_repr : ∀ (x : K) (i : Fin 3), b.repr x i = Ψe x i := by
    intro x i
    rw [← Module.Basis.equivFun_apply, Module.Basis.equivFun_ofEquivFun]
  have hb_apply : ∀ i : Fin 3, b i = Ψe.symm (Pi.single i 1) := by
    intro i
    rw [Module.Basis.coe_ofEquivFun]
  have hbj : ∀ j : Fin 3, φ (b j) *ᵥ v₀ = Pi.single j 1 := by
    intro j
    rw [← hΨe_apply, hb_apply, LinearEquiv.apply_symm_apply]
  have hleft : Algebra.leftMulMatrix b t = φ t := by
    ext i j
    calc (Algebra.leftMulMatrix b t) i j
        = b.repr (t * b j) i := Algebra.leftMulMatrix_eq_repr_mul b t i j
      _ = Ψe (t * b j) i := by rw [hb_repr]
      _ = (φ (t * b j) *ᵥ v₀) i := by rw [hΨe_apply]
      _ = ((φ t * φ (b j)) *ᵥ v₀) i := by rw [map_mul]
      _ = (φ t *ᵥ (φ (b j) *ᵥ v₀)) i := by rw [Matrix.mulVec_mulVec]
      _ = (φ t *ᵥ Pi.single j 1) i := by rw [hbj]
      _ = (φ t) i j := by simp [Matrix.mulVec_single, Matrix.col_apply]
  rw [← hleft]
  exact (Algebra.norm_eq_matrix_det b t).symm

private lemma triD4Line_algebraMap_matrix_eq_scalar (k : Type) [Field k] (a : k) :
    algebraMap k (Matrix (Fin 3) (Fin 3) k) a = Matrix.scalar (Fin 3) a := by
  rw [Matrix.algebraMap_eq_diagonal]
  rfl

private lemma triD4Line_unitsMap_algebraMap_eq_scalar (k K : Type) [Field k] [Field K]
    [Algebra k K] (φ : K →ₐ[k] Matrix (Fin 3) (Fin 3) k) (μ : kˣ) :
    Units.map φ.toMonoidHom (Units.map (algebraMap k K).toMonoidHom μ) =
      Matrix.GeneralLinearGroup.scalar (Fin 3) μ := by
  apply Units.ext
  simp only [Units.coe_map]
  change φ (algebraMap k K (μ : k)) = Matrix.scalar (Fin 3) (μ : k)
  rw [AlgHom.commutes φ (μ : k)]
  exact triD4Line_algebraMap_matrix_eq_scalar k (μ : k)

private lemma triD4LineMk_mul_comm (k K : Type) [Field k] [Field K] [Algebra k K]
    (ψ : Kˣ →* GL (Fin 3) k) (t d t' d' : Kˣ)
    (h : Matrix.GeneralLinearGroup.det (ψ t) = Units.map (Algebra.norm k (S := K)) d)
    (h' : Matrix.GeneralLinearGroup.det (ψ t') = Units.map (Algebra.norm k (S := K)) d') :
    triD4LineMk k K (ψ t) d h * triD4LineMk k K (ψ t') d' h' =
      triD4LineMk k K (ψ t') d' h' * triD4LineMk k K (ψ t) d h := by
  have h1 : Matrix.GeneralLinearGroup.det (ψ t * ψ t') =
      Units.map (Algebra.norm k (S := K)) (d * d') := by
    rw [map_mul, map_mul, h, h']
  have h2 : Matrix.GeneralLinearGroup.det (ψ t' * ψ t) =
      Units.map (Algebra.norm k (S := K)) (d' * d) := by
    rw [map_mul, map_mul, h', h]
  rw [triD4LineMk_mul k K (ψ t) (ψ t') d d' h h' h1,
      triD4LineMk_mul k K (ψ t') (ψ t) d' d h' h h2]
  exact triD4LineMk_eq_of_eq k K
    (by rw [← MonoidHom.map_mul ψ t t', ← MonoidHom.map_mul ψ t' t, mul_comm t t'])
    (mul_comm d d') h1 h2

theorem triD4Line_exists_torus (k K : Type) [Field k] [Field K] [Algebra k K] [Finite K]
    (hdeg : Module.finrank k K = 3) (e₁ : TriD4LineX k K) (he₁ : e₁ ^ 3 = 1)
    (hN : e₁ ∉ triD4LineN0 k K) :
    ∃ T : Subgroup (TriD4LineX k K), T ≤ Subgroup.centralizer {e₁} ∧
      Nonempty (T ≃* Multiplicative (ZMod (Nat.card k ^ 2 + Nat.card k + 1)) ×
        Multiplicative (ZMod (Nat.card k ^ 2 + Nat.card k + 1))) := by
  classical
  haveI : Finite k := Finite.of_injective (algebraMap k K) (algebraMap k K).injective
  haveI : Fintype k := Fintype.ofFinite k
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨g₁, c₁, h₁, rfl⟩ := triD4LineMk_surjective k K e₁
  have hpow : Matrix.GeneralLinearGroup.det (g₁ ^ 3) =
      Units.map (Algebra.norm k (S := K)) (c₁ ^ 3) := by
    rw [map_pow, h₁, map_pow]
  have h3 : triD4LineMk k K (g₁ ^ 3) (c₁ ^ 3) hpow = 1 := by
    rw [← triD4LineMk_pow k K g₁ c₁ h₁ 3 hpow, he₁]
  obtain ⟨ν, hgν, hcν⟩ := (triD4LineMk_eq_one_iff k K (g₁ ^ 3) (c₁ ^ 3) hpow).mp h3
  have hc₁_ne : (c₁ : K) ∉ Set.range (algebraMap k K) := by
    rintro ⟨a, ha⟩
    have ha0 : a ≠ 0 := by
      intro h0
      have hzero : (c₁ : K) = 0 := by rw [← ha, h0, map_zero]
      exact c₁.ne_zero hzero
    refine hN ((triD4LineMk_mem_N0_iff k K hdeg g₁ c₁ h₁).2 ⟨Units.mk0 a ha0, ?_⟩)
    ext
    rw [Units.coe_map, Units.val_mk0]
    exact ha.symm
  have hint : IsIntegral k (c₁ : K) := Algebra.IsIntegral.isIntegral _
  have hprime : Nat.Prime (Module.finrank k K) := by rw [hdeg]; norm_num
  haveI : IsSimpleOrder (IntermediateField k K) :=
    IntermediateField.isSimpleOrder_of_finrank_prime k K hprime
  have hbot : k⟮(c₁ : K)⟯ ≠ ⊥ := by
    intro h
    have hmem : (c₁ : K) ∈ (⊥ : IntermediateField k K) := by
      rw [← h]; exact IntermediateField.mem_adjoin_simple_self k _
    rw [IntermediateField.mem_bot] at hmem
    exact hc₁_ne hmem
  have htop : k⟮(c₁ : K)⟯ = ⊤ := by
    rcases eq_bot_or_eq_top k⟮(c₁ : K)⟯ with h | h
    · exact absurd h hbot
    · exact h
  have hmin : minpoly k (c₁ : K) = X ^ 3 - C (ν : k) := by
    have hcνK : (c₁ : K) ^ 3 = algebraMap k K (ν : k) := by
      have := congrArg (fun u : Kˣ => (u : K)) hcν
      simpa using this
    have hp_dvd : minpoly k (c₁ : K) ∣ X ^ 3 - C (ν : k) := by
      apply minpoly.dvd
      rw [Polynomial.aeval_sub, Polynomial.aeval_X_pow, Polynomial.aeval_C, hcνK, sub_self]
    have hdeg_min : (minpoly k (c₁ : K)).natDegree = 3 := by
      rw [← IntermediateField.adjoin.finrank hint, htop, IntermediateField.finrank_top', hdeg]
    have hq_monic : (X ^ 3 - C (ν : k)).Monic := Polynomial.monic_X_pow_sub_C _ (by norm_num)
    have := Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hq_monic hp_dvd
      (by rw [Polynomial.natDegree_X_pow_sub_C, hdeg_min])
    exact this.symm
  have hadjoin : Algebra.adjoin k ({(c₁ : K)} : Set K) = ⊤ :=
    (IntermediateField.adjoin_eq_top_iff).mp htop
  let pb : PowerBasis k K := PowerBasis.ofAdjoinEqTop hint hadjoin
  have hpb_gen : pb.gen = (c₁ : K) := PowerBasis.ofAdjoinEqTop_gen hint hadjoin
  have hgν' : (g₁ : Matrix (Fin 3) (Fin 3) k) ^ 3 = Matrix.scalar (Fin 3) (ν : k) := by
    have := congrArg (fun u : GL (Fin 3) k => (u : Matrix (Fin 3) (Fin 3) k)) hgν
    simpa using this
  have hy : Polynomial.aeval (g₁ : Matrix (Fin 3) (Fin 3) k) (minpoly k pb.gen) = 0 := by
    rw [hpb_gen, hmin, Polynomial.aeval_sub, Polynomial.aeval_X_pow, Polynomial.aeval_C, hgν',
      triD4Line_algebraMap_matrix_eq_scalar, sub_self]
  let φ : K →ₐ[k] Matrix (Fin 3) (Fin 3) k := pb.lift (g₁ : Matrix (Fin 3) (Fin 3) k) hy
  have hφc : φ (c₁ : K) = (g₁ : Matrix (Fin 3) (Fin 3) k) := by
    rw [← hpb_gen]
    exact PowerBasis.lift_gen pb _ hy
  let ψ : Kˣ →* GL (Fin 3) k := Units.map φ.toMonoidHom
  have hφdet : ∀ t : Kˣ, Matrix.GeneralLinearGroup.det (ψ t) =
      Units.map (Algebra.norm k (S := K)) t := by
    intro t
    apply Units.ext
    change (ψ t : Matrix (Fin 3) (Fin 3) k).det = Algebra.norm k (t : K)
    rw [Units.coe_map]
    exact triD4Line_algHom_det_eq_norm k K hdeg φ (t : K)
  have hψc : ψ c₁ = g₁ := Units.ext hφc
  let Nm : Kˣ →* kˣ := Units.map (Algebra.norm k (S := K))
  have hφdet_one : ∀ u : Nm.ker, Matrix.GeneralLinearGroup.det (ψ (u : Kˣ)) =
      Units.map (Algebra.norm k (S := K)) (1 : Kˣ) := by
    intro u
    rw [hφdet (u : Kˣ), u.2, map_one]
  let Φ₂map : Kˣ →* TriD4LineX k K :=
    MonoidHom.mk' (fun d => triD4LineMk k K (ψ d) d (hφdet d)) (by
      intro d d'
      have h'' : Matrix.GeneralLinearGroup.det (ψ d * ψ d') =
          Units.map (Algebra.norm k (S := K)) (d * d') := by
        rw [map_mul, map_mul, hφdet d, hφdet d']
      rw [triD4LineMk_mul k K (ψ d) (ψ d') d d' (hφdet d) (hφdet d') h'']
      exact triD4LineMk_eq_of_eq k K (MonoidHom.map_mul ψ d d') rfl (hφdet (d * d')) h'')
  have hΦ₂map_apply : ∀ d : Kˣ,
      Φ₂map d = triD4LineMk k K (ψ d) d (hφdet d) := fun d => rfl
  let H : Subgroup Kˣ := (Units.map (algebraMap k K).toMonoidHom).range
  have hH_le : H ≤ Φ₂map.ker := by
    rintro x ⟨μ, rfl⟩
    rw [MonoidHom.mem_ker, hΦ₂map_apply]
    refine (triD4LineMk_eq_one_iff k K _ _ _).2 ⟨μ, ?_, rfl⟩
    exact triD4Line_unitsMap_algebraMap_eq_scalar k K φ μ
  haveI : H.Normal := inferInstance
  let Q := Kˣ ⧸ H
  let Φ₂ : Q →* TriD4LineX k K := QuotientGroup.lift H Φ₂map hH_le
  have hΦ₂_apply : ∀ d : Kˣ,
      Φ₂ (QuotientGroup.mk d) = triD4LineMk k K (ψ d) d (hφdet d) := by
    intro d
    rw [QuotientGroup.lift_mk, hΦ₂map_apply]
  let Φ₁ : Nm.ker →* TriD4LineX k K :=
    MonoidHom.mk' (fun u => triD4LineMk k K (ψ (u : Kˣ)) 1 (hφdet_one u)) (by
      intro u v
      have h'' : Matrix.GeneralLinearGroup.det (ψ (u : Kˣ) * ψ (v : Kˣ)) =
          Units.map (Algebra.norm k (S := K)) ((1 : Kˣ) * 1) := by
        rw [map_mul, map_mul, hφdet_one u, hφdet_one v]
      rw [triD4LineMk_mul k K (ψ (u : Kˣ)) (ψ (v : Kˣ)) 1 1
        (hφdet_one u) (hφdet_one v) h'']
      exact triD4LineMk_eq_of_eq k K (MonoidHom.map_mul ψ (u : Kˣ) (v : Kˣ))
        (one_mul (1 : Kˣ)).symm (hφdet_one (u * v)) h'')
  have hΦ₁_apply : ∀ u : Nm.ker,
      Φ₁ u = triD4LineMk k K (ψ (u : Kˣ)) 1 (hφdet_one u) := fun u => rfl
  have hcomm : ∀ (u : Nm.ker) (q : Q), Commute (Φ₁ u) (Φ₂ q) := by
    intro u q
    refine QuotientGroup.induction_on q ?_
    intro d
    rw [hΦ₁_apply, hΦ₂_apply]
    exact triD4LineMk_mul_comm k K ψ (u : Kˣ) 1 d d (hφdet_one u) (hφdet d)
  let Φ : Nm.ker × Q →* TriD4LineX k K := MonoidHom.noncommCoprod Φ₁ Φ₂ hcomm
  have hΦ_apply : ∀ (u : Nm.ker) (q : Q), Φ (u, q) = Φ₁ u * Φ₂ q :=
    fun u q => MonoidHom.noncommCoprod_apply _ _ _ _
  have hΦker : ∀ p : Nm.ker × Q, Φ p = 1 → p = 1 := by
    rintro ⟨u, q⟩ hp
    obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective q
    have hφdet_ud : Matrix.GeneralLinearGroup.det (ψ ((u : Kˣ) * d)) =
        Units.map (Algebra.norm k (S := K)) d := by
      rw [hφdet ((u : Kˣ) * d), map_mul, u.2, one_mul]
    have hval : Φ (u, (QuotientGroup.mk d : Q)) =
        triD4LineMk k K (ψ ((u : Kˣ) * d)) d hφdet_ud := by
      rw [hΦ_apply, hΦ₁_apply, hΦ₂_apply]
      have h'' : Matrix.GeneralLinearGroup.det (ψ (u : Kˣ) * ψ d) =
          Units.map (Algebra.norm k (S := K)) ((1 : Kˣ) * d) := by
        rw [map_mul, map_mul, hφdet_one u, hφdet d]
      rw [triD4LineMk_mul k K (ψ (u : Kˣ)) (ψ d) 1 d (hφdet_one u) (hφdet d) h'']
      exact triD4LineMk_eq_of_eq k K ((MonoidHom.map_mul ψ (u : Kˣ) d).symm)
        (one_mul d) h'' hφdet_ud
    have hp' : triD4LineMk k K (ψ ((u : Kˣ) * d)) d hφdet_ud = 1 := by
      rw [← hval]; exact hp
    obtain ⟨μ, hscalar, hd⟩ :=
      (triD4LineMk_eq_one_iff k K (ψ ((u : Kˣ) * d)) d hφdet_ud).mp hp'
    have hq1 : (QuotientGroup.mk d : Q) = 1 := by
      rw [QuotientGroup.eq_one_iff]
      exact ⟨μ, hd.symm⟩
    have hψinj : Function.Injective ψ :=
      Units.map_injective (RingHom.injective φ.toRingHom)
    have hu1 : u = 1 := by
      have heq : ψ ((u : Kˣ) * d) = ψ (Units.map (algebraMap k K).toMonoidHom μ) := by
        rw [hscalar, triD4Line_unitsMap_algebraMap_eq_scalar k K φ μ]
      have heq' : (u : Kˣ) * d = Units.map (algebraMap k K).toMonoidHom μ := hψinj heq
      have hcancel : (u : Kˣ) * d = 1 * d := by rw [one_mul, heq', hd]
      exact Subtype.ext (mul_right_cancel hcancel)
    exact Prod.ext hu1 hq1
  have hΦinj : Function.Injective Φ := by
    intro p q hpq
    have h1 : Φ (p * q⁻¹) = 1 := by rw [map_mul, map_inv, hpq, mul_inv_cancel]
    exact mul_inv_eq_one.mp (hΦker _ h1)
  have hq2 : 2 ≤ Nat.card k := by
    have h := Fintype.one_lt_card (α := k)
    rw [← Nat.card_eq_fintype_card] at h
    omega
  have hqpos : 0 < Nat.card k - 1 := by omega
  have hfac0 : Nat.card k ^ 3 - 1 =
      (Nat.card k ^ 2 + Nat.card k + 1) * (Nat.card k - 1) := by
    rw [Nat.mul_sub_left_distrib, mul_one]
    have h : (Nat.card k ^ 2 + Nat.card k + 1) * Nat.card k =
        Nat.card k ^ 3 + Nat.card k ^ 2 + Nat.card k := by ring
    rw [h]
    omega
  have hfac : Nat.card k ^ 3 - 1 =
      (Nat.card k - 1) * (Nat.card k ^ 2 + Nat.card k + 1) :=
    hfac0.trans (mul_comm _ _)
  have hcardK : Nat.card K = Nat.card k ^ 3 := by
    rw [Nat.card_eq_fintype_card (α := K), Nat.card_eq_fintype_card (α := k),
      Module.card_eq_pow_finrank (K := k) (V := K), hdeg]
  have hcardKunits : Nat.card Kˣ = Nat.card k ^ 3 - 1 := by
    rw [Nat.card_units, hcardK]
  have hcardkunits : Nat.card kˣ = Nat.card k - 1 := Nat.card_units k
  have hcard_ker : Nat.card Nm.ker * (Nat.card k - 1) = Nat.card k ^ 3 - 1 := by
    have h := Subgroup.card_ker_mul_card_of_surjective
      (FiniteField.unitsMap_norm_surjective k K)
    rw [hcardkunits, hcardKunits] at h
    exact h
  have hcard_ker' : Nat.card Nm.ker = Nat.card k ^ 2 + Nat.card k + 1 :=
    Nat.mul_right_cancel hqpos (hcard_ker.trans hfac0)
  have hcardH : Nat.card H = Nat.card k - 1 := by
    have hinj : Function.Injective (Units.map (algebraMap k K).toMonoidHom) :=
      Units.map_injective (algebraMap k K).injective
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hcardkunits]
  have hcardQ : Nat.card Q = Nat.card k ^ 2 + Nat.card k + 1 := by
    have h1 : Nat.card H * Nat.card Q = Nat.card Kˣ := by
      rw [← Subgroup.index_eq_card H]
      exact Subgroup.card_mul_index H
    rw [hcardH, hcardKunits] at h1
    exact Nat.mul_left_cancel hqpos (h1.trans hfac)
  haveI : Finite Kˣ := Finite.of_injective (fun u : Kˣ => (u : K)) Units.val_injective
  haveI : IsCyclic Kˣ := instIsCyclicUnitsOfFinite
  haveI : IsCyclic Nm.ker := Subgroup.isCyclic Nm.ker
  haveI : IsCyclic Q :=
    isCyclic_of_surjective (QuotientGroup.mk' H) (QuotientGroup.mk'_surjective H)
  have eK : Nm.ker ≃* Multiplicative (ZMod (Nat.card k ^ 2 + Nat.card k + 1)) := by
    rw [← hcard_ker']
    exact (zmodCyclicMulEquiv (inferInstance : IsCyclic Nm.ker)).symm
  have eQ : Q ≃* Multiplicative (ZMod (Nat.card k ^ 2 + Nat.card k + 1)) := by
    rw [← hcardQ]
    exact (zmodCyclicMulEquiv (inferInstance : IsCyclic Q)).symm
  let T : Subgroup (TriD4LineX k K) := Φ.range
  refine ⟨T, ?_, ?_⟩
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    obtain ⟨p, rfl⟩ := MonoidHom.mem_range.mp hx
    obtain ⟨u, q⟩ := p
    have he₁' : triD4LineMk k K g₁ c₁ h₁ =
        triD4LineMk k K (ψ c₁) c₁ (hφdet c₁) :=
      triD4LineMk_eq_of_eq k K hψc.symm rfl h₁ (hφdet c₁)
    have hc1 : Commute (triD4LineMk k K g₁ c₁ h₁) (Φ₁ u) := by
      rw [he₁', hΦ₁_apply]
      exact triD4LineMk_mul_comm k K ψ c₁ c₁ (u : Kˣ) 1 (hφdet c₁) (hφdet_one u)
    have hc2 : Commute (triD4LineMk k K g₁ c₁ h₁) (Φ₂ q) := by
      obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective q
      rw [he₁', hΦ₂_apply]
      exact triD4LineMk_mul_comm k K ψ c₁ c₁ d d (hφdet c₁) (hφdet d)
    rw [hΦ_apply]
    exact hc1.mul_right hc2
  · exact ⟨(MonoidHom.ofInjective hΦinj).symm.trans (MulEquiv.prodCongr eK eQ)⟩

end CFSG.StandardType
