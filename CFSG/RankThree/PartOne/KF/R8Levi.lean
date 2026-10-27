module

public import CFSG.RankThree.PartOne.KF.R8Final
public import CFSG.RankThree.PartOne.KF.R5Levi

public section

namespace CFSG.RankThree.PartOne.KFQ

open CFSG CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Unitary

variable {K : Type} [Field K] [Finite K] [CharP K 2]

instance instCharPQext : CharP (Qext K) 2 :=
  charP_of_injective_algebraMap (algebraMap K (Qext K)).injective 2

@[expose] noncomputable def lift8 (X : Matrix.SpecialLinearGroup (Fin 2) (Qext K)) :
    QV K (Fin 2) ≃ₗ[K] QV K (Fin 2) where
  toFun v := (X : Matrix (Fin 2) (Fin 2) (Qext K)).mulVec v
  map_add' v w := Matrix.mulVec_add _ v w
  map_smul' c v := by
    simp only [RingHom.id_apply]
    exact Matrix.mulVec_smul _ c v
  invFun v := ((X⁻¹ : Matrix.SpecialLinearGroup (Fin 2) (Qext K)) :
    Matrix (Fin 2) (Fin 2) (Qext K)).mulVec v
  left_inv v := by
    simp only [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  right_inv v := by
    simp only [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

theorem lift8_apply (X : Matrix.SpecialLinearGroup (Fin 2) (Qext K)) (v : QV K (Fin 2)) :
    lift8 X v = (X : Matrix (Fin 2) (Fin 2) (Qext K)).mulVec v := rfl

@[expose] noncomputable def blk8 :
    Matrix.SpecialLinearGroup (Fin 2) (Qext K) →* (QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) where
  toFun := lift8
  map_one' := by
    ext v i
    simp [lift8_apply]
  map_mul' X Y := by
    refine LinearEquiv.ext fun v => ?_
    show ((X * Y : Matrix.SpecialLinearGroup (Fin 2) (Qext K)) :
        Matrix (Fin 2) (Fin 2) (Qext K)).mulVec v =
      (X : Matrix (Fin 2) (Fin 2) (Qext K)).mulVec
        ((Y : Matrix (Fin 2) (Fin 2) (Qext K)).mulVec v)
    rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]

theorem blk8_apply (X : Matrix.SpecialLinearGroup (Fin 2) (Qext K)) (v : QV K (Fin 2)) :
    blk8 X v = (X : Matrix (Fin 2) (Fin 2) (Qext K)).mulVec v := rfl

theorem det_blk8 (X : Matrix.SpecialLinearGroup (Fin 2) (Qext K)) :
    LinearEquiv.det (blk8 X : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) = 1 := by
  apply Units.ext
  rw [LinearEquiv.coe_det]
  have h : ((blk8 X : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) : QV K (Fin 2) →ₗ[K] QV K (Fin 2)) =
      (Matrix.toLin' (X : Matrix (Fin 2) (Fin 2) (Qext K))).restrictScalars K :=
    LinearMap.ext fun v => rfl
  rw [h, LinearMap.det_restrictScalars, LinearMap.det_toLin', X.2, map_one]
  simp

@[expose] noncomputable def blk8M :
    Matrix.SpecialLinearGroup (Fin 2) (Qext K) →* ↥(M8 K) :=
  (blk8 (K := K)).codRestrict (M8 K) (fun X => (mem_M8_iff _).2 (det_blk8 X))

theorem blk8M_apply (X : Matrix.SpecialLinearGroup (Fin 2) (Qext K)) (v : QV K (Fin 2)) :
    ((blk8M X : ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) v =
      (X : Matrix (Fin 2) (Fin 2) (Qext K)).mulVec v := rfl

theorem blk8M_injective : Function.Injective (blk8M (K := K)) := by
  intro X Y h
  apply Subtype.ext
  ext i j
  have h1 := congrArg (fun g : ↥(M8 K) =>
    (g : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) (Pi.single j 1) i) h
  simpa [blk8M_apply, Matrix.mulVec_single_one] using h1

theorem span_one_z {z : (Qext K)ˣ} (hz : (z : Qext K) ∉ Set.range (algebraMap K (Qext K)))
    (a : Qext K) : ∃ s t : K, a = s • (1 : Qext K) + t • (z : Qext K) := by
  have hli : LinearIndependent K ![(1 : Qext K), (z : Qext K)] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h0 : algebraMap K (Qext K) s + algebraMap K (Qext K) t * (z : Qext K) = 0 := by
      simpa [Algebra.smul_def] using hst
    by_cases ht : t = 0
    · subst ht
      rw [map_zero, zero_mul, add_zero] at h0
      exact ⟨(map_eq_zero _).1 h0, rfl⟩
    · exfalso
      apply hz
      have ht' : algebraMap K (Qext K) t ≠ 0 := (map_ne_zero _).2 ht
      refine ⟨-s / t, ?_⟩
      rw [map_div₀, map_neg, div_eq_iff ht']
      linear_combination -h0
  have hspan : Submodule.span K (Set.range ![(1 : Qext K), (z : Qext K)]) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by simp [finrank_qext])
  have hrange : Set.range ![(1 : Qext K), (z : Qext K)] = {1, (z : Qext K)} := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  have ha : a ∈ Submodule.span K (Set.range ![(1 : Qext K), (z : Qext K)]) := by
    rw [hspan]
    trivial
  rw [hrange, Submodule.mem_span_pair] at ha
  obtain ⟨s, t, hst⟩ := ha
  exact ⟨s, t, hst.symm⟩

theorem torusEquiv_scalar_apply (z : (Qext K)ˣ) (w : QV K (Fin 2)) :
    torusEquiv ![z, z] w = (z : Qext K) • w := by
  funext i
  fin_cases i <;> simp [torusEquiv_apply]

theorem smul_comm_of_commute {z : (Qext K)ˣ}
    (hz : (z : Qext K) ∉ Set.range (algebraMap K (Qext K)))
    {g : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)}
    (hg : g * torusEquiv ![z, z] = torusEquiv ![z, z] * g) (a : Qext K) (v : QV K (Fin 2)) :
    g (a • v) = a • g v := by
  obtain ⟨s, t, rfl⟩ := span_one_z hz a
  have hz' : g ((z : Qext K) • v) = (z : Qext K) • g v := by
    have := congrArg (fun h : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2) => h v) hg
    simpa [LinearEquiv.mul_apply, torusEquiv_scalar_apply] using this
  have e : ∀ w : QV K (Fin 2), (s • (1 : Qext K) + t • (z : Qext K)) • w =
      s • w + t • ((z : Qext K) • w) := by
    intro w
    funext i
    simp only [Pi.smul_apply, Pi.add_apply]
    simp only [smul_eq_mul, Algebra.smul_def]
    ring
  rw [e v, e (g v), map_add, map_smul, map_smul, hz']

@[expose] noncomputable def bM8 (z : (Qext K)ˣ) (hmem : torusEquiv ![z, z] ∈ M8 K) : ↥(M8 K) :=
  ⟨torusEquiv ![z, z], hmem⟩

@[expose] noncomputable def toK' (g : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2))
    (h : ∀ (a : Qext K) (v : QV K (Fin 2)), g (a • v) = a • g v) :
    QV K (Fin 2) ≃ₗ[Qext K] QV K (Fin 2) where
  toFun := g
  map_add' := map_add g
  map_smul' a v := h a v
  invFun := g.symm
  left_inv := g.left_inv
  right_inv := g.right_inv

theorem comm_of_mem_centralizer {z : (Qext K)ˣ} {hmem : torusEquiv ![z, z] ∈ M8 K}
    {g : ↥(M8 K)} (hg : g ∈ Subgroup.centralizer ({bM8 z hmem} : Set ↥(M8 K))) :
    (g : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) * torusEquiv ![z, z] =
      torusEquiv ![z, z] * (g : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) :=
  congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hg)

@[expose] noncomputable def phi8 {z : (Qext K)ˣ}
    (hz : (z : Qext K) ∉ Set.range (algebraMap K (Qext K)))
    (hmem : torusEquiv ![z, z] ∈ M8 K) :
    ↥(Subgroup.centralizer ({bM8 z hmem} : Set ↥(M8 K))) →* (Qext K)ˣ where
  toFun g := LinearEquiv.det (toK' ((g : ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2))
    (smul_comm_of_commute hz (comm_of_mem_centralizer g.2)))
  map_one' := by
    have : toK' ((((1 : ↥(Subgroup.centralizer ({bM8 z hmem} : Set ↥(M8 K)))) : ↥(M8 K)) :
        QV K (Fin 2) ≃ₗ[K] QV K (Fin 2))) (smul_comm_of_commute hz
          (comm_of_mem_centralizer (1 : ↥(Subgroup.centralizer
            ({bM8 z hmem} : Set ↥(M8 K)))).2)) = 1 := LinearEquiv.ext fun _ => rfl
    rw [this, map_one]
  map_mul' g h := by
    have : toK' ((((g * h : ↥(Subgroup.centralizer ({bM8 z hmem} : Set ↥(M8 K)))) : ↥(M8 K)) :
        QV K (Fin 2) ≃ₗ[K] QV K (Fin 2))) (smul_comm_of_commute hz
          (comm_of_mem_centralizer (g * h).2)) =
        toK' ((g : ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2))
          (smul_comm_of_commute hz (comm_of_mem_centralizer g.2)) *
        toK' ((h : ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2))
          (smul_comm_of_commute hz (comm_of_mem_centralizer h.2)) :=
      LinearEquiv.ext fun _ => rfl
    rw [this, map_mul]

theorem blk8M_mem_centralizer {z : (Qext K)ˣ} (hmem : torusEquiv ![z, z] ∈ M8 K)
    (X : Matrix.SpecialLinearGroup (Fin 2) (Qext K)) :
    blk8M X ∈ Subgroup.centralizer ({bM8 z hmem} : Set ↥(M8 K)) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  refine LinearEquiv.ext fun v => ?_
  show blk8 X (torusEquiv ![z, z] v) = torusEquiv ![z, z] (blk8 X v)
  rw [torusEquiv_scalar_apply, torusEquiv_scalar_apply, blk8_apply, blk8_apply,
    Matrix.mulVec_smul]

theorem ker_phi8 {z : (Qext K)ˣ} (hz : (z : Qext K) ∉ Set.range (algebraMap K (Qext K)))
    (hmem : torusEquiv ![z, z] ∈ M8 K) :
    (phi8 hz hmem).ker =
      (blk8M (K := K)).range.subgroupOf
        (Subgroup.centralizer ({bM8 z hmem} : Set ↥(M8 K))) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  have hg' := smul_comm_of_commute hz (comm_of_mem_centralizer g.2)
  constructor
  · intro h
    have hdet : LinearMap.det (toK' ((g : ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) hg' :
        QV K (Fin 2) →ₗ[Qext K] QV K (Fin 2)) = 1 := by
      have := congrArg (fun u : (Qext K)ˣ => (u : Qext K)) h
      simpa [phi8, LinearEquiv.coe_det] using this
    let X : Matrix (Fin 2) (Fin 2) (Qext K) :=
      LinearMap.toMatrix' (toK' ((g : ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) hg' :
        QV K (Fin 2) →ₗ[Qext K] QV K (Fin 2))
    have hX : X.det = 1 := by
      rw [LinearMap.det_toMatrix']
      exact hdet
    refine ⟨⟨X, hX⟩, ?_⟩
    apply Subtype.ext
    refine LinearEquiv.ext fun v => ?_
    show X.mulVec v = ((g : ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) v
    have := congrArg (fun f : QV K (Fin 2) →ₗ[Qext K] QV K (Fin 2) => f v)
      (Matrix.toLin'_toMatrix' (toK' ((g : ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) hg' :
        QV K (Fin 2) →ₗ[Qext K] QV K (Fin 2)))
    simp only [Matrix.toLin'_apply] at this
    exact this
  · rintro ⟨X, hX⟩
    apply Units.ext
    show ((LinearEquiv.det (toK' ((g : ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) hg') :
      (Qext K)ˣ) : Qext K) = 1
    rw [LinearEquiv.coe_det]
    have hlin : ((toK' ((g : ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) hg' :
        QV K (Fin 2) ≃ₗ[Qext K] QV K (Fin 2)) : QV K (Fin 2) →ₗ[Qext K] QV K (Fin 2)) =
        Matrix.toLin' (X : Matrix (Fin 2) (Fin 2) (Qext K)) := by
      refine LinearMap.ext fun v => ?_
      show ((g : ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) v = _
      rw [← hX]
      rfl
    rw [hlin, LinearMap.det_toLin', X.2]

theorem perfectResidual_centralizer_b8 (hK : 4 ≤ Nat.card (Qext K)) {z : (Qext K)ˣ}
    (hz : (z : Qext K) ∉ Set.range (algebraMap K (Qext K)))
    (hmem : torusEquiv ![z, z] ∈ M8 K) :
    inSubgroup perfectResidual (Subgroup.centralizer ({bM8 z hmem} : Set ↥(M8 K))) =
      (blk8M (K := K)).range := by
  have hq := CFSG.RankThree.CALinearPlane.isQuasisimple_SL_of_two_le (k := Qext K) (m := 2)
    le_rfl hK
  have hperf : Group.IsPerfect ↥((blk8M (K := K)).range) := by
    have := hq.1
    exact Group.IsPerfect.ofSurjective
      (f := (MonoidHom.ofInjective blk8M_injective).toMonoidHom)
      (MonoidHom.ofInjective blk8M_injective).surjective
  exact inSubgroup_perfectResidual_eq_of_ker (by
    rintro _ ⟨X, rfl⟩
    exact blk8M_mem_centralizer hmem X) hperf (phi8 hz hmem) (ker_phi8 hz hmem)

theorem isQuasisimple_perfectResidual_centralizer_b8 (hK : 4 ≤ Nat.card (Qext K))
    {z : (Qext K)ˣ} (hz : (z : Qext K) ∉ Set.range (algebraMap K (Qext K)))
    (hmem : torusEquiv ![z, z] ∈ M8 K) :
    IsQuasisimple ↥(inSubgroup perfectResidual
      (Subgroup.centralizer ({bM8 z hmem} : Set ↥(M8 K)))) := by
  rw [perfectResidual_centralizer_b8 hK hz hmem]
  exact isQuasisimple_of_mulEquiv (MonoidHom.ofInjective blk8M_injective)
    (CFSG.RankThree.CALinearPlane.isQuasisimple_SL_of_two_le (k := Qext K) (m := 2) le_rfl hK)

theorem card_center_range_blk8M :
    Nat.card (Subgroup.center ↥((blk8M (K := K)).range)) = 1 := by
  rw [← card_center_mulEquiv (MonoidHom.ofInjective blk8M_injective)]
  exact card_center_SL_two

theorem mem_T8_iff {p : ℕ} {g : ↥(M8 K)} :
    g ∈ T8 p K ↔ ∃ a b : (Qext K)ˣ, a ^ p = 1 ∧ b ^ p = 1 ∧
      (g : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) = torusEquiv ![a, b] := by
  rw [T8, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨(v.1 : rootsOfUnity p (Qext K)), (v.2 : rootsOfUnity p (Qext K)),
      (mem_rootsOfUnity p _).1 v.1.2, (mem_rootsOfUnity p _).1 v.2.2, ?_⟩
    rw [← hv]
    rfl
  · rintro ⟨a, b, ha, hb, h⟩
    refine ⟨(⟨a, (mem_rootsOfUnity p _).2 ha⟩, ⟨b, (mem_rootsOfUnity p _).2 hb⟩), ?_⟩
    rw [h]
    rfl

theorem T8_pow_eq_one {p : ℕ} {g : ↥(M8 K)} (hg : g ∈ T8 p K) : g ^ p = 1 := by
  obtain ⟨v, hv⟩ := Subgroup.mem_subgroupOf.mp hg
  apply Subtype.ext
  show ((g : ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) ^ p = 1
  rw [← hv]
  exact d8Emb_pow v

theorem bM8_mem_T8 {p : ℕ} {z : (Qext K)ˣ} (hmem : torusEquiv ![z, z] ∈ M8 K) (hz : z ^ p = 1) :
    bM8 z hmem ∈ T8 p K :=
  mem_T8_iff.2 ⟨z, z, hz, hz, rfl⟩

@[expose] noncomputable def rho8 (K : Type) [Field K] [Finite K] [CharP K 2] :
    (Qext K)ˣ →* ↥(M8 K) :=
  (blk8M (K := K)).comp (diag2Hom (Qext K))

theorem rho8_injective : Function.Injective (rho8 K) :=
  blk8M_injective.comp (diag2Hom_injective _)

theorem coe_rho8 (a : (Qext K)ˣ) :
    ((rho8 K a : ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) = torusEquiv ![a, a⁻¹] := by
  refine LinearEquiv.ext fun v => ?_
  have h : ((rho8 K a : ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) v =
      ((diag2 a : Matrix.SpecialLinearGroup (Fin 2) (Qext K)) :
        Matrix (Fin 2) (Fin 2) (Qext K)).mulVec v := rfl
  rw [h]
  funext i
  fin_cases i <;> simp [diag2, Matrix.mulVec_diagonal, torusEquiv_apply]

theorem rho8_mem_range (a : (Qext K)ˣ) : (rho8 K a : ↥(M8 K)) ∈ (blk8M (K := K)).range :=
  ⟨diag2 a, rfl⟩

theorem rho8_mem_T8 {p : ℕ} {a : (Qext K)ˣ} (ha : a ^ p = 1) : (rho8 K a : ↥(M8 K)) ∈ T8 p K :=
  mem_T8_iff.2 ⟨a, a⁻¹, ha, by rw [inv_pow, ha, inv_one], coe_rho8 a⟩

theorem T8_inf_range_eq (p : ℕ) :
    T8 p K ⊓ (blk8M (K := K)).range = (rootsOfUnity p (Qext K)).map (rho8 K) := by
  ext g
  constructor
  · rintro ⟨hgT, X, hX⟩
    obtain ⟨a, b, ha, hb, hab⟩ := mem_T8_iff.1 hgT
    have hev : ∀ v : QV K (Fin 2),
        (X : Matrix (Fin 2) (Fin 2) (Qext K)).mulVec v = torusEquiv ![a, b] v := by
      intro v
      have h1 := congrArg (fun h : ↥(M8 K) => (h : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) v) hX
      rw [← hab]
      exact h1
    have e00 : (X : Matrix (Fin 2) (Fin 2) (Qext K)) 0 0 = a := by
      simpa [Matrix.mulVec_single_one, torusEquiv_apply] using congrFun (hev (Pi.single 0 1)) 0
    have e10 : (X : Matrix (Fin 2) (Fin 2) (Qext K)) 1 0 = 0 := by
      simpa [Matrix.mulVec_single_one, torusEquiv_apply] using congrFun (hev (Pi.single 0 1)) 1
    have e01 : (X : Matrix (Fin 2) (Fin 2) (Qext K)) 0 1 = 0 := by
      simpa [Matrix.mulVec_single_one, torusEquiv_apply] using congrFun (hev (Pi.single 1 1)) 0
    have e11 : (X : Matrix (Fin 2) (Fin 2) (Qext K)) 1 1 = b := by
      simpa [Matrix.mulVec_single_one, torusEquiv_apply] using congrFun (hev (Pi.single 1 1)) 1
    have hdet : (X : Matrix (Fin 2) (Fin 2) (Qext K)).det = 1 := X.2
    rw [Matrix.det_fin_two, e00, e11, e01, e10, mul_zero, sub_zero] at hdet
    have hba : b = a⁻¹ := eq_inv_of_mul_eq_one_right (Units.ext hdet)
    refine ⟨a, (mem_rootsOfUnity p _).2 ha, ?_⟩
    apply Subtype.ext
    rw [coe_rho8, hab, hba]
  · rintro ⟨a, ha, rfl⟩
    exact ⟨rho8_mem_T8 ((mem_rootsOfUnity p _).1 ha), rho8_mem_range a⟩

theorem card_T8_inf_range {p : ℕ} (hp : 0 < p) (hζ : ∃ ζ : (Qext K)ˣ, IsPrimitiveRoot ζ p) :
    Nat.card ↥(T8 p K ⊓ (blk8M (K := K)).range) = p := by
  have : NeZero p := ⟨hp.ne'⟩
  obtain ⟨ζ, hζ⟩ := hζ
  rw [T8_inf_range_eq, Subgroup.card_map_of_injective rho8_injective]
  exact IsPrimitiveRoot.card_rootsOfUnity (IsPrimitiveRoot.coe_units_iff.mpr hζ)

@[expose] noncomputable def rootU8 (K : Type) [Field K] [Finite K] [CharP K 2] :
    Subgroup ↥(M8 K) :=
  ((blk8M (K := K)).comp (tr2Hom (Qext K))).range

theorem mem_rootU8_iff {g : ↥(M8 K)} : g ∈ rootU8 K ↔ ∃ c : Qext K, g = blk8M (tr2 c) :=
  ⟨fun ⟨c, hc⟩ => ⟨Multiplicative.toAdd c, hc.symm⟩,
    fun ⟨c, hc⟩ => ⟨Multiplicative.ofAdd c, hc.symm⟩⟩

theorem blk8M_tr2_mem_rootU8 (c : Qext K) : (blk8M (tr2 c) : ↥(M8 K)) ∈ rootU8 K :=
  mem_rootU8_iff.2 ⟨c, rfl⟩

theorem rootU8_le_range : rootU8 K ≤ (blk8M (K := K)).range := by
  intro g hg
  obtain ⟨c, rfl⟩ := mem_rootU8_iff.1 hg
  exact ⟨tr2 c, rfl⟩

theorem blk8M_tr2_apply (c : Qext K) (v : QV K (Fin 2)) :
    ((blk8M (tr2 c) : ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) v =
      ![v 0 + c * v 1, v 1] := by
  rw [blk8M_apply]
  funext i
  fin_cases i <;>
    simp [tr2, Matrix.transvection, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem isPGroup_rootU8 : IsPGroup 2 ↥(rootU8 K) := by
  rw [IsPGroup.iff_orderOf]
  rintro ⟨g, hg⟩
  obtain ⟨c, rfl⟩ := mem_rootU8_iff.1 hg
  have hsq : (blk8M (tr2 c) : ↥(M8 K)) ^ 2 = 1 := by
    rw [pow_two, ← map_mul, tr2_mul, CharTwo.add_self_eq_zero, tr2_zero, map_one]
  have hdvd : orderOf (⟨blk8M (tr2 c), hg⟩ : ↥(rootU8 K)) ∣ 2 := by
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    simpa using hsq
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
  · exact ⟨0, by simpa using h⟩
  · exact ⟨1, by simpa using h⟩

theorem T8_conj_rootU8 {p : ℕ} {g : ↥(M8 K)} (hg : g ∈ T8 p K) :
    ∀ x ∈ rootU8 K, g * x * g⁻¹ ∈ rootU8 K := by
  intro x hx
  obtain ⟨c, rfl⟩ := mem_rootU8_iff.1 hx
  obtain ⟨a, b, -, -, hab⟩ := mem_T8_iff.1 hg
  have h : g * blk8M (tr2 c) = blk8M (tr2 ((a : Qext K) * c * (b : Qext K)⁻¹)) * g := by
    apply Subtype.ext
    refine LinearEquiv.ext fun v => ?_
    show (g : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2))
        (((blk8M (tr2 c) : ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) v) =
      ((blk8M (tr2 ((a : Qext K) * c * (b : Qext K)⁻¹)) : ↥(M8 K)) :
        QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) ((g : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) v)
    rw [hab]
    funext i
    fin_cases i
    · simp only [torusEquiv_apply, blk8M_tr2_apply]
      simp
      field_simp
    · simp [torusEquiv_apply, blk8M_tr2_apply]
  have : g * blk8M (tr2 c) * g⁻¹ = blk8M (tr2 ((a : Qext K) * c * (b : Qext K)⁻¹)) := by
    rw [h, mul_inv_cancel_right]
  rw [this]
  exact blk8M_tr2_mem_rootU8 _

theorem T8_le_normalizer_rootU8 {p : ℕ} :
    T8 p K ≤ Subgroup.normalizer (rootU8 K : Set ↥(M8 K)) := fun g hg =>
  mem_normalizer_of_conj_mem (T8_conj_rootU8 hg) (fun y hy => by
    have := T8_conj_rootU8 ((T8 p K).inv_mem hg) y hy
    simpa using this)

theorem blk8M_tr2_one_not_commute_rho8 {a : (Qext K)ˣ} (ha : a ≠ 1) :
    (blk8M (tr2 (1 : Qext K)) : ↥(M8 K)) * rho8 K a ≠ rho8 K a * blk8M (tr2 (1 : Qext K)) := by
  intro h
  have h1 := congrArg (fun x : ↥(M8 K) =>
    (x : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) (Pi.single 1 1) 0) h
  simp [coe_rho8, blk8M_tr2_apply, torusEquiv_apply] at h1
  have h2 : (a⁻¹ : (Qext K)ˣ) = a := Units.ext (by rw [Units.val_inv_eq_inv_val]; exact h1)
  exact ha (eq_one_of_inv_eq_self_two h2)

end CFSG.RankThree.PartOne.KFQ
