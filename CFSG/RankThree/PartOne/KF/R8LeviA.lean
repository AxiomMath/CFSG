module

public import CFSG.RankThree.PartOne.KFOUT3.KtyL4
public import CFSG.RankThree.PartOne.KF.LayerCover
public import CFSG.RankThree.PartOne.KF.R8Final
public import CFSG.RankThree.SteinbergR3ECALinearSplitBlocks

public section

namespace CFSG.RankThree.PartOne.KFQ

open CFSG CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne CFSG.Assembly.LowTwoRank
  CFSG.LieType.Chevalley CFSG.LieType.Universal.Unitary

variable {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}

@[expose] noncomputable def extCoord (i : Fin 2) :
    (Qext K ≃ₗ[K] Qext K) →* (QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) where
  toFun g := LinearEquiv.piCongrRight fun j => if j = i then g else LinearEquiv.refl K (Qext K)
  map_one' := by
    refine LinearEquiv.ext fun v => funext fun j => ?_
    by_cases hj : j = i <;> simp [hj]
  map_mul' g h := by
    refine LinearEquiv.ext fun v => funext fun j => ?_
    by_cases hj : j = i <;> simp [hj]

theorem extCoord_apply (i : Fin 2) (g : Qext K ≃ₗ[K] Qext K) (v : QV K (Fin 2)) (j : Fin 2) :
    extCoord i g v j = if j = i then g (v j) else v j := by
  by_cases hj : j = i <;> simp [extCoord, hj]

theorem extCoord_injective (i : Fin 2) : Function.Injective (extCoord (K := K) i) := by
  intro g g' h
  refine LinearEquiv.ext fun y => ?_
  have := congrArg (fun m : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2) => m (Pi.single i y) i) h
  simpa [extCoord_apply] using this

theorem det_extCoord (i : Fin 2) (g : Qext K ≃ₗ[K] Qext K) :
    LinearEquiv.det (extCoord i g) = LinearEquiv.det g := by
  apply Units.ext
  rw [LinearEquiv.coe_det, LinearEquiv.coe_det]
  have h : ((extCoord i g : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) : QV K (Fin 2) →ₗ[K] QV K (Fin 2)) =
      LinearMap.pi (fun j : Fin 2 => ((if j = i then g else LinearEquiv.refl K (Qext K) :
        Qext K ≃ₗ[K] Qext K) : Qext K →ₗ[K] Qext K).comp (LinearMap.proj j)) := by
    refine LinearMap.ext fun v => funext fun j => ?_
    by_cases hj : j = i <;> simp [extCoord, hj]
  rw [h, LinearMap.det_pi, Fin.prod_univ_two]
  fin_cases i <;> simp

@[expose] noncomputable def qBasis (K : Type) [Field K] [Finite K] [CharP K 2] :
    Module.Basis (Fin 2) K (Qext K) :=
  Module.finBasisOfFinrankEq K (Qext K) finrank_qext

@[expose] noncomputable def glK : (Qext K ≃ₗ[K] Qext K) ≃* GL (Fin 2) K :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Qext K)).symm.trans
    (Units.mapEquiv (LinearMap.toMatrixAlgEquiv (qBasis K)).toMulEquiv)

theorem det_glK (g : Qext K ≃ₗ[K] Qext K) :
    ((glK g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = (LinearEquiv.det g : K) := by
  rw [LinearEquiv.coe_det]
  exact LinearMap.det_toMatrix (qBasis K) (g : Qext K →ₗ[K] Qext K)

@[expose] noncomputable def iotaK : Matrix.SpecialLinearGroup (Fin 2) K →* (Qext K ≃ₗ[K] Qext K) :=
  (glK (K := K)).symm.toMonoidHom.comp Matrix.SpecialLinearGroup.toGL

theorem glK_iotaK (X : Matrix.SpecialLinearGroup (Fin 2) K) :
    glK (iotaK X) = Matrix.SpecialLinearGroup.toGL X := by
  simp [iotaK]

theorem det_iotaK (X : Matrix.SpecialLinearGroup (Fin 2) K) : LinearEquiv.det (iotaK X) = 1 := by
  apply Units.ext
  have h := det_glK (iotaK X)
  rw [glK_iotaK] at h
  have h2 : ((Matrix.SpecialLinearGroup.toGL X : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (X : Matrix (Fin 2) (Fin 2) K) := rfl
  rw [h2, Matrix.SpecialLinearGroup.det_coe] at h
  simpa using h.symm

theorem iotaK_injective : Function.Injective (iotaK (K := K)) := by
  intro X Y h
  have h1 := congrArg (glK (K := K)) h
  rw [glK_iotaK, glK_iotaK] at h1
  apply Subtype.ext
  have h2 := congrArg (fun u : GL (Fin 2) K => (u : Matrix (Fin 2) (Fin 2) K)) h1
  exact h2

@[expose] noncomputable def blkA (i : Fin 2) :
    Matrix.SpecialLinearGroup (Fin 2) K →* ↥(M8 K) :=
  ((extCoord i).comp (iotaK (K := K))).codRestrict (M8 K) (fun X =>
    (mem_M8_iff _).2 (by
      rw [MonoidHom.comp_apply, det_extCoord, det_iotaK]))

theorem blkA_apply (i : Fin 2) (X : Matrix.SpecialLinearGroup (Fin 2) K) :
    ((blkA i X : ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) = extCoord i (iotaK X) := rfl

theorem blkA_injective (i : Fin 2) : Function.Injective (blkA (K := K) i) := by
  intro X Y h
  have h1 := congrArg (fun g : ↥(M8 K) => (g : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2))) h
  exact iotaK_injective (extCoord_injective i h1)

section Centralizer

variable (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1)

@[expose] noncomputable def bA (z : rootsOfUnity p (Qext K)) : ↥(M8 K) :=
  ⟨d8Emb ((1 : rootsOfUnity p (Qext K)), z), d8Emb_mem_M8 hp hp2 hpq _⟩

theorem bA_mem_T8 (z : rootsOfUnity p (Qext K)) : bA hp hp2 hpq z ∈ T8 p K := by
  rw [T8, Subgroup.mem_subgroupOf]
  exact ⟨((1 : rootsOfUnity p (Qext K)), z), rfl⟩

variable {hp hp2 hpq}

@[expose] noncomputable def lamA (g : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) : Qext K :=
  g (Pi.single 1 1) 1

theorem mem_centralizer_bA_comm {z : rootsOfUnity p (Qext K)} {g : ↥(M8 K)}
    (hg : g ∈ Subgroup.centralizer ({bA hp hp2 hpq z} : Set ↥(M8 K))) (v : QV K (Fin 2)) :
    d8Emb ((1 : rootsOfUnity p (Qext K)), z) ((g : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) v) =
      (g : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) (d8Emb ((1 : rootsOfUnity p (Qext K)), z) v) := by
  have h1 := Subgroup.mem_centralizer_iff.mp hg _ (Set.mem_singleton _)
  exact congrArg (fun y : ↥(M8 K) => ((y : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) v)) h1

omit [Finite K] in
theorem root_pow_eq_one (z : rootsOfUnity p (Qext K)) :
    (((z : rootsOfUnity p (Qext K)) : (Qext K)ˣ) : Qext K) ^ p = 1 := by
  have := (mem_rootsOfUnity p _).mp z.2
  simpa using congrArg Units.val this

omit [Finite K] in
theorem root_ne_one {z : rootsOfUnity p (Qext K)} (hz1 : z ≠ 1) :
    (((z : rootsOfUnity p (Qext K)) : (Qext K)ˣ) : Qext K) ≠ 1 := fun h =>
  hz1 (Subtype.ext (Units.ext h))

theorem span_root (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1)
    {z : rootsOfUnity p (Qext K)} (hz1 : z ≠ 1) :
    Submodule.span K {(1 : Qext K), (((z : rootsOfUnity p (Qext K)) : (Qext K)ˣ) : Qext K)} = ⊤ :=
  KFOUT3.span_one_of_not_mem_range
    (KFOUT3.not_mem_range_of_root hp hp2 hpq (root_pow_eq_one z) (root_ne_one hz1))

theorem blockA (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1)
    {z : rootsOfUnity p (Qext K)} (hz1 : z ≠ 1) (g : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2))
    (hg : ∀ v, d8Emb ((1 : rootsOfUnity p (Qext K)), z) (g v) =
      g (d8Emb ((1 : rootsOfUnity p (Qext K)), z) v)) (v : QV K (Fin 2)) :
    g v 0 = KFOUT3.blk (g : QV K (Fin 2) →ₗ[K] QV K (Fin 2)) 0 0 (v 0) ∧ g v 1 = v 1 * lamA g := by
  have hb := KFOUT3.eq_blocks hz1 (g : QV K (Fin 2) →ₗ[K] QV K (Fin 2)) hg v
  refine ⟨congrFun hb 0, ?_⟩
  have h1 := congrFun hb 1
  have h2 := KFOUT3.blk_one_one_linear (g : QV K (Fin 2) →ₗ[K] QV K (Fin 2)) hg
    (span_root hp hp2 hpq hz1) (v 1)
  have h3 : KFOUT3.blk (g : QV K (Fin 2) →ₗ[K] QV K (Fin 2)) 1 1 1 = lamA g :=
    KFOUT3.blk_apply _ 1 1 1
  rw [h3] at h2
  exact h1.trans h2

theorem lamA_ne_zero (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1)
    {z : rootsOfUnity p (Qext K)} (hz1 : z ≠ 1) (g : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2))
    (hg : ∀ v, d8Emb ((1 : rootsOfUnity p (Qext K)), z) (g v) =
      g (d8Emb ((1 : rootsOfUnity p (Qext K)), z) v)) : lamA g ≠ 0 := by
  intro h0
  have hone : (Pi.single 1 (1 : Qext K) : QV K (Fin 2)) ≠ 0 := by
    intro h
    have := congrFun h 1
    simp at this
  apply hone
  apply g.injective
  rw [map_zero]
  funext i
  obtain ⟨b0, b1⟩ := blockA hp hp2 hpq hz1 g hg (Pi.single 1 1)
  fin_cases i
  · simp only [Fin.zero_eta, Pi.zero_apply]
    rw [b0]
    simp
  · simp only [Fin.mk_one, Pi.zero_apply]
    rw [b1, h0]
    simp

@[expose] noncomputable def phiA (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1)
    {z : rootsOfUnity p (Qext K)} (hz1 : z ≠ 1) :
    ↥(Subgroup.centralizer ({bA hp hp2 hpq z} : Set ↥(M8 K))) →* (Qext K)ˣ where
  toFun g := Units.mk0 (lamA ((g : ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)))
    (lamA_ne_zero hp hp2 hpq hz1 _ (mem_centralizer_bA_comm g.2))
  map_one' := by
    apply Units.ext
    simp [lamA]
  map_mul' g h := by
    apply Units.ext
    show lamA (((g * h : ↥(Subgroup.centralizer ({bA hp hp2 hpq z} : Set ↥(M8 K)))) :
      ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) = _
    have hh := (blockA hp hp2 hpq hz1 ((h : ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2))
      (mem_centralizer_bA_comm h.2) (Pi.single 1 1))
    have he : (h : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) (Pi.single 1 1) =
        Pi.single 1 (lamA ((h : ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2))) := by
      funext i
      fin_cases i
      · simpa using hh.1
      · simpa using hh.2
    have hg2 := (blockA hp hp2 hpq hz1 ((g : ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2))
      (mem_centralizer_bA_comm g.2)
      (Pi.single 1 (lamA ((h : ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2))))).2
    show ((g : ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2))
        (((h : ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) (Pi.single 1 1)) 1 = _
    rw [he, hg2]
    simp [mul_comm]

theorem blkA_mem_centralizer {z : rootsOfUnity p (Qext K)}
    (X : Matrix.SpecialLinearGroup (Fin 2) K) :
    blkA 0 X ∈ Subgroup.centralizer ({bA hp hp2 hpq z} : Set ↥(M8 K)) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  refine LinearEquiv.ext fun v => funext fun j => ?_
  show ((blkA 0 X : ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2))
      (d8Emb ((1 : rootsOfUnity p (Qext K)), z) v) j =
    d8Emb ((1 : rootsOfUnity p (Qext K)), z)
      (((blkA 0 X : ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) v) j
  fin_cases j
  · simp [blkA_apply, extCoord_apply, d8Emb_apply_zero]
  · simp [blkA_apply, extCoord_apply, d8Emb_apply_one]

theorem ker_phiA {z : rootsOfUnity p (Qext K)} (hz1 : z ≠ 1) :
    (phiA hp hp2 hpq hz1).ker =
      (blkA (K := K) 0).range.subgroupOf
        (Subgroup.centralizer ({bA hp hp2 hpq z} : Set ↥(M8 K))) := by
  classical
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  have hg := mem_centralizer_bA_comm g.2
  constructor
  · intro h
    have hlam : lamA ((g : ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) = 1 := by
      have := congrArg (fun u : (Qext K)ˣ => (u : Qext K)) h
      simpa [phiA] using this
    set gl : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2) :=
      ((g : ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) with hgl
    have hb := blockA hp hp2 hpq hz1 gl hg
    set b00 : Qext K →ₗ[K] Qext K := KFOUT3.blk (gl : QV K (Fin 2) →ₗ[K] QV K (Fin 2)) 0 0 with hb00
    have hinj : Function.Injective b00 := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro y hy
      have hz : gl (Pi.single 0 y) = 0 := by
        funext i
        obtain ⟨c0, c1⟩ := hb (Pi.single 0 y)
        fin_cases i
        · simp only [Fin.zero_eta, Pi.zero_apply]
          rw [c0]
          simpa using hy
        · simp only [Fin.mk_one, Pi.zero_apply]
          rw [c1]
          simp
      have := gl.injective (hz.trans (map_zero gl).symm)
      simpa using congrFun this 0
    set g₀ : Qext K ≃ₗ[K] Qext K := LinearEquiv.ofInjectiveEndo b00 hinj with hg₀def
    have hg₀ : ∀ y, g₀ y = b00 y := fun y => rfl
    have hEq : gl = extCoord 0 g₀ := LinearEquiv.ext fun v => funext fun j => by
      obtain ⟨c0, c1⟩ := hb v
      fin_cases j
      · simp only [Fin.zero_eta]
        rw [c0, extCoord_apply]
        simp [hg₀]
      · simp only [Fin.mk_one]
        rw [c1, hlam, extCoord_apply]
        simp
    have hdet : LinearEquiv.det g₀ = 1 := by
      have h1 : LinearEquiv.det gl = 1 := (mem_M8_iff _).1 (g : ↥(M8 K)).2
      rw [hEq, det_extCoord] at h1
      exact h1
    let X : Matrix.SpecialLinearGroup (Fin 2) K :=
      ⟨((glK g₀ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K), by rw [det_glK, hdet]; simp⟩
    have hXg : iotaK X = g₀ := by
      apply glK.injective
      rw [glK_iotaK]
      exact Units.ext rfl
    refine ⟨X, ?_⟩
    apply Subtype.ext
    show extCoord 0 (iotaK X) = gl
    rw [hXg, hEq]
  · rintro ⟨X, hX⟩
    apply Units.ext
    show lamA ((g : ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) = 1
    have := congrArg (fun y : ↥(M8 K) => (y : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2))) hX
    rw [← this]
    simp [lamA, blkA_apply, extCoord_apply]

theorem perfectResidual_centralizer_bA (hK : 4 ≤ Nat.card K) {z : rootsOfUnity p (Qext K)}
    (hz1 : z ≠ 1) :
    inSubgroup perfectResidual (Subgroup.centralizer ({bA hp hp2 hpq z} : Set ↥(M8 K))) =
      (blkA (K := K) 0).range := by
  have hq := CFSG.RankThree.CALinearPlane.isQuasisimple_SL_of_two_le (k := K) (m := 2) le_rfl hK
  have hperf : Group.IsPerfect ↥((blkA (K := K) 0).range) := by
    have := hq.1
    exact Group.IsPerfect.ofSurjective
      (f := (MonoidHom.ofInjective (blkA_injective (K := K) 0)).toMonoidHom)
      (MonoidHom.ofInjective (blkA_injective (K := K) 0)).surjective
  exact inSubgroup_perfectResidual_eq_of_ker (by
    rintro _ ⟨X, rfl⟩
    exact blkA_mem_centralizer X) hperf (phiA hp hp2 hpq hz1) (ker_phiA hz1)

end Centralizer

section Torus

@[expose] noncomputable def mulK : (Qext K)ˣ →* (Qext K ≃ₗ[K] Qext K) :=
  DistribMulAction.toModuleAut K (Qext K)

theorem mulK_apply (a : (Qext K)ˣ) (y : Qext K) : mulK a y = (a : Qext K) * y := rfl

theorem extCoord_zero_mulK (a : rootsOfUnity p (Qext K)) :
    extCoord 0 (mulK ((a : (Qext K)ˣ))) =
      d8Emb ((a, (1 : rootsOfUnity p (Qext K))) : D8Mod p (Qext K)) := by
  refine LinearEquiv.ext fun v => funext fun j => ?_
  fin_cases j
  · simp [extCoord_apply, d8Emb_apply_zero, mulK_apply]
  · simp [extCoord_apply, d8Emb_apply_one]

variable (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1)

include hp hp2 hpq

theorem det_mulK_eq_one (a : rootsOfUnity p (Qext K)) :
    LinearEquiv.det (mulK ((a : (Qext K)ˣ))) = 1 := by
  refine det_eq_one_of_pow_eq_one hp (not_dvd_pred hp hp2 hpq) _ ?_
  rw [← map_pow, (mem_rootsOfUnity p _).mp a.2, map_one]

theorem exists_iotaK_eq_mulK (a : rootsOfUnity p (Qext K)) :
    ∃ X : Matrix.SpecialLinearGroup (Fin 2) K, iotaK X = mulK ((a : (Qext K)ˣ)) := by
  let X : Matrix.SpecialLinearGroup (Fin 2) K :=
    ⟨((glK (mulK ((a : (Qext K)ˣ))) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K), by
      rw [det_glK, det_mulK_eq_one hp hp2 hpq]; simp⟩
  refine ⟨X, ?_⟩
  apply glK.injective
  rw [glK_iotaK]
  exact Units.ext rfl

@[expose] noncomputable def thetaA : rootsOfUnity p (Qext K) →* ↥(M8 K) :=
  ((d8Emb (p := p) (K := K)).comp
    (MonoidHom.inl (rootsOfUnity p (Qext K)) (rootsOfUnity p (Qext K)))).codRestrict (M8 K)
    (fun _ => d8Emb_mem_M8 hp hp2 hpq _)

theorem coe_thetaA (a : rootsOfUnity p (Qext K)) :
    ((thetaA hp hp2 hpq a : ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) =
      d8Emb ((a, (1 : rootsOfUnity p (Qext K))) : D8Mod p (Qext K)) := rfl

theorem thetaA_injective : Function.Injective (thetaA (K := K) hp hp2 hpq) := by
  intro a a' h
  have h1 := congrArg (fun g : ↥(M8 K) => (g : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2))) h
  have h2 := d8Emb_injective h1
  exact (Prod.mk.inj h2).1

theorem thetaA_mem_range (a : rootsOfUnity p (Qext K)) :
    thetaA hp hp2 hpq a ∈ (blkA (K := K) 0).range := by
  obtain ⟨X, hX⟩ := exists_iotaK_eq_mulK hp hp2 hpq a
  refine ⟨X, Subtype.ext ?_⟩
  rw [blkA_apply, hX, extCoord_zero_mulK a]
  rfl

theorem T8_inf_range_blkA :
    T8 p K ⊓ (blkA (K := K) 0).range = (thetaA hp hp2 hpq).range := by
  ext g
  constructor
  · rintro ⟨hgT, X, hX⟩
    obtain ⟨v, hv⟩ := Subgroup.mem_subgroupOf.mp hgT
    have h1 := congrArg (fun y : ↥(M8 K) =>
      (y : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) (Pi.single 1 1) 1) hX
    simp only [blkA_apply, extCoord_apply] at h1
    have h2 : d8Emb v (Pi.single 1 1) 1 = 1 := by
      have : (g : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) (Pi.single 1 1) 1 = 1 := by
        rw [← h1]
        simp
      rw [← hv] at this
      exact this
    rw [d8Emb_apply_one] at h2
    have hv2 : v.2 = 1 := by
      apply Subtype.ext
      apply Units.ext
      simpa using h2
    refine ⟨v.1, ?_⟩
    apply Subtype.ext
    rw [coe_thetaA, ← hv]
    congr 1
    exact Prod.ext rfl hv2.symm
  · rintro ⟨a, rfl⟩
    exact ⟨⟨((a, (1 : rootsOfUnity p (Qext K))) : D8Mod p (Qext K)), rfl⟩,
      thetaA_mem_range hp hp2 hpq a⟩

theorem card_T8_inf_range_blkA (hζ : ∃ ζ : (Qext K)ˣ, IsPrimitiveRoot ζ p) :
    Nat.card ↥(T8 p K ⊓ (blkA (K := K) 0).range) = p := by
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := hζ
  rw [T8_inf_range_blkA hp hp2 hpq,
    Nat.card_congr (MonoidHom.ofInjective (thetaA_injective hp hp2 hpq)).toEquiv.symm]
  exact IsPrimitiveRoot.card_rootsOfUnity (IsPrimitiveRoot.coe_units_iff.mpr hζ)

end Torus

@[expose] noncomputable def swapM : ↥(M8 K) :=
  ⟨gSwap, (mem_M8_iff _).2 (det_eq_one_of_mul_self _ gSwap_mul_self)⟩

theorem coe_swapM :
    ((swapM : ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) = gSwap := rfl

theorem swapM_mul_self : (swapM : ↥(M8 K)) * swapM = 1 :=
  Subtype.ext gSwap_mul_self

theorem swapM_inv : (swapM : ↥(M8 K))⁻¹ = swapM :=
  inv_eq_of_mul_eq_one_right swapM_mul_self

theorem gSwap_extCoord_zero (g : Qext K ≃ₗ[K] Qext K) :
    (gSwap : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) * extCoord 0 g * gSwap = extCoord 1 g := by
  refine LinearEquiv.ext fun v => funext fun j => ?_
  fin_cases j
  · simp [gSwap_apply, extCoord_apply]
  · simp [gSwap_apply, extCoord_apply]

theorem swapM_blkA (X : Matrix.SpecialLinearGroup (Fin 2) K) :
    (swapM : ↥(M8 K)) * blkA 0 X * swapM⁻¹ = blkA 1 X := by
  rw [swapM_inv]
  apply Subtype.ext
  show gSwap * extCoord 0 (iotaK X) * gSwap = extCoord 1 (iotaK X)
  exact gSwap_extCoord_zero _

theorem gSwap_d8Emb {p : ℕ} (v : D8Mod p (Qext K)) :
    (gSwap : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) * d8Emb v * gSwap = d8Emb (v.2, v.1) := by
  refine LinearEquiv.ext fun w => funext fun j => ?_
  fin_cases j
  · simp [gSwap_apply, d8Emb_apply_zero, d8Emb_apply_one]
  · simp [gSwap_apply, d8Emb_apply_zero, d8Emb_apply_one]

theorem map_conj_swapM_range_blkA :
    (blkA (K := K) 0).range.map (MulAut.conj (swapM : ↥(M8 K))).toMonoidHom =
      (blkA (K := K) 1).range := by
  ext y
  constructor
  · rintro ⟨_, ⟨X, rfl⟩, rfl⟩
    exact ⟨X, (swapM_blkA X).symm⟩
  · rintro ⟨X, rfl⟩
    exact ⟨blkA 0 X, ⟨X, rfl⟩, swapM_blkA X⟩

end CFSG.RankThree.PartOne.KFQ
