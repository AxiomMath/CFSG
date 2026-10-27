module

public import CFSG.RankThree.GF2n.Stroth80.Sec108Levi
public import CFSG.Quasithin.Background.A1cTransfer
public import CFSG.HardMathSupport.Solomon.Coordinator.I22_4Basic

public section

namespace CFSG.RankThree.GF2n.Stroth80.Sec108

open CFSG CFSG.Open Matrix CFSG.Open.StatedAPI
open scoped commutatorElement

variable {𝓜 : Type} [Group 𝓜] [Finite 𝓜] {K : Type} [Field K] [Finite K] [CharP K 2]
  {L R N Y : Subgroup 𝓜} {ρ : ↥R →* GL (Fin 3) K} {μ : ↥N →* Multiplicative (Fin 3 → K)}
  {T : ↥(NLY L Y) →* AddMonoid.End (Fin 3 → K)}

private def P0pre (L R : Subgroup 𝓜) : Subgroup ↥(NL L) := (P0frak L R).comap (mkG L)

private lemma mem_P0pre_iff {g : ↥(NL L)} :
    g ∈ P0pre L R ↔ mkG L g ∈ P0frak L R := Iff.rfl

private lemma P0pre_le_R (hC : Levi108 K L R N Y ρ μ T) {g : ↥(P0pre L R)} :
    (g : 𝓜) ∈ R :=
  hC.mem_R_of_mem_Pfrak (P0frak_le_Pfrak L R g.2)

private lemma P0pre_rho00 (hC : Levi108 K L R N Y ρ μ T) {g : ↥(P0pre L R)} :
    (ρ ⟨(g : 𝓜), P0pre_le_R hC⟩ : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 :=
  (hC.mem_P0frak_iff (g : ↥(NL L)) (P0pre_le_R hC)).1 g.2

private lemma P0pre_normalizer (hC : Levi108 K L R N Y ρ μ T) {g : ↥(P0pre L R)} :
    (ρ ⟨(g : 𝓜), P0pre_le_R hC⟩ : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 ∧
      (ρ ⟨(g : 𝓜), P0pre_le_R hC⟩ : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 :=
  (hC.mem_normalizer_iff (g : 𝓜) (P0pre_le_R hC)).1 (g : ↥(NL L)).2

private def block (hC : Levi108 K L R N Y ρ μ T) (g : ↥(P0pre L R)) :
    Matrix (Fin 2) (Fin 2) K :=
  fun i j => (ρ ⟨(g : 𝓜), P0pre_le_R hC⟩ : Matrix (Fin 3) (Fin 3) K) i.succ j.succ

private lemma block_mul (hC : Levi108 K L R N Y ρ μ T) (g h : ↥(P0pre L R)) :
    block hC (g * h) = block hC g * block hC h := by
  have h10 := (P0pre_normalizer hC (g := g)).1
  have h20 := (P0pre_normalizer hC (g := g)).2
  have hsub : (⟨(g : 𝓜) * (h : 𝓜), P0pre_le_R hC (g := g * h)⟩ : ↥R) =
      ⟨(g : 𝓜), P0pre_le_R hC⟩ * ⟨(h : 𝓜), P0pre_le_R hC⟩ := Subtype.ext rfl
  have hmul : (ρ ⟨(g : 𝓜) * (h : 𝓜), P0pre_le_R hC (g := g * h)⟩ : Matrix (Fin 3) (Fin 3) K) =
      (ρ ⟨(g : 𝓜), P0pre_le_R hC⟩ : Matrix (Fin 3) (Fin 3) K) *
        (ρ ⟨(h : 𝓜), P0pre_le_R hC⟩ : Matrix (Fin 3) (Fin 3) K) := by
    rw [hsub, map_mul, GeneralLinearGroup.coe_mul]
  ext i j
  fin_cases i <;>
  simp [block, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, h10, h20, hmul,
    Fin.succ]

private lemma block_det (hC : Levi108 K L R N Y ρ μ T) (g : ↥(P0pre L R)) :
    (block hC g).det = 1 := by
  have h00 := P0pre_rho00 hC (g := g)
  have h10 := (P0pre_normalizer hC (g := g)).1
  have h20 := (P0pre_normalizer hC (g := g)).2
  have hdet : (ρ ⟨(g : 𝓜), P0pre_le_R hC⟩ : Matrix (Fin 3) (Fin 3) K).det = 1 :=
    det_of_mem_statedSL (hC.range_rho ▸ MonoidHom.mem_range.2 ⟨⟨(g : 𝓜), P0pre_le_R hC⟩, rfl⟩)
  rw [Matrix.det_fin_three] at hdet
  rw [Matrix.det_fin_two]
  rw [h00, h10, h20] at hdet
  simp only [block]
  simpa using hdet

private noncomputable def blockHom (hC : Levi108 K L R N Y ρ μ T) :
    ↥(P0pre L R) →* SpecialLinearGroup (Fin 2) K where
  toFun g := ⟨block hC g, block_det hC g⟩
  map_one' := by
    ext i j
    have h1 : (ρ ⟨(1 : 𝓜), P0pre_le_R hC (g := 1)⟩ : Matrix (Fin 3) (Fin 3) K) = 1 := by
      have hsub : (⟨(1 : 𝓜), P0pre_le_R hC (g := 1)⟩ : ↥R) = 1 := Subtype.ext rfl
      rw [hsub, map_one, GeneralLinearGroup.coe_one]
    simp [block, h1, Matrix.one_apply, Fin.succ_inj]
  map_mul' g h := by ext i j; exact congrFun (congrFun (block_mul hC g h) i) j

private def diagBlock (A : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 3) (Fin 3) K :=
  !![1, 0, 0; 0, A 0 0, A 0 1; 0, A 1 0, A 1 1]

private lemma diagBlock_det (A : Matrix (Fin 2) (Fin 2) K) (hA : A.det = 1) :
    (diagBlock A).det = 1 := by
  rw [Matrix.det_fin_two] at hA
  rw [Matrix.det_fin_three]
  simp [diagBlock]
  linear_combination hA

private lemma blockHom_surjective (hC : Levi108 K L R N Y ρ μ T) :
    Function.Surjective (blockHom hC) := by
  intro A
  let B : GL (Fin 3) K := Matrix.GeneralLinearGroup.mkOfDetNeZero
    (diagBlock (A : Matrix (Fin 2) (Fin 2) K))
    (by rw [diagBlock_det (A : Matrix (Fin 2) (Fin 2) K) A.2]; exact one_ne_zero)
  have hBmat_def : (B : Matrix (Fin 3) (Fin 3) K) = diagBlock (A : Matrix (Fin 2) (Fin 2) K) := rfl
  have hB : B ∈ ρ.range := by
    rw [hC.range_rho]
    exact mem_statedSL_of_det (by rw [hBmat_def, diagBlock_det (A : Matrix (Fin 2) (Fin 2) K) A.2])
  obtain ⟨r, hr⟩ := MonoidHom.mem_range.1 hB
  have hBmat : (ρ r : Matrix (Fin 3) (Fin 3) K) = diagBlock (A : Matrix (Fin 2) (Fin 2) K) := by
    rw [hr, hBmat_def]
  have h10 : (ρ r : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 := by rw [hBmat]; simp [diagBlock]
  have h20 : (ρ r : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := by rw [hBmat]; simp [diagBlock]
  have hNL : (r : 𝓜) ∈ NL L :=
    (hC.mem_normalizer_iff (r : 𝓜) r.2).2 ⟨h10, h20⟩
  have h00 : (ρ r : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 := by rw [hBmat]; simp [diagBlock]
  have hP0 : mkG L ⟨(r : 𝓜), hNL⟩ ∈ P0frak L R :=
    (hC.mem_P0frak_iff ⟨(r : 𝓜), hNL⟩ r.2).2 (by simpa using h00)
  let g : ↥(P0pre L R) := ⟨⟨(r : 𝓜), hNL⟩, hP0⟩
  refine ⟨g, ?_⟩
  have hmat : (ρ ⟨(g : 𝓜), P0pre_le_R hC⟩ : Matrix (Fin 3) (Fin 3) K) =
      diagBlock (A : Matrix (Fin 2) (Fin 2) K) := hBmat
  ext i j
  change (ρ ⟨(g : 𝓜), P0pre_le_R hC⟩ : Matrix (Fin 3) (Fin 3) K) i.succ j.succ = A i j
  rw [hmat]
  fin_cases i <;> fin_cases j <;> simp [diagBlock]

private lemma rho_eq_one_of_mem_N (hC : Levi108 K L R N Y ρ μ T) {n : 𝓜} (hnR : n ∈ R)
    (hnN : n ∈ N) : (ρ ⟨n, hnR⟩ : Matrix (Fin 3) (Fin 3) K) = 1 := by
  have hmem : (⟨n, hnR⟩ : ↥R) ∈ ρ.ker := by
    rw [hC.ker_rho]
    exact Subgroup.mem_subgroupOf.2 hnN
  have h1 : ρ ⟨n, hnR⟩ = 1 := MonoidHom.mem_ker.1 hmem
  rw [h1, GeneralLinearGroup.coe_one]

private lemma N_subgroupOf_le_P0pre (hC : Levi108 K L R N Y ρ μ T) :
    N.subgroupOf (NL L) ≤ P0pre L R := by
  intro n hn
  rw [mem_P0pre_iff]
  refine (hC.mem_P0frak_iff n (hC.N_le_R (Subgroup.mem_subgroupOf.1 hn))).2 ?_
  rw [rho_eq_one_of_mem_N hC (hC.N_le_R (Subgroup.mem_subgroupOf.1 hn))
    (Subgroup.mem_subgroupOf.1 hn)]
  simp

private lemma blockHom_apply_N (hC : Levi108 K L R N Y ρ μ T) {n : ↥(NL L)}
    (hnN : n ∈ N.subgroupOf (NL L)) (hnP : n ∈ P0pre L R) :
    blockHom hC ⟨n, hnP⟩ = 1 := by
  ext i j
  change (ρ ⟨(n : 𝓜), P0pre_le_R hC (g := ⟨n, hnP⟩)⟩ : Matrix (Fin 3) (Fin 3) K) i.succ j.succ =
    (1 : Matrix (Fin 2) (Fin 2) K) i j
  rw [rho_eq_one_of_mem_N hC (hC.N_le_R (Subgroup.mem_subgroupOf.1 hnN))
    (Subgroup.mem_subgroupOf.1 hnN)]
  simp [Matrix.one_apply, Fin.succ_inj]

private lemma blockHom_apply_L (hC : Levi108 K L R N Y ρ μ T) {l : ↥(NL L)}
    (hlL : l ∈ L.subgroupOf (NL L)) (hlP : l ∈ P0pre L R) :
    blockHom hC ⟨l, hlP⟩ = 1 := by
  obtain ⟨u, hu0, hu⟩ := hC.rho_L (l : 𝓜) (Subgroup.mem_subgroupOf.1 hlL)
  ext i j
  change (ρ ⟨(l : 𝓜), P0pre_le_R hC (g := ⟨l, hlP⟩)⟩ : Matrix (Fin 3) (Fin 3) K) i.succ j.succ =
    (1 : Matrix (Fin 2) (Fin 2) K) i j
  have hsub : (⟨(l : 𝓜), P0pre_le_R hC (g := ⟨l, hlP⟩)⟩ : ↥R) =
      ⟨(l : 𝓜), hC.L_le_R (Subgroup.mem_subgroupOf.1 hlL)⟩ := Subtype.ext rfl
  rw [show (ρ ⟨(l : 𝓜), P0pre_le_R hC (g := ⟨l, hlP⟩)⟩ : Matrix (Fin 3) (Fin 3) K) =
      (ρ ⟨(l : 𝓜), hC.L_le_R (Subgroup.mem_subgroupOf.1 hlL)⟩ : Matrix (Fin 3) (Fin 3) K)
      from congrArg (fun x : ↥R => (ρ x : Matrix (Fin 3) (Fin 3) K)) hsub, hu]
  fin_cases i <;> fin_cases j <;> simp [Matrix.vecMulVec, e₀, Matrix.one_apply]

private lemma block_eq_one_exists_param (hC : Levi108 K L R N Y ρ μ T)
    {g : ↥(P0pre L R)} (hbmat : block hC g = 1) :
    ∃ u : Fin 3 → K, u 0 = 0 ∧
      (ρ ⟨(g : 𝓜), P0pre_le_R hC⟩ : Matrix (Fin 3) (Fin 3) K) =
        1 + Matrix.vecMulVec (e₀ K) u := by
  have hA : (ρ ⟨(g : 𝓜), P0pre_le_R hC⟩ : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 :=
    P0pre_rho00 hC
  have h10 : (ρ ⟨(g : 𝓜), P0pre_le_R hC⟩ : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 :=
    (P0pre_normalizer hC).1
  have h20 : (ρ ⟨(g : 𝓜), P0pre_le_R hC⟩ : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 :=
    (P0pre_normalizer hC).2
  have h11 : (ρ ⟨(g : 𝓜), P0pre_le_R hC⟩ : Matrix (Fin 3) (Fin 3) K) 1 1 = 1 := by
    simpa [block] using congrFun (congrFun hbmat 0) 0
  have h12 : (ρ ⟨(g : 𝓜), P0pre_le_R hC⟩ : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 := by
    simpa [block] using congrFun (congrFun hbmat 0) 1
  have h21 : (ρ ⟨(g : 𝓜), P0pre_le_R hC⟩ : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 := by
    simpa [block] using congrFun (congrFun hbmat 1) 0
  have h22 : (ρ ⟨(g : 𝓜), P0pre_le_R hC⟩ : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
    simpa [block] using congrFun (congrFun hbmat 1) 1
  refine ⟨fun j => if j = 0 then 0 else
    (ρ ⟨(g : 𝓜), P0pre_le_R hC⟩ : Matrix (Fin 3) (Fin 3) K) 0 j, by simp, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hA, h10, h20, h11, h12, h21, h22, Matrix.vecMulVec, e₀, Matrix.one_apply]

private lemma blockHom_one_mem_Yhat (hC : Levi108 K L R N Y ρ μ T)
    {g : ↥(P0pre L R)} (hb : blockHom hC g = 1) :
    mkG L (g : ↥(NL L)) ∈ Yhat L N := by
  obtain ⟨u, hu0, hAeq⟩ := block_eq_one_exists_param hC (congrArg Subtype.val hb)
  obtain ⟨l, hlL, hlρ⟩ := hC.exists_L u hu0
  have hlR : l ∈ R := hC.L_le_R hlL
  have hglR : (g : 𝓜) * l⁻¹ ∈ R := R.mul_mem (P0pre_le_R hC) (R.inv_mem hlR)
  have hgl_eq : (ρ ⟨(g : 𝓜), P0pre_le_R hC⟩ : GL (Fin 3) K) = ρ ⟨l, hlR⟩ := by
    apply Units.ext
    exact hAeq.trans hlρ.symm
  have hglN : (g : 𝓜) * l⁻¹ ∈ N := by
    have hglGL : (ρ ⟨(g : 𝓜), P0pre_le_R hC⟩ : GL (Fin 3) K) *
        (ρ ⟨l, hlR⟩ : GL (Fin 3) K)⁻¹ = 1 := by
      rw [hgl_eq, mul_inv_cancel]
    have hglρ : (ρ ⟨(g : 𝓜) * l⁻¹, hglR⟩ : Matrix (Fin 3) (Fin 3) K) = 1 := by
      have hsub : (⟨(g : 𝓜) * l⁻¹, hglR⟩ : ↥R) =
          ⟨(g : 𝓜), P0pre_le_R hC⟩ * (⟨l, hlR⟩ : ↥R)⁻¹ := Subtype.ext rfl
      rw [show (ρ ⟨(g : 𝓜) * l⁻¹, hglR⟩ : Matrix (Fin 3) (Fin 3) K) =
          (ρ (⟨(g : 𝓜), P0pre_le_R hC⟩ * (⟨l, hlR⟩ : ↥R)⁻¹) :
            Matrix (Fin 3) (Fin 3) K) from
          congrArg (fun x : ↥R => (ρ x : Matrix (Fin 3) (Fin 3) K)) hsub,
        map_mul, map_inv, hglGL, GeneralLinearGroup.coe_one]
    have hmem : (⟨(g : 𝓜) * l⁻¹, hglR⟩ : ↥R) ∈ ρ.ker :=
      MonoidHom.mem_ker.2 (Units.ext hglρ)
    rw [hC.ker_rho] at hmem
    exact Subgroup.mem_subgroupOf.1 hmem
  have hglNL : (g : 𝓜) * l⁻¹ ∈ NL L := hC.N_le_NL hglN
  have hdecomp : (g : ↥(NL L)) = ⟨(g : 𝓜) * l⁻¹, hglNL⟩ *
      ⟨l, L.le_normalizer hlL⟩ := Subtype.ext (by simp)
  rw [hdecomp, map_mul]
  have hgl : mkG L ⟨l, L.le_normalizer hlL⟩ = 1 :=
    (QuotientGroup.eq_one_iff _).2 hlL
  rw [hgl, mul_one]
  exact Subgroup.mem_map_of_mem (f := mkG L) (Subgroup.mem_subgroupOf.2 hglN)

private lemma blockHom_eq_one_iff (hC : Levi108 K L R N Y ρ μ T) {g : ↥(P0pre L R)} :
    blockHom hC g = 1 ↔ mkG L (g : ↥(NL L)) ∈ Yhat L N := by
  constructor
  · exact blockHom_one_mem_Yhat hC
  · intro hmem
    obtain ⟨n, hnN, hnEq⟩ := Subgroup.mem_map.1 hmem
    have hnP : n ∈ P0pre L R := N_subgroupOf_le_P0pre hC hnN
    have hgn : (g : ↥(NL L)) * n⁻¹ ∈ L.subgroupOf (NL L) := by
      refine (QuotientGroup.eq_one_iff ((g : ↥(NL L)) * n⁻¹)).1 ?_
      show mkG L ((g : ↥(NL L)) * n⁻¹) = 1
      rw [map_mul, map_inv, ← hnEq, mul_inv_cancel]
    have hgnP : (g : ↥(NL L)) * n⁻¹ ∈ P0pre L R :=
      (P0pre L R).mul_mem g.2 ((P0pre L R).inv_mem hnP)
    have hdecomp : g = ⟨(g : ↥(NL L)) * n⁻¹, hgnP⟩ * ⟨n, hnP⟩ := Subtype.ext (by simp)
    rw [hdecomp, map_mul, blockHom_apply_L hC hgn hgnP, blockHom_apply_N hC hnN hnP, one_mul]

private lemma Ltilde_le_ker_blockHom (hC : Levi108 K L R N Y ρ μ T) :
    (L.subgroupOf (NL L)).subgroupOf (P0pre L R) ≤ (blockHom hC).ker := by
  intro l hl
  rw [MonoidHom.mem_ker]
  have hl' : (l : ↥(NL L)) ∈ L.subgroupOf (NL L) := by
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_subgroupOf.1 hl
  exact blockHom_apply_L hC hl' l.2

private noncomputable def P0preToP0 (L R : Subgroup 𝓜) :
    ↥(P0pre L R) →* ↥(P0frak L R) where
  toFun g := ⟨mkG L (g : ↥(NL L)), g.2⟩
  map_one' := by ext; simp [mkG]
  map_mul' g h := by ext; simp [mkG]

private lemma P0preToP0_surjective (L R : Subgroup 𝓜) :
    Function.Surjective (P0preToP0 L R) := by
  intro x
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (L.subgroupOf (NL L)) (x : GG L)
  refine ⟨⟨g, ?_⟩, ?_⟩
  · rw [mem_P0pre_iff, hg]
    exact x.2
  · exact Subtype.ext hg

private lemma P0preToP0_ker (L R : Subgroup 𝓜) :
    (P0preToP0 L R).ker = (L.subgroupOf (NL L)).subgroupOf (P0pre L R) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    exact (QuotientGroup.eq_one_iff (g : ↥(NL L))).1 (congrArg Subtype.val h)
  · intro h
    exact Subtype.ext ((QuotientGroup.eq_one_iff (g : ↥(NL L))).2 h)

private noncomputable def P0quotEquiv (L R : Subgroup 𝓜) :
    (↥(P0pre L R) ⧸ (L.subgroupOf (NL L)).subgroupOf (P0pre L R)) ≃* ↥(P0frak L R) :=
  (QuotientGroup.quotientMulEquivOfEq (P0preToP0_ker L R).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (P0preToP0 L R) (P0preToP0_surjective L R))

private lemma P0quotEquiv_apply (L R : Subgroup 𝓜) (g : ↥(P0pre L R)) :
    P0quotEquiv L R (QuotientGroup.mk g) = P0preToP0 L R g := by
  simp [P0quotEquiv, QuotientGroup.quotientKerEquivOfSurjective, QuotientGroup.kerLift_mk]

private noncomputable def beta0 (hC : Levi108 K L R N Y ρ μ T) :
    ↥(P0frak L R) →* SpecialLinearGroup (Fin 2) K :=
  (QuotientGroup.lift ((L.subgroupOf (NL L)).subgroupOf (P0pre L R)) (blockHom hC)
    (Ltilde_le_ker_blockHom hC)).comp (P0quotEquiv L R).symm.toMonoidHom

private lemma beta0_apply (hC : Levi108 K L R N Y ρ μ T) (g : ↥(P0pre L R)) :
    beta0 hC (P0preToP0 L R g) = blockHom hC g := by
  have hsymm : (P0quotEquiv L R).symm (P0preToP0 L R g) = QuotientGroup.mk g := by
    apply (P0quotEquiv L R).injective
    rw [MulEquiv.apply_symm_apply, P0quotEquiv_apply]
  change (QuotientGroup.lift ((L.subgroupOf (NL L)).subgroupOf (P0pre L R)) (blockHom hC)
    (Ltilde_le_ker_blockHom hC)) ((P0quotEquiv L R).symm (P0preToP0 L R g)) = blockHom hC g
  rw [hsymm, QuotientGroup.lift_mk]

private lemma beta0_surjective (hC : Levi108 K L R N Y ρ μ T) :
    Function.Surjective (beta0 hC) := by
  intro A
  obtain ⟨g, hg⟩ := blockHom_surjective hC A
  exact ⟨P0preToP0 L R g, by rw [beta0_apply, hg]⟩

private lemma beta0_ker (hC : Levi108 K L R N Y ρ μ T) :
    (beta0 hC).ker = (Yhat L N).subgroupOf (P0frak L R) := by
  ext x
  obtain ⟨g, rfl⟩ := P0preToP0_surjective L R x
  rw [MonoidHom.mem_ker, beta0_apply]
  constructor
  · intro hb
    rw [Subgroup.mem_subgroupOf]
    exact (blockHom_eq_one_iff hC).1 hb
  · intro hx
    rw [Subgroup.mem_subgroupOf] at hx
    exact (blockHom_eq_one_iff hC).2 hx

private def permMat : Matrix (Fin 3) (Fin 3) K := !![0, 1, 0; 1, 0, 0; 0, 0, 1]

private lemma permMat_self : permMat (K := K) * permMat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [permMat, Matrix.mul_apply, Fin.sum_univ_three]

private lemma permMat_det : (permMat (K := K)).det = 1 := by
  rw [Matrix.det_fin_three]
  simp [permMat, CharTwo.neg_eq]

private lemma exists_permElem (hC : Levi108 K L R N Y ρ μ T) :
    ∃ r : ↥R, (ρ r : Matrix (Fin 3) (Fin 3) K) = permMat := by
  let B : GL (Fin 3) K := Matrix.GeneralLinearGroup.mkOfDetNeZero (permMat (K := K))
    (by rw [permMat_det]; exact one_ne_zero)
  have hBmat : (B : Matrix (Fin 3) (Fin 3) K) = permMat := rfl
  have hB : B ∈ ρ.range := by
    rw [hC.range_rho]
    exact mem_statedSL_of_det (by rw [hBmat, permMat_det])
  obtain ⟨r, hr⟩ := MonoidHom.mem_range.1 hB
  exact ⟨r, by rw [hr, hBmat]⟩

private lemma permMat_inv : (permMat (K := K))⁻¹ = permMat :=
  Matrix.inv_eq_right_inv permMat_self

private lemma permMat_conj_vecMulVec {u : Fin 3 → K} (hu0 : u 0 = 0) :
    permMat (K := K) * (1 + Matrix.vecMulVec (e₀ K) u) * permMat =
      1 + Matrix.vecMulVec (Pi.single 1 1) (permMat *ᵥ u) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [permMat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMulVec, Matrix.vecMul,
      dotProduct, e₀, hu0, Matrix.one_apply, Matrix.vecHead, Matrix.vecTail]

private noncomputable def rPerm (hC : Levi108 K L R N Y ρ μ T) : ↥R :=
  Classical.choose (exists_permElem hC)

private lemma rPerm_rho (hC : Levi108 K L R N Y ρ μ T) :
    (ρ (rPerm hC) : Matrix (Fin 3) (Fin 3) K) = permMat :=
  Classical.choose_spec (exists_permElem hC)

private noncomputable def conjL (hC : Levi108 K L R N Y ρ μ T) : Subgroup 𝓜 :=
  L.map (MulAut.conj (rPerm hC : 𝓜)).toMonoidHom

private noncomputable def Csub (hC : Levi108 K L R N Y ρ μ T) : Subgroup 𝓜 :=
  conjL hC ⊓ NL L

private lemma conjL_le_R (hC : Levi108 K L R N Y ρ μ T) : conjL hC ≤ R := by
  intro g hg
  obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.1 hg
  simpa [MulAut.conj_apply] using
    R.mul_mem (R.mul_mem (rPerm hC).2 (hC.L_le_R hl)) (R.inv_mem (rPerm hC).2)

private lemma Csub_le_R (hC : Levi108 K L R N Y ρ μ T) : Csub hC ≤ R :=
  (inf_le_left.trans (conjL_le_R hC))

private lemma Csub_le_NL (hC : Levi108 K L R N Y ρ μ T) : Csub hC ≤ NL L := inf_le_right

private lemma rho_conj_eq (hC : Levi108 K L R N Y ρ μ T) {l : 𝓜} (hl : l ∈ L) :
    let hR : (rPerm hC : 𝓜) * l * (rPerm hC : 𝓜)⁻¹ ∈ R :=
      R.mul_mem (R.mul_mem (rPerm hC).2 (hC.L_le_R hl)) (R.inv_mem (rPerm hC).2)
    (ρ ⟨(rPerm hC : 𝓜) * l * (rPerm hC : 𝓜)⁻¹, hR⟩ : Matrix (Fin 3) (Fin 3) K) =
      permMat * (ρ ⟨l, hC.L_le_R hl⟩ : Matrix (Fin 3) (Fin 3) K) * permMat := by
  intro hR
  let a : ↥R := ⟨(rPerm hC : 𝓜), (rPerm hC).2⟩
  let b : ↥R := ⟨l, hC.L_le_R hl⟩
  have hsub : (⟨(rPerm hC : 𝓜) * l * (rPerm hC : 𝓜)⁻¹, hR⟩ : ↥R) = a * b * a⁻¹ :=
    Subtype.ext rfl
  have h1 : (ρ (a * b * a⁻¹) : Matrix (Fin 3) (Fin 3) K) =
      (ρ a : Matrix (Fin 3) (Fin 3) K) * (ρ b : Matrix (Fin 3) (Fin 3) K) *
        (ρ a : Matrix (Fin 3) (Fin 3) K)⁻¹ := by
    simp only [map_mul, map_inv, GeneralLinearGroup.coe_mul, GeneralLinearGroup.coe_inv]
  have hρa : (ρ a : Matrix (Fin 3) (Fin 3) K) = permMat := rPerm_rho hC
  calc
    (ρ ⟨(rPerm hC : 𝓜) * l * (rPerm hC : 𝓜)⁻¹, hR⟩ : Matrix (Fin 3) (Fin 3) K) =
        (ρ (a * b * a⁻¹) : Matrix (Fin 3) (Fin 3) K) :=
      congrArg (fun x : ↥R => (ρ x : Matrix (Fin 3) (Fin 3) K)) hsub
    _ = (ρ a : Matrix (Fin 3) (Fin 3) K) * (ρ b : Matrix (Fin 3) (Fin 3) K) *
        (ρ a : Matrix (Fin 3) (Fin 3) K)⁻¹ := h1
    _ = permMat * (ρ b : Matrix (Fin 3) (Fin 3) K) * permMat := by
      rw [hρa, permMat_inv]

private noncomputable def Chat (hC : Levi108 K L R N Y ρ μ T) : Subgroup (GG L) :=
  ((Csub hC).subgroupOf (NL L)).map (mkG L)

private lemma Csub_isElemAbelian (hC : Levi108 K L R N Y ρ μ T) :
    IsElemAbelian 2 (Csub hC) :=
  (hC.elemAb_L.map (MulAut.conj (rPerm hC : 𝓜)).toMonoidHom).mono inf_le_left

private lemma Chat_isElemAbelian (hC : Levi108 K L R N Y ρ μ T) :
    IsElemAbelian 2 (Chat hC) :=
  ((Csub_isElemAbelian hC).subgroupOf (NL L)).map (mkG L)

private lemma Csub_rho00 (hC : Levi108 K L R N Y ρ μ T) {g : 𝓜} (hg : g ∈ Csub hC) :
    (ρ ⟨g, Csub_le_R hC hg⟩ : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 := by
  obtain ⟨l, hl, hgl⟩ := Subgroup.mem_map.1 ((inf_le_left : Csub hC ≤ conjL hC) hg)
  have hgl' : (rPerm hC : 𝓜) * l * (rPerm hC : 𝓜)⁻¹ = g := by
    simpa [conjL, MulAut.conj_apply] using hgl
  let hR : (rPerm hC : 𝓜) * l * (rPerm hC : 𝓜)⁻¹ ∈ R :=
    R.mul_mem (R.mul_mem (rPerm hC).2 (hC.L_le_R hl)) (R.inv_mem (rPerm hC).2)
  have hconj : (⟨g, Csub_le_R hC hg⟩ : ↥R) =
      ⟨(rPerm hC : 𝓜) * l * (rPerm hC : 𝓜)⁻¹, hR⟩ := by
    apply Subtype.ext
    exact hgl'.symm
  rw [show (ρ ⟨g, Csub_le_R hC hg⟩ : Matrix (Fin 3) (Fin 3) K) =
      (ρ ⟨(rPerm hC : 𝓜) * l * (rPerm hC : 𝓜)⁻¹, hR⟩ : Matrix (Fin 3) (Fin 3) K)
      from congrArg (fun x : ↥R => (ρ x : Matrix (Fin 3) (Fin 3) K)) hconj,
    rho_conj_eq hC hl]
  obtain ⟨u, hu0, hu⟩ := hC.rho_L l hl
  rw [hu, permMat_conj_vecMulVec hu0]
  simp [Matrix.vecMulVec, e₀]

private lemma Csub_mem_P0pre (hC : Levi108 K L R N Y ρ μ T) {g : 𝓜} (hg : g ∈ Csub hC) :
    (⟨g, Csub_le_NL hC hg⟩ : ↥(NL L)) ∈ P0pre L R := by
  rw [mem_P0pre_iff]
  refine (hC.mem_P0frak_iff ⟨g, Csub_le_NL hC hg⟩ (Csub_le_R hC hg)).2 ?_
  simpa using Csub_rho00 hC hg

private lemma Chat_le_P0 (hC : Levi108 K L R N Y ρ μ T) : Chat hC ≤ P0frak L R := by
  intro x hx
  obtain ⟨g, hgC, rfl⟩ := Subgroup.mem_map.1 hx
  have hpre := Csub_mem_P0pre hC (Subgroup.mem_subgroupOf.1 hgC)
  have heq : (⟨(g : 𝓜), Csub_le_NL hC (Subgroup.mem_subgroupOf.1 hgC)⟩ : ↥(NL L)) = g :=
    Subtype.ext rfl
  rwa [heq] at hpre

private lemma permMat_transpose : (permMat (K := K))ᵀ = permMat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [permMat, Matrix.transpose_apply]

private lemma N_conj_mem (hC : Levi108 K L R N Y ρ μ T) {r n : 𝓜} (hr : r ∈ R)
    (hn : n ∈ N) : r * n * r⁻¹ ∈ N := by
  have hnR : n ∈ R := hC.N_le_R hn
  let hR : r * n * r⁻¹ ∈ R := R.mul_mem (R.mul_mem hr hnR) (R.inv_mem hr)
  have h1 : (ρ ⟨n, hnR⟩ : GL (Fin 3) K) = 1 := Units.ext (rho_eq_one_of_mem_N hC hnR hn)
  have hmem : (⟨r * n * r⁻¹, hR⟩ : ↥R) ∈ ρ.ker := by
    rw [MonoidHom.mem_ker]
    have hsub : (⟨r * n * r⁻¹, hR⟩ : ↥R) = ⟨r, hr⟩ * ⟨n, hnR⟩ * ⟨r, hr⟩⁻¹ :=
      Subtype.ext rfl
    rw [hsub, map_mul, map_mul, map_inv, h1]
    simp
  rw [hC.ker_rho] at hmem
  exact Subgroup.mem_subgroupOf.1 hmem

private lemma rho_inv_perm (hC : Levi108 K L R N Y ρ μ T) :
    (ρ ((rPerm hC)⁻¹ : ↥R) : Matrix (Fin 3) (Fin 3) K) = permMat := by
  let a : ↥R := ⟨(rPerm hC : 𝓜), (rPerm hC).2⟩
  have hsub : ((rPerm hC)⁻¹ : ↥R) = a⁻¹ := Subtype.ext rfl
  rw [show (ρ ((rPerm hC)⁻¹ : ↥R) : Matrix (Fin 3) (Fin 3) K) =
      (ρ a⁻¹ : Matrix (Fin 3) (Fin 3) K) from
      congrArg (fun x : ↥R => (ρ x : Matrix (Fin 3) (Fin 3) K)) hsub,
    map_inv, GeneralLinearGroup.coe_inv, rPerm_rho, permMat_inv]

private lemma exists_conj_mem_L (hC : Levi108 K L R N Y ρ μ T) {n : ↥(NL L)}
    (hnN : n ∈ N.subgroupOf (NL L)) :
    ∃ m : 𝓜, ∃ (hmN : m ∈ N), ∃ l' : 𝓜, l' ∈ L ∧
      m = (rPerm hC : 𝓜) * l' * (rPerm hC : 𝓜)⁻¹ ∧
      mkG L ⟨m, hC.N_le_NL hmN⟩ = mkG L n := by
  have hn : (n : 𝓜) ∈ N := Subgroup.mem_subgroupOf.1 hnN
  let c : K := (Multiplicative.toAdd (μ ⟨(n : 𝓜), hn⟩)) 0
  obtain ⟨m, hmμ⟩ := hC.surjective_mu (Multiplicative.ofAdd (c • e₀ K))
  have hmN : (m : 𝓜) ∈ N := m.2
  have hmμ' : Multiplicative.toAdd (μ ⟨(m : 𝓜), hmN⟩) = c • e₀ K := by
    simpa using congrArg Multiplicative.toAdd hmμ
  let l' : 𝓜 := (rPerm hC : 𝓜)⁻¹ * (m : 𝓜) * (rPerm hC : 𝓜)
  have hl'N : l' ∈ N := by
    simpa [l'] using N_conj_mem hC (R.inv_mem (rPerm hC).2) hmN
  have hmu0 : (Multiplicative.toAdd (μ ⟨l', hl'N⟩)) 0 = 0 := by
    have hconj := hC.mu_conj (r := ((rPerm hC)⁻¹ : ↥R)) (hr := R.inv_mem (rPerm hC).2)
      (n := (m : 𝓜)) (hn := hmN) (n' := l') (hn' := hl'N) (by simp [l'])
    rw [hconj, hmμ']
    have hinvmat : ((((ρ ((rPerm hC)⁻¹ : ↥R))⁻¹ : GL (Fin 3) K)) :
        Matrix (Fin 3) (Fin 3) K) = permMat := by
      rw [GeneralLinearGroup.coe_inv, rho_inv_perm hC, permMat_inv]
    rw [hinvmat, permMat_transpose]
    simp [permMat, e₀, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Pi.smul_apply]
  have hl'L : l' ∈ L := (hC.mem_L_iff_mu l' hl'N).2 hmu0
  have hmnN : (m : 𝓜) * (n : 𝓜)⁻¹ ∈ N := N.mul_mem hmN (N.inv_mem hn)
  have hmnμ0 : (Multiplicative.toAdd (μ ⟨(m : 𝓜) * (n : 𝓜)⁻¹, hmnN⟩)) 0 = 0 := by
    have h1 : Multiplicative.toAdd (μ ⟨(m : 𝓜) * (n : 𝓜)⁻¹, hmnN⟩) =
        Multiplicative.toAdd (μ ⟨(m : 𝓜), hmN⟩) -
          Multiplicative.toAdd (μ ⟨(n : 𝓜), hn⟩) := by
      have hsub : (⟨(m : 𝓜) * (n : 𝓜)⁻¹, hmnN⟩ : ↥N) =
          ⟨(m : 𝓜), hmN⟩ * (⟨(n : 𝓜), hn⟩ : ↥N)⁻¹ := Subtype.ext rfl
      rw [show Multiplicative.toAdd (μ ⟨(m : 𝓜) * (n : 𝓜)⁻¹, hmnN⟩) =
          Multiplicative.toAdd (μ (⟨(m : 𝓜), hmN⟩ * (⟨(n : 𝓜), hn⟩ : ↥N)⁻¹)) from
          congrArg (fun y : ↥N => Multiplicative.toAdd (μ y)) hsub,
        map_mul, map_inv, toAdd_mul, toAdd_inv]
      abel
    rw [h1, hmμ']
    simp [c, e₀, Pi.smul_apply, sub_eq_add_neg]
  have hmnL : (m : 𝓜) * (n : 𝓜)⁻¹ ∈ L := (hC.mem_L_iff_mu _ hmnN).2 hmnμ0
  have hmnNL : (m : 𝓜) * (n : 𝓜)⁻¹ ∈ NL L := hC.N_le_NL hmnN
  have heq : mkG L ⟨(m : 𝓜), hC.N_le_NL hmN⟩ = mkG L n := by
    refine (QuotientGroup.eq_iff_div_mem).2 ?_
    simpa [div_eq_mul_inv, Subgroup.mem_subgroupOf] using hmnL
  refine ⟨m, hmN, l', hl'L, ?_, heq⟩
  simp only [l']
  group

private lemma Yhat_le_Chat (hC : Levi108 K L R N Y ρ μ T) : Yhat L N ≤ Chat hC := by
  intro x hx
  obtain ⟨n, hnN, rfl⟩ := Subgroup.mem_map.1 hx
  obtain ⟨m, hmN, l', hl'L, hm_eq, heq⟩ := exists_conj_mem_L hC hnN
  have hmNL : (m : 𝓜) ∈ NL L := hC.N_le_NL hmN
  have hmC : (m : 𝓜) ∈ Csub hC := by
    refine ⟨?_, hmNL⟩
    rw [hm_eq]
    exact Subgroup.mem_map.2 ⟨l', hl'L, by simp [MulAut.conj_apply]⟩
  have hmChat : mkG L ⟨(m : 𝓜), hmNL⟩ ∈ Chat hC :=
    Subgroup.mem_map_of_mem (f := mkG L) (Subgroup.mem_subgroupOf.2 hmC)
  rw [heq] at hmChat
  exact hmChat

private lemma rho_conj_transvection (hC : Levi108 K L R N Y ρ μ T) {l : 𝓜} (hl : l ∈ L)
    (a : K)
    (hlρ : (ρ ⟨l, hC.L_le_R hl⟩ : Matrix (Fin 3) (Fin 3) K) =
      1 + Matrix.vecMulVec (e₀ K) (a • Pi.single 2 1)) :
    let hR : (rPerm hC : 𝓜) * l * (rPerm hC : 𝓜)⁻¹ ∈ R :=
      R.mul_mem (R.mul_mem (rPerm hC).2 (hC.L_le_R hl)) (R.inv_mem (rPerm hC).2)
    (ρ ⟨(rPerm hC : 𝓜) * l * (rPerm hC : 𝓜)⁻¹, hR⟩ : Matrix (Fin 3) (Fin 3) K) =
      Matrix.transvection 1 2 a := by
  intro hR
  rw [rho_conj_eq hC hl, hlρ, permMat_conj_vecMulVec (by simp)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [permMat, Matrix.vecMulVec, e₀, Matrix.transvection, Pi.single, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three, Pi.smul_apply]

private lemma Yhat_le_P0frak (hC : Levi108 K L R N Y ρ μ T) :
    Yhat L N ≤ P0frak L R := by
  intro x hx
  obtain ⟨n, hnN, rfl⟩ := Subgroup.mem_map.1 hx
  have hn : (n : 𝓜) ∈ N := Subgroup.mem_subgroupOf.1 hnN
  refine (hC.mem_P0frak_iff n (hC.N_le_R hn)).2 ?_
  rw [rho_eq_one_of_mem_N hC (hC.N_le_R hn) hn]
  simp

private lemma card_Yhat_subgroupOf (hC : Levi108 K L R N Y ρ μ T) :
    Nat.card ((Yhat L N).subgroupOf (P0frak L R)) = Nat.card K := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Yhat_le_P0frak hC)).toEquiv]
  exact hC.card_Yhat

private lemma card_P0 (hC : Levi108 K L R N Y ρ μ T) :
    Nat.card (P0frak L R) = Nat.card K * (Nat.card K * (Nat.card K ^ 2 - 1)) := by
  have hq : Nat.card (↥(P0frak L R) ⧸ (beta0 hC).ker) =
      Nat.card (SpecialLinearGroup (Fin 2) K) :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective (beta0 hC)
      (beta0_surjective hC)).toEquiv
  rw [beta0_ker hC] at hq
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((Yhat L N).subgroupOf (P0frak L R))
  rw [hq, card_Yhat_subgroupOf hC] at hcard
  have hSL : Nat.card (SpecialLinearGroup (Fin 2) K) = Nat.card K * (Nat.card K ^ 2 - 1) := by
    rw [← card_statedSL 2 K, card_statedSL_two K]
  rw [hSL] at hcard
  rw [hcard]
  ring

private noncomputable def transvectionHom :
    Multiplicative K →* SpecialLinearGroup (Fin 2) K where
  toFun m := Matrix.SpecialLinearGroup.transvection (i := 0) (j := 1) (by decide)
    (Multiplicative.toAdd m)
  map_one' := by
    rw [show Multiplicative.toAdd (1 : Multiplicative K) = 0 from rfl]
    simp
  map_mul' x y := by
    rw [show Multiplicative.toAdd (x * y) =
      Multiplicative.toAdd x + Multiplicative.toAdd y from rfl,
      Matrix.SpecialLinearGroup.transvection_add (by decide)]

private lemma transvectionHom_injective : Function.Injective (transvectionHom (K := K)) := by
  intro x y h
  have h' := congrFun (congrFun (congrArg Subtype.val h) 0) 1
  change (Matrix.transvection (n := Fin 2) 0 1 (Multiplicative.toAdd x)) 0 1 =
    (Matrix.transvection (n := Fin 2) 0 1 (Multiplicative.toAdd y)) 0 1 at h'
  simp [Matrix.transvection, Matrix.one_apply, Matrix.single] at h'
  exact Multiplicative.toAdd.injective h'

private noncomputable def rootGroup : Subgroup (SpecialLinearGroup (Fin 2) K) :=
  (⊤ : Subgroup (Multiplicative K)).map transvectionHom

private lemma card_rootGroup : Nat.card (rootGroup (K := K)) = Nat.card K := by
  rw [rootGroup, Subgroup.card_map_of_injective transvectionHom_injective]
  rw [Nat.card_congr Subgroup.topEquiv.toEquiv, Nat.card_congr Multiplicative.toAdd]

private noncomputable def phi (hC : Levi108 K L R N Y ρ μ T) :
    ↥(Chat hC) →* SpecialLinearGroup (Fin 2) K :=
  (beta0 hC).comp (Subgroup.inclusion (Chat_le_P0 hC))

private lemma phi_ker (hC : Levi108 K L R N Y ρ μ T) :
    (phi hC).ker = (Yhat L N).subgroupOf (Chat hC) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, phi, MonoidHom.comp_apply]
  rw [← MonoidHom.mem_ker, beta0_ker, Subgroup.mem_subgroupOf]
  rfl

private lemma phi_isPGroup (hC : Levi108 K L R N Y ρ μ T) :
    IsPGroup 2 (phi hC).range := by
  exact (Chat_isElemAbelian hC).isPGroup.of_surjective (phi hC).rangeRestrict
    (phi hC).rangeRestrict_surjective

private lemma card_phi_range_le (hC : Levi108 K L R N Y ρ μ T) :
    Nat.card (phi hC).range ≤ Nat.card K :=
  CFSG.RankThree.GF2n.Smith81.D2.card_le_of_isPGroup_sl2 (phi_isPGroup hC)

private lemma blockHom_eq_transvection (hC : Levi108 K L R N Y ρ μ T)
    {g : ↥(P0pre L R)} {a : K}
    (hmat : (ρ ⟨(g : 𝓜), P0pre_le_R hC⟩ : Matrix (Fin 3) (Fin 3) K) =
      Matrix.transvection 1 2 a) :
    blockHom hC g = transvectionHom (Multiplicative.ofAdd a) := by
  ext i j
  change (ρ ⟨(g : 𝓜), P0pre_le_R hC⟩ : Matrix (Fin 3) (Fin 3) K) i.succ j.succ =
    (Matrix.transvection (n := Fin 2) 0 1 a) i j
  rw [hmat]
  fin_cases i <;> fin_cases j <;> simp [Matrix.transvection]

private lemma transvection_mem_range (hC : Levi108 K L R N Y ρ μ T) (a : K) :
    transvectionHom (Multiplicative.ofAdd a) ∈ (phi hC).range := by
  obtain ⟨l, hlL, hlρ⟩ := hC.exists_L (a • Pi.single 2 1) (by simp)
  let hR : (rPerm hC : 𝓜) * l * (rPerm hC : 𝓜)⁻¹ ∈ R :=
    R.mul_mem (R.mul_mem (rPerm hC).2 (hC.L_le_R hlL)) (R.inv_mem (rPerm hC).2)
  have hmat : (ρ ⟨(rPerm hC : 𝓜) * l * (rPerm hC : 𝓜)⁻¹, hR⟩ :
      Matrix (Fin 3) (Fin 3) K) = Matrix.transvection 1 2 a :=
    rho_conj_transvection hC hlL a hlρ
  have hNL : (rPerm hC : 𝓜) * l * (rPerm hC : 𝓜)⁻¹ ∈ NL L := by
    refine (hC.mem_normalizer_iff _ hR).2 ⟨?_, ?_⟩
    · rw [hmat]; simp [Matrix.transvection]
    · rw [hmat]; simp [Matrix.transvection]
  have hCsub : (rPerm hC : 𝓜) * l * (rPerm hC : 𝓜)⁻¹ ∈ Csub hC := by
    refine ⟨Subgroup.mem_map.2 ⟨l, hlL, ?_⟩, hNL⟩
    simp [MulAut.conj_apply]
  let g : ↥(P0pre L R) :=
    ⟨⟨(rPerm hC : 𝓜) * l * (rPerm hC : 𝓜)⁻¹, hNL⟩, Csub_mem_P0pre hC hCsub⟩
  let x : ↥(Chat hC) :=
    ⟨mkG L (g : ↥(NL L)), Subgroup.mem_map_of_mem (f := mkG L) (Subgroup.mem_subgroupOf.2 hCsub)⟩
  have hmat' : (ρ ⟨(g : 𝓜), P0pre_le_R hC⟩ : Matrix (Fin 3) (Fin 3) K) =
      Matrix.transvection 1 2 a := by
    have hsub : (⟨(g : 𝓜), P0pre_le_R hC⟩ : ↥R) =
        ⟨(rPerm hC : 𝓜) * l * (rPerm hC : 𝓜)⁻¹, hR⟩ := Subtype.ext rfl
    rw [show (ρ ⟨(g : 𝓜), P0pre_le_R hC⟩ : Matrix (Fin 3) (Fin 3) K) =
        (ρ ⟨(rPerm hC : 𝓜) * l * (rPerm hC : 𝓜)⁻¹, hR⟩ : Matrix (Fin 3) (Fin 3) K)
        from congrArg (fun y : ↥R => (ρ y : Matrix (Fin 3) (Fin 3) K)) hsub, hmat]
  have hphi : phi hC x = transvectionHom (Multiplicative.ofAdd a) := by
    have hbeta : phi hC x = beta0 hC (P0preToP0 L R g) := by
      apply congrArg (beta0 hC)
      exact Subtype.ext rfl
    rw [hbeta, beta0_apply]
    exact blockHom_eq_transvection hC hmat'
  exact MonoidHom.mem_range.2 ⟨x, hphi⟩

private lemma rootGroup_le_range (hC : Levi108 K L R N Y ρ μ T) :
    rootGroup (K := K) ≤ (phi hC).range := by
  intro y hy
  rw [rootGroup] at hy
  obtain ⟨m, -, rfl⟩ := Subgroup.mem_map.1 hy
  rw [show m = Multiplicative.ofAdd (Multiplicative.toAdd m) from rfl]
  exact transvection_mem_range hC (Multiplicative.toAdd m)

private lemma card_phi_range (hC : Levi108 K L R N Y ρ μ T) :
    Nat.card (phi hC).range = Nat.card K := by
  refine le_antisymm (card_phi_range_le hC) ?_
  rw [← card_rootGroup (K := K)]
  exact Subgroup.card_le_of_le (rootGroup_le_range hC)

private lemma card_Chat (hC : Levi108 K L R N Y ρ μ T) :
    Nat.card (Chat hC) = Nat.card K * Nat.card K := by
  have hquot : Nat.card (↥(Chat hC) ⧸ (phi hC).ker) = Nat.card (phi hC).range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange (phi hC)).toEquiv
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup ((phi hC).ker)
  rw [hquot, phi_ker hC] at hcard
  have hY : Nat.card ((Yhat L N).subgroupOf (Chat hC)) = Nat.card K := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Yhat_le_Chat hC)).toEquiv]
    exact hC.card_Yhat
  rw [hY, card_phi_range hC] at hcard
  exact hcard

private lemma card_Chatsub (hC : Levi108 K L R N Y ρ μ T) :
    Nat.card ((Chat hC).subgroupOf (P0frak L R)) = Nat.card K * Nat.card K := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Chat_le_P0 hC)).toEquiv]
  exact card_Chat hC

private lemma Chatsub_isPGroup (hC : Levi108 K L R N Y ρ μ T) :
    IsPGroup 2 ((Chat hC).subgroupOf (P0frak L R)) :=
  ((Chat_isElemAbelian hC).subgroupOf (P0frak L R)).isPGroup

private lemma Chatsub_index (hC : Levi108 K L R N Y ρ μ T) :
    ((Chat hC).subgroupOf (P0frak L R)).index = Nat.card K * Nat.card K - 1 := by
  have hmul := Subgroup.card_mul_index ((Chat hC).subgroupOf (P0frak L R))
  have hP0 := card_P0 hC
  have hS := card_Chatsub hC
  rw [hP0, hS] at hmul
  have hqpos : 0 < Nat.card K := Nat.card_pos
  have hpos : 0 < Nat.card K * Nat.card K := Nat.mul_pos hqpos hqpos
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [hmul, show Nat.card K * Nat.card K = Nat.card K ^ 2 from (pow_two _).symm]
  ring

private lemma Chatsub_not_dvd_index (hC : Levi108 K L R N Y ρ μ T) :
    ¬ 2 ∣ ((Chat hC).subgroupOf (P0frak L R)).index := by
  rw [Chatsub_index hC]
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  have hEven : Even (Nat.card K) := by
    rw [Nat.card_eq_fintype_card, hn]
    exact Nat.even_pow.mpr ⟨even_two, n.pos.ne'⟩
  have hEven2 : Even (Nat.card K * Nat.card K) := hEven.mul_right _
  have hle : 1 ≤ Nat.card K * Nat.card K := by
    have hq : 0 < Nat.card K := Nat.card_pos
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hq.ne' hq.ne')
  exact (Nat.Even.sub_odd hle hEven2 odd_one).not_two_dvd_nat

private noncomputable def ChatSylow (hC : Levi108 K L R N Y ρ μ T) :
    Sylow 2 ↥(P0frak L R) :=
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  (Chatsub_isPGroup hC).toSylow (Chatsub_not_dvd_index hC)

private lemma V_le_center (hC : Levi108 K L R N Y ρ μ T) :
    (Yhat L N).subgroupOf (P0frak L R) ≤ Subgroup.center ↥(P0frak L R) := by
  intro v hv
  rw [Subgroup.mem_center_iff]
  intro x
  apply Subtype.ext
  have hv' : (v : GG L) ∈ Yhat L N := Subgroup.mem_subgroupOf.1 hv
  have hcomm := (Subgroup.mem_centralizer_iff.1 (hC.Yhat_le_centralizer_P0frak hv'))
    (x : GG L) x.2
  simpa using hcomm

private lemma V_normal (hC : Levi108 K L R N Y ρ μ T) :
    ((Yhat L N).subgroupOf (P0frak L R)).Normal :=
  Subgroup.normal_of_le_center (V_le_center hC)

private lemma V_isElemAbelian (hC : Levi108 K L R N Y ρ μ T) :
    IsElemAbelian 2 ((Yhat L N).subgroupOf (P0frak L R)) :=
  hC.isElemAbelian_Yhat.subgroupOf _

private lemma Chatsub_isElemAbelian (hC : Levi108 K L R N Y ρ μ T) :
    IsElemAbelian 2 ((Chat hC).subgroupOf (P0frak L R)) :=
  (Chat_isElemAbelian hC).subgroupOf _

private lemma exists_compl_Chatsub (hC : Levi108 K L R N Y ρ μ T) :
    ∃ K : Subgroup ↥(P0frak L R), K ≤ (Chat hC).subgroupOf (P0frak L R) ∧
      ((Yhat L N).subgroupOf (P0frak L R)) ⊓ K = ⊥ ∧
      ((Yhat L N).subgroupOf (P0frak L R)) ⊔ K = (Chat hC).subgroupOf (P0frak L R) := by
  have hle : (Yhat L N).subgroupOf (P0frak L R) ≤ (Chat hC).subgroupOf (P0frak L R) := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact Yhat_le_Chat hC hx
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.HardMathSupport.Solomon.Coordinator.i224_exists_compl
    (Chatsub_isElemAbelian hC) hle

private lemma exists_compl_P0 (hC : Levi108 K L R N Y ρ μ T) :
    ∃ K : Subgroup ↥(P0frak L R),
      ((Yhat L N).subgroupOf (P0frak L R)) ⊓ K = ⊥ ∧
      ((Yhat L N).subgroupOf (P0frak L R)) ⊔ K = ⊤ := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : ((Yhat L N).subgroupOf (P0frak L R)).Normal := V_normal hC
  haveI : IsMulCommutative ((Yhat L N).subgroupOf (P0frak L R)) :=
    (V_isElemAbelian hC).1
  have hVp : IsPGroup 2 ((Yhat L N).subgroupOf (P0frak L R)) :=
    (V_isElemAbelian hC).isPGroup
  have hGas := CFSG.Quasithin.gaschutz (p := 2)
    (V := (Yhat L N).subgroupOf (P0frak L R)) hVp (ChatSylow hC)
  refine hGas.2 ?_
  obtain ⟨K, hKle, hVK, hsupK⟩ := exists_compl_Chatsub hC
  exact ⟨K, hKle, hVK, hsupK⟩

private noncomputable def Kbeta (hC : Levi108 K L R N Y ρ μ T)
    (Kc : Subgroup ↥(P0frak L R)) : ↥Kc →* SpecialLinearGroup (Fin 2) K :=
  (beta0 hC).comp Kc.subtype

private lemma Kbeta_injective (hC : Levi108 K L R N Y ρ μ T)
    {Kc : Subgroup ↥(P0frak L R)}
    (hVK : ((Yhat L N).subgroupOf (P0frak L R)) ⊓ Kc = ⊥) :
    Function.Injective (Kbeta hC Kc) := by
  intro a b h
  have hprod : Kbeta hC Kc (a * b⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  have hker : (⟨a * b⁻¹, Kc.mul_mem a.2 (Kc.inv_mem b.2)⟩ : ↥Kc) ∈
      (Kbeta hC Kc).ker := MonoidHom.mem_ker.2 hprod
  have hker' : (((a * b⁻¹ : ↥Kc) : ↥(P0frak L R))) ∈ (beta0 hC).ker := by
    simpa [Kbeta] using hker
  rw [beta0_ker] at hker'
  have hmemV : ((a * b⁻¹ : ↥Kc) : ↥(P0frak L R)) ∈
      (Yhat L N).subgroupOf (P0frak L R) := Subgroup.mem_subgroupOf.2 hker'
  have hmemK : ((a * b⁻¹ : ↥Kc) : ↥(P0frak L R)) ∈ Kc :=
    Kc.mul_mem a.2 (Kc.inv_mem b.2)
  have hone : a * b⁻¹ = 1 := by
    have hmem : ((a * b⁻¹ : ↥Kc) : ↥(P0frak L R)) ∈
        ((Yhat L N).subgroupOf (P0frak L R)) ⊓ Kc := ⟨hmemV, hmemK⟩
    rw [hVK] at hmem
    apply Subtype.ext
    simpa using hmem
  exact mul_inv_eq_one.mp hone

private lemma Kbeta_surjective (hC : Levi108 K L R N Y ρ μ T)
    {Kc : Subgroup ↥(P0frak L R)}
    (hsupK : ((Yhat L N).subgroupOf (P0frak L R)) ⊔ Kc = ⊤) :
    Function.Surjective (Kbeta hC Kc) := by
  haveI : ((Yhat L N).subgroupOf (P0frak L R)).Normal := V_normal hC
  intro A
  obtain ⟨x, hx⟩ := beta0_surjective hC A
  have hxmem : x ∈ ((Yhat L N).subgroupOf (P0frak L R)) ⊔ Kc :=
    hsupK ▸ Subgroup.mem_top x
  obtain ⟨v, hv, k, hk, rfl⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := (Yhat L N).subgroupOf (P0frak L R))
      (t := Kc) (x := x)).1 hxmem
  refine ⟨⟨k, hk⟩, ?_⟩
  have hvker : v ∈ (beta0 hC).ker := by
    rw [beta0_ker]
    exact Subgroup.mem_subgroupOf.2 hv
  have hv1 : beta0 hC v = 1 := MonoidHom.mem_ker.1 hvker
  have hxk : beta0 hC k = A := by
    rw [← hx, map_mul, hv1, one_mul]
  simpa [Kbeta] using hxk

private lemma K_equiv_SL2 (hC : Levi108 K L R N Y ρ μ T) {Kc : Subgroup ↥(P0frak L R)}
    (hVK : ((Yhat L N).subgroupOf (P0frak L R)) ⊓ Kc = ⊥)
    (hsupK : ((Yhat L N).subgroupOf (P0frak L R)) ⊔ Kc = ⊤) :
    Nonempty (↥Kc ≃* SpecialLinearGroup (Fin 2) K) :=
  ⟨MulEquiv.ofBijective (Kbeta hC Kc)
    ⟨Kbeta_injective hC hVK, Kbeta_surjective hC hsupK⟩⟩

private lemma K_commutator_eq_self (hC : Levi108 K L R N Y ρ μ T)
    {Kc : Subgroup ↥(P0frak L R)}
    (hVK : ((Yhat L N).subgroupOf (P0frak L R)) ⊓ Kc = ⊥)
    (hsupK : ((Yhat L N).subgroupOf (P0frak L R)) ⊔ Kc = ⊤) :
    ⁅Kc, Kc⁆ = Kc := by
  obtain ⟨e⟩ := K_equiv_SL2 hC hVK hsupK
  have hSL : commutator (SpecialLinearGroup (Fin 2) K) = ⊤ :=
    CFSG.RankThree.GF2n.Smith81.D2.sl2_commutator_eq_top hC.four_le_card
  have hperf : commutator ↥Kc = ⊤ := by
    have hmap := Subgroup.map_commutator (H₁ := (⊤ : Subgroup (SpecialLinearGroup (Fin 2) K)))
      (H₂ := ⊤) e.symm.toMonoidHom
    rw [show ⁅(⊤ : Subgroup (SpecialLinearGroup (Fin 2) K)), ⊤⁆ = ⊤ from hSL,
      Subgroup.map_top, MonoidHom.range_eq_top.2 e.symm.surjective] at hmap
    exact hmap.symm
  have hmapK := Subgroup.map_subtype_commutator Kc
  rw [hperf, Subgroup.map_top, Subgroup.range_subtype] at hmapK
  exact hmapK.symm

private lemma K_normal (hC : Levi108 K L R N Y ρ μ T) {Kc : Subgroup ↥(P0frak L R)}
    (hsupK : ((Yhat L N).subgroupOf (P0frak L R)) ⊔ Kc = ⊤) : Kc.Normal := by
  haveI : ((Yhat L N).subgroupOf (P0frak L R)).Normal := V_normal hC
  refine ⟨fun k hk g => ?_⟩
  have hg : g ∈ ((Yhat L N).subgroupOf (P0frak L R)) ⊔ Kc := hsupK ▸ Subgroup.mem_top g
  obtain ⟨v, hv, k', hk', rfl⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := (Yhat L N).subgroupOf (P0frak L R))
      (t := Kc) (x := g)).1 hg
  have hvcomm : ∀ y : ↥(P0frak L R), v * y = y * v := fun y =>
    ((Subgroup.mem_center_iff.1 (V_le_center hC hv)) y).symm
  have hconj : (v * k') * k * (v * k')⁻¹ = k' * k * k'⁻¹ := by
    calc (v * k') * k * (v * k')⁻¹ = v * (k' * k * k'⁻¹) * v⁻¹ := by group
      _ = (k' * k * k'⁻¹) * v * v⁻¹ := by rw [hvcomm (k' * k * k'⁻¹)]
      _ = k' * k * k'⁻¹ := by simp
  rw [hconj]
  exact Kc.mul_mem (Kc.mul_mem hk' hk) (Kc.inv_mem hk')

private lemma commutator_P0_le_K (hC : Levi108 K L R N Y ρ μ T)
    {Kc : Subgroup ↥(P0frak L R)}
    (hVK : ((Yhat L N).subgroupOf (P0frak L R)) ⊓ Kc = ⊥)
    (hsupK : ((Yhat L N).subgroupOf (P0frak L R)) ⊔ Kc = ⊤) :
    commutator ↥(P0frak L R) ≤ Kc := by
  haveI : Kc.Normal := K_normal hC hsupK
  have hVcomm : IsMulCommutative ((Yhat L N).subgroupOf (P0frak L R)) :=
    (V_isElemAbelian hC).1
  have hsup : Kc ⊔ ((Yhat L N).subgroupOf (P0frak L R)) = ⊤ := by
    rw [sup_comm]
    exact hsupK
  exact Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup hVcomm

private lemma Xlevi_eq_commutator_map (hC : Levi108 K L R N Y ρ μ T) :
    Xlevi L R = (commutator ↥(P0frak L R)).map (P0frak L R).subtype := by
  exact (Subgroup.map_subtype_commutator (P0frak L R)).symm

private lemma Xlevi_eq_X1 (hC : Levi108 K L R N Y ρ μ T)
    {Kc : Subgroup ↥(P0frak L R)}
    (hVK : ((Yhat L N).subgroupOf (P0frak L R)) ⊓ Kc = ⊥)
    (hsupK : ((Yhat L N).subgroupOf (P0frak L R)) ⊔ Kc = ⊤) :
    Xlevi L R = Kc.map (P0frak L R).subtype := by
  apply le_antisymm
  · rw [Xlevi_eq_commutator_map hC]
    exact Subgroup.map_mono (f := (P0frak L R).subtype) (commutator_P0_le_K hC hVK hsupK)
  · have hperf := K_commutator_eq_self hC hVK hsupK
    have hKle : Kc ≤ commutator ↥(P0frak L R) := by
      rw [← hperf]
      exact Subgroup.commutator_mono le_top le_top
    rw [Xlevi_eq_commutator_map hC]
    exact Subgroup.map_mono (f := (P0frak L R).subtype) hKle

private lemma exists_Xlevi_block_data (hC : Levi108 K L R N Y ρ μ T)
    (A : SpecialLinearGroup (Fin 2) K) :
    ∃ g : ↥(NL L), mkG L g ∈ Xlevi L R ∧ ∃ hg : (g : 𝓜) ∈ R,
      ∀ i j : Fin 2, (ρ ⟨g, hg⟩ : Matrix (Fin 3) (Fin 3) K) i.succ j.succ =
        (A : Matrix (Fin 2) (Fin 2) K) i j := by
  obtain ⟨Kc, hVK, hsupK⟩ := exists_compl_P0 hC
  obtain ⟨k, hk⟩ := Kbeta_surjective hC hsupK A
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (L.subgroupOf (NL L)) (k : ↥(P0frak L R))
  have hxP0pre : x ∈ P0pre L R := by
    rw [mem_P0pre_iff, hx]
    exact (k : ↥(P0frak L R)).2
  have hxR : (x : 𝓜) ∈ R := P0pre_le_R hC (g := ⟨x, hxP0pre⟩)
  have hxX1 : mkG L x ∈ Kc.map (P0frak L R).subtype := by
    rw [hx]
    exact Subgroup.mem_map_of_mem (f := (P0frak L R).subtype) k.2
  have hxXlevi : mkG L x ∈ Xlevi L R := by
    rw [Xlevi_eq_X1 hC hVK hsupK]
    exact hxX1
  refine ⟨x, hxXlevi, hxR, ?_⟩
  intro i j
  have hkbeta : (Kbeta hC Kc k : Matrix (Fin 2) (Fin 2) K) i j =
      (A : Matrix (Fin 2) (Fin 2) K) i j := by
    rw [hk]
  have hblock : (Kbeta hC Kc k : Matrix (Fin 2) (Fin 2) K) i j =
      (ρ ⟨(x : 𝓜), hxR⟩ : Matrix (Fin 3) (Fin 3) K) i.succ j.succ := by
    have h1 : (Kbeta hC Kc k : Matrix (Fin 2) (Fin 2) K) = block hC ⟨x, hxP0pre⟩ := by
      have hk_eq : Kbeta hC Kc k = beta0 hC (P0preToP0 L R ⟨x, hxP0pre⟩) := by
        rw [show P0preToP0 L R ⟨x, hxP0pre⟩ = k from Subtype.ext hx]
        rfl
      rw [hk_eq, beta0_apply]
      rfl
    rw [h1]
    rfl
  rw [← hblock, hkbeta]

private lemma scalar_det (ω : K) (hω3 : ω ^ 3 = 1) :
    (Matrix.scalar (Fin 3) ω : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  rw [Matrix.det_fin_three]
  simp [Matrix.scalar_apply]
  rw [show ω * ω * ω = ω ^ 3 by ring, hω3]

private lemma exists_scalar_r (hC : Levi108 K L R N Y ρ μ T) {ω : K}
    (hω3 : ω ^ 3 = 1) :
    ∃ r : ↥R, (ρ r : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) ω := by
  let B : GL (Fin 3) K := Matrix.GeneralLinearGroup.mkOfDetNeZero
    (Matrix.scalar (Fin 3) ω) (by rw [scalar_det ω hω3]; exact one_ne_zero)
  have hBmat : (B : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) ω := rfl
  have hB : B ∈ ρ.range := by
    rw [hC.range_rho]
    exact mem_statedSL_of_det (by rw [hBmat, scalar_det ω hω3])
  obtain ⟨r, hr⟩ := MonoidHom.mem_range.1 hB
  exact ⟨r, by rw [hr, hBmat]⟩

private lemma scalar_pow_three (ω : K) (hω3 : ω ^ 3 = 1) :
    (Matrix.scalar (Fin 3) ω : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
  rw [Matrix.scalar_apply, Matrix.diagonal_pow]
  have hfun : (fun x : Fin 3 => ω) ^ 3 = (fun _ => (1 : K)) := by
    funext i
    simpa using hω3
  rw [hfun]
  simp

private lemma exists_omega (hC : Levi108 K L R N Y ρ μ T) (hq : Nat.card K = 4) :
    ∃ ω : K, ω ≠ 1 ∧ ω ^ 3 = 1 := by
  obtain ⟨ω, hω0, hω1⟩ := CFSG.RankThree.GF2n.Smith81.D2.exists_ne_zero_ne_one hC.four_le_card
  refine ⟨ω, hω1, ?_⟩
  haveI : Fintype K := Fintype.ofFinite K
  have h := FiniteField.pow_card_sub_one_eq_one ω hω0
  rw [show Fintype.card K = 4 by rw [← Nat.card_eq_fintype_card]; exact hq] at h
  norm_num at h
  exact h

private lemma V_map_subtype (hC : Levi108 K L R N Y ρ μ T) :
    ((Yhat L N).subgroupOf (P0frak L R)).map (P0frak L R).subtype = Yhat L N := by
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left]
  exact Yhat_le_P0frak hC

private lemma inf_Yhat_Xlevi (hC : Levi108 K L R N Y ρ μ T) :
    Yhat L N ⊓ Xlevi L R = ⊥ := by
  obtain ⟨Kc, hVK, hsupK⟩ := exists_compl_P0 hC
  have hinf := congrArg (Subgroup.map (P0frak L R).subtype) hVK
  rw [Subgroup.map_inf _ _ _ Subtype.coe_injective, V_map_subtype hC, Subgroup.map_bot] at hinf
  rw [Xlevi_eq_X1 hC hVK hsupK]
  exact hinf

private lemma exists_tau_order (hC : Levi108 K L R N Y ρ μ T) (hq : Nat.card K = 4) :
    ∃ (r : ↥R) (ω : K), ω ≠ 1 ∧ ω ^ 3 = 1 ∧
      (ρ r : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) ω ∧
      (r : 𝓜) ^ 6 = 1 := by
  obtain ⟨ω, hω1, hω3⟩ := exists_omega hC hq
  obtain ⟨r, hr⟩ := exists_scalar_r hC hω3
  have h3R : (r : 𝓜) ^ 3 ∈ R := R.pow_mem r.2 3
  have hGL : (ρ r : GL (Fin 3) K) ^ 3 = 1 := by
    apply Units.ext
    change (ρ r : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1
    rw [hr]
    exact scalar_pow_three ω hω3
  have hρr3 : (ρ ⟨(r : 𝓜) ^ 3, h3R⟩ : Matrix (Fin 3) (Fin 3) K) = 1 := by
    have hsub : (⟨(r : 𝓜) ^ 3, h3R⟩ : ↥R) = r ^ 3 := Subtype.ext rfl
    rw [show (ρ ⟨(r : 𝓜) ^ 3, h3R⟩ : Matrix (Fin 3) (Fin 3) K) =
        (ρ (r ^ 3) : Matrix (Fin 3) (Fin 3) K) from
        congrArg (fun x : ↥R => (ρ x : Matrix (Fin 3) (Fin 3) K)) hsub,
      map_pow]
    exact congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) hGL
  have hr3N : (r : 𝓜) ^ 3 ∈ N := by
    have hmem : (⟨(r : 𝓜) ^ 3, h3R⟩ : ↥R) ∈ ρ.ker :=
      MonoidHom.mem_ker.2 (Units.ext hρr3)
    rw [hC.ker_rho] at hmem
    exact Subgroup.mem_subgroupOf.1 hmem
  have h6 : (r : 𝓜) ^ 6 = 1 := by
    have h2 := hC.elemAb_N.2 ((r : 𝓜) ^ 3) hr3N
    rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul]
    exact h2
  exact ⟨r, ω, hω1, hω3, hr, h6⟩

private lemma tau_of_data (hC : Levi108 K L R N Y ρ μ T) {r : ↥R} {ω : K}
    (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1)
    (hρ : (ρ r : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) ω)
    (h6 : (r : 𝓜) ^ 6 = 1) :
    ∃ (τ : ↥(NL L)) (hτ : (τ : 𝓜) ∈ R), orderOf (τ : 𝓜) = 3 ∧
      (ρ ⟨τ, hτ⟩ : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) ω := by
  have hNL : (r : 𝓜) ∈ NL L := by
    refine (hC.mem_normalizer_iff (r : 𝓜) r.2).2 ⟨?_, ?_⟩
    · rw [hρ]; simp [Matrix.scalar_apply]
    · rw [hρ]; simp [Matrix.scalar_apply]
  let τ : ↥(NL L) := ⟨(r : 𝓜) ^ 4, (NL L).pow_mem hNL 4⟩
  have hτR : (τ : 𝓜) ∈ R := R.pow_mem r.2 4
  have hτ3 : (τ : 𝓜) ^ 3 = 1 := by
    calc (τ : 𝓜) ^ 3 = ((r : 𝓜) ^ 4) ^ 3 := rfl
      _ = (r : 𝓜) ^ 12 := by rw [← pow_mul]
      _ = ((r : 𝓜) ^ 6) ^ 2 := by rw [show (12 : ℕ) = 6 * 2 by norm_num, pow_mul]
      _ = 1 := by rw [h6, one_pow]
  have hτρ : (ρ ⟨(τ : 𝓜), hτR⟩ : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) ω := by
    have hpow : (((ρ r : GL (Fin 3) K)) ^ 4 : Matrix (Fin 3) (Fin 3) K) =
        Matrix.scalar (Fin 3) ω := by
      change (ρ r : Matrix (Fin 3) (Fin 3) K) ^ 4 = Matrix.scalar (Fin 3) ω
      rw [hρ]
      rw [show (Matrix.scalar (Fin 3) ω : Matrix (Fin 3) (Fin 3) K) ^ 4 =
          Matrix.scalar (Fin 3) (ω ^ 4) by
        rw [Matrix.scalar_apply, Matrix.diagonal_pow]
        rfl]
      rw [show ω ^ 4 = ω by rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ, hω3, one_mul]]
    have hτeq : (⟨(τ : 𝓜), hτR⟩ : ↥R) = r ^ 4 := Subtype.ext rfl
    rw [show (ρ ⟨(τ : 𝓜), hτR⟩ : Matrix (Fin 3) (Fin 3) K) =
        (ρ (r ^ 4) : Matrix (Fin 3) (Fin 3) K) from
        congrArg (fun x : ↥R => (ρ x : Matrix (Fin 3) (Fin 3) K)) hτeq, map_pow]
    exact hpow
  have hτne : (τ : 𝓜) ≠ 1 := by
    intro h
    have hρτ1 : (ρ ⟨(τ : 𝓜), hτR⟩ : Matrix (Fin 3) (Fin 3) K) = 1 := by
      have hτ1 : (⟨(τ : 𝓜), hτR⟩ : ↥R) = 1 := Subtype.ext h
      rw [hτ1, map_one, GeneralLinearGroup.coe_one]
    have hsc : Matrix.scalar (Fin 3) ω = 1 := by rw [← hτρ, hρτ1]
    have hsc' : Matrix.scalar (Fin 3) ω = Matrix.scalar (Fin 3) (1 : K) := by
      simpa using hsc
    exact hω1 (Matrix.scalar_inj.1 hsc')
  exact ⟨τ, hτR, orderOf_eq_prime hτ3 hτne, hτρ⟩

private lemma commutator_N_of_scalar (hC : Levi108 K L R N Y ρ μ T) {τ g : ↥(NL L)}
    (hτR : (τ : 𝓜) ∈ R) (hgR : (g : 𝓜) ∈ R) {ω : K}
    (hτρ : (ρ ⟨(τ : 𝓜), hτR⟩ : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) ω) :
    ((⁅τ, g⁆ : ↥(NL L)) : 𝓜) ∈ N := by
  have hcR : ((⁅τ, g⁆ : ↥(NL L)) : 𝓜) ∈ R :=
    R.mul_mem (R.mul_mem (R.mul_mem hτR hgR) (R.inv_mem hτR)) (R.inv_mem hgR)
  have hGL : (ρ ⟨((⁅τ, g⁆ : ↥(NL L)) : 𝓜), hcR⟩ : GL (Fin 3) K) = 1 := by
    have hcsub : (⟨((⁅τ, g⁆ : ↥(NL L)) : 𝓜), hcR⟩ : ↥R) =
        ⁅(⟨(τ : 𝓜), hτR⟩ : ↥R), (⟨(g : 𝓜), hgR⟩ : ↥R)⁆ := Subtype.ext rfl
    rw [show (ρ ⟨((⁅τ, g⁆ : ↥(NL L)) : 𝓜), hcR⟩ : GL (Fin 3) K) =
        ρ ⁅(⟨(τ : 𝓜), hτR⟩ : ↥R), (⟨(g : 𝓜), hgR⟩ : ↥R)⁆ from
        congrArg (fun x : ↥R => ρ x) hcsub, map_commutatorElement]
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    apply Units.ext
    change (ρ ⟨(τ : 𝓜), hτR⟩ : Matrix (Fin 3) (Fin 3) K) *
        (ρ ⟨(g : 𝓜), hgR⟩ : Matrix (Fin 3) (Fin 3) K) =
      (ρ ⟨(g : 𝓜), hgR⟩ : Matrix (Fin 3) (Fin 3) K) *
        (ρ ⟨(τ : 𝓜), hτR⟩ : Matrix (Fin 3) (Fin 3) K)
    rw [hτρ]
    exact Matrix.scalar_comm ω (fun _ => Commute.all _ _) _
  have hmem : (⟨((⁅τ, g⁆ : ↥(NL L)) : 𝓜), hcR⟩ : ↥R) ∈ ρ.ker :=
    MonoidHom.mem_ker.2 hGL
  rw [hC.ker_rho] at hmem
  exact Subgroup.mem_subgroupOf.1 hmem

private lemma tau_mem_Kfrak (hC : Levi108 K L R N Y ρ μ T) {τ : ↥(NL L)} {ω : K}
    (hτR : (τ : 𝓜) ∈ R)
    (hτρ : (ρ ⟨(τ : 𝓜), hτR⟩ : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) ω) :
    mkG L τ ∈ Kfrak L R := by
  rw [Kfrak, Subgroup.mem_centralizer_iff]
  intro x hx
  have hxPfrak : x ∈ Pfrak L R :=
    (Xlevi_le_P0frak L R).trans (P0frak_le_Pfrak L R) hx
  obtain ⟨g, hg, hgx⟩ := Subgroup.mem_map.1 hxPfrak
  have hgR : (g : 𝓜) ∈ R := Subgroup.mem_subgroupOf.1 hg
  have hcN : ((⁅τ, g⁆ : ↥(NL L)) : 𝓜) ∈ N :=
    commutator_N_of_scalar hC hτR hgR hτρ
  have hcY : mkG L ⟨((⁅τ, g⁆ : ↥(NL L)) : 𝓜), (⁅τ, g⁆ : ↥(NL L)).2⟩ ∈ Yhat L N :=
    Subgroup.mem_map_of_mem (f := mkG L) (Subgroup.mem_subgroupOf.2 hcN)
  have hcX : ⁅mkG L τ, x⁆ ∈ Xlevi L R := by
    have hnorm : Pfrak L R ≤ Subgroup.normalizer (Xlevi L R : Set (GG L)) :=
      hC.Pfrak_le_Nfrak.trans hC.Nfrak_le_normalizer_Xlevi
    have hle : ⁅Pfrak L R, Xlevi L R⁆ ≤ Xlevi L R :=
      (Subgroup.le_normalizer_iff_commutator_le_right).1 hnorm
    have hτP : mkG L τ ∈ Pfrak L R :=
      Subgroup.mem_map_of_mem (f := mkG L) (Subgroup.mem_subgroupOf.2 hτR)
    exact hle (Subgroup.commutator_mem_commutator hτP hx)
  have hcomm_eq : ⁅mkG L τ, x⁆ =
      mkG L ⟨((⁅τ, g⁆ : ↥(NL L)) : 𝓜), (⁅τ, g⁆ : ↥(NL L)).2⟩ := by
    rw [← hgx]
    exact (map_commutatorElement (mkG L) τ g).symm
  have hinf : ⁅mkG L τ, x⁆ ∈ Xlevi L R ⊓ Yhat L N := ⟨hcX, hcomm_eq ▸ hcY⟩
  rw [inf_comm, inf_Yhat_Xlevi hC] at hinf
  have hone : ⁅mkG L τ, x⁆ = 1 := by simpa using hinf
  exact (commutatorElement_eq_one_iff_mul_comm.mp hone).symm

private lemma sup_Yhat_Xlevi (hC : Levi108 K L R N Y ρ μ T) :
    Yhat L N ⊔ Xlevi L R = P0frak L R := by
  obtain ⟨Kc, hVK, hsupK⟩ := exists_compl_P0 hC
  have hsup := congrArg (Subgroup.map (P0frak L R).subtype) hsupK
  rw [Subgroup.map_sup, V_map_subtype hC, Subgroup.map_top, Subgroup.range_subtype] at hsup
  rw [Xlevi_eq_X1 hC hVK hsupK]
  exact hsup

private lemma Xlevi_mulEquiv_SL2 (hC : Levi108 K L R N Y ρ μ T) :
    Nonempty (Xlevi L R ≃* SpecialLinearGroup (Fin 2) K) := by
  obtain ⟨Kc, hVK, hsupK⟩ := exists_compl_P0 hC
  obtain ⟨e⟩ := K_equiv_SL2 hC hVK hsupK
  have hX : Xlevi L R = Kc.map (P0frak L R).subtype := Xlevi_eq_X1 hC hVK hsupK
  have emap : (Kc.map (P0frak L R).subtype) ≃* ↥Kc :=
    (Subgroup.equivMapOfInjective Kc (P0frak L R).subtype Subtype.coe_injective).symm
  exact ⟨hX ▸ (emap.trans e)⟩

private lemma exists_tau_data (hC : Levi108 K L R N Y ρ μ T) (hq : Nat.card K = 4) :
    ∃ τ : ↥(NL L), ∃ hτ : (τ : 𝓜) ∈ R, orderOf (τ : 𝓜) = 3 ∧
      ∃ ω : K, ω ≠ 1 ∧ ω ^ 3 = 1 ∧
        (ρ ⟨τ, hτ⟩ : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) ω ∧
        mkG L τ ∈ Kfrak L R := by
  obtain ⟨r, ω, hω1, hω3, hρ, h6⟩ := exists_tau_order hC hq
  obtain ⟨τ, hτ, horder, hτρ⟩ := tau_of_data hC hω1 hω3 hρ h6
  exact ⟨τ, hτ, horder, ω, hω1, hω3, hτρ, tau_mem_Kfrak hC hτ hτρ⟩

theorem Levi108.Yhat_sup_Xlevi (hC : Levi108 K L R N Y ρ μ T) :
    Yhat L N ⊔ Xlevi L R = P0frak L R :=
  sup_Yhat_Xlevi hC

theorem Levi108.exists_Xlevi_block (hC : Levi108 K L R N Y ρ μ T)
    (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    ∃ g : ↥(NL L), mkG L g ∈ Xlevi L R ∧ ∃ hg : (g : 𝓜) ∈ R,
      ∀ i j : Fin 2, (ρ ⟨g, hg⟩ : Matrix (Fin 3) (Fin 3) K) i.succ j.succ =
        (A : Matrix (Fin 2) (Fin 2) K) i j :=
  exists_Xlevi_block_data hC A

theorem Levi108.nonempty_mulEquiv_SL2 (hC : Levi108 K L R N Y ρ μ T) :
    Nonempty (Xlevi L R ≃* Matrix.SpecialLinearGroup (Fin 2) K) :=
  Xlevi_mulEquiv_SL2 hC

theorem Levi108.exists_tau (hC : Levi108 K L R N Y ρ μ T) (hq : Nat.card K = 4) :
    ∃ τ : ↥(NL L), ∃ hτ : (τ : 𝓜) ∈ R, orderOf (τ : 𝓜) = 3 ∧ ∃ ω : K, ω ≠ 1 ∧ ω ^ 3 = 1 ∧
      (ρ ⟨τ, hτ⟩ : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) ω ∧
      mkG L τ ∈ Kfrak L R :=
  exists_tau_data hC hq

end CFSG.RankThree.GF2n.Stroth80.Sec108
