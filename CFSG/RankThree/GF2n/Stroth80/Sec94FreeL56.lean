module

public import CFSG.RankThree.GF2n.Stroth80.Sec94FreeL123
public import CFSG.RankThree.GF2n.Stroth80.Sec94FreeL4
public import CFSG.RankThree.GF2n.Stroth80.Sec94FreeL7
public import CFSG.RankThree.GF2n.Stroth80.Sec97FiveLineX
public import CFSG.RankThree.GF2n.Stroth80.Sec92SplitN
public import CFSG.RankThree.GF2n.Stroth80.Sec94FreeL56U

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.G11.P3Ortho.Om4
open CFSG.Open.StatedAPI
open scoped commutatorElement Matrix


namespace S94F

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

private theorem l56_sub_one_eq_of_mulVec {K : Type} [Field K] [CharP K 2]
    (A : Matrix.SpecialLinearGroup (Fin 2) K) {a : Fin 2 → K} (ha : a ≠ 0)
    (hAa : (A : Matrix (Fin 2) (Fin 2) K) *ᵥ a = a) :
    ∃ c : Fin 2 → K, (A : Matrix (Fin 2) (Fin 2) K) - 1 = Matrix.vecMulVec a c ∧ c ⬝ᵥ a = 0 := by
  classical
  by_cases hA1 : (A : Matrix (Fin 2) (Fin 2) K) = 1
  · exact ⟨0, by rw [hA1, sub_self, Matrix.vecMulVec_zero], by simp⟩
  · have hdetT : ((A : Matrix (Fin 2) (Fin 2) K)ᵀ).det = 1 := by
      rw [Matrix.det_transpose]
      exact A.2
    have hvec : a ᵥ* (A : Matrix (Fin 2) (Fin 2) K)ᵀ = a := by
      rw [Matrix.vecMul_transpose]
      exact hAa
    have hneT : (A : Matrix (Fin 2) (Fin 2) K)ᵀ ≠ 1 := fun h => hA1 (by
      rw [← Matrix.transpose_transpose (A : Matrix (Fin 2) (Fin 2) K), h, Matrix.transpose_one])
    obtain ⟨c, -, hc⟩ := HS9.exists_vecMulVec_one_sub_of_vecMul_eq_self hdetT ha hvec hneT
    have hsub : (A : Matrix (Fin 2) (Fin 2) K) - 1 = Matrix.vecMulVec a c := by
      have h := congrArg Matrix.transpose hc
      rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_transpose,
        Matrix.transpose_vecMulVec] at h
      rw [← h]
      ext i j
      simp only [Matrix.sub_apply]
      rw [CharTwo.sub_eq_add, CharTwo.sub_eq_add, add_comm]
    refine ⟨c, hsub, ?_⟩
    have h0 : ((A : Matrix (Fin 2) (Fin 2) K) - 1) *ᵥ a = 0 := by
      rw [Matrix.sub_mulVec, hAa, Matrix.one_mulVec, sub_self]
    rw [hsub, Matrix.vecMulVec_mulVec] at h0
    obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact ha (funext hcon)
    have h1 := congrFun h0 i
    simp only [Pi.smul_apply, Pi.zero_apply, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op] at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd h2 hi
    · exact h2

private theorem l56_sub_one_mul_sub_one {K : Type} [Field K] [CharP K 2]
    (A A' : Matrix.SpecialLinearGroup (Fin 2) K) {a : Fin 2 → K} (ha : a ≠ 0)
    (hAa : (A : Matrix (Fin 2) (Fin 2) K) *ᵥ a = a)
    (hA'a : (A' : Matrix (Fin 2) (Fin 2) K) *ᵥ a = a) :
    ((A' : Matrix (Fin 2) (Fin 2) K) - 1) * ((A : Matrix (Fin 2) (Fin 2) K) - 1) = 0 := by
  obtain ⟨c, hc, -⟩ := l56_sub_one_eq_of_mulVec A ha hAa
  obtain ⟨c', hc', hc'a⟩ := l56_sub_one_eq_of_mulVec A' ha hA'a
  rw [hc, hc', Matrix.vecMulVec_mul_vecMulVec, hc'a, zero_smul, Matrix.vecMulVec_zero]

private theorem l56_sub_one_mul_sub_one_right {K : Type} [Field K] [CharP K 2]
    (C C' : Matrix.SpecialLinearGroup (Fin 2) K) {b : Fin 2 → K} (hb : b ≠ 0)
    (hCb : b ᵥ* (C : Matrix (Fin 2) (Fin 2) K) = b)
    (hC'b : b ᵥ* (C' : Matrix (Fin 2) (Fin 2) K) = b) :
    ((C : Matrix (Fin 2) (Fin 2) K) - 1) * ((C' : Matrix (Fin 2) (Fin 2) K) - 1) = 0 := by
  have hT : ∀ D : Matrix.SpecialLinearGroup (Fin 2) K, b ᵥ* (D : Matrix (Fin 2) (Fin 2) K) = b →
      ((D.transpose : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ b = b :=
    fun D hD => by
      rw [Matrix.SpecialLinearGroup.coe_transpose, Matrix.mulVec_transpose]
      exact hD
  have h := l56_sub_one_mul_sub_one C.transpose C'.transpose hb (hT C hCb) (hT C' hC'b)
  have h2 := congrArg Matrix.transpose h
  rw [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_sub, Matrix.transpose_one,
    Matrix.SpecialLinearGroup.coe_transpose, Matrix.SpecialLinearGroup.coe_transpose,
    Matrix.transpose_transpose, Matrix.transpose_transpose, Matrix.transpose_zero] at h2
  exact h2

theorem l56_comm_comm_mem_Z (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {X Y : Subgroup G}
    (hsplit : HS9.Split95 M Q Z B t X Y) {y y' v : G} (hy : y ∈ LB M Q B ⊓ Y)
    (hy' : y' ∈ LB M Q B ⊓ Y) (hv : v ∈ Vt M (LB M Q B) B Z t) :
    ⁅y', ⁅y, v⁆⁆ ∈ Z := by
  classical
  obtain ⟨K, fK, finK, chK, hn, φ, ψ, u, hK, hrange, hker, hnorm, hψ, hBiff, -, hdet, hu0⟩ :=
    HS9.sec9_coord h34 hc hs
  haveI := hn
  haveI : CharP K 2 := chK
  obtain ⟨a, b, ha, hb, hu⟩ := HS9.exists_vecMulVec_of_det_eq_zero hdet hu0
  have hfac := HS9.sec97_factor_pair h34 h311a hc hs hsplit hK φ hrange hker
  have hsplit0 := hsplit
  obtain ⟨⟨-, -, -, hYR, -, -, -⟩, -, -⟩ := hsplit0
  have hyR : y ∈ Rt M (LB M Q B) t := hYR hy.2
  have hy'R : y' ∈ Rt M (LB M Q B) t := hYR hy'.2
  set w : ↥(Vt M (LB M Q B) B Z t) :=
    ⟨⁅y, v⁆, comm_mem_of_le_normalizer hnorm ⟨y, hyR⟩ ⟨v, hv⟩⟩ with hw
  have h1 : HS9.cmat ψ w = Ψ K (φ ⟨y, hyR⟩) (HS9.cmat ψ ⟨v, hv⟩) - HS9.cmat ψ ⟨v, hv⟩ :=
    HS9.cmat_comm_eq φ ψ hψ hnorm ⟨y, hyR⟩ ⟨v, hv⟩
  have h2 := HS9.cmat_comm_eq φ ψ hψ hnorm ⟨y', hy'R⟩ w
  have hfu : ∀ {z : G} (hz : z ∈ LB M Q B ⊓ Y) (hzR : z ∈ Rt M (LB M Q B) t),
      Ψ K (φ ⟨z, hzR⟩) (toMat K u) = toMat K u := fun hz hzR =>
    HS9.apply_toMat_u_eq hc φ ψ hψ hnorm u hBiff hz.1 hzR
  suffices h0 : HS9.cmat ψ ⟨⁅((⟨y', hy'R⟩ : ↥(Rt M (LB M Q B) t)) : G), (w : G)⁆,
      comm_mem_of_le_normalizer hnorm ⟨y', hy'R⟩ w⟩ = 0 from (HS9.cmat_eq_zero_iff ψ _).mp h0
  rw [h2, h1]
  rcases hfac with ⟨hYeq, -⟩ | ⟨hYeq, -⟩
  ·
    have hmem : ∀ {z : G} (hz : z ∈ LB M Q B ⊓ Y) (hzR : z ∈ Rt M (LB M Q B) t),
        ∃ A : Matrix.SpecialLinearGroup (Fin 2) K, rho' K (A, 1) = Ψ K (φ ⟨z, hzR⟩) ∧
          (A : Matrix (Fin 2) (Fin 2) K) *ᵥ a = a := by
      intro z hz hzR
      have hzMem : Ψ K (φ ⟨z, hzR⟩) ∈ HS9.leftF K := by
        rw [← hYeq]
        exact ⟨⟨z, hzR⟩, Subgroup.mem_subgroupOf.mpr hz.2, rfl⟩
      obtain ⟨A, hA0⟩ := hzMem
      have hA : rho' K (A, 1) = Ψ K (φ ⟨z, hzR⟩) := by simpa using hA0
      refine ⟨A, hA, ?_⟩
      have hAu : (A : Matrix (Fin 2) (Fin 2) K) * toMat K u = toMat K u := by
        rw [← HS9.rho'_inl_apply, hA]
        exact hfu hz hzR
      rw [hu, Matrix.mul_vecMulVec] at hAu
      obtain ⟨j, hj⟩ : ∃ j, b j ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hb (funext hcon)
      funext i
      have h' := congrFun (congrFun hAu i) j
      simp only [Matrix.vecMulVec_apply] at h'
      exact mul_right_cancel₀ hj h'
    obtain ⟨A, hA, hAa⟩ := hmem hy hyR
    obtain ⟨A', hA', hA'a⟩ := hmem hy' hy'R
    rw [← hA, ← hA', HS9.rho'_inl_apply, HS9.rho'_inl_apply]
    have key := l56_sub_one_mul_sub_one A A' ha hAa hA'a
    have e : (A' : Matrix (Fin 2) (Fin 2) K) * ((A : Matrix (Fin 2) (Fin 2) K) *
          HS9.cmat ψ ⟨v, hv⟩ - HS9.cmat ψ ⟨v, hv⟩) -
        ((A : Matrix (Fin 2) (Fin 2) K) * HS9.cmat ψ ⟨v, hv⟩ - HS9.cmat ψ ⟨v, hv⟩) =
        (((A' : Matrix (Fin 2) (Fin 2) K) - 1) * ((A : Matrix (Fin 2) (Fin 2) K) - 1)) *
          HS9.cmat ψ ⟨v, hv⟩ := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_assoc]
      abel
    rw [e, key, Matrix.zero_mul]
  ·
    have hmem : ∀ {z : G} (hz : z ∈ LB M Q B ⊓ Y) (hzR : z ∈ Rt M (LB M Q B) t),
        ∃ Bm : Matrix.SpecialLinearGroup (Fin 2) K, rho' K (1, Bm) = Ψ K (φ ⟨z, hzR⟩) ∧
          b ᵥ* ((Bm⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = b := by
      intro z hz hzR
      have hzMem : Ψ K (φ ⟨z, hzR⟩) ∈ HS9.rightF K := by
        rw [← hYeq]
        exact ⟨⟨z, hzR⟩, Subgroup.mem_subgroupOf.mpr hz.2, rfl⟩
      obtain ⟨Bm, hB0⟩ := hzMem
      have hB : rho' K (1, Bm) = Ψ K (φ ⟨z, hzR⟩) := by simpa using hB0
      refine ⟨Bm, hB, ?_⟩
      have hMu : toMat K u * ((Bm⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K) = toMat K u := by
        rw [← HS9.rho'_inr_apply, hB]
        exact hfu hz hzR
      rw [hu, Matrix.vecMulVec_mul] at hMu
      obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact ha (funext hcon)
      funext j
      have h' := congrFun (congrFun hMu i) j
      simp only [Matrix.vecMulVec_apply] at h'
      exact mul_left_cancel₀ hi h'
    obtain ⟨Bm, hBm, hBb⟩ := hmem hy hyR
    obtain ⟨Bm', hBm', hB'b⟩ := hmem hy' hy'R
    rw [← hBm, ← hBm', HS9.rho'_inr_apply, HS9.rho'_inr_apply]
    have key := l56_sub_one_mul_sub_one_right Bm⁻¹ Bm'⁻¹ hb hBb hB'b
    set C := ((Bm⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
    set C' := ((Bm'⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
    have e : (HS9.cmat ψ ⟨v, hv⟩ * C - HS9.cmat ψ ⟨v, hv⟩) * C' -
        (HS9.cmat ψ ⟨v, hv⟩ * C - HS9.cmat ψ ⟨v, hv⟩) =
        HS9.cmat ψ ⟨v, hv⟩ * ((C - 1) * (C' - 1)) := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
    rw [e, key, Matrix.mul_zero]

theorem l56_mem_CN_of_comm_uline (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {X Y : Subgroup G}
    (hsplit : HS9.Split95 M Q Z B t X Y) {x : G} (hx : x ∈ X)
    (hfix : ∀ v ∈ HS9.Uline Z B X, ⁅x, v⁆ ∈ Z) : x ∈ hc.CN t := by
  classical
  obtain ⟨K, fK, finK, chK, hn, φ, ψ, u, hK, hrange, hker, hnorm, hψ, hBiff, -, hdet, hu0⟩ :=
    HS9.sec9_coord h34 hc hs
  haveI := hn
  haveI : CharP K 2 := chK
  obtain ⟨a, b, ha, hb, hu⟩ := HS9.exists_vecMulVec_of_det_eq_zero hdet hu0
  have hfac := HS9.sec97_factor_pair h34 h311a hc hs hsplit hK φ hrange hker
  obtain ⟨⟨-, hXR, -, -, -, -, -⟩, -, -⟩ := hsplit
  have hxR : x ∈ Rt M (LB M Q B) t := hXR hx
  obtain ⟨b₀, hb₀B, hb₀u⟩ := (hBiff u).mpr ⟨1, (one_smul K u).symm⟩
  have hcb₀ : HS9.cmat ψ b₀ = toMat K u := by
    unfold HS9.cmat
    rw [hb₀u]
  have hkey : ∀ r : ↥(Rt M (LB M Q B) t), (r : G) ∈ X →
      Ψ K (φ ⟨x, hxR⟩) (Ψ K (φ r) (toMat K u)) = Ψ K (φ r) (toMat K u) := by
    intro r hrX
    have hvV : (r : G) * b₀ * (r : G)⁻¹ ∈ Vt M (LB M Q B) B Z t :=
      (Subgroup.mem_normalizer_iff.mp (hnorm r.2) b₀).mp b₀.2
    have hvU : (r : G) * b₀ * (r : G)⁻¹ ∈ HS9.Uline Z B X := by
      refine HS9.conjSubgroup_le_Uline hrX ?_
      rw [mem_conjSubgroup, show (r : G)⁻¹ * ((r : G) * b₀ * (r : G)⁻¹) * r = b₀ by group]
      exact hb₀B
    have hcv : HS9.cmat ψ ⟨_, hvV⟩ = Ψ K (φ r) (toMat K u) := by
      rw [HS9.cmat_conj ψ φ hψ r b₀ ⟨_, hvV⟩ rfl, hcb₀]
    have h0 : HS9.cmat ψ ⟨⁅((⟨x, hxR⟩ : ↥(Rt M (LB M Q B) t)) : G),
        (((⟨_, hvV⟩ : ↥(Vt M (LB M Q B) B Z t))) : G)⁆,
        comm_mem_of_le_normalizer hnorm ⟨x, hxR⟩ ⟨_, hvV⟩⟩ = 0 :=
      (HS9.cmat_eq_zero_iff ψ _).mpr (hfix _ hvU)
    rw [HS9.cmat_comm_eq φ ψ hψ hnorm ⟨x, hxR⟩ ⟨_, hvV⟩, hcv] at h0
    exact sub_eq_zero.mp h0
  suffices h1 : Ψ K (φ ⟨x, hxR⟩) = 1 by
    refine Ctx.mem_CN.mpr ⟨hxR, fun v hv => ?_⟩
    have h0 := HS9.cmat_comm_eq φ ψ hψ hnorm ⟨x, hxR⟩ ⟨v, hv⟩
    rw [h1] at h0
    have h2 : HS9.cmat ψ ⟨⁅((⟨x, hxR⟩ : ↥(Rt M (LB M Q B) t)) : G),
        ((⟨v, hv⟩ : ↥(Vt M (LB M Q B) B Z t)) : G)⁆,
        comm_mem_of_le_normalizer hnorm ⟨x, hxR⟩ ⟨v, hv⟩⟩ = 0 := by
      rw [h0]
      exact sub_self _
    exact (HS9.cmat_eq_zero_iff ψ _).mp h2
  have hsingle : ∀ j : Fin 2, (Pi.single j (1 : K) : Fin 2 → K) ≠ 0 := fun j h => by
    have := congrFun h j
    simp at this
  rcases hfac with ⟨-, hXeq⟩ | ⟨-, hXeq⟩
  ·
    have hxF : Ψ K (φ ⟨x, hxR⟩) ∈ HS9.rightF K := by
      rw [← hXeq]
      exact ⟨⟨x, hxR⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    obtain ⟨B', hB'0⟩ := hxF
    have hB' : rho' K (1, B') = Ψ K (φ ⟨x, hxR⟩) := by simpa using hB'0
    obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact ha (funext hcon)
    have hrow : ∀ g : Matrix.SpecialLinearGroup (Fin 2) K,
        (b ᵥ* (g : Matrix (Fin 2) (Fin 2) K)) ᵥ*
            ((B'⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
          b ᵥ* (g : Matrix (Fin 2) (Fin 2) K) := by
      intro g
      have hgF : rho' K (1, g⁻¹) ∈ HS9.rightF K := ⟨g⁻¹, rfl⟩
      rw [← hXeq] at hgF
      obtain ⟨r, hrX, hrg⟩ := hgF
      have hrg' : Ψ K (φ r) = rho' K (1, g⁻¹) := hrg
      have h := hkey r (Subgroup.mem_subgroupOf.mp hrX)
      rw [hrg', ← hB', HS9.rho'_inr_apply, HS9.rho'_inr_apply, inv_inv, hu,
        Matrix.vecMulVec_mul, Matrix.vecMulVec_mul] at h
      funext j
      have h' := congrFun (congrFun h i) j
      simp only [Matrix.vecMulVec_apply] at h'
      exact mul_left_cancel₀ hi h'
    have hB'1 : ((B'⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
      ext i' j
      obtain ⟨g₁, hg₁⟩ := HS9.exists_sl2_mulVec_eq hb (hsingle i')
      have h := congrFun (hrow g₁.transpose) j
      rw [Matrix.SpecialLinearGroup.coe_transpose, Matrix.vecMul_transpose, hg₁,
        Matrix.single_one_vecMul] at h
      simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using h
    have hB'eq : B' = 1 := inv_eq_one.mp (Subtype.ext hB'1)
    rw [← hB', hB'eq]
    exact map_one (rho' K)
  ·
    have hxF : Ψ K (φ ⟨x, hxR⟩) ∈ HS9.leftF K := by
      rw [← hXeq]
      exact ⟨⟨x, hxR⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    obtain ⟨A', hA'0⟩ := hxF
    have hA' : rho' K (A', 1) = Ψ K (φ ⟨x, hxR⟩) := by simpa using hA'0
    obtain ⟨j, hj⟩ : ∃ j, b j ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hb (funext hcon)
    have hcol : ∀ g : Matrix.SpecialLinearGroup (Fin 2) K,
        (A' : Matrix (Fin 2) (Fin 2) K) *ᵥ ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ a) =
          (g : Matrix (Fin 2) (Fin 2) K) *ᵥ a := by
      intro g
      have hgF : rho' K (g, 1) ∈ HS9.leftF K := ⟨g, rfl⟩
      rw [← hXeq] at hgF
      obtain ⟨r, hrX, hrg⟩ := hgF
      have hrg' : Ψ K (φ r) = rho' K (g, 1) := hrg
      have h := hkey r (Subgroup.mem_subgroupOf.mp hrX)
      rw [hrg', ← hA', HS9.rho'_inl_apply, HS9.rho'_inl_apply, hu, Matrix.mul_vecMulVec,
        Matrix.mul_vecMulVec] at h
      funext i
      have h' := congrFun (congrFun h i) j
      simp only [Matrix.vecMulVec_apply] at h'
      exact mul_right_cancel₀ hj h'
    have hA'1 : (A' : Matrix (Fin 2) (Fin 2) K) = 1 := by
      ext i j'
      obtain ⟨g₁, hg₁⟩ := HS9.exists_sl2_mulVec_eq ha (hsingle j')
      have h := congrFun (hcol g₁) i
      rw [hg₁, Matrix.mulVec_single_one] at h
      simpa [Matrix.one_apply, Pi.single_apply] using h
    have hA'eq : A' = 1 := Subtype.ext hA'1
    rw [← hA', hA'eq]
    exact map_one (rho' K)

theorem l56_split95_conj (hc : Ctx M Q Z B) {t : G} {X Y : Subgroup G}
    (hsplit : HS9.Split95 M Q Z B t X Y) {z : G} (hz : z ∈ M) :
    HS9.Split95 M Q Z B (z * t * z⁻¹) (conjSubgroup z X) (conjSubgroup z Y) := by
  obtain ⟨⟨hQX, hXR, hQY, hYR, hXY, hXYQ, hcomm⟩, hYsl, hW⟩ := hsplit
  have hQz : conjSubgroup z Q = Q := hc.conj_Q_eq hz
  have hZz : conjSubgroup z Z = Z := hc.conj_Z_eq hz
  have hR : Rt M (LB M Q B) (z * t * z⁻¹) = conjSubgroup z (Rt M (LB M Q B) t) :=
    (conjSubgroup_Rt_eq hz t).symm
  have hV : Vt M (LB M Q B) B Z (z * t * z⁻¹) = conjSubgroup z (Vt M (LB M Q B) B Z t) :=
    (conjSubgroup_Vt_eq hz hZz t).symm
  have hWz : Wt Q (conjSubgroup z (Vt M (LB M Q B) B Z t)) =
      conjSubgroup z (Wt Q (Vt M (LB M Q B) B Z t)) := by
    unfold Wt
    rw [conjSubgroup_inf, conjSubgroup_centralizer, hQz]
  have hconj : ∀ {S : Subgroup G} {g : G}, g ∈ S → z * g * z⁻¹ ∈ conjSubgroup z S :=
    fun {S g} hg => by
      rw [mem_conjSubgroup, show z⁻¹ * (z * g * z⁻¹) * z = g by group]
      exact hg
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [← hQz]
    exact Subgroup.map_mono hQX
  · rw [hR]
    exact Subgroup.map_mono hXR
  · rw [← hQz]
    exact Subgroup.map_mono hQY
  · rw [hR]
    exact Subgroup.map_mono hYR
  · rw [hR, ← hXY, conjSubgroup_sup']
  · rw [← conjSubgroup_inf, hXYQ, hQz]
  · intro a ha y hy
    have h := hcomm _ (mem_conjSubgroup.mp ha) _ (mem_conjSubgroup.mp hy)
    have e : ⁅a, y⁆ = z * ⁅z⁻¹ * a * z, z⁻¹ * y * z⁆ * z⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e, ← hQz]
    exact hconj h
  · exact hQz ▸ QuotSat.conj (fun X Y _ _ e h => IsSLModel.congr e h) hYsl z
  · intro a ha w hw
    rw [hV] at hw ⊢
    rw [hWz] at hw
    have h := hW _ (mem_conjSubgroup.mp ha) _ (mem_conjSubgroup.mp hw)
    have e : ⁅a, w⁆ = z * ⁅z⁻¹ * a * z, z⁻¹ * w * z⁆ * z⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact hconj h

theorem l56_data_conj (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) (h312b : Stroth312bStatement) {hc : Ctx M Q Z B}
    {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {s : G} (hs0 : s ∈ Z0) (hsQ : s ∉ Q)
    {X Y : Subgroup G} (hsplit : HS9.Split95 M Q Z B t X Y) {h : G} (hh : h ∈ M)
    (hZL : conjSubgroup h Z0 ≤ LB M Q B) (hY : conjSubgroup h Y = Y) :
    Sec9Hyp hc n (h * s * h⁻¹) ∧
      Vt M (LB M Q B) B Z (h * s * h⁻¹) = conjSubgroup h (Vt M (LB M Q B) B Z t) ∧
      HS9.Split95 M Q Z B (h * s * h⁻¹) (conjSubgroup h X) Y := by
  have hs5 := hs.toSec5
  have hP : Step94PointStatement := step94Point_holds h34
  obtain ⟨r, hr⟩ :=
    sec9AExists_of h34 h311a (sec9NComm_of_311b h34 h311bComm) G M Q Z B hc n t hs
  have hRs : Rt M (LB M Q B) s = Rt M (LB M Q B) t :=
    HS9.Rt_eq_of_mem_Z091 h34 h311a h311bComm h312b hs hr hZ0 hs0 hsQ
  have hVs : Vt M (LB M Q B) B Z s = Vt M (LB M Q B) B Z t :=
    Vt_eq_of_mem_Z0 h34 h311a h311bComm h312b hP hs hZ0 hs0 hsQ
  have hsplit_s : HS9.Split95 M Q Z B s X Y := by
    unfold HS9.Split95
    rw [hRs, hVs]
    exact hsplit
  have heZ : h * s * h⁻¹ ∈ conjSubgroup h Z0 := by
    rw [mem_conjSubgroup, show h⁻¹ * (h * s * h⁻¹) * h = s by group]
    exact hs0
  have heQ : h * s * h⁻¹ ∉ Q := by
    intro hq
    apply hsQ
    have h1 := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (M.inv_mem hh))
      (h * s * h⁻¹)).mp hq
    rwa [show h⁻¹ * (h * s * h⁻¹) * h⁻¹⁻¹ = s by group] at h1
  refine ⟨⟨⟨hs5.width, hs5.n_gt, hs5.noA2, hs5.gen, hZL heZ, heQ⟩,
    omegaPlusNat_conj_of_mem_Z0 h34 h311a h311bComm h312b hP hs hZ0 hs0 hsQ hh, hs.large⟩,
    ?_, ?_⟩
  · rw [← conjSubgroup_Vt_eq hh (hc.conj_Z_eq hh) s, hVs]
  · have h1 := l56_split95_conj hc hsplit_s hh
    rwa [hY] at h1

theorem l56_mem_conj_LB {X' Y : Subgroup G} (hcomm : ∀ a ∈ X', ∀ y ∈ Y, ⁅a, y⁆ ∈ Q) {c w : G}
    (hc : c ∈ X') (hw : w ∈ LB M Q B ⊓ Y) : w ∈ conjSubgroup c (LB M Q B) := by
  rw [mem_conjSubgroup]
  have h := hcomm c⁻¹ (X'.inv_mem hc) w⁻¹ (Y.inv_mem hw.2)
  have e : c⁻¹ * w * c = w * ⁅c⁻¹, w⁻¹⁆⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact (LB M Q B).mul_mem hw.1 (sec39_Q_le_LB (Q.inv_mem h))

theorem l56_core (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) {hc : Ctx M Q Z B} {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    {X Y : Subgroup G} (hsplit : HS9.Split95 M Q Z B t X Y) {x : G} (hxX : x ∈ X)
    (hxN : x ∉ hc.CN t) {h : G} (hh : h ∈ M) (hxh : x ∈ conjSubgroup h Z0) :
    ∃ c ∈ X, ∃ b ∈ conjSubgroup c B, ∃ a ∈ conjSubgroup h (Vt M (LB M Q B) B Z t), ⁅b, a⁆ ≠ 1 := by
  by_contra hcon
  push Not at hcon
  apply hxN
  have hNC : Sec9NCommStatement := sec9NComm_of_311b h34 h311bComm
  obtain ⟨r, hr⟩ := sec9AExists_of h34 h311a hNC G M Q Z B hc n t hs
  have h91b : Stroth91bStatement :=
    stroth91b_of_steps h34 h311a hNC (step91OrderQB_of h34) (step91OrderVQB_of h34)
      (step91Inter_of h34) (step91MixedComm_of h34)
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hVhQ : conjSubgroup h (Vt M (LB M Q B) B Z t) ≤ Q := fun a ha => by
    have h1 := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hh) _).mp
      (hVQ (mem_conjSubgroup.mp ha))
    rwa [show h * (h⁻¹ * a * h) * h⁻¹ = a by group] at h1
  have hUV : HS9.Uline Z B X ≤ Vt M (LB M Q B) B Z t :=
    (HS9.ulineX_data h34 h311a hc hs hsplit).2.2.2
  have hUC : HS9.Uline Z B X ≤
      Subgroup.centralizer (conjSubgroup h (Vt M (LB M Q B) B Z t) : Set G) := by
    refine sup_le ?_ (iSup₂_le fun c hcX => ?_)
    · intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact hc.Z_central hz (hVhQ ha)
    · intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have h1 := hcon c hcX b hb a ha
      rw [commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1.symm
  refine l56_mem_CN_of_comm_uline h34 h311a hc hs hsplit hxX fun v hv => ?_
  have hvW : h⁻¹ * v * h ∈ Wt Q (Vt M (LB M Q B) B Z t) := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h1 := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (M.inv_mem hh)) v).mp
        (hVQ (hUV hv))
      rwa [inv_inv] at h1
    · rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have hah : h * a * h⁻¹ ∈ conjSubgroup h (Vt M (LB M Q B) B Z t) := by
        rw [mem_conjSubgroup, show h⁻¹ * (h * a * h⁻¹) * h = a by group]
        exact ha
      have h1 := Subgroup.mem_centralizer_iff.mp (hUC hv) (h * a * h⁻¹) hah
      calc a * (h⁻¹ * v * h) = h⁻¹ * ((h * a * h⁻¹) * v) * h := by group
        _ = h⁻¹ * (v * (h * a * h⁻¹)) * h := by rw [h1]
        _ = h⁻¹ * v * h * a := by group
  have h1 := HS9.comm_Wt_le_Z91 h34 h91b hs hr hZ0 (mem_conjSubgroup.mp hxh) _ hvW
  have e : ⁅x, v⁆ = h * ⁅h⁻¹ * x * h, h⁻¹ * v * h⁆ * h⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  have h2 := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hh) _).mp h1
  exact h2

theorem l56_data (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) (h311bCard : Stroth311bCardStatement)
    (h312b : Stroth312bStatement) {hc : Ctx M Q Z B} {n : ℕ} {t : G} (hs : Sec9Hyp hc n t)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {s : G} (hs0 : s ∈ Z0)
    {x : G} (hxL : x ∈ LB M Q B) (hxN : x ∉ hc.CN t) (hconj : ConjMod M Q s x)
    {Y : Subgroup G} (hdp : IsDirectProdQuot (Rt M (LB M Q B) t) (Sec9R0 hc t x) Y Q)
    (hYsl : QuotSat Y Q (IsSLModel 2 (Nat.card Z))) {u : G} (hu : u ∈ LB M Q B ⊓ Y) :
    ∃ c ∈ M, ∃ d ∈ M,
      (∀ w ∈ LB M Q B ⊓ Y, w ∈ conjSubgroup c (LB M Q B) ∧ w ∈ conjSubgroup d (LB M Q B)) ∧
      ∃ b ∈ conjSubgroup c B, ∃ a ∈ Q, ⁅u, a⁆ ∈ conjSubgroup d B ⊔ Z ∧ ⁅b, a⁆ ≠ 1 ∧
        Rt M (LB M Q B) u ≠ LB M Q B ∧
        Nat.card Z ^ 3 < Nat.card ↥(Vt M (LB M Q B) B Z u) := by
  classical
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  have h92 : Stroth92Statement := stroth92_of_split h34 h311a h311bCard h311bComm
    (step92Split_of h34 h311a h311bComm h311bCard)
  have hB : Step94ConjVStatement := step94ConjV_of h34 h311a h311bComm
  have hsplit := split95_of_step94 h92 hB hc hs hZ0 hs0 hxL hxN hconj hdp hYsl
  have hR0 : Step94ZInR0Statement := step94ZInR0_of (step94CYW_holds h34 h311a h311bComm) h92 hB
  have hYC : Step94YConjStatement :=
    step94YConj_of h34 h311a h311bComm h311bCard h312b h92 hB (step94Point_holds h34) hR0
  obtain ⟨h, hh, hZL, hxh, -⟩ := step94ZExists_holds h34 h311a h311bComm h312b G M Q Z B hc n t
    hs Z0 hZ0 s hs0 x hxL hxN hconj
  have hY : conjSubgroup h Y = Y :=
    hYC G M Q Z B hc n t hs Z0 hZ0 s hs0 x hxL hxN hconj Y hdp hYsl h hh hZL
  have hsQ : s ∉ Q := not_mem_Q_of_conjMod hc ht hxN hconj
  obtain ⟨hse, hVe, hsplite⟩ :=
    l56_data_conj h34 h311a h311bComm h312b hs hZ0 hs0 hsQ hsplit hh hZL hY
  have hxX : x ∈ Sec9R0 hc t x := by
    unfold Sec9R0
    refine Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem (1 : G)
      (Subgroup.mem_iSup_of_mem (Rt M (LB M Q B) t).one_mem ?_))
    rw [one_mul, inv_one, mul_one]
    exact Subgroup.mem_zpowers x
  obtain ⟨c, hcX, b, hb, a, ha, hba⟩ := l56_core h34 h311a h311bComm hs hZ0 hsplit hxX hxN hh hxh
  rw [← hVe] at ha
  have h4e := sec4_of h34 h311a G M Q Z B hc n (h * s * h⁻¹) hse _ Y hsplite
  have huRe : u ∈ Rt M (LB M Q B) (h * s * h⁻¹) := hsplite.1.2.2.2.1 hu.2
  have huaV : ⁅u, a⁆ ∈ Vt M (LB M Q B) B Z (h * s * h⁻¹) := by
    have h1 := (Subgroup.mem_normalizer_iff.mp
      (hc.Rt_normalizes_Vt hse.toSec5.mem huRe) a).mp ha
    rw [commutatorElement_def]
    exact (Vt M (LB M Q B) B Z (h * s * h⁻¹)).mul_mem h1 (Subgroup.inv_mem _ ha)
  have hua : ⁅u, a⁆ ∈ HS9.Uline Z B (conjSubgroup h (Sec9R0 hc t x)) :=
    HS9.mem_ulineX_of_fix h34 h311a hc hse hsplite h4e huaV fun y hy =>
      l56_comm_comm_mem_Z h34 h311a hc hse hsplite hu hy ha
  obtain ⟨hcard', -, hcover', hUVe⟩ := HS9.ulineX_data h34 h311a hc hse hsplite
  obtain ⟨d, hdX, hd⟩ := hcover' _ hua
  have hXM : Sec9R0 hc t x ≤ M := fun y hy => hc.Rt_le_M t (hdp.2.1 hy)
  have hXhM : ∀ y ∈ conjSubgroup h (Sec9R0 hc t x), y ∈ M := by
    intro y hy
    have h1 := M.mul_mem (M.mul_mem hh (hXM (mem_conjSubgroup.mp hy))) (M.inv_mem hh)
    rwa [show h * (h⁻¹ * y * h) * h⁻¹ = y by group] at h1
  have hcM : c ∈ M := hXM hcX
  have hdM : d ∈ M := hXhM d hdX
  have hcommXh := hsplite.1.2.2.2.2.2.2
  have hS : ∀ w ∈ LB M Q B ⊓ Y,
      w ∈ conjSubgroup c (LB M Q B) ∧ w ∈ conjSubgroup d (LB M Q B) := fun w hw =>
    ⟨l56_mem_conj_LB hdp.2.2.2.2.2.2 hcX hw, l56_mem_conj_LB hcommXh hdX hw⟩
  have hcommVe : ∀ y ∈ Vt M (LB M Q B) B Z (h * s * h⁻¹), ⁅y, a⁆ = 1 := by
    intro y hy
    have h1 := (Subgroup.mem_inf.mp (HS6.Vt_le_Wt h34 hc hse.toSec5 ha)).2
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_centralizer_iff.mp h1 y hy
  have hR : Rt M (LB M Q B) u ≠ LB M Q B := by
    intro hRu
    have hLc : conjSubgroup c (LB M Q B) ≤ LB M Q B := by
      have h1 := conjSubgroup_le_Rt hcM (hS u hu).1
      rwa [hRu] at h1
    have hLc' : conjSubgroup c (LB M Q B) = LB M Q B :=
      Subgroup.eq_of_le_of_card_ge hLc (by rw [card_conjSubgroup])
    have h35 := (stroth_3_5 h34 hc hs5.width hs5.n_gt hs5.noA2 hs5.gen).2.1
    have h35c := (stroth_3_5 h34 (hc.conj_of_mem hcM) hs5.width hs5.n_gt
      (hc.noA2_conj hs5.noA2 hcM) (hs5.gen.conj_of_mem hcM)).2.1
    rw [hc.LB_conj hcM, hLc', h35] at h35c
    have hbBZ : b ∈ ((B ⊔ Z : Subgroup G) : Set G) := by
      rw [h35c]
      exact Subgroup.mem_sup_left hb
    have hBZVe : B ⊔ Z ≤ Vt M (LB M Q B) B Z (h * s * h⁻¹) :=
      sup_le (hc.B_le_Vt hse.toSec5.mem) sec39_Z_le_Vt
    exact hba (hcommVe b (hBZVe hbBZ))
  have hcard : Nat.card Z ^ 3 < Nat.card ↥(Vt M (LB M Q B) B Z u) := by
    by_contra hle
    push Not at hle
    have hlV : HS9.Uline Z B (conjSubgroup h (Sec9R0 hc t x)) ≤ Vt M (LB M Q B) B Z u :=
      sup_le sec39_Z_le_Vt (iSup₂_le fun d' hd' =>
        sec39_conjB_le_Vt (hXhM d' hd') (l56_mem_conj_LB hcommXh hd' hu))
    have heq : HS9.Uline Z B (conjSubgroup h (Sec9R0 hc t x)) = Vt M (LB M Q B) B Z u :=
      Subgroup.eq_of_le_of_card_ge hlV (by rw [hcard']; exact hle)
    have hbVu : b ∈ Vt M (LB M Q B) B Z u := sec39_conjB_le_Vt hcM (hS u hu).1 hb
    rw [← heq] at hbVu
    exact hba (hcommVe b (hUVe hbVu))
  exact ⟨c, hcM, d, hdM, hS, b, hb, a, hc.Vt_le_Q _ ha, hd, hba, hR, hcard⟩

theorem l56_comm_mem_Q_of_mem_sup (hc : Ctx M Q Z B) {c d w : G} (hcM : c ∈ M) (hdM : d ∈ M)
    (hwc : w ∈ conjSubgroup c (LB M Q B)) (hwd : w ∈ conjSubgroup d (LB M Q B)) :
    ∀ y ∈ conjSubgroup c (LB M Q B) ⊔ conjSubgroup d (LB M Q B), ⁅y, w⁆ ∈ Q := by
  have hQn : ∀ g ∈ M, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q := fun g hg q hq =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hg) q).mp hq
  let C : Subgroup G :=
    { carrier := {y | y ∈ M ∧ ⁅y, w⁆ ∈ Q}
      one_mem' := ⟨M.one_mem, by rw [commutatorElement_one_left]; exact Q.one_mem⟩
      mul_mem' := by
        rintro y₁ y₂ ⟨h₁M, h₁Q⟩ ⟨h₂M, h₂Q⟩
        refine ⟨M.mul_mem h₁M h₂M, ?_⟩
        have e : ⁅y₁ * y₂, w⁆ = y₁ * ⁅y₂, w⁆ * y₁⁻¹ * ⁅y₁, w⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact Q.mul_mem (hQn y₁ h₁M _ h₂Q) h₁Q
      inv_mem' := by
        rintro y ⟨hM, hQ⟩
        refine ⟨M.inv_mem hM, ?_⟩
        have e : ⁅y⁻¹, w⁆ = y⁻¹ * ⁅y, w⁆⁻¹ * y⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact hQn y⁻¹ (M.inv_mem hM) _ (Q.inv_mem hQ) }
  have hle : ∀ {g : G}, g ∈ M → w ∈ conjSubgroup g (LB M Q B) → conjSubgroup g (LB M Q B) ≤ C := by
    intro g hg hwg y hy
    have hyM : y ∈ M := by
      have h1 := M.mul_mem (M.mul_mem hg (hc.LB_le_M (mem_conjSubgroup.mp hy))) (M.inv_mem hg)
      rwa [show g * (g⁻¹ * y * g) * g⁻¹ = y by group] at h1
    refine ⟨hyM, ?_⟩
    have h1 : ⁅g⁻¹ * y * g, g⁻¹ * w * g⁆ ∈ Q := hc.commutator_LB_le_Q
      (Subgroup.commutator_mem_commutator (mem_conjSubgroup.mp hy) (mem_conjSubgroup.mp hwg))
    have e : ⁅y, w⁆ = g * ⁅g⁻¹ * y * g, g⁻¹ * w * g⁆ * g⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact hQn g hg _ h1
  intro y hy
  exact (sup_le (hle hcM hwc) (hle hdM hwd) hy).2

end S94F

theorem step94NotQB_holds (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) (h311bCard : Stroth311bCardStatement)
    (h312b : Stroth312bStatement) : Step94NotQBStatement := by
  intro G _ _ M Q Z B hc n t hs Z0 hZ0 _ s hs0 x hxL hxN hconj Y hdp hYsl _ u hu huQ hV
  obtain ⟨c, hcM, d, hdM, hS, b, hb, a, ha, hua, hba, hR, hcard⟩ :=
    S94F.l56_data h34 h311a h311bComm h311bCard h312b hs hZ0 hs0 hxL hxN hconj hdp hYsl hu
  have hs5 := hs.toSec5
  have hsu : Sec5Hyp hc n u := ⟨hs5.width, hs5.n_gt, hs5.noA2, hs5.gen, hu.1, huQ⟩
  have hsl : SLNat hc u :=
    stroth310SLBranch_of_transv (stroth310SLTransv_of_34 h34) G M Q Z B hc n u hsu hR hV
  have hbV : b ∈ Vt M (LB M Q B) B Z u := sec39_conjB_le_Vt hcM (hS u hu).1 hb
  have huaV : ⁅u, a⁆ ∈ Vt M (LB M Q B) B Z u :=
    (sup_le (sec39_conjB_le_Vt hdM (hS u hu).2) sec39_Z_le_Vt) hua
  exact S94F.l56u_false_of_SLNat h34 hsu hsl hcard hbV ha huaV hba

theorem step94Gen_holds (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) (h311bCard : Stroth311bCardStatement)
    (h312b : Stroth312bStatement) (hX : Classify.TheoremXStatement) : Step94GenStatement := by
  intro G _ _ M Q Z B hc n t hs Z0 hZ0 hsc s hs0 x hxL hxN hconj Y hdp hYsl hn5 u hu huQ
  obtain ⟨c, hcM, d, hdM, hS, b, hb, a, ha, hua, hba, hR, -⟩ :=
    S94F.l56_data h34 h311a h311bComm h311bCard h312b hs hZ0 hs0 hxL hxN hconj hdp hYsl hu
  have hs5 := hs.toSec5
  have hsu : Sec5Hyp hc n u := ⟨hs5.width, hs5.n_gt, hs5.noA2, hs5.gen, hu.1, huQ⟩
  have hnot := step94NotQB_holds h34 h311a h311bComm h311bCard h312b G M Q Z B hc n t hs Z0 hZ0
    hsc s hs0 x hxL hxN hconj Y hdp hYsl hn5 u hu huQ
  refine ⟨c, hcM, d, hdM, ?_, ?_, ?_⟩
  · rw [hc.LB_conj hcM, hc.LB_conj hdM]
    exact sup_le (conjSubgroup_le_Rt hcM (hS u hu).1) (conjSubgroup_le_Rt hdM (hS u hu).2)
  · rw [hc.LB_conj hcM, hc.LB_conj hdM]
    exact S94F.l56u_gen_of_opp h34 hX hsu hR hnot hcM hdM (hS u hu).1 (hS u hu).2 hb ha hua hba
  · rw [hc.LB_conj hcM, hc.LB_conj hdM]
    intro y hy w hw
    exact S94F.l56_comm_mem_Q_of_mem_sup hc hcM hdM (hS w hw).1 (hS w hw).2 y hy

end CFSG.RankThree.GF2n.Stroth80
