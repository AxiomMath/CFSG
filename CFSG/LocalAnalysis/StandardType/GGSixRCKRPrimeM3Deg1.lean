module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeDefs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelPSL
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionSL
public import CFSG.ClassicalInvolution.ModelFacts.WeylTransitive
public import CFSG.Assembly.OrderReductions.LinearOrders

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag)

private theorem rckM3d1_blockDegree_eq_one {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {A : Subalgebra F (Matrix ι ι F)} {e : Matrix ι ι F} (he : IsPrimIdemIn A e)
    (hdeg : blockDegree A e < 2) : blockDegree A e = 1 := by
  have hpos : 1 ≤ blockDegree A e := by
    let M : Submodule F (Matrix ι ι F) :=
      (Subalgebra.toSubmodule A).map (LinearMap.mulRight F e)
    have heM : e ∈ M :=
      ⟨1, by simpa using A.one_mem, by rw [LinearMap.mulRight_apply, one_mul]⟩
    have hne : (⟨e, heM⟩ : M) ≠ 0 := by
      intro h
      exact he.2.2.1 (by simpa using congrArg Subtype.val h)
    haveI : Nontrivial M := ⟨⟨⟨e, heM⟩, 0, hne⟩⟩
    have hpos' : 0 < Module.finrank F M := Module.finrank_pos_iff.mpr inferInstance
    change 1 ≤ Module.finrank F M
    omega
  omega

private theorem rckM3d1_rootGroup_conj {m : ℕ} {F : Type} [Field F]
    {β β₀ : Fin (SpecialLinear.rootDatum m F).rank → ℤ}
    (hβ : β ∈ (SpecialLinear.rootDatum m F).roots)
    (hβ₀ : β₀ ∈ (SpecialLinear.rootDatum m F).roots) :
    ∃ g : Matrix.SpecialLinearGroup (Fin (m + 1)) F,
      ((SpecialLinear.rootDatum m F).rootGroup β₀).map (MulAut.conj g).toMonoidHom =
        (SpecialLinear.rootDatum m F).rootGroup β := by
  obtain ⟨w, hw⟩ := CFSG.StandardType.exists_weylAction_eq_of_simpleConj
    (D := SpecialLinear.rootDatum m F) rfl
    (fun i j => CFSG.StandardType.GGRootSL.ggSimpleConj (m := m) (F := F) i j) hβ hβ₀
  obtain ⟨g, hg⟩ := CFSG.ClassicalInvolution.ModelFacts.exists_map_conj_rootGroup
    (D := SpecialLinear.rootDatum m F) (n := SpecialLinear.weylRep m F)
    (H := SpecialLinear.torus m F)
    (CFSG.LieType.Universal.SpecialLinear.isCTGroupDatum m F) w
  exact ⟨g, by rw [hg β₀ hβ₀, hw]⟩

private theorem rckM3d1_vecMulVec_mul_self {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (v φ : ι → F) (hdot : φ ⬝ᵥ v = 0) :
    Matrix.vecMulVec v φ * Matrix.vecMulVec v φ = 0 := by
  rw [Matrix.vecMulVec_mul]
  have hφ : Matrix.vecMul φ (Matrix.vecMulVec v φ) = (φ ⬝ᵥ v) • φ := by
    ext j
    simp [Matrix.vecMul_apply, Matrix.vecMulVec_apply, Matrix.col_apply, dotProduct,
      Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]
  rw [hφ, hdot, zero_smul]
  ext i j
  simp [Matrix.vecMulVec]

private theorem rckM3d1_transv_mul {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (v φ : ι → F) (hdot : φ ⬝ᵥ v = 0) (c d : F) :
    (1 + c • Matrix.vecMulVec v φ) * (1 + d • Matrix.vecMulVec v φ) =
      1 + (c + d) • Matrix.vecMulVec v φ := by
  have hsq := rckM3d1_vecMulVec_mul_self v φ hdot
  calc (1 + c • Matrix.vecMulVec v φ) * (1 + d • Matrix.vecMulVec v φ)
      = 1 * (1 + d • Matrix.vecMulVec v φ) +
          (c • Matrix.vecMulVec v φ) * (1 + d • Matrix.vecMulVec v φ) := by
        rw [Matrix.add_mul]
    _ = (1 * 1 + 1 * (d • Matrix.vecMulVec v φ)) +
          ((c • Matrix.vecMulVec v φ) * 1 +
            (c • Matrix.vecMulVec v φ) * (d • Matrix.vecMulVec v φ)) := by
        rw [Matrix.mul_add, Matrix.mul_add]
    _ = (1 + d • Matrix.vecMulVec v φ) +
          (c • Matrix.vecMulVec v φ +
            (c * d) • (Matrix.vecMulVec v φ * Matrix.vecMulVec v φ)) := by
        simp only [Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
          mul_comm d c]
    _ = (1 + d • Matrix.vecMulVec v φ) + (c • Matrix.vecMulVec v φ + 0) := by
        rw [hsq, smul_zero]
    _ = 1 + d • Matrix.vecMulVec v φ + c • Matrix.vecMulVec v φ := by rw [add_zero]
    _ = 1 + (c + d) • Matrix.vecMulVec v φ := by
        rw [add_assoc, ← add_smul, add_comm d c]

private theorem rckM3d1_mem_matTransvGroup {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {v φ : ι → F} (hdot : φ ⬝ᵥ v = 0) {g : GL ι F}
    (hg : g ∈ matTransvGroup v φ) :
    ∃ c : F, (g : Matrix ι ι F) = 1 + c • Matrix.vecMulVec v φ := by
  let S : Subgroup (GL ι F) :=
    { carrier := {g : GL ι F | ∃ c : F, (g : Matrix ι ι F) = 1 + c • Matrix.vecMulVec v φ}
      one_mem' := by
        refine ⟨0, ?_⟩
        simp
      mul_mem' := by
        rintro g h ⟨c, hc⟩ ⟨d, hd⟩
        refine ⟨c + d, ?_⟩
        rw [Units.val_mul, hc, hd]
        exact rckM3d1_transv_mul v φ hdot c d
      inv_mem' := by
        rintro g ⟨c, hc⟩
        refine ⟨-c, ?_⟩
        have h : (g : Matrix ι ι F) * (1 + (-c) • Matrix.vecMulVec v φ) = 1 := by
          rw [hc, rckM3d1_transv_mul v φ hdot c (-c), add_neg_cancel, zero_smul, add_zero]
        have hg_left : ((g⁻¹ : GL ι F) : Matrix ι ι F) * (g : Matrix ι ι F) = 1 := by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
        calc ((g⁻¹ : GL ι F) : Matrix ι ι F)
            = ((g⁻¹ : GL ι F) : Matrix ι ι F) * 1 := by rw [mul_one]
          _ = ((g⁻¹ : GL ι F) : Matrix ι ι F) *
                ((g : Matrix ι ι F) * (1 + (-c) • Matrix.vecMulVec v φ)) := by rw [h]
          _ = (((g⁻¹ : GL ι F) : Matrix ι ι F) * (g : Matrix ι ι F)) *
                (1 + (-c) • Matrix.vecMulVec v φ) := by rw [mul_assoc]
          _ = 1 * (1 + (-c) • Matrix.vecMulVec v φ) := by rw [hg_left]
          _ = 1 + (-c) • Matrix.vecMulVec v φ := by rw [one_mul] }
  have hle : matTransvGroup v φ ≤ S := by
    rw [matTransvGroup, Subgroup.closure_le]
    intro g hg
    exact hg
  exact hle hg

private theorem rckM3d1_conj_vecMulVec {m : ℕ} {F : Type} [Field F]
    (u : Matrix.SpecialLinearGroup (Fin (m + 1)) F) (v φ : Fin (m + 1) → F) (c : F) :
    (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
        (1 + c • Matrix.vecMulVec v φ) *
        ((u⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      1 + c • Matrix.vecMulVec
        (Matrix.mulVec (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) v)
        (Matrix.vecMul φ ((u⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) F)) := by
  have hwu : (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
      ((u⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hwu, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]

private theorem rckM3d1_odd_center_PSL {n q : ℕ} (hn : 1 ≤ n) (hq : q ≠ 0) :
    Odd (Nat.card (Subgroup.center
      (Matrix.SpecialLinearGroup (Fin n) (GaloisField 2 q)))) := by
  have hodd : Odd (2 ^ q - 1) := by
    have hpos : 0 < 2 ^ (q - 1) := pow_pos (by norm_num) _
    have hsplit : 2 ^ q = 2 * 2 ^ (q - 1) := by
      have hq' : q = (q - 1) + 1 := by omega
      conv_lhs => rw [hq']
      rw [pow_succ, mul_comm]
    have hnot : ¬ 2 ∣ 2 ^ q - 1 := by
      rw [hsplit]
      exact Nat.two_not_dvd_two_mul_sub_one hpos
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact hnot
  rw [CFSG.OrderReductions.LinearOrders.card_specialLinear_center
    (GaloisField 2 q) n hn]
  rw [GaloisField.card (p := 2) q hq]
  exact hodd.of_dvd_nat (Nat.gcd_dvd_right _ _)

private theorem rckM3d1_range_smul {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {c : F} (hc : c ≠ 0) (M : Matrix ι ι F) :
    LinearMap.range (Matrix.toLin' (c • M)) = LinearMap.range (Matrix.toLin' M) := by
  have h : Matrix.toLin' (c • M) = c • Matrix.toLin' M := map_smul Matrix.toLin' c M
  rw [h, LinearMap.range_smul (Matrix.toLin' M) c hc]

private theorem rckM3d1_ker_smul {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {c : F} (hc : c ≠ 0) (M : Matrix ι ι F) :
    LinearMap.ker (Matrix.toLin' (c • M)) = LinearMap.ker (Matrix.toLin' M) := by
  have h : Matrix.toLin' (c • M) = c • Matrix.toLin' M := map_smul Matrix.toLin' c M
  rw [h, LinearMap.ker_smul (Matrix.toLin' M) c hc]

theorem rckM3_PSL_deg1
    (m g : ℕ) (hg : 1 ≤ g) (S : Set (GL (Fin (m + 1)) (GaloisField 2 g)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 g)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 g) (Units.val '' S)) e)
    {J' : Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 g))}
    (hJe : IsComponentOf J' ⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
      glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆)
    (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 g) (Units.val '' S)) e < 2) :
    ∃ (k : ℕ) (ι : (ggU .PSL (k + 1)
        (g * blockDegree (Algebra.adjoin (GaloisField 2 g) (Units.val '' S)) e)).K →*
        (ggU .PSL (m + 1) g).K),
      (∀ y, ι y ∈ Subgroup.center (ggU .PSL (m + 1) g).K →
        y ∈ Subgroup.center (ggU .PSL (k + 1)
          (g * blockDegree (Algebra.adjoin (GaloisField 2 g) (Units.val '' S)) e)).K) ∧
      ι.range = J' ∧
      ∀ β ∈ (ggU .PSL (k + 1)
          (g * blockDegree (Algebra.adjoin (GaloisField 2 g) (Units.val '' S)) e)).D.roots,
        ∃ W H : Submodule (GaloisField 2 g) (Fin (m + 1) → GaloisField 2 g), W ≤ H ∧
          ∀ x ∈ (ggU .PSL (k + 1)
              (g * blockDegree (Algebra.adjoin (GaloisField 2 g) (Units.val '' S)) e)).D.rootGroup β,
            x ≠ 1 →
            LinearMap.range (Matrix.toLin'
              (((Matrix.SpecialLinearGroup.toGL (ι x) : GL (Fin (m + 1)) (GaloisField 2 g)) :
                Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 g)) - 1)) = W ∧
            LinearMap.ker (Matrix.toLin'
              (((Matrix.SpecialLinearGroup.toGL (ι x) : GL (Fin (m + 1)) (GaloisField 2 g)) :
                Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 g)) - 1)) = H := by
  classical
  have hd1 : blockDegree (Algebra.adjoin (GaloisField 2 g) (Units.val '' S)) e = 1 :=
    rckM3d1_blockDegree_eq_one he hdeg
  rw [hd1, Nat.mul_one]
  obtain ⟨k, ι, β₀, v, φ, v', φ', hlong₀, hιker, hιrange, hφv, hφ'v', hφv', hφ'v, hT, hT',
    hk, hJ'eq, hβ₀root⟩ := exists_blockModel_PSL_rank m g S hS he hdeg hJe
  refine ⟨k, ι, hιker, hιrange, ?_⟩
  have hOddCenter : Odd (Nat.card (Subgroup.center
      (Matrix.SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 g)))) :=
    rckM3d1_odd_center_PSL (n := k + 1) (q := g) (by omega) (by omega)
  have hker_le : ι.ker ≤ Subgroup.center
      (Matrix.SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 g)) := by
    intro y hy
    exact hιker y (by rw [MonoidHom.mem_ker.mp hy]; exact Subgroup.one_mem _)
  have hOddKer : Odd (Nat.card (ι.ker)) :=
    hOddCenter.of_dvd_nat (Subgroup.card_dvd_of_le hker_le)
  intro β hβ
  have hβ' : β ∈ (SpecialLinear.rootDatum k (GaloisField 2 g)).roots := hβ
  have hβ₀' : β₀ ∈ (SpecialLinear.rootDatum k (GaloisField 2 g)).roots := hβ₀root
  obtain ⟨u, hu⟩ := rckM3d1_rootGroup_conj (m := k) (F := GaloisField 2 g) hβ' hβ₀'
  let um : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 g) := ι u
  let U : GL (Fin (m + 1)) (GaloisField 2 g) := Matrix.SpecialLinearGroup.toGL um
  let v₁ : Fin (m + 1) → GaloisField 2 g :=
    Matrix.mulVec (um : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 g)) v
  let φ₁ : Fin (m + 1) → GaloisField 2 g :=
    Matrix.vecMul φ (((um⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 g))) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 g))
  have hφ₁v₁ : φ₁ ⬝ᵥ v₁ = 0 := by
    dsimp only [φ₁, v₁]
    rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul,
      inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec, hφv]
  have hdisj : (SpecialLinear.rootDatum k (GaloisField 2 g)).rootGroup β ⊓ ι.ker = ⊥ := by
    apply Subgroup.inf_eq_bot_of_coprime
    obtain ⟨n, hn⟩ :=
      (CFSG.StandardType.GGRootSL.isPGroup_rootGroup (m := k) (F := GaloisField 2 g) hβ').exists_card_eq
    rw [hn]
    exact (hOddKer.coprime_two_right.pow_right n).symm
  refine ⟨LinearMap.range (Matrix.toLin' (Matrix.vecMulVec v₁ φ₁)),
    LinearMap.ker (Matrix.toLin' (Matrix.vecMulVec v₁ φ₁)), ?_, ?_⟩
  ·
    rintro y ⟨w, rfl⟩
    rw [LinearMap.mem_ker]
    change (Matrix.toLin' (Matrix.vecMulVec v₁ φ₁) ∘ₗ
      Matrix.toLin' (Matrix.vecMulVec v₁ φ₁)) w = 0
    rw [← Matrix.toLin'_mul, rckM3d1_vecMulVec_mul_self v₁ φ₁ hφ₁v₁, map_zero,
      LinearMap.zero_apply]
  · intro x hx hxne
    have hx' : x ∈ (SpecialLinear.rootDatum k (GaloisField 2 g)).rootGroup β := hx
    have hxmem : x ∈ ((SpecialLinear.rootDatum k (GaloisField 2 g)).rootGroup β₀).map
        (MulAut.conj u).toMonoidHom := by rw [hu]; exact hx'
    obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp hxmem
    have ha' : a ∈ (ggU .PSL (k + 1) g).D.rootGroup β₀ := ha
    have hTa : Matrix.SpecialLinearGroup.toGL (ι a) ∈ matTransvGroup v φ := by
      have h1 : ι a ∈ Subgroup.map ι ((ggU .PSL (k + 1) g).D.rootGroup β₀) :=
        Subgroup.mem_map_of_mem ι ha'
      have h2 : Matrix.SpecialLinearGroup.toGL (ι a) ∈
          Subgroup.map Matrix.SpecialLinearGroup.toGL
            (Subgroup.map ι ((ggU .PSL (k + 1) g).D.rootGroup β₀)) :=
        Subgroup.mem_map_of_mem Matrix.SpecialLinearGroup.toGL h1
      erw [hT] at h2
      exact h2
    obtain ⟨c, hc⟩ := rckM3d1_mem_matTransvGroup hφv hTa
    let am : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 g) := ι a
    let xm : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 g) := ι x
    have hc' : (am : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 g)) =
        1 + c • Matrix.vecMulVec v φ := by
      erw [← Matrix.SpecialLinearGroup.coe_GL_coe_matrix am]
      exact hc
    have hx_eq : x = u * a * u⁻¹ := by
      have h := hax
      change (MulAut.conj u) a = x at h
      rw [MulAut.conj_apply] at h
      exact h.symm
    have hM : ((Matrix.SpecialLinearGroup.toGL (ι x) : GL (Fin (m + 1)) (GaloisField 2 g)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 g)) - 1 =
        c • Matrix.vecMulVec v₁ φ₁ := by
      erw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix (ι x)]
      change (xm : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 g)) - 1 =
        c • Matrix.vecMulVec v₁ φ₁
      have hxmat : (xm : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 g)) =
          (um : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 g)) *
            (am : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 g)) *
            (((um⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 g))) :
              Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 g)) := by
        dsimp only [xm, um, am]
        erw [hx_eq, map_mul, map_mul, map_inv, Matrix.SpecialLinearGroup.coe_mul,
          Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv]
      rw [hxmat, hc', rckM3d1_conj_vecMulVec um v φ c, add_sub_cancel_left]
    have hcne : c ≠ 0 := by
      intro hc0
      apply hxne
      have hxker : x ∈ ι.ker := by
        rw [MonoidHom.mem_ker]
        apply Matrix.SpecialLinearGroup.toGL_injective
        apply Units.ext
        have hmat : ((Matrix.SpecialLinearGroup.toGL (ι x) : GL (Fin (m + 1)) (GaloisField 2 g)) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 g)) = 1 := by
          have h0 : ((Matrix.SpecialLinearGroup.toGL (ι x) : GL (Fin (m + 1)) (GaloisField 2 g)) :
              Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 g)) - 1 = 0 := by
            rw [hM, hc0, zero_smul]
          exact sub_eq_zero.mp h0
        erw [map_one, Units.val_one]
        exact hmat
      have hxbot : x ∈ (SpecialLinear.rootDatum k (GaloisField 2 g)).rootGroup β ⊓ ι.ker :=
        ⟨hx', hxker⟩
      rw [hdisj] at hxbot
      exact Subgroup.mem_bot.mp hxbot
    rw [hM]
    exact ⟨by rw [rckM3d1_range_smul hcne (Matrix.vecMulVec v₁ φ₁)],
      by rw [rckM3d1_ker_smul hcne (Matrix.vecMulVec v₁ φ₁)]⟩
end CFSG.StandardType.RCKRP
