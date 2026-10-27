module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpTwo
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpInner
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2NatB
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinL28
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Ctx
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallSp4
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallRep
import CFSG.LocalAnalysis.UniquenessCase.UC22K147SpUSp4
import CFSG.Blueprint.LieModelAPI
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bAut
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.Blueprint (LieModel)

open CFSG.QuasithinUnique.Setup.X7b CFSG.ComponentClassification.UnbalancedCatalog.SpChain in
private theorem w135c2_spFour_rank_lowUSp_zero {K : Type} [Field K] [CharP K 2]
    (b d : K) (hb : b ≠ 0) :
    (glMat ((lowUSp (0 : K) b 0 d : antiSp K) : GL (Fin 4) K) - 1).rank = 2 := by
  classical
  let N : Matrix (Fin 4) (Fin 4) K := !![0, 0, 0, 0; 0, 0, 0, 0; 1, 0, 0, 0; 0, 1, 0, 0]
  let W : Matrix (Fin 4) (Fin 4) K := !![b, 0, 0, 0; d, b, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]
  have hN : N.rank = 2 := by
    let σ : Equiv.Perm (Fin 4) := Equiv.swap (0 : Fin 4) 2 * Equiv.swap 1 3
    have hsub : N = (mE0213 K).submatrix σ σ := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [N, mE0213, Matrix.submatrix_apply, σ, Equiv.swap_apply_def]
    rw [hsub, Matrix.rank_submatrix, rank_mE0213]
  have hM : glMat ((lowUSp (0 : K) b 0 d : antiSp K) : GL (Fin 4) K) - 1 = N * W := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [N, W, glMat_lowUSp, lowU, Matrix.mul_apply, Fin.sum_univ_four, Matrix.sub_apply]
  have hle : (glMat ((lowUSp (0 : K) b 0 d : antiSp K) : GL (Fin 4) K) - 1).rank ≤ 2 := by
    rw [hM]
    calc (N * W).rank ≤ N.rank := Matrix.rank_mul_le_left _ _
      _ = 2 := hN
  have hdet : (!![b, 0; d, b] : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
    rw [Matrix.det_fin_two]
    simpa using mul_ne_zero hb hb
  have hge : 2 ≤ (glMat ((lowUSp (0 : K) b 0 d : antiSp K) : GL (Fin 4) K) - 1).rank := by
    have hsubeq : ((glMat ((lowUSp (0 : K) b 0 d : antiSp K) : GL (Fin 4) K) - 1).submatrix
        ![2, 3] ![0, 1]) = !![b, 0; d, b] := by
      rw [hM]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [N, W, Matrix.submatrix_apply]
    have hrank : ((glMat ((lowUSp (0 : K) b 0 d : antiSp K) : GL (Fin 4) K) - 1).submatrix
        ![2, 3] ![0, 1]).rank = 2 := by
      rw [hsubeq, Matrix.rank_of_det_ne_zero hdet]
      norm_num
    calc 2 = _ := hrank.symm
      _ ≤ _ := Matrix.rank_submatrix_le _ _ _
  omega

open CFSG.QuasithinUnique.Setup.X7b in
private theorem w135c2_spFour_lowUSp_zero_ne_one {K : Type} [Field K] [CharP K 2]
    {s : K} (hs : s ≠ 0) : lowUSp (0 : K) s 0 s ≠ 1 := by
  intro h
  have h1 := congrArg (fun g : antiSp K => glMat (g : GL (Fin 4) K) 2 0) h
  simp [glMat_lowUSp, lowU] at h1
  exact hs h1

open CFSG.QuasithinUnique.Setup.X7b in
private theorem w135c2_spFour_lowUSp_zero_mul_self {K : Type} [Field K] [CharP K 2] (s : K) :
    lowUSp (0 : K) s 0 s * lowUSp 0 s 0 s = 1 := by
  rw [lowUSp_mul]
  simp [CharTwo.add_self_eq_zero, lowUSp_zero]

open CFSG.QuasithinUnique.Setup.X7b CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5 in
private theorem w135c2_spFour_outer_even_form {K : Type} [Field K] [Fintype K] [CharP K 2]
    {m : ℕ} (c : antiSp K) (x : K) :
    ((MulAut.conj c * minorAut K ^ (2 * m) * (MulAut.conj c)⁻¹)
        (c * lowUSp 0 x 0 x * c⁻¹))⁻¹ * (c * lowUSp 0 x 0 x * c⁻¹) =
      c * lowUSp 0 (x ^ 2 ^ m + x) 0 (x ^ 2 ^ m + x) * c⁻¹ := by
  have h1 : (MulAut.conj c * minorAut K ^ (2 * m) * (MulAut.conj c)⁻¹)
      (c * lowUSp 0 x 0 x * c⁻¹) =
        c * lowUSp 0 (x ^ 2 ^ m) 0 (x ^ 2 ^ m) * c⁻¹ := by
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_inv_apply,
      show c⁻¹ * (c * lowUSp 0 x 0 x * c⁻¹) * c = lowUSp 0 x 0 x by group,
      minorAut_pow_two_mul_lowUSp, MulAut.conj_apply]
    simp
  have hinner : (lowUSp (0 : K) (x ^ 2 ^ m) 0 (x ^ 2 ^ m))⁻¹ * lowUSp 0 x 0 x =
      lowUSp 0 (x ^ 2 ^ m + x) 0 (x ^ 2 ^ m + x) := by
    rw [lowUSp_inv, lowUSp_mul]
    simp only [zero_mul, mul_zero, add_zero]
  rw [h1]
  rw [show (c * lowUSp (0 : K) (x ^ 2 ^ m) 0 (x ^ 2 ^ m) * c⁻¹)⁻¹ *
      (c * lowUSp 0 x 0 x * c⁻¹) =
      c * ((lowUSp (0 : K) (x ^ 2 ^ m) 0 (x ^ 2 ^ m))⁻¹ * lowUSp 0 x 0 x) * c⁻¹ by group,
    hinner]

open CFSG.QuasithinUnique.Setup.X7b CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5 in
private theorem w135c2_spFour_conj_lowUSp_props {K : Type} [Field K] [Fintype K] [CharP K 2]
    (c : antiSp K) {s : K} (hs : s ≠ 0) :
    (c * lowUSp (0 : K) s 0 s * c⁻¹ ≠ 1) ∧
      (c * lowUSp 0 s 0 s * c⁻¹ * (c * lowUSp 0 s 0 s * c⁻¹) = 1) ∧
      (rk0 (c * lowUSp 0 s 0 s * c⁻¹) = 2) ∧
      (rk1 (c * lowUSp 0 s 0 s * c⁻¹) = 2) := by
  have hminor : minorHom K (lowUSp (0 : K) s 0 s) = lowUSp 0 s 0 (s ^ 2) := by
    rw [minorHom_lowUSp]
    simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have h3 : lowUSp (0 : K) s 0 s = 1 := by
      calc lowUSp (0 : K) s 0 s = c⁻¹ * (c * lowUSp 0 s 0 s * c⁻¹) * c := by group
        _ = 1 := by rw [h]; group
    exact w135c2_spFour_lowUSp_zero_ne_one hs h3
  · rw [show c * lowUSp (0 : K) s 0 s * c⁻¹ * (c * lowUSp 0 s 0 s * c⁻¹) =
        c * (lowUSp 0 s 0 s * lowUSp 0 s 0 s) * c⁻¹ by group,
      w135c2_spFour_lowUSp_zero_mul_self s, mul_one, mul_inv_cancel]
  · rw [(rk_conj c (lowUSp (0 : K) s 0 s)).1]
    exact w135c2_spFour_rank_lowUSp_zero s s hs
  · rw [(rk_conj c (lowUSp (0 : K) s 0 s)).2, rk1, hminor]
    exact w135c2_spFour_rank_lowUSp_zero s (s ^ 2) hs

open CFSG.QuasithinUnique.Setup.X7b CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5 in
private theorem w135c2_spFour_outer_even_aux {K : Type} [Field K] [Fintype K] [CharP K 2]
    {m : ℕ} (hm : 1 ≤ m) (hK : Fintype.card K = 2 ^ (2 * m)) (c : antiSp K)
    {α : MulAut (antiSp K)}
    (hα : α = MulAut.conj c * minorAut K ^ (2 * m) * (MulAut.conj c)⁻¹) :
    ∃ l : antiSp K, (α l)⁻¹ * l ≠ 1 ∧ (α l)⁻¹ * l * ((α l)⁻¹ * l) = 1 ∧
      rk0 ((α l)⁻¹ * l) = 2 ∧ rk1 ((α l)⁻¹ * l) = 2 := by
  subst hα
  obtain ⟨x, hx⟩ := exists_pow_two_pow_ne_self hm hK
  have hs0 : x ^ 2 ^ m + x ≠ 0 := by
    intro h
    apply hx
    have := congrArg (· + x) h
    simpa [CharTwo.add_self_eq_zero, add_assoc] using this
  refine ⟨c * lowUSp 0 x 0 x * c⁻¹, ?_⟩
  rw [w135c2_spFour_outer_even_form c x]
  exact w135c2_spFour_conj_lowUSp_props c hs0

theorem exists_rank_two_involution_of_outer_even {K : Type} [Field K] [Fintype K] [CharP K 2]
    {m : ℕ} (hm : 1 ≤ m) (hK : Fintype.card K = 2 ^ (2 * m)) (c : antiSp K)
    {α : MulAut (antiSp K)}
    (hα : α = MulAut.conj c * minorAut K ^ (2 * m) * (MulAut.conj c)⁻¹) :
    ∃ l : antiSp K, (α l)⁻¹ * l ≠ 1 ∧ (α l)⁻¹ * l * ((α l)⁻¹ * l) = 1 ∧
      CFSG.QuasithinUnique.Setup.X7b.rk0 ((α l)⁻¹ * l) = 2 ∧
      CFSG.QuasithinUnique.Setup.X7b.rk1 ((α l)⁻¹ * l) = 2 :=
  w135c2_spFour_outer_even_aux hm hK c hα

open CFSG.LocalAnalysis.UniquenessCase.UC22 in
private theorem w135c2_spFour_finrank_range_mul_le_six {G : Type} [Group G] {V : Type}
    [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
    (a : Representation (ZMod 2) G V) (T Λ : G)
    (hdT : Module.finrank (ZMod 2) (LinearMap.range ((a T : V →ₗ[ZMod 2] V) - 1)) ≤ 3) :
    Module.finrank (ZMod 2) (LinearMap.range
      ((a (T * (Λ⁻¹ * T * Λ)) : V →ₗ[ZMod 2] V) - 1)) ≤ 6 := by
  have h4 := Submodule.finrank_mono (K147SpU.range_mul_le_sup a T (Λ⁻¹ * T * Λ))
  have h5 := Submodule.finrank_add_le_finrank_add_finrank
    (LinearMap.range ((a T : V →ₗ[ZMod 2] V) - 1))
    (LinearMap.range ((a (Λ⁻¹ * T * Λ) : V →ₗ[ZMod 2] V) - 1))
  have h6 := K147SpU.finrank_range_conj a T Λ
  omega

open CFSG.LocalAnalysis.UniquenessCase.UC22 in
private theorem w135c2_spFour_isSpn {X : Type} [Group X] {f : ℕ}
    (hX : LieModel X .PSp 2 2 f) : IsSpn X 4 f := by
  obtain ⟨F, instF, instFin, hF, ⟨e⟩⟩ := w135c2_nonempty_equiv_statedSp_of_lieModel_psp hX
  exact ⟨⟨2, rfl⟩, F, instF, instFin, hF, ⟨e.symm⟩⟩

open CFSG.QuasithinUnique.Setup.X7b CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.SL2Modules CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5 in
private theorem w135c2_spFour_repOf_irreducible {K : Type} [Field K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {W : Type} [CommGroup W]
    {L : Subgroup (MulAut W)} {π : antiSp K →* (V ≃ₗ[ZMod 2] V)}
    (θ : W ≃* Multiplicative V) (φ : ↥L ≃* antiSp K)
    (hπ : ∀ g v, π g v = binPsi θ ((φ.symm g : ↥L) : MulAut W) v)
    (hirr : IsIrrOn L ⊤ ⊥) : Fact (B42Sp4.repOf π).IsIrreducible := by
  obtain ⟨hlt, -, -, hJ⟩ := hirr
  have hirrV : ∀ J : Subgroup W, (∀ l ∈ L, ∀ v ∈ J, l v ∈ J) → J = ⊥ ∨ J = ⊤ :=
    fun J hJL => hJ J hJL bot_le le_top
  have hirrW : ∀ U : Submodule (ZMod 2) V, (∀ g, ∀ u ∈ U, π g u ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    refine B42L2.irr_map θ hirrV U ?_
    rintro _ ⟨l, hl, rfl⟩ u hu
    have h := hU (φ ⟨l, hl⟩) u hu
    rwa [hπ, MulEquiv.symm_apply_apply] at h
  have hntW : Nontrivial V := by
    obtain ⟨v, -, hv⟩ := SetLike.exists_of_lt hlt
    replace hv : v ≠ 1 := fun h => hv (h ▸ Subgroup.one_mem _)
    refine ⟨⟨Multiplicative.toAdd (θ v), 0, fun h => hv ?_⟩⟩
    have h1 : θ v = 1 := Multiplicative.toAdd.injective (by simpa using h)
    simpa using congrArg θ.symm h1
  exact ⟨(CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff (B42Sp4.repOf π)).mpr
    ⟨hntW, hirrW⟩⟩

open CFSG.QuasithinUnique.Setup.X7b CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.SL2Modules CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5 in
private theorem w135c2_spFour_repOf_nontrivial {K : Type} [Field K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {W : Type} [CommGroup W]
    {L : Subgroup (MulAut W)} {π : antiSp K →* (V ≃ₗ[ZMod 2] V)}
    (θ : W ≃* Multiplicative V) (φ : ↥L ≃* antiSp K)
    (hπ : ∀ g v, π g v = binPsi θ ((φ.symm g : ↥L) : MulAut W) v) :
    ∃ g, B42Sp4.repOf π g ≠ 1 := by
  refine ⟨lowUSp 0 1 0 1, fun h => K147SpU.lowUSp_zero_one_zero_one_ne_one (K := K) ?_⟩
  have h3 : ((φ.symm (lowUSp (0 : K) 1 0 1) : ↥L) : MulAut W) = 1 := by
    apply (binPsi θ).injective
    apply LinearEquiv.ext
    intro v
    rw [← hπ (lowUSp (0 : K) 1 0 1) v]
    simpa using LinearMap.congr_fun h v
  have h4 : φ.symm (lowUSp (0 : K) 1 0 1) = 1 := Subtype.ext h3
  rw [← φ.apply_symm_apply (lowUSp (0 : K) 1 0 1), h4, map_one]

private theorem w135c2_spFour_t_data {W : Type} [CommGroup W] [Finite W]
    {Y L : Subgroup (MulAut W)} {t : MulAut W} (hctx : Is135Context Y L) (htY : t ∈ Y)
    (ht2 : orderOf t = 2) :
    t ∈ Subgroup.normalizer (L : Set (MulAut W)) ∧ t ≠ 1 ∧ t * t = 1 := by
  have hLY : L ≤ Y := hctx.2.2.1
  refine ⟨?_, ?_, ?_⟩
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer hLY).mp (w135_normal_of_ctx hctx) htY
  · intro h1
    rw [h1, orderOf_one] at ht2
    omega
  · have h1 := pow_orderOf_eq_one t
    rwa [ht2, pow_two] at h1

private theorem w135c2_spFour_htc {W : Type} [CommGroup W] [Finite W]
    {Y L : Subgroup (MulAut W)} {t : MulAut W} (hctx : Is135Context Y L) (htY : t ∈ Y)
    (hZ : Subgroup.center ↥L = ⊥) (ht1 : t ≠ 1) : ∃ x ∈ L, t * x ≠ x * t := by
  by_contra hall
  push Not at hall
  have hZc : Zc L = ⊥ := by rw [Zc, hZ, Subgroup.map_bot]
  have htZ : t ∈ Zc L := w135c2_mem_Zc_of_comm hctx htY (fun l hl => by
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (hall l hl)]
    exact (Zc L).one_mem)
  rw [hZc] at htZ
  exact ht1 (Subgroup.mem_bot.mp htZ)

open CFSG.QuasithinUnique.Setup.X7b CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.SL2Modules CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5 in
private theorem w135c2_spFour_hdT {W : Type} [CommGroup W] [Finite W] {V : Type}
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {Y : Subgroup (MulAut W)} {t : MulAut W}
    (htY : t ∈ Y) (θ : W ≃* Multiplicative V)
    (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3) :
    Module.finrank (ZMod 2)
      (LinearMap.range ((subRep θ Y ⟨t, htY⟩ : V →ₗ[ZMod 2] V) - 1)) ≤ 3 := by
  let a := subRep θ Y
  let T : ↥Y := ⟨t, htY⟩
  have hT' : ∀ w : W, θ (t w) = Multiplicative.ofAdd ((a T : V →ₗ[ZMod 2] V)
      (Multiplicative.toAdd (θ w))) := fun w => by
    rw [subRep_toAdd, ofAdd_toAdd]
  have heq := finL28_two_pow_mQuot_eq_card_range θ t (a T) hT'
  have hcardR : Nat.card (LinearMap.range ((a T : V →ₗ[ZMod 2] V) - 1)) =
      2 ^ Module.finrank (ZMod 2) (LinearMap.range ((a T : V →ₗ[ZMod 2] V) - 1)) := by
    let R : Submodule (ZMod 2) V := LinearMap.range ((a T : V →ₗ[ZMod 2] V) - 1)
    refine letI : Module.Finite (ZMod 2) R := Module.Finite.of_finite; ?_
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  rw [hcardR] at heq
  have hmq := Nat.pow_right_injective (le_refl 2) heq
  rw [← hmq]
  exact hm

open CFSG.QuasithinUnique.Setup.X7b CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.SL2Modules CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5 in
private theorem w135c2_spFour_z_data {K : Type} [Field K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
    {W : Type} [CommGroup W] {Y L : Subgroup (MulAut W)} {t l : MulAut W}
    {π : antiSp K →* (V ≃ₗ[ZMod 2] V)} {θ : W ≃* Multiplicative V} {φ : ↥L ≃* antiSp K}
    (hπ : ∀ g v, π g v = binPsi θ ((φ.symm g : ↥L) : MulAut W) v)
    (htY : t ∈ Y) (hLY : L ≤ Y) (hlL : l ∈ L)
    (hyL : t * (l⁻¹ * t * l) ∈ L) (hy1 : t * (l⁻¹ * t * l) ≠ 1)
    (hy2 : t * (l⁻¹ * t * l) * (t * (l⁻¹ * t * l)) = 1)
    (hdT : Module.finrank (ZMod 2)
      (LinearMap.range ((subRep θ Y ⟨t, htY⟩ : V →ₗ[ZMod 2] V) - 1)) ≤ 3) :
    ∃ z : antiSp K, z * z = 1 ∧ z ≠ 1 ∧ dispRank (π z) ≤ 6 := by
  let a := subRep θ Y
  let T : ↥Y := ⟨t, htY⟩
  let Λ : ↥Y := ⟨l, hLY hlL⟩
  have hdY : Module.finrank (ZMod 2)
      (LinearMap.range ((a (T * (Λ⁻¹ * T * Λ)) : V →ₗ[ZMod 2] V) - 1)) ≤ 6 :=
    w135c2_spFour_finrank_range_mul_le_six a T Λ hdT
  let z : antiSp K := φ ⟨t * (l⁻¹ * t * l), hyL⟩
  have hz2 : z * z = 1 := by
    rw [← map_mul, show (⟨_, hyL⟩ : ↥L) * ⟨_, hyL⟩ = 1 from Subtype.ext hy2, map_one]
  have hz1 : z ≠ 1 := by
    intro h
    apply hy1
    have h1 : (⟨_, hyL⟩ : ↥L) = 1 := by
      rw [← φ.symm_apply_apply ⟨_, hyL⟩]
      show φ.symm z = 1
      rw [h, map_one]
    exact congrArg Subtype.val h1
  have hdisp : dispRank (π z) ≤ 6 := by
    have hπz : π z = binPsi θ (t * (l⁻¹ * t * l)) := by
      apply LinearEquiv.ext
      intro v
      rw [hπ z v, MulEquiv.symm_apply_apply]
    unfold dispRank
    rw [hπz]
    exact hdY
  exact ⟨z, hz2, hz1, hdisp⟩

open CFSG.QuasithinUnique.Setup.X7b CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.SL2Modules CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5 in
private theorem w135c2_spFour_dim_ne_four_of_three_le {K : Type} [Field K] [Fintype K]
    [CharP K 2] {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {f : ℕ}
    (hKf : Fintype.card K = 2 ^ f) (hf : 3 ≤ f) (π : antiSp K →* (V ≃ₗ[ZMod 2] V))
    [Fact (B42Sp4.repOf π).IsIrreducible] (hntπ : ∃ g, B42Sp4.repOf π g ≠ 1)
    {z : antiSp K} (hz2 : z * z = 1) (hz1 : z ≠ 1) (hdisp : dispRank (π z) ≤ 6)
    (hne4 : Module.finrank (EndRing (B42Sp4.repOf π)) V ≠ 4) : False := by
  have h3 := (B42Sp4.displacement_ge hKf (by omega) π hntπ hne4 hz2 hz1).1
  omega

open CFSG.QuasithinUnique.Setup.X7b CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.SL2Modules CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5 in
private theorem w135c2_spFour_inner_data {K : Type} [Field K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {W : Type} [CommGroup W]
    {Y L : Subgroup (MulAut W)} {t : MulAut W} {π : antiSp K →* (V ≃ₗ[ZMod 2] V)}
    {θ : W ≃* Multiplicative V} {φ : ↥L ≃* antiSp K}
    (hπ : ∀ g v, π g v = binPsi θ ((φ.symm g : ↥L) : MulAut W) v)
    (htY : t ∈ Y) (htL : t ∈ L) (htt : t * t = 1) (ht1 : t ≠ 1)
    (hdT : Module.finrank (ZMod 2)
      (LinearMap.range ((subRep θ Y ⟨t, htY⟩ : V →ₗ[ZMod 2] V) - 1)) ≤ 3) :
    ∃ zT : antiSp K, zT * zT = 1 ∧ zT ≠ 1 ∧ dispRank (π zT) ≤ 3 := by
  let a := subRep θ Y
  let T : ↥Y := ⟨t, htY⟩
  refine ⟨φ ⟨t, htL⟩, ?_, ?_, ?_⟩
  · rw [← map_mul, show (⟨t, htL⟩ : ↥L) * ⟨t, htL⟩ = 1 from Subtype.ext htt, map_one]
  · intro h
    apply ht1
    have h1 : (⟨t, htL⟩ : ↥L) = 1 := by
      rw [← φ.symm_apply_apply ⟨t, htL⟩]
      rw [show φ ⟨t, htL⟩ = 1 from h, map_one]
    exact congrArg Subtype.val h1
  · have hzTeq : (π (φ ⟨t, htL⟩) : V →ₗ[ZMod 2] V) = a T := by
      have h1 : π (φ ⟨t, htL⟩) = binPsi θ t := by
        apply LinearEquiv.ext
        intro v
        rw [hπ (φ ⟨t, htL⟩) v, MulEquiv.symm_apply_apply]
      rw [h1]
      rfl
    unfold dispRank
    rw [hzTeq]
    exact hdT

open CFSG.QuasithinUnique.Setup.X7b CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.SL2Modules CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5 in
private theorem w135c2_spFour_dim_ne_four_of_two_inner {K : Type} [Field K] [Fintype K]
    [CharP K 2] {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {f : ℕ}
    (hKf : Fintype.card K = 2 ^ f) (hf2 : f = 2) (π : antiSp K →* (V ≃ₗ[ZMod 2] V))
    [Fact (B42Sp4.repOf π).IsIrreducible] (hntπ : ∃ g, B42Sp4.repOf π g ≠ 1)
    {zT : antiSp K} (hzT2 : zT * zT = 1) (hzT1 : zT ≠ 1) (hdispT : dispRank (π zT) ≤ 3)
    (hne4 : Module.finrank (EndRing (B42Sp4.repOf π)) V ≠ 4) : False := by
  have h6 := (B42Sp4.displacement_ge hKf (by omega) π hntπ hne4 hzT2 hzT1).1
  omega

open CFSG.QuasithinUnique.Setup.X7b CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.SL2Modules CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5 in
private theorem w135c2_spFour_outer_alpha {W : Type} [CommGroup W] [Finite W]
    {Y L : Subgroup (MulAut W)} {K : Type} [Field K] [Fintype K] [CharP K 2]
    (φ : ↥L ≃* antiSp K) {t : MulAut W}
    (htN : t ∈ Subgroup.normalizer (L : Set (MulAut W))) (hctx : Is135Context Y L)
    (htY : t ∈ Y) (hZ : Subgroup.center ↥L = ⊥) (htL : t ∉ L) (htt : t * t = 1) :
    ∃ α : MulAut (antiSp K), α * α = 1 ∧
      α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (antiSp K) ∧
      ∀ x : ↥L, α (φ x) = φ (K148.AutAux.condHom L ⟨t, htN⟩ x) := by
  let b : ↥(Subgroup.normalizer (L : Set (MulAut W))) := ⟨t, htN⟩
  let α : MulAut (antiSp K) := MulAut.congr φ (K148.AutAux.condHom L b)
  have hαe : ∀ x : ↥L, α (φ x) = φ (K148.AutAux.condHom L b x) := fun x => by
    show φ (K148.AutAux.condHom L b (φ.symm (φ x))) = φ (K148.AutAux.condHom L b x)
    rw [MulEquiv.symm_apply_apply]
  have hαα : α * α = 1 := by
    show MulAut.congr φ (K148.AutAux.condHom L b) *
      MulAut.congr φ (K148.AutAux.condHom L b) = 1
    rw [← map_mul, ← map_mul, show b * b = 1 from Subtype.ext htt, map_one, map_one]
  have hαinn : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (antiSp K) := by
    rintro ⟨s, hs⟩
    apply htL
    refine w135c2_mem_of_conj_eq_conj hctx htY (φ.symm s).2 ?_ hZ
    intro x hx
    have h1 : MulAut.conj s (φ ⟨x, hx⟩) = φ (K148.AutAux.condHom L b ⟨x, hx⟩) := by
      rw [hs]
      exact hαe ⟨x, hx⟩
    rw [MulAut.conj_apply] at h1
    have h2 : φ (K148.AutAux.condHom L b ⟨x, hx⟩) =
        φ ((φ.symm s) * ⟨x, hx⟩ * (φ.symm s)⁻¹) := by
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      exact h1.symm
    have h3 := φ.injective h2
    have h4 := congrArg Subtype.val h3
    rw [K148.AutAux.condHom_apply] at h4
    simpa using h4
  exact ⟨α, hαα, hαinn, hαe⟩

open CFSG.QuasithinUnique.Setup.X7b CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.SL2Modules CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5 in
private theorem w135c2_spFour_outer_key {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    {K : Type} [Field K] [CharP K 2] (φ : ↥L ≃* antiSp K) (l₀ : antiSp K)
    {t : MulAut W} (htN : t ∈ Subgroup.normalizer (L : Set (MulAut W))) (htt : t * t = 1)
    {α : MulAut (antiSp K)}
    (hαe : ∀ x : ↥L, α (φ x) = φ (K148.AutAux.condHom L ⟨t, htN⟩ x)) :
    t * (((φ.symm l₀ : ↥L) : MulAut W)⁻¹ * t * ((φ.symm l₀ : ↥L) : MulAut W)) =
      ((φ.symm ((α l₀)⁻¹ * l₀) : ↥L) : MulAut W) := by
  let b : ↥(Subgroup.normalizer (L : Set (MulAut W))) := ⟨t, htN⟩
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have h1 : φ.symm (α l₀) = K148.AutAux.condHom L b (φ.symm l₀) := by
    rw [MulEquiv.symm_apply_eq, ← hαe, MulEquiv.apply_symm_apply]
  rw [map_mul φ.symm, map_inv φ.symm, h1, Subgroup.coe_mul, Subgroup.coe_inv,
    K148.AutAux.condHom_apply]
  show t * (((φ.symm l₀ : ↥L) : MulAut W)⁻¹ * t * (φ.symm l₀ : ↥L)) =
    (t * (φ.symm l₀ : MulAut W) * t⁻¹)⁻¹ * (φ.symm l₀ : MulAut W)
  simp only [mul_inv_rev, htinv]
  group

open CFSG.QuasithinUnique.Setup.X7b CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.SL2Modules CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5 in
private theorem w135c2_spFour_outer_z_data {W : Type} [CommGroup W] {Y L : Subgroup (MulAut W)}
    {K : Type} [Field K] [Fintype K] [CharP K 2] {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [Module.Finite (ZMod 2) V] {f : ℕ} (hKcard : Nat.card K = 2 ^ f)
    (hKf : Fintype.card K = 2 ^ f) (hf : 2 ≤ f) (hf2 : f = 2) {t : MulAut W}
    (htN : t ∈ Subgroup.normalizer (L : Set (MulAut W))) (htY : t ∈ Y) (htt : t * t = 1)
    (hLY : L ≤ Y)
    {π : antiSp K →* (V ≃ₗ[ZMod 2] V)} {θ : W ≃* Multiplicative V} (φ : ↥L ≃* antiSp K)
    (hπ : ∀ g v, π g v = binPsi θ ((φ.symm g : ↥L) : MulAut W) v)
    (hdT : Module.finrank (ZMod 2)
      (LinearMap.range ((subRep θ Y ⟨t, htY⟩ : V →ₗ[ZMod 2] V) - 1)) ≤ 3)
    {α : MulAut (antiSp K)} (hαα : α * α = 1)
    (hαinn : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (antiSp K))
    (hαe : ∀ x : ↥L, α (φ x) = φ (K148.AutAux.condHom L ⟨t, htN⟩ x)) :
    ∃ z' : antiSp K, z' * z' = 1 ∧ z' ≠ 1 ∧ rk0 z' = 2 ∧ rk1 z' = 2 ∧
      dispRank (π z') ≤ 6 := by
  let a := subRep θ Y
  let T : ↥Y := ⟨t, htY⟩
  obtain ⟨c, hc⟩ := outer_involution_conj hf hKcard α hαα hαinn
  obtain ⟨l₀, hl₀1, hl₀2, hl₀rk0, hl₀rk1⟩ :=
    exists_rank_two_involution_of_outer_even (m := 1) (α := α) (by norm_num)
      (by rw [show (2 : ℕ) * 1 = f by omega]; exact hKf) c (by rw [hc, hf2])
  let lam : ↥L := φ.symm l₀
  have key := w135c2_spFour_outer_key φ l₀ htN htt hαe
  have hy'L : t * (((lam : ↥L) : MulAut W)⁻¹ * t * (lam : ↥L)) ∈ L := by
    rw [key]; exact (φ.symm _).2
  let z' : antiSp K := φ ⟨t * (((lam : ↥L) : MulAut W)⁻¹ * t * (lam : ↥L)), hy'L⟩
  have hz'eq : z' = (α l₀)⁻¹ * l₀ := by
    have h : (⟨t * (((lam : ↥L) : MulAut W)⁻¹ * t * (lam : ↥L)), hy'L⟩ : ↥L) =
        φ.symm ((α l₀)⁻¹ * l₀) := Subtype.ext key
    show φ ⟨_, hy'L⟩ = _
    rw [h, MulEquiv.apply_symm_apply]
  have hz'2 : z' * z' = 1 := by rw [hz'eq]; exact hl₀2
  have hz'1 : z' ≠ 1 := by rw [hz'eq]; exact hl₀1
  let Λ' : ↥Y := ⟨(lam : ↥L), hLY (lam : ↥L).2⟩
  have hdisp' : dispRank (π z') ≤ 6 := by
    have hπz' : (π z' : V →ₗ[ZMod 2] V) = a (T * (Λ'⁻¹ * T * Λ')) := by
      have h1 : π z' = binPsi θ (t * (((lam : ↥L) : MulAut W)⁻¹ * t * (lam : ↥L))) := by
        apply LinearEquiv.ext
        intro v
        rw [hπ z' v, hz'eq, ← key]
      rw [h1]
      rfl
    unfold dispRank
    rw [hπz']
    exact w135c2_spFour_finrank_range_mul_le_six a T Λ' hdT
  exact ⟨z', hz'2, hz'1, by rw [hz'eq]; exact hl₀rk0, by rw [hz'eq]; exact hl₀rk1, hdisp'⟩

open CFSG.QuasithinUnique.Setup.X7b CFSG.QuasithinUnique.Setup.SL2Modules in
private theorem w135c2_spFour_dim_ne_four_of_two_outer {K : Type} [Field K] [Fintype K]
    [CharP K 2] {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {f : ℕ}
    (hKf : Fintype.card K = 2 ^ f) (hf2 : f = 2) (π : antiSp K →* (V ≃ₗ[ZMod 2] V))
    [Fact (B42Sp4.repOf π).IsIrreducible] (hntπ : ∃ g, B42Sp4.repOf π g ≠ 1)
    {z' : antiSp K} (hz'2 : z' * z' = 1) (hz'1 : z' ≠ 1) (hrk0 : rk0 z' = 2)
    (hrk1 : rk1 z' = 2) (hdisp' : dispRank (π z') ≤ 6)
    (hne4 : Module.finrank (EndRing (B42Sp4.repOf π)) V ≠ 4) : False := by
  have h8 := (B42Sp4.displacement_ge hKf (by omega) π hntπ hne4 hz'2 hz'1).2 hrk0 hrk1
  omega

open CFSG.QuasithinUnique.Setup.X7b CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.SL2Modules CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5 in
private theorem w135c2_spFour_natural_aux
    {W : Type} [CommGroup W] [Finite W]
    {Y L : Subgroup (MulAut W)} {t : MulAut W} (hW : ∀ w : W, w ^ 2 = 1)
    (hctx : Is135Context Y L) (htY : t ∈ Y) (ht2 : orderOf t = 2)
    (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3) {f : ℕ} (hf : 2 ≤ f)
    (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .PSp 2 2 f) :
    IsSpn ↥L 4 f ∧ NatSpn L ⊤ ⊥ 4 f := by
  classical
  have hZ : Subgroup.center ↥L = ⊥ := w135c2_center_eq_bot_of_lieModel_psp hctx hlie
  have hL' : LieModel ↥L .PSp 2 2 f := LieModel.of_quotient_center hZ hlie
  have hLY : L ≤ Y := hctx.2.2.1
  obtain ⟨-, K, instField, instFintype, instCharP, hKcard, ⟨φ⟩⟩ := K148.exists_antiSp_of_isSp4 hL'
  have hKf : Fintype.card K = 2 ^ f := by rw [← Nat.card_eq_fintype_card, hKcard]
  obtain ⟨V, _, _, _, ⟨θ⟩⟩ := Actor.exists_binModel_of_binary (V := W)
    (fun v => by rw [← pow_two]; exact hW v)
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  let π : antiSp K →* (V ≃ₗ[ZMod 2] V) :=
    (binPsi θ).toMonoidHom.comp (L.subtype.comp φ.symm.toMonoidHom)
  have hπ : ∀ g v, π g v = binPsi θ ((φ.symm g : ↥L) : MulAut W) v := fun _ _ => rfl
  have : Fact (B42Sp4.repOf π).IsIrreducible :=
    w135c2_spFour_repOf_irreducible θ φ hπ hctx.2.2.2.2.2
  have hntπ := w135c2_spFour_repOf_nontrivial θ φ hπ
  obtain ⟨htN, ht1, htt⟩ := w135c2_spFour_t_data hctx htY ht2
  have htc := w135c2_spFour_htc hctx htY hZ ht1
  obtain ⟨l, hlL, hyL, hy1, hy2⟩ := exists_mul_conj_involution' hL' htN htt htc
  have hdT := w135c2_spFour_hdT htY θ hm
  obtain ⟨z, hz2, hz1, hdisp⟩ := w135c2_spFour_z_data hπ htY hLY hlL hyL hy1 hy2 hdT
  have hdim : Module.finrank (EndRing (B42Sp4.repOf π)) V = 4 := by
    by_contra hne4
    by_cases hf3 : 3 ≤ f
    · exact w135c2_spFour_dim_ne_four_of_three_le hKf hf3 π hntπ hz2 hz1 hdisp hne4
    · have hf2 : f = 2 := by omega
      by_cases htL : t ∈ L
      · obtain ⟨zT, hzT2, hzT1, hdispT⟩ := w135c2_spFour_inner_data hπ htY htL htt ht1 hdT
        exact w135c2_spFour_dim_ne_four_of_two_inner hKf hf2 π hntπ hzT2 hzT1 hdispT hne4
      · obtain ⟨α, hαα, hαinn, hαe⟩ := w135c2_spFour_outer_alpha φ htN hctx htY hZ htL htt
        obtain ⟨z', hz'2, hz'1, hz'0, hz'1', hdisp'⟩ :=
          w135c2_spFour_outer_z_data hKcard hKf hf hf2 htN htY htt hLY φ hπ hdT hαα hαinn hαe
        exact w135c2_spFour_dim_ne_four_of_two_outer hKf hf2 π hntπ hz'2 hz'1 hz'0 hz'1'
          hdisp' hne4
  obtain ⟨i, φ', hφ'⟩ := B42Sp4.exists_natural_of_four hKf (by omega) π hntπ hdim
  have hNat : NatSpn L ⊤ ⊥ 4 f := by
    refine natSpn_of_mulVec hKcard θ (φ.trans (minorAut K ^ i)) φ' fun l w => ?_
    have h := hφ' (φ l) w
    rwa [hπ, MulEquiv.symm_apply_apply] at h
  exact ⟨w135c2_spFour_isSpn hL', hNat⟩

theorem w135c2_sp_four_natural
    {W : Type} [CommGroup W] [Finite W] {Y L : Subgroup (MulAut W)}
    {t : MulAut W} (hW : ∀ w : W, w ^ 2 = 1) (hctx : Is135Context Y L) (htY : t ∈ Y)
    (ht2 : orderOf t = 2) (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3) {f : ℕ}
    (hf : 2 ≤ f) (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .PSp 2 2 f) :
    IsSpn ↥L 4 f ∧ NatSpn L ⊤ ⊥ 4 f :=
  w135c2_spFour_natural_aux hW hctx htY ht2 hm hf hlie

theorem w135c2_sp_four
    {W : Type} [CommGroup W] [Finite W] {Y L : Subgroup (MulAut W)}
    {t : MulAut W} (hW : ∀ w : W, w ^ 2 = 1) (hctx : Is135Context Y L) (htY : t ∈ Y)
    (ht2 : orderOf t = 2) (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3) {f : ℕ}
    (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .PSp 2 2 f) : W4Lem13_5Concl W Y L t := by
  have hZ : Subgroup.center ↥L = ⊥ := w135c2_center_eq_bot_of_lieModel_psp hctx hlie
  have hL' : LieModel ↥L .PSp 2 2 f := CFSG.Blueprint.LieModel.of_quotient_center hZ hlie
  have hf : 2 ≤ f := (CFSG.LocalAnalysis.UniquenessCase.UC22.K148.exists_antiSp_of_isSp4 hL').1
  obtain ⟨hS, hNat⟩ := w135c2_sp_four_natural hW hctx htY ht2 hm hf hlie
  exact w135c2_natural hctx htY ht2 hW
    (Or.inl ⟨4, f, Or.inr (Or.inl ⟨hS, hNat⟩)⟩)

end CFSG.LocalAnalysis.WeakClosure81
