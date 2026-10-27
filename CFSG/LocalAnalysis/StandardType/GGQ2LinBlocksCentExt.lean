module

public import CFSG.LocalAnalysis.StandardType.GGQ2LinBlocksDefs
import CFSG.LocalAnalysis.StandardType.GGQ2LinBlocksBasic
import CFSG.LocalAnalysis.StandardType.GGQ2LinTorusAutBasic
import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksCentExt

public section

namespace CFSG.StandardType.GGQ2Frame.LinBlocks

open CFSG CFSG.StandardType CFSG.StandardType.SpJoin Matrix
open CFSG.Open (StatedSp)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open scoped commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} {t : ℕ} {ε : Fin 2}

noncomputable section

private def linExtHom (t : ℕ) (ε : Fin 2) : ↥(StatedSp t K) →* GL (LinIdx t ε) K :=
  (planeExt t ε).comp (StatedSp t K).subtype

omit [Finite K] [CharP K 2] in
private theorem linExtHom_tau (u : PlaneRaw.V t) :
    linExtHom (K := K) t ε (SpBlocks.tau ζ t u) = tau ζ t ε u :=
  (tau_eq_planeExt ζ t ε u).symm

omit [Finite K] [CharP K 2] in
private theorem planeExt_apply_mat' (A : GL (Fin t ⊕ Fin t) K) :
    ((planeExt t ε A : GL (LinIdx t ε) K) : Matrix (LinIdx t ε) (LinIdx t ε) K) =
      Matrix.fromBlocks (A : Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K) 0 0 1 :=
  rfl

omit [Finite K] [CharP K 2] in
private theorem tau_apply_mat' (u : PlaneRaw.V t) :
    ((tau ζ t ε u : GL (LinIdx t ε) K) : Matrix (LinIdx t ε) (LinIdx t ε) K) =
      Matrix.fromBlocks
        (WitSpNs.planeMat fun j =>
          ((ζ (Multiplicative.ofAdd (u j)) : SpecialLinearGroup (Fin 2) K) :
            Matrix (Fin 2) (Fin 2) K)) 0 0 1 := by
  rw [tau_eq_planeExt, planeExt_apply_mat', SpBlocks.coe_tau]

omit [Finite K] [CharP K 2] in
private theorem planeIdem_apply_mat' (S : Finset (Fin t)) :
    (planeIdem t ε S false : Matrix (LinIdx t ε) (LinIdx t ε) K) =
      Matrix.fromBlocks (SpBlocks.planeIdem t S) 0 0 0 := by
  ext x y
  rcases x with (i | i) | k <;> rcases y with (j | j) | l <;>
    simp [planeIdem, SpBlocks.planeIdem, Matrix.fromBlocks, Matrix.diagonal_apply]

omit [Finite K] [CharP K 2] in
private theorem one_sub_planeIdem_apply_mat' (S : Finset (Fin t)) :
    (1 - planeIdem t ε S false : Matrix (LinIdx t ε) (LinIdx t ε) K) =
      Matrix.fromBlocks (1 - SpBlocks.planeIdem t S) 0 0 1 := by
  ext x y
  rcases x with (i | i) | k <;> rcases y with (j | j) | l <;>
    simp [planeIdem, SpBlocks.planeIdem, Matrix.fromBlocks, Matrix.diagonal_apply,
      Matrix.one_apply]

omit [Finite K] [CharP K 2] in
private theorem tau_injective' (hζ : Function.Injective ζ) :
    Function.Injective (tau ζ t ε) := by
  intro u v h
  apply SpBlocks.tau_injective hζ t
  apply Subtype.ext
  exact planeExt_injective (K := K) t ε (by simpa only [tau_eq_planeExt] using h)

omit [Finite K] [CharP K 2] in
private theorem planeExt_mem_levi' {S : Finset (Fin t)} {g : ↥(StatedSp t K)}
    (hg : g ∈ SpBlocks.levi t S) :
    planeExt t ε ((g : ↥(StatedSp t K)) : GL (Fin t ⊕ Fin t) K) ∈
      levi (planeIdem t ε S false) := by
  set G : Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K :=
    (((g : ↥(StatedSp t K)) : GL (Fin t ⊕ Fin t) K) :
      Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K) with hG
  set P : Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K := SpBlocks.planeIdem t S with hP
  have hGQ : G * (1 - P) = 1 - P := by
    change (((g : ↥(StatedSp t K)) : GL (Fin t ⊕ Fin t) K) :
      Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K) *
      (1 - SpBlocks.planeIdem t S) = 1 - SpBlocks.planeIdem t S
    exact hg
  have hGP : G * P = P * G := by
    change (((g : ↥(StatedSp t K)) : GL (Fin t ⊕ Fin t) K) :
      Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K) * SpBlocks.planeIdem t S =
      SpBlocks.planeIdem t S * (((g : ↥(StatedSp t K)) : GL (Fin t ⊕ Fin t) K) :
        Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K)
    exact SpBlocks.commute_planeIdem_of_mem_levi hg
  have hQG : (1 - P) * G = 1 - P := by
    calc (1 - P) * G = G - P * G := by rw [sub_mul, one_mul]
      _ = G - G * P := by rw [hGP]
      _ = G * (1 - P) := by rw [mul_sub, mul_one]
      _ = 1 - P := hGQ
  constructor
  · calc ((planeExt t ε ((g : ↥(StatedSp t K)) : GL (Fin t ⊕ Fin t) K) : GL (LinIdx t ε) K) :
        Matrix (LinIdx t ε) (LinIdx t ε) K) * (1 - planeIdem t ε S false)
        = Matrix.fromBlocks G 0 0 1 * Matrix.fromBlocks (1 - P) 0 0 1 := by
            rw [planeExt_apply_mat', one_sub_planeIdem_apply_mat']
      _ = Matrix.fromBlocks (G * (1 - P)) 0 0 1 := by
            rw [Matrix.fromBlocks_multiply]; simp
      _ = Matrix.fromBlocks (1 - P) 0 0 1 := by rw [hGQ]
      _ = 1 - planeIdem t ε S false := by rw [one_sub_planeIdem_apply_mat']
  · calc (1 - planeIdem t ε S false) *
        ((planeExt t ε ((g : ↥(StatedSp t K)) : GL (Fin t ⊕ Fin t) K) : GL (LinIdx t ε) K) :
          Matrix (LinIdx t ε) (LinIdx t ε) K)
        = Matrix.fromBlocks (1 - P) 0 0 1 * Matrix.fromBlocks G 0 0 1 := by
            rw [planeExt_apply_mat', one_sub_planeIdem_apply_mat']
      _ = Matrix.fromBlocks ((1 - P) * G) 0 0 1 := by
            rw [Matrix.fromBlocks_multiply]; simp
      _ = Matrix.fromBlocks (1 - P) 0 0 1 := by rw [hQG]
      _ = 1 - planeIdem t ε S false := by rw [one_sub_planeIdem_apply_mat']

omit [Finite K] [CharP K 2] in
private theorem mem_blockGroup_extension_iff_lin {e : PlaneRaw.V t} {g : GL (LinIdx t ε) K} :
    g ∈ blockGroup ζ t ε (.extension e) ↔
      g ∈ levi (planeIdem t ε (PlaneRaw.Code.extSupport e) false) ∧
        g * tau ζ t ε e = tau ζ t ε e * g := by
  show g ∈ levi (planeIdem t ε (PlaneRaw.Code.extSupport e) false) ⊓
      Subgroup.centralizer {tau ζ t ε e} ↔ _
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]

omit [Finite K] [CharP K 2] in
private theorem map_blockGroup_le (e : PlaneRaw.V t) :
    (SpBlocks.blockGroup ζ t (.extension e)).map (linExtHom (K := K) t ε) ≤
      blockGroup ζ t ε (.extension e) := by
  intro x hx
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
  rw [mem_blockGroup_extension_iff_lin]
  refine ⟨planeExt_mem_levi' (SpBlocks.mem_blockGroup_extension_iff.mp hg).1, ?_⟩
  have h := congrArg (linExtHom (K := K) t ε)
    (SpBlocks.mem_blockGroup_extension_iff.mp hg).2
  rw [map_mul, map_mul, linExtHom_tau] at h
  exact h

omit [Finite K] [CharP K 2] in
private theorem map_ycode_le (e : PlaneRaw.V t) :
    (SpBlocks.Ycode ζ t (.extension e)).map (linExtHom (K := K) t ε) ≤
      Ycode ζ t ε (.extension e) := by
  rw [SpBlocks.Ycode, Ycode, Subgroup.map_commutator]
  exact Subgroup.commutator_mono (map_blockGroup_le e) (map_blockGroup_le e)

omit [Finite K] [CharP K 2] in
private theorem ycode_le_blockGroup_lin (c : PlaneRaw.Code t) :
    Ycode ζ t ε c ≤ blockGroup ζ t ε c := by
  rw [Ycode]
  exact Subgroup.commutator_le_self _

omit [Finite K] [CharP K 2] in
private theorem spTau_mem_levi_of_lin {e u : PlaneRaw.V t}
    (h : tau ζ t ε u ∈ levi (planeIdem t ε (PlaneRaw.Code.extSupport e) false)) :
    SpBlocks.tau ζ t u ∈ SpBlocks.levi t (PlaneRaw.Code.extSupport e) := by
  have hmat : ((tau ζ t ε u : GL (LinIdx t ε) K) : Matrix (LinIdx t ε) (LinIdx t ε) K) *
      (1 - planeIdem t ε (PlaneRaw.Code.extSupport e) false) =
      1 - planeIdem t ε (PlaneRaw.Code.extSupport e) false := h.1
  rw [tau_apply_mat', one_sub_planeIdem_apply_mat', Matrix.fromBlocks_multiply] at hmat
  simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.zero_mul, add_zero, zero_add] at hmat
  rw [Matrix.fromBlocks_inj] at hmat
  change (((SpBlocks.tau ζ t u : ↥(StatedSp t K)) : GL (Fin t ⊕ Fin t) K) :
      Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K) *
      (1 - SpBlocks.planeIdem t (PlaneRaw.Code.extSupport e)) =
    1 - SpBlocks.planeIdem t (PlaneRaw.Code.extSupport e)
  rw [SpBlocks.coe_tau]
  exact hmat.1

private theorem tau_mem_ycode_extension_of_lin (hK : Nat.card K = 2)
    (hζ : Function.Injective ζ) {e u : PlaneRaw.V t} {i₀ : Fin t} (hi₀ : e i₀ ≠ 0)
    (hu : u ∈ PlaneRaw.insideExt e) :
    tau ζ t ε u ∈ Ycode ζ t ε (.extension e) := by
  have hsp := SpBlocks.tau_mem_ycode_extension_of hK hζ hi₀ hu
  have hmap := map_ycode_le (ζ := ζ) (t := t) (ε := ε) e
    (Subgroup.mem_map_of_mem _ hsp)
  rwa [linExtHom_tau] at hmap

omit [Finite K] [CharP K 2] in
private theorem linTau_nsmul (n : ℕ) (v : PlaneRaw.V t) :
    tau ζ t ε (n • v) = tau ζ t ε v ^ n := by
  have h : (fun i => Multiplicative.ofAdd ((n • v) i)) =
      (fun i => Multiplicative.ofAdd (v i)) ^ n := by
    funext i
    rw [Pi.pow_apply, Pi.smul_apply, ofAdd_nsmul]
  rw [tau, tau, h, map_pow]

omit [Finite K] [CharP K 2] in
private theorem linTau_smul (c : ZMod 3) (v : PlaneRaw.V t) :
    tau ζ t ε (c • v) = tau ζ t ε v ^ c.val := by
  rw [← linTau_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val]

private def linPlanePart (M : Matrix (LinIdx t ε) (LinIdx t ε) K) :
    Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K :=
  Matrix.toBlocks₁₁ M

omit [Finite K] [CharP K 2] in
private theorem linPlanePart_tau (u : PlaneRaw.V t) :
    linPlanePart ((tau ζ t ε u : GL (LinIdx t ε) K) :
        Matrix (LinIdx t ε) (LinIdx t ε) K) =
      WitSpNs.planeMat (fun j =>
        ((ζ (Multiplicative.ofAdd (u j)) : SpecialLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K)) := by
  rw [tau_apply_mat', linPlanePart, Matrix.toBlocks_fromBlocks₁₁]

omit [Finite K] [CharP K 2] in
private theorem linPlanePart_one :
    linPlanePart (1 : Matrix (LinIdx t ε) (LinIdx t ε) K) = 1 := by
  rw [linPlanePart, ← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₁₁]

omit [Finite K] [CharP K 2] in
private theorem eq_fromBlocks_linPlanePart {S : Finset (Fin t)} {g : GL (LinIdx t ε) K}
    (hg : g ∈ levi (planeIdem t ε S false)) :
    (g : Matrix (LinIdx t ε) (LinIdx t ε) K) =
      Matrix.fromBlocks (linPlanePart ((g : GL (LinIdx t ε) K) :
        Matrix (LinIdx t ε) (LinIdx t ε) K)) 0 0 1 := by
  set M : Matrix (LinIdx t ε) (LinIdx t ε) K :=
    (g : Matrix (LinIdx t ε) (LinIdx t ε) K) with hM
  have h1 : M * (1 - planeIdem t ε S false) = 1 - planeIdem t ε S false := by
    rw [hM]
    exact hg.1
  have h2 : (1 - planeIdem t ε S false) * M = 1 - planeIdem t ε S false := by
    rw [hM]
    exact hg.2
  have hQ : (1 - planeIdem t ε S false : Matrix (LinIdx t ε) (LinIdx t ε) K) =
      Matrix.fromBlocks (SpBlocks.planeIdem t Sᶜ) 0 0 1 := by
    rw [one_sub_planeIdem_apply_mat', ← SpBlocks.planeIdem_compl]
  rw [hQ] at h1 h2
  rw [← Matrix.fromBlocks_toBlocks M, Matrix.fromBlocks_multiply] at h1 h2
  simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.one_mul, Matrix.zero_mul, add_zero,
    zero_add] at h1 h2
  have hB0 : M.toBlocks₁₂ = 0 := (Matrix.fromBlocks_inj.mp h1).2.1
  have hD1 : M.toBlocks₂₂ = 1 := (Matrix.fromBlocks_inj.mp h1).2.2.2
  have hC0 : M.toBlocks₂₁ = 0 := (Matrix.fromBlocks_inj.mp h2).2.2.1
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks M]
  rw [hB0, hC0, hD1]
  rfl

omit [Finite K] [CharP K 2] in
private theorem linPlanePart_mul_planeIdem_compl {S : Finset (Fin t)} {g : GL (LinIdx t ε) K}
    (hg : g ∈ levi (planeIdem t ε S false)) :
    linPlanePart ((g : GL (LinIdx t ε) K) : Matrix (LinIdx t ε) (LinIdx t ε) K) *
        SpBlocks.planeIdem t Sᶜ = SpBlocks.planeIdem t Sᶜ := by
  have hQ : (1 - planeIdem t ε S false : Matrix (LinIdx t ε) (LinIdx t ε) K) =
      Matrix.fromBlocks (SpBlocks.planeIdem t Sᶜ) 0 0 1 := by
    rw [one_sub_planeIdem_apply_mat', ← SpBlocks.planeIdem_compl]
  have h1 := hg.1
  rw [hQ] at h1
  rw [eq_fromBlocks_linPlanePart hg, Matrix.fromBlocks_multiply] at h1
  simpa only [Matrix.mul_zero, Matrix.mul_one, Matrix.zero_mul, add_zero] using
    (Matrix.fromBlocks_inj.mp h1).1

omit [Finite K] [CharP K 2] in
private theorem linPlanePart_mul_of_mem_levi {S : Finset (Fin t)} {g h : GL (LinIdx t ε) K}
    (hg : g ∈ levi (planeIdem t ε S false)) (hh : h ∈ levi (planeIdem t ε S false)) :
    linPlanePart (((g * h : GL (LinIdx t ε) K)) :
        Matrix (LinIdx t ε) (LinIdx t ε) K) =
      linPlanePart ((g : Matrix (LinIdx t ε) (LinIdx t ε) K)) *
        linPlanePart ((h : Matrix (LinIdx t ε) (LinIdx t ε) K)) := by
  have hprod : ((g * h : GL (LinIdx t ε) K) : Matrix (LinIdx t ε) (LinIdx t ε) K) =
      Matrix.fromBlocks (linPlanePart ((g : Matrix (LinIdx t ε) (LinIdx t ε) K)) *
        linPlanePart ((h : Matrix (LinIdx t ε) (LinIdx t ε) K))) 0 0 1 := by
    rw [Units.val_mul]
    conv_lhs => rw [eq_fromBlocks_linPlanePart hg, eq_fromBlocks_linPlanePart hh]
    rw [Matrix.fromBlocks_multiply]
    simp
  rw [hprod]
  simp [linPlanePart]

private theorem zmod3_mul_self' {a : ZMod 3} (ha : a ≠ 0) : a * a = 1 := by
  revert a
  decide

omit [Finite K] [CharP K 2] in
private theorem coe_apply_of_mat_levi {S : Finset (Fin t)}
    {G : Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K}
    (hG : G * SpBlocks.planeIdem t Sᶜ = SpBlocks.planeIdem t Sᶜ)
    (x : Fin t ⊕ Fin t) {y : Fin t ⊕ Fin t} (hy : Sum.elim id id y ∉ S) :
    G x y = (1 : Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K) x y := by
  have h' := congrFun (congrFun hG x) y
  rw [SpBlocks.planeIdem, Matrix.mul_diagonal, Matrix.diagonal_apply,
    if_pos (Finset.mem_compl.mpr hy), mul_one] at h'
  rw [h', Matrix.one_apply]
  by_cases hxy : x = y
  · rw [if_pos hxy, if_pos hxy, hxy, if_pos (Finset.mem_compl.mpr hy)]
  · rw [if_neg hxy, if_neg hxy]

omit [Finite K] [CharP K 2] in
private theorem planeBlock_eq_zero_of_mat_levi {S : Finset (Fin t)}
    {G : Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K}
    (hG : G * SpBlocks.planeIdem t Sᶜ = SpBlocks.planeIdem t Sᶜ)
    {a c : Fin t} (hc : c ∉ S) (hac : a ≠ c) :
    SpBlocks.planeBlock G a c = 0 := by
  ext s t
  have hne : WitSpNs.coord s a ≠ WitSpNs.coord t c := fun h =>
    hac (by simpa using congrArg WitSpNs.plane h)
  have hy : Sum.elim id id (WitSpNs.coord t c) ∉ S := by
    show WitSpNs.plane (WitSpNs.coord t c) ∉ S
    rw [WitSpNs.plane_coord]
    exact hc
  rw [SpBlocks.planeBlock, Matrix.of_apply, coe_apply_of_mat_levi hG _ hy,
    Matrix.one_apply_ne hne]
  rfl

omit [Finite K] [CharP K 2] in
private theorem mul_conj_mul' {A B N N' L R : Matrix (Fin 2) (Fin 2) K} (h : N' * N = 1) :
    L * (A * B) * R = L * A * N' * (N * B * R) := by
  rw [show A * B = A * (N' * N) * B by rw [h, Matrix.mul_one]]
  simp only [Matrix.mul_assoc]

omit [Finite K] [CharP K 2] in
private theorem normBlock_mul_lin {e : PlaneRaw.V t}
    {G : Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K}
    (hG : G * SpBlocks.planeIdem t (PlaneRaw.Code.extSupport e)ᶜ =
      SpBlocks.planeIdem t (PlaneRaw.Code.extSupport e)ᶜ)
    (H : Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K) {a : Fin t}
    (ha : a ∈ PlaneRaw.Code.extSupport e) (b : Fin t) :
    SpBlocks.normBlock e (G * H) a b =
      ∑ c ∈ PlaneRaw.Code.extSupport e,
        SpBlocks.normBlock e G a c * SpBlocks.normBlock e H c b := by
  have hsum : SpBlocks.planeBlock (G * H) a b =
      ∑ c ∈ PlaneRaw.Code.extSupport e,
        SpBlocks.planeBlock G a c * SpBlocks.planeBlock H c b := by
    rw [SpBlocks.planeBlock_mul]
    refine (Finset.sum_subset (Finset.subset_univ _) fun c _ hc => ?_).symm
    rw [planeBlock_eq_zero_of_mat_levi hG hc fun hac => hc (hac ▸ ha), Matrix.zero_mul]
  rw [SpBlocks.normBlock, hsum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [SpBlocks.normBlock, SpBlocks.normBlock]
  exact mul_conj_mul' (SpBlocks.coe_normSL_inv_mul (e c))

omit [Finite K] [CharP K 2] in
private theorem conj_commute' {Na Na' Nb Nb' B Za Zb Z : Matrix (Fin 2) (Fin 2) K}
    (ha : Na' * Na = 1) (hb : Nb' * Nb = 1) (hZa : Na * Za * Na' = Z) (hZb : Nb * Zb * Nb' = Z)
    (hB : B * Zb = Za * B) : Na * B * Nb' * Z = Z * (Na * B * Nb') := by
  calc Na * B * Nb' * Z = Na * B * Nb' * (Nb * Zb * Nb') := by rw [hZb]
    _ = Na * B * (Nb' * Nb) * Zb * Nb' := by simp only [Matrix.mul_assoc]
    _ = Na * (B * Zb) * Nb' := by rw [hb, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = Na * (Za * B) * Nb' := by rw [hB]
    _ = Na * Za * (Na' * Na) * B * Nb' := by rw [ha, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = (Na * Za * Na') * (Na * B * Nb') := by simp only [Matrix.mul_assoc]
    _ = Z * (Na * B * Nb') := by rw [hZa]

private theorem normBlock_commute_lin (hK : Nat.card K = 2)
    (hζ : Function.Injective ζ) {e : PlaneRaw.V t} {g : GL (LinIdx t ε) K}
    {G : Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K}
    (hg : (g : Matrix (LinIdx t ε) (LinIdx t ε) K) = Matrix.fromBlocks G 0 0 1)
    (hgC : g * tau ζ t ε e = tau ζ t ε e * g) {a b : Fin t} (ha : e a ≠ 0) (hb : e b ≠ 0) :
    SpBlocks.normBlock e G a b *
        ((ζ (Multiplicative.ofAdd 1) : SpecialLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K) =
      ((ζ (Multiplicative.ofAdd 1) : SpecialLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K) * SpBlocks.normBlock e G a b := by
  have hmat := congrArg (fun x : GL (LinIdx t ε) K =>
    ((x : Matrix (LinIdx t ε) (LinIdx t ε) K))) hgC
  simp only [Units.val_mul] at hmat
  rw [hg, tau_apply_mat', Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at hmat
  simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.zero_mul, add_zero] at hmat
  have hB : SpBlocks.planeBlock G a b *
      ((ζ (Multiplicative.ofAdd (e b)) : SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) =
      ((ζ (Multiplicative.ofAdd (e a)) : SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) * SpBlocks.planeBlock G a b := by
    have h := congrArg (fun X => SpBlocks.planeBlock X a b) (Matrix.fromBlocks_inj.mp hmat).1
    rw [SpBlocks.planeBlock_mul_planeMat, SpBlocks.planeBlock_planeMat_mul] at h
    exact h
  have hZa := SpBlocks.coe_normSL_conj_zeta hK hζ ha (e a)
  have hZb := SpBlocks.coe_normSL_conj_zeta hK hζ hb (e b)
  rw [zmod3_mul_self' ha] at hZa
  rw [zmod3_mul_self' hb] at hZb
  exact conj_commute' (SpBlocks.coe_normSL_inv_mul _) (SpBlocks.coe_normSL_inv_mul _)
    hZa hZb hB

private noncomputable def linBlockMat (hK : Nat.card K = 2)
    (hζ : Function.Injective ζ) {e : PlaneRaw.V t}
    (g : ↥(blockGroup ζ t ε (PlaneRaw.Code.extension e))) :
    Matrix ↥(PlaneRaw.Code.extSupport e) ↥(PlaneRaw.Code.extSupport e) ↥(SpBlocks.zAlg ζ) :=
  Matrix.of fun a b =>
    ⟨SpBlocks.normBlock e (linPlanePart ((g : GL (LinIdx t ε) K) :
        Matrix (LinIdx t ε) (LinIdx t ε) K)) a b,
      SpBlocks.mem_zAlg_of_commute hK hζ
        (normBlock_commute_lin hK hζ
          (eq_fromBlocks_linPlanePart (mem_blockGroup_extension_iff_lin.mp g.2).1)
          (mem_blockGroup_extension_iff_lin.mp g.2).2
          ((PlaneRaw.mem_extSupport e a).mp a.2)
          ((PlaneRaw.mem_extSupport e b).mp b.2))⟩

private theorem linBlockMat_one (hK : Nat.card K = 2)
    (hζ : Function.Injective ζ) {e : PlaneRaw.V t} :
    linBlockMat (ζ := ζ) (t := t) (ε := ε) hK hζ
        (1 : ↥(blockGroup ζ t ε (PlaneRaw.Code.extension e))) = 1 := by
  refine Matrix.ext fun a b => Subtype.ext ?_
  change SpBlocks.normBlock e (linPlanePart
      (((1 : ↥(blockGroup ζ t ε (PlaneRaw.Code.extension e))) : GL (LinIdx t ε) K) :
        Matrix (LinIdx t ε) (LinIdx t ε) K)) a b =
    (((1 : Matrix ↥(PlaneRaw.Code.extSupport e) ↥(PlaneRaw.Code.extSupport e) ↥(SpBlocks.zAlg ζ))
      a b : ↥(SpBlocks.zAlg ζ)) : Matrix (Fin 2) (Fin 2) K)
  rw [show ((1 : ↥(blockGroup ζ t ε (PlaneRaw.Code.extension e))) : GL (LinIdx t ε) K) = 1
    from rfl, show linPlanePart ((1 : GL (LinIdx t ε) K) :
      Matrix (LinIdx t ε) (LinIdx t ε) K) = 1 from linPlanePart_one]
  rw [SpBlocks.normBlock, SpBlocks.planeBlock_one]
  by_cases hab : a = b
  · subst hab
    rw [Matrix.one_apply_eq, if_pos rfl, Matrix.mul_one, SpBlocks.coe_normSL_mul_inv]
    rfl
  · rw [Matrix.one_apply_ne hab, if_neg fun h => hab (Subtype.ext h), Matrix.mul_zero,
      Matrix.zero_mul]
    rfl

private theorem linBlockMat_mul (hK : Nat.card K = 2)
    (hζ : Function.Injective ζ) {e : PlaneRaw.V t}
    (g h : ↥(blockGroup ζ t ε (PlaneRaw.Code.extension e))) :
    linBlockMat hK hζ (g * h) = linBlockMat hK hζ g * linBlockMat hK hζ h := by
  refine Matrix.ext fun a b => Subtype.ext ?_
  rw [Matrix.mul_apply, AddSubmonoidClass.coe_finset_sum]
  change SpBlocks.normBlock e (linPlanePart
      (((g * h : ↥(blockGroup ζ t ε (PlaneRaw.Code.extension e))) : GL (LinIdx t ε) K) :
        Matrix (LinIdx t ε) (LinIdx t ε) K)) a b =
    ∑ c : ↥(PlaneRaw.Code.extSupport e),
      SpBlocks.normBlock e (linPlanePart
        ((g : GL (LinIdx t ε) K) : Matrix (LinIdx t ε) (LinIdx t ε) K)) a c *
      SpBlocks.normBlock e (linPlanePart
        ((h : GL (LinIdx t ε) K) : Matrix (LinIdx t ε) (LinIdx t ε) K)) c b
  have hgL : (g : GL (LinIdx t ε) K) ∈
      levi (planeIdem t ε (PlaneRaw.Code.extSupport e) false) :=
    (mem_blockGroup_extension_iff_lin.mp g.2).1
  have hhL : (h : GL (LinIdx t ε) K) ∈
      levi (planeIdem t ε (PlaneRaw.Code.extSupport e) false) :=
    (mem_blockGroup_extension_iff_lin.mp h.2).1
  rw [Subgroup.coe_mul, linPlanePart_mul_of_mem_levi hgL hhL]
  rw [normBlock_mul_lin (e := e) (G := linPlanePart ((g : GL (LinIdx t ε) K) :
      Matrix (LinIdx t ε) (LinIdx t ε) K))
      (H := linPlanePart ((h : GL (LinIdx t ε) K) :
        Matrix (LinIdx t ε) (LinIdx t ε) K))
      (linPlanePart_mul_planeIdem_compl hgL) a.2 b]
  exact (Finset.sum_coe_sort (PlaneRaw.Code.extSupport e)
    (fun c => SpBlocks.normBlock e (linPlanePart ((g : GL (LinIdx t ε) K) :
      Matrix (LinIdx t ε) (LinIdx t ε) K)) a c *
      SpBlocks.normBlock e (linPlanePart ((h : GL (LinIdx t ε) K) :
        Matrix (LinIdx t ε) (LinIdx t ε) K)) c b)).symm

end

attribute [local instance] SpBlocks.zAlgCommRing

private noncomputable def linDet (hK : Nat.card K = 2)
    (hζ : Function.Injective ζ) {e : PlaneRaw.V t} :
    ↥(blockGroup ζ t ε (PlaneRaw.Code.extension e)) →* ↥(SpBlocks.zAlg ζ) where
  toFun g := (linBlockMat hK hζ g).det
  map_one' := by rw [linBlockMat_one, Matrix.det_one]
  map_mul' g h := by rw [linBlockMat_mul, Matrix.det_mul]

private theorem linDet_apply (hK : Nat.card K = 2)
    (hζ : Function.Injective ζ) {e : PlaneRaw.V t}
    (g : ↥(blockGroup ζ t ε (PlaneRaw.Code.extension e))) :
    linDet hK hζ g = (linBlockMat hK hζ g).det :=
  rfl

private theorem linBlockMat_tau (hK : Nat.card K = 2)
    (hζ : Function.Injective ζ) {e u : PlaneRaw.V t}
    (hu : tau ζ t ε u ∈ blockGroup ζ t ε (PlaneRaw.Code.extension e)) :
    linBlockMat hK hζ ⟨tau ζ t ε u, hu⟩ =
      Matrix.diagonal fun a : ↥(PlaneRaw.Code.extSupport e) =>
        SpBlocks.zetaC ζ (Multiplicative.ofAdd (e a * u a)) := by
  refine Matrix.ext fun a b => Subtype.ext ?_
  change SpBlocks.normBlock e (linPlanePart ((tau ζ t ε u : GL (LinIdx t ε) K) :
      Matrix (LinIdx t ε) (LinIdx t ε) K)) a b =
    (((Matrix.diagonal fun a : ↥(PlaneRaw.Code.extSupport e) =>
      SpBlocks.zetaC ζ (Multiplicative.ofAdd (e a * u a))) a b : ↥(SpBlocks.zAlg ζ)) :
      Matrix (Fin 2) (Fin 2) K)
  rw [linPlanePart_tau, SpBlocks.normBlock, SpBlocks.planeBlock_planeMat, Matrix.diagonal_apply]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl, if_pos rfl, SpBlocks.coe_normSL_conj_zeta hK hζ
      ((PlaneRaw.mem_extSupport e a).mp a.2) (u a)]
    rfl
  · rw [if_neg fun h => hab (Subtype.ext h), if_neg hab, Matrix.mul_zero, Matrix.zero_mul]
    rfl

private theorem linDet_tau (hK : Nat.card K = 2)
    (hζ : Function.Injective ζ) {e u : PlaneRaw.V t}
    (hu : tau ζ t ε u ∈ blockGroup ζ t ε (PlaneRaw.Code.extension e)) :
    linDet hK hζ ⟨tau ζ t ε u, hu⟩ =
      SpBlocks.zetaC ζ (Multiplicative.ofAdd
        (∑ a : ↥(PlaneRaw.Code.extSupport e), e a * u a)) := by
  rw [linDet_apply, linBlockMat_tau, Matrix.det_diagonal, ofAdd_sum, map_prod]

private theorem linDet_eq_one_of_mem_ycode (hK : Nat.card K = 2)
    (hζ : Function.Injective ζ) {e : PlaneRaw.V t} {g : GL (LinIdx t ε) K}
    (hg : g ∈ Ycode ζ t ε (PlaneRaw.Code.extension e)) :
    linDet hK hζ ⟨g, ycode_le_blockGroup_lin _ hg⟩ = 1 := by
  have key : Ycode ζ t ε (PlaneRaw.Code.extension e) ≤
      (linDet hK hζ).ker.map (blockGroup ζ t ε (PlaneRaw.Code.extension e)).subtype := by
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    refine ⟨⁅(⟨a, ha⟩ : ↥(blockGroup ζ t ε (PlaneRaw.Code.extension e))), ⟨b, hb⟩⁆,
      MonoidHom.mem_ker.mpr ?_, rfl⟩
    rw [commutatorElement_def, map_mul, map_mul, map_mul]
    calc linDet hK hζ ⟨a, ha⟩ * linDet hK hζ ⟨b, hb⟩ * linDet hK hζ ⟨a, ha⟩⁻¹ *
          linDet hK hζ ⟨b, hb⟩⁻¹
        = linDet hK hζ (⟨a, ha⟩ * ⟨a, ha⟩⁻¹) * linDet hK hζ (⟨b, hb⟩ * ⟨b, hb⟩⁻¹) := by
          rw [map_mul, map_mul]
          ring
      _ = 1 := by rw [mul_inv_cancel, mul_inv_cancel, map_one, mul_one]
  obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.mp (key hg)
  have hx' : x = ⟨g, ycode_le_blockGroup_lin _ hg⟩ := Subtype.ext hxg
  rw [← hx']
  exact hx

private theorem sum_eq_zero_of_tau_mem_ycode_lin (hK : Nat.card K = 2)
    (hζ : Function.Injective ζ) {e u : PlaneRaw.V t}
    (h : tau ζ t ε u ∈ Ycode ζ t ε (PlaneRaw.Code.extension e)) :
    ∑ i, e i * u i = 0 := by
  have hB : tau ζ t ε u ∈ blockGroup ζ t ε (PlaneRaw.Code.extension e) :=
    ycode_le_blockGroup_lin _ h
  have h1 := linDet_eq_one_of_mem_ycode hK hζ h
  rw [show linDet hK hζ ⟨tau ζ t ε u, hB⟩ = SpBlocks.zetaC ζ
      (Multiplicative.ofAdd (∑ a : ↥(PlaneRaw.Code.extSupport e), e a * u a)) from
    linDet_tau hK hζ hB] at h1
  have h2 : Multiplicative.ofAdd (∑ a : ↥(PlaneRaw.Code.extSupport e), e a * u a) = 1 :=
    SpBlocks.zetaC_injective hζ (h1.trans (map_one _).symm)
  rw [ofAdd_eq_one, Finset.sum_coe_sort (PlaneRaw.Code.extSupport e)
    fun i => e i * u i] at h2
  rw [← h2]
  exact (Finset.sum_subset (Finset.subset_univ _) fun k _ hk => by
    rw [PlaneRaw.mem_extSupport, not_not] at hk
    rw [hk, zero_mul]).symm

theorem tau_mem_ycode_extension_iff (hK : Nat.card K = 2) (hζ : Function.Injective ζ)
    {e : PlaneRaw.V t} (he : 2 ≤ (PlaneRaw.Code.extSupport e).card) (u : PlaneRaw.V t) :
    tau ζ t ε u ∈ Ycode ζ t ε (PlaneRaw.Code.extension e) ↔ u ∈ PlaneRaw.insideExt e := by
  constructor
  · intro h
    rw [PlaneRaw.mem_insideExt]
    refine ⟨?_, sum_eq_zero_of_tau_mem_ycode_lin hK hζ h⟩
    intro i hi
    have hB : tau ζ t ε u ∈ blockGroup ζ t ε (PlaneRaw.Code.extension e) :=
      ycode_le_blockGroup_lin _ h
    have hsp := spTau_mem_levi_of_lin (mem_blockGroup_extension_iff_lin.mp hB).1
    exact SpBlocks.eq_zero_of_tau_mem_levi hK hζ hsp i (by simpa using hi)
  · intro hu
    obtain ⟨i₀, hi₀⟩ := Finset.card_pos.mp (by omega : 0 <
      (PlaneRaw.Code.extSupport e).card)
    exact tau_mem_ycode_extension_of_lin hK hζ ((PlaneRaw.mem_extSupport e i₀).mp hi₀) hu

omit [Finite K] [CharP K 2] in
private theorem commute_tau_of_mem_levi_linear'
    {S : Finset (Fin t)} {u : PlaneRaw.V t} (hu : ∀ i ∈ S, u i = 0)
    {g : GL (LinIdx t ε) K} (hg : g ∈ levi (planeIdem t ε S false)) :
    g * tau ζ t ε u = tau ζ t ε u * g := by
  set G : Matrix (LinIdx t ε) (LinIdx t ε) K := (g : Matrix (LinIdx t ε) (LinIdx t ε) K)
    with hG
  set T : Matrix (LinIdx t ε) (LinIdx t ε) K :=
    ((tau ζ t ε u : GL (LinIdx t ε) K) : Matrix (LinIdx t ε) (LinIdx t ε) K) with hT
  set P : Matrix (LinIdx t ε) (LinIdx t ε) K := planeIdem t ε S false with hP
  set Q : Matrix (LinIdx t ε) (LinIdx t ε) K := 1 - P with hQ
  have hGQ : G * Q = Q := by simpa [hG, hQ, hP] using hg.1
  have hQG : Q * G = Q := by simpa [hG, hQ, hP] using hg.2
  have hPQ : P + Q = 1 := by rw [hQ]; simp
  have hP' : P = 1 - Q := by rw [hQ]; abel_nf
  have hGP : G * P = P * G := by
    have h1 : G * P = G - Q := by
      rw [hP', mul_sub, mul_one, hGQ]
    have h2 : P * G = G - Q := by
      rw [hP', sub_mul, one_mul, hQG]
    rw [h1, h2]
  have hPsp : SpBlocks.planeIdem (K := K) t S * SpBlocks.planeIdem (K := K) t S =
      SpBlocks.planeIdem (K := K) t S :=
    SpBlocks.isIdempotentElem_planeIdem (K := K) t S
  have hPP : P * P = P := by
    rw [show P = Matrix.fromBlocks (SpBlocks.planeIdem t S) 0 0 0 by
      simpa [hP] using planeIdem_apply_mat' (S := S),
      Matrix.fromBlocks_multiply]
    simp [hPsp]
  have hQQ : Q * Q = Q := by
    rw [hQ]
    calc (1 - P) * (1 - P) = 1 * (1 - P) - P * (1 - P) := by rw [sub_mul]
      _ = (1 - P) - (P * 1 - P * P) := by rw [one_mul, mul_sub]
      _ = (1 - P) - (P - P) := by rw [mul_one, hPP]
      _ = 1 - P := by rw [sub_self, sub_zero]
  have hM : ∀ i ∈ S,
      ((ζ (Multiplicative.ofAdd (u i)) : SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) = 1 := by
    intro i hi
    rw [hu i hi, ofAdd_zero, map_one, Matrix.SpecialLinearGroup.coe_one]
  have hAB : WitSpNs.planeMat (fun j =>
      ((ζ (Multiplicative.ofAdd (u j)) : SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K)) * SpBlocks.planeIdem t S = SpBlocks.planeIdem t S := by
    rw [SpBlocks.planeIdem_eq_planeMat, WitSpNs.planeMat_mul]
    congr 1
    funext j
    by_cases hj : j ∈ S
    · simp [hj, hM j hj]
    · simp [hj]
  have hBA : SpBlocks.planeIdem t S * WitSpNs.planeMat (fun j =>
      ((ζ (Multiplicative.ofAdd (u j)) : SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K)) = SpBlocks.planeIdem t S := by
    rw [SpBlocks.planeIdem_eq_planeMat, WitSpNs.planeMat_mul]
    congr 1
    funext j
    by_cases hj : j ∈ S
    · simp [hj, hM j hj]
    · simp [hj]
  have hTP : T * P = P := by
    rw [show T = Matrix.fromBlocks (WitSpNs.planeMat fun j =>
        ((ζ (Multiplicative.ofAdd (u j)) : SpecialLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K)) 0 0 1 by simpa [hT] using tau_apply_mat' (u := u),
      show P = Matrix.fromBlocks (SpBlocks.planeIdem t S) 0 0 0 by
        simpa [hP] using planeIdem_apply_mat' (S := S),
      Matrix.fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero]
    rw [hAB]
  have hPT : P * T = P := by
    rw [show T = Matrix.fromBlocks (WitSpNs.planeMat fun j =>
        ((ζ (Multiplicative.ofAdd (u j)) : SpecialLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K)) 0 0 1 by simpa [hT] using tau_apply_mat' (u := u),
      show P = Matrix.fromBlocks (SpBlocks.planeIdem t S) 0 0 0 by
        simpa [hP] using planeIdem_apply_mat' (S := S),
      Matrix.fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero]
    rw [hBA]
  have hTQ : T * Q = Q * T := by
    calc T * Q = T * (1 - P) := by rw [hQ]
      _ = T - T * P := by rw [mul_sub, mul_one]
      _ = T - P := by rw [hTP]
      _ = T - P * T := by rw [hPT]
      _ = (1 - P) * T := by rw [sub_mul, one_mul]
      _ = Q * T := by rw [hQ]
  have hQTQ : Q * T * Q = Q * T := by
    rw [Matrix.mul_assoc, hTQ, ← Matrix.mul_assoc, hQQ]
  have hTdecomp : T = P + Q * T * Q := by
    calc T = T * 1 := by rw [mul_one]
      _ = T * (P + Q) := by rw [hPQ]
      _ = T * P + T * Q := by rw [mul_add]
      _ = P + T * Q := by rw [hTP]
      _ = P + Q * T := by rw [hTQ]
      _ = P + Q * T * Q := by rw [hQTQ]
  have hGZ : G * (Q * T * Q) = Q * T * Q := by
    calc G * (Q * T * Q) = (G * (Q * T)) * Q := by rw [← Matrix.mul_assoc]
      _ = ((G * Q) * T) * Q := by rw [← Matrix.mul_assoc]
      _ = (G * Q) * (T * Q) := by rw [Matrix.mul_assoc]
      _ = Q * (T * Q) := by rw [hGQ]
      _ = Q * T * Q := by rw [← Matrix.mul_assoc]
  have hTZG : (Q * T * Q) * G = Q * T * Q := by
    calc (Q * T * Q) * G = (Q * T) * (Q * G) := by rw [← Matrix.mul_assoc]
      _ = Q * T * Q := by rw [hQG]
  have hGT : G * T = P * G + Q * T * Q := by
    calc G * T = G * (P + Q * T * Q) := by conv_lhs => rw [hTdecomp]
      _ = G * P + G * (Q * T * Q) := by rw [mul_add]
      _ = P * G + G * (Q * T * Q) := by rw [hGP]
      _ = P * G + Q * T * Q := by rw [hGZ]
  have hTG : T * G = P * G + Q * T * Q := by
    calc T * G = (P + Q * T * Q) * G := by conv_lhs => rw [hTdecomp]
      _ = P * G + (Q * T * Q) * G := by rw [add_mul]
      _ = P * G + Q * T * Q := by rw [hTZG]
  apply Units.ext
  exact hGT.trans hTG.symm

omit [Finite K] [CharP K 2] in
private theorem tau_commute_ycode_extension_of_lin {e u : PlaneRaw.V t} {i₀ : Fin t}
    (hi₀ : e i₀ ≠ 0)
    (hu : u ∈ PlaneRaw.centExt e) :
    ∀ g ∈ Ycode ζ t ε (PlaneRaw.Code.extension e), tau ζ t ε u * g = g * tau ζ t ε u := by
  intro g hg
  have hgB : g ∈ blockGroup ζ t ε (PlaneRaw.Code.extension e) := ycode_le_blockGroup_lin _ hg
  obtain ⟨hgL, hgC⟩ := mem_blockGroup_extension_iff_lin.mp hgB
  have hzero : ∀ i ∈ PlaneRaw.Code.extSupport e, (u - (e i₀ * u i₀) • e) i = 0 := by
    intro i hi
    have h := (PlaneRaw.mem_centExt e u).mp hu i hi i₀ ((PlaneRaw.mem_extSupport e i₀).mpr hi₀)
    have hsq := zmod3_mul_self' ((PlaneRaw.mem_extSupport e i).mp hi)
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination e i * h - u i * hsq
  have hdec : tau ζ t ε u = tau ζ t ε e ^ (e i₀ * u i₀).val *
      tau ζ t ε (u - (e i₀ * u i₀) • e) := by
    rw [← linTau_smul, ← tau_add, add_sub_cancel]
  have h1 : Commute (tau ζ t ε e) g := hgC.symm
  have h2 : Commute (tau ζ t ε (u - (e i₀ * u i₀) • e)) g :=
    (commute_tau_of_mem_levi_linear' hzero hgL).symm
  rw [hdec]
  exact (h1.pow_left _).mul_left h2

omit [Finite K] in
private theorem sl2W_mul_self' :
    (sl2W : SpecialLinearGroup (Fin 2) K) * sl2W = 1 := by
  rw [sl2W_mul_sl2W, sp_units_neg_one_eq_one_of_two (CharP.cast_eq_zero K 2), map_one]

omit [Finite K] in
private theorem extSwap_mul_self' {e : PlaneRaw.V t} {i j : Fin t} (hij : i ≠ j) :
    (SpBlocks.extSwap (K := K) e i j hij : ↥(StatedSp t K)) *
      SpBlocks.extSwap (K := K) e i j hij = 1 := by
  unfold SpBlocks.extSwap
  split_ifs with h
  · rw [← map_mul, sl2W_mul_self', map_one]
  · set a : ↥(StatedSp t K) := lam i sl2W
    set b : ↥(StatedSp t K) := lam j sl2W
    set r : ↥(StatedSp t K) := rho i j hij sl2W
    have ha : a * a = 1 := by
      dsimp only [a]
      rw [← map_mul, sl2W_mul_self', map_one]
    have hb : b * b = 1 := by
      dsimp only [b]
      rw [← map_mul, sl2W_mul_self', map_one]
    have hr : r * r = 1 := by
      dsimp only [r]
      rw [← map_mul, sl2W_mul_self', map_one]
    have hra : r * a * r⁻¹ = b := by
      have h := congrArg (fun f => f sl2W)
        (conj_rho_sl2W_comp_lam_fst (k := K) (i := i) (j := j) hij)
      simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        a, b, r] using h
    have hrb : r * b * r⁻¹ = a := by
      have h := congrArg (fun f => f sl2W)
        (conj_rho_sl2W_comp_lam_snd (k := K) (i := i) (j := j) hij)
      simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        a, b, r] using h
    have hrinv : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr
    have hra' : r * a = b * r := by
      have h1 : r * a * r = b := by rwa [hrinv] at hra
      calc r * a = (r * a) * 1 := (mul_one _).symm
        _ = (r * a) * (r * r) := by rw [hr]
        _ = (r * a * r) * r := by group
        _ = b * r := by rw [h1]
    have hrb' : r * b = a * r := by
      have h1 : r * b * r = a := by rwa [hrinv] at hrb
      calc r * b = (r * b) * 1 := (mul_one _).symm
        _ = (r * b) * (r * r) := by rw [hr]
        _ = (r * b * r) * r := by group
        _ = a * r := by rw [h1]
    calc (a * b * r) * (a * b * r) = a * (b * ((r * a) * b)) * r := by group
      _ = a * (b * ((b * r) * b)) * r := by rw [hra']
      _ = a * ((b * b) * (r * b)) * r := by group
      _ = a * (a * r) * r := by rw [hb, one_mul, hrb']
      _ = (a * a) * (r * r) := by group
      _ = 1 := by rw [ha, hr, mul_one]

private theorem mem_ycode_of_mul_self_relIndex_three {G : Type*} [Group G]
    {B Y : Subgroup G} [hN : (Y.subgroupOf B).Normal] (hidx : Y.relIndex B = 3)
    {σ : G} (hσB : σ ∈ B) (hσ2 : σ * σ = 1) : σ ∈ Y := by
  classical
  let q : ↥B →* (↥B ⧸ Y.subgroupOf B) := QuotientGroup.mk' _
  have hcard : Nat.card (↥B ⧸ Y.subgroupOf B) = 3 := by
    rw [← Subgroup.index_eq_card]
    exact hidx
  have hq2 : q ⟨σ, hσB⟩ ^ 2 = 1 := by
    rw [← map_pow, show (⟨σ, hσB⟩ : ↥B) ^ 2 = 1 from by
      rw [pow_two]
      exact Subtype.ext hσ2, map_one]
  have hdvd2 : orderOf (q ⟨σ, hσB⟩) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hq2
  have hdvd3 : orderOf (q ⟨σ, hσB⟩) ∣ 3 := by
    rw [← hcard]
    exact orderOf_dvd_natCard _
  have hone : orderOf (q ⟨σ, hσB⟩) = 1 := by
    have h : orderOf (q ⟨σ, hσB⟩) ∣ Nat.gcd 2 3 := Nat.dvd_gcd hdvd2 hdvd3
    rwa [show Nat.gcd 2 3 = 1 by decide, Nat.dvd_one] at h
  have hq1 : q ⟨σ, hσB⟩ = 1 := orderOf_eq_one_iff.mp hone
  have hmem : (⟨σ, hσB⟩ : ↥B) ∈ Y.subgroupOf B := by
    rw [← QuotientGroup.eq_one_iff]
    simpa only [q, QuotientGroup.mk'_apply] using hq1
  exact Subgroup.mem_subgroupOf.mp hmem

omit [Finite K] [CharP K 2] in
private theorem subgroupOf_ycode_normal (e : PlaneRaw.V t) :
    ((Ycode ζ t ε (PlaneRaw.Code.extension e)).subgroupOf
      (blockGroup ζ t ε (PlaneRaw.Code.extension e))).Normal := by
  set B := blockGroup ζ t ε (PlaneRaw.Code.extension e) with hB
  set Y := Ycode ζ t ε (PlaneRaw.Code.extension e) with hY
  have hYB : Y ≤ B := ycode_le_blockGroup_lin _
  refine ⟨fun n hn b => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hbn : ⁅(b : GL (LinIdx t ε) K), (n : GL (LinIdx t ε) K)⁆ ∈ Y := by
    rw [hY, Ycode]
    exact Subgroup.commutator_mem_commutator b.2 (hYB hn)
  have hEq : (((b * n * b⁻¹ : ↥B)) : GL (LinIdx t ε) K) =
      ⁅(b : GL (LinIdx t ε) K), (n : GL (LinIdx t ε) K)⁆ *
        (n : GL (LinIdx t ε) K) := by
    rw [commutatorElement_def]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [hEq]
  exact Y.mul_mem hbn hn

omit [Finite K] in
private theorem linExtSwap_mul_self {e : PlaneRaw.V t} {i j : Fin t} (hij : i ≠ j) :
    linExtHom (K := K) t ε (SpBlocks.extSwap e i j hij) *
      linExtHom (K := K) t ε (SpBlocks.extSwap e i j hij) = 1 := by
  rw [← map_mul, extSwap_mul_self' hij, map_one]

private theorem linExtSwap_mem_ycode (hK : Nat.card K = 2)
    (hζ : Function.Injective ζ) {e : PlaneRaw.V t} {i j : Fin t} (hij : i ≠ j)
    (hei : e i ≠ 0) (hej : e j ≠ 0)
    (hidx : (Ycode ζ t ε (PlaneRaw.Code.extension e)).relIndex
      (blockGroup ζ t ε (PlaneRaw.Code.extension e)) = 3) :
    linExtHom (K := K) t ε (SpBlocks.extSwap e i j hij) ∈
      Ycode ζ t ε (PlaneRaw.Code.extension e) := by
  have hB : linExtHom (K := K) t ε (SpBlocks.extSwap e i j hij) ∈
      blockGroup ζ t ε (PlaneRaw.Code.extension e) :=
    map_blockGroup_le e (Subgroup.mem_map_of_mem _
      (SpBlocks.extSwap_mem_blockGroup hK hζ hei hej hij))
  exact mem_ycode_of_mul_self_relIndex_three
    (hN := subgroupOf_ycode_normal (ζ := ζ) (t := t) (ε := ε) e) hidx hB
    (linExtSwap_mul_self hij)

private theorem linExtSwap_conj_tau (hK : Nat.card K = 2)
    (hζ : Function.Injective ζ) {e : PlaneRaw.V t} {i j : Fin t} (hij : i ≠ j)
    (hei : e i ≠ 0) (hej : e j ≠ 0) (u : PlaneRaw.V t) :
    linExtHom (K := K) t ε (SpBlocks.extSwap e i j hij) * tau ζ t ε u *
        (linExtHom (K := K) t ε (SpBlocks.extSwap e i j hij))⁻¹ =
      tau ζ t ε (SpBlocks.swapVec e i j u) := by
  have h := congrArg (linExtHom (K := K) t ε)
    (SpBlocks.extSwap_conj_tau hK hζ hij hei hej u)
  simpa only [map_mul, map_inv, linExtHom_tau] using h

private theorem centExt_of_tau_commute_ycode_lin
    (hK : Nat.card K = 2) (hζ : Function.Injective ζ) {e u : PlaneRaw.V t}
    (hidx : (Ycode ζ t ε (PlaneRaw.Code.extension e)).relIndex
      (blockGroup ζ t ε (PlaneRaw.Code.extension e)) = 3)
    (h : ∀ g ∈ Ycode ζ t ε (PlaneRaw.Code.extension e),
      tau ζ t ε u * g = g * tau ζ t ε u) :
    u ∈ PlaneRaw.centExt e := by
  rw [PlaneRaw.mem_centExt]
  intro i hi j hj
  by_cases hij : i = j
  · rw [hij]
  · have hei := (PlaneRaw.mem_extSupport e i).mp hi
    have hej := (PlaneRaw.mem_extSupport e j).mp hj
    let σ : GL (LinIdx t ε) K :=
      linExtHom (K := K) t ε (SpBlocks.extSwap e i j hij)
    have hσY : σ ∈ Ycode ζ t ε (PlaneRaw.Code.extension e) :=
      linExtSwap_mem_ycode hK hζ hij hei hej hidx
    have hcomm := h σ hσY
    have hconj := linExtSwap_conj_tau (t := t) (ε := ε) hK hζ hij hei hej u
    have htau : tau ζ t ε u = tau ζ t ε (SpBlocks.swapVec e i j u) := by
      rw [← hconj]
      rw [show σ * tau ζ t ε u * σ⁻¹ = tau ζ t ε u by
        rw [← hcomm, mul_inv_cancel_right]]
    have hu : u = SpBlocks.swapVec e i j u := tau_injective' hζ htau
    have hui := congrFun hu i
    rw [SpBlocks.swapVec_apply_fst e hij] at hui
    have hsq := zmod3_mul_self' hei
    calc e i * u i = e i * (e i * e j * u j) := by rw [hui]
      _ = (e i * e i) * (e j * u j) := by ring
      _ = e j * u j := by rw [hsq, one_mul]

theorem tau_commute_ycode_extension_iff_of_relIndex (hK : Nat.card K = 2)
    (hζ : Function.Injective ζ) {e : PlaneRaw.V t} (he : 2 ≤ (PlaneRaw.Code.extSupport e).card)
    (hidx : (Ycode ζ t ε (PlaneRaw.Code.extension e)).relIndex
      (blockGroup ζ t ε (PlaneRaw.Code.extension e)) = 3) (u : PlaneRaw.V t) :
    (∀ g ∈ Ycode ζ t ε (PlaneRaw.Code.extension e), tau ζ t ε u * g = g * tau ζ t ε u) ↔
      u ∈ PlaneRaw.centExt e := by
  constructor
  · exact centExt_of_tau_commute_ycode_lin hK hζ hidx
  · intro hu
    obtain ⟨i₀, hi₀⟩ := Finset.card_pos.mp (by omega : 0 <
      (PlaneRaw.Code.extSupport e).card)
    exact tau_commute_ycode_extension_of_lin
      ((PlaneRaw.mem_extSupport e i₀).mp hi₀) hu

end CFSG.StandardType.GGQ2Frame.LinBlocks

end
