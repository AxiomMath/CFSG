module

public import CFSG.LocalAnalysis.StandardType.GGQ2LinTorusAutBasic
import CFSG.LocalAnalysis.StandardType.GGQ2LinBlocksBasic
import CFSG.LocalAnalysis.StandardType.GGQ2LinTorusAutExt
import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksGroup
import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksIdem

public section

namespace CFSG.StandardType.GGQ2Frame.LinBlocks

open CFSG CFSG.StandardType Matrix
open CFSG.Open (StatedSp)
open scoped commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {K : Type} [Field K]

private theorem linPlaneExt_apply_mat (t : ℕ) (ε : Fin 2) (A : GL (Fin t ⊕ Fin t) K) :
    ((planeExt t ε A : GL (LinIdx t ε) K) : Matrix (LinIdx t ε) (LinIdx t ε) K) =
      Matrix.fromBlocks (A : Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K) 0 0 1 :=
  rfl

private theorem linTau_apply_mat (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K)
    (t : ℕ) (ε : Fin 2) (u : PlaneRaw.V t) :
    ((tau ζ t ε u : GL (LinIdx t ε) K) : Matrix (LinIdx t ε) (LinIdx t ε) K) =
      Matrix.fromBlocks
        (WitSpNs.planeMat fun j =>
          ((ζ (Multiplicative.ofAdd (u j)) : SpecialLinearGroup (Fin 2) K) :
            Matrix (Fin 2) (Fin 2) K)) 0 0 1 := by
  rw [tau_eq_planeExt, linPlaneExt_apply_mat, SpBlocks.coe_tau]

private theorem linPlaneIdem_apply_mat (t : ℕ) (ε : Fin 2) (S : Finset (Fin t)) :
    (planeIdem t ε S false : Matrix (LinIdx t ε) (LinIdx t ε) K) =
      Matrix.fromBlocks (SpBlocks.planeIdem t S) 0 0 0 := by
  ext x y
  rcases x with (i | i) | k <;> rcases y with (j | j) | l <;>
    simp [planeIdem, SpBlocks.planeIdem, Matrix.fromBlocks, Matrix.diagonal_apply]

private theorem linOneSubPlaneIdem_apply_mat (t : ℕ) (ε : Fin 2) (S : Finset (Fin t)) :
    (1 - planeIdem t ε S false : Matrix (LinIdx t ε) (LinIdx t ε) K) =
      Matrix.fromBlocks (1 - SpBlocks.planeIdem t S) 0 0 1 := by
  ext x y
  rcases x with (i | i) | k <;> rcases y with (j | j) | l <;>
    simp [planeIdem, SpBlocks.planeIdem, Matrix.fromBlocks, Matrix.diagonal_apply,
      Matrix.one_apply]

private theorem linTau_mul_one_sub_planeIdem
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ) (ε : Fin 2)
    {S : Finset (Fin t)} {u : PlaneRaw.V t} (hu : ∀ i, i ∉ S → u i = 0) :
    ((tau ζ t ε u : GL (LinIdx t ε) K) : Matrix (LinIdx t ε) (LinIdx t ε) K) *
        (1 - planeIdem t ε S false) = 1 - planeIdem t ε S false := by
  have hzero : ∀ i ∈ Sᶜ, u i = 0 := fun i hi => hu i (by simpa using hi)
  have h := SpBlocks.tau_mul_planeIdem_eq ζ t (v := u) (w := 0) (S := Sᶜ) hzero
  simp only [SpBlocks.coe_tau, SpBlocks.tau_zero, SpBlocks.planeIdem_compl] at h
  rw [linTau_apply_mat, linOneSubPlaneIdem_apply_mat, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [h]

private theorem linTau_mem_levi (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K)
    (t : ℕ) (ε : Fin 2) {S : Finset (Fin t)} {u : PlaneRaw.V t}
    (hu : ∀ i, i ∉ S → u i = 0) :
    tau ζ t ε u ∈ levi (planeIdem t ε S false) := by
  set T : Matrix (LinIdx t ε) (LinIdx t ε) K :=
    ((tau ζ t ε u : GL (LinIdx t ε) K) : Matrix (LinIdx t ε) (LinIdx t ε) K)
  have h1 : T * (1 - planeIdem t ε S false) = 1 - planeIdem t ε S false :=
    linTau_mul_one_sub_planeIdem ζ t ε hu
  have hcomm : T * planeIdem t ε S false =
      planeIdem t ε S false * T := by
    change ((tau ζ t ε u : GL (LinIdx t ε) K) :
        Matrix (LinIdx t ε) (LinIdx t ε) K) * planeIdem t ε S false =
      planeIdem t ε S false * ((tau ζ t ε u : GL (LinIdx t ε) K) :
        Matrix (LinIdx t ε) (LinIdx t ε) K)
    rw [linTau_apply_mat, linPlaneIdem_apply_mat, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero]
    rw [SpBlocks.planeIdem_eq_planeMat, WitSpNs.planeMat_mul, WitSpNs.planeMat_mul,
      Matrix.fromBlocks_inj]
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine congrArg WitSpNs.planeMat ?_
      funext j
      by_cases hj : j ∈ S <;> simp [hj]
    all_goals simp
  refine ⟨h1, ?_⟩
  calc (1 - planeIdem t ε S false) * T
      = T - planeIdem t ε S false * T := by rw [sub_mul, one_mul]
    _ = T - T * planeIdem t ε S false := by rw [hcomm]
    _ = T * (1 - planeIdem t ε S false) := by rw [mul_sub, mul_one]
    _ = 1 - planeIdem t ε S false := h1

private theorem linTau_mul_comm (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K)
    (t : ℕ) (ε : Fin 2) (u v : PlaneRaw.V t) :
    tau ζ t ε u * tau ζ t ε v = tau ζ t ε v * tau ζ t ε u := by
  rw [← tau_add ζ t ε u v, add_comm, tau_add ζ t ε v u]

private theorem exists_zpow_mul_mem_of_relIndex_three {G : Type*} [Group G] {B Y : Subgroup G}
    [hN : (Y.subgroupOf B).Normal] (hindex : Y.relIndex B = 3) {z : G} (hzB : z ∈ B)
    (hzY : z ∉ Y) {g : G} (hgB : g ∈ B) : ∃ k : ℤ, z ^ k * g ∈ Y := by
  classical
  let q : ↥B →* (↥B ⧸ Y.subgroupOf B) := QuotientGroup.mk' _
  have hcard : Nat.card (↥B ⧸ Y.subgroupOf B) = 3 := by
    rw [← Subgroup.index_eq_card]
    exact hindex
  have hne : q ⟨z, hzB⟩ ≠ 1 := by
    intro h1
    have h1' : (⟨z, hzB⟩ : ↥B) ∈ Y.subgroupOf B := by
      rw [← QuotientGroup.eq_one_iff]
      simpa only [q, QuotientGroup.mk'_apply] using h1
    exact hzY (Subgroup.mem_subgroupOf.mp h1')
  have hgen : q ⟨g, hgB⟩ ∈ Subgroup.zpowers (q ⟨z, hzB⟩) := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [zpowers_eq_top_of_prime_card hcard hne]
    exact Subgroup.mem_top _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hgen
  refine ⟨-k, ?_⟩
  have hq : q (⟨z, hzB⟩ ^ (-k) * ⟨g, hgB⟩) = 1 := by
    rw [map_mul, map_zpow, ← hk]
    simp
  have hmem : (⟨z, hzB⟩ ^ (-k) * ⟨g, hgB⟩) ∈ Y.subgroupOf B := by
    rw [← QuotientGroup.eq_one_iff]
    simpa only [q, QuotientGroup.mk'_apply] using hq
  simpa using (Subgroup.mem_subgroupOf.mp hmem)

theorem torusAut_ycode_extension_eq (h : LinTorusAutSubsetSignedPerm) {K : Type} [Field K]
    [Finite K] [CharP K 2] {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} {t : ℕ}
    {ε : Fin 2} (hK : Nat.card K = 2) (hζ : Function.Injective ζ) {e : PlaneRaw.V t}
    (hidx : (Ycode ζ t ε (PlaneRaw.Code.extension e)).relIndex
      (blockGroup ζ t ε (PlaneRaw.Code.extension e)) = 3)
    {i : Fin t} (hi : e i ≠ 0)
    (hz : tau ζ t ε (Pi.single i 1) ∉ Ycode ζ t ε (PlaneRaw.Code.extension e)) :
    torusAut ζ t ε (Ycode ζ t ε (PlaneRaw.Code.extension e)) =
      ((PlaneRaw.twistedPermGroupOn t e : Subgroup _) : Set _) := by
  set B := blockGroup ζ t ε (PlaneRaw.Code.extension e) with hB
  set Y := Ycode ζ t ε (PlaneRaw.Code.extension e) with hY
  set z := tau ζ t ε (Pi.single i 1) with hzdef
  have hYB : Y ≤ B := by
    rw [hY, hB, Ycode]
    exact Subgroup.commutator_le_self _
  have hN : (Y.subgroupOf B).Normal := by
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
  have hzB : z ∈ B := by
    have hmem : i ∈ PlaneRaw.Code.extSupport e := (PlaneRaw.mem_extSupport e i).mpr hi
    have hzlevi : tau ζ t ε (Pi.single i 1) ∈
        levi (planeIdem t ε (PlaneRaw.Code.extSupport e) false) := by
      refine linTau_mem_levi ζ t ε ?_
      intro j hj
      refine Pi.single_eq_of_ne (fun hji => hj ?_) 1
      rw [hji]
      exact hmem
    have hzcent : tau ζ t ε (Pi.single i 1) ∈
        Subgroup.centralizer ({tau ζ t ε e} : Set (GL (LinIdx t ε) K)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact linTau_mul_comm ζ t ε _ _
    rw [hzdef, hB]
    change tau ζ t ε (Pi.single i 1) ∈
      levi (planeIdem t ε (PlaneRaw.Code.extSupport e) false) ⊓
        Subgroup.centralizer ({tau ζ t ε e} : Set (GL (LinIdx t ε) K))
    exact Subgroup.mem_inf.mpr ⟨hzlevi, hzcent⟩
  have hrel : Y.relIndex B = 3 := hidx
  have hzY : z ∉ Y := hz
  apply Set.Subset.antisymm
  · intro φ hφ
    have hφB : φ ∈ torusAut ζ t ε B := torusAut_mono ζ t ε hYB hφ
    have hEq := torusAut_blockGroup_extension_eq (ε := ε) h hK hζ e
    rw [← hB] at hEq
    exact hEq.le hφB
  · intro φ hφ
    have hφB : φ ∈ torusAut ζ t ε B := by
      have hEq := torusAut_blockGroup_extension_eq (ε := ε) h hK hζ e
      rw [← hB] at hEq
      rwa [hEq]
    obtain ⟨g, hgB, hgφ⟩ := hφB
    obtain ⟨k, hk⟩ :=
      exists_zpow_mul_mem_of_relIndex_three (hN := hN) hrel hzB hzY hgB
    refine ⟨z ^ k * g, hk, fun u => ?_⟩
    have hzcomm : ∀ v, z * tau ζ t ε v = tau ζ t ε v * z := by
      intro v
      rw [hzdef]
      exact linTau_mul_comm ζ t ε _ v
    calc (z ^ k * g) * tau ζ t ε u * (z ^ k * g)⁻¹
        = z ^ k * (g * tau ζ t ε u * g⁻¹) * (z ^ k)⁻¹ := by group
      _ = z ^ k * tau ζ t ε (φ u) * (z ^ k)⁻¹ := by rw [hgφ u]
      _ = (tau ζ t ε (φ u) * z ^ k) * (z ^ k)⁻¹ := by
            rw [(Commute.zpow_left (hzcomm (φ u)) k).eq]
      _ = tau ζ t ε (φ u) := by rw [mul_inv_cancel_right]

end CFSG.StandardType.GGQ2Frame.LinBlocks
