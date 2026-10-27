module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVQuasi
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylMatrices
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearNative
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.ClassicalGroups.Symplectic.Simple
public import CFSG.Foundations
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.RankThree.PartTwo.Sec14.Std
public import CFSG.RankThree.PartTwo.Sec4.Item423ResProof432
public import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
public import CFSG.RankThree.PartTwo.Sec4.Item47Diag
public import CFSG.RankThree.PartTwo.Sec4.Item47LThree
public import CFSG.RankThree.PartTwo.Sec4.Item47SpFour
public import CFSG.RankThree.PartTwo.Sec4.Item47Statement
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
public import CFSG.RankThree.PartTwo.Sec4.RonanK429Rows
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Rows
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open Matrix CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.Open
open scoped commutatorElement

namespace RowV

variable {K : Type} [Field K]

local notation "spTorus" => CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.torusHom

@[expose] def spMat (h : StatedSp 3 K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K :=
  ((h : GL (Fin 3 ⊕ Fin 3) K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K)

theorem leviSp_injective' : Function.Injective (leviSp (r := 3) (k := K)) := by
  intro A B h
  apply Units.ext
  ext i j
  have := congrArg (fun g : StatedSp 3 K => spMat g (Sum.inl i) (Sum.inl j)) h
  simpa [spMat, coe_leviSp] using this

theorem spMat_torusHom_const (c : Kˣ) :
    spMat (spTorus (fun _ : Fin 3 => c)) =
      diagonal (Sum.elim (fun _ : Fin 3 => (c : K)) fun _ => ((c⁻¹ : Kˣ) : K)) := by
  rw [spMat, CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.coe_torusHom]

theorem mem_range_leviSp_of_commute {c : Kˣ} (hc : (c : K) ≠ ((c⁻¹ : Kˣ) : K))
    {h : StatedSp 3 K} (hh : h * spTorus (fun _ : Fin 3 => c) =
      spTorus (fun _ : Fin 3 => c) * h) :
    h ∈ (leviSp (r := 3) (k := K)).range := by
  set M := spMat h with hM
  have hcomm : M * diagonal (Sum.elim (fun _ : Fin 3 => (c : K)) fun _ => ((c⁻¹ : Kˣ) : K)) =
      diagonal (Sum.elim (fun _ : Fin 3 => (c : K)) fun _ => ((c⁻¹ : Kˣ) : K)) * M := by
    have h1 := congrArg spMat hh
    simp only [spMat, Subgroup.coe_mul, Units.val_mul] at h1
    rw [← spMat_torusHom_const, hM]
    exact h1
  have hent : ∀ a b, M a b * Sum.elim (fun _ : Fin 3 => (c : K)) (fun _ => ((c⁻¹ : Kˣ) : K)) b =
      Sum.elim (fun _ : Fin 3 => (c : K)) (fun _ => ((c⁻¹ : Kˣ) : K)) a * M a b := by
    intro a b
    have := congrFun (congrFun hcomm a) b
    rwa [mul_diagonal, diagonal_mul] at this
  have h12 : ∀ i j, M (Sum.inl i) (Sum.inr j) = 0 := by
    intro i j
    have := hent (Sum.inl i) (Sum.inr j)
    simp only [Sum.elim_inl, Sum.elim_inr] at this
    have h2 : (((c⁻¹ : Kˣ) : K) - c) * M (Sum.inl i) (Sum.inr j) = 0 := by
      rw [sub_mul]; linear_combination this
    exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr (Ne.symm hc))
  have h21 : ∀ i j, M (Sum.inr i) (Sum.inl j) = 0 := by
    intro i j
    have := hent (Sum.inr i) (Sum.inl j)
    simp only [Sum.elim_inl, Sum.elim_inr] at this
    have h2 : ((c : K) - ((c⁻¹ : Kˣ) : K)) * M (Sum.inr i) (Sum.inl j) = 0 := by
      rw [sub_mul]; linear_combination this
    exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hc)
  set P := M.toBlocks₁₁ with hP
  set Q := M.toBlocks₂₂ with hQ
  have hMblk : M = fromBlocks P 0 0 Q := by
    rw [← fromBlocks_toBlocks M]
    congr 1
    · ext i j; exact h12 i j
    · ext i j; exact h21 i j
  have hsp := (mem_statedSp_iff (g := (h : GL (Fin 3 ⊕ Fin 3) K))).mp h.2
  rw [← spMat, ← hM, hMblk, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply] at hsp
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.transpose_zero,
    Matrix.mul_one, Matrix.one_mul] at hsp
  have hPQ : Pᵀ * Q = 1 := by
    have := congrArg Matrix.toBlocks₁₂ hsp
    simpa using this
  have hdet : P.det ≠ 0 := by
    have h1 := congrArg Matrix.det hPQ
    rw [det_mul, det_transpose, det_one] at h1
    exact left_ne_zero_of_mul_eq_one h1
  let Pu : GL (Fin 3) K := Matrix.GeneralLinearGroup.mkOfDetNeZero P hdet
  refine ⟨Pu, ?_⟩
  apply statedSp_ext
  rw [coe_leviSp]
  change fromBlocks P 0 0 (((Pu⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))ᵀ = spMat h
  rw [← hM, hMblk]
  congr 1
  have hinv : ((Pu⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = P⁻¹ := by
    rw [Matrix.coe_units_inv]
    rfl
  rw [hinv, transpose_nonsing_inv]
  exact Matrix.inv_eq_right_inv hPQ

@[expose] noncomputable def leviSL : Matrix.SpecialLinearGroup (Fin 3) K →* StatedSp 3 K :=
  (leviSp (r := 3) (k := K)).comp Matrix.SpecialLinearGroup.toGL

theorem leviSL_injective : Function.Injective (leviSL (K := K)) := by
  intro A B h
  apply Subtype.ext
  have h1 := leviSp_injective' h
  have h2 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) h1
  exact h2

theorem centQuasi_torusHom_const [Finite K] (hK : Nat.card K = 4) {c : Kˣ} (hc1 : c ≠ 1)
    (hc3 : c ^ 3 = 1) (N₁ : ℕ) : CentQuasi (spTorus (fun _ : Fin 3 => c)) N₁ 60480 := by
  right
  set d := spTorus (fun _ : Fin 3 => c) with hd
  have hcc : (c : K) ≠ ((c⁻¹ : Kˣ) : K) := by
    intro h
    have hcu : c = c⁻¹ := Units.ext h
    apply hc1
    have h2 : c ^ 2 = 1 := by
      calc c ^ 2 = c * c := sq c
        _ = c * c⁻¹ := by rw [← hcu]
        _ = 1 := mul_inv_cancel c
    calc c = c ^ 3 * (c ^ 2)⁻¹ := by group
      _ = 1 := by rw [hc3, h2, inv_one, one_mul]
  have hc3K : (c : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hc3, Units.val_one]
  let cS : Matrix.SpecialLinearGroup (Fin 3) K :=
    ⟨(c : K) • (1 : Matrix (Fin 3) (Fin 3) K), by
      rw [det_smul, det_one, mul_one, Fintype.card_fin, hc3K]⟩
  have hcS : ∀ B : Matrix.SpecialLinearGroup (Fin 3) K, B * cS = cS * B := by
    intro B
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    change (B : Matrix (Fin 3) (Fin 3) K) * ((c : K) • (1 : Matrix (Fin 3) (Fin 3) K)) =
      ((c : K) • (1 : Matrix (Fin 3) (Fin 3) K)) * B
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
  have hdφ : d = leviSL cS := by
    apply statedSp_ext
    rw [hd, CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.coe_torusHom, leviSL,
      MonoidHom.comp_apply, coe_leviSp]
    have hinv : (((Matrix.SpecialLinearGroup.toGL cS)⁻¹ : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = ((c⁻¹ : Kˣ) : K) • (1 : Matrix (Fin 3) (Fin 3) K) := by
      rw [Matrix.coe_units_inv]
      change ((c : K) • (1 : Matrix (Fin 3) (Fin 3) K))⁻¹ = _
      rw [Matrix.inv_smul _ _ (by simp), inv_one]
      simp
    rw [hinv]
    change diagonal _ = fromBlocks ((c : K) • (1 : Matrix (Fin 3) (Fin 3) K)) 0 0
      (((c⁻¹ : Kˣ) : K) • (1 : Matrix (Fin 3) (Fin 3) K))ᵀ
    ext x y
    rcases x with x | x <;> rcases y with y | y <;>
      simp [Matrix.diagonal_apply, Matrix.one_apply]
  refine ⟨(leviSL (K := K)).range, ?_, ?_, ?_, ⟨d, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rintro _ ⟨B, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, hdφ, ← map_mul, ← map_mul, hcS]
  · intro a ha b hb
    have ha' : a * d = d * a := Subgroup.mem_centralizer_singleton_iff.mp ha
    have hb' : b * d = d * b := Subgroup.mem_centralizer_singleton_iff.mp hb
    obtain ⟨A, rfl⟩ := mem_range_leviSp_of_commute hcc ha'
    obtain ⟨B, rfl⟩ := mem_range_leviSp_of_commute hcc hb'
    have hdet : Matrix.GeneralLinearGroup.det ⁅A, B⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, mul_comm]
    have hdetS : ((⁅A, B⁆ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply, hdet, Units.val_one]
    let S : Matrix.SpecialLinearGroup (Fin 3) K :=
      ⟨((⁅A, B⁆ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K), hdetS⟩
    have htoGL : Matrix.SpecialLinearGroup.toGL S = ⁅A, B⁆ := Units.ext rfl
    refine ⟨S, ?_⟩
    show leviSp (Matrix.SpecialLinearGroup.toGL S) = _
    rw [htoGL, map_commutatorElement]
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (MonoidHom.ofInjective leviSL_injective)
      (CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple 3 K
        (by norm_num) (Or.inl (by norm_num)) (Or.inl (by norm_num)))
  · exact ⟨cS, hdφ.symm⟩
  · intro h1
    have h2 := congrArg (fun g : StatedSp 3 K => spMat g (Sum.inl 0) (Sum.inl 0)) h1
    simp only [hd, spMat_torusHom_const, diagonal_apply_eq, Sum.elim_inl] at h2
    exact hc1 (Units.ext (by simpa [spMat] using h2))
  · rw [hd, ← map_pow, show (fun _ : Fin 3 => c) ^ 3 = 1 from funext fun _ => by simp [hc3],
      map_one]
  · rintro _ ⟨B, rfl⟩
    rw [hdφ, ← map_mul, ← map_mul, hcS]
  · rw [Nat.card_congr (MonoidHom.ofInjective leviSL_injective).toEquiv.symm,
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (K := K) (n := 3) (by norm_num),
      hK]
    decide

theorem spTorus_eq_prod (a : Fin 3 → Kˣ) :
    spTorus a = lam 0 (sl2Diag (a 0)) * lam 1 (sl2Diag (a 1)) * lam 2 (sl2Diag (a 2)) := by
  rw [lam_sl2Diag, lam_sl2Diag, lam_sl2Diag, ← map_mul, ← map_mul]
  congr 1
  funext j
  fin_cases j <;> simp [Pi.mulSingle_apply]

theorem conj_lam_lam (i j : Fin 3) (g : Matrix.SpecialLinearGroup (Fin 2) K) :
    lam i sl2W * lam j g * (lam i sl2W)⁻¹ =
      if j = i then lam i (sl2W * g * sl2W⁻¹) else lam j g := by
  split_ifs with hji
  · subst hji
    rw [map_mul, map_mul, map_inv]
  · rw [((commute_lam_lam (Ne.symm hji) sl2W g)).eq, mul_inv_cancel_right]

theorem flip_conj_torusHom (i : Fin 3) (a : Fin 3 → Kˣ) :
    lam i sl2W * spTorus a * (lam i sl2W)⁻¹ = spTorus (Function.update a i (a i)⁻¹) := by
  have hw : ∀ x : Kˣ, (sl2W : Matrix.SpecialLinearGroup (Fin 2) K) * sl2Diag x * sl2W⁻¹ =
      sl2Diag x⁻¹ := fun x => by rw [sl2W_mul_sl2Diag, mul_assoc, mul_inv_cancel, mul_one]
  have hconj : ∀ x y z : StatedSp 3 K,
      lam i sl2W * (x * y * z) * (lam i sl2W)⁻¹ =
        (lam i sl2W * x * (lam i sl2W)⁻¹) * (lam i sl2W * y * (lam i sl2W)⁻¹) *
          (lam i sl2W * z * (lam i sl2W)⁻¹) := fun x y z => by group
  rw [spTorus_eq_prod, spTorus_eq_prod, hconj, conj_lam_lam, conj_lam_lam, conj_lam_lam]
  fin_cases i <;> simp [hw, Function.update_apply]

end RowV

end CFSG.RankThree.PartTwo.Sec4.RonanK429
