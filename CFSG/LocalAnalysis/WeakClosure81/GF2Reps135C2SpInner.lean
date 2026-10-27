module

import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpSL2
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpInvol
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinL28
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8CuUnique
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallSp6B3Modules
import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.TopRank
import CFSG.Blueprint.LieModelAPI
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Symplectic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsC
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135Ctx

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.Sp6B3
open CFSG.Blueprint (LieModel)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open scoped MatrixGroups

private theorem permMatrix_injective {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] :
    Function.Injective (fun σ : Equiv.Perm ι => Equiv.Perm.permMatrix K σ) := by
  intro σ τ h
  ext i
  have h' := congrFun (congrFun h i) (σ i)
  simp only [PEquiv.toMatrix_toPEquiv_apply] at h'
  rw [Pi.single_eq_same] at h'
  by_contra hne
  rw [Pi.single_eq_of_ne hne] at h'
  exact one_ne_zero h'

private theorem inv_swap {n : ℕ} {σ : Equiv.Perm (Fin n ⊕ Fin n)}
    (h : ∀ x, σ x.swap = (σ x).swap) : ∀ x, σ.symm x.swap = (σ.symm x).swap := by
  intro x
  apply σ.injective
  rw [h (σ.symm x), Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem w135c2_center_eq_bot_of_lieModel_psp
    {W : Type} [CommGroup W] [Finite W] {Y L : Subgroup (MulAut W)} (hctx : Is135Context Y L)
    {n f : ℕ} (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .PSp n 2 f) :
    Subgroup.center ↥L = ⊥ := by
  obtain ⟨-, F, instF, instFin, hF, ⟨eZ⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel hlie (by decide)
  exact letI : Field F := instF;
        letI : Finite F := instFin;
        letI : Fintype F := Fintype.ofFinite F;
        letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩;
        letI : CharP F 2 :=
          charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hF);
        letI : Group.IsPerfect ↥L := hctx.2.2.2.2.1.1;
        CFSG.SectionRank.EvenCover.center_eq_bot_of_even_symplectic (n := n) (K := F)
          (hodd := w135_odd_card_center hctx) eZ

theorem w135c2_nonempty_equiv_statedSp_of_lieModel_psp {X : Type} [Group X] {n f : ℕ}
    (hX : LieModel X .PSp n 2 f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F),
      Nat.card F = 2 ^ f ∧ Nonempty (StatedSp n F ≃* X) := by
  obtain ⟨-, F, instF, instFin, hF, ⟨e⟩⟩ := LieModel.statedClassicalModel hX (by decide)
  refine ⟨F, instF, instFin, hF, ?_⟩
  let hField : Field F := instF
  let hFinite : Finite F := instFin
  let hFintype : Fintype F := Fintype.ofFinite F
  let hFact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let hCharP : CharP F 2 :=
    charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hF)
  let eProj : StatedSp n F ≃* StatedProj (StatedSp n F) :=
    ((QuotientGroup.quotientMulEquivOfEq
      (CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot (n := n) (K := F))).trans
        QuotientGroup.quotientBot).symm
  exact ⟨(e.trans eProj.symm).symm⟩

private theorem exists_sl2Hom_conj {K : Type} [Field K] [CharP K 2] {n : ℕ}
    {g y : StatedSp n K} {π : Equiv.Perm (Fin n)} {s : Fin n → ℤ} (hy : y * y = 1)
    (hmat : mat n K (g * y * g⁻¹) = Equiv.Perm.permMatrix K (spMonoPerm π s).symm) :
    ∃ (φ : SL(2, K) →* StatedSp n K) (t : SL(2, K)), t ≠ 1 ∧ t * t = 1 ∧ φ t = g * y * g⁻¹ := by
  set σ : Equiv.Perm (Fin n ⊕ Fin n) := (spMonoPerm π s).symm with hσdef
  have hmat' : mat n K (g * y * g⁻¹) = Equiv.Perm.permMatrix K σ := by
    rw [hσdef]; exact hmat
  have hconj2 : (g * y * g⁻¹) * (g * y * g⁻¹) = 1 := by
    rw [show (g * y * g⁻¹) * (g * y * g⁻¹) = g * (y * y) * g⁻¹ by group, hy, mul_one,
      mul_inv_cancel]
  have hsq : Equiv.Perm.permMatrix K σ * Equiv.Perm.permMatrix K σ = 1 := by
    rw [← hmat', ← map_mul, hconj2, map_one]
  have hσ2 : σ * σ = 1 := permMatrix_injective (by
    change Equiv.Perm.permMatrix K (σ * σ) = Equiv.Perm.permMatrix K 1
    rw [Matrix.permMatrix_mul, hsq, Matrix.permMatrix_one])
  have hτ : ∀ x, σ x.swap = (σ x).swap := inv_swap (spMonoPerm_swap π s)
  obtain ⟨φ, t, ht1, htt, hφt⟩ := exists_sl2Hom_mat_eq_permMatrix (K := K) σ hσ2 hτ
  exact ⟨φ, t, ht1, htt, mat_injective (hφt.trans hmat'.symm)⟩

private theorem le_finrank_range_sub_one_of_statedSp_of_two_le {K : Type} [Field K] [Finite K]
    [CharP K 2] {n f : ℕ} (hn : 2 ≤ n) (hf2 : 2 ≤ f) (hK : Nat.card K = 2 ^ f) {V : Type}
    [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
    (ρ : Representation (ZMod 2) (StatedSp n K) V) {y : StatedSp n K} (hy : y * y = 1)
    (hρy : ρ y ≠ 1) : f ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ y - 1)) := by
  have hy1 : y ≠ 1 := by
    intro h1
    exact hρy (by rw [h1, map_one])
  obtain ⟨g, π, s, hs, -, hmat⟩ := exists_conj_mat_eq_spMonoPerm (K := K) hn hy hy1
  obtain ⟨φ, t, ht1, htt, hφt⟩ := exists_sl2Hom_conj hy hmat
  have hρ't : (ρ.comp φ) t ≠ 1 := by
    intro h1
    apply hρy
    have h1' : ρ (g * y * g⁻¹) = 1 := by
      have h2 := h1
      rwa [MonoidHom.comp_apply, hφt] at h2
    calc ρ y = ρ (g⁻¹ * (g * y * g⁻¹) * g) := by congr 1; group
      _ = ρ (g⁻¹) * ρ (g * y * g⁻¹) * ρ g := by rw [map_mul, map_mul]
      _ = 1 := by rw [h1', mul_one, ← map_mul, inv_mul_cancel, map_one]
  let hFintypeK : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 2 ^ f := by
    rw [← Nat.card_eq_fintype_card]; exact hK
  have h4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  have hperf : Group.IsPerfect SL(2, K) :=
    CFSG.ClassicalInvolution.sl2_isPerfect (by rw [hK]; exact h4)
  have hB := le_finrank_range_sub_one_of_sl2 (F := K) (n := f) (W := V)
    (by omega) hcard hperf (ρ.comp φ) ⟨t, hρ't⟩ ht1 htt
  have heq : Module.finrank (ZMod 2) (LinearMap.range ((ρ.comp φ) t - 1)) =
      Module.finrank (ZMod 2) (LinearMap.range (ρ y - 1)) := by
    rw [MonoidHom.comp_apply, hφt]
    exact CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.finrank_range_rep_conj_sub_one ρ g y
  rwa [heq] at hB

theorem le_finrank_range_sub_one_of_statedSp {K : Type} [Field K] [Finite K] [CharP K 2]
    {n f : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ f) {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
    (ρ : Representation (ZMod 2) (StatedSp n K) V) {y : StatedSp n K} (hy : y * y = 1)
    (hρy : ρ y ≠ 1) : f ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ y - 1)) := by
  have hf1 : 1 ≤ f := by
    by_contra h
    have hf0 : f = 0 := by omega
    rw [hf0, pow_zero] at hK
    have := Finite.one_lt_card (α := K)
    omega
  by_cases hf : f = 1
  · subst hf
    have hne : ρ y - 1 ≠ 0 := sub_ne_zero.mpr hρy
    have hfin_ne : Module.finrank (ZMod 2) (LinearMap.range (ρ y - 1)) ≠ 0 := by
      intro h
      rw [Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h
      exact hne h
    omega
  · exact le_finrank_range_sub_one_of_statedSp_of_two_le hn (by omega) hK ρ hy hρy

theorem w135c2_sp_inner_le_mQuot
    {W : Type} [CommGroup W] [Finite W] {Y L : Subgroup (MulAut W)}
    {t : MulAut W} (hW : ∀ w : W, w ^ 2 = 1) (hctx : Is135Context Y L) (htL : t ∈ L)
    (ht2 : orderOf t = 2) {n f : ℕ} (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .PSp n 2 f) :
    f ≤ E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) := by
  have hZ : Subgroup.center ↥L = ⊥ := w135c2_center_eq_bot_of_lieModel_psp hctx hlie
  have hL' : LieModel ↥L .PSp n 2 f := LieModel.of_quotient_center hZ hlie
  obtain ⟨F, instF, instFin, hF, ⟨e⟩⟩ := w135c2_nonempty_equiv_statedSp_of_lieModel_psp hL'
  let hField : Field F := instF
  let hFinite : Finite F := instFin
  let hFintype : Fintype F := Fintype.ofFinite F
  let hFact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let hCharP : CharP F 2 :=
    charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hF)
  have hn : 2 ≤ n := (LieModel.admissible hlie).2.2.1
  have hirr : IsIrrOn L ⊤ ⊥ := hctx.2.2.2.2.2
  obtain ⟨V, _, _, _, ρ, θ, _, hθ⟩ := cu_binModel hW hirr e
  have hFinV : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  let y : StatedSp n F := e.symm ⟨t, htL⟩
  have hey : e y = ⟨t, htL⟩ := e.apply_symm_apply _
  have hge : ((e y : ↥L) : MulAut W) = t := by rw [hey]
  have htt : t * t = 1 := by
    have h1 := pow_orderOf_eq_one t
    rwa [ht2, pow_two] at h1
  have hy2 : y * y = 1 := by
    apply e.injective
    rw [map_mul, map_one, hey]
    exact Subtype.ext htt
  have hρy : ρ y ≠ 1 := rho_ne_one_of_conj e hθ hge ht2
  have hB : f ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ y - 1)) :=
    le_finrank_range_sub_one_of_statedSp hn hF ρ hy2 hρy
  have heq := finL28_two_pow_mQuot_eq_card_range θ t (ρ y) (fun w => by
    rw [← hge]
    exact hθ y w)
  have hcardR : Nat.card (LinearMap.range (ρ y - 1)) =
      2 ^ Module.finrank (ZMod 2) (LinearMap.range (ρ y - 1)) := by
    refine letI : Module.Finite (ZMod 2) (LinearMap.range (ρ y - 1)) :=
      Module.Finite.of_finite;
      ?_
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  rw [hcardR] at heq
  have hm := Nat.pow_right_injective (le_refl 2) heq
  rw [hm]
  exact hB

end CFSG.LocalAnalysis.WeakClosure81
