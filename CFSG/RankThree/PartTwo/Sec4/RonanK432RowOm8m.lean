module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Rows
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Wreath
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Sylow
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434OmegaMinus
import CFSG.LocalAnalysis.EvenSmallLie.OmegaEightMinus.NativeMain

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.Item434Kit
open CFSG.RankThree.PartTwo.Sec4.Item434OmegaMinus
open CFSG.EvenSmallLie.OmegaEightMinus
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Assembly.RankThreeEven (projOmegaMinus)

@[expose] noncomputable def om8mFlipM :
    omegaT :=
  sT 0 * zT 0 ^ 2 * sT 0 ^ 4 * zT 0 * sT 0

theorem sT_commute {k i : Fin 3}
    (hik : i ≠ k) : Commute (sT k) (zT i) := by
  show sT k * zT i = zT i * sT k
  exact Subtype.ext (sPerm_spec.2 k i hik)

theorem flipM_commute {i : Fin 3}
    (hi : i ≠ 0) : Commute om8mFlipM (zT i) := by
  have h1 : Commute (sT 0) (zT i) := sT_commute hi
  have h2 : Commute (zT 0) (zT i) := wreathFacts_omegaT.comm_z 0 i
  exact ((((h1.mul_left (h2.pow_left 2)).mul_left (h1.pow_left 4)).mul_left h2).mul_left h1)

theorem eqA_of_range_all {t u : Array ℕ}
    (h : (List.range 136).all (fun i => t[i]! == u[i]!) = true) : eqA 136 t u = true := by
  unfold eqA
  rw [allLt_iff]
  intro i hi
  exact List.all_eq_true.mp h i (List.mem_range.mpr hi)

theorem eq_of_range_all {t u : Array ℕ} {g h : Equiv.Perm (Fin 136)} (ht : Rep 136 t g)
    (hu : Rep 136 u h) (hlist : (List.range 136).all (fun i => t[i]! == u[i]!) = true) :
    g = h :=
  eq_of_eqA ht hu (eqA_of_range_all hlist)

theorem flip_list_check : (List.range 136).all (fun i =>
    (compA 136 (compA 136 (compA 136 (compA 136 (compA 136 sArrs[0]! (powArr (zArr 0) 2))
      (powArr sArrs[0]! 4)) (zArr 0)) sArrs[0]!) (zArr 0))[i]! ==
    (compA 136 (powArr (zArr 0) 2) (compA 136 (compA 136 (compA 136 (compA 136
      sArrs[0]! (powArr (zArr 0) 2)) (powArr sArrs[0]! 4)) (zArr 0)) sArrs[0]!))[i]!) = true := by
  decide +kernel

theorem flipPerm_mul_z0 :
    sPerm 0 * zPerm 0 ^ 2 * sPerm 0 ^ 4 * zPerm 0 * sPerm 0 * zPerm 0 =
      zPerm 0 ^ 2 * (sPerm 0 * zPerm 0 ^ 2 * sPerm 0 ^ 4 * zPerm 0 * sPerm 0) := by
  have hz : Rep 136 (zArr 0) (zPerm 0) := rep_zPerm 0
  have hz2 := rep_powArr hz 2
  have hs : Rep 136 sArrs[0]! (sPerm 0) := rep_sPerm 0
  have hs4 := rep_powArr hs 4
  exact eq_of_range_all
    (rep_compA (rep_compA (rep_compA (rep_compA (rep_compA hs hz2) hs4) hz) hs) hz)
    (rep_compA hz2 (rep_compA (rep_compA (rep_compA (rep_compA hs hz2) hs4) hz) hs))
    flip_list_check

theorem flipM_mul_z0 :
    om8mFlipM * zT 0 = zT 0 ^ 2 * om8mFlipM :=
  Subtype.ext flipPerm_mul_z0

theorem zT_sq_eq_inv :
    zT 0 ^ 2 = (zT 0)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact wreathFacts_omegaT.pow_z 0)

theorem flipM_conj0 :
    om8mFlipM * zT 0 * om8mFlipM⁻¹ = (zT 0)⁻¹ := by
  rw [flipM_mul_z0, mul_assoc, mul_inv_cancel, mul_one, zT_sq_eq_inv]

theorem flipM_conj1 :
    om8mFlipM * zT 1 * om8mFlipM⁻¹ = zT 1 := by
  rw [(flipM_commute (by decide : (1 : Fin 3) ≠ 0)).eq]
  group

theorem flipM_conj2 :
    om8mFlipM * zT 2 * om8mFlipM⁻¹ = zT 2 := by
  rw [(flipM_commute (by decide : (2 : Fin 3) ≠ 0)).eq]
  group

theorem om8m_conj_vecElt_const {H : Type} [Group H] {z : Fin 3 → H} {t m : H}
    (hf : WreathFacts z t)
    (h0 : m * z 0 * m⁻¹ = (z 0)⁻¹) (h1 : m * z 1 * m⁻¹ = z 1) (h2 : m * z 2 * m⁻¹ = z 2) :
    m * vecElt z ![1, 1, 1] * m⁻¹ = vecElt z ![2, 1, 1] := by
  have hz2 : z 0 ^ 2 = (z 0)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hf.pow_z 0)
  have e1 : vecElt z ![1, 1, 1] = z 0 * z 1 * z 2 := by
    have hs : (![1, 1, 1] : Fin 3 → ZMod 3) = Pi.single 0 1 + Pi.single 1 1 + Pi.single 2 1 := by
      decide
    rw [hs, vecElt_add hf, vecElt_add hf, vecElt_single_one, vecElt_single_one,
      vecElt_single_one]
  have e2 : vecElt z ![2, 1, 1] = (z 0)⁻¹ * z 1 * z 2 := by
    have hs : (![2, 1, 1] : Fin 3 → ZMod 3) = Pi.single 0 2 + Pi.single 1 1 + Pi.single 2 1 := by
      decide
    have hv2 : (2 : ZMod 3).val = 2 := rfl
    rw [hs, vecElt_add hf, vecElt_add hf, vecElt_single, hv2, vecElt_single_one,
      vecElt_single_one, hz2]
  rw [e1, e2,
    show m * (z 0 * z 1 * z 2) * m⁻¹ = (m * z 0 * m⁻¹) * (m * z 1 * m⁻¹) * (m * z 2 * m⁻¹) by
      group,
    h0, h1, h2]

theorem om8m_flip_facts {H : Type} [Group H] {z : Fin 3 → H} {t m : H} (hf : WreathFacts z t)
    (h0 : m * z 0 * m⁻¹ = (z 0)⁻¹) (h1 : m * z 1 * m⁻¹ = z 1) (h2 : m * z 2 * m⁻¹ = z 2) :
    m * vecElt z ![1, 1, 1] * m⁻¹ ∈ baseA z ∧
      m * vecElt z ![1, 1, 1] * m⁻¹ ∉ Subgroup.zpowers (vecElt z ![1, 1, 1]) := by
  rw [om8m_conj_vecElt_const hf h0 h1 h2]
  have hc3 : vecElt z ![1, 1, 1] ^ 3 = 1 :=
    (isElemAbelian_baseA hf).2 _ (vecElt_mem_baseA hf _)
  refine ⟨vecElt_mem_baseA hf _, fun hmem => ?_⟩
  rcases mem_zpowers_cases_of_pow_three hc3 hmem with h | h | h
  · exact absurd (congrFun (hf.inj _ h) 1) (by decide)
  · exact absurd (congrFun (vecElt_injective hf h) 0) (by decide)
  · have hsum : vecElt z (![2, 1, 1] + ![1, 1, 1]) = 1 := by
      rw [vecElt_add hf, h, inv_mul_cancel]
    exact absurd (congrFun (hf.inj _ hsum) 1) (by decide)

theorem om8mFlipM_facts :
    om8mFlipM * vecElt zT ![1, 1, 1] * om8mFlipM⁻¹ ∈ baseA zT ∧
      om8mFlipM * vecElt zT ![1, 1, 1] * om8mFlipM⁻¹ ∉ Subgroup.zpowers (vecElt zT ![1, 1, 1]) :=
  om8m_flip_facts wreathFacts_omegaT flipM_conj0 flipM_conj1 flipM_conj2

theorem listRow_omegaT :
    ListRow omegaT :=
  listRow_of_wreath3 wreathFacts_omegaT card_wreathW_omegaT
    (by rw [card_omegaT]; norm_num) ⟨om8mFlipM, om8mFlipM_facts⟩

theorem outerRow_omegaT : OuterRow omegaT :=
  outerRow_of_not_three_dvd_outer (by rw [card_outer_omegaT]; norm_num)

theorem row_omegaMinus :
    ∀ b c : GaloisField 2 1, (∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) →
      RowOf (projOmegaMinus 3 (GaloisField 2 1) b c) := by
  intro b c hbc S _ _ _ _ ⟨e⟩
  obtain ⟨θ⟩ := nonempty_mulEquiv_omegaT (X := S)
    (Or.inl ⟨by decide, statedClassicalModel_of_mulEquiv hbc e⟩)
  exact GoodRow.of_mulEquiv θ.symm ⟨listRow_omegaT, outerRow_omegaT⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK432
