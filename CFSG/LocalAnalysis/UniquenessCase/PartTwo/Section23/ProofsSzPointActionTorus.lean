module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsSzPointActionModel

public noncomputable section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.GroupTheory
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.MatrixGroups
open SzPointModel
open scoped Pointwise

attribute [local instance]
  CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator.suzukiOvoidAction

private theorem inf_sylow_eq_bot (m : ℕ) (hm : 0 < m) {U V : Sylow 2 (G m)}
    (hUV : U ≠ V) : (U : Subgroup (G m)) ⊓ (V : Subgroup (G m)) = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro x hx
  have hfix : (⟨x, hx.1⟩ : U) • V = V :=
    (Sylow.smul_eq_iff_mem_normalizer).mpr (Subgroup.le_normalizer hx.2)
  obtain ⟨u, hu, huniq⟩ := regular_sylow m hm U V V hUV.symm hUV.symm
  have hx1 : (⟨x, hx.1⟩ : U) = 1 := by
    calc (⟨x, hx.1⟩ : U) = u := huniq ⟨x, hx.1⟩ hfix
      _ = 1 := (huniq 1 (by simp)).symm
  simpa using congrArg Subtype.val hx1

private theorem eq_of_smul_eq_of_ne (m : ℕ) (hm : 0 < m) {U V W : Sylow 2 (G m)}
    {h : G m} (hh1 : h ≠ 1) (hUV : U ≠ V) (hU : h • U = U) (hV : h • V = V)
    (hW : h • W = W) (hWU : W ≠ U) (hWV : W ≠ V) : False := by
  classical
  let f : Fin 3 → {P : Sylow 2 (G m) // h • P = P} :=
    fun i => ![⟨U, hU⟩, ⟨V, hV⟩, ⟨W, hW⟩] i
  have hinj : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f]
  have h2 : 2 < Nat.card {P : Sylow 2 (G m) // h • P = P} := by
    letI : Fintype (Sylow 2 (G m)) := Fintype.ofFinite _
    have h3 : 3 ≤ Fintype.card {P : Sylow 2 (G m) // h • P = P} := by
      simpa using Fintype.card_le_of_injective f hinj
    rw [Nat.card_eq_fintype_card]
    omega
  have hle := fixes_le_two_model m hm h hh1
  omega

private theorem inf_normalizer_inf_sylow_eq_bot (m : ℕ) (hm : 0 < m) {U V : Sylow 2 (G m)}
    (hUV : U ≠ V) :
    (Subgroup.normalizer ((U : Subgroup (G m)) : Set (G m)) ⊓
      Subgroup.normalizer ((V : Subgroup (G m)) : Set (G m))) ⊓
      (U : Subgroup (G m)) = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro x hx
  have hxN : x ∈ Subgroup.normalizer ((V : Subgroup (G m)) : Set (G m)) := hx.1.2
  have hxUV : x ∈ (U : Subgroup (G m)) ⊓ (V : Subgroup (G m)) := by
    rw [← IsPGroup.inf_normalizer_sylow (p := 2) (P := (U : Subgroup (G m)))
      U.isPGroup' V]
    exact ⟨hx.2, hxN⟩
  rw [inf_sylow_eq_bot m hm hUV] at hxUV
  exact hxUV

private theorem isCyclic_of_disjoint_root_normalizer (m : ℕ) (hm : 0 < m)
    {D' : Subgroup (G m)}
    (hle : D' ≤ Subgroup.normalizer ((suzukiCoverRoot m : Subgroup (G m)) : Set (G m)))
    (hdisj : D' ⊓ suzukiCoverRoot m = ⊥) : IsCyclic ↥D' := by
  let NR := Subgroup.normalizer ((suzukiCoverRoot m : Subgroup (G m)) : Set (G m))
  haveI : IsCyclic (↥NR ⧸ (suzukiCoverRoot m).subgroupOf NR) :=
    isCyclic_normalizer_root_quotient m hm
  let φ : ↥D' →* (↥NR ⧸ (suzukiCoverRoot m).subgroupOf NR) :=
    (QuotientGroup.mk' ((suzukiCoverRoot m).subgroupOf NR)).comp (Subgroup.inclusion hle)
  have hφ : Function.Injective φ := by
    intro a b hab
    have hmem : ((a : G m)⁻¹ * (b : G m)) ∈ suzukiCoverRoot m := by
      have h := (QuotientGroup.eq).1 hab
      rw [Subgroup.mem_subgroupOf] at h
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion] using h
    have hD'mem : ((a : G m)⁻¹ * (b : G m)) ∈ D' := D'.mul_mem (D'.inv_mem a.2) b.2
    have hbot : ((a : G m)⁻¹ * (b : G m)) = 1 := by
      have hx : ((a : G m)⁻¹ * (b : G m)) ∈ D' ⊓ suzukiCoverRoot m := ⟨hD'mem, hmem⟩
      rw [hdisj] at hx
      exact Subgroup.mem_bot.mp hx
    exact Subtype.ext (inv_mul_eq_one.mp hbot)
  exact isCyclic_of_injective φ hφ

private theorem inf_normalizer_isCyclic (m : ℕ) (hm : 0 < m) {U V : Sylow 2 (G m)}
    (hUV : U ≠ V) :
    IsCyclic ↥(Subgroup.normalizer ((U : Subgroup (G m)) : Set (G m)) ⊓
      Subgroup.normalizer ((V : Subgroup (G m)) : Set (G m))) := by
  classical
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (G m) (suzukiCoverSylow m hm) U
  let R := suzukiCoverRoot m
  let NR := Subgroup.normalizer ((R : Subgroup (G m)) : Set (G m))
  let D := Subgroup.normalizer ((U : Subgroup (G m)) : Set (G m)) ⊓
    Subgroup.normalizer ((V : Subgroup (G m)) : Set (G m))
  have hDdef : D = Subgroup.normalizer ((U : Subgroup (G m)) : Set (G m)) ⊓
      Subgroup.normalizer ((V : Subgroup (G m)) : Set (G m)) := rfl
  have hcomp : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id (G m) := by
    ext y
    simp [MulAut.conj_apply, mul_assoc]
  have hUmap : (U : Subgroup (G m)).map (MulAut.conj g⁻¹).toMonoidHom = R := by
    rw [coe_eq_map_root_conj m hm hg, Subgroup.map_map, hcomp, Subgroup.map_id]
  have hDle : Subgroup.normalizer ((U : Subgroup (G m)) : Set (G m)) ⊓
      Subgroup.normalizer ((V : Subgroup (G m)) : Set (G m)) ≤
      NR.map (MulAut.conj g).toMonoidHom := by
    rw [normalizer_eq_map_root_conj m hm hg]
    exact inf_le_left
  have hDmap_le : D.map (MulAut.conj g⁻¹).toMonoidHom ≤ NR := by
    calc D.map (MulAut.conj g⁻¹).toMonoidHom
        ≤ (NR.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom :=
          Subgroup.map_mono hDle
      _ = NR := by rw [Subgroup.map_map, hcomp, Subgroup.map_id]
  have hDU : D ⊓ (U : Subgroup (G m)) = ⊥ := by
    rw [hDdef]
    exact inf_normalizer_inf_sylow_eq_bot m hm hUV
  have hdisj : D.map (MulAut.conj g⁻¹).toMonoidHom ⊓ R = ⊥ := by
    have hmapinf : D.map (MulAut.conj g⁻¹).toMonoidHom ⊓ R =
        (D ⊓ (U : Subgroup (G m))).map (MulAut.conj g⁻¹).toMonoidHom := by
      rw [← hUmap, ← Subgroup.map_inf D (U : Subgroup (G m))
        (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective]
    rw [hmapinf, hDU, Subgroup.map_bot]
  have hD'le : D.map (MulAut.conj g⁻¹).toMonoidHom ≤
      Subgroup.normalizer ((suzukiCoverRoot m : Subgroup (G m)) : Set (G m)) := hDmap_le
  exact ((MulAut.conj g⁻¹).subgroupMap D).isCyclic.mpr
    (isCyclic_of_disjoint_root_normalizer m hm hD'le hdisj)

private theorem inf_normalizer_free (m : ℕ) (hm : 0 < m) {U V : Sylow 2 (G m)}
    (hUV : U ≠ V) {h : G m}
    (hhN : h ∈ Subgroup.normalizer ((U : Subgroup (G m)) : Set (G m)) ⊓
      Subgroup.normalizer ((V : Subgroup (G m)) : Set (G m))) (hh1 : h ≠ 1) (u : U)
    (hu : h * (u : G m) * h⁻¹ = (u : G m)) : u = 1 := by
  have hfixU : h • U = U := (Sylow.smul_eq_iff_mem_normalizer).mpr hhN.1
  have hfixV : h • V = V := (Sylow.smul_eq_iff_mem_normalizer).mpr hhN.2
  have hcomm : h * (u : G m) = (u : G m) * h := by
    have h := congrArg (· * h) hu
    simpa [mul_assoc] using h
  have huVfix : h • ((u : G m) • V) = (u : G m) • V := by
    calc h • ((u : G m) • V) = (h * (u : G m)) • V := (mul_smul h (u : G m) V).symm
      _ = ((u : G m) * h) • V := by rw [hcomm]
      _ = (u : G m) • (h • V) := mul_smul (u : G m) h V
      _ = (u : G m) • V := by rw [hfixV]
  have huVne : (u : G m) • V ≠ U := by
    intro hEq
    have hinv : ((u : G m))⁻¹ ∈ Subgroup.normalizer ((U : Subgroup (G m)) : Set (G m)) :=
      (Subgroup.normalizer ((U : Subgroup (G m)) : Set (G m))).inv_mem
        (Subgroup.le_normalizer u.2)
    have hfixU' : ((u : G m))⁻¹ • U = U := (Sylow.smul_eq_iff_mem_normalizer).mpr hinv
    have h := congrArg (fun X : Sylow 2 (G m) => ((u : G m))⁻¹ • X) hEq
    rw [← mul_smul, inv_mul_cancel, one_smul, hfixU'] at h
    exact hUV h.symm
  have huVeq : (u : G m) • V = V := by
    by_contra hne
    exact eq_of_smul_eq_of_ne m hm hh1 hUV hfixU hfixV huVfix huVne hne
  obtain ⟨u₀, -, huniq⟩ := regular_sylow m hm U V V hUV.symm hUV.symm
  exact (huniq u huVeq).trans (huniq 1 (by simp)).symm

private theorem card_frattini (m : ℕ) (hm : 0 < m) (U : Sylow 2 (G m)) :
    Nat.card (↥U ⧸ frattini ↥U) = q m := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (G m) (suzukiCoverSylow m hm) U
  have hmap : (suzukiCoverRoot m).map (MulAut.conj g).toMonoidHom = (U : Subgroup (G m)) := by
    rw [← suzukiCoverSylow_coe m hm]
    change (g • suzukiCoverSylow m hm : Sylow 2 (G m)).toSubgroup = U.toSubgroup
    rw [hg]
  let e : suzukiCoverRoot m ≃* ↥U :=
    (Subgroup.equivMapOfInjective (suzukiCoverRoot m) (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr hmap)
  have hfr : (frattini ↥(suzukiCoverRoot m)).map e.toMonoidHom = frattini ↥U :=
    CFSG.RankThree.PartOne.Torsion37.frattini_map_mulEquiv e
  have hidx : (frattini ↥U).index = (frattini ↥(suzukiCoverRoot m)).index := by
    rw [← hfr]
    exact Subgroup.index_map_equiv (H := frattini ↥(suzukiCoverRoot m)) e
  have hroot : Nat.card (↥(suzukiCoverRoot m) ⧸ frattini ↥(suzukiCoverRoot m)) = q m := by
    rw [frattini_root m hm]
    calc Nat.card (↥(suzukiCoverRoot m) ⧸ Subgroup.center ↥(suzukiCoverRoot m))
        = (Subgroup.center ↥(suzukiCoverRoot m)).index := Subgroup.index_eq_card _
      _ = Nat.card ↥(suzukiCoverRoot m) /
            Nat.card (Subgroup.center ↥(suzukiCoverRoot m)) :=
          Subgroup.index_eq_card_div (H := Subgroup.center ↥(suzukiCoverRoot m))
      _ = q m ^ 2 / q m := by rw [card_root m hm, card_center_root m hm]
      _ = q m := by rw [pow_two, Nat.mul_div_cancel_left _ (by positivity)]
  calc Nat.card (↥U ⧸ frattini ↥U) = (frattini ↥U).index := (Subgroup.index_eq_card _).symm
    _ = (frattini ↥(suzukiCoverRoot m)).index := hidx
    _ = Nat.card (↥(suzukiCoverRoot m) ⧸ frattini ↥(suzukiCoverRoot m)) :=
        Subgroup.index_eq_card _
    _ = q m := hroot

private theorem faithful_model (m : ℕ) (hm : 0 < m) :
    FaithfulSMul (G m) (Sylow 2 (G m)) := by
  refine faithfulSMul_iff.mpr ?_
  intro x hx
  have hfix : ∀ p : SzOvoid m, x • p = p := by
    intro p
    obtain ⟨U, rfl⟩ := sylowPoint_surjective m hm p
    rw [← sylowPoint_smul m hm x U, hx U]
  by_contra hx1
  letI : Fintype (SzOvoid m) := Fintype.ofFinite _
  have h3 : 2 < Fintype.card (SzOvoid m) := by
    have hq : 2 ≤ 2 ^ (2 * m + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4 : 4 ≤ (2 ^ (2 * m + 1)) ^ 2 := by
      rw [pow_two]
      calc 4 = 2 * 2 := by norm_num
        _ ≤ 2 ^ (2 * m + 1) * 2 ^ (2 * m + 1) := Nat.mul_le_mul hq hq
    have hcard : Fintype.card (SzOvoid m) = (2 ^ (2 * m + 1)) ^ 2 + 1 := by
      rw [← Nat.card_eq_fintype_card]
      exact suzuki_ovoid_card m
    rw [hcard]
    omega
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp h3
  exact suzuki_ovoid_three_point_free m hm x hx1 a b c hab hac hbc
    ⟨hfix a, hfix b, hfix c⟩

theorem suzukiTorusData_suzukiMatrixGroup (m : ℕ) (hm : 0 < m) :
    CFSG.GroupTheory.SuzukiTorusData (SuzukiMatrixGroup m) (2 ^ (2 * m + 1)) where
  faithful := faithful_model m hm
  card_points := (card_sylow_eq_ovoid m hm).trans (suzuki_ovoid_card m)
  fixes_le_two := fixes_le_two_model m hm
  card_sylow := fun U => (sylow_card_and_center m hm U).1
  regular := regular_sylow m hm
  inf_normalizer_isCyclic := fun U U' hUV => inf_normalizer_isCyclic m hm hUV
  inf_normalizer_card := fun U U' hUV => card_inf_normalizer m hm hUV
  inf_normalizer_free := fun U U' hUV h hhN hh1 u hu =>
    inf_normalizer_free m hm hUV hhN hh1 u hu
  card_frattini := card_frattini m hm

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
