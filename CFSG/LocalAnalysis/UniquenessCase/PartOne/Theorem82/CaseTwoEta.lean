module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoP1Defs
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs2
public import CFSG.CGT.PushingUpLit.CGT6.EmbEndSmall
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoTwoLocalA
import all CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoRArgument
import all CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoPi
import all CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoSylow
import all CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoKy
import all CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoKyNormal
import all CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoFixedEnd
import all CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoPoints
import CFSG.GroupTheory.PGroup.CardCoprime

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace CaseTwoTransitive

variable {c : Ctx812E G} (t : CaseTwoTransitive c)

private theorem Lhat_map_conj_le (r : G) (hrM : r ∈ c.S.M) (i : Fin 3) :
    (t.Lhat i).map (MulAut.conj (t.qmk ⟨r, hrM⟩)).toMonoidHom
      ≤ t.Lhat (t.d.permHom t.hinj (hperm_d t) ⟨r, t.hdM ▸ (show r ∈ t.M from hrM)⟩ i) := by
  let rmM : ↥t.M := ⟨r, hrM⟩
  let rmD : ↥t.d.M := ⟨r, t.hdM ▸ (show r ∈ t.M from hrM)⟩
  rintro z ⟨aM, haM, rfl⟩
  obtain ⟨aG, haG, rfl⟩ := Subgroup.mem_map.mp haM
  have hai : (aG : G) ∈ t.d.Lf i := Subgroup.mem_subgroupOf.mp haG
  have hconj : r * (aG : G) * r⁻¹ ∈
      t.d.Lf (t.d.permHom t.hinj (hperm_d t) rmD i) := by
    have h : r * (aG : G) * r⁻¹ ∈ (t.d.Lf i).map (MulAut.conj r).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨(aG : G), hai, rfl⟩
    have hspec := t.d.map_conj_Lf_eq t.hinj (hperm_d t) rmD i
    rw [show (rmD : G) = r from rfl] at hspec
    rw [hspec] at h
    exact h
  have hconjM : r * (aG : G) * r⁻¹ ∈ c.S.M :=
    c.S.M.mul_mem (c.S.M.mul_mem hrM aG.2) (c.S.M.inv_mem hrM)
  let bM : ↥t.M := ⟨r * (aG : G) * r⁻¹, hconjM⟩
  have hbM : bM ∈
      (t.d.Lf (t.d.permHom t.hinj (hperm_d t) rmD i)).subgroupOf t.M :=
    Subgroup.mem_subgroupOf.mpr hconj
  refine Subgroup.mem_map.mpr ⟨bM, hbM, ?_⟩
  change t.qmk bM = (t.qmk rmM) * (t.qmk aG) * (t.qmk rmM)⁻¹
  rw [← map_mul, ← map_inv, ← map_mul]
  rfl


private theorem conj_delta_eq_self (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) {R : Subgroup G}
    (hRM : R ≤ c.S.M) (hKR : t.Ky ≤ Subgroup.normalizer (R : Set G))
    (hR2 : IsPGroup 2 R) {r : G} (hrR : r ∈ R) (u : ↥(t.Lhat 0)) :
    t.qmk ⟨r, hRM hrR⟩ * t.delta u * (t.qmk ⟨r, hRM hrR⟩)⁻¹ = t.delta u := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3R : ¬ 3 ∣ Nat.card R :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup hR2 Nat.prime_three (by norm_num)
  have hcomm : ⁅R, t.Ky⁆ ≤ c.L ⊓ t.d.N :=
    (t.commutator_Ky_le_inf_N hK32 hGA hSp hRM hKR h3R).trans inf_le_right
  have hdelta_mem : t.delta u ∈ (t.phiKy).range := by
    rw [t.phiKy_range_eq_delta_range hK32 hGA hSp]
    exact ⟨u, rfl⟩
  obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp hdelta_mem
  have hkM : t.qmk (kM t k) = t.delta u := by
    change t.phiKy k = t.delta u
    exact hk
  have hmem : ⁅r, (k : G)⁆ ∈ c.L ⊓ t.d.N :=
    Subgroup.commutator_le.mp hcomm r hrR (k : G) k.2
  let rmM : ↥t.M := ⟨r, hRM hrR⟩
  have hkconj : t.qmk (rmM * kM t k * rmM⁻¹) = t.qmk (kM t k) := by
    have hmemKq : rmM * kM t k * rmM⁻¹ * (kM t k)⁻¹ ∈ t.Kq := by
      rw [show rmM * kM t k * rmM⁻¹ * (kM t k)⁻¹ = ⁅rmM, kM t k⁆ from by
        rw [commutatorElement_def]]
      exact Subgroup.mem_subgroupOf.mpr
        (show ⁅(rmM : G), (kM t k : G)⁆ ∈ c.L ⊓ t.d.N from hmem)
    have h1 : t.qmk (rmM * kM t k * rmM⁻¹ * (kM t k)⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hmemKq
    rw [map_mul, map_mul, map_inv, map_inv] at h1
    exact mul_inv_eq_one.mp h1
  calc t.qmk rmM * t.delta u * (t.qmk rmM)⁻¹
      = t.qmk rmM * t.qmk (kM t k) * (t.qmk rmM)⁻¹ := by rw [hkM]
    _ = t.qmk (rmM * kM t k * rmM⁻¹) := by rw [map_mul, map_mul, map_inv]
    _ = t.qmk (kM t k) := hkconj
    _ = t.delta u := hkM


private noncomputable def diagComp (u : ↥(t.Lhat 0)) : (m : Fin 3) → ↥(t.Lhat m)
  | 0 => u
  | 1 => ⟨(MulAut.conj t.ybar) (u : t.Mb), conj_ybar_mem_Lhat_one t u.2⟩
  | 2 => ⟨(MulAut.conj (t.ybar ^ 2)) (u : t.Mb), conj_ybar_sq_mem_Lhat_two t u.2⟩

private theorem muL_diagComp (u : ↥(t.Lhat 0)) :
    t.muL ((diagComp t u 0, diagComp t u 1), diagComp t u 2) = t.delta u := by
  rw [muL_apply, delta_apply]
  rfl



private theorem ybar_sq_eq_inv : t.ybar ^ 2 = t.ybar⁻¹ := by
  have h := t.ybar_pow_three
  calc t.ybar ^ 2 = t.ybar ^ 2 * 1 := by rw [mul_one]
    _ = t.ybar ^ 2 * (t.ybar * t.ybar⁻¹) := by rw [mul_inv_cancel]
    _ = (t.ybar ^ 2 * t.ybar) * t.ybar⁻¹ := by group
    _ = t.ybar ^ 3 * t.ybar⁻¹ := by group
    _ = t.ybar⁻¹ := by rw [h, one_mul]




private theorem mulAut_conj_inv_conj (x : t.Mb) :
    (MulAut.conj t.ybar⁻¹) ((MulAut.conj t.ybar) x) = x := by
  rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]

private theorem mulAut_conj_conj_sq (x : t.Mb) :
    (MulAut.conj t.ybar) ((MulAut.conj (t.ybar ^ 2)) x) = x := by
  rw [← MulAut.mul_apply, ← map_mul]
  have h : t.ybar * t.ybar ^ 2 = 1 := by
    rw [← pow_succ', t.ybar_pow_three]
  rw [h, map_one, MulAut.one_apply]

private theorem conj_fixed_components (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) {R : Subgroup G}
    (hRM : R ≤ c.S.M) (hKR : t.Ky ≤ Subgroup.normalizer (R : Set G))
    (hR2 : IsPGroup 2 R) {r : G} (hrR : r ∈ R)
    (hπ : ∀ m : Fin 3,
      t.d.permHom t.hinj (hperm_d t) ⟨r, t.hdM ▸ (show r ∈ t.M from hRM hrR)⟩ m = m)
    (u : ↥(t.Lhat 0)) :
    let a := diagComp t u
    let σ := MulAut.conj (t.qmk ⟨r, hRM hrR⟩)
    σ (a 0 : t.Mb) = (a 0 : t.Mb) ∧ σ (a 1 : t.Mb) = (a 1 : t.Mb) ∧
      σ (a 2 : t.Mb) = (a 2 : t.Mb) := by
  let rmM : ↥t.M := ⟨r, hRM hrR⟩
  let σ := MulAut.conj (t.qmk rmM)
  let a : (m : Fin 3) → ↥(t.Lhat m) := diagComp t u
  have hσdelta : σ (t.delta u) = t.delta u :=
    conj_delta_eq_self t hK32 hGA hSp hRM hKR hR2 hrR u
  have hmem : ∀ m : Fin 3, σ (a m : t.Mb) ∈ t.Lhat m := by
    intro m
    have h := Lhat_map_conj_le t r (hRM hrR) m
      (Subgroup.mem_map_of_mem (MulAut.conj (t.qmk ⟨r, hRM hrR⟩)).toMonoidHom (a m).2)
    rw [hπ m] at h
    exact h
  let c0 : ↥(t.Lhat 0) := ⟨σ (a 0 : t.Mb), hmem 0⟩
  let c1 : ↥(t.Lhat 1) := ⟨σ (a 1 : t.Mb), hmem 1⟩
  let c2 : ↥(t.Lhat 2) := ⟨σ (a 2 : t.Mb), hmem 2⟩
  have hmuLc : t.muL ((c0, c1), c2) = σ (t.muL ((a 0, a 1), a 2)) := by
    rw [muL_apply, muL_apply]
    change (c0 : t.Mb) * (c1 : t.Mb) * (c2 : t.Mb) =
      σ ((a 0 : t.Mb) * (a 1 : t.Mb) * (a 2 : t.Mb))
    rw [map_mul, map_mul]
  have hmuLa : t.muL ((a 0, a 1), a 2) = t.delta u := muL_diagComp t u
  have hEq : t.muL ((c0, c1), c2) = t.muL ((a 0, a 1), a 2) := by
    rw [hmuLc, hmuLa, hσdelta, ← hmuLa]
  have htuple := t.muL_injective hK32 hGA hSp hEq
  have h0 : (c0 : t.Mb) = (a 0 : t.Mb) :=
    congrArg (fun p : (↥(t.Lhat 0) × ↥(t.Lhat 1)) × ↥(t.Lhat 2) =>
      ((p.1.1 : ↥(t.Lhat 0)) : t.Mb)) htuple
  have h1 : (c1 : t.Mb) = (a 1 : t.Mb) :=
    congrArg (fun p : (↥(t.Lhat 0) × ↥(t.Lhat 1)) × ↥(t.Lhat 2) =>
      ((p.1.2 : ↥(t.Lhat 1)) : t.Mb)) htuple
  have h2 : (c2 : t.Mb) = (a 2 : t.Mb) :=
    congrArg (fun p : (↥(t.Lhat 0) × ↥(t.Lhat 1)) × ↥(t.Lhat 2) =>
      ((p.2 : ↥(t.Lhat 2)) : t.Mb)) htuple
  exact ⟨h0, h1, h2⟩


private theorem conj_swap_zero_one_components (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) {R : Subgroup G}
    (hRM : R ≤ c.S.M) (hKR : t.Ky ≤ Subgroup.normalizer (R : Set G))
    (hR2 : IsPGroup 2 R) {r : G} (hrR : r ∈ R)
    (hπ0 : t.d.permHom t.hinj (hperm_d t)
      ⟨r, t.hdM ▸ (show r ∈ t.M from hRM hrR)⟩ 0 = 1)
    (hπ1 : t.d.permHom t.hinj (hperm_d t)
      ⟨r, t.hdM ▸ (show r ∈ t.M from hRM hrR)⟩ 1 = 0)
    (hπ2 : t.d.permHom t.hinj (hperm_d t)
      ⟨r, t.hdM ▸ (show r ∈ t.M from hRM hrR)⟩ 2 = 2)
    (u : ↥(t.Lhat 0)) :
    let a := diagComp t u
    let σ := MulAut.conj (t.qmk ⟨r, hRM hrR⟩)
    σ (a 0 : t.Mb) = (a 1 : t.Mb) ∧ σ (a 1 : t.Mb) = (a 0 : t.Mb) ∧
      σ (a 2 : t.Mb) = (a 2 : t.Mb) := by
  let rmM : ↥t.M := ⟨r, hRM hrR⟩
  let σ := MulAut.conj (t.qmk rmM)
  let a : (m : Fin 3) → ↥(t.Lhat m) := diagComp t u
  have hσdelta : σ (t.delta u) = t.delta u :=
    conj_delta_eq_self t hK32 hGA hSp hRM hKR hR2 hrR u
  have hmem1 : σ (a 1 : t.Mb) ∈ t.Lhat 0 := by
    have h := Lhat_map_conj_le t r (hRM hrR) 1
      (Subgroup.mem_map_of_mem (MulAut.conj (t.qmk ⟨r, hRM hrR⟩)).toMonoidHom (a 1).2)
    rwa [hπ1] at h
  have hmem0 : σ (a 0 : t.Mb) ∈ t.Lhat 1 := by
    have h := Lhat_map_conj_le t r (hRM hrR) 0
      (Subgroup.mem_map_of_mem (MulAut.conj (t.qmk ⟨r, hRM hrR⟩)).toMonoidHom (a 0).2)
    rwa [hπ0] at h
  have hmem2 : σ (a 2 : t.Mb) ∈ t.Lhat 2 := by
    have h := Lhat_map_conj_le t r (hRM hrR) 2
      (Subgroup.mem_map_of_mem (MulAut.conj (t.qmk ⟨r, hRM hrR⟩)).toMonoidHom (a 2).2)
    rwa [hπ2] at h
  let c0 : ↥(t.Lhat 0) := ⟨σ (a 1 : t.Mb), hmem1⟩
  let c1 : ↥(t.Lhat 1) := ⟨σ (a 0 : t.Mb), hmem0⟩
  let c2 : ↥(t.Lhat 2) := ⟨σ (a 2 : t.Mb), hmem2⟩
  have hcomm : (c0 : t.Mb) * (c1 : t.Mb) = (c1 : t.Mb) * (c0 : t.Mb) :=
    (commute_of_mem_Lhat t 0 1 (by decide) (c0 : t.Mb) (c1 : t.Mb) c0.2 c1.2).eq
  have hmuLc : t.muL ((c0, c1), c2) = σ (t.muL ((a 0, a 1), a 2)) := by
    rw [muL_apply, muL_apply]
    change (c0 : t.Mb) * (c1 : t.Mb) * (c2 : t.Mb) =
      σ ((a 0 : t.Mb) * (a 1 : t.Mb) * (a 2 : t.Mb))
    rw [map_mul, map_mul]
    rw [hcomm]
  have hmuLa : t.muL ((a 0, a 1), a 2) = t.delta u := muL_diagComp t u
  have hEq : t.muL ((c0, c1), c2) = t.muL ((a 0, a 1), a 2) := by
    rw [hmuLc, hmuLa, hσdelta, ← hmuLa]
  have htuple := t.muL_injective hK32 hGA hSp hEq
  have h0 : (c0 : t.Mb) = (a 0 : t.Mb) :=
    congrArg (fun p : (↥(t.Lhat 0) × ↥(t.Lhat 1)) × ↥(t.Lhat 2) =>
      ((p.1.1 : ↥(t.Lhat 0)) : t.Mb)) htuple
  have h1 : (c1 : t.Mb) = (a 1 : t.Mb) :=
    congrArg (fun p : (↥(t.Lhat 0) × ↥(t.Lhat 1)) × ↥(t.Lhat 2) =>
      ((p.1.2 : ↥(t.Lhat 1)) : t.Mb)) htuple
  have h2 : (c2 : t.Mb) = (a 2 : t.Mb) :=
    congrArg (fun p : (↥(t.Lhat 0) × ↥(t.Lhat 1)) × ↥(t.Lhat 2) =>
      ((p.2 : ↥(t.Lhat 2)) : t.Mb)) htuple
  exact ⟨h1, h0, h2⟩

private theorem conj_swap_one_two_components (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) {R : Subgroup G}
    (hRM : R ≤ c.S.M) (hKR : t.Ky ≤ Subgroup.normalizer (R : Set G))
    (hR2 : IsPGroup 2 R) {r : G} (hrR : r ∈ R)
    (hπ0 : t.d.permHom t.hinj (hperm_d t)
      ⟨r, t.hdM ▸ (show r ∈ t.M from hRM hrR)⟩ 0 = 0)
    (hπ1 : t.d.permHom t.hinj (hperm_d t)
      ⟨r, t.hdM ▸ (show r ∈ t.M from hRM hrR)⟩ 1 = 2)
    (hπ2 : t.d.permHom t.hinj (hperm_d t)
      ⟨r, t.hdM ▸ (show r ∈ t.M from hRM hrR)⟩ 2 = 1)
    (u : ↥(t.Lhat 0)) :
    let a := diagComp t u
    let σ := MulAut.conj (t.qmk ⟨r, hRM hrR⟩)
    σ (a 0 : t.Mb) = (a 0 : t.Mb) ∧ σ (a 1 : t.Mb) = (a 2 : t.Mb) ∧
      σ (a 2 : t.Mb) = (a 1 : t.Mb) := by
  let rmM : ↥t.M := ⟨r, hRM hrR⟩
  let σ := MulAut.conj (t.qmk rmM)
  let a : (m : Fin 3) → ↥(t.Lhat m) := diagComp t u
  have hσdelta : σ (t.delta u) = t.delta u :=
    conj_delta_eq_self t hK32 hGA hSp hRM hKR hR2 hrR u
  have hmem0 : σ (a 0 : t.Mb) ∈ t.Lhat 0 := by
    have h := Lhat_map_conj_le t r (hRM hrR) 0
      (Subgroup.mem_map_of_mem (MulAut.conj (t.qmk ⟨r, hRM hrR⟩)).toMonoidHom (a 0).2)
    rwa [hπ0] at h
  have hmem2 : σ (a 2 : t.Mb) ∈ t.Lhat 1 := by
    have h := Lhat_map_conj_le t r (hRM hrR) 2
      (Subgroup.mem_map_of_mem (MulAut.conj (t.qmk ⟨r, hRM hrR⟩)).toMonoidHom (a 2).2)
    rwa [hπ2] at h
  have hmem1 : σ (a 1 : t.Mb) ∈ t.Lhat 2 := by
    have h := Lhat_map_conj_le t r (hRM hrR) 1
      (Subgroup.mem_map_of_mem (MulAut.conj (t.qmk ⟨r, hRM hrR⟩)).toMonoidHom (a 1).2)
    rwa [hπ1] at h
  let c0 : ↥(t.Lhat 0) := ⟨σ (a 0 : t.Mb), hmem0⟩
  let c1 : ↥(t.Lhat 1) := ⟨σ (a 2 : t.Mb), hmem2⟩
  let c2 : ↥(t.Lhat 2) := ⟨σ (a 1 : t.Mb), hmem1⟩
  have hcomm : (c1 : t.Mb) * (c2 : t.Mb) = (c2 : t.Mb) * (c1 : t.Mb) :=
    (commute_of_mem_Lhat t 1 2 (by decide) (c1 : t.Mb) (c2 : t.Mb) c1.2 c2.2).eq
  have hmuLc : t.muL ((c0, c1), c2) = σ (t.muL ((a 0, a 1), a 2)) := by
    rw [muL_apply, muL_apply]
    change (c0 : t.Mb) * (c1 : t.Mb) * (c2 : t.Mb) =
      σ ((a 0 : t.Mb) * (a 1 : t.Mb) * (a 2 : t.Mb))
    rw [map_mul, map_mul]
    change (c0 : t.Mb) * (c1 : t.Mb) * (c2 : t.Mb) =
      (c0 : t.Mb) * (c2 : t.Mb) * (c1 : t.Mb)
    calc (c0 : t.Mb) * (c1 : t.Mb) * (c2 : t.Mb)
        = (c0 : t.Mb) * ((c1 : t.Mb) * (c2 : t.Mb)) := by rw [mul_assoc]
      _ = (c0 : t.Mb) * ((c2 : t.Mb) * (c1 : t.Mb)) := by rw [hcomm]
      _ = (c0 : t.Mb) * (c2 : t.Mb) * (c1 : t.Mb) := by rw [mul_assoc]
  have hmuLa : t.muL ((a 0, a 1), a 2) = t.delta u := muL_diagComp t u
  have hEq : t.muL ((c0, c1), c2) = t.muL ((a 0, a 1), a 2) := by
    rw [hmuLc, hmuLa, hσdelta, ← hmuLa]
  have htuple := t.muL_injective hK32 hGA hSp hEq
  have h0 : (c0 : t.Mb) = (a 0 : t.Mb) :=
    congrArg (fun p : (↥(t.Lhat 0) × ↥(t.Lhat 1)) × ↥(t.Lhat 2) =>
      ((p.1.1 : ↥(t.Lhat 0)) : t.Mb)) htuple
  have h1 : (c1 : t.Mb) = (a 1 : t.Mb) :=
    congrArg (fun p : (↥(t.Lhat 0) × ↥(t.Lhat 1)) × ↥(t.Lhat 2) =>
      ((p.1.2 : ↥(t.Lhat 1)) : t.Mb)) htuple
  have h2 : (c2 : t.Mb) = (a 2 : t.Mb) :=
    congrArg (fun p : (↥(t.Lhat 0) × ↥(t.Lhat 1)) × ↥(t.Lhat 2) =>
      ((p.2 : ↥(t.Lhat 2)) : t.Mb)) htuple
  exact ⟨h0, h2, h1⟩


private theorem conj_swap_two_zero_components (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) {R : Subgroup G}
    (hRM : R ≤ c.S.M) (hKR : t.Ky ≤ Subgroup.normalizer (R : Set G))
    (hR2 : IsPGroup 2 R) {r : G} (hrR : r ∈ R)
    (hπ0 : t.d.permHom t.hinj (hperm_d t)
      ⟨r, t.hdM ▸ (show r ∈ t.M from hRM hrR)⟩ 0 = 2)
    (hπ1 : t.d.permHom t.hinj (hperm_d t)
      ⟨r, t.hdM ▸ (show r ∈ t.M from hRM hrR)⟩ 1 = 1)
    (hπ2 : t.d.permHom t.hinj (hperm_d t)
      ⟨r, t.hdM ▸ (show r ∈ t.M from hRM hrR)⟩ 2 = 0)
    (u : ↥(t.Lhat 0)) :
    let a := diagComp t u
    let σ := MulAut.conj (t.qmk ⟨r, hRM hrR⟩)
    σ (a 0 : t.Mb) = (a 2 : t.Mb) ∧ σ (a 1 : t.Mb) = (a 1 : t.Mb) ∧
      σ (a 2 : t.Mb) = (a 0 : t.Mb) := by
  let rmM : ↥t.M := ⟨r, hRM hrR⟩
  let σ := MulAut.conj (t.qmk rmM)
  let a : (m : Fin 3) → ↥(t.Lhat m) := diagComp t u
  have hσdelta : σ (t.delta u) = t.delta u :=
    conj_delta_eq_self t hK32 hGA hSp hRM hKR hR2 hrR u
  have hmem2 : σ (a 2 : t.Mb) ∈ t.Lhat 0 := by
    have h := Lhat_map_conj_le t r (hRM hrR) 2
      (Subgroup.mem_map_of_mem (MulAut.conj (t.qmk ⟨r, hRM hrR⟩)).toMonoidHom (a 2).2)
    rwa [hπ2] at h
  have hmem1 : σ (a 1 : t.Mb) ∈ t.Lhat 1 := by
    have h := Lhat_map_conj_le t r (hRM hrR) 1
      (Subgroup.mem_map_of_mem (MulAut.conj (t.qmk ⟨r, hRM hrR⟩)).toMonoidHom (a 1).2)
    rwa [hπ1] at h
  have hmem0 : σ (a 0 : t.Mb) ∈ t.Lhat 2 := by
    have h := Lhat_map_conj_le t r (hRM hrR) 0
      (Subgroup.mem_map_of_mem (MulAut.conj (t.qmk ⟨r, hRM hrR⟩)).toMonoidHom (a 0).2)
    rwa [hπ0] at h
  let c0 : ↥(t.Lhat 0) := ⟨σ (a 2 : t.Mb), hmem2⟩
  let c1 : ↥(t.Lhat 1) := ⟨σ (a 1 : t.Mb), hmem1⟩
  let c2 : ↥(t.Lhat 2) := ⟨σ (a 0 : t.Mb), hmem0⟩
  have hc01 : Commute (c0 : t.Mb) (c1 : t.Mb) :=
    commute_of_mem_Lhat t 0 1 (by decide) (c0 : t.Mb) (c1 : t.Mb) c0.2 c1.2
  have hc02 : Commute (c0 : t.Mb) (c2 : t.Mb) :=
    commute_of_mem_Lhat t 0 2 (by decide) (c0 : t.Mb) (c2 : t.Mb) c0.2 c2.2
  have hc12 : Commute (c1 : t.Mb) (c2 : t.Mb) :=
    commute_of_mem_Lhat t 1 2 (by decide) (c1 : t.Mb) (c2 : t.Mb) c1.2 c2.2
  have hc012 : Commute ((c0 : t.Mb) * (c1 : t.Mb)) (c2 : t.Mb) := hc02.mul_left hc12
  have hmuLc : t.muL ((c0, c1), c2) = σ (t.muL ((a 0, a 1), a 2)) := by
    rw [muL_apply, muL_apply]
    change (c0 : t.Mb) * (c1 : t.Mb) * (c2 : t.Mb) =
      σ ((a 0 : t.Mb) * (a 1 : t.Mb) * (a 2 : t.Mb))
    rw [map_mul, map_mul]
    calc (c0 : t.Mb) * (c1 : t.Mb) * (c2 : t.Mb)
        = (c2 : t.Mb) * ((c0 : t.Mb) * (c1 : t.Mb)) := hc012.eq
      _ = (c2 : t.Mb) * ((c1 : t.Mb) * (c0 : t.Mb)) := by rw [hc01.eq]
      _ = (c2 : t.Mb) * (c1 : t.Mb) * (c0 : t.Mb) := by rw [mul_assoc]
  have hmuLa : t.muL ((a 0, a 1), a 2) = t.delta u := muL_diagComp t u
  have hEq : t.muL ((c0, c1), c2) = t.muL ((a 0, a 1), a 2) := by
    rw [hmuLc, hmuLa, hσdelta, ← hmuLa]
  have htuple := t.muL_injective hK32 hGA hSp hEq
  have h0 : (c0 : t.Mb) = (a 0 : t.Mb) :=
    congrArg (fun p : (↥(t.Lhat 0) × ↥(t.Lhat 1)) × ↥(t.Lhat 2) =>
      ((p.1.1 : ↥(t.Lhat 0)) : t.Mb)) htuple
  have h1 : (c1 : t.Mb) = (a 1 : t.Mb) :=
    congrArg (fun p : (↥(t.Lhat 0) × ↥(t.Lhat 1)) × ↥(t.Lhat 2) =>
      ((p.1.2 : ↥(t.Lhat 1)) : t.Mb)) htuple
  have h2 : (c2 : t.Mb) = (a 2 : t.Mb) :=
    congrArg (fun p : (↥(t.Lhat 0) × ↥(t.Lhat 1)) × ↥(t.Lhat 2) =>
      ((p.2 : ↥(t.Lhat 2)) : t.Mb)) htuple
  exact ⟨h2, h1, h0⟩


private theorem exists_diagComp_one {x : t.Mb} (hx : x ∈ t.Lhat 1) :
    ∃ u : ↥(t.Lhat 0), x = (diagComp t u 1 : t.Mb) := by
  have hx' : x ∈ (t.Lhat 0).map (MulAut.conj t.ybar).toMonoidHom := by
    rw [Lhat_conj t 0]
    exact hx
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx'
  exact ⟨⟨u, hu⟩, rfl⟩

private theorem exists_diagComp_two {x : t.Mb} (hx : x ∈ t.Lhat 2) :
    ∃ u : ↥(t.Lhat 0), x = (diagComp t u 2 : t.Mb) := by
  have hx' : x ∈ (t.Lhat 0).map (MulAut.conj (t.ybar ^ 2)).toMonoidHom := by
    rw [Lhat_two_eq_map t]
    exact hx
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx'
  exact ⟨⟨u, hu⟩, rfl⟩


private theorem conj_fixed_mem (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) {R : Subgroup G}
    (hRM : R ≤ c.S.M) (hKR : t.Ky ≤ Subgroup.normalizer (R : Set G))
    (hR2 : IsPGroup 2 R) {r : G} (hrR : r ∈ R)
    (hπ : ∀ m : Fin 3,
      t.d.permHom t.hinj (hperm_d t) ⟨r, t.hdM ▸ (show r ∈ t.M from hRM hrR)⟩ m = m)
    {i : Fin 3} {x : t.Mb} (hx : x ∈ t.Lhat i) :
    (MulAut.conj (t.qmk ⟨r, hRM hrR⟩)) x = x := by
  fin_cases i
  · exact (conj_fixed_components t hK32 hGA hSp hRM hKR hR2 hrR hπ ⟨x, hx⟩).1
  · obtain ⟨u, rfl⟩ := exists_diagComp_one t hx
    exact (conj_fixed_components t hK32 hGA hSp hRM hKR hR2 hrR hπ u).2.1
  · obtain ⟨u, rfl⟩ := exists_diagComp_two t hx
    exact (conj_fixed_components t hK32 hGA hSp hRM hKR hR2 hrR hπ u).2.2

private theorem conj_transposition_mem (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) {R : Subgroup G}
    (hRM : R ≤ c.S.M) (hKR : t.Ky ≤ Subgroup.normalizer (R : Set G))
    (hR2 : IsPGroup 2 R) {r : G} (hrR : r ∈ R) (j : Fin 3)
    (hπj : t.d.permHom t.hinj (hperm_d t)
      ⟨r, t.hdM ▸ (show r ∈ t.M from hRM hrR)⟩ j = j + 1)
    (hπk : t.d.permHom t.hinj (hperm_d t)
      ⟨r, t.hdM ▸ (show r ∈ t.M from hRM hrR)⟩ (j + 1) = j)
    (hπi : t.d.permHom t.hinj (hperm_d t)
      ⟨r, t.hdM ▸ (show r ∈ t.M from hRM hrR)⟩ (j + 2) = j + 2) :
    (∀ x : t.Mb, x ∈ t.Lhat j →
        (MulAut.conj (t.qmk ⟨r, hRM hrR⟩)) x = (MulAut.conj t.ybar) x) ∧
    (∀ x : t.Mb, x ∈ t.Lhat (j + 1) →
        (MulAut.conj (t.qmk ⟨r, hRM hrR⟩)) x = (MulAut.conj t.ybar⁻¹) x) ∧
    (∀ x : t.Mb, x ∈ t.Lhat (j + 2) →
        (MulAut.conj (t.qmk ⟨r, hRM hrR⟩)) x = x) := by
  fin_cases j
  · have hπ0 := hπj
    have hπ1 := hπk
    have hπ2 := hπi
    have h := conj_swap_zero_one_components t hK32 hGA hSp hRM hKR hR2 hrR hπ0 hπ1 hπ2
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      exact (h ⟨x, hx⟩).1
    · intro x hx
      obtain ⟨u, rfl⟩ := exists_diagComp_one t hx
      have h1 := (h u).2.1
      rw [h1]
      exact (mulAut_conj_inv_conj t u).symm
    · intro x hx
      obtain ⟨u, rfl⟩ := exists_diagComp_two t hx
      exact (h u).2.2
  · have hπ1 := hπj
    have hπ2 := hπk
    have hπ0 := hπi
    have h := conj_swap_one_two_components t hK32 hGA hSp hRM hKR hR2 hrR hπ0 hπ1 hπ2
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨u, rfl⟩ := exists_diagComp_one t hx
      have h1 := (h u).2.1
      rw [h1]
      exact (mulAut_conj_sq t u).symm
    · intro x hx
      obtain ⟨u, rfl⟩ := exists_diagComp_two t hx
      have h1 := (h u).2.2
      have h2 : (diagComp t u 2 : t.Mb) = (MulAut.conj t.ybar) (diagComp t u 1 : t.Mb) :=
        (mulAut_conj_sq t u).symm
      rw [h1, h2]
      exact (mulAut_conj_inv_conj t (diagComp t u 1 : t.Mb)).symm
    · intro x hx
      exact (h ⟨x, hx⟩).1
  · have hπ2 := hπj
    have hπ0 := hπk
    have hπ1 := hπi
    have h := conj_swap_two_zero_components t hK32 hGA hSp hRM hKR hR2 hrR hπ0 hπ1 hπ2
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨u, rfl⟩ := exists_diagComp_two t hx
      have h1 := (h u).2.2
      rw [h1]
      exact (mulAut_conj_conj_sq t u).symm
    · intro x hx
      have h1 := (h ⟨x, hx⟩).1
      have hx0 : x = (t.diagComp ⟨x, hx⟩ 0 : t.Mb) := rfl
      rw [hx0, h1]
      change (MulAut.conj (t.ybar ^ 2)) (t.diagComp ⟨x, hx⟩ 0 : t.Mb) =
        (MulAut.conj t.ybar⁻¹) (t.diagComp ⟨x, hx⟩ 0 : t.Mb)
      rw [ybar_sq_eq_inv t]
    · intro x hx
      obtain ⟨u, rfl⟩ := exists_diagComp_one t hx
      exact (h u).2.1


private noncomputable def conjHom (j : Fin 3) : ↥(t.d.A j) →* ↥(t.d.A (j + 1)) where
  toFun a :=
    ⟨t.y * (a : G) * t.y⁻¹, by
      have h := Subgroup.mem_map_of_mem (MulAut.conj t.y).toMonoidHom a.2
      rwa [t.map_conj_A j] at h⟩
  map_one' := by ext; simp
  map_mul' a b := by
    ext
    simp only [Subgroup.coe_mul, Subgroup.coe_mk, MulAut.conj_apply]
    group

private noncomputable def diagHom (j : Fin 3) :
    ↥(t.d.A j) →* ↥(t.d.A j ⊔ t.d.A (j + 1)) := by
  letI : IsMulCommutative ↥(t.d.A j ⊔ t.d.A (j + 1)) :=
    (t.d.isElemAbelian_A_sup_A j (j + 1)).1
  letI : CommGroup ↥(t.d.A j ⊔ t.d.A (j + 1)) := IsMulCommutative.instCommGroup
  exact (Subgroup.inclusion le_sup_left) *
    ((Subgroup.inclusion le_sup_right).comp (conjHom t j))

private noncomputable def Diag (j : Fin 3) : Subgroup G :=
  (diagHom t j).range.map (Subgroup.subtype (t.d.A j ⊔ t.d.A (j + 1)))


private theorem diagHom_apply (j : Fin 3) (a : ↥(t.d.A j)) :
    (diagHom t j a : G) = (a : G) * (t.y * (a : G) * t.y⁻¹) := by
  letI : IsMulCommutative ↥(t.d.A j ⊔ t.d.A (j + 1)) :=
    (t.d.isElemAbelian_A_sup_A j (j + 1)).1
  letI : CommGroup ↥(t.d.A j ⊔ t.d.A (j + 1)) := IsMulCommutative.instCommGroup
  rfl

private theorem inf_A_A_succ_eq_bot (j : Fin 3) : t.d.A j ⊓ t.d.A (j + 1) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨hxj, hxk⟩ := Subgroup.mem_inf.mp hx
  have hS : x ∈ t.d.S := t.d.A_le_S j hxj
  have hLfj : x ∈ t.d.Lf j := (t.d.A_le_H j).trans (t.d.H_le_Lf j) hxj
  have hLfk : x ∈ t.d.Lf (j + 1) ⊔ t.d.Lf (j + 2) :=
    Subgroup.mem_sup_left ((t.d.A_le_H (j + 1)).trans (t.d.H_le_Lf (j + 1)) hxk)
  have h1 : j ≠ j + 1 := by fin_cases j <;> decide
  have h2 : j ≠ j + 2 := by fin_cases j <;> decide
  have h3 : j + 1 ≠ j + 2 := by fin_cases j <;> decide
  exact t.d.eq_one_of_mem_Lf_of_mem_sup h1 h2 h3 hS hLfj hLfk

private theorem Diag_le_AA (j : Fin 3) : t.Diag j ≤ t.d.AA := by
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hy
  have hay : t.y * (a : G) * t.y⁻¹ ∈ t.d.A (j + 1) := by
    have h := Subgroup.mem_map_of_mem (MulAut.conj t.y).toMonoidHom a.2
    rwa [t.map_conj_A j] at h
  change (diagHom t j a : G) ∈ t.d.AA
  rw [diagHom_apply t j a]
  exact t.d.AA.mul_mem (A_le_AA t j a.2) (A_le_AA t (j + 1) hay)

private theorem diagHom_injective (j : Fin 3) : Function.Injective (diagHom t j) := by
  intro a b h
  have h1 : (a : G) * (t.y * (a : G) * t.y⁻¹) =
      (b : G) * (t.y * (b : G) * t.y⁻¹) := by
    simpa [diagHom_apply t j] using congrArg Subtype.val h
  have hay : t.y * (a : G) * t.y⁻¹ ∈ t.d.A (j + 1) := by
    have h := Subgroup.mem_map_of_mem (MulAut.conj t.y).toMonoidHom a.2
    rwa [t.map_conj_A j] at h
  have hby : t.y * (b : G) * t.y⁻¹ ∈ t.d.A (j + 1) := by
    have h := Subgroup.mem_map_of_mem (MulAut.conj t.y).toMonoidHom b.2
    rwa [t.map_conj_A j] at h
  have hab_comm : (a : G) * (b : G) = (b : G) * (a : G) :=
    t.d.isElemAbelian_AA.comm (A_le_AA t j a.2) (A_le_AA t j b.2)
  have hcab : Commute (a : G) (b : G) := (commute_iff_eq _ _).mpr hab_comm
  have h2 : (a : G) * (b : G)⁻¹ =
      (t.y * (b : G) * t.y⁻¹) * (t.y * (a : G) * t.y⁻¹)⁻¹ := by
    calc (a : G) * (b : G)⁻¹ = (b : G)⁻¹ * (a : G) := by
          simpa using hcab.inv_right.eq
      _ = (b : G)⁻¹ * ((a : G) * (t.y * (a : G) * t.y⁻¹)) *
            (t.y * (a : G) * t.y⁻¹)⁻¹ := by group
      _ = (b : G)⁻¹ * ((b : G) * (t.y * (b : G) * t.y⁻¹)) *
            (t.y * (a : G) * t.y⁻¹)⁻¹ := by rw [h1]
      _ = (t.y * (b : G) * t.y⁻¹) * (t.y * (a : G) * t.y⁻¹)⁻¹ := by group
  have hin : (a : G) * (b : G)⁻¹ ∈ t.d.A j ⊓ t.d.A (j + 1) := by
    refine Subgroup.mem_inf.mpr ⟨(t.d.A j).mul_mem a.2 ((t.d.A j).inv_mem b.2), ?_⟩
    rw [h2]
    exact (t.d.A (j + 1)).mul_mem hby ((t.d.A (j + 1)).inv_mem hay)
  rw [inf_A_A_succ_eq_bot t j] at hin
  have hab : (a : G) * (b : G)⁻¹ = 1 := Subgroup.mem_bot.mp hin
  exact Subtype.ext (mul_inv_eq_one.mp hab)

private theorem card_Diag (j : Fin 3) : Nat.card ↥(t.Diag j) = 3 := by
  rw [Diag, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  have hcard : Nat.card ↥(diagHom t j).range = Nat.card ↥(t.d.A j) := by
    rw [← Nat.card_range_of_injective (diagHom_injective t j)]
    rfl
  rw [hcard, t.d.card_A j]



private theorem fin_ne_succ (j : Fin 3) : j ≠ j + 1 := by
  fin_cases j <;> decide

private theorem fin_add_two_ne (j : Fin 3) : j + 2 ≠ j := by
  fin_cases j <;> decide

private theorem fin_add_two_ne_succ (j : Fin 3) : j + 2 ≠ j + 1 := by
  fin_cases j <;> decide

private theorem AA_le_M : t.d.AA ≤ c.S.M := by
  have h := c.hyp81.1
  rw [← t.hdL] at h
  exact t.d.AA_le_L.trans h

private theorem qmk_conj_y (x : ↥t.M) :
    t.qmk (yM t * x * (yM t)⁻¹) = (MulAut.conj t.ybar) (t.qmk x) := by
  simp only [MulAut.conj_apply]
  change t.qmk (yM t * x * (yM t)⁻¹) =
    t.qmk (yM t) * t.qmk x * (t.qmk (yM t))⁻¹
  rw [← map_mul, ← map_inv, ← map_mul]

private theorem qmk_mem_Lhat {i : Fin 3} {x : G} (hx : x ∈ t.d.Lf i) (hxM : x ∈ t.M) :
    t.qmk ⟨x, hxM⟩ ∈ t.Lhat i :=
  Subgroup.mem_map.mpr ⟨⟨x, hxM⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩

private theorem Diag_le_sup (j : Fin 3) : t.Diag j ≤ t.d.A j ⊔ t.d.A (j + 1) := by
  rintro x ⟨y, hy, rfl⟩
  exact y.2

private theorem inf_A_Diag_eq_bot (j : Fin 3) : t.d.A (j + 2) ⊓ t.Diag j = ⊥ := by
  refine le_antisymm ?_ bot_le
  calc t.d.A (j + 2) ⊓ t.Diag j ≤ t.d.A (j + 2) ⊓ (t.d.A j ⊔ t.d.A (j + 1)) :=
        inf_le_inf_left _ (Diag_le_sup t j)
    _ = ⊥ := by
        refine t.inf_A_sup_A_eq_bot (i := j + 2) (j := j) (k := j + 1) ?_ ?_ ?_
        · fin_cases j <;> decide
        · fin_cases j <;> decide
        · fin_cases j <;> decide



private theorem mem_Diag_iff {j : Fin 3} {d : G} :
    d ∈ t.Diag j ↔ ∃ a ∈ t.d.A j, d = a * (t.y * a * t.y⁻¹) := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hy
    exact ⟨a, a.2, diagHom_apply t j a⟩
  · rintro ⟨a, ha, rfl⟩
    refine ⟨diagHom t j ⟨a, ha⟩, ⟨⟨a, ha⟩, rfl⟩, ?_⟩
    exact diagHom_apply t j ⟨a, ha⟩

private theorem commutator_mem_R_of_qmk_fixed {R : Subgroup G}
    (hRM : R ≤ c.S.M) (hO2R : c.L ⊓ t.d.N ≤ R) {r x : G} (hr : r ∈ R)
    (hxM : x ∈ t.M)
    (hfix : (MulAut.conj (t.qmk ⟨r, hRM hr⟩)) (t.qmk ⟨x, hxM⟩) = t.qmk ⟨x, hxM⟩) :
    ⁅r, x⁆ ∈ R := by
  let rmM : ↥t.M := ⟨r, hRM hr⟩
  let xM : ↥t.M := ⟨x, hxM⟩
  have hmemKq : ⁅rmM, xM⁆ ∈ t.Kq := by
    refine (QuotientGroup.eq_one_iff _).mp ?_
    change t.qmk ⁅rmM, xM⁆ = 1
    rw [map_commutatorElement, commutatorElement_def]
    have hconj : t.qmk rmM * t.qmk xM * (t.qmk rmM)⁻¹ = t.qmk xM := by
      simpa [MulAut.conj_apply] using hfix
    rw [hconj]
    group
  have hmemG : ⁅r, x⁆ ∈ c.L ⊓ t.d.N := by
    have h := Subgroup.mem_subgroupOf.mp hmemKq
    change ⁅r, x⁆ ∈ c.L ⊓ t.d.N at h
    exact h
  exact hO2R hmemG


private theorem perm_fixed_cases (σ : Equiv.Perm (Fin 3)) (i : Fin 3) (hi : σ i = i) :
    (σ (i + 1) = i + 1 → σ = 1) ∧
      (σ (i + 1) ≠ i + 1 → σ = Equiv.swap (i + 1) ((i + 1) + 1)) := by
  fin_cases i
  · revert hi σ; decide
  · revert hi σ; decide
  · revert hi σ; decide

private theorem A_succ_succ_le_normalizer
    (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) {R : Subgroup G}
    (hRM : R ≤ c.S.M) (hR2 : IsPGroup 2 R)
    (hKR : t.Ky ≤ Subgroup.normalizer (R : Set G))
    (hO2R : c.L ⊓ t.d.N ≤ R) (i : Fin 3)
    (hi : ∀ r : ↥R, t.d.permHom t.hinj (hperm_d t)
      ⟨(r : G), t.hdM ▸ (show (r : G) ∈ t.M from hRM r.2)⟩ i = i) :
    t.d.A (i + 1 + 2) ≤ Subgroup.normalizer (R : Set G) := by
  have hRM' : R ≤ t.d.M := by rwa [t.hdM]
  let πhom : ↥t.d.M →* Equiv.Perm (Fin 3) := t.d.permHom t.hinj (hperm_d t)
  let rmD : ↥R → ↥t.d.M := fun r => ⟨(r : G), t.hdM ▸ (show (r : G) ∈ t.M from hRM r.2)⟩
  have hπR_eq : ∀ r : ↥R, πhom (rmD r) =
      (πhom.comp (Subgroup.inclusion hRM')) r := fun r => by
    apply congrArg πhom
    exact Subtype.ext rfl
  let j : Fin 3 := i + 1
  have hcases : ∀ r : ↥R,
      (πhom (rmD r) = 1 ∨ πhom (rmD r) = Equiv.swap j (j + 1)) := by
    intro r
    have hi_r : πhom (rmD r) i = i := by
      rw [hπR_eq r]
      exact hi r
    have hc := perm_fixed_cases (πhom (rmD r)) i hi_r
    by_cases hj : πhom (rmD r) j = j
    · exact Or.inl (hc.1 hj)
    · exact Or.inr (hc.2 hj)
  rw [Subgroup.le_normalizer_iff_commutator_le_left]
  refine Subgroup.commutator_le.mpr ?_
  intro r hr a ha
  have haM : a ∈ t.M := AA_le_M t (A_le_AA t (j + 2) ha)
  have hqa : t.qmk ⟨a, haM⟩ ∈ t.Lhat (j + 2) :=
    qmk_mem_Lhat t ((t.d.A_le_H (j + 2)).trans (t.d.H_le_Lf (j + 2)) ha) haM
  have hfix : (MulAut.conj (t.qmk ⟨r, hRM hr⟩)) (t.qmk ⟨a, haM⟩) = t.qmk ⟨a, haM⟩ := by
    rcases hcases ⟨r, hr⟩ with htriv | hswap
    · have hπ : ∀ m : Fin 3, πhom (rmD ⟨r, hr⟩) m = m := by
        intro m; rw [htriv]; rfl
      exact conj_fixed_mem t hK32 hGA hSp hRM hKR hR2 hr hπ hqa
    · have hπj : πhom (rmD ⟨r, hr⟩) j = j + 1 := by
        rw [hswap]; exact Equiv.swap_apply_left j (j + 1)
      have hπk : πhom (rmD ⟨r, hr⟩) (j + 1) = j := by
        rw [hswap]; exact Equiv.swap_apply_right j (j + 1)
      have hπi : πhom (rmD ⟨r, hr⟩) (j + 2) = j + 2 := by
        rw [hswap]
        exact Equiv.swap_apply_of_ne_of_ne (fin_add_two_ne j) (fin_add_two_ne_succ j)
      have hact := conj_transposition_mem t hK32 hGA hSp hRM hKR hR2 hr j hπj hπk hπi
      exact hact.2.2 (t.qmk ⟨a, haM⟩) hqa
  exact commutator_mem_R_of_qmk_fixed t hRM hO2R hr haM hfix

private theorem Diag_le_normalizer
    (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) {R : Subgroup G}
    (hRM : R ≤ c.S.M) (hR2 : IsPGroup 2 R)
    (hKR : t.Ky ≤ Subgroup.normalizer (R : Set G))
    (hO2R : c.L ⊓ t.d.N ≤ R) (i : Fin 3)
    (hi : ∀ r : ↥R, t.d.permHom t.hinj (hperm_d t)
      ⟨(r : G), t.hdM ▸ (show (r : G) ∈ t.M from hRM r.2)⟩ i = i) :
    t.Diag (i + 1) ≤ Subgroup.normalizer (R : Set G) := by
  have hRM' : R ≤ t.d.M := by rwa [t.hdM]
  let πhom : ↥t.d.M →* Equiv.Perm (Fin 3) := t.d.permHom t.hinj (hperm_d t)
  let rmD : ↥R → ↥t.d.M := fun r => ⟨(r : G), t.hdM ▸ (show (r : G) ∈ t.M from hRM r.2)⟩
  have hπR_eq : ∀ r : ↥R, πhom (rmD r) =
      (πhom.comp (Subgroup.inclusion hRM')) r := fun r => by
    apply congrArg πhom
    exact Subtype.ext rfl
  let j : Fin 3 := i + 1
  have hcases : ∀ r : ↥R,
      (πhom (rmD r) = 1 ∨ πhom (rmD r) = Equiv.swap j (j + 1)) := by
    intro r
    have hi_r : πhom (rmD r) i = i := by
      rw [hπR_eq r]
      exact hi r
    have hc := perm_fixed_cases (πhom (rmD r)) i hi_r
    by_cases hj : πhom (rmD r) j = j
    · exact Or.inl (hc.1 hj)
    · exact Or.inr (hc.2 hj)
  rw [Subgroup.le_normalizer_iff_commutator_le_left]
  refine Subgroup.commutator_le.mpr ?_
  intro r hr d hd
  obtain ⟨a0, ha0, hd_eq⟩ := (mem_Diag_iff (t := t) (j := j) (d := d)).mp hd
  have ha0M : a0 ∈ t.M := AA_le_M t (A_le_AA t j ha0)
  have hay : t.y * a0 * t.y⁻¹ ∈ t.d.A (j + 1) := by
    have h := Subgroup.mem_map_of_mem (MulAut.conj t.y).toMonoidHom ha0
    rwa [t.map_conj_A j] at h
  have hayM : t.y * a0 * t.y⁻¹ ∈ t.M := AA_le_M t (A_le_AA t (j + 1) hay)
  let a0M : ↥t.M := ⟨a0, ha0M⟩
  let ayM : ↥t.M := ⟨t.y * a0 * t.y⁻¹, hayM⟩
  have hq0 : t.qmk a0M ∈ t.Lhat j :=
    qmk_mem_Lhat t ((t.d.A_le_H j).trans (t.d.H_le_Lf j) ha0) ha0M
  have hqay : t.qmk ayM ∈ t.Lhat (j + 1) :=
    qmk_mem_Lhat t ((t.d.A_le_H (j + 1)).trans (t.d.H_le_Lf (j + 1)) hay) hayM
  have hqay_eq : t.qmk ayM = (MulAut.conj t.ybar) (t.qmk a0M) := by
    exact qmk_conj_y t a0M
  have hcommL : (t.qmk a0M) * (t.qmk ayM) = (t.qmk ayM) * (t.qmk a0M) :=
    (commute_of_mem_Lhat t j (j + 1) (fin_ne_succ j)
      (t.qmk a0M) (t.qmk ayM) hq0 hqay).eq
  have hcommL' : (MulAut.conj t.ybar) (t.qmk a0M) * (t.qmk a0M) =
      (t.qmk a0M) * (MulAut.conj t.ybar) (t.qmk a0M) := by
    rw [← hqay_eq]
    exact hcommL.symm
  have hdM : d ∈ t.M := AA_le_M t (Diag_le_AA t j hd)
  have hdM' : a0 * (t.y * a0 * t.y⁻¹) ∈ t.M :=
    c.S.M.mul_mem ha0M (c.S.M.mul_mem
      (c.S.M.mul_mem (t.hP.le t.hyP) ha0M) (c.S.M.inv_mem (t.hP.le t.hyP)))
  have hfix' : (MulAut.conj (t.qmk ⟨r, hRM hr⟩))
      (t.qmk ⟨a0 * (t.y * a0 * t.y⁻¹), hdM'⟩) =
      t.qmk ⟨a0 * (t.y * a0 * t.y⁻¹), hdM'⟩ := by
    change (MulAut.conj (t.qmk ⟨r, hRM hr⟩)) (t.qmk (a0M * ayM)) =
      t.qmk (a0M * ayM)
    rw [map_mul, map_mul]
    rcases hcases ⟨r, hr⟩ with htriv | hswap
    · have hπ : ∀ m : Fin 3, πhom (rmD ⟨r, hr⟩) m = m := by
        intro m; rw [htriv]; rfl
      rw [conj_fixed_mem t hK32 hGA hSp hRM hKR hR2 hr hπ hq0,
        conj_fixed_mem t hK32 hGA hSp hRM hKR hR2 hr hπ hqay]
    · have hπj : πhom (rmD ⟨r, hr⟩) j = j + 1 := by
        rw [hswap]; exact Equiv.swap_apply_left j (j + 1)
      have hπk : πhom (rmD ⟨r, hr⟩) (j + 1) = j := by
        rw [hswap]; exact Equiv.swap_apply_right j (j + 1)
      have hπi : πhom (rmD ⟨r, hr⟩) (j + 2) = j + 2 := by
        rw [hswap]
        exact Equiv.swap_apply_of_ne_of_ne (fin_add_two_ne j) (fin_add_two_ne_succ j)
      have hact := conj_transposition_mem t hK32 hGA hSp hRM hKR hR2 hr j hπj hπk hπi
      rw [hact.1 (t.qmk a0M) hq0, hact.2.1 (t.qmk ayM) hqay, hqay_eq,
        mulAut_conj_inv_conj t (t.qmk a0M), hcommL']
  have hd_eq' : (⟨d, hdM⟩ : ↥t.M) = ⟨a0 * (t.y * a0 * t.y⁻¹), hdM'⟩ :=
    Subtype.ext hd_eq
  have hfix : (MulAut.conj (t.qmk ⟨r, hRM hr⟩)) (t.qmk ⟨d, hdM⟩) = t.qmk ⟨d, hdM⟩ := by
    rw [hd_eq']
    exact hfix'
  exact commutator_mem_R_of_qmk_fixed t hRM hO2R hr hdM hfix


private theorem exists_rankTwo_le_normalizer
    (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) {R : Subgroup G}
    (hRM : R ≤ c.S.M) (hR2 : IsPGroup 2 R)
    (hKR : t.Ky ≤ Subgroup.normalizer (R : Set G))
    (hO2R : c.L ⊓ t.d.N ≤ R) :
    ∃ B : Subgroup G, B ≤ t.d.AA ∧ 2 ≤ CFSG.Open.pRank 3 B ∧
      B ≤ Subgroup.normalizer (R : Set G) := by
  have hRM' : R ≤ t.d.M := by rwa [t.hdM]
  let πhom : ↥t.d.M →* Equiv.Perm (Fin 3) := t.d.permHom t.hinj (hperm_d t)
  let rmD : ↥R → ↥t.d.M := fun r => ⟨(r : G), t.hdM ▸ (show (r : G) ∈ t.M from hRM r.2)⟩
  let πR : ↥R →* Equiv.Perm (Fin 3) := πhom.comp (Subgroup.inclusion hRM')
  letI : MulAction ↥R (Fin 3) := MulAction.compHom (Fin 3) πR
  obtain ⟨i, hi₀⟩ := hR2.nonempty_fixed_point_of_prime_not_dvd_card (Fin 3) (by
    rw [Nat.card_fin]; norm_num)
  have hπR_eq : ∀ r : ↥R, πhom (rmD r) = πR r := fun r => by
    apply congrArg πhom
    exact Subtype.ext rfl
  have hi : ∀ r : ↥R, πhom (rmD r) i = i := by
    intro r
    rw [hπR_eq r]
    have h := MulAction.mem_fixedPoints.mp hi₀ r
    simpa [MulAction.compHom_smul_def] using h
  let j : Fin 3 := i + 1
  let B : Subgroup G := t.d.A (j + 2) ⊔ t.Diag j
  have hBAA : B ≤ t.d.AA := sup_le (A_le_AA t (j + 2)) (Diag_le_AA t j)
  refine ⟨B, hBAA, ?_, sup_le ?_ ?_⟩
  · have hcomm : ∀ x ∈ t.d.A (j + 2), ∀ y ∈ t.Diag j, x * y = y * x :=
      fun x hx y hy => t.d.isElemAbelian_AA.comm (A_le_AA t (j + 2) hx) (Diag_le_AA t j hy)
    have hBcard : Nat.card B = 9 := by
      obtain ⟨hcard, -⟩ :=
        CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (t.d.A (j + 2)) (t.Diag j) hcomm
      rw [inf_A_Diag_eq_bot t j, Subgroup.card_bot, mul_one,
        t.d.card_A (j + 2), card_Diag t j] at hcard
      rw [hcard]
    have hBelem : CFSG.Open.IsElemAbelian 3 B := t.d.isElemAbelian_AA.mono hBAA
    have hBcard9 : Nat.card B = 3 ^ 2 := by rw [hBcard]; norm_num
    exact CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_rfl hBelem hBcard9
  · exact A_succ_succ_le_normalizer t hK32 hGA hSp hRM hR2 hKR hO2R i hi
  · exact Diag_le_normalizer t hK32 hGA hSp hRM hR2 hKR hO2R i hi


theorem kyInEta (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) {p : ℕ}
    (hp : p ∈ c.sig) (hN : t.PairNormalizerLe p)
    (hZ : Subgroup.centralizer (t.Z : Set G) ≤ c.S.M) : t.KyInEta := by
  intro R hRM hR2 hKR hO2R H hH hMH
  obtain ⟨B, hBA, hBrank, hBN⟩ :=
    t.exists_rankTwo_le_normalizer hK32 hGA hSp hRM hR2 hKR hO2R
  have hBM : B ≤ c.S.M := hBA.trans (AA_le_M t)
  have hBH : B ≤ H := (le_inf hBM hBN).trans hMH
  exact t.le_M_of_isTwoLocal_of_le_AA hp hN hZ hBA hBrank hH hBH

end CaseTwoTransitive

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
