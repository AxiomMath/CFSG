module

public import CFSG.RankThree.PartTwo.Sec19.SeitzFieldTwoU1
public import CFSG.RankThree.PartTwo.Sec19.SeitzFieldTwoU9

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG.LieType.SeitzGeneration CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartTwo.KFacts

theorem three_ne_zero_of_unitaryFieldData {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) (hQ : p ^ f % 3 = 2) : (3 : K) ≠ 0 := by
  intro h3
  haveI := h.charP
  have h3' : ((3 : ℕ) : K) = 0 := by exact_mod_cast h3
  rw [CharP.cast_eq_zero_iff K p] at h3'
  have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_three).1 h3'
  subst hp3
  obtain ⟨k, rfl⟩ : ∃ k, f = k + 1 := ⟨f - 1, by have := h.one_le; omega⟩
  have h0 : 3 ^ (k + 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd (dvd_pow_self 3 (Nat.succ_ne_zero k))
  rw [h0] at hQ
  norm_num at hQ

@[expose] noncomputable def descPSUHom {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (hq : 2 < p ^ f) : MulAut (unitarySU p f K 3) →* MulAut (unitaryPSU h 3) :=
  (MulAut.congr (suCenterEquiv h hq)).toMonoidHom.comp (centerDescend _)

theorem descPSUHom_suConj {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (hq : 2 < p ^ f) (A : unitaryIsom3 h) :
    descPSUHom h hq (suConj h A) = psuConj h A :=
  CFSG.RankThree.PartTwo.Sec4.congr_centerDescend_suConj h hq A

theorem descPSUHom_suField {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (hq : 2 < p ^ f) (σ : K ≃+* K) :
    descPSUHom h hq (suField h σ) = psuField h σ :=
  CFSG.RankThree.PartTwo.Sec4.congr_centerDescend_suField h hq σ

theorem descPSUHom_injective {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (hq : 2 < p ^ f) : Function.Injective (descPSUHom h hq) := by
  intro α β hαβ
  exact Item19Res6Proof.eq_of_descend_eq (h := h) hq (φ := α) (ψ := β) hαβ

theorem planeGen_of_closure_fixSet {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (hq : 2 < p ^ f) {E : Subgroup (MulAut (unitaryPSU h 3))}
    (D : Subgroup (MulAut (unitarySU p f K 3))) (hDle : D ≤ E.comap (descPSUHom h hq))
    (hcl : Subgroup.closure (CFSG.LocalAnalysis.RankThreeTheoremC.SL3CoverGen.fixSet D) = ⊤) :
    PlaneGen E := by
  have hinj := descPSUHom_injective h hq
  have hfix : ∀ s ∈ CFSG.LocalAnalysis.RankThreeTheoremC.SL3CoverGen.fixSet D,
      unitaryProj h 3 s ∈ planeClosure E := by
    intro s hs
    obtain ⟨d, hdD, hd1, hds⟩ := hs
    apply mem_planeClosure_of_fixed (e := descPSUHom h hq d) (hDle hdD)
    · intro he
      apply hd1
      apply hinj
      rw [he, map_one]
    · have hk : descPSUHom h hq d (unitaryProj h 3 s) = unitaryProj h 3 (d s) := rfl
      rw [hk, hds]
  have hsub : Subgroup.closure
      (unitaryProj h 3 '' CFSG.LocalAnalysis.RankThreeTheoremC.SL3CoverGen.fixSet D) ≤
        planeClosure E := by
    rw [Subgroup.closure_le]
    rintro _ ⟨s, hs, rfl⟩
    exact hfix s hs
  have hmap : Subgroup.closure
      (unitaryProj h 3 '' CFSG.LocalAnalysis.RankThreeTheoremC.SL3CoverGen.fixSet D) = ⊤ := by
    rw [← MonoidHom.map_closure, hcl, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.2 (unitaryProj_surjective h 3)]
  rw [hmap] at hsub
  exact top_le_iff.1 hsub

theorem planeGen_unitaryPSU_field {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) (hQ : p ^ f % 3 = 2) (hq : 2 < p ^ f) (hQ8 : p ^ f ≠ 8)
    {E : Subgroup (MulAut (unitaryPSU h 3))} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hc : Nat.card E = 9) (hN : ¬ NarrowScope 3 E) : PlaneGen E := by
  have := h.finite
  have h3 := three_ne_zero_of_unitaryFieldData h hQ
  have hnot := not_le_psuConj_range_of_not_narrow h3 hq hE hN
  obtain ⟨φ, hφE, hφN⟩ := SetLike.not_le_iff_exists.1 hnot
  obtain ⟨y, hyE, hyN, hy1⟩ := exists_ne_one_inf_psuConj_range h3 hq hE hc hnot
  obtain ⟨σ, -, H, hφH⟩ := unitary_order_three_field_descent hq φ (hE.2 φ hφE) hφN
  obtain ⟨B, hB⟩ := hyN
  have hD3 : ∀ d ∈ E.comap (descPSUHom h hq), d ^ 3 = 1 := by
    intro d hd
    apply descPSUHom_injective h hq
    rw [map_pow, map_one]
    exact hE.2 _ (Subgroup.mem_comap.1 hd)
  have hφt_desc : descPSUHom h hq (suConj h H * suField h σ * (suConj h H)⁻¹) = φ := by
    rw [map_mul, map_mul, map_inv, descPSUHom_suConj, descPSUHom_suField]
    exact hφH.symm
  have hyt_desc : descPSUHom h hq (suConj h B) = y := by
    rw [descPSUHom_suConj]
    exact hB
  have hφtD : suConj h H * suField h σ * (suConj h H)⁻¹ ∈ E.comap (descPSUHom h hq) :=
    Subgroup.mem_comap.2 (by rw [hφt_desc]; exact hφE)
  have hytD : suConj h B ∈ E.comap (descPSUHom h hq) :=
    Subgroup.mem_comap.2 (by rw [hyt_desc]; exact hyE)
  have hφtN : suConj h H * suField h σ * (suConj h H)⁻¹ ∉ (suConj h).range := by
    rintro ⟨C, hC⟩
    apply hφN
    refine ⟨C, ?_⟩
    rw [← hφt_desc, ← hC, descPSUHom_suConj]
  have hyt1 : suConj h B ≠ 1 := by
    intro h1
    apply hy1
    rw [← hyt_desc, h1, map_one]
  have hytN : suConj h B ∈ (suConj h).range := ⟨B, rfl⟩
  have hfix := closure_fixSet_eq_top_of_field_gen h hQ hq hQ8 (E.comap (descPSUHom h hq)) hD3
    hφtD hφtN hytD hyt1 hytN
  exact planeGen_of_closure_fixSet h hq (E.comap (descPSUHom h hq)) le_rfl hfix

end CFSG.RankThree.PartTwo.Sec19
