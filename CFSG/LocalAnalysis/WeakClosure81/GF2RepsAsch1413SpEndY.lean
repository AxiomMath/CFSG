module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714Sp4Aux
public import CFSG.Quasithin.Background.F6SQTK

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch1413

open CFSG.Quasithin CFSG.ComponentClassification.CatFactsSp4 CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial SymplecticHigher SymplecticFlag Subgroup
open scoped Matrix

private theorem a1413SpEndY_ringChar_ne_two_of_odd_card {K : Type} [Field K] [Finite K]
    (h : Odd (Nat.card K)) : ringChar K ≠ 2 := by
  intro hc
  haveI : Fintype K := Fintype.ofFinite K
  have h2 := (FiniteField.even_card_iff_char_two (F := K)).mp hc
  rw [← Nat.card_eq_fintype_card] at h2
  exact (Nat.not_even_iff_odd.mpr h) (Nat.even_iff.mpr h2)

private theorem a1413SpEndY_negOne_fix {K : Type} [Field K] (B : gsp 2 K) :
    toSp (-1) neg_one_symplectic ∈ fixOf (conjSp 2 K B) := by
  have hz : toSp (-1) neg_one_symplectic ∈ spScalars 2 K :=
    (mem_spScalars_iff _).mpr (Or.inr rfl)
  have hz' := Subgroup.mem_subgroupOf.mp hz
  rw [CFSG.Open.StatedAPI.statedScalars_eq_center] at hz'
  have hcomm := Subgroup.mem_center_iff.mp hz' (B : GL (Fin 2 ⊕ Fin 2) K)
  rw [mem_fixOf]
  exact Subtype.ext (by rw [coe_conjSp, hcomm, mul_inv_cancel_right])

private theorem a1413SpEndY_map_ker_eq_center {K : Type} [Field K] (B : gsp 2 K)
    (hchar : ringChar K ≠ 2) {E : Type} [Field E]
    (φ : ↥(fixOf (conjSp 2 K B)) ≃* Matrix.SpecialLinearGroup (Fin 2) E) :
    Subgroup.map (φ : ↥(fixOf (conjSp 2 K B)) →* Matrix.SpecialLinearGroup (Fin 2) E)
        ((spScalars 2 K).subgroupOf (fixOf (conjSp 2 K B))) =
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) E) := by
  have hZle : (spScalars 2 K).subgroupOf (fixOf (conjSp 2 K B)) ≤
      Subgroup.center (fixOf (conjSp 2 K B)) := by
    rw [← ker_fixProj (conjSp 2 K B)]
    exact ker_fixProj_le_center (conjSp 2 K B)
  have hle : Subgroup.map (φ : ↥(fixOf (conjSp 2 K B)) →*
        Matrix.SpecialLinearGroup (Fin 2) E)
        ((spScalars 2 K).subgroupOf (fixOf (conjSp 2 K B))) ≤
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) E) := by
    rw [← Subgroup.map_center_eq φ]
    exact Subgroup.map_mono hZle
  apply le_antisymm hle
  intro x hx
  rcases eq_one_or_neg_of_mem_center hx with hm | hm
  · have hx1 : x = 1 := Subtype.ext hm
    rw [hx1]
    exact Subgroup.mem_map.mpr ⟨1, Subgroup.one_mem _,
      map_one (φ : ↥(fixOf (conjSp 2 K B)) →* Matrix.SpecialLinearGroup (Fin 2) E)⟩
  · have hxn : x = -1 := Subtype.ext hm
    rw [hxn]
    let z0 : StatedSp 2 K := toSp (-1) neg_one_symplectic
    have hz0Y : z0 ∈ fixOf (conjSp 2 K B) := a1413SpEndY_negOne_fix B
    have hz0sp : z0 ∈ spScalars 2 K :=
      (mem_spScalars_iff z0).mpr (Or.inr (coe_toSp (-1) neg_one_symplectic))
    have hz0Z : (⟨z0, hz0Y⟩ : ↥(fixOf (conjSp 2 K B))) ∈
        (spScalars 2 K).subgroupOf (fixOf (conjSp 2 K B)) :=
      Subgroup.mem_subgroupOf.mpr hz0sp
    have hz0mem : φ ⟨z0, hz0Y⟩ ∈ Subgroup.map (φ : ↥(fixOf (conjSp 2 K B)) →*
        Matrix.SpecialLinearGroup (Fin 2) E)
        ((spScalars 2 K).subgroupOf (fixOf (conjSp 2 K B))) :=
      Subgroup.mem_map.mpr ⟨⟨z0, hz0Y⟩, hz0Z, rfl⟩
    have hz0cent : φ ⟨z0, hz0Y⟩ ∈
        Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) E) := hle hz0mem
    have hz0ne : φ ⟨z0, hz0Y⟩ ≠ 1 := by
      intro h
      have hz01 : (⟨z0, hz0Y⟩ : ↥(fixOf (conjSp 2 K B))) = 1 :=
        φ.injective (by rw [h, map_one])
      have hz0one : z0 = 1 := by simpa using Subtype.ext_iff.mp hz01
      have hmat : (-1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1 := by
        have h2 : ((z0 : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) = 1 := by
          rw [hz0one]
          rfl
        have h3 := congrArg (fun u : GL (Fin 2 ⊕ Fin 2) K =>
          (u : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) h2
        simpa [z0, coe_toSp] using h3
      have hdiag : (-1 : K) = 1 := by
        simpa using congrFun (congrFun hmat (Sum.inl 0)) (Sum.inl 0)
      exact Ring.neg_one_ne_one_of_char_ne_two hchar hdiag
    rcases eq_one_or_neg_of_mem_center hz0cent with hm1 | hm2
    · exact absurd (Subtype.ext hm1) hz0ne
    · exact Subgroup.mem_map.mpr ⟨⟨z0, hz0Y⟩, hz0Z, Subtype.ext hm2⟩

private theorem a1413SpEndY_iso {K : Type} [Field K] (B : gsp 2 K) (hchar : ringChar K ≠ 2)
    {E : Type} [Field E]
    (φ : ↥(fixOf (conjSp 2 K B)) ≃* Matrix.SpecialLinearGroup (Fin 2) E) :
    Nonempty (↥((fixOf (conjSp 2 K B)).map (proj 2 K)) ≃* StatedProj (StatedSL 2 E)) := by
  have hmap := a1413SpEndY_map_ker_eq_center B hchar φ
  haveI : ((spScalars 2 K).subgroupOf (fixOf (conjSp 2 K B))).Normal :=
    Subgroup.normal_of_le_center (by
      rw [← ker_fixProj (conjSp 2 K B)]
      exact ker_fixProj_le_center (conjSp 2 K B))
  have hker : ((proj 2 K).subgroupMap (fixOf (conjSp 2 K B))).ker =
      (spScalars 2 K).subgroupOf (fixOf (conjSp 2 K B)) := ker_fixProj (conjSp 2 K B)
  have hsurj : Function.Surjective ((proj 2 K).subgroupMap (fixOf (conjSp 2 K B))) :=
    (proj 2 K).subgroupMap_surjective (fixOf (conjSp 2 K B))
  exact ⟨((QuotientGroup.quotientKerEquivOfSurjective
      ((proj 2 K).subgroupMap (fixOf (conjSp 2 K B))) hsurj).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hker)).trans
    ((QuotientGroup.congr ((spScalars 2 K).subgroupOf (fixOf (conjSp 2 K B)))
        (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) E)) φ hmap).trans
      (projectiveSpecialLinearGroupEquivStatedProj 2 E))⟩

theorem sp4_Y_of_B {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p) (B : gsp 2 K) {d : K} (hd0 : d ≠ 0) (hdsq : ∀ l : K, l ^ 2 ≠ d)
    (hBB : ((B : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((B : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = d • 1)
    (hμ : ((B : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ * formJ 2 K *
      ((B : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = d • formJ 2 K) :
    F6.IsL2 p 2 ↥((fixOf (conjSp 2 K B)).map (proj 2 K)) := by
  have hK' : Nat.card K = p ^ 1 := by rw [pow_one]; exact hK
  obtain ⟨E, hEfield, hEfinite, hEcard, ⟨φ⟩⟩ :=
    ivk714_fixOf_conjSp_nonsquare_sl2 hp hp2 le_rfl hK' B hd0 hdsq hBB hμ
  letI : Field E := hEfield
  letI : Finite E := hEfinite
  have hEcard2 : Nat.card E = p ^ 2 := by rw [hEcard, pow_one]
  have hoddK : Odd (Nat.card K) := by rw [hK]; exact hp.odd_of_ne_two hp2
  have hchar : ringChar K ≠ 2 := a1413SpEndY_ringChar_ne_two_of_odd_card hoddK
  have hp3 : 3 ≤ p := by
    have h2 := hp.two_le
    omega
  refine ⟨⟨hp, by norm_num, by norm_num, ?_, ?_⟩, E, inferInstance, inferInstance, hEcard2,
    a1413SpEndY_iso B hchar φ⟩
  · intro h
    have h2 := congrArg Prod.snd h
    have h9 : 9 ≤ p ^ 2 := by nlinarith
    omega
  · intro h
    have h2 := congrArg Prod.snd h
    have h9 : 9 ≤ p ^ 2 := by nlinarith
    omega

end CFSG.LocalAnalysis.WeakClosure81.Asch1413

end
