module

public import CFSG.RankThree.PartTwo.Sec12.Hering129CFamEps
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RHe

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint CFSG.RankThree.PartTwo.Sec4.Ronan148S CFSG.RankThree.PartTwo.Sec4.Ronan148R

namespace Hering129C

section He

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.HeldB
open CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He CFSG.AGLEmbeddingD2.Wilson.Census219

theorem he_eps_data
    (hy3 : heY ^ 3 = 1) :
    ∃ F : Subgroup heP, F ≤ Subgroup.centralizer ({heY} : Set heP) ∧
      CFSG.Assembly.IsElemAbelian 3 F ∧ Nat.card F = 9 ∧ heY ∈ F ∧
      ∃ n ∈ Subgroup.normalizer (F : Set heP),
        n ∉ Subgroup.normalizer (Subgroup.zpowers heY : Set heP) := by
  obtain ⟨hc, hf1, hf2, hf3, hnf⟩ := heN0_facts
  obtain ⟨nP, hnv⟩ : ∃ nP : heP, (nP : Equiv.Perm (Fin 8330)) = heN0 := ⟨⟨heN0, heN0_mem⟩, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : heP, f = nP * heY * nP⁻¹ := ⟨_, rfl⟩
  have hyv : (heY : Equiv.Perm (Fin 8330)) = bOf heThreeWordsA := rfl
  have hfv : (f : Equiv.Perm (Fin 8330)) = heN0 * bOf heThreeWordsA * heN0⁻¹ := by
    rw [hf, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hnv, hyv]
  have hy1 : heY ≠ 1 := by
    intro h
    apply hf1
    rw [← hyv, h]
    simp
  have hyinv : heY⁻¹ = heY * heY := by
    rw [inv_eq_iff_mul_eq_one, ← pow_three]
    exact hy3
  have hc' : heY * f = f * heY := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hfv, hyv]
    exact hc.symm
  have hf1' : f ≠ 1 := fun h => hf1 (by rw [← hfv, h]; rfl)
  have hf2' : f ≠ heY := fun h => hf2 (by rw [← hfv, h, hyv])
  have hf3' : f ≠ heY⁻¹ := by
    intro h
    apply hf3
    rw [← hfv, h, hyinv, Subgroup.coe_mul, hyv]
  have hnf' : nP * f * nP⁻¹ = heY * f := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul, hfv, hyv, hnv]
    exact hnf
  have hfy3 : f ^ 3 = 1 := by rw [hf, conj_pow, hy3]; group
  have hfs := not_mem_zpowers_of_ne hy3 hf1' hf2' hf3'
  obtain ⟨hE, hE9⟩ := e9_of_commute hy3 hy1 hfy3 hc' hfs
  obtain ⟨hn, hns⟩ := move_of_conj hfs hf.symm hnf'
  refine ⟨Subgroup.zpowers heY ⊔ Subgroup.zpowers f, ?_, hE, hE9,
    Subgroup.mem_sup_left (Subgroup.mem_zpowers _), nP, hn, hns⟩
  exact sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl))
    (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hc'.symm))

theorem kFCensus46Five_He :
    KFCensusOn (fun Q _ => Nonempty (Q ≃* NativeSporadic.Carrier .He)) := by
  intro Q Lb _ _ _ c a I X f hQ hD
  exfalso
  obtain ⟨e0⟩ := hQ
  let e : Q ≃* NativeSporadic.He := e0
  let ψ0 : Q ≃* heP := e.trans heEquivP
  haveI : Finite heP := Finite.of_equiv Q ψ0.toEquiv
  set s : heP := ψ0 c with hs
  have hord : orderOf (s : Equiv.Perm (Fin 8330)) = 3 := by
    rw [Subgroup.orderOf_coe, hs, MulEquiv.orderOf_eq]
    exact hD.orderOf_c
  rcases three_conj_cases s.2 hord with ⟨cc, hc, hcx⟩ | ⟨cc, hc, hcx⟩
  ·
    set gP : heP := ⟨cc, hc⟩ with hgP
    set φ : heP ≃* heP := MulAut.conj gP⁻¹ with hφ
    have hφs : φ s = heY := by
      apply Subtype.ext
      have h1 : ((φ s : heP) : Equiv.Perm (Fin 8330)) =
          cc⁻¹ * (s : Equiv.Perm (Fin 8330)) * cc := by
        simp [hφ, hgP, MulAut.conj_apply]
      rw [h1, hcx]
      show cc⁻¹ * (cc * bOf heThreeWordsA * cc⁻¹) * cc = bOf heThreeWordsA
      group
    set ψ : Q ≃* heP := ψ0.trans φ with hψ
    have hψy : ψ c = heY := hφs
    obtain ⟨-, ⟨e''⟩, -⟩ := he_layer
    have hCq : CFSG.IsQuasisimple ↥(Subgroup.centralizer ({heY} : Set heP)) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv e''.symm heTc_spec.2.1
    have hJC := census_map_eq_centralizer_of_quasisimple hD ψ hψy hCq
    have hy3 : heY ^ 3 = 1 := by
      rw [← hψy, ← map_pow, c_pow_three hD, map_one]
    obtain ⟨F, hFC, hFe, hF9, hxF, n, hn, hns⟩ := he_eps_data hy3
    exact census_false_of_eps_model hD ψ hψy F (hFC.trans hJC.symm.le) hFe hF9 hxF n hn hns
  ·
    set gP : heP := ⟨cc, hc⟩ with hgP
    set φ : heP ≃* heP := MulAut.conj gP⁻¹ with hφ
    have hφs : ((φ s : heP) : Equiv.Perm (Fin 8330)) = bOf heThreeWordsB := by
      have h1 : ((φ s : heP) : Equiv.Perm (Fin 8330)) =
          cc⁻¹ * (s : Equiv.Perm (Fin 8330)) * cc := by
        simp [hφ, hgP, MulAut.conj_apply]
      rw [h1, hcx]
      group
    have hcard : Nat.card ↥(Subgroup.centralizer ({φ s} : Set heP)) = 504 := by
      rw [card_centralizer_heP, hφs]
      exact card_cent_B
    obtain ⟨g', hg'⟩ := (ppair_self hD).map (ψ0.trans φ)
    exact hg'.false_of_card_dvd (M := 504) (B := 8) (by norm_num) (by norm_num)
      (by decide +kernel) hcard.dvd

end He

end Hering129C

end CFSG.RankThree.PartTwo.Sec12
