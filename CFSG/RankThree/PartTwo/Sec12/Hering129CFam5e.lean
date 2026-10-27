module

public import CFSG.RankThree.PartTwo.Sec12.Hering129CFamEps
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census219.M24KFact
import CFSG.RankThree.PartTwo.Sec4.Ronan148SRowM24

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint CFSG.RankThree.PartTwo.Sec4.Ronan148S

namespace Hering129C

section M24

open CFSG.AGLEmbeddingD2.Wilson.ThreeCore.M24 CFSG.AGLEmbeddingD2.Wilson.Census219
open CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.RealThree (tp_eq_of_rep)
open CFSG.Sporadic.SmallOddCore (tp)


theorem card_centralizer_m24y :
    Nat.card ↥(Subgroup.centralizer ({m24y} : Set NativeSporadic.M24)) = 1080 := by
  obtain ⟨-, ⟨e'⟩, -⟩ := m24_layer
  rw [Nat.card_congr e'.toEquiv, card_m24TcQ]

theorem m24_eps_data : ∃ F : Subgroup NativeSporadic.M24,
    F ≤ Subgroup.centralizer ({m24y} : Set NativeSporadic.M24) ∧
      CFSG.Assembly.IsElemAbelian 3 F ∧ Nat.card F = 9 ∧ m24y ∈ F ∧
      ∃ n ∈ Subgroup.normalizer (F : Set NativeSporadic.M24),
        n ∉ Subgroup.normalizer (Subgroup.zpowers m24y : Set NativeSporadic.M24) := by
  obtain ⟨hc, hf1, hf2, hf3, hnf⟩ := m24N0_facts
  rw [← m24y_eq] at hc hf1 hf2 hf3 hnf
  set f := m24N0 * m24y * m24N0⁻¹ with hf
  have hy3 : m24y ^ 3 = 1 := by rw [m24y_eq]; exact Sec4.RonanK432.m24RA_pow_three
  have hy1 : m24y ≠ 1 := by
    intro h
    apply hf1
    rw [hf, h]
    group
  have hfy3 : f ^ 3 = 1 := by rw [hf, conj_pow, hy3]; group
  have hfs := not_mem_zpowers_of_ne hy3 hf1 hf2 hf3
  obtain ⟨hE, hE9⟩ := e9_of_commute hy3 hy1 hfy3 hc.symm hfs
  obtain ⟨hn, hns⟩ := move_of_conj hfs rfl hnf
  refine ⟨Subgroup.zpowers m24y ⊔ Subgroup.zpowers f, ?_, hE, hE9,
    Subgroup.mem_sup_left (Subgroup.mem_zpowers _), m24N0, hn, hns⟩
  exact sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl))
    (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hc))

theorem kFCensus46Five_M24 :
    KFCensusOn (fun Q _ => Nonempty (Q ≃* NativeSporadic.Carrier .M24)) := by
  intro Q Lb _ _ _ c a I X f hQ hD
  exfalso
  obtain ⟨e0⟩ := hQ
  let e : Q ≃* NativeSporadic.M24 := e0
  set s : NativeSporadic.M24 := e c with hs
  have hord : orderOf (s : Equiv.Perm (Fin 24)) = 3 := by
    rw [Subgroup.orderOf_coe, hs, MulEquiv.orderOf_eq]
    exact hD.orderOf_c
  obtain ⟨r, hr, g, hg, hgr⟩ := m24_cover s.2 hord
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  set gP : NativeSporadic.M24 := ⟨g, hg⟩ with hgP
  set φ : NativeSporadic.M24 ≃* NativeSporadic.M24 := MulAut.conj gP⁻¹ with hφ
  have hφs : ((φ s : NativeSporadic.M24) : Equiv.Perm (Fin 24)) = tp 24 r.rep := by
    have : ((φ s : NativeSporadic.M24) : Equiv.Perm (Fin 24)) =
        g⁻¹ * (s : Equiv.Perm (Fin 24)) * g := by
      simp [hφ, hgP, MulAut.conj_apply]
    rw [this, hgr]
    group
  set ψ : Q ≃* NativeSporadic.M24 := e.trans φ with hψ
  have hψc : ψ c = φ s := rfl
  haveI : Finite NativeSporadic.M24 := Finite.of_equiv Q ψ.toEquiv
  obtain ⟨g', hg'⟩ := (ppair_self hD).map ψ
  rcases hr with rfl | rfl
  ·
    have hφy : φ s = m24y := Subtype.ext hφs
    have hψy : ψ c = m24y := hψc.trans hφy
    rw [hψy] at hg'
    have hJC := hg'.eq_centralizer_of_card (M := 1080) (B := 11) card_centralizer_m24y
      (by norm_num) (by norm_num) (by decide +kernel)
    obtain ⟨F, hFC, hFe, hF9, hxF, n, hn, hns⟩ := m24_eps_data
    exact census_false_of_eps_model hD ψ hψy F (hFC.trans hJC.symm.le) hFe hF9 hxF n hn hns
  ·
    have hcard : Nat.card ↥(Subgroup.centralizer ({φ s} : Set NativeSporadic.M24)) = 504 :=
      card_centralizer_m24B hφs
    rw [← hψc] at hcard
    exact hg'.false_of_card_dvd (M := 504) (B := 8) (by norm_num) (by norm_num)
      (by decide +kernel) hcard.dvd

end M24

end Hering129C

end CFSG.RankThree.PartTwo.Sec12
