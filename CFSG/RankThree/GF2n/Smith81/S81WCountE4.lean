module

public import CFSG.RankThree.GF2n.Smith81.S81BBridge
public import CFSG.RankThree.GF2n.Smith81.S81BConj
public import CFSG.RankThree.GF2n.Smith81.S81WConjE45
public import CFSG.RankThree.GF2n.Smith81.S81WGeomD6
public import CFSG.RankThree.GF2n.Smith81.S81WTacitE4
public import CFSG.RankThree.GF2n.Smith81.S81BLane
public import CFSG.RankThree.GF2n.Smith81.S81D6Basic

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81.D6Spin


theorem smith216ECountE4_of_inputs (hFE1 : Smith24E4UniformStatement)
    (hTacit : ETacitE4Statement) (h34 : Stroth34Statement) : Smith216ECountE4Statement := by
  intro G _ _ M Q Z B IH hc h4 z hz hz1 A C hA hC hAC hCA
  obtain ⟨y, hy⟩ := hA
  have hc' := hc.conj y
  have h4' := h4.conj y
  rw [← hy] at hc' h4'
  have hH' : StrothHyp (conjSubgroup y M) (conjSubgroup y Q) A := hc'.ctx.hyp
  have hQB : QB A = conjSubgroup y Q := by
    rw [hy, QB_conj, hc.ctx.hyp.QB_Z]
  obtain ⟨K, _, _, _, γ, M₀, hg⟩ := stroth_globalModelData hH'
  obtain ⟨ψ, φ, d⟩ := hFE1 G (conjSubgroup y M) (conjSubgroup y Q) A (conjSubgroup y B) IH
    hc'.toRemCfg h4' K γ M₀ hg
  have hB' : Ctx (conjSubgroup y M) (conjSubgroup y Q) A (conjSubgroup y B) := hc'.ctx
  have hw : Width (conjSubgroup y Q) A 16 := by
    obtain ⟨t, -, h⟩ := h4'
    exact h.1
  have hTac := hTacit G _ _ _ _ IH hc' h4'
  have hC' : Ctx (conjSubgroup y M) (conjSubgroup y Q) A C := by
    refine ⟨hH', ?_, ?_, hAC.symm⟩
    · obtain ⟨h, hh⟩ := hC
      refine ⟨h * y⁻¹, ?_⟩
      rw [hh, hy, ← conjSubgroup_mul]
      simp
    · rw [← hQB]
      exact hCA
  obtain ⟨S, hS, hSz, hScard⟩ := exists_S_of_uniform hg d d6MinuscGeom hB' hw h34 (by norm_num)
    (fun C' hC' => (hTac C' hC').1) (fun C' hC' => (hTac C' hC').2) hC'
  refine ⟨S, ?_, ?_, ?_⟩
  · rw [hQB]
    exact hS
  · intro s hs hs1
    obtain ⟨g, a, haA, ha1, rfl⟩ := hSz s hs hs1
    rw [hy, mem_conjSubgroup] at haA
    have hz₀1 : y⁻¹ * a * y ≠ 1 := by
      intro h
      apply ha1
      have : a = y * (y⁻¹ * a * y) * y⁻¹ := by group
      rw [this, h]
      group
    obtain ⟨m, -, hm⟩ := Z_isConj hc.ctx.hyp hz hz1 haA hz₀1
    refine isConj_iff.mpr ⟨g * y * m, ?_⟩
    calc g * y * m * z * (g * y * m)⁻¹ = g * y * (m * z * m⁻¹) * y⁻¹ * g⁻¹ := by group
      _ = g * y * (y⁻¹ * a * y) * y⁻¹ * g⁻¹ := by rw [hm]
      _ = g * a * g⁻¹ := by group
  · rwa [hy, card_conjSubgroup] at hScard

theorem smith216ECountE4_of_uniform (hFE1 : Smith24E4UniformStatement)
    (hGen : StrothGenByBStatement) (h34 : Stroth34Statement) : Smith216ECountE4Statement :=
  smith216ECountE4_of_inputs hFE1 (eTacitE4_of_uniform hFE1 hGen) h34

end CFSG.RankThree.GF2n.Smith81
