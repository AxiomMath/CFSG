module

public import CFSG.RankThree.GF2n.Smith81.S81BTacitFree
public import CFSG.RankThree.GF2n.Smith81.S81UMinusc
public import CFSG.RankThree.GF2n.Smith81.S81UConj
public import CFSG.RankThree.GF2n.Smith81.S81BConj

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom

theorem smith216ECountE3U_of_inputs
    (hFE1 : Smith24E3UUniformStatement)
    (hTacit : ETacitE3UStatement) (h34 : Stroth34Statement) :
    Smith216ECountE3UStatement := by
  intro G _ _ M Q Z B IH hc h3U z hz hz1 A C hA hC hAC hCA
  obtain ⟨y, hy⟩ := hA
  have hc' := hc.conj y
  have h3U' := h3U.conj y
  rw [← hy] at hc' h3U'
  have hH' : StrothHyp (conjSubgroup y M) (conjSubgroup y Q) A := hc'.ctx.hyp
  have hQB : QB A = conjSubgroup y Q := by
    rw [hy, QB_conj, hc.ctx.hyp.QB_Z]
  obtain ⟨K, _, _, _, γ, M₀, hg⟩ := stroth_globalModelData hH'
  obtain ⟨F, _, _, _, f, hF, e, ψ, φ, d⟩ := hFE1 G (conjSubgroup y M) (conjSubgroup y Q) A (conjSubgroup y B) IH
    hc'.toRemCfg h3U' K γ M₀ hg
  have hB' : Ctx (conjSubgroup y M) (conjSubgroup y Q) A (conjSubgroup y B) := hc'.ctx
  have hw : Width (conjSubgroup y Q) A 10 := by
    obtain ⟨t, -, h⟩ := h3U'
    exact h.1
  have hTac := hTacit G _ _ _ _ IH hc' h3U'
  have hC' : Ctx (conjSubgroup y M) (conjSubgroup y Q) A C := by
    refine ⟨hH', ?_, ?_, hAC.symm⟩
    · obtain ⟨h, hh⟩ := hC
      refine ⟨h * y⁻¹, ?_⟩
      rw [hh, hy, ← conjSubgroup_mul]
      simp
    · rw [← hQB]
      exact hCA
  obtain ⟨S, hS, hSz, hScard⟩ := exists_S_of_uniform hg d (u6MinuscStatement_holds F f hF K e).1 hB' hw h34 (by norm_num)
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

end CFSG.RankThree.GF2n.Smith81
