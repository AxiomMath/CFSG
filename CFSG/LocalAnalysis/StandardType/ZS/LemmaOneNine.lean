module

public import CFSG.LocalAnalysis.StandardType.ZS.LemmaOneNineCentral
public import CFSG.LocalAnalysis.StandardType.ZS.LemmaOneNineCore

public section

namespace CFSG.StandardType.ZS

theorem centreOrderBound_of_primitive {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] [Module.Finite (ZMod p) U] {G : Subgroup (U ≃ₗ[ZMod p] U)}
    (htv : QTwoLin.TransvectionFree G) (habs : AbsIrred p G)
    (hprim : ¬ Quasithin.SimsG4.IsImprimitiveOnV G) :
    ∀ X ≤ G, ReflGen p X → SplitSupport X (Module.finrank (ZMod p) U - 1) →
      ∀ z ∈ X, (∀ x ∈ X, z * x = x * z) → orderOf z ≤ 3 := by
  intro X hXG hXgen hs z hz hzc
  have hn : Module.finrank (ZMod p) U - 1 = 0 ∨ Module.finrank (ZMod p) U - 1 = 1 ∨
      3 ≤ Module.finrank (ZMod p) U := by omega
  rcases hn with h0 | h1 | h3
  · have hs0 : SplitSupport X 0 := by rwa [h0] at hs
    rw [eq_one_of_splitSupport_zero hs0 hz, orderOf_one]
    norm_num
  · have hs1 : SplitSupport X 1 := by rwa [h1] at hs
    have hzz : z * z = 1 := mul_self_eq_one_of_splitSupport_one hXgen hs1 hz
    have hpow : z ^ 2 = 1 := by rwa [pow_two]
    have hdvd : orderOf z ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hpow
    have hle : orderOf z ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  · obtain ⟨τ, g, c, φ, hgHull, hhom, hord⟩ :=
      exists_isHomologyWith_of_mem_center hXgen hs hz hzc
    have hgG : g ∈ scalarHull G := scalarHull_mono hXG hgHull
    have hb := orderOf_le_three_of_isHomologyWith (H := scalarHull G) h3
      (irreducible_scalarHull (G := G) habs.1)
      (transvectionFree_scalarHull (G := G) htv)
      (not_isImprimitiveOnV_scalarHull (G := G) hprim) hgG hhom
    rw [hord]
    exact hb

end CFSG.StandardType.ZS

end
