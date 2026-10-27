module

public import CFSG.Quasithin.Vol2.Ch11G2Q8CartanW
public import CFSG.Quasithin.Vol2.Ch11SecAFacts15b

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.KGNat Matrix
open CFSG.Quasithin.Vol2.Ch11.G2Q8
open CFSG.Quasithin.Vol2.Ch11.SecS (gammaW)
open CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A (pCoreOf_map_of_injective)

namespace KC2

variable {F : Type} [Field F] [CharP F 2]

theorem mem_stdF_one_of_fix3 {x : Ix3 → F} (h1 : g2Act (g2X ![(1 : F), 0, 0]) x = x)
    (h2 : g2Act (g2Y ![0, (1 : F), 0]) x = x) (h3 : g2Act (g2Y ![0, 0, (1 : F)]) x = x) :
    x ∈ stdF F 1 := by
  rw [q6_eta x, g2Act_x0q] at h1
  rw [q6_eta x, g2Act_y12q] at h2 h3
  obtain ⟨e0, -, -, -, e4, e5⟩ := q6_inj h1
  obtain ⟨f0, -, -, -, -, -⟩ := q6_inj h2
  obtain ⟨g0, -, -, -, -, -⟩ := q6_inj h3
  rw [mem_stdF]
  conv => rw [q6_eta x]
  rw [inF_q6_iff]
  refine ⟨by omega, fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_⟩
  · linear_combination e5
  · linear_combination e4
  · linear_combination e0
  · linear_combination g0
  · linear_combination f0

end KC2

open KC2 in
theorem factRadicalFixedG2_holds : FactRadicalFixedG2 := by
  intro K _ _ n hn hK W _ _ hW H Z π hπ P hP U hU
  have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
  have : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  have := finite_cayleyGroup (F := K)
  have h4 := four_le_card hn hK
  obtain ⟨c₀, hc0, hc1⟩ := exists_ne_zero_ne_one_of_card hn hK
  obtain ⟨f, hf⟩ := exists_isCoord (lmG K) hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_U0 hK (by omega) hf hc0 hc1 hP
  have hU1 := eq_U1_of_isFlagWG hW hf hc0 hc1 hg (by rw [hK]; exact hU)
  subst hU1
  have hψ := psiG_injective hf hc0 hc1 g
  intro w hw
  have key : ∀ γ ∈ stabV0 K, levi1Mat γ = 1 → psiG hc0 hc1 π g γ w * w⁻¹ ∈ Z := by
    intro γ hγ hl
    have hmem : psiG hc0 hc1 π g γ ∈
        pCoreOf 2 (gammaW H (hf.pre (gmapG g (stdF K 1)).toAddSubgroup)) := by
      rw [gammaW_one_eqG h4 hf hc0 hc1 g, pCoreOf_map_of_injective _ hψ]
      exact ⟨γ, mem_pCoreOf_stabV0_iff.mpr ⟨hγ, hl⟩, rfl⟩
    obtain ⟨y, hy, hyeq⟩ := hmem
    have h := hw y (by exact hy)
    rwa [← hyeq]
  have hfix : ∀ γ ∈ stabV0 K, levi1Mat γ = 1 →
      g2Act γ (g2Act g⁻¹ (f w)) = g2Act g⁻¹ (f w) := by
    intro γ hγ hl
    have h := key γ hγ hl
    rw [← hf.ker, hf.map_mul_inv, psiG_apply, IsCoord.actG hf hc0 hc1, sub_eq_zero] at h
    have h2 := congrArg (g2Act g⁻¹) h
    rwa [g2Act_mul_apply, g2Act_mul_apply, g2Act_inv_apply] at h2
  have hx := mem_stdF_one_of_fix3 (hfix _ (g2X_e0_mem_stabV0 1) (levi1Mat_g2X 1))
    (hfix _ (g2Y_mem_stabV0 1 0) (levi1Mat_g2Y 1 0))
    (hfix _ (g2Y_mem_stabV0 0 1) (levi1Mat_g2Y 0 1))
  change f w ∈ gmapG g (stdF K 1)
  rw [mem_gmapG]
  exact hx

end CFSG.Quasithin.Vol2.Ch11.SecA
