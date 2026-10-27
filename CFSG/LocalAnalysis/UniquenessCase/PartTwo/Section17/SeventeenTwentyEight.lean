module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSevenA
public import CFSG.LocalAnalysis.WeakClosure81.W19Struct

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Open CFSG.Quasithin
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem gam_eq_gammaSet (i : ℕ) (X V : Subgroup G) (hV : IsElemAbelian 2 V) :
    CFSG.LocalAnalysis.UniquenessCase.UC22.F12.Gam i X V =
      CFSG.Quasithin.E3.gammaSet V i X := by
  ext A
  constructor
  · rintro ⟨hAX, U, g, hUV, hcard, rfl⟩
    refine ⟨hAX, g⁻¹, ?_, ?_⟩
    · simpa [conjSubgroup] using Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hUV
    · have hVg : IsPGroup 2 (conjSubgroup V g⁻¹) :=
        (CFSG.Quasithin.B2F.isPGroup_of_isElemAbelian hV).map _
      have hAg : U.map (MulAut.conj g).toMonoidHom ≤ conjSubgroup V g⁻¹ := by
        simpa [conjSubgroup] using Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hUV
      have hcm := CFSG.Quasithin.E3.card_eq_two_pow_mul hVg hAg
      have hcardg : Nat.card (conjSubgroup V g⁻¹) = Nat.card V := by
        simpa [conjSubgroup] using Subgroup.card_map_of_injective
          (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
      have hcardA : Nat.card (U.map (MulAut.conj g).toMonoidHom) = Nat.card U :=
        Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
          (MulAut.conj g).injective
      rw [hcardg, hcardA] at hcm
      have hEq : 2 ^ CFSG.Quasithin.E3.mQuot (conjSubgroup V g⁻¹)
          (U.map (MulAut.conj g).toMonoidHom) * Nat.card U = 2 ^ i * Nat.card U := by
        rw [← hcm, hcard]
      have hpow := Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := U)) hEq
      exact Nat.pow_right_injective (by norm_num : 1 < 2) hpow
  · rintro ⟨hAX, g, hAg, hm⟩
    let U : Subgroup G := A.map (MulAut.conj g).toMonoidHom
    have hU : U ≤ V := by
      intro u hu
      obtain ⟨a, ha, rfl⟩ := hu
      have hain : g * a * g⁻¹ ∈ V := (mem_conjSubgroup_iff).1 (hAg ha)
      simpa [MulAut.conj_apply] using hain
    refine ⟨hAX, U, g⁻¹, hU, ?_, ?_⟩
    · have hVg : IsPGroup 2 (conjSubgroup V g) :=
        (CFSG.Quasithin.B2F.isPGroup_of_isElemAbelian hV).map _
      have hcm := CFSG.Quasithin.E3.card_eq_two_pow_mul hVg hAg
      have hcardg : Nat.card (conjSubgroup V g) = Nat.card V := by
        rw [conjSubgroup, Subgroup.card_map_of_injective
          (f := (MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g⁻¹).injective]
      have hcardU : Nat.card U = Nat.card A :=
        Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
          (MulAut.conj g).injective
      rw [hcardg] at hcm
      calc Nat.card V = 2 ^ CFSG.Quasithin.E3.mQuot (conjSubgroup V g) A * Nat.card A := hcm
        _ = 2 ^ i * Nat.card U := by rw [hm, hcardU]
    · show A = (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom
      rw [Subgroup.map_map]
      have hcomp : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
          (MulAut.conj (g⁻¹ * g)).toMonoidHom := by
        ext x
        simp [MulAut.conj_apply, mul_assoc]
      rw [hcomp, inv_mul_cancel]
      have h1 : MulAut.conj (1 : G) = 1 := map_one _
      rw [h1]
      exact (Subgroup.map_id A).symm

theorem Wi_eq_wClos (i : ℕ) (X V : Subgroup G) (hV : IsElemAbelian 2 V) :
    CFSG.LocalAnalysis.UniquenessCase.UC22.F12.Wi i X V =
      CFSG.Quasithin.E3.wClos V i X := by
  unfold CFSG.LocalAnalysis.UniquenessCase.UC22.F12.Wi CFSG.Quasithin.E3.wClos
  rw [gam_eq_gammaSet i X V hV]

theorem Ci_eq_cClos (i : ℕ) (X V : Subgroup G) (hV : IsElemAbelian 2 V) :
    CFSG.LocalAnalysis.UniquenessCase.UC22.F12.Ci i X V =
      CFSG.Quasithin.E3.cClos V i X := by
  unfold CFSG.LocalAnalysis.UniquenessCase.UC22.F12.Ci CFSG.Quasithin.E3.cClos
  rw [Wi_eq_wClos i X V hV]

theorem seventeen_twentyeight (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V)
    (h17_24 : R17_24At D V₀ V) (h17_27 : R17_27At D V₀ V)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h66 : UC6.R6_6 D) (h126 : R126 D)
    (h127 : R127 D) (h1114 : R1114 D) (h111 : W3Thm111 G) (h183 : W3Thm183 G) :
    R17_28At D V₀ V := by
  intro L c
  have hm3 : MBarGT D.M V₀ V 3 := by
    rcases h17_24 L c with h1 | h2
    · exact TwelveShort.mBarGT_mono h1.1 (by omega)
    · have hm4 : mBar D.M V₀ V c.hyp125.isElemAbelian = 4 := h2.2.2.1
      exact (c.hyp125.mBarGT_iff_lt_mBar 3).2 (by omega)
  have hk2 : D.k ≤ 2 := TwelveSeven.k_le_two D
  have hVP : IsPGroup 2 V := CFSG.Quasithin.B2F.isPGroup_of_isElemAbelian c.hyp125.isElemAbelian
  have hd : Nat.card V = 2 ^ rk ↥V := CFSG.Quasithin.card_eq_two_pow_of_isPGroup hVP
  have hcard : 2 ^ 4 ≤ Nat.card V := CFSG.LocalAnalysis.WeakClosure81.mBarGT_card_le hm3
  have hrk4 : 4 ≤ rk ↥V := by
    rw [hd] at hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hcard
  have h1 : 1 < rk ↥V := by omega
  have hNW0 : Subgroup.normalizer (CFSG.Quasithin.E3.wClos V 0 D.T : Set G) ≤ D.M := by
    simpa [Wi_eq_wClos 0 D.T V c.hyp125.isElemAbelian] using (h17_27 L c).2
  have hV0 : V₀ = ⊥ := by
    by_contra hne
    have hmk : MBarGT D.M V₀ V (D.k + 1) :=
      TwelveShort.mBarGT_mono hm3 (by omega)
    have h10 := (twelve_ten D hx h61 h66 h126 h127 h1114 h111 h183 c.hyp125).1 hne hmk
    have hNW1 : Subgroup.normalizer (CFSG.Quasithin.E3.wClos V 1 D.T : Set G) ≤
        Subgroup.normalizer (CFSG.Quasithin.E3.wClos V 0 D.T : Set G) :=
      CFSG.LocalAnalysis.WeakClosure81.normalizer_wClos_anti c.hyp125.isElemAbelian
        (Nat.zero_le 1) h1
    exact h10 (hNW1.trans hNW0)
  refine ⟨hV0, ?_⟩
  subst hV0
  have hmk : MBarGT D.M ⊥ V (D.k + 0) :=
    TwelveShort.mBarGT_mono hm3 (by omega)
  have hdisj := (twelve_ten D hx h61 h66 h126 h127 h1114 h111 h183 c.hyp125).2 rfl 0 hmk
  rcases hdisj with hN | hC
  · exact absurd hNW0 hN
  · intro hC2
    exfalso
    have hWk_le : CFSG.Quasithin.E3.wClos V D.k D.T ≤ CFSG.Quasithin.E3.wClos V 2 D.T :=
      CFSG.Quasithin.SteinbergBS.wClos_le_wClos c.hyp125.isElemAbelian hd (by omega) (by omega) D.T
    have hC2le : CFSG.LocalAnalysis.UniquenessCase.UC22.F12.Ci 2 D.T V ≤
        CFSG.Quasithin.E3.cClos V (D.k + 0) D.T := by
      rw [Ci_eq_cClos 2 D.T V c.hyp125.isElemAbelian]
      simp only [Nat.add_zero]
      rw [CFSG.Quasithin.E3.cClos, CFSG.Quasithin.E3.cClos]
      exact inf_le_inf le_rfl (Subgroup.centralizer_le (by intro x hx; exact hWk_le hx))
    have hCk_le : Subgroup.centralizer (CFSG.Quasithin.E3.cClos V (D.k + 0) D.T : Set G) ≤
        Subgroup.centralizer (CFSG.LocalAnalysis.UniquenessCase.UC22.F12.Ci 2 D.T V : Set G) :=
      Subgroup.centralizer_le (by intro x hx; exact hC2le hx)
    exact hC (hCk_le.trans hC2)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
