module

public import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenAsm
public import CFSG.LocalAnalysis.StandardType.GGRootGenSpOrthSplitAvoid
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorus
import CFSG.LocalAnalysis.StandardType.GGOmegaPlusCentrallyClosed
import CFSG.LocalAnalysis.StandardType.GGOmegaMinusCentrallyClosed
import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixNsLiftOmega
import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestTailFinal
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaPlus
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaMinus

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open OrthTorus

theorem ggTorusRootGenAvoidKG_omegaPlusNs {K : Type} [Field K] [Finite K] {n m p : ℕ}
    (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) (hm : 4 ≤ m) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K + 1) (r : ℕ) :
    GGTorusRootGenAvoidKG p r (OrthRest.RPlus K m) (LargeEvenInnSet (OrthRest.RPlus K m)) := by
  have : CharP K 2 := charP_two_of_card hK
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  let e := rPlusEquiv K (m := m) (by omega)
  refine ggTorusRootGenAvoidKG_of_mulEquiv e (fun φ hφ => ?_)
    (OmNsRootGen.ggTorusRootGenAvoidKG_orthDerived (TableBOrth.nondegenerate_qPlusForm m) hp hp2
      hpq h4 (ℓ := m) ?_ hm (fun L' _ _ ψ hψ hker hperf => ?_) r)
  · obtain ⟨x, rfl⟩ := hφ
    refine ⟨e x, MulEquiv.ext fun y => ?_⟩
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulAut.conj_apply, map_mul, map_inv,
      MulEquiv.apply_symm_apply]
  · rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin, two_mul]
  · have h := rPlus_injective_of_cover hK hn (by omega) L' (e.symm.toMonoidHom.comp ψ)
      (e.symm.surjective.comp hψ) (fun l hl => hker (by simpa [MonoidHom.mem_ker] using hl)) hperf
    exact fun x y hxy => h (congrArg e.symm hxy)

theorem ggTorusRootGenAvoidKG_omegaMinusNs
    {K : Type} [Field K] [Finite K]
    {n m p : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) (hm : 3 ≤ m) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (r : ℕ) :
    GGTorusRootGenAvoidKG p r (OrthRest.RMinus K m b c)
      (LargeEvenInnSet (OrthRest.RMinus K m b c)) := by
  have : CharP K 2 := charP_two_of_card hK
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  let e := rMinusEquiv K m b c
  refine ggTorusRootGenAvoidKG_of_mulEquiv e (fun φ hφ => ?_)
    (OmNsRootGen.ggTorusRootGenAvoidKG_orthDerived (TableBOrth.nondegenerate_qMinusForm m hirr)
      hp hp2 hpq h4 (ℓ := m + 1) ?_ (by omega) (fun L' _ _ ψ hψ hker hperf => ?_) r)
  · obtain ⟨x, rfl⟩ := hφ
    refine ⟨e x, MulEquiv.ext fun y => ?_⟩
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulAut.conj_apply, map_mul, map_inv,
      MulEquiv.apply_symm_apply]
  · rw [Module.finrank_fintype_fun_eq_card]
    simp only [LargeEvenMinusIdx, Fintype.card_sum, Fintype.card_fin]
    ring
  · have h := rMinus_injective_of_cover hK hn hm hirr L' (e.symm.toMonoidHom.comp ψ)
      (e.symm.surjective.comp hψ) (fun l hl => hker (by simpa [MonoidHom.mem_ker] using hl)) hperf
    exact fun x y hxy => h (congrArg e.symm hxy)

theorem largeEvenLabelAll_rootGenAvoidKG_omegaPlusNs {p l n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : p ∣ 2 ^ n + 1) (hn : 2 ≤ n) (hl : 4 ≤ l) :
    LargeEvenLabelAll ⟨.D, l, n⟩ fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGTorusRootGenAvoidKG p r R I := by
  refine largeEvenLabelAll_omegaPlus rfl hl fun K _ _ _ hK => ?_
  have hpq : p ∣ Nat.card K + 1 := by
    rw [hK]
    exact hpn
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  exact ⟨3, TableBSymp.ggTorusLift_omegaPlusNs hp hp2 hpq h4 hl,
    ggTorusRootGenAvoidKG_omegaPlusNs hK hn hl hp hp2 hpq 3⟩

theorem largeEvenLabelAll_rootGenAvoidKG_omegaMinusNs
    {p l n : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ n + 1) (hn : 2 ≤ n) (hl : 4 ≤ l) :
    LargeEvenLabelAll ⟨.twD, l, n⟩ fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGTorusRootGenAvoidKG p r R I := by
  refine largeEvenLabelAll_omegaMinus rfl hl fun K _ _ _ hK b c hirr => ?_
  have hpq : p ∣ Nat.card K + 1 := by
    rw [hK]
    exact hpn
  exact ⟨l - 1, ggOrthRestTorusLiftInput_holds.1 K n (l - 1) p b c hK (by omega) hp hpn hirr,
    ggTorusRootGenAvoidKG_omegaMinusNs (m := l - 1) hK hn (by omega) hp hp2 hpq hirr (l - 1)⟩

theorem ggRootGenKGAvoidOn_orth :
    GGRootGenKGAvoidOn GGRootGenOrthLabel := by
  rintro p ⟨t, l, n⟩ hp hp2 - ⟨hpn, hn, ht | ht, hl⟩
  · dsimp only at ht hpn hn hl
    subst ht
    exact largeEvenLabelAll_rootGenAvoidKG_omegaPlusNs hp hp2 hpn hn hl
  · dsimp only at ht hpn hn hl
    subst ht
    exact largeEvenLabelAll_rootGenAvoidKG_omegaMinusNs hp hp2 hpn hn hl

end CFSG.StandardType

end
