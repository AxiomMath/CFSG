module

public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD
public import CFSG.Permutation.FinPackDec

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.ThreeGroup

open CFSG.Permutation.FinPack

@[expose] def evenOrder3Codes : List ℕ :=
  [3490320, 4411920, 5391120, 2380560, 5448720, 2438160, 3417360, 4338960, 5509920, 5321760,
    1324320, 5513520, 5325360, 1331760, 5386560, 5444160, 1389120, 2371920, 3412560, 4272720,
    5517345, 3489825, 4411425, 5505585, 2425905, 4326705, 5255745, 2118465, 3155265, 275025, 148305,
    205905, 5517570, 3490050, 4411650, 5505810, 5256210, 275730, 1070130, 83250, 1377090, 202050,
    4260690, 3150930, 5509635, 2429955, 4330755, 5513235, 5259795, 283155, 87075, 1066275, 1384515,
    151875, 4268115, 2113875, 5321220, 2183940, 3220740, 5386260, 5440020, 340500, 332580, 1246500,
    1200180, 336180, 3280980, 2294100, 1323525, 1196805, 1254405, 2371605, 3408405, 4207125,
    4199205, 3212325, 2179125, 4202805, 2297925, 3277125]

local notation "e6" => enc (1 : Equiv.Perm (Fin 6))

theorem evenOrder3Codes_complete : ∀ τ : Equiv.Perm (Fin 6), τ ^ 3 = 1 → τ ≠ 1 →
    Equiv.Perm.sign τ = 1 → memK (enc τ) evenOrder3Codes = true := by
  have hw : walkK 6 (fun t => !Nat.beq (powK 6 e6 t 3) e6 || Nat.beq t e6 || !evenK 6 t ||
      memK t evenOrder3Codes) 6 0 0 0 = true := by
    decide +kernel
  have hn : 6 ≤ 16 := by norm_num
  intro τ h3 h1 hs
  have h := walkK_sound hw τ
  simp only [beq_enc_eq_decide hn, powK_enc hn, evenK_enc_eq_decide hn, h3, h1, hs, decide_true,
    decide_false, Bool.not_true, Bool.false_or] at h
  exact h

theorem evenOrder3Codes_noncomm : walkK 6 (fun k => !evenK 6 k || Nat.beq (powK 6 e6 k 3) e6 ||
    allK (fun t => !commLaneK 6 k t) evenOrder3Codes) 6 0 0 0 = true := by
  decide +kernel

theorem alt_six_centralizer_cube : ∀ τ : Equiv.Perm (Fin 6), τ ^ 3 = 1 → τ ≠ 1 →
    Equiv.Perm.sign τ = 1 → ∀ κ : Equiv.Perm (Fin 6), Equiv.Perm.sign κ = 1 → κ * τ = τ * κ →
    κ ^ 3 = 1 := by
  have hn : 6 ≤ 16 := by norm_num
  intro τ h3 h1 hs κ hκ hc
  have hτ := memK_iff.1 (evenOrder3Codes_complete τ h3 h1 hs)
  have h := walkK_sound evenOrder3Codes_noncomm κ
  simp only [beq_enc_eq_decide hn, powK_enc hn, evenK_enc_eq_decide hn, hκ, decide_true,
    Bool.not_true, Bool.false_or, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · exact h
  · have h' := allK_iff.1 h _ hτ
    rw [commLaneK_enc_eq_decide hn] at h'
    simp [hc] at h'

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.ThreeGroup
