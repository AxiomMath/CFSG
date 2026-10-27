module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Stage2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Stage3FinInputs

public section

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.A5 CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique.DoubleA3 CFSG.QuasithinUnique.A5.Delta5

namespace CertificateChecks.Batch17027

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.A5 CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique.DoubleA3 CFSG.QuasithinUnique.A5.Delta5

private theorem thRaw_rone_0 : thRaw rone = 0 := by
  decide +kernel

private theorem thRaw_zraw_1 : thRaw zraw = 0 := by
  decide +kernel

private theorem thRaw_mul_2 : ∀ v ∈ Evens, v 4 = 0 → ∀ σ ∈ Vset, ∀ v' ∈ Evens, v' 4 = 0 → ∀ σ' ∈ Vset,
    thRaw (rmul (v, σ) (v', σ')) = thRaw (v, σ) + thRaw (v', σ') := by
  decide +kernel

private theorem thRaw_ker_3 : ∀ v ∈ Evens, v 4 = 0 → ∀ σ ∈ Vset, thRaw (v, σ) = 0 →
    (v, σ) = rone ∨ (v, σ) = zraw := by
  decide +kernel

private theorem thRaw_pre_4 : ∀ v : V4, isE8 (preraw v).1 ∧ (preraw v).2 ∈ Vset ∧ thRaw (preraw v) = v := by
  decide +kernel

private theorem thRaw_q_5 : ∀ v ∈ Evens, v 4 = 0 → ∀ σ ∈ Vset,
    (quadHyp (thRaw (v, σ)) = 0 ∧ rmul (v, σ) (v, σ) = rone) ∨
    (quadHyp (thRaw (v, σ)) = 1 ∧ rmul (v, σ) (v, σ) = zraw) := by
  decide +kernel

private theorem thRaw_W0_6 : ∀ v ∈ Evens, v 4 = 0 → ∀ σ ∈ Vset,
    (thRaw (v, σ) 0 = 0 ∧ thRaw (v, σ) 2 = 0) → σ = 1 := by
  decide +kernel

private theorem Mt1_act_7 : ∀ v ∈ Evens, v 4 = 0 → ∀ σ ∈ Vset,
    Mt1.mulVec (thRaw (v, σ)) = thRaw (rmul (rmul gt1 (v, σ)) gt1) := by
  decide +kernel

private theorem Ms01_act_8 : ∀ v ∈ Evens, v 4 = 0 → ∀ σ ∈ Vset,
    Ms01.mulVec (thRaw (v, σ)) = thRaw (rmul (rmul gs01 (v, σ)) gs01) := by
  decide +kernel

private theorem Mk_act_9 : ∀ v ∈ Evens, v 4 = 0 → ∀ σ ∈ Vset,
    Mk.mulVec (thRaw (v, σ)) = thRaw (rmul (rmul gk (v, σ)) gkinv) := by
  decide +kernel

private theorem W0_sing_10 : ∀ v : V4, inW0 v → v ≠ 0 → inSing v := by
  decide +kernel

private theorem Mk_trans_W0_11 : ∀ v : V4, inW0 v → v ≠ 0 → ∀ v' : V4, inW0 v' → v' ≠ 0 →
    v' = v ∨ v' = Mk.mulVec v ∨ v' = Mk.mulVec (Mk.mulVec v) := by
  decide +kernel

private theorem sing6_conn_12 : ∀ a ∈ sing6, ∀ b ∈ sing6, ∃ w ∈ wordsUpTo 3, wact w a = b := by
  decide +kernel

private theorem t1_step_13 : ∀ v : V4, ¬ inW0 v → inW0 (Mt1.mulVec v + v) ∧ Mt1.mulVec v + v ≠ 0 := by
  decide +kernel

private theorem S4_distinct_14 : (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) ≠ Mt1 ∧
    (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) ≠ Ms01 ∧
    (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) ≠ Mt1 * Ms01 ∧ Mt1 ≠ Ms01 ∧ Mt1 ≠ Mt1 * Ms01 ∧
    Ms01 ≠ Mt1 * Ms01 := by
  decide +kernel

private theorem S4_inj_15 : ∀ i j : Fin 4,
    (![1, Mt1, Ms01, Mt1 * Ms01] : Fin 4 → Matrix (Fin 4) (Fin 4) (ZMod 2)) i =
      (![1, Mt1, Ms01, Mt1 * Ms01] : Fin 4 → Matrix (Fin 4) (Fin 4) (ZMod 2)) j → i = j := by
  decide +kernel

private theorem thRaw_one_W0_16 : ∀ v : Fin 5 → ZMod 2, thRaw (v, 1) 0 = 0 ∧ thRaw (v, 1) 2 = 0 := by
  decide +kernel

private theorem swap_moves_e02_17 : pact (Equiv.swap 0 1) ![1, 0, 1, 0, 0] ≠ ![1, 0, 1, 0, 0] := by
  decide +kernel

private theorem e02_even_18 : isEven ![1, 0, 1, 0, 0] := by
  decide +kernel

private theorem e02_four_19 : (![1, 0, 1, 0, 0] : Fin 5 → ZMod 2) 4 = 0 := by
  decide +kernel

private theorem c3_inv_20 : c3⁻¹ = c3 * c3 := by
  decide +kernel

private theorem nine_sing_21 : (Finset.univ.filter fun v : V4 => inSing v).card = 9 := by
  decide +kernel

private theorem sing_gen_22 : ∀ v : V4, v = 0 ∨ inSing v ∨ ∃ a b : V4, inSing a ∧ inSing b ∧ a + b = v := by
  decide +kernel

private theorem card_O4Cols_23 : Fintype.card O4Cols = 72 := by
  decide +kernel

end CertificateChecks.Batch17027

namespace Certificates

open CertificateChecks

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.A5 CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique.DoubleA3 CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5.Action CFSG.QuasithinUnique.A5.Split in
theorem certificate17027 : (
 thRaw rone = 0 
)
    ∧ (
 thRaw zraw = 0 
)
    ∧ (
 ∀ v ∈ Evens, v 4 = 0 → ∀ σ ∈ Vset, ∀ v' ∈ Evens, v' 4 = 0 → ∀ σ' ∈ Vset,
    thRaw (rmul (v, σ) (v', σ')) = thRaw (v, σ) + thRaw (v', σ') 
)
    ∧ (
 ∀ v ∈ Evens, v 4 = 0 → ∀ σ ∈ Vset, thRaw (v, σ) = 0 →
    (v, σ) = rone ∨ (v, σ) = zraw 
)
    ∧ (
 ∀ v : V4, isE8 (preraw v).1 ∧ (preraw v).2 ∈ Vset ∧ thRaw (preraw v) = v 
)
    ∧ (
 ∀ v ∈ Evens, v 4 = 0 → ∀ σ ∈ Vset,
    (quadHyp (thRaw (v, σ)) = 0 ∧ rmul (v, σ) (v, σ) = rone) ∨
    (quadHyp (thRaw (v, σ)) = 1 ∧ rmul (v, σ) (v, σ) = zraw) 
)
    ∧ (
 ∀ v ∈ Evens, v 4 = 0 → ∀ σ ∈ Vset,
    (thRaw (v, σ) 0 = 0 ∧ thRaw (v, σ) 2 = 0) → σ = 1 
)
    ∧ (
 ∀ v ∈ Evens, v 4 = 0 → ∀ σ ∈ Vset,
    Mt1.mulVec (thRaw (v, σ)) = thRaw (rmul (rmul gt1 (v, σ)) gt1) 
)
    ∧ (
 ∀ v ∈ Evens, v 4 = 0 → ∀ σ ∈ Vset,
    Ms01.mulVec (thRaw (v, σ)) = thRaw (rmul (rmul gs01 (v, σ)) gs01) 
)
    ∧ (
 ∀ v ∈ Evens, v 4 = 0 → ∀ σ ∈ Vset,
    Mk.mulVec (thRaw (v, σ)) = thRaw (rmul (rmul gk (v, σ)) gkinv) 
)
    ∧ (
 ∀ v : V4, inW0 v → v ≠ 0 → inSing v 
)
    ∧ (
 ∀ v : V4, inW0 v → v ≠ 0 → ∀ v' : V4, inW0 v' → v' ≠ 0 →
    v' = v ∨ v' = Mk.mulVec v ∨ v' = Mk.mulVec (Mk.mulVec v) 
)
    ∧ (
 ∀ a ∈ sing6, ∀ b ∈ sing6, ∃ w ∈ wordsUpTo 3, wact w a = b 
)
    ∧ (
 ∀ v : V4, ¬ inW0 v → inW0 (Mt1.mulVec v + v) ∧ Mt1.mulVec v + v ≠ 0 
)
    ∧ (
 (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) ≠ Mt1 ∧
    (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) ≠ Ms01 ∧
    (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) ≠ Mt1 * Ms01 ∧ Mt1 ≠ Ms01 ∧ Mt1 ≠ Mt1 * Ms01 ∧
    Ms01 ≠ Mt1 * Ms01 
)
    ∧ (
 ∀ i j : Fin 4,
    (![1, Mt1, Ms01, Mt1 * Ms01] : Fin 4 → Matrix (Fin 4) (Fin 4) (ZMod 2)) i =
      (![1, Mt1, Ms01, Mt1 * Ms01] : Fin 4 → Matrix (Fin 4) (Fin 4) (ZMod 2)) j → i = j 
)
    ∧ (
 ∀ v : Fin 5 → ZMod 2, thRaw (v, 1) 0 = 0 ∧ thRaw (v, 1) 2 = 0 
)
    ∧ (
 pact (Equiv.swap 0 1) ![1, 0, 1, 0, 0] ≠ ![1, 0, 1, 0, 0] 
)
    ∧ (
 isEven ![1, 0, 1, 0, 0] 
)
    ∧ (
 (![1, 0, 1, 0, 0] : Fin 5 → ZMod 2) 4 = 0 
)
    ∧ (
 c3⁻¹ = c3 * c3 
)
    ∧ (
 (Finset.univ.filter fun v : V4 => inSing v).card = 9 
)
    ∧ (
 ∀ v : V4, v = 0 ∨ inSing v ∨ ∃ a b : V4, inSing a ∧ inSing b ∧ a + b = v 
)
    ∧ (
 Fintype.card O4Cols = 72 
) := by
  exact ⟨@CertificateChecks.Batch17027.thRaw_rone_0, @CertificateChecks.Batch17027.thRaw_zraw_1, @CertificateChecks.Batch17027.thRaw_mul_2, @CertificateChecks.Batch17027.thRaw_ker_3, @CertificateChecks.Batch17027.thRaw_pre_4, @CertificateChecks.Batch17027.thRaw_q_5, @CertificateChecks.Batch17027.thRaw_W0_6, @CertificateChecks.Batch17027.Mt1_act_7, @CertificateChecks.Batch17027.Ms01_act_8, @CertificateChecks.Batch17027.Mk_act_9, @CertificateChecks.Batch17027.W0_sing_10, @CertificateChecks.Batch17027.Mk_trans_W0_11, @CertificateChecks.Batch17027.sing6_conn_12, @CertificateChecks.Batch17027.t1_step_13, @CertificateChecks.Batch17027.S4_distinct_14, @CertificateChecks.Batch17027.S4_inj_15, @CertificateChecks.Batch17027.thRaw_one_W0_16, @CertificateChecks.Batch17027.swap_moves_e02_17, @CertificateChecks.Batch17027.e02_even_18, @CertificateChecks.Batch17027.e02_four_19, @CertificateChecks.Batch17027.c3_inv_20, @CertificateChecks.Batch17027.nine_sing_21, @CertificateChecks.Batch17027.sing_gen_22, @CertificateChecks.Batch17027.card_O4Cols_23⟩

end Certificates
