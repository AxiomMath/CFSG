module

public import CFSG.LocalAnalysis.StandardType.PhanEFlagPsi
public import CFSG.LocalAnalysis.StandardType.PhanEFlagPsiVdm
public import CFSG.LocalAnalysis.StandardType.PhanEFlagAsm
public import CFSG.LocalAnalysis.StandardType.PhanEFlagPart

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Flag

open Module CFSG.Monster.B.Geometry CFSG.LieType.Chevalley.CosetBuilding
  CFSG.ClassicalInvolution.Phan.PhanE

variable {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2] {m : ℕ} {d : List ℕ}

private theorem q2cFPo_finrank_Vsub_sup_A {n : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2)
    (hd : IsCut n d) (pol : List Bool) {ω : Fin 4 → K} (hω : Function.Injective ω) {b r : ℕ}
    (hb : b + 1 < d.length) (hs : blockSize d b ≤ 4) (hr : r ≤ blockSize d b) :
    finrank K (Vsub n (d.getD b 0) ⊔ q2cFPo_A d pol ω b r : Submodule K (Fin n → K)) =
      d.getD b 0 + r := by
  have hbn : d.getD b 0 ≤ n := q2cFPo_le_last hd (by omega)
  have hinf : Vsub n (d.getD b 0) ⊓ q2cFPo_A d pol ω b r = ⊥ := by
    refine le_antisymm ?_ bot_le
    calc Vsub n (d.getD b 0) ⊓ q2cFPo_A d pol ω b r
        ≤ Vsub n (d.getD b 0) ⊓ q2cFPo_Wb d b :=
          inf_le_inf le_rfl (q2cFPo_A_le_Wb pol ω b r)
      _ = ⊥ := by rw [inf_comm, q2cFPo_Wb_inf_Vsub]
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq (Vsub (K := K) n (d.getD b 0))
    (q2cFPo_A (K := K) (n := n) d pol ω b r)
  rw [hinf, finrank_bot, finrank_Vsub hbn, q2cFPo_finrank_A hd pol hω hb hs hr] at hsup
  omega

theorem exists_opp_flagPsi (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f)
    (hn : m + 1 ≤ 4) (hd : IsCut (m + 1) d) (pol : List Bool) :
    ∃ z ∈ refSet K (m + 1) d,
      flagδ m z (flagPsi hK hd pol z) = longest (symCox m) (cutTypes m d) := by
  obtain ⟨ω, hω, hσω⟩ := q2cFPo_exists_nodes (K := K) (f := f) hK hq
  let S : ℕ → ℕ → Submodule K (Fin (m + 1) → K) :=
    fun b s => Vsub (m + 1) (d.getD b 0) ⊔ q2cFPo_A (n := m + 1) d pol ω b s
  have hlo : ∀ b s, b + 1 < d.length → s ≤ blockSize d b →
      Vsub (m + 1) (d.getD b 0) ≤ S b s := fun _ _ _ _ => le_sup_left
  have hhi : ∀ b s, b + 1 < d.length → s ≤ blockSize d b →
      S b s ≤ Vsub (m + 1) (d.getD (b + 1) 0) := by
    intro b s hb _
    have hle : d.getD b 0 ≤ d.getD (b + 1) 0 := le_of_lt (hd.strict b hb)
    exact sup_le (Vsub_mono hle)
      (le_trans (q2cFPo_A_le_Wb pol ω b s) q2cFPo_Wb_le_Vsub)
  have hmono : ∀ b s s', b + 1 < d.length → s ≤ s' → s' ≤ blockSize d b →
      S b s ≤ S b s' := by
    intro b s s' _ hss' _
    exact sup_le_sup_left (q2cFPo_A_mono pol ω b hss') (Vsub (m + 1) (d.getD b 0))
  have hdim : ∀ b s, b + 1 < d.length → s ≤ blockSize d b →
      finrank K (S b s) = d.getD b 0 + s := by
    intro b s hb hs
    have hs4 : blockSize d b ≤ 4 := le_trans (q2cFPo_blockSize_le hd hb) hn
    exact q2cFPo_finrank_Vsub_sup_A (K := K) (f := f) hK hd pol hω hb hs4 hs
  obtain ⟨z, hz, hblk⟩ := exists_flag_of_blocks (K := K) (n := m + 1) hd S hlo hhi hmono hdim
  refine ⟨z, hz, (flagδ_eq_longest_cutTypes_iff hd hz (flagPsi_mem hK hd pol hz)).2 ?_⟩
  intro b r hb hr
  have hs4 : blockSize d b ≤ 4 := le_trans (q2cFPo_blockSize_le hd hb) hn
  have hsub : blockSize d b - (blockSize d b - r) = r := by omega
  rw [hblk b r hb hr, flagPsi_E hK hd pol hz hb (Nat.sub_le _ _), psiSub]
  by_cases hp : pol.getD b false = true
  · rw [if_pos hp, hsub, hblk b r hb hr]
    exact q2cFPo_inf_perpB_A (K := K) (f := f) hd (pol := pol) (ω := ω) hb hs4 hr hp
  · rw [if_neg hp, hblk b (blockSize d b - r) hb (Nat.sub_le _ _)]
    exact q2cFPo_inf_sgS_A (K := K) (f := f) hK hd (pol := pol) (ω := ω) hω hσω hb hs4 hr
      (Bool.eq_false_of_not_eq_true hp)

end CFSG.ClassicalInvolution.Phan.PhanE.Flag
