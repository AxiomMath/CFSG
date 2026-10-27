module

public import CFSG.Quasithin.Background.B3Off
public import CFSG.Assembly.Defs

public section

namespace CFSG.Quasithin.B3

variable {n : ℕ}

theorem U_mul_self (w : U n) : w * w = 1 := by
  ext i
  simp only [U.val_mul, U.val_one]
  exact CharTwo.add_self_eq_zero _

theorem V_sq (k : Mod) (v : Mod.V n k) : v ^ 2 = 1 := by
  induction v using QuotientGroup.induction_on with
  | H w =>
    rw [pow_two, ← QuotientGroup.mk_mul]
    have : w * w = 1 := Subtype.ext (U_mul_self (w : U n))
    rw [this]
    rfl

theorem V_sq' (k : Mod) : ∀ v : Mod.V n k, v ^ 2 = 1 := V_sq k

theorem cntF_id (k : Mod) :
    Nat.card (Mod.V n k) * cN n k = cntF n k [idT n] := by
  have h := card_fix_cnt k (⊥ : Subgroup (Gp n)) [idT n]
    (fun t ht => by
      simp only [List.mem_singleton] at ht
      rw [ht, ← tab_one]
      exact isTab_tab _)
    (fun x => by
      rw [Subgroup.mem_bot, ← tab_one]
      simp only [List.mem_singleton]
      exact ⟨fun h => by rw [h], fun h => tab_injective h⟩)
  rw [Subgroup.map_bot, B1.fixV_bot, Subgroup.card_top] at h
  exact h

theorem index_fixV_mul_cntF (k : Mod) {L : List Tab} {K : Subgroup (Gp n)}
    (hLv : ∀ t ∈ L, isTab n t = true) (hK : ∀ x : Gp n, x ∈ K ↔ tab x ∈ L) :
    (fixV (K.map (Mod.act n k))).index * cntF n k L = cntF n k [idT n] := by
  have h1 := card_fix_cnt k K L hLv hK
  rw [← h1, ← cntF_id k, ← mul_assoc, Subgroup.index_mul_card]
  rfl

theorem rank_data (hn : 5 ≤ n) (k : Mod) {L : List Tab} (hL : subOK n L = true) {r s : ℕ}
    (hlen : L.length = 2 ^ r) (hcnt : cntF n k L * 2 ^ s = cntF n k [idT n]) :
    rk (subOf n L) = r ∧ rkIdx (fixV ((subOf n L).map (Mod.act n k))) = s ∧
      rAV ((subOf n L).map (Mod.act n k)) = (s : ℚ) / r := by
  have hK : ∀ x : Gp n, x ∈ subOf n L ↔ tab x ∈ L := fun x => mem_subOf hL
  have hrk : rk (subOf n L) = r := by
    unfold rk
    rw [card_subOf hL, hlen, padicValNat.prime_pow]
  have hidx := index_fixV_mul_cntF k (subOK_spec hL).1 hK
  have hpos : 0 < cntF n k [idT n] := by
    rw [← cntF_id k]
    exact Nat.mul_pos Nat.card_pos (cN_pos k)
  have hcpos : 0 < cntF n k L := by
    rcases Nat.eq_zero_or_pos (cntF n k L) with h0 | h0
    · rw [h0, zero_mul] at hcnt
      omega
    · exact h0
  have hix : (fixV ((subOf n L).map (Mod.act n k))).index = 2 ^ s := by
    apply Nat.eq_of_mul_eq_mul_right hcpos
    rw [hidx, ← hcnt, mul_comm]
  have hrkIdx : rkIdx (fixV ((subOf n L).map (Mod.act n k))) = s := by
    unfold rkIdx
    rw [hix, padicValNat.prime_pow]
  have hrk' : rk ((subOf n L).map (Mod.act n k)) = r := by
    unfold rk
    rw [Subgroup.card_map_of_injective (act_injective hn k), card_subOf hL, hlen,
      padicValNat.prime_pow]
  refine ⟨hrk, hrkIdx, ?_⟩
  unfold rAV
  rw [hrkIdx, hrk']

theorem rk_cj (g : Gp n) (K : Subgroup (Gp n)) : rk (cj g K) = rk K := by
  unfold rk cj
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem rkIdx_fixV_map_cj (k : Mod) (g : Gp n) (K : Subgroup (Gp n)) :
    rkIdx (fixV ((cj g K).map (Mod.act n k))) = rkIdx (fixV (K.map (Mod.act n k))) := by
  rw [map_cj]
  unfold rkIdx
  rw [B1.fixV_conjAut]
  exact congrArg (padicValNat 2)
    (Subgroup.index_map_equiv (fixV (K.map (Mod.act n k))) (Mod.act n k g))

theorem rAV_map_cj (k : Mod) (g : Gp n) (K : Subgroup (Gp n)) :
    rAV ((cj g K).map (Mod.act n k)) = rAV (K.map (Mod.act n k)) := by
  have h1 : rk ((cj g K).map (Mod.act n k)) = rk (K.map (Mod.act n k)) := by
    rw [map_cj]
    unfold rk
    rw [B1.card_conjAut]
  unfold rAV
  rw [h1, rkIdx_fixV_map_cj]

end CFSG.Quasithin.B3
