module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec3SixLoc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec3Three

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

local notation "pval" => CFSG.Quasithin.Fan86.valence

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace FanTree

variable {F : FanTree Γ G}

theorem false_of_le_ballStab (L : LocalFacts F) (h32 : Fan32 F) {a b c : V} (hab : Γ.Adj a b)
    (hbc : Γ.Adj b c) (ha3 : pval Γ a = 3) (hc3 : pval Γ c = 3) (hb5 : pval Γ b = 5)
    (hM : nbrStab Γ G a ⊓ nbrStab Γ G b ⊓ nbrStab Γ G c ≤ ballStab Γ G 2 b) : False := by
  set U := ballStab Γ G 2 b with hU
  have hKb : nbrStab Γ G b ≤ MulAction.stabilizer G b := F.nbrStab_le_stabilizer b
  have hUKb : U ≤ nbrStab Γ G b := fun g hg => ((F.mem_ballStab_two_iff).1 hg).1
  have hD : nbrStab Γ G a ⊓ nbrStab Γ G b ≤ MulAction.stabilizer G c ⊓ MulAction.stabilizer G b :=
    fun g hg => ⟨MulAction.mem_stabilizer_iff.2 (mem_nbrStab.1 hg.2 c hbc),
      F.nbrStab_le_stabilizer b hg.2⟩
  have hKbab : nbrStab Γ G b ≤ MulAction.stabilizer G a ⊓ MulAction.stabilizer G b :=
    fun g hg => ⟨MulAction.mem_stabilizer_iff.2 (mem_nbrStab.1 hg a hab.symm), hKb hg⟩
  have hDKb : nbrStab Γ G a ⊓ nbrStab Γ G b ≤ nbrStab Γ G b := inf_le_right
  have h1 : (nbrStab Γ G a ⊓ nbrStab Γ G b).relIndex (nbrStab Γ G b) ≤ 2 := by
    rw [Subgroup.inf_relIndex_right]
    exact F.relIndex_le_two hab ha3 hKbab
  have h2 : (nbrStab Γ G a ⊓ nbrStab Γ G b ⊓ nbrStab Γ G c).relIndex
      (nbrStab Γ G a ⊓ nbrStab Γ G b) ≤ 2 := by
    rw [Subgroup.inf_relIndex_left]
    exact F.relIndex_le_two hbc.symm hc3 hD
  have hMD : nbrStab Γ G a ⊓ nbrStab Γ G b ⊓ nbrStab Γ G c ≤ nbrStab Γ G a ⊓ nbrStab Γ G b :=
    inf_le_left
  have hMKb := Subgroup.relIndex_mul_relIndex _ _ _ hMD hDKb
  have hfinKb : Finite ↥(nbrStab Γ G b) := by
    have := F.loc_finite b
    exact Finite.of_injective (Subgroup.inclusion hKb) (Subgroup.inclusion_injective _)
  have hne0 : U.relIndex (nbrStab Γ G b) ≠ 0 := relIndex_ne_zero_of_finite _ _
  have hdvd := Subgroup.relIndex_dvd_of_le_left (nbrStab Γ G b) hM
  have hMne : (nbrStab Γ G a ⊓ nbrStab Γ G b ⊓ nbrStab Γ G c).relIndex (nbrStab Γ G b) ≠ 0 :=
    relIndex_ne_zero_of_finite _ _
  have hle4 : U.relIndex (nbrStab Γ G b) ≤ 4 := by
    have h3 : (nbrStab Γ G a ⊓ nbrStab Γ G b ⊓ nbrStab Γ G c).relIndex (nbrStab Γ G b) ≤ 4 := by
      rw [← hMKb]
      exact (Nat.mul_le_mul h2 h1).trans (by norm_num)
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hMne) hdvd).trans h3
  obtain ⟨x, hx, hxo⟩ := F.exists_orderOf_eq_valence b
  have hxp : x ^ 5 = 1 := by
    rw [← hb5, ← hxo]
    exact pow_orderOf_eq_one x
  have hcomm := comm_mod_of_relIndex_lt U (nbrStab Γ G b)
    (fun k hk => F.mem_normalizer_ballStab_two (hKb hk)) (F.mem_normalizer_ballStab_two hx)
    (fun s hs => F.conj_mem_nbrStab_of_stab hx hs) Nat.prime_five hxp (by omega) hne0
  exact XSetup.false_of_comm (F := F) ⟨hab.symm, hx, by rw [hxo, hb5]⟩ L h32
    (fun g hg => hKb (hUKb hg)) (F.normal_ballStab_two b)
    (fun g hg => (F.ballStab_two_le_inf hab.symm hg).2) (fun g hg => hcomm g hg)

end FanTree

end CFSG.Quasithin.Fan86
