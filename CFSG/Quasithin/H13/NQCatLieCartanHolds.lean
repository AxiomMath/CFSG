module

public import CFSG.Quasithin.H13.NQCatLieCartanRank1
public import CFSG.Quasithin.H13.NQCatLieCartanL3
public import CFSG.Quasithin.H13.NQCatLieCartanSp4
public import CFSG.Quasithin.H13.NQCatLieCartanG2
public import CFSG.Quasithin.H13.NQCatLieCartanD4
public import CFSG.Quasithin.H13.NQCatLieCartanF4

public section

namespace CFSG.Quasithin.H13.NQCat.LieCartan

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.QuasithinUnique.Setup.X6

theorem torusConcl_of_isLieChar2Big
    {S : Type} [Group S] [Finite S] (hL : IsLieChar2Big S) :
    TorusConcl S (∃ k : ℕ, 2 ≤ k ∧ (IsPSL 2 2 k S ∨ IsSz k S ∨ IsPSp4 2 k S)) := by
  obtain ⟨k, hk, h⟩ := hL
  rcases h with h | h | h | h | h | h | h | h
  · exact torusConcl_rank1 hk (Or.inl h)
  ·
    obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h
    have : CharP F 2 := LieMult.charP_two_of_card hF
    exact (TorusConcl.of_mulEquiv (e.trans (Setup.X7a.statedSLEquivProjectiveSL 3 F))
      L3.torusConcl_l3).mono False.elim
  · exact torusConcl_rank1 hk (Or.inr (Or.inl h))
  ·
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id h
    have : CharP K 2 := LieMult.charP_two_of_card hK
    have hK4 : 4 ≤ Nat.card K := by
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    let e' : CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSp 2 K) ≃*
        CFSG.Assembly.LowTwoRank.StatedSp 2 K :=
      (MulEquiv.ofBijective (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj 2 K)
        ⟨Vol2Native.A312L.proj_injective_charTwo, QuotientGroup.mk'_surjective _⟩).symm
    exact (TorusConcl.of_mulEquiv (e.trans e') (Sp4.torusConcl_sp4 hK4)).mono
      fun _ => ⟨k, hk, Or.inr (Or.inr h)⟩
  ·
    obtain ⟨hf, F, _, _, _, hF, ⟨e⟩⟩ := exists_mulEquiv_G2_model h
    exact (TorusConcl.of_mulEquiv e (G2.torusConcl_g2 hF hf)).mono False.elim
  ·
    obtain ⟨hn, K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_triality_model h
    exact (TorusConcl.of_mulEquiv e (D4.torusConcl_d4 σ hn hK hσ)).mono False.elim
  · exact torusConcl_rank1 hk (Or.inr (Or.inr h))
  ·
    obtain ⟨-, -, -, -, ⟨a, ha, hka⟩, hiso⟩ := ReeTag.large_Ree_model_Schreier S 2 k h
    obtain ⟨-, a', hka', ⟨K, _, _, hK, he⟩⟩ := h
    have : Fintype K := Fintype.ofFinite K
    have : CharP K ReeTag.F4.prime := charP_of_card_eq_prime_pow (f := k) (by
      rw [← Nat.card_eq_fintype_card, hK]
      rfl)
    have haa' : a' = a := by omega
    subst haa'
    obtain ⟨e⟩ := hiso a' K hka' hK he
    have hK' : Nat.card K = 2 ^ (2 * a' + 1) := by rw [hK, hka']
    exact (TorusConcl.of_mulEquiv e (F4.torusConcl_f4 ha hK')).mono False.elim

theorem lieCartanFact_holds :
    LieCartanFact := fun _ _ _ _ hL => torusConcl_of_isLieChar2Big hL

end CFSG.Quasithin.H13.NQCat.LieCartan
