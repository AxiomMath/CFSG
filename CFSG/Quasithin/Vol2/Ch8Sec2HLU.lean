module

public import CFSG.Quasithin.Vol2.Ch8Sec2HFactsLU
public import CFSG.Quasithin.Background.HLURows24

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.L3W9
  CFSG.Quasithin.H.LU

theorem card_of_binaryNine {V : Type} [CommGroup V] {H : Subgroup (MulAut V)}
    (h : BinaryNineTensor H ⊤ ⊥ 1) : Nat.card V = 2 ^ 9 := by
  obtain ⟨e, -⟩ := exists_equiv_w9 h
  exact card_of_equiv e

theorem card_of_code22 {V : Type} [CommGroup V]
    {H : Subgroup (MulAut V)} (h : MathieuCode22 H ⊤ ⊥) : Nat.card V = 2 ^ 10 := by
  obtain ⟨e, -⟩ := code22_std h
  exact card_of_equiv e

theorem rk_of_card_lu {V : Type} [Group V] {n : ℕ} (h : Nat.card V = 2 ^ n) : rk V = n := by
  unfold rk
  rw [h, padicValNat.prime_pow]

theorem hLU82_holds :
    HLU82 := by
  intro V _ _ H X hXN hXe hrow
  rcases hrow with ⟨h, hX, hfX⟩ | ⟨h, hX, hfX⟩ | ⟨h, hX, hfX⟩ | ⟨h, hX, hfX⟩
  · obtain ⟨⟨hq, hA⟩, hV⟩ := luRow_L34 hXN hXe h hX hfX
    refine ⟨hq, fun _ => hA, fun ⟨h', _⟩ => ?_, fun ⟨h', _⟩ => ?_⟩
    · have := code24_card h'
      rw [hV] at this
      norm_num at this
    · have := cocode24_card h'
      rw [hV] at this
      norm_num at this
  · obtain ⟨⟨hq, hA⟩, hV⟩ := luRow_M22 hXN hXe h hX hfX
    refine ⟨hq, fun _ => hA, fun ⟨h', _⟩ => ?_, fun ⟨h', _⟩ => ?_⟩
    · have := code24_card h'
      rw [hV] at this
      norm_num at this
    · have := cocode24_card h'
      rw [hV] at this
      norm_num at this
  · obtain ⟨⟨hq, hA⟩, hV⟩ := luRow_Code24 hXN hXe h hX hfX
    refine ⟨hq, fun hr => ?_, fun _ => hA, fun ⟨_, _, hfr⟩ => ?_⟩
    · exfalso
      rcases hr with ⟨h', _⟩ | ⟨h', _⟩
      · have := card_of_binaryNine h'
        rw [hV] at this
        norm_num at this
      · have := card_of_code22 h'
        rw [hV] at this
        norm_num at this
    · exfalso
      have := rk_add_rkIdx (fixV X)
      rw [rk_of_card_lu hV] at this
      omega
  · obtain ⟨⟨hq, htop⟩, hV⟩ := luRow_Coc24 hXN hXe h hX hfX
    refine ⟨hq, fun hr => ?_, fun ⟨_, _, hfr⟩ => ?_, fun _ => htop⟩
    · exfalso
      rcases hr with ⟨h', _⟩ | ⟨h', _⟩
      · have := card_of_binaryNine h'
        rw [hV] at this
        norm_num at this
      · have := card_of_code22 h'
        rw [hV] at this
        norm_num at this
    · exfalso
      have := rk_add_rkIdx (fixV X)
      rw [rk_of_card_lu hV] at this
      omega

end CFSG.Quasithin.H13
