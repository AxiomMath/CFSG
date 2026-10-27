module

public import CFSG.Quasithin.Vol2.Ch8Sec2D3Inputs
public import CFSG.Quasithin.Vol2.Ch8Sec2D5Inputs
public import CFSG.Quasithin.Background.HSecQuot

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative

@[expose] def OneBL3Nine5_828 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    Hyp8_2_1 T L I → ∀ _ : IsMulCommutative ↥(fsuV T I), Case8_2 T L I →
      ∀ (H : Subgroup G) (h : G) (k : ℕ), IsHStar T (fsuM T L) H → h ∈ H →
        Concl822 T L I H h k → (∃ n : ℕ, Row711L3Nine T L I n) →
        Nonempty (E2.StarQuot (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h) ≃*
          DihedralGroup 5) →
        ∀ K : Subgroup G, quasithinIsCComponent K
            (Subgroup.normalizer (ch82U (fsuV T I) h : Set G)) →
          ch82LU L (ch82U (fsuV T I) h) ≤ K → K = ch82LU L (ch82U (fsuV T I) h)

theorem step828OneB_of (hthree : Stmt8_2_9_three) (h8283 : Step828Three) (h825 : Stmt8_2_5)
    (hL3 : OneBL3Nine5_828) : Step828OneB := by
  intro G _ _ T L I hyp h731 h821 hc hrow H h k hH hh hC hcase K hK hLUK
  have hno24 : ¬ Row711M24Code T L I := hthree G T L I hyp h731 h821 hc hrow
  rcases hcase with ⟨hrow', m, hm3, ⟨e⟩⟩ | h24
  · have h3 := (h8283 G T L I hyp h731 h821 hc hrow H h k hH hh hC).1
    have hC5 := h825 G T L I hyp h731 h821 hc hrow H h k hH hh hC
    rcases h3 with ⟨hk1, ⟨eD3⟩⟩ | hP | ⟨hrowD, hk1, ⟨eD5⟩⟩
    ·
      exfalso
      apply hm3
      have hcard := Nat.card_congr (e.symm.trans eD3).toEquiv
      have hpos : 0 < Nat.card (E2.StarQuot (fsuM T L ⊓ ch82I (fsuV T I) h)
          (ch82I (fsuV T I) h)) := Nat.card_pos
      have hm0 : m ≠ 0 := by
        rintro rfl
        have : Nat.card (DihedralGroup 0) = 0 := Nat.card_eq_zero_of_infinite
        rw [Nat.card_congr e.toEquiv, this] at hpos
        exact lt_irrefl 0 hpos
      haveI : NeZero m := ⟨hm0⟩
      rw [DihedralGroup.nat_card, DihedralGroup.nat_card] at hcard
      have : m = 3 := by omega
      rw [this]
    ·
      exfalso
      have hk : k = 1 := by
        rcases hrow' with ⟨n, hr⟩ | hr
        · have : (k : ℕ∞) = 1 := hC5.1.symm.trans (hC5.2.2.2.1 ⟨n, hr⟩).1
          exact_mod_cast this
        · have : (k : ℕ∞) = 1 := hC5.1.symm.trans (hC5.2.2.2.2.1 hr).1
          exact_mod_cast this
      rw [hk] at hP
      obtain ⟨⟨-, -, -, h22, -⟩, -⟩ := hP
      exact absurd rfl h22
    · rcases hrowD with hL | h24'
      · exact hL3 G T L I hyp h731 h821 hc hrow H h k hH hh hC hL ⟨eD5⟩ K hK hLUK
      · exact absurd h24' hno24
  · exact absurd h24 hno24

end CFSG.Quasithin.H13
