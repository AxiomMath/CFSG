module

public import CFSG.Quasithin.EmptyFaithful.S153QPC1
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223Ord3
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P2Cfg

public section

namespace CFSG.Quasithin.S15223

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem genByOrderThree_of_lin2 [Finite G] {Y : Subgroup G} (hY : IsShort2 Y) {n : ℕ}
    (hn : 1 < n) (hlin : IsLin2Type Y n) : GenByOrderThree Y := by
  have h3 : 3 ∣ Nat.card Y := three_dvd_card_of_type (Or.inr ⟨n, hn, hlin⟩)
  obtain ⟨F, hFf, hFfin, hcard, α, hαs, hαk, -⟩ := hlin
  have hq : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card]; exact hcard
  have : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      hn.le hq
  have h4 : 4 ≤ Nat.card F := by
    rw [hq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hsimple : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
    CFSG.Quasithin.QP.sl2_isSimpleGroup h4
  exact genByOrderThree_of_epi_simple hY.1 hαs hαk h3

end CFSG.Quasithin.S15223
