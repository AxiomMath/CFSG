module

public import CFSG.Quasithin.Vol2.Ch10SecA1012P5One
public import CFSG.Quasithin.Vol2.Ch10SecA1012P5Sz
public import CFSG.Quasithin.Vol2.Ch10SecA1012P5Orth
public import CFSG.Quasithin.Vol2.Ch10SecA1011

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem not_case_three_of_case_four {n : ℕ} (h4 : Ch10.Case10_1_1Four T L I n) :
    ¬ Ch10.Case10_1_1Three T L I := by
  obtain ⟨hn, ⟨K, _, _, hK, ⟨e⟩⟩, -⟩ := h4
  rintro ⟨⟨e'⟩, -⟩
  have h1 := (Nat.card_congr e.toEquiv).symm.trans (Nat.card_congr e'.toEquiv)
  rw [card_SL_two_pow hK, card_SL_three_zmod_two] at h1
  have h2 : 2 ^ (2 * n) * (4 ^ (2 * n) - 1) = 2 ^ 3 * 21 := h1.trans (by norm_num)
  obtain ⟨h3, -⟩ := two_pow_mul_odd_inj (odd_four_pow_sub_one (by omega)) (by decide) h2
  omega

theorem part_five
    (hF : Facts10_1) (hFT : FactsTorus) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h322 : TmpL6_3_2_2_two) (hshape : Stmt7_0_1_shape)
    (h42 : AsB42) (h51 : AsB51) (h154 : AsB15Part4) (h116 : ASInputs.AS_I_1_6_one)
    (h3210 : TmpL6_3_2_10_nine) (hyp : Ch10.Hyp10 G T L I) :
    ¬ Ch10.LBarL32 L → ∀ D : Subgroup G, Lin2.IsHallTwoPrimeOf D (B0 T L) →
      ((∃ n, Ch10.Case10_1_1One T L I n) ∨ Ch10.Case10_1_1Seven T L I →
        D ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) = ⊥) ∧
      ∀ n : ℕ, Ch10.Case10_1_1Four T L I n →
        ∃ f : ↥(D ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) →*
          Multiplicative (ZMod (2 ^ n + 1) × ZMod (2 ^ n + 1)), Function.Injective f := by
  intro _ D hD
  refine ⟨?_, fun n h4 => ?_⟩
  · rintro (⟨n, h1⟩ | h7)
    · exact inf_centralizer_eq_bot_of_case_one h37 h38 h322 hyp h1 hD
    · obtain ⟨m, hsz, -⟩ := id h7
      have hC0 := fsuCVM_eq_bot hF h37 h38 h322 hshape h42 h51 h154 h116 h3210 hyp
        (not_cases13_of_suzuki hsz)
      exact inf_centralizer_eq_bot_of_case_seven hFT.sz h37 h38 h322 hyp h7 hC0 hD
  · by_cases h1 : ∃ m, Ch10.Case10_1_1One T L I m
    · obtain ⟨m, h1⟩ := h1
      have hbot := inf_centralizer_eq_bot_of_case_one h37 h38 h322 hyp h1 hD
      refine ⟨1, fun a b _ => Subtype.ext ?_⟩
      rw [Subgroup.mem_bot.mp (hbot.le a.2), Subgroup.mem_bot.mp (hbot.le b.2)]
    · have hC0 := fsuCVM_eq_bot hF h37 h38 h322 hshape h42 h51 h154 h116 h3210 hyp
        (fun h => h.elim h1 (not_case_three_of_case_four h4))
      exact exists_injective_of_case_four hFT.orth h37 h38 h322 hyp h4 hC0 hD

end CFSG.Quasithin.Vol2.Ch10.SecA
