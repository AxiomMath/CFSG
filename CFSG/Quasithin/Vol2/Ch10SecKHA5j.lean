module

public import CFSG.Quasithin.Vol2.Ch10SecKHA5d
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3A314Red

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem noSL25In_l3odd {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : IsPSL 3 p 1 X) : NoSL25In X := by
  refine noSL25In_of_card_lt fun E hE => ?_
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h
  have hchar : CharP F p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp le_rfl hF
  have h2 : (2 : F) ≠ 0 := Lin2.two_ne_zero_of_charP hp hp2
  have hE' : IsElemAbelian 2 (E.map e.toMonoidHom) := Lin2.isElemAbelian_map' hE _
  have hc : Nat.card (E.map e.toMonoidHom) = Nat.card E :=
    Lin2.card_map_of_inf_ker_eq_bot E _ fun x _ hx => e.injective (by rw [map_one] at *; exact hx)
  have h4 := Lin2.card_le_four_of_stated_proj h2 (CFSG.Assembly.LowTwoRank.StatedSL 3 F)
    (fun x hx => Lin2.det_eq_one_of_mem_statedSL hx) hE'
  omega

theorem noSL25In_u3odd {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : IsPSU 3 p 1 X) : NoSL25In X := by
  refine noSL25In_of_card_lt fun E hE => ?_
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h
  have hchar : CharP F p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp
      (k := 2) (by norm_num) (by rw [hF]; ring)
  have h2 : (2 : F) ≠ 0 := Lin2.two_ne_zero_of_charP hp hp2
  have hE' : IsElemAbelian 2 (E.map e.toMonoidHom) := Lin2.isElemAbelian_map' hE _
  have hc : Nat.card (E.map e.toMonoidHom) = Nat.card E :=
    Lin2.card_map_of_inf_ker_eq_bot E _ fun x _ hx => e.injective (by rw [map_one] at *; exact hx)
  have h4 := Lin2.card_le_four_of_stated_proj h2
    (CFSG.Assembly.LowTwoRank.StatedSU 3 (p ^ 1) F)
    (fun x hx => Lin2.det_eq_one_of_mem_statedSU hx) hE'
  omega

theorem noSL25In_sl3odd {X : Type} [Group X] [Finite X] {s : Bool} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h : IsSLEps3 s p X) : NoSL25In X := by
  refine noSL25In_of_card_lt fun E hE => ?_
  cases s
  · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
    have hchar : CharP F p :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp
        (k := 2) (by norm_num) hF
    have h2 : (2 : F) ≠ 0 := Lin2.two_ne_zero_of_charP hp hp2
    have := A5.G3.card_le_four_of_embedding h2
      ((CFSG.Assembly.LowTwoRank.StatedSU 3 p F).subtype.comp e.toMonoidHom)
      ((CFSG.Assembly.LowTwoRank.StatedSU 3 p F).subtype_injective.comp e.injective)
      (fun x => Lin2.det_eq_one_of_mem_statedSU (e x).2) hE
    omega
  · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
    have hchar : CharP F p :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp
        (k := 1) le_rfl (by rw [hF, pow_one])
    have h2 : (2 : F) ≠ 0 := Lin2.two_ne_zero_of_charP hp hp2
    have := A5.G3.card_le_four_of_embedding h2
      ((CFSG.Assembly.LowTwoRank.StatedSL 3 F).subtype.comp e.toMonoidHom)
      ((CFSG.Assembly.LowTwoRank.StatedSL 3 F).subtype_injective.comp e.injective)
      (fun x => Lin2.det_eq_one_of_mem_statedSL (e x).2) hE
    omega

theorem noSL25In_hat7 {X : Type} [Group X] [Finite X]
    (h : IsHat X (alternatingGroup (Fin 7))) : NoSL25In X := by
  obtain ⟨-, hc, ⟨e⟩⟩ := h
  have hcard := Lin2.OddRank.card_of_cover_alt (by norm_num) hc e
  refine noSL25In_of_card_lt fun E hE => ?_
  have := A5.G3.card_lt_sixteen_of_card_eq (m := 945) (by rw [hcard]; decide) (by omega) hE
  omega

theorem noSL25In_j1
    {X : Type} [Group X] [Finite X] (h : IsSporadic .J1 X) : NoSL25In X := by
  obtain ⟨e⟩ := h
  have hcard : Nat.card X = 175560 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.J1.card_J1
  refine noSL25In_of_card_lt fun E hE => ?_
  have := A5.G3.card_lt_sixteen_of_card_eq (m := 21945) (by rw [hcard]) (by omega) hE
  omega

end CFSG.Quasithin.Vol2.Ch10.SecF.C10KH
