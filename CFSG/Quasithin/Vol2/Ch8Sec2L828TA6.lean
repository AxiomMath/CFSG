module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828D

public section

namespace CFSG.Quasithin.H13

open CFSG.Quasithin

theorem nine_dvd_card_of_alternatingNatural_six {W : Type*} [CommGroup W]
    {H : Subgroup (MulAut W)} (hH : AlternatingNatural H ⊤ ⊥ 6) : 9 ∣ Nat.card ↥H := by
  have hne : H ≠ ⊥ := ne_bot_of_alternatingNatural_828 (Or.inr rfl) hH
  obtain ⟨π₀, hsurj₀, -⟩ := hH
  obtain ⟨π, hsurj⟩ : ∃ π : ↥(alternatingGroup (Fin 6)) →* ↥H, Function.Surjective π :=
    ⟨π₀, hsurj₀⟩
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hker : π.ker = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal π.ker with h | h
    · exact h
    ·
      exfalso
      apply hne
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      obtain ⟨g, hg⟩ := hsurj ⟨x, hx⟩
      have hgk : g ∈ π.ker := by
        rw [h]
        exact Subgroup.mem_top g
      rw [MonoidHom.mem_ker] at hgk
      have hx1 : (⟨x, hx⟩ : ↥H) = 1 := by
        rw [← hg, hgk]
      exact congrArg Subtype.val hx1
  have hbij : Function.Bijective π := ⟨(MonoidHom.ker_eq_bot_iff π).mp hker, hsurj⟩
  have hcard : Nat.card ↥H = Nat.card ↥(alternatingGroup (Fin 6)) :=
    (Nat.card_congr (Equiv.ofBijective π hbij)).symm
  rw [hcard, nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

end CFSG.Quasithin.H13
