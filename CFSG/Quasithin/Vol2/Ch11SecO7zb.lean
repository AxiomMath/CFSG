module

public import CFSG.Quasithin.Vol2.Ch11SecO7za

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Blueprint

namespace C10KH

variable {Y : Type} [Group Y] [Finite Y] {B L : Subgroup Y} {X : Type} [Group X]


theorem a312List11_nonquasi {n : ℕ} (e : ModO2 B ≃* X) (hIn : InLists X n)
    (h : A312Nonquasi B L) : n = 2 ∧ ⁅(CFSG.oddCore ↥L).map L.subtype, L⁆ ≠ ⊥ ∧
      L = B ⊔ (CFSG.oddCore ↥L).map L.subtype := by
  have : Finite X := Finite.of_equiv _ e.toEquiv
  obtain ⟨hXq, hXZ⟩ := lists_qs hIn
  obtain ⟨hn, hl, -, -⟩ := id hIn
  dsimp only [A312Nonquasi] at h
  rcases h with ⟨hc, hL, q, hq, hq2, ⟨f⟩⟩ | ⟨-, -, N, hNn, hN, ⟨f⟩⟩
  · refine ⟨?_, hc, hL⟩
    rcases hl with h2 | ⟨hn2, -⟩
    · exfalso
      have hBL : B ≤ L := hL ▸ le_sup_left
      by_cases hq3 : q = 3
      · subst hq3
        have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
        have hLc := (CFSG.oddCore ↥L).card_eq_card_quotient_mul_card_subgroup
        rw [Nat.card_congr f.toEquiv, CFSG.GorensteinWalter.sl2_card_formula, Nat.card_zmod]
          at hLc
        obtain ⟨k, hk⟩ :=
          CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog.odd_card_oddCore (G := ↥L)
        have h16 : 2 ^ 6 ∣ Nat.card ↥L :=
          (two_pow_six_dvd hn h2).trans ((card_dvd_B e).trans (Subgroup.card_dvd_of_le hBL))
        rw [hLc, hk] at h16
        norm_num at h16
        omega
      · have hq5 : 5 ≤ q := five_le_of_prime hq (by have := hq.two_le; omega)
        have : Fact q.Prime := ⟨hq⟩
        have hsup : B.subgroupOf L ⊔ CFSG.oddCore ↥L = ⊤ := by
          have h1 := Subgroup.subgroupOf_sup (A := B) (A' := (CFSG.oddCore ↥L).map L.subtype)
            hBL (Subgroup.map_subtype_le _)
          have hO' : ((CFSG.oddCore ↥L).map L.subtype).subgroupOf L = CFSG.oddCore ↥L :=
            Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
          rw [← hL, Subgroup.subgroupOf_self, hO'] at h1
          exact h1.symm
        have hsurj := surjective_of_sup_eq hsup
        obtain ⟨c, hc3, hcX⟩ := card_of_surj_sl2 e hXq hXZ hq5
          (f.toMonoidHom.comp (((QuotientGroup.mk' (CFSG.oddCore ↥L)).comp
            (B.subgroupOf L).subtype).comp (Subgroup.subgroupOfEquivOfLe hBL).symm.toMonoidHom))
          (f.surjective.comp (hsurj.comp (Subgroup.subgroupOfEquivOfLe hBL).symm.surjective))
        exact list2_ne_artin hn h2 (Odd.of_dvd_nat (by decide) hc3) (hq.odd_of_ne_two hq2)
          (by omega) hcX
    · exact hn2
  · exfalso
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hsup : B.subgroupOf (B ⊔ (CFSG.oddCore ↥L).map L.subtype) ⊔ N = ⊤ := by
      have h1 := Subgroup.subgroupOf_sup (A := B) (A' := (CFSG.oddCore ↥L).map L.subtype)
        (le_sup_left : B ≤ B ⊔ (CFSG.oddCore ↥L).map L.subtype) le_sup_right
      rw [Subgroup.subgroupOf_self, ← hN] at h1
      exact h1.symm
    have hsurj := surjective_of_sup_eq hsup
    have hBO : B ≤ B ⊔ (CFSG.oddCore ↥L).map L.subtype := le_sup_left
    obtain ⟨c, hc3, hcX⟩ := card_of_surj_sl2 e hXq hXZ le_rfl
      (f.toMonoidHom.comp (((QuotientGroup.mk' N).comp
        (B.subgroupOf (B ⊔ (CFSG.oddCore ↥L).map L.subtype)).subtype).comp
        (Subgroup.subgroupOfEquivOfLe hBO).symm.toMonoidHom))
      (f.surjective.comp (hsurj.comp (Subgroup.subgroupOfEquivOfLe hBO).symm.surjective))
    have h180 : Nat.card X ∣ 180 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hc3 with rfl | rfl
      · norm_num at hcX
        exact ⟨3, by omega⟩
      · norm_num at hcX
        exact ⟨1, by omega⟩
    exact lists_not_dvd hIn h180 (by norm_num) (by norm_num) (by norm_num)

end C10KH


theorem a312List11Fact_holds : A312List11Fact := by
  intro Y _ _ B L X _ n hn ⟨e⟩ hl hA hE h
  have hIn : C10KH.InLists X n := ⟨hn, hl, hA, hE⟩
  rcases h with h | h
  · obtain ⟨h2, hc⟩ := C10KH.a312List11_case e hIn h
    refine ⟨h2, ?_⟩
    rcases hc with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  · obtain ⟨h2, hc, hL⟩ := C10KH.a312List11_nonquasi e hIn h
    exact ⟨h2, Or.inr (Or.inr (Or.inr ⟨hc, hL⟩))⟩

end CFSG.Quasithin.Vol2.Ch11.SecE
