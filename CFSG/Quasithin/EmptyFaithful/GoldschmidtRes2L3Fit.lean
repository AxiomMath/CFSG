module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.MinimalInvariantCommutator
public import CFSG.RankThree.Coprime.ThompsonElementaryComplement
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.theorem_3_6

public section

namespace CFSG.Quasithin.Gap6R2.L3

open scoped commutatorElement

variable {H : Type} [Group H] [Finite H]

theorem odd_card_of_forall_odd {R : Subgroup H} (hR : ∀ x ∈ R, Odd (orderOf x)) :
    Odd (Nat.card R) := by
  by_contra hcon
  have h2 : 2 ∣ Nat.card R := by
    rw [Nat.not_odd_iff_even] at hcon
    exact even_iff_two_dvd.mp hcon
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hx2 : orderOf (x : H) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
  have := hR x x.2
  rw [hx2] at this
  exact (Nat.not_odd_iff_even.mpr even_two) this

theorem coprime_card_of_isPGroup_two_of_odd {A R : Subgroup H} (hA : IsPGroup 2 A)
    (hR : Odd (Nat.card R)) : Nat.Coprime (Nat.card A) (Nat.card R) := by
  obtain ⟨n, hn⟩ := hA.exists_card_eq
  rw [hn]
  exact Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hR)

theorem commutator_eq_bot_of_minimal {Y Tb Vb : Subgroup H}
    (hYc : ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) (hYodd : ∀ x ∈ Y, Odd (orderOf x))
    (hT2 : IsPGroup 2 Tb) (hVT : Vb ≤ Tb)
    (hTY : Tb ≤ Subgroup.normalizer (Y : Set H))
    (hTV : Tb ≤ Subgroup.normalizer (Vb : Set H))
    (hmin : ∀ B : Subgroup H, B ≤ Y → B ≠ ⊥ → Tb ≤ Subgroup.normalizer (B : Set H) →
      (∀ B' : Subgroup H, B' ≤ B → Tb ≤ Subgroup.normalizer (B' : Set H) → B' ≠ ⊥ → B' = B) →
      ⁅B, Vb⁆ = ⊥) :
    ⁅Y, Vb⁆ = ⊥ := by
  by_contra hne
  obtain ⟨R, ⟨hRY, hRn, hRne⟩, hRmin⟩ := (wellFounded_lt (α := Subgroup H)).has_min
    {R : Subgroup H | R ≤ Y ∧ Tb ≤ Subgroup.normalizer (R : Set H) ∧ ⁅R, Vb⁆ ≠ ⊥}
    ⟨Y, le_rfl, hTY, hne⟩
  have hVR : Vb ≤ Subgroup.normalizer (R : Set H) := hVT.trans hRn
  have hRodd : Odd (Nat.card R) := odd_card_of_forall_odd fun x hx => hYodd x (hRY hx)
  have hcop : Nat.Coprime (Nat.card Vb) (Nat.card R) :=
    coprime_card_of_isPGroup_two_of_odd (hT2.to_le hVT) hRodd
  have hRself : ⁅R, Vb⁆ = R :=
    GorensteinWalter.commutator_eq_self_of_minimal_invariant_coprime Tb R Vb hRn hTV hVR hcop hRne
      fun R' hR'R hR'n hR'ne => by
        by_contra hnot
        exact hRmin R' ⟨hR'R.trans hRY, hR'n, hR'ne⟩
          (lt_of_le_of_ne hR'R fun h => hnot (h ▸ le_rfl))
  have hRbot : R ≠ ⊥ := by
    rintro rfl
    exact hRne (Subgroup.commutator_bot_left Vb)
  obtain ⟨B, ⟨hBR, hBn, hBne⟩, hBmin⟩ := (wellFounded_lt (α := Subgroup H)).has_min
    {B : Subgroup H | B ≤ R ∧ Tb ≤ Subgroup.normalizer (B : Set H) ∧ B ≠ ⊥}
    ⟨R, le_rfl, hRn, hRbot⟩
  have hB : ⁅B, Vb⁆ = ⊥ :=
    hmin B (hBR.trans hRY) hBne hBn fun B' hB'B hB'n hB'ne =>
      eq_of_le_of_not_lt hB'B (hBmin B' ⟨hB'B.trans hBR, hB'n, hB'ne⟩)
  have hBc : B ≤ Subgroup.centralizer (Vb : Set H) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hB
  have hfit : ⁅Vb, R⁆ ⊓ Subgroup.centralizer (Vb : Set H) = ⊥ :=
    CFSG.RankThree.Coprime.commutator_inf_centralizer_eq_bot
      (fun x hx y hy => hYc x (hRY hx) y (hRY hy)) hVR hcop
  rw [Subgroup.commutator_comm, hRself] at hfit
  exact hBne (eq_bot_iff.mpr (hfit ▸ le_inf hBR hBc))

end CFSG.Quasithin.Gap6R2.L3
