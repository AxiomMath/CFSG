module

public import CFSG.RankThree.PartOne.Q1327S.Abelian
public import CFSG.RankThree.PartOne.Q1327S.Arith
public import CFSG.RankThree.PartOne.Q1327S.Center
public import CFSG.RankThree.PartOne.Q1327S.Conf
public import CFSG.RankThree.PartOne.Q1327S.Cube
public import CFSG.RankThree.PartOne.Q1327S.HN
public import CFSG.RankThree.PartOne.Q1327S.J2
public import CFSG.RankThree.PartOne.Q1327S.Ly
public import CFSG.RankThree.PartOne.Q1327S.Orders
public import CFSG.RankThree.PartOne.CTP.StrongPSporadic

public section

namespace CFSG.RankThree.PartOne.Q1327S

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Q1327T CFSG.Blueprint TauCeti

theorem false_of_perm3
    {Q : Type} [Group Q] [Finite Q] {p g : ℕ} {Ē : Subgroup Q} (h : Row8Conf p g Q Ē)
    (hZ : Subgroup.center Q = ⊥) {s : SporadicName} (hs : s ∈ Census3.sporadicsThm3)
    (e : Q ≃* NativeSporadic.Carrier s)
    (hW : Nonempty (torusImage Ē ⊤ ≃* Equiv.Perm (Fin 3))) : False := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hsq : p ^ 2 ∣ Nat.card (NativeSporadic.Carrier s) := by
    rw [← Nat.card_congr e.toEquiv]
    exact p_sq_dvd_card h
  have hpair := CTP.sporadicPair_of_sq_dvd hs hp h.five_le hsq
  have hp7 : p ≠ 7 := ne_seven_of_dvd_two_pow_add_one h.p_dvd
  have hcen : ∀ P : Subgroup Q, IsPGroup p P → Ē ≤ P →
      P ≤ Subgroup.centralizer (Ē : Set Q) := fun P hP hEP =>
    le_centralizer_of_perm3 h hZ hW hP hEP
  rcases hpair with hNC | hAb
  · by_cases hLy : s = .Ly
    · subst hLy
      have h5 : p = 5 := by simpa [CTP.SporadicPairNC] using hNC
      subst h5
      exact false_Ly e h
    by_cases hHN : s = .HN
    · subst hHN
      have h5 : p = 5 := by simpa [CTP.SporadicPairNC] using hNC
      subst h5
      exact false_HN e h.card hcen
    · obtain ⟨hc3, hc4⟩ := cube_of_pairNC hNC hLy hHN hp7
      have hN : StrongP.HasNoncommPair p Q :=
        (CTP.hasNoncommPair_carrier hNC).map e.symm.toMonoidHom e.symm.injective
      have hcard : Nat.card Q = Nat.card (NativeSporadic.Carrier s) := Nat.card_congr e.toEquiv
      exact false_of_noncomm_cube hp h.card (by rw [hcard]; exact hc3) (by rw [hcard]; exact hc4)
        hN hcen
  · rcases hAb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact not_perm3_J2 e h.card hW
    · exact not_perm3_He e h.card hW
    · exact not_perm3_Suz e h.card hW
    · exact absurd rfl hp7

theorem row8U3Item_sporadic
    : Row8U3Item 5 := by
  intro Q _ _ p g Ē hS hc
  obtain ⟨s, hs, ⟨e0⟩⟩ := hS
  have hsimple : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hc.quasisimple.2.1
  have : IsSimpleGroup (CFSGIndex.sporadic s).Group := e0.symm.isSimpleGroup
  obtain ⟨e1⟩ := Census3.nonempty_carrier_mulEquiv_of_mem hs
  let e : Q ⧸ Subgroup.center Q ≃* NativeSporadic.Carrier s := e0.trans e1.symm
  have hZ : Subgroup.center Q = ⊥ :=
    center_eq_bot_of_sporadic hc.quasisimple hs e hc.prime hc.five_le hc.center_p
  refine ⟨hZ, fun hW => ?_⟩
  exfalso
  let eQ : Q ≃* NativeSporadic.Carrier s :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans e
  exact false_of_perm3 hc hZ hs eQ hW

end CFSG.RankThree.PartOne.Q1327S
