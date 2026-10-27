module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4D1Par

public section

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open

namespace CFSG.Quasithin.S15223P4.D1

variable {G : Type} [Group G] [Finite G] {X A P : Subgroup G}

theorem card_eq_of_overgroup (ψ : OTwoQuot X ≃* SL3F2) (hA : IsSylowTwoOf A X) (hAP : A ≤ P)
    (hPX : P ≤ X) (hne : P ≠ X) (h3 : 3 ∣ Nat.card P) : Nat.card P = 3 * Nat.card A := by
  have hρ := rhoOf_surjective ψ
  have hk := rhoOf_ker_isPGroup ψ
  have hA' := sylow_subgroupOf_top hA
  have hkA : (rhoOf ψ).ker ≤ A.subgroupOf X := SzN2.ker_le_of_isSylowTwoOf hk hA'
  have hAP' : A.subgroupOf X ≤ P.subgroupOf X := fun a ha => hAP ha
  have hkP : (rhoOf ψ).ker ≤ P.subgroupOf X := hkA.trans hAP'
  have h8 := card_sylow_SL3F2 (isSylowTwoOf_top_map_of_surjective hA' (rhoOf ψ) hρ)
  have e1 := card_eq_card_map_mul_card_ker (rhoOf ψ) hρ hkP
  have e2 := card_eq_card_map_mul_card_ker (rhoOf ψ) hρ hkA
  have c1 : Nat.card (P.subgroupOf X) = Nat.card P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPX).toEquiv
  have c2 : Nat.card (A.subgroupOf X) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA.1).toEquiv
  rw [h8] at e2
  set Pb : Subgroup SL3F2 := (P.subgroupOf X).map (rhoOf ψ) with hPb
  have h8d : 8 ∣ Nat.card Pb := by
    have hle : (A.subgroupOf X).map (rhoOf ψ) ≤ Pb := Subgroup.map_mono hAP'
    have := Subgroup.card_dvd_of_le hle
    rwa [h8] at this
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card (p := 2)).mp hk
  have h3d : 3 ∣ Nat.card Pb := by
    have h3' : 3 ∣ Nat.card Pb * Nat.card (rhoOf ψ).ker := by rw [← e1, c1]; exact h3
    rw [hj] at h3'
    have hcop : Nat.Coprime 3 (2 ^ j) := Nat.Coprime.pow_right _ (by norm_num)
    exact hcop.dvd_of_dvd_mul_right h3'
  have h24 : 24 ∣ Nat.card Pb := by
    have : Nat.Coprime 8 3 := by norm_num
    exact (Nat.Coprime.mul_dvd_of_dvd_of_dvd this h8d h3d : 8 * 3 ∣ Nat.card Pb)
  have hdvd : Nat.card Pb ∣ 168 := by
    have := Subgroup.card_subgroup_dvd_card Pb
    rwa [card_SL3F2] at this
  have hPb24 : Nat.card Pb = 24 := by
    obtain ⟨m, hm⟩ := h24
    have hm' : 24 * m ∣ 24 * 7 := by rwa [← hm]
    have hm7 : m ∣ 7 := Nat.dvd_of_mul_dvd_mul_left (by norm_num) hm'
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).1 hm7 with h | h
    · rw [hm, h]
    · exfalso
      apply hne
      have htop : Pb = ⊤ := Subgroup.eq_top_of_card_eq Pb (by rw [hm, h, card_SL3F2])
      have hcm : Pb.comap (rhoOf ψ) = P.subgroupOf X := Subgroup.comap_map_eq_self hkP
      rw [htop, Subgroup.comap_top] at hcm
      have : P.subgroupOf X = ⊤ := hcm.symm
      rw [Subgroup.subgroupOf_eq_top] at this
      exact le_antisymm hPX this
  rw [hPb24] at e1
  omega

end CFSG.Quasithin.S15223P4.D1
