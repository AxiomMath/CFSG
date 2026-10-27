module

public import CFSG.LocalAnalysis.StandardType.GGKnownInputsPsuOrder
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatTypeDetOrders

public section

namespace CFSG.StandardType.SCFourCover

open CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.Orders

private theorem not_ten_mul_dvd_of_lt {g c a : ℕ} (hg : 0 < g) (ha : 0 < a) (ha10 : a < 10) :
    ¬ 10 * (g * c) ∣ g * a := by
  intro h
  rw [show 10 * (g * c) = g * (10 * c) by ring] at h
  have h2 : 10 ∣ a := (Dvd.intro c rfl).trans (Nat.dvd_of_mul_dvd_mul_left hg h)
  omega

theorem not_ordTwistedA_five_dvd_ordA {g n m : ℕ} (hg : 1 ≤ g) (hn : 1 ≤ n) (hgn : g ∣ n)
    (hm1 : 1 ≤ m) (hm : m ≤ 8) : ¬ ordTwistedA 5 (2 ^ n) ∣ ordA m (2 ^ g) := by
  intro hdvd
  obtain ⟨p, hp, hpU⟩ := exists_ppd_dvd_ordTwistedA_five hn
  obtain ⟨c, rfl⟩ := hgn
  obtain ⟨i, hi, hd⟩ := ((CFSG.SeitzReduction.F4Pilot.profile_idxA hm1 hg).prim p
    (10 * (g * c)) hp (by omega)).1 (hpU.trans hdvd)
  obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.mp hi
  exact not_ten_mul_dvd_of_lt hg (by omega) (by omega) hd

theorem not_ordTwistedA_five_dvd_ordBC {g n m : ℕ} (hg : 1 ≤ g) (hn : 1 ≤ n) (hgn : g ∣ n)
    (hm : m ≤ 4) : ¬ ordTwistedA 5 (2 ^ n) ∣ ordBC m (2 ^ g) := by
  intro hdvd
  obtain ⟨p, hp, hpU⟩ := exists_ppd_dvd_ordTwistedA_five hn
  obtain ⟨c, rfl⟩ := hgn
  obtain ⟨i, hi, hd⟩ := ((CFSG.SeitzReduction.F4Pilot.profile_idxBC (n := m) hg).prim p
    (10 * (g * c)) hp (by omega)).1 (hpU.trans hdvd)
  obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.mp hi
  exact not_ten_mul_dvd_of_lt hg (by omega) (by omega) hd

theorem not_ordTwistedA_five_dvd_ordD {g n m : ℕ} (hg : 1 ≤ g) (hn : 1 ≤ n) (hgn : g ∣ n)
    (hm1 : 1 ≤ m) (hm : m ≤ 5) : ¬ ordTwistedA 5 (2 ^ n) ∣ ordD m (2 ^ g) := by
  intro hdvd
  obtain ⟨p, hp, hpU⟩ := exists_ppd_dvd_ordTwistedA_five hn
  obtain ⟨c, rfl⟩ := hgn
  rcases ((CFSG.SeitzReduction.F4Pilot.profile_idxD hm1 hg).prim p (10 * (g * c)) hp
    (by omega)).1 (hpU.trans hdvd) with h | ⟨i, hi, h⟩
  · exact not_ten_mul_dvd_of_lt hg (by omega) (by omega) h
  · obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.mp hi
    exact not_ten_mul_dvd_of_lt hg (by omega) (by omega) h

end CFSG.StandardType.SCFourCover

end
