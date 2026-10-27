module

public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Quasithin.Background.F918Z4c1Ppd
public import CFSG.LocalAnalysis.SectionRank.SuzukiCover
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructureTransport

public section

namespace CFSG.Quasithin

open CFSG.Timmesfeld

theorem card_of_isSz {L : Type} [Group L] {n : ℕ} (hL : IsSz n L) :
    Nat.card L = ((2 ^ n) ^ 2 + 1) * (2 ^ n) ^ 2 * (2 ^ n - 1) := by
  obtain ⟨-, a, ha, K, _, _, rfl, hK, ⟨φ⟩⟩ := hL
  rw [Nat.card_congr φ.toEquiv, Nat.card_congr
    (CFSG.ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup hK).toEquiv]
  exact CFSG.SectionRank.card_suzukiMatrixGroup a ha

theorem four_mul_le_of_isSz {L : Type} [Group L] [Finite L] {n : ℕ} (hn : 3 ≤ n) (hL : IsSz n L)
    {F : Type} [Field F] [Finite F] {e d : ℕ} (hF : Nat.card F = 2 ^ e)
    (ρ : L →* Matrix.GeneralLinearGroup (Fin d) F) (hρ : Function.Injective ρ) :
    4 * n ≤ d * e := by
  have hk : 0 < 4 * n := by omega
  obtain ⟨r, hr⟩ := exists_isPrimitivePrimeDivisor (k := 4 * n) (by omega) (by omega)
  have h1 : r ∣ (2 ^ n) ^ 2 + 1 := by
    rw [← pow_mul, mul_comm n 2]
    exact (hr.dvd_add_one_iff hk _).mpr
      ⟨⟨1, by ring⟩, Nat.not_dvd_of_pos_of_lt (by omega) (by omega)⟩
  have hrL : r ∣ Nat.card L := by
    rw [card_of_isSz hL]
    exact (h1.mul_right _).mul_right _
  exact le_of_isPrimitivePrimeDivisor_dvd_card hF ρ hρ hr hk hrL

end CFSG.Quasithin
