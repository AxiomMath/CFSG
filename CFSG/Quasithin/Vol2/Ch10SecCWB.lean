module

public import CFSG.Quasithin.H13.StatementsL6
public import CFSG.Quasithin.Vol2.Ch10StatementsInputs

public section

namespace CFSG.Quasithin.Vol2.Ch10

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13

theorem tmpL6_4_4_13_of (h : Stmt4_4_13) : TmpL6_4_4_13 := by
  intro G _ _ H S MH hs hnab hK hO hn hS hU
  obtain ⟨⟨P, hP, hPn⟩, hB⟩ := h G H S MH hs hnab hK hO hn hS hU
  refine ⟨⟨P, ⟨hP.1, hP.2.1, hP.2.2⟩,
    (Subgroup.normal_subgroupOf_iff_le_normalizer hP.1).mpr hPn⟩, fun B hBH => ?_⟩
  obtain ⟨hBMH, hBodd, hBidx⟩ := hBH
  obtain ⟨h1, h2⟩ := hB B hBMH hBodd hBidx
  refine ⟨h1, fun M Mp hM hSM hMH hMp hMpM hMN => ?_⟩
  have hset : ((B ⊓ sectionCentralizer Mp (pCoreOf 2 Mp) : Subgroup G) : Set G) =
      {b | b ∈ B ∧ ∀ m ∈ Mp, b * m * b⁻¹ * m⁻¹ ∈ pCoreOf 2 Mp} := by
    ext b
    constructor
    · rintro ⟨hb, -, -, hbm⟩
      exact ⟨hb, hbm⟩
    · rintro ⟨hb, hbm⟩
      have hbN : b ∈ Subgroup.normalizer (Mp : Set G) :=
        hMN (hMH ▸ hBMH hb : b ∈ M ⊓ H).1
      exact ⟨hb, hbN, CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Mp hbN, hbm⟩
  rw [hset]
  exact h2 M Mp hM hSM hMH hMp.symm hMpM hMN

end CFSG.Quasithin.Vol2.Ch10
