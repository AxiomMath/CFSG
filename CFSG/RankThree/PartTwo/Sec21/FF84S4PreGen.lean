module

public import CFSG.RankThree.PartTwo.Sec21.FF84Defs
public import CFSG.GroupTheory.PCore.SubgroupCore

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84

variable {G : Type} [Group G] [Finite G]

theorem Opp_le (p : ℕ) (H : Subgroup G) : Opp p H ≤ H := Subgroup.map_subtype_le _

theorem coprime_card_Opp (p : ℕ) (H : Subgroup G) : Nat.Coprime p (Nat.card (Opp p H)) := by
  have := CFSG.coprime_card_pPrimeCore p ↥H
  rwa [← Subgroup.card_map_of_injective (Subgroup.subtype_injective H)] at this

theorem Opp_conj (p : ℕ) {H : Subgroup G} {g h : G} (hg : g ∈ H) (hh : h ∈ Opp p H) :
    g * h * g⁻¹ ∈ Opp p H := by
  obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hh
  have hN := (CFSG.pPrimeCore_normal (p := p) (G := ↥H)).conj_mem n hn ⟨g, hg⟩
  exact Subgroup.mem_map.2 ⟨_, hN, by simp⟩

theorem le_nor_Opp (p : ℕ) {H M : Subgroup G} (hM : M ≤ H) : M ≤ Nor (Opp p H) := fun g hg =>
  Subgroup.mem_normalizer_iff.2 fun h =>
    ⟨fun hh => Opp_conj p (hM hg) hh, fun hh => by
      have := Opp_conj p (H := H) (inv_mem (hM hg)) hh
      simpa [mul_assoc] using this⟩

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
