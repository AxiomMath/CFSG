module

public import CFSG.Quasithin.EmptyFaithful.SzF53A1
public import CFSG.Quasithin.EmptyFaithful.SzF53MDefs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F53Mod

namespace F53B3.NoE

variable {G : Type} [Group G] [Finite G] {H S E : Subgroup G}

theorem exists_fixed_of_step (hq : Nonempty (OTwoQuot H ≃* Equiv.Perm (Fin 5)))
    (hE : F53EData H S E)
    (horth3 : ∀ F L X : Subgroup G, IsOrthSec F L X → ∀ d ∈ F, d ∉ cSecIn F L X →
      d ^ 3 ∈ cSecIn F L X → ∃ x ∈ X, x ∉ L ∧ d * x * d⁻¹ * x⁻¹ ∈ L)
    {d : G} (hd : d ∈ H) (hdQ : d ∉ pCoreOf 2 H) (hd3 : d ^ 3 ∈ pCoreOf 2 H)
    {L N : Subgroup G} (hs : IsChiefStep H E L N) (hnc : ¬ IsCentralStep H L N) :
    ∃ x ∈ N, x ∉ L ∧ d * x * d⁻¹ * x⁻¹ ∈ L := by
  obtain ⟨hcS, -, hn, hNat⟩ := hE.shape_five hq hs hnc
  have := hn
  have hOrth : IsOrthSec H L N := naturalSn_five_iff.mp hNat
  exact horth3 H L N hOrth d hd (by rw [hcS]; exact hdQ) (by rw [hcS]; exact hd3)

theorem exists_chiefStep_of_lt {H U A B : Subgroup G} (hA : IsNormalIn H U A)
    (hB : IsNormalIn H U B) (hAB : A < B) : ∃ J : Subgroup G, IsChiefStep H U A J ∧ J ≤ B := by
  obtain ⟨J, ⟨hJ, hAJ, hJB⟩, hmin⟩ := (wellFounded_lt (α := Subgroup G)).has_min
    {J | IsNormalIn H U J ∧ A < J ∧ J ≤ B} ⟨B, hB, hAB, le_rfl⟩
  refine ⟨J, ⟨hJ, hA, hAJ, fun K hK hAK hKJ => ?_⟩, hJB⟩
  rcases eq_or_lt_of_le hAK with h | h
  · exact Or.inl h.symm
  · right
    by_contra hne
    exact hmin K ⟨hK, h, hKJ.trans hJB⟩ (lt_of_le_of_ne hKJ hne)

theorem eq_of_key (hq : Nonempty (OTwoQuot H ≃* Equiv.Perm (Fin 5))) (hE : F53EData H S E)
    (horth3 : ∀ F L X : Subgroup G, IsOrthSec F L X → ∀ d ∈ F, d ∉ cSecIn F L X →
      d ^ 3 ∈ cSecIn F L X → ∃ x ∈ X, x ∉ L ∧ d * x * d⁻¹ * x⁻¹ ∈ L)
    {d : G} (hd : d ∈ H) (hdQ : d ∉ pCoreOf 2 H) (hd3 : d ^ 3 ∈ pCoreOf 2 H)
    {A B : Subgroup G} (hA : IsNormalIn H E A) (hB : IsNormalIn H E B) (hAB : A ≤ B)
    (key : ∀ x ∈ B, d * x * d⁻¹ * x⁻¹ ∈ A → x ∈ A) : B = A := by
  by_contra hne
  obtain ⟨J, hJ, hJB⟩ := exists_chiefStep_of_lt hA hB (lt_of_le_of_ne hAB (Ne.symm hne))
  have hnc : ¬ IsCentralStep H A J := fun hc => by
    refine absurd (fun x hx => key x (hJB hx) (hc d hd x hx)) ?_
    intro hJA
    exact absurd (le_antisymm hJA hJ.2.2.1.le) hJ.2.2.1.ne'
  obtain ⟨x, hxJ, hxA, hdx⟩ := exists_fixed_of_step hq hE horth3 hd hdQ hd3 hJ hnc
  exact hxA (key x (hJB hxJ) hdx)

end F53B3.NoE

end CFSG.Quasithin
