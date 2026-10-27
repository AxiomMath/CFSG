module

public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.Quasithin

namespace A38

theorem oddCore_eq_pPrimeCore_two (X : Type*) [Group X] :
    CFSG.oddCore X = CFSG.pPrimeCore 2 X := by
  unfold CFSG.oddCore CFSG.pPrimeCore
  congr 1
  ext N
  simp [Nat.coprime_two_left]

theorem odd_card_oddCore (X : Type*) [Group X] [Finite X] : Odd (Nat.card (CFSG.oddCore X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [oddCore_eq_pPrimeCore_two]
  exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card

theorem oddCore_subgroupOf_of_normal {X : Type*} [Group X] [Finite X] (L : Subgroup X)
    [L.Normal] : (CFSG.oddCore X).subgroupOf L = CFSG.oddCore ↥L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · refine le_sSup ⟨inferInstance, ?_⟩
    have h1 : Nat.card ↥((CFSG.oddCore X).subgroupOf L) = Nat.card ↥(CFSG.oddCore X ⊓ L) := by
      rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective L.subtype_injective]
    rw [h1]
    exact (odd_card_oddCore X).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  · have hchar : (CFSG.oddCore ↥L).Characteristic := by
      rw [oddCore_eq_pPrimeCore_two]
      infer_instance
    have hN : ((CFSG.oddCore ↥L).map L.subtype).Normal := ConjAct.normal_of_characteristic_of_normal
    have hle : (CFSG.oddCore ↥L).map L.subtype ≤ CFSG.oddCore X := by
      refine le_sSup ⟨hN, ?_⟩
      rw [Subgroup.card_map_of_injective L.subtype_injective]
      exact odd_card_oddCore ↥L
    exact Subgroup.map_le_iff_le_comap.mp hle

theorem isQuasisimple_map_oddCore {X : Type*} [Group X] [Finite X] (L : Subgroup X) [L.Normal]
    (hL : CFSG.IsQuasisimple (↥L ⧸ CFSG.oddCore ↥L)) :
    CFSG.IsQuasisimple ↥(L.map (QuotientGroup.mk' (CFSG.oddCore X))) := by
  let ρ : X →* X ⧸ CFSG.oddCore X := QuotientGroup.mk' (CFSG.oddCore X)
  let φ : ↥L →* ↥(L.map ρ) := ρ.subgroupMap L
  have hφ : Function.Surjective φ := ρ.subgroupMap_surjective L
  have hker : φ.ker = CFSG.oddCore ↥L := by
    rw [← oddCore_subgroupOf_of_normal L]
    ext x
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : ρ (x : X) = 1 := congrArg Subtype.val h
      exact (QuotientGroup.eq_one_iff _).mp h1
    · intro h
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff _).mpr h
  let e : (↥L ⧸ φ.ker) ≃* ↥(L.map ρ) := QuotientGroup.quotientKerEquivOfSurjective φ hφ
  have e2 : (↥L ⧸ CFSG.oddCore ↥L) ≃* (↥L ⧸ φ.ker) :=
    QuotientGroup.quotientMulEquivOfEq hker.symm
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (e2.trans e) hL

end A38

end CFSG.Quasithin
