module

public import CFSG.StronglyEmbedded.TheoremSE.InvolutionCoreTransitivity
public import CFSG.StronglyEmbedded.TheoremSE.StrongEmbeddingCosetCardinality

public section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1

noncomputable section

theorem IsStronglyEmbedded.bender_quotient_borel_index
    {X : Type*} [Group X] [Finite X] {H : Subgroup X}
    (hH : IsStronglyEmbedded H) (hB : TheoremSEBenderConclusion H) :
    (((H ⊓ involutionCore X).subgroupOf (involutionCore X)).map
      (QuotientGroup.mk' (twoPrimeCore (involutionCore X)))).index = H.index := by
  let L : Subgroup X := involutionCore X
  let A : Subgroup L := (H ⊓ L).subgroupOf L
  let O : Subgroup L := twoPrimeCore L
  have hOA : O ≤ A := by
    intro x hx
    exact hB.2.1 (Subgroup.mem_map_of_mem L.subtype hx)
  have hmap : (A.map (QuotientGroup.mk' O)).index = A.index :=
    A.index_map_eq (QuotientGroup.mk'_surjective O) (by simpa using hOA)
  have hstab : MulAction.stabilizer L (QuotientGroup.mk 1 : conjugateCosetSpace H) = A := by
    ext x
    change (x : X) • (QuotientGroup.mk 1 : conjugateCosetSpace H) =
      QuotientGroup.mk 1 ↔ x ∈ A
    rw [← MulAction.mem_stabilizer_iff, baseCoset_stabilizer]
    exact ⟨fun hx => ⟨hx, x.property⟩, fun hx => hx.1⟩
  let : MulAction.IsPretransitive L (conjugateCosetSpace H) :=
    hH.involutionCore_isPretransitive
  calc
    (A.map (QuotientGroup.mk' O)).index = A.index := hmap
    _ = (MulAction.stabilizer L (QuotientGroup.mk 1 : conjugateCosetSpace H)).index :=
      congrArg Subgroup.index hstab.symm
    _ = Nat.card (conjugateCosetSpace H) := MulAction.index_stabilizer_of_transitive L _
    _ = H.index := H.index_eq_card.symm

theorem IsStronglyEmbedded.exists_bender_sylow_card
    {X : Type*} [Group X] [Finite X] {H : Subgroup X}
    (hH : IsStronglyEmbedded H) (hB : TheoremSEBenderConclusion H) :
    ∃ P : Sylow 2
      (((H ⊓ involutionCore X).subgroupOf (involutionCore X)).map
        (QuotientGroup.mk' (twoPrimeCore (involutionCore X)))),
      Nat.card P = H.index - 1 := by
  classical
  let L : Subgroup X := involutionCore X
  let O : Subgroup L := twoPrimeCore L
  let Q := L ⧸ O
  let B : Subgroup Q := ((H ⊓ L).subgroupOf L).map (QuotientGroup.mk' O)
  have hBQ : IsBorelSubgroup B := hB.2.2
  obtain ⟨P, _hPn, hreg⟩ := simpleBender_borel_normalSylow_regular hBQ hB.1
  have hcardCosets : Nat.card (Q ⧸ B) = H.index :=
    B.index_eq_card.symm.trans (hH.bender_quotient_borel_index hB)
  have hgt : 1 < Nat.card (Q ⧸ B) := by
    rw [hcardCosets]
    exact Subgroup.one_lt_index_of_ne_top hH.ne_top
  let : Nontrivial (Q ⧸ B) := Finite.one_lt_card_iff_nontrivial.mp hgt
  have hex : ∃ q : Q ⧸ B, q ≠ QuotientGroup.mk 1 := exists_ne _
  have hfix : ((P : Subgroup B).map B.subtype) ≤
      MulAction.stabilizer Q (QuotientGroup.mk 1 : Q ⧸ B) := by
    rw [baseCoset_stabilizer]
    exact Subgroup.map_subtype_le _
  refine ⟨P, ?_⟩
  have hc := hreg.natCard_compl_point hfix hex
  rw [Subgroup.card_map_of_injective B.subtype_injective, hcardCosets] at hc
  exact hc

theorem IsStronglyEmbedded.involutionCore_index_odd_of_bender
    {X : Type*} [Group X] [Finite X] {H : Subgroup X}
    (hH : IsStronglyEmbedded H) (hB : TheoremSEBenderConclusion H) :
    Odd (involutionCore X).index := by
  let L : Subgroup X := involutionCore X
  let O : Subgroup L := twoPrimeCore L
  let Q := L ⧸ O
  let B : Subgroup Q := ((H ⊓ L).subgroupOf L).map (QuotientGroup.mk' O)
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hSH⟩ := hH.containsSylowTwo
  obtain ⟨P, hPcard⟩ := hH.exists_bender_sylow_card hB
  have hdvd : Nat.card S ∣ Nat.card P := by
    rw [hPcard]
    exact hH.sylow_card_dvd_nonbase_cosets S hSH
  have hPdvdQ : Nat.card P ∣ Nat.card Q :=
    (Subgroup.card_subgroup_dvd_card (P : Subgroup B)).trans
      (Subgroup.card_subgroup_dvd_card B)
  have hQdvdL : Nat.card Q ∣ Nat.card L :=
    ⟨Nat.card O, Subgroup.card_eq_card_quotient_mul_card_subgroup O⟩
  have hSdL : Nat.card S ∣ Nat.card L := hdvd.trans (hPdvdQ.trans hQdvdL)
  have hScard := S.card_eq_multiplicity
  have hle : (Nat.card X).factorization 2 ≤ (Nat.card L).factorization 2 := by
    apply (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp
    rwa [hScard] at hSdL
  have hfactor : (Nat.card X).factorization 2 =
      L.index.factorization 2 + (Nat.card L).factorization 2 := by
    rw [← L.index_mul_card, Nat.factorization_mul
      (Subgroup.index_ne_zero_of_finite (H := L)) Nat.card_pos.ne']
    rfl
  have hzero : L.index.factorization 2 = 0 := by omega
  apply Nat.not_even_iff_odd.mp
  intro heven
  have hpos : 1 ≤ L.index.factorization 2 :=
    (Nat.prime_two.pow_dvd_iff_le_factorization
      (Subgroup.index_ne_zero_of_finite (H := L))).mp
      (by simpa using even_iff_two_dvd.mp heven)
  omega

end

end CFSG.BenderSuzuki
