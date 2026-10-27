module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86ModelAssembly
public import CFSG.Quasithin.Recognition.CertTwoF4AmalgamLocalFinal

public section

namespace CFSG.Quasithin.Fan86.Model

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Sporadic.Schreier.Tits

theorem card_extSub_of_not_mem {M : Type*} [Group M] [Finite M] {H : Subgroup M} {q : M}
    {hq : q ∈ Subgroup.normalizer (H : Set M)} {hq2 : q * q ∈ H} (hqH : q ∉ H) :
    Nat.card (extSub H q hq hq2) = 2 * Nat.card H := by
  have h := Subgroup.relIndex_mul_card (H := H) (K := extSub H q hq hq2)
  rw [relIndex_extSub hqH, inf_eq_left.2 le_extSub] at h
  exact h.symm

section Generic

variable {M : Type*} [Group M] [Finite M] (d : IndexTwoLatticeData M)

theorem card_toLattice_S : Nat.card d.toLattice.S = 2 * Nat.card d.S :=
  card_extSub_of_not_mem (hq := d.q_norm_S) (hq2 := d.q_mul_self_mem_S)
    (fun h => d.q_not_mem (d.S_le_D h))

theorem card_toLattice_P₁ : Nat.card d.toLattice.P₁ = 2 * Nat.card d.P₁ :=
  card_extSub_of_not_mem (hq := d.q_norm_P₁) (hq2 := d.q_mul_self_mem_P₁)
    (fun h => d.q_not_mem (d.P₁_le_D h))

theorem card_toLattice_P₂ : Nat.card d.toLattice.P₂ = 2 * Nat.card d.P₂ :=
  card_extSub_of_not_mem (hq := d.q_norm_P₂) (hq2 := d.q_mul_self_mem_P₂)
    (fun h => d.q_not_mem (d.P₂_le_D h))

omit [Finite M] in
theorem relIndex_toLattice_P₁ : d.P₁.relIndex d.toLattice.P₁ = 2 :=
  relIndex_extSub (hq := d.q_norm_P₁) (hq2 := d.q_mul_self_mem_P₁)
    (fun h => d.q_not_mem (d.P₁_le_D h))

omit [Finite M] in
theorem relIndex_toLattice_P₂ : d.P₂.relIndex d.toLattice.P₂ = 2 :=
  relIndex_extSub (hq := d.q_norm_P₂) (hq2 := d.q_mul_self_mem_P₂)
    (fun h => d.q_not_mem (d.P₂_le_D h))

end Generic

set_option linter.unusedSectionVars false


theorem card_twoF4Lattice_S : Nat.card twoF4Lattice.S = 2 ^ 12 := by
  have h := card_toLattice_S twoF4Data
  change Nat.card twoF4Lattice.S = 2 * Nat.card (titsS.subgroupOf twoF4M) at h
  rw [h, card_subgroupOf_eq titsS_le_twoF4M, titsQS_facts.2.2.2]
  norm_num

theorem card_twoF4Lattice_P₁ : Nat.card twoF4Lattice.P₁ = 5 * 2 ^ 12 := by
  have h := card_toLattice_P₁ twoF4Data
  change Nat.card twoF4Lattice.P₁ = 2 * Nat.card (titsH.subgroupOf twoF4M) at h
  rw [h, card_subgroupOf_eq titsH_le_twoF4M, titsQH_facts.2.2.2]
  norm_num

theorem card_twoF4Lattice_P₂ : Nat.card twoF4Lattice.P₂ = 3 * 2 ^ 12 := by
  have h := card_toLattice_P₂ twoF4Data
  change Nat.card twoF4Lattice.P₂ = 2 * Nat.card (titsN.subgroupOf twoF4M) at h
  rw [h, card_subgroupOf_eq titsN_le_twoF4M, titsQN_facts.2.2.2]
  norm_num

theorem card_pCoreOf_twoF4Lattice_P₁ : Nat.card (pCoreOf 2 twoF4Lattice.P₁) = 2 ^ 10 := by
  rw [twoF4Lattice_P₁, card_pCoreOf_eq_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe twoF4H_le_twoF4M), card_pCoreOf_twoF4H]
  norm_num

theorem twoF4_titsH_le_normalizer :
    titsH ≤ Subgroup.normalizer (titsJ : Set (Equiv.Perm (Fin 1755))) := by
  obtain ⟨-, -, -, -, -, -, hJn, -⟩ := AT_Tits_intrinsic_local_pair
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer titsJ_le_titsH).1 hJn

theorem twoF4_titsN_le_normalizer :
    titsN ≤ Subgroup.normalizer (titsK : Set (Equiv.Perm (Fin 1755))) := by
  obtain ⟨-, -, -, -, -, -, -, hKn, -⟩ := AT_Tits_intrinsic_local_pair
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer titsK_le_titsN).1 hKn

theorem charTwo_twoF4Lattice_P₁ : CharTwo twoF4Lattice.P₁ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hCJ, -⟩ := AT_Tits_intrinsic_local_pair
  refine charTwo_of_index_le_two (X := titsH.subgroupOf twoF4M)
    (J := titsJ.subgroupOf twoF4M) (fun _ hx => Or.inl hx) ?_ ?_
    (fun _ hx => titsJ_le_titsH hx) ?_ (inf_centralizer_subgroupOf_le titsJ_le_twoF4M hCJ)
  · exact (relIndex_toLattice_P₁ twoF4Data).le
  · exact IsPGroup.of_card (n := 9) (by
      rw [card_subgroupOf_eq titsJ_le_twoF4M, titsQJ_facts.2.2.2]
      norm_num)
  · intro x hx
    rcases hx with hx | hx
    · exact mem_normalizer_subgroupOf (twoF4_titsH_le_normalizer hx)
    · have hx' : ((x * twoF4Q⁻¹ : twoF4M) : Equiv.Perm (Fin 1755)) ∈ titsH := hx
      have h1 := mem_normalizer_subgroupOf (M := twoF4M) (g := x * twoF4Q⁻¹)
        (twoF4_titsH_le_normalizer hx')
      have h2 : twoF4Q ∈ Subgroup.normalizer ((titsJ.subgroupOf twoF4M : Subgroup twoF4M) :
          Set twoF4M) := mem_normalizer_subgroupOf tπ_norm_J
      simpa using Subgroup.mul_mem _ h1 h2

theorem charTwo_twoF4Lattice_P₂ : CharTwo twoF4Lattice.P₂ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hCK⟩ := AT_Tits_intrinsic_local_pair
  refine charTwo_of_index_le_two (X := titsN.subgroupOf twoF4M)
    (J := titsK.subgroupOf twoF4M) (fun _ hx => Or.inl hx) ?_ ?_
    (fun _ hx => titsK_le_titsN hx) ?_ (inf_centralizer_subgroupOf_le titsK_le_twoF4M hCK)
  · exact (relIndex_toLattice_P₂ twoF4Data).le
  · exact IsPGroup.of_card (n := 10) (by
      rw [card_subgroupOf_eq titsK_le_twoF4M, titsQK_facts.2.2.2]
      norm_num)
  · intro x hx
    rcases hx with hx | hx
    · exact mem_normalizer_subgroupOf (twoF4_titsN_le_normalizer hx)
    · have hx' : ((x * twoF4Q⁻¹ : twoF4M) : Equiv.Perm (Fin 1755)) ∈ titsN := hx
      have h1 := mem_normalizer_subgroupOf (M := twoF4M) (g := x * twoF4Q⁻¹)
        (twoF4_titsN_le_normalizer hx')
      have h2 : twoF4Q ∈ Subgroup.normalizer ((titsK.subgroupOf twoF4M : Subgroup twoF4M) :
          Set twoF4M) := mem_normalizer_subgroupOf tπ_norm_K
      simpa using Subgroup.mul_mem _ h1 h2

theorem modelFacts_twoF4 :
    ∃ (Y : Type) (_ : Group Y) (T M₁ M₂ : Subgroup Y), IsTwistedF4Over 1 Y ∧
      IsYAmalgamPair T M₁ M₂ ∧ Hyp53 (GoldAmalgam.ofSubgroupPair M₁ M₂) ∧
      Nat.card ↥(M₁ ⊓ M₂) = 2 ^ 12 ∧ Nat.card ↥(pCoreOf 2 M₁) = 2 ^ 10 ∧
      Nat.card ↥(pCoreOf 2 M₂) = 2 ^ 11 := by
  have hO₁ : 4 * Nat.card (pCoreOf 2 twoF4Lattice.P₁) = 2 ^ 12 := by
    rw [card_pCoreOf_twoF4Lattice_P₁]
    norm_num
  obtain ⟨h53, hinf, hO₂⟩ := hyp53_of_lattice twoF4Lattice card_twoF4Lattice_S
    card_twoF4Lattice_P₁ card_twoF4Lattice_P₂ charTwo_twoF4Lattice_P₁
    charTwo_twoF4Lattice_P₂ hO₁
  refine ⟨↥twoF4M, inferInstance, twoF4Lattice.S, twoF4Lattice.P₁, twoF4Lattice.P₂,
    Or.inl ⟨rfl, ⟨(twoF4AutEquiv titsOutBound).symm⟩⟩, isYAmalgamPair_lattice _, h53, hinf,
    card_pCoreOf_twoF4Lattice_P₁, ?_⟩
  omega

end CFSG.Quasithin.Fan86.Model
