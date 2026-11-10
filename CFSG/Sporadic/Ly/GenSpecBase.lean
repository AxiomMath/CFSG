
module

public import CFSG.Sporadic.Ly.Primitive
public import CFSG.Sporadic.Ly.GenOmega

@[expose] public section

namespace CFSG.Sporadic.Ly

open CFSG.Sporadic.Th (wordG)
open CFSG.Sporadic.Fi23 (slpG slpG_eq)
open CFSG.Sporadic.Ly.Gen CFSG.Sporadic.Ly.Omega CFSG.Sporadic.LySchreier MulAction

section

noncomputable def genGs (j : ℕ) : J := slpG genG genWords j

theorem genG_eq_seedLetter : (genG : ℤ → J) = seedLetter := by
  funext z
  unfold genG seedLetter
  rfl

theorem genGs_eq (j : ℕ) : genGs j = slpG seedLetter genWords j := by
  unfold genGs
  rw [genG_eq_seedLetter]

abbrev GenFacts : Prop := LyGenFacts

theorem genFacts : GenFacts := ly_word_facts.1

theorem gen_a_u (hF : GenFacts) : a * genGs 2 = genGs 2 * a := by
  rw [genGs_eq]
  exact hF.2.2.2.1

theorem gen_a_z (hF : GenFacts) : a * genGs 4 = genGs 4 * a := by
  rw [genGs_eq]
  exact hF.2.2.2.2.1

theorem gen_u_t (hF : GenFacts) : genGs 2 ^ 7 * genGs 5 = genGs 5 * genGs 2 ^ 7 := by
  rw [genGs_eq, genGs_eq]
  exact hF.2.2.2.2.2.1

theorem orderOf_genU (hF : GenFacts) : orderOf (genGs 2) = 21 := by
  rw [genGs_eq]
  exact orderOf_eq_21 hF.1 hF.2.1 hF.2.2.1

theorem eleven_dvd_orderOf_genZ (hF : GenFacts) : 11 ∣ orderOf (genGs 4) := by
  rw [genGs_eq]
  have h22 : orderOf (genZ : J) ∣ 22 := orderOf_dvd_of_pow_eq_one hF.2.2.2.2.2.2.1
  have h2 : ¬ orderOf (genZ : J) ∣ 2 := fun h => hF.2.2.2.2.2.2.2.1 (orderOf_dvd_iff_pow_eq_one.1 h)
  have hd : orderOf (genZ : J) ∈ Nat.divisors 22 := Nat.mem_divisors.2 ⟨h22, by norm_num⟩
  have e : Nat.divisors 22 = {1, 2, 11, 22} := by decide
  rw [e] at hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  change 11 ∣ orderOf (genZ : J)
  rcases hd with h | h | h | h
  · exact absurd (by rw [h]; exact one_dvd 2) h2
  · exact absurd (by rw [h]) h2
  · rw [h]
  · rw [h]
    norm_num

theorem lyH_le_closure_zt (hF : GenFacts) : lyH ≤ Subgroup.closure {genGs 4, genGs 5} := by
  rw [genGs_eq, genGs_eq]
  unfold lyH
  rw [Subgroup.closure_le]
  rintro _ ⟨j, ⟨hj1, hj2⟩, rfl⟩
  exact hF.2.2.2.2.2.2.2.2 j hj1 hj2

theorem isCoatom_lyH : IsCoatom lyH := by
  have : IsPreprimitive J (Fin 8835156) := isPreprimitive
  rw [← stabilizer_zero]
  exact IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive J (0 : Fin 8835156)

theorem closure_gen_zt (hF : GenFacts) : Subgroup.closure ({genGs 4, genGs 5} : Set J) = ⊤ := by
  refine (isCoatom_lyH.lt_iff.1 (lt_of_le_of_ne (lyH_le_closure_zt hF) fun h => ?_))
  have hz : genGs 4 ∈ lyH := h ▸ Subgroup.subset_closure (Set.mem_insert _ _)
  have hdvd : orderOf (⟨genGs 4, hz⟩ : lyH) ∣ Nat.card lyH := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, ly_certificate.2.2.2.1] at hdvd
  have := (eleven_dvd_orderOf_genZ hF).trans hdvd
  norm_num at this

theorem exists_gen_pair :
    ∃ u : J, orderOf u = 21 ∧ a * u = u * a ∧
      Subgroup.centralizer ({a} : Set J) ⊔ Subgroup.centralizer ({u ^ 7} : Set J) = ⊤ :=
  have hF := genFacts
  exists_gen_pair_of a (genGs 2) (genGs 4) (genGs 5) (orderOf_genU hF) (gen_a_u hF) (gen_a_z hF)
    (gen_u_t hF) (closure_gen_zt hF)

end

end CFSG.Sporadic.Ly
