module

public import CFSG.Quasithin.EmptyFaithful.S146yB1Four
public import CFSG.Quasithin.EmptyFaithful.S146xB2C1
public import CFSG.Quasithin.EmptyFaithful.S146xB2Excl
public import CFSG.Quasithin.Background.E2TwoNoNStmt
public import CFSG.Quasithin.EmptyFaithful.S146yB1
public import CFSG.Quasithin.EmptyFaithful.S146yB1Comp

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
open scoped commutatorElement

@[expose] def Input1469B1NoN : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (I S Iz : Subgroup G) (z : G),
    IsSQTKTC I → ¬ CharTwo I → MinParabolic I S Iz →
    z ∈ quasithinOmegaOneCenter S → z ≠ 1 → Iz = I ⊓ Subgroup.centralizer ({z} : Set G) →
    (∃ L : Subgroup G, IsComponentIn L I) →
    (∀ L : Subgroup G, IsComponentIn L I → ⁅L, Subgroup.zpowers z⁆ = L ∧ Lemma115Cases L z) →
    (∃ K : Subgroup G, K ∈ cComp I ∧ I = K ⊔ S ∧
      CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.Open.pCore 2 ↥K) ∧ E2.E22CasesNoN I S Iz K) →
    ∃ K : Subgroup G, K ∈ cComp I ∧ I = K ⊔ S ∧
      CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.Open.pCore 2 ↥K) ∧ E2.E22CasesNoN I S Iz K ∧
      Shape1469B S Iz K I

@[expose] def Input1469B2NoN : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (I S Iz K : Subgroup G),
    IsSQTKTC I → ¬ CharTwo I → MinParabolic I S Iz → K ∈ cComp I → I = K ⊔ S →
    CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.Open.pCore 2 ↥K) → E2.E22CasesNoN I S Iz K →
    Shape1469B S Iz K I →
    ∀ A : Subgroup G, A ≤ S → S ≤ Subgroup.normalizer (A : Set G) → IsElemAbelian 2 A →
      4 ≤ mIdx A (pCoreOf 2 I) → False

theorem input1469B1_of_residuesNoN (h : B1Residues) : Input1469B1NoN := by
  intro G _ _ I S Iz z hSQ hnc hMP hzS hz1 hIz hex hcomp hE
  obtain ⟨K, hKc, hIK, hKq, hKE⟩ := hE
  refine ⟨K, hKc, hIK, hKq, hKE, ?_⟩
  have hSI : S ≤ I := hMP.isSylow.1
  have hS2 : IsPGroup 2 S := hMP.isSylow.2.1
  have hSsolv : Group.IsSolvable S := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := hS2.isNilpotent
    infer_instance
  have hKI : K ≤ I := le_of_mem_cComp hKc
  have hKcomp : IsComponentIn K I := isComponentIn_of_cComp_of_exists hKc hIK hSsolv hex
  obtain ⟨hKz, hK115c⟩ := hcomp K hKcomp
  have hK115 : Lemma115Type ↥K := lemma115Type_of_cases hK115c
  obtain ⟨hzS', -, hz2⟩ := mem_quasithinOmegaOneCenter_iff.mp hzS
  have hctx : B1Ctx I Iz K z :=
    ⟨hKI, ne_bot_of_mem_cComp hKc, hSI hzS', hz2, hKz, hIz⟩
  unfold E2.E22CasesNoN at hKE
  dsimp only at hKE
  rcases hKE with ⟨-, t, ht, hne, hM, h1⟩ | ⟨-, -, h2⟩
  · rcases h1 with ⟨n, hn, hX, hB⟩ | ⟨p, hp, hp8, hX, -, h8⟩
    · exact (hctx.false_of_borel h.borel (Or.inl ⟨hn, hX.elim Or.inl (fun h' => Or.inr (Or.inl h'))⟩)
        hB).elim
    · exact shape_of_psl_prime h.l2Prime h.l3Two hSI hS2 hKI hKcomp hK115 hp hp8 hX h8
  · rcases h2 with ⟨n, hX, hB⟩ | ⟨n, hn, hX, hD, hB⟩ | ⟨p, e, hp, hp3, he, he8, hX, -, h8⟩ |
      ⟨p, hp, hp2, hX, -⟩
    · exact (hctx.false_of_borel h.borel (Or.inl hX) hB).elim
    · by_cases hn1 : n = 1
      · subst hn1
        refine Or.inr (Or.inl ⟨?_, hD⟩)
        rcases hX with hX | hX
        · exact Or.inl hX
        · exact Or.inr (by simpa [E2.IsSp4Prime] using hX)
      · exact (hctx.false_of_borel h.borel (Or.inr ⟨by omega, hX⟩) hB).elim
    · rcases he with rfl | rfl
      · have hp8 : p % 8 = 1 ∨ p % 8 = 7 := by simpa using he8
        exact shape_of_psl_prime h.l2Prime h.l3Two hSI hS2 hKI hKcomp hK115 hp hp8
          (by simpa using hX) h8
      · exact (B1_false_of_psl_square h.l2Square hKcomp hK115 hp hp3 hX).elim
    · rcases hX with ⟨hp4, hX⟩ | ⟨hp4, hX, -⟩
      · exact (B1_false_of_psu_three h.u3Odd hKcomp hK115 hp hp4 hX).elim
      · by_cases hp3 : p = 3
        · subst hp3
          exact Or.inr (Or.inr hX)
        · have hp3' : 3 < p := by
            have := hp.two_le
            have h3 : p ≠ 3 := hp3
            omega
          exact (B1_false_of_psl_three h.l3Odd hKcomp hK115 hp hp4 hp3' hX).elim

theorem input1469B1_of_fiveNoN (h : B1ResiduesFive) : Input1469B1NoN :=
  input1469B1_of_residuesNoN h.toResidues

theorem input1469B1_of_fourNoN (h : B1ResiduesFour) : Input1469B1NoN :=
  input1469B1_of_fiveNoN h.toFive

theorem input1469B2_proofNoN : Input1469B2NoN := by
  intro G _ _ I S Iz K hSQ _hnc hMP hK hIK _hqs hE22 hshape A hAS hSA hAel h4
  have hS := hMP.isSylow
  have hmem : Iz ∈ maxOver I S := by
    have h := hMP.uniqueMax
    unfold IsUniqueMaxOver at h
    rw [h]
    exact Set.mem_singleton Iz
  have hSIz : S ≤ Iz := hmem.2
  have hshape' : (∃ p : ℕ, IsFermatOrMersennePrime p ∧ 7 < p ∧ IsPSL 2 p 1 ↥(E2.star Iz I K)) ∨
      IsPSL 3 2 1 ↥(E2.star Iz I K) ∨ IsAlt 6 ↥(E2.star Iz I K) ∨ IsPSL 3 3 1 ↥(E2.star Iz I K) := by
    rcases hshape with h | ⟨h | h, -⟩ | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  rcases hE22 with ⟨hker, t, htS, hKt, -, hcase⟩ | ⟨hSK, hJ, -⟩
  · rcases hcase with ⟨n, hn2, hB, -⟩ | ⟨p, hp, hp8, hpsl, -, h8⟩
    · exact false_of_bender_of_shape hn2 hB hshape'
    · exact e22_case_one_b_false hSQ hMP hK hIK hker htS hKt hp hp8 hpsl h8 hAS hSA hAel h4
  · refine e22_case_two_false hS hSIz hIK hSK hJ ?_ hAS hAel h4
    rcases hshape' with ⟨p, hp, hp7, h⟩ | h | h | h
    · exact Or.inl ⟨p, hp.1, by omega, h⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))

end CFSG.Quasithin
