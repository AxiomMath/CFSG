module

public import CFSG.RankThree.PartTwo.Sec19.Step1917ProofDefs
import CFSG.RankThree.PartTwo.Sec19.Step1917ProofTools
import CFSG.RankThree.PartTwo.Sec19.Step1917StepsBasic
import CFSG.RankThree.PartTwo.Sec19.Step1915Proof
import CFSG.RankThree.PartTwo.Sec19.Step1910Proof
import CFSG.RankThree.PartTwo.Sec19.Step198DProof
import CFSG.RankThree.PartOne.S10.AmbientTheta

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13

@[expose] def Step1917PushEq :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E M : Subgroup G)
    (hctx : Ctx1912 G A c L E M), L ≤ M → ∀ d ∈ A ⊓ E, d ∉ Subgroup.zpowers c →
      ¬ Subgroup.normalizer (Subgroup.zpowers d : Set G) ≤ M →
      ∀ H ∈ scriptM (Subgroup.normalizer (Subgroup.zpowers d : Set G) : Set G), H ≠ M →
      ∀ K ∈ oTwoComponentsIn M, L ≤ K → Step1917Proof.Alt1915W L K c → K ≤ H →
        ¬ (letI := Sec15.kerAO2_normal hctx.mem_lA.2.1;
          Nonempty (↥(A ⊔ L) ⧸ Sec15.kerAO2 A L ≃*
            Multiplicative (ZMod 3) × CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2))) →
        ∀ X ∈ oTwoComponentsIn H, L ≤ X → c ∈ Subgroup.normalizer (X : Set G) →
          ¬ (∀ x ∈ X, c * x * c⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 X) → K = X

@[expose] def Step1917LiftEq :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E M : Subgroup G)
    (hctx : Ctx1912 G A c L E M), L ≤ M → ∀ d ∈ A ⊓ E, d ∉ Subgroup.zpowers c →
      ¬ Subgroup.normalizer (Subgroup.zpowers d : Set G) ≤ M →
      ∀ H ∈ scriptM (Subgroup.normalizer (Subgroup.zpowers d : Set G) : Set G), H ≠ M →
      ∀ K ∈ oTwoComponentsIn M, L ≤ K → Step1917Proof.Alt1915W L K c → K ≤ H →
        ¬ H ≤ Subgroup.normalizer (K : Set G) →
        (letI := Sec15.kerAO2_normal hctx.mem_lA.2.1;
          Nonempty (↥(A ⊔ L) ⧸ Sec15.kerAO2 A L ≃*
            Multiplicative (ZMod 3) × CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2))) →
        ∀ X ∈ oTwoComponentsIn H, L ≤ X → c ∈ Subgroup.normalizer (X : Set G) →
          ¬ (∀ x ∈ X, c * x * c⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 X) → K = X

namespace Step1917Steps

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_oTwoComponentsIn
    (h1913 : Step1913) (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) {A L E M H : Subgroup G} {c : G}
    (hctx : Ctx1912 G A c L E M) (hH : IsMaximalTwoLocal H) (hEH : E ≤ H) (hLH : L ≤ H) :
    ∃ X ∈ oTwoComponentsIn H, L ≤ X ∧ E ≤ Subgroup.normalizer (X : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hst := hctx.toPartTwoStanding
  have hL : L ∈ thetaComponentsAt 3 c := hctx.mem_lA.1
  have hE := Step1916Proof2.isE27_E hctx
  have hc3 := Step1916Proof2.orderOf_eq hctx
  have hc1 : c ≠ 1 := fun h => by
    rw [h, orderOf_one] at hc3
    norm_num at hc3
  have hcE := Step1916Proof2.mem_E hctx
  have hcH : c ∈ H := hEH hcE
  have hLq := Sec12.isQuasisimple_thetaQuot_of_mem hL
  obtain ⟨F, hFL, hF, hF9⟩ := Step1918Proof.exists_elemAbelian_nine h1913 hctx
  have hHtop : H ≠ ⊤ := by
    have : IsSimpleGroup G := hst.isSimpleGroup
    exact ne_top_of_pCoreOf_ne_bot hst.nonabelian (pCoreOf_ne_bot_of_isMaximalTwoLocal hH)
  have hH4 : SectionFourHyp H := hst.toTheoremFourHyp.sectionFourHyp hHtop
  obtain ⟨L', hL', hLL'⟩ := h48 H hH4 (E.subgroupOf H)
    (Step198DProof.isElemAbelian_subgroupOf hE.1 H)
    ⟨3, le_rfl, by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEH).toEquiv, hE.2]; norm_num⟩
    ⟨c, hcH⟩ (Subgroup.mem_subgroupOf.mpr hcE) (fun h => hc1 (congrArg Subtype.val h))
    (L.subgroupOf H) (Step198Proof.subgroupOf_mem_thetaComponentsAt hL hLH hcH)
  have hXθ : L'.map H.subtype ∈ thetaComponentsIn H := ⟨L', hL', rfl⟩
  have hLX : L ≤ L'.map H.subtype := fun l hl =>
    ⟨⟨l, hLH hl⟩, hLL' (Subgroup.mem_subgroupOf.mpr hl), rfl⟩
  exact ⟨_, Step1915Proof.mem_oTwoComponentsIn_of_card hst.toTheoremFourHyp hH.1 hHtop hXθ hLX hLq
    (Or.inr (Step1915Proof.le_card_quot_center h1913 hctx)) hFL hF9 hF.2, hLX,
    Step198Proof.le_normalizer_map_of_isE27 h45 hH4 hE hEH hL'⟩

theorem E_le_H {A L E M H : Subgroup G} {c : G} (hctx : Ctx1912 G A c L E M) {d : G}
    (hdE : d ∈ E) (hH : Subgroup.normalizer (Subgroup.zpowers d : Set G) ≤ H) : E ≤ H :=
  le_H (Step1916Proof2.isE27_E hctx).1.1 hdE hH

theorem eq_of_mem_oTwoComponentsIn
    (h1913 : Step1913) {A L E M : Subgroup G} {c : G} (hctx : Ctx1912 G A c L E M)
    {Y K₁ K₂ : Subgroup G} (h₁ : K₁ ∈ oTwoComponentsIn Y) (h₂ : K₂ ∈ oTwoComponentsIn Y)
    (hL₁ : L ≤ K₁) (hL₂ : L ≤ K₂) : K₁ = K₂ := by
  by_contra hne
  obtain ⟨-, hZ, -⟩ := Step1916Proof2.lBar_facts h1913 hctx
  obtain ⟨F, hFL, hF, hF9⟩ := Step1918Proof.exists_elemAbelian_nine h1913 hctx
  have hF1 : F ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hF9
    omega
  obtain ⟨⟨a, haF⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hF1
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  apply ha1'
  refine Step1916Proof2.eq_one_of_forall_commutator_mem hZ
    (hL₁.trans (le_of_mem_oTwoComponentsIn h₁)) (hFL haF) (k := 1)
    (by rw [pow_one]; exact hF.2 a haF) fun l hl => ?_
  exact Step1910Proof.commutator_mem_pCoreOf h₁ h₂ hne (hL₁ (hFL haF)) (hL₂ hl)

theorem eq_of_central
    (h1913 : Step1913) {A L E M H K X : Subgroup G} {c : G} (hctx : Ctx1912 G A c L E M)
    (hH : IsMaximalTwoLocal H) (hEH : E ≤ H) (hK : K ∈ oTwoComponentsIn M) (hLK : L ≤ K)
    (hKH : K ≤ H) (hX : X ∈ oTwoComponentsIn H) (hLX : L ≤ X)
    (hcX : c ∈ Subgroup.normalizer (X : Set G))
    (hcen : ∀ x ∈ X, c * x * c⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 X) : K = X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL : L ∈ thetaComponentsAt 3 c := hctx.mem_lA.1
  have hE := Step1916Proof2.isE27_E hctx
  have hc3 := Step1916Proof2.orderOf_eq hctx
  obtain ⟨F, hFL, -, hF9⟩ := Step1918Proof.exists_elemAbelian_nine h1913 hctx
  have hL1 : L ≠ ⊥ := by
    rintro rfl
    have h1 : Nat.card F ≤ Nat.card (⊥ : Subgroup G) := Subgroup.card_le_of_le hFL
    rw [Subgroup.card_bot] at h1
    omega
  have hXL : X = L ⊔ CFSG.Open.pCoreOf 2 X :=
    Step1915Proof.eq_sup_of_central_of_mem_normalizer
      (Sec18.isQuasisimple_of_mem_oTwoComponentsIn hX) hLX hcX hc3
      (Sec6.le_centralizer_of_mem_thetaComponentsAt hL)
      (PartOne.isSubnormal_of_mem_thetaComponentsAt hL)
      (Sec6.isPerfect_of_mem_thetaComponentsAt hL) hL1 hcen
  have hLM : L ≤ M := hLK.trans (le_of_mem_oTwoComponentsIn hK)
  have hOH : CFSG.Open.pCoreOf 2 H ≤ M := by
    rw [← hctx.hyp191 E M H hE hctx.mem_scriptM hEH (pCoreOf_ne_bot_of_isMaximalTwoLocal hH)]
    exact (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_right
  have hXM : X ≤ M := by
    rw [hXL]
    exact sup_le hLM ((Sec18.pCoreOf_le_pCoreOf_of_mem_oTwoComponentsIn hX).trans hOH)
  have hKMH : K ∈ oTwoComponentsIn (M ⊓ H) := by
    obtain ⟨hKM, -, hKsn, -⟩ := mem_oTwoComponentsIn_iff.mp hK
    exact Sec18.mem_oTwoComponentsIn_of_quasisimple (le_inf hKM hKH)
      (Sec18.isSubnormal_subgroupOf_of_le hKsn inf_le_left)
      (Sec18.commutator_eq_of_mem_oTwoComponentsIn hK)
      (Sec18.isQuasisimple_of_mem_oTwoComponentsIn hK)
  have hXMH : X ∈ oTwoComponentsIn (M ⊓ H) := by
    obtain ⟨hXH, -, hXsn, -⟩ := mem_oTwoComponentsIn_iff.mp hX
    exact Sec18.mem_oTwoComponentsIn_of_quasisimple (le_inf hXM hXH)
      (Sec18.isSubnormal_subgroupOf_of_le hXsn inf_le_right)
      (Sec18.commutator_eq_of_mem_oTwoComponentsIn hX)
      (Sec18.isQuasisimple_of_mem_oTwoComponentsIn hX)
  exact eq_of_mem_oTwoComponentsIn h1913 hctx hKMH hXMH hLK hLX

end Step1917Steps

open Step1917Steps in
theorem step1917Push_of
    (h1913 : Step1913) (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (hEq : Step1917PushEq) :
    Step1917Push := by
  intro G _ _ A c L E M hctx hLM d hdD hdc hN H hH hHM K hK hLK halt hKH
  by_cases hiso : (letI := Sec15.kerAO2_normal hctx.mem_lA.2.1;
      Nonempty (↥(A ⊔ L) ⧸ Sec15.kerAO2 A L ≃*
        Multiplicative (ZMod 3) × CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)))
  · exact Or.inr hiso
  · left
    have hEH := E_le_H hctx hdD.2 hH.2
    obtain ⟨X, hX, hLX, hEX⟩ := exists_mem_oTwoComponentsIn h1913 h45 h48 hctx hH.1 hEH
      (hLK.trans hKH)
    have hcX : c ∈ Subgroup.normalizer (X : Set G) := hEX (Step1916Proof2.mem_E hctx)
    have hKX : K = X := by
      by_cases hcen : ∀ x ∈ X, c * x * c⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 X
      · exact eq_of_central h1913 hctx hH.1 hEH hK hLK hKH hX hLX hcX hcen
      · exact hEq G A c L E M hctx hLM d hdD hdc hN H hH hHM K hK hLK halt hKH hiso X hX hLX
          hcX hcen
    rw [hKX]
    obtain ⟨-, hZ, -⟩ := Step1916Proof2.lBar_facts h1913 hctx
    obtain ⟨F, hFL, hF, hF9⟩ := Step1918Proof.exists_elemAbelian_nine h1913 hctx
    intro h hh
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      (Step1917Proof.map_conj_eq_of_mem_of_isMaximalTwoLocal hctx.toPartTwoStanding hH.1 hZ hX
        hLX hFL hF hF9 hh)

open Step1917Steps in
theorem step1917Lift_of
    (h1913 : Step1913) (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (hEq : Step1917LiftEq) :
    Step1917Lift := by
  intro G _ _ A c L E M hctx hLM d hdD hdc hN H hH hHM K hK hLK halt hKH hHK hiso
  have hEH := E_le_H hctx hdD.2 hH.2
  obtain ⟨X, hX, hLX, hEX⟩ := exists_mem_oTwoComponentsIn h1913 h45 h48 hctx hH.1 hEH
    (hLK.trans hKH)
  have hcX : c ∈ Subgroup.normalizer (X : Set G) := hEX (Step1916Proof2.mem_E hctx)
  have hKX : K = X := by
    by_cases hcen : ∀ x ∈ X, c * x * c⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 X
    · exact eq_of_central h1913 hctx hH.1 hEH hK hLK hKH hX hLX hcX hcen
    · exact hEq G A c L E M hctx hLM d hdD hdc hN H hH hHM K hK hLK halt hKH hHK hiso X hX hLX
        hcX hcen
  rw [hKX]
  exact hX

end CFSG.RankThree.PartTwo.Sec19
