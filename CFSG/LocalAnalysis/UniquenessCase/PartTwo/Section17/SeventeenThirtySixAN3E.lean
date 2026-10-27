module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtySixAN3D

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC6S846
open CFSG.QuasithinUnique (IsSylowTwoOf)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def Gap17_36a_n3_two_Q (D : Data G) (V₀ V L : Subgroup G) (n : ℕ) : Prop :=
  Ctx17_33 D V₀ V L n → V₀ ≠ ⊥ → n = 3 →
    3 ∣ Nat.card (Subgroup.center (Bar2 L)) → (conjSetOf D.M L).ncard = 2 → 3 ∉ D.sig →
      ∀ Q : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 Q (conjClosure D.M L) →
        rankThreeGamma 1 3 Q ≤ D.M

theorem gap17_36a_n3_two_torus_of_inputs
    (D : Data G) (V₀ V L : Subgroup G) (n : ℕ)
    (hK : K_SU3EightBorelNine)
    (hCen : UCK.U3Center)
    (hK3 : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.K_BorelTorusAbelian) :
    Ctx17_33 D V₀ V L n → V₀ ≠ ⊥ → n = 3 →
      3 ∣ Nat.card (Subgroup.center (Bar2 L)) → (conjSetOf D.M L).ncard = 2 →
        ∃ E : Subgroup G, E ≤ conjClosure D.M L ∧ IsElemAbelian 3 E ∧
          Permutes E D.T ∧ 2 ≤ CFSG.Open.pRank 3 E := by
  intro c _ hn hZ hcard
  subst hn
  obtain ⟨K₁, K₂, hne, hpair⟩ := Set.ncard_eq_two.mp hcard
  have hK₁ : K₁ ∈ conjSetOf D.M L := by
    rw [hpair]
    exact Set.mem_insert_iff.mpr (Or.inl rfl)
  have hK₂ : K₂ ∈ conjSetOf D.M L := by
    rw [hpair]
    exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton _))
  exact exists_permuting_E9_of_two_conj D V₀ V L hK hCen hK3 c hZ hK₁ hK₂ hne

theorem gap17_36a_n3_two_p_of_inputs
    (D : Data G) (V₀ V L : Subgroup G) (n : ℕ)
    (hK : K_SU3EightBorelNine) (hCen : UCK.U3Center)
    (hK3 : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.K_BorelTorusAbelian)
    (hSg : SigmaStd D) (hQ : Gap17_36a_n3_two_Q D V₀ V L n) :
    Gap17_36a_n3_two_p D V₀ V L n := by
  classical
  intro c hV0 hn hZ hcard
  obtain ⟨E, hEK, hEel, hEperm, hErank⟩ :=
    gap17_36a_n3_two_torus_of_inputs D V₀ V L n hK hCen hK3 c hV0 hn hZ hcard
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEp : IsPGroup 3 (E.subgroupOf (conjClosure D.M L)) :=
    IsPGroup.of_equiv hEel.isPGroup (Subgroup.subgroupOfEquivOfLe hEK).symm
  obtain ⟨Qbar, hQbar⟩ := hEp.exists_le_sylow (G := ↥(conjClosure D.M L))
  let Q : Subgroup G := (Qbar : Subgroup ↥(conjClosure D.M L)).map
    (conjClosure D.M L).subtype
  have hQsyl : CFSG.ABGLocalTools.IsSylowOf 3 Q (conjClosure D.M L) := ⟨Qbar, rfl⟩
  have hKleM : conjClosure D.M L ≤ D.M :=
    uc22p22v_conjClosure_le (Subgroup.le_normalizer (H := D.M)) c.mem_calC.1.le
  have hMnormK : D.M ≤ Subgroup.normalizer (conjClosure D.M L : Set G) :=
    uc22p22v_le_normalizer_conjClosure D.M L
  have hEQ : E ≤ Q := by
    have h1 : E.subgroupOf (conjClosure D.M L) ≤ (Qbar : Subgroup ↥(conjClosure D.M L)) := hQbar
    calc E = (E.subgroupOf (conjClosure D.M L)).map (conjClosure D.M L).subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hEK).symm
      _ ≤ Qbar.map (conjClosure D.M L).subtype := Subgroup.map_mono h1
  have hΓQ : rankThreeGamma 1 3 Q ≤ D.M := by
    by_cases h3 : 3 ∈ D.sig
    · have hns : ¬ Group.IsSolvable ↥D.M := not_solvable_of_mem_calC c.mem_calC
      have hstr : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M :=
        sp_of_mem_sig hSg hns h3
      exact hstr.rankThreeGamma_one_le_of_le Nat.prime_three hQsyl.isPGroup
        (hQsyl.le.trans hKleM)
    · exact hQ c hV0 hn hZ hcard h3 Q hQsyl
  have hΓE : rankThreeGamma 1 3 E ≤ D.M := (uc22p22u_gamma_mono hEQ).trans hΓQ
  have hEM : E ≤ D.M :=
    hEK.trans (uc22p22v_conjClosure_le (Subgroup.le_normalizer (H := D.M)) c.mem_calC.1.le)
  have hQnc : ¬ IsCyclic ↥Q := by
    intro hcyc
    have h1 : CFSG.Open.pRank 3 E ≤ 1 :=
      (CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hEQ).trans
        (CFSG.SectionRank.pRank_le_one_of_isCyclic Nat.prime_three hcyc)
    omega
  have hQleM : Q ≤ D.M := hQsyl.le.trans hKleM
  have hQp' : IsPGroup 3 (Q.subgroupOf D.M) :=
    IsPGroup.of_equiv hQsyl.isPGroup (Subgroup.subgroupOfEquivOfLe hQleM).symm
  obtain ⟨Pbar, hPbar⟩ := hQp'.exists_le_sylow (G := ↥D.M)
  let P : Subgroup G := (Pbar : Subgroup ↥D.M).map D.M.subtype
  have hPsyl : CFSG.ABGLocalTools.IsSylowOf 3 P D.M := ⟨Pbar, rfl⟩
  have hQP : Q ≤ P := by
    have h1 : Q.subgroupOf D.M ≤ (Pbar : Subgroup ↥D.M) := hPbar
    calc Q = (Q.subgroupOf D.M).map D.M.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hQleM).symm
      _ ≤ Pbar.map D.M.subtype := Subgroup.map_mono h1
  have hQeq : Q = P ⊓ conjClosure D.M L := by
    have hPK : CFSG.ABGLocalTools.IsSylowOf 3 (P ⊓ conjClosure D.M L)
        (conjClosure D.M L) :=
      hPsyl.inf_of_le_normalizer hKleM hMnormK
    exact (hQsyl.eq_of_le (le_inf hQP hQsyl.le) inf_le_right hPK.isPGroup).symm
  have hPnormQ : P ≤ Subgroup.normalizer (Q : Set G) := by
    rw [hQeq]
    intro p hp
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨hyP, hyK⟩
      exact ⟨Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hp) y |>.mp hyP,
        (Subgroup.mem_normalizer_iff.mp (hMnormK (hPsyl.le hp)) y).mp hyK⟩
    · rintro ⟨hyP, hyK⟩
      exact ⟨Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hp) y |>.mpr hyP,
        (Subgroup.mem_normalizer_iff.mp (hMnormK (hPsyl.le hp)) y).mpr hyK⟩
  refine ⟨E, ?_⟩
  refine ⟨3, Nat.prime_three, by norm_num, hEM, hEel.isPGroup, hEel.2, ?_, hEperm, hΓE,
    Or.inr ⟨Q, hQnc, ⟨P, hPsyl, hQP, hPnormQ⟩, hΓQ⟩⟩
  intro hcyc
  have h1 : CFSG.Open.pRank 3 E ≤ 1 :=
    CFSG.SectionRank.pRank_le_one_of_isCyclic Nat.prime_three hcyc
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
