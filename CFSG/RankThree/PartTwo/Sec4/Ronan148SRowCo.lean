module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148SComp
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.Co3Shape
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo2Cent
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo2U42

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open scoped commutatorElement

section Simple

variable {S : Type} [Group S] [Finite S]

theorem not_isType425_of_simple {Q : Type} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (hQna : ∃ a b : Q, a * b ≠ b * a) {M B : ℕ} (hM : Nat.card Q = M) (hB : M < B ^ 3)
    (hfree : M ∉ typeOrders425 M B) : ¬ IsType425 (Q ⧸ aschbacherSolvableCore 3 Q) := by
  intro hT
  obtain ⟨hQq, hZ⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hQna
  have hθ : aschbacherSolvableCore 3 Q = ⊥ :=
    le_bot_iff.mp ((aschbacherSolvableCore_le_center hQq).trans hZ.le)
  have hc1 : Nat.card (aschbacherSolvableCore 3 Q) = 1 := by
    rw [hθ, Subgroup.card_bot]
  have hcardq : Nat.card (Q ⧸ aschbacherSolvableCore 3 Q) = Nat.card Q := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 Q)
    rw [hc1, mul_one] at h
    exact h.symm
  have hM0 : 0 < M := by
    rw [← hM]
    exact Nat.card_pos
  have hdvd : Nat.card (Q ⧸ aschbacherSolvableCore 3 Q) ∣ M := dvd_of_eq (hcardq.trans hM)
  have hmem := card_mem_typeOrders425 (isQuasisimple_theta_quot hQq) hM0 hB hT hdvd
  rw [hcardq, hM] at hmem
  exact hfree hmem

theorem good425_of_simpleNormal {C L : Subgroup S} (hLC : L ≤ C)
    (hLn : ∀ g ∈ C, ∀ l ∈ L, g * l * g⁻¹ ∈ L) [hLs : IsSimpleGroup L]
    (hLna : ∃ a b : L, a * b ≠ b * a) {M B : ℕ} (hM : Nat.card L = M) (hB : M < B ^ 3)
    (hfree : M ∉ typeOrders425 M B)
    (hcent : ∀ g ∈ C, (∀ l ∈ L, l * g = g * l) → g ^ 3 = 1) : Good425 C := by
  intro K hKC hKq hKs hT
  haveI : Group.IsPerfect K := hKq.1
  haveI : Nontrivial K := CFSG.LocalCores.isQuasisimple_nontrivial hKq
  have hL'n : (L.subgroupOf C).Normal := RonanK429H.normal_subgroupOf_of_forall_conj' hLn
  have hK'c : IsComponent (K.subgroupOf C) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKC).symm hKq, hKs⟩
  rcases CFSG.LocalCores.component_normal_subgroup hK'c hL'n with hle | hcomm
  · have hKL : K ≤ L := fun k hk => hle (show (⟨k, hKC hk⟩ : C) ∈ K.subgroupOf C from hk)
    have hsL : (K.subgroupOf L).IsSubnormal :=
      RonanK429H.isSubnormal_subgroupOf_of_le hLC hKL hKs
    rcases hsL.eq_bot_or_top_of_isSimpleGroup hLs with hbot | htop
    · rw [Subgroup.subgroupOf_eq_bot] at hbot
      have hK0 : K = ⊥ := by
        rw [eq_bot_iff]
        intro k hk
        exact Subgroup.mem_bot.mpr (Subgroup.disjoint_def.mp hbot hk (hKL hk))
      exact (Subgroup.nontrivial_iff_ne_bot K).mp inferInstance hK0
    · have hKeq : K = L := le_antisymm hKL (Subgroup.subgroupOf_eq_top.mp htop)
      subst hKeq
      exact not_isType425_of_simple hLna hM hB hfree hT
  · have hk3 : ∀ k ∈ K, k ^ 3 = 1 := by
      intro k hk
      apply hcent k (hKC hk)
      intro l hl
      have hmem : ⁅(⟨k, hKC hk⟩ : C), (⟨l, hLC hl⟩ : C)⁆ ∈ ⁅K.subgroupOf C, L.subgroupOf C⁆ :=
        Subgroup.commutator_mem_commutator (show (⟨k, hKC hk⟩ : C) ∈ K.subgroupOf C from hk)
          (show (⟨l, hLC hl⟩ : C) ∈ L.subgroupOf C from hl)
      rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact (congrArg Subtype.val hmem).symm
    have hK3 : IsPGroup 3 K := RonanK429H.isPGroup_three_of_pow_three hk3
    haveI := hK3.isNilpotent
    exact Group.IsPerfect.not_isSolvable K inferInstance

end Simple

section Co2

open CFSG.HardMathSupport.Dickson.I271 CFSG.Sporadic.Co2Cert

theorem good425_co2A :
    Good425 (Subgroup.centralizer ({co2XA} : Set (Equiv.Perm (Fin 2300))) ⊓ co2P) := by
  obtain ⟨-, -, -, hcard, hle, hnorm, hcent⟩ := co2CaseA_spec
  exact good425_of_selfCentralizing' hle hnorm
    (IsPGroup.of_card (n := 5) (by rw [hcard]; norm_num)) hcent

theorem good425_co2B :
    Good425 (Subgroup.centralizer ({co2XB} : Set (Equiv.Perm (Fin 2300))) ⊓ co2P) := by
  obtain ⟨-, -, -, hcard, hLC, hLn, hcent, hrels⟩ := co2CaseB_spec
  obtain ⟨eL⟩ := nonempty_mulEquiv_QP45_of_rels uvGen hrels hcard
  haveI : IsSimpleGroup Lsub := isSimpleGroup_of_equiv_QP45 eL
  have hna : ∃ a b : Lsub, a * b ≠ b * a := nonabelian_of_equiv_QP45 eL
  exact good425_of_simpleNormal hLC hLn hna (M := 25920) (B := 30) hcard (by norm_num)
    (by decide +kernel) hcent

theorem good425_co2P : ∀ x ∈ co2P, orderOf x = 3 →
    Good425 (Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 2300))) ⊓ co2P) := by
  intro x hx hx3
  obtain ⟨k, hk, c, hc, e, he, hkc⟩ := co2_exists_conj_classes hx hx3
  rw [← hkc]
  rcases hc with rfl | rfl
  · exact Good425.conj hk co2CaseA_spec.1 he good425_co2A
  · exact Good425.conj hk co2CaseB_spec.1 he good425_co2B

theorem noCC425_co2P : NoCC425 ↥co2P := noCC425_of_subgroupModel (MulEquiv.refl _) good425_co2P

end Co2

section Co3

open CFSG.HardMathSupport.Dickson.I271 CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T
open CFSG.Sporadic.Schreier.Co3

theorem good425_co3A :
    Good425 (Subgroup.centralizer ({XA} : Set (Equiv.Perm (Fin 276))) ⊓ co3P) := by
  obtain ⟨-, -, -, hcard, hle, hnorm, hcent⟩ := caseA_spec
  exact good425_of_selfCentralizing' hle hnorm
    (IsPGroup.of_card (n := 5) (by rw [hcard]; norm_num)) hcent

theorem good425_co3B :
    Good425 (Subgroup.centralizer ({XB} : Set (Equiv.Perm (Fin 276))) ⊓ co3P) := by
  obtain ⟨-, -, -, hcard, hle, hnorm, hcent⟩ := caseB_spec
  exact good425_of_selfCentralizing' hle hnorm
    (IsPGroup.of_card (n := 5) (by rw [hcard]; norm_num)) hcent

theorem good425_co3C :
    Good425 (Subgroup.centralizer ({yPerm} : Set (Equiv.Perm (Fin 276))) ⊓ co3P) := by
  obtain ⟨⟨hCeq, hcard⟩, -⟩ := caseC_spec
  exact good425_of_card_dvd (M := 4536) (B := 17) (dvd_of_eq (by rw [← hCeq, hcard]))
    (by norm_num) (by norm_num) (by decide +kernel)

theorem good425_co3P : ∀ x ∈ co3P, orderOf x = 3 →
    Good425 (Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 276))) ⊓ co3P) := by
  intro x hx hx3
  obtain ⟨k, hk, c, hc, e, he, hkc⟩ := exists_conj_classes hx hx3
  rw [← hkc]
  rcases hc with rfl | rfl | rfl
  · exact Good425.conj hk caseA_spec.1 he good425_co3A
  · exact Good425.conj hk caseB_spec.1 he good425_co3B
  · exact Good425.conj hk yPerm_pow he good425_co3C

theorem noCC425_co3P : NoCC425 ↥co3P := noCC425_of_subgroupModel (MulEquiv.refl _) good425_co3P

end Co3

section Rows

section Co2Row

theorem rowOf425_co2 : RowOf425 (Spor .Co2) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Co2.nonempty_mulEquiv
  exact rowOf425_of_noCC fun S _ _ _ _ ⟨e⟩ =>
    NoCC425.of_mulEquiv (e.trans (b.symm.trans CFSG.Sporadic.Co2Cert.co2PermEquiv)) noCC425_co2P

end Co2Row

section Co3Row

theorem rowOf425_co3 : RowOf425 (Spor .Co3) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Co3.nonempty_mulEquiv
  exact rowOf425_of_noCC fun S _ _ _ _ ⟨e⟩ =>
    NoCC425.of_mulEquiv (e.trans (b.symm.trans CFSG.Sporadic.Schreier.Co3.co3PermEquiv))
      noCC425_co3P

end Co3Row

end Rows

end CFSG.RankThree.PartTwo.Sec4.Ronan148S
