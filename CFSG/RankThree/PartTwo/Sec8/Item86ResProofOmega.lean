module

public import CFSG.RankThree.PartTwo.Sec8.Item83ProofAfter
public import CFSG.RankThree.PartTwo.Sec8.Item86ResProofBridge
import CFSG.RankThree.Asc83Table.E9
public import CFSG.RankThree.PartTwo.Sec8.Item83ProofLift

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item86ResProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec8.Item83Proof

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a d : G}
  {n : ℕ}

theorem lt_card_of_sec8Std (h : Sec8Std G A c L a d n) : 27 < Nat.card A := by
  have := h.data83.card_eq
  omega

theorem card_closure_of_sec8Std (hInd : KF83Indep) (h : Sec8Std G A c L a d n) :
    Nat.card (Subgroup.closure ({c, a, d} : Set G)) = 27 := by
  have hd := h.data83
  have hA₀e := hd.isElemAbelian
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA₀e.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have ha := h.a_mem_normalizer
  have ha3 : a ^ 3 = 1 := hA₀e.2 a hd.a_mem
  have hc3 : c ^ 3 = 1 := hA₀e.2 c hd.c_mem
  have hca : c * a = a * c := hcomm c hd.c_mem a hd.a_mem
  have hcL : L ≤ Subgroup.centralizer {c} := by
    obtain ⟨L', -, rfl⟩ := h.mem_thetaComponentsAt
    exact Subgroup.map_subtype_le _
  have hcy : ∀ y ∈ L, c * y = y * c := fun y hy =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hcL hy)).symm
  have hcN : c ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun y hy => (hcy y hy).symm)
  have hac : a ∉ Subgroup.zpowers c := by
    intro h1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
    apply h.not_isInnerAut_induced
    have hk' : (⟨a, ha⟩ : Subgroup.normalizer (L : Set G)) = ⟨c, hcN⟩ ^ k :=
      Subtype.ext (by simp [hk])
    rw [hk', map_zpow, map_zpow, KFacts.thetaQuotMulAut_compAction_eq_one hcN hcy, one_zpow]
    exact ⟨1, map_one _⟩
  have hca9 := CFSG.RankThree.Asc83Table.card_closure_pair_eq_nine hc3 ha3 hca h.ne_one hac
  exact card_closure_triple hA₀e hd.c_mem hd.a_mem hd.d_mem hca9
    (hInd G A c L a A d n h.toHyp81 (lt_card_of_sec8Std h) hd)

theorem exists_invariant_two_of_sec8Std (hKB : KF83KBarTwo) (h : Sec8Std G A c L a d n) :
    ∃ T ∈ invariantPiSubgroups L (Subgroup.closure ({c, a, d} : Set G)) (piOf 2), T ≠ ⊥ ∧
      T ≤ inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d}) := by
  have hd := h.data83
  have hA₀e := hd.isElemAbelian
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA₀e.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have ha := h.a_mem_normalizer
  have ha3 : a ^ 3 = 1 := hA₀e.2 a hd.a_mem
  have hcL : L ≤ Subgroup.centralizer {c} := by
    obtain ⟨L', -, rfl⟩ := h.mem_thetaComponentsAt
    exact Subgroup.map_subtype_le _
  have hcy : ∀ y ∈ L, c * y = y * c := fun y hy =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hcL hy)).symm
  obtain ⟨X, hX1, hX2, hXK, hXa⟩ := hKB G A c L a A d n h.toHyp81 (lt_card_of_sec8Std h) hd
  have hKL : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d}) ≤ L :=
    (Subgroup.map_subtype_le _).trans inf_le_left
  have hKd : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d}) ≤
      Subgroup.centralizer {d} := (Subgroup.map_subtype_le _).trans inf_le_right
  have hda : d * a = a * d := hcomm d hd.d_mem a hd.a_mem
  have haLd : a ∈ Subgroup.normalizer ((L ⊓ Subgroup.centralizer {d} : Subgroup G) : Set G) := by
    have haC : a ∈ Subgroup.normalizer (Subgroup.centralizer ({d} : Set G) : Set G) :=
      Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr hda.symm)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [Subgroup.mem_inf, Subgroup.mem_inf, (Subgroup.mem_normalizer_iff.mp ha y),
      (Subgroup.mem_normalizer_iff.mp haC y)]
  have haK : a ∈ Subgroup.normalizer
      (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d}) : Set G) :=
    CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual
      _ haLd
  obtain ⟨T, hTK, hT1, hT2, hTa⟩ := exists_twoGroup_le_of_imageModTheta ha haK ha3 hX1 hX2 hXK hXa
  have hET : Subgroup.closure ({c, a, d} : Set G) ≤ Subgroup.normalizer (T : Set G) := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl | rfl)
    · refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun t ht => ?_)
      exact (hcy t (hKL (hTK ht))).symm
    · exact hTa
    · refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun t ht => ?_)
      exact Subgroup.mem_centralizer_singleton_iff.mp (hKd (hTK ht))
  exact ⟨T, ⟨hTK.trans hKL, (isPiSubgroup_piOf_iff Nat.prime_two T).mpr hT2, hET⟩, hT1, hTK⟩

theorem closure_le_of_sec8Std (h : Sec8Std G A c L a d n) :
    Subgroup.closure ({c, a, d} : Set G) ≤ A := by
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl | rfl)
  · exact h.mem_A
  · exact h.a_mem
  · exact h.data83.d_mem

theorem mem_pairOmega_of_sec8Std (hKB : KF83KBarTwo)
    (hInd : KF83Indep) (h : Sec8Std G A c L a d n) : (c, L) ∈ pairOmega A := by
  obtain ⟨T, hT, hT1, -⟩ := exists_invariant_two_of_sec8Std hKB h
  refine ⟨h.mem_A, h.ne_one, h.mem_thetaComponentsAt, ⟨a, h.a_mem, h.inducesStdKind⟩,
    ⟨_, closure_le_of_sec8Std h, ?_, T, hT, hT1⟩, ⟨d, n, isGammaIndex_of_data83 h.data83⟩⟩
  rw [card_closure_of_sec8Std hInd h, h.data83.card_eq]

end CFSG.RankThree.PartTwo.Sec8.Item86ResProof
