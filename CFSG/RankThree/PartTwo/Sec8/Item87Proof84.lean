module

public import CFSG.RankThree.PartTwo.Sec8.Item87ProofGamma
public import CFSG.RankThree.PartTwo.Sec8.Item812ProofFinal
public import CFSG.RankThree.PartTwo.Sec8.Item812Proof811
import CFSG.RankThree.PartTwo.KFacts.K71Residual
import CFSG.RankThree.PartTwo.Sec10.Sec10XProofSym
import CFSG.RankThree.PartTwo.Sec6.Item65Tools
import CFSG.RankThree.PartOne.S10.FiveSuccessorTheta

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

namespace Item87Proof

variable {G : Type} [Group G] [Finite G]

theorem not_mem_zpowers_of_inducesOuterTheta {x y : G} {L : Subgroup G}
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G)) (hy : Sec4.InducesOuterTheta y L) :
    y ∉ Subgroup.zpowers x := by
  have hxC : x ∈ Subgroup.centralizer (L : Set G) := Subgroup.mem_centralizer_iff.mpr fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (hLx hl)
  rintro ⟨k, rfl⟩
  exact Sec10.Sec10XProof.not_inducesOuterTheta_of_mem_centralizer
    (Subgroup.zpow_mem _ hxC k) hy

theorem imageModTheta_eq_top_of_eq_sup {L K : Subgroup G} (hKL : K ≤ L)
    (h : L = K ⊔ inSubgroup (aschbacherSolvableCore 3) L) : imageModTheta L K = ⊤ := by
  have hθL : inSubgroup (aschbacherSolvableCore 3) L ≤ L := Subgroup.map_subtype_le _
  have hθ : (inSubgroup (aschbacherSolvableCore 3) L).subgroupOf L =
      aschbacherSolvableCore 3 L := by
    rw [inSubgroup, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective L.subtype_injective]
  have htop : K.subgroupOf L ⊔ aschbacherSolvableCore 3 L = ⊤ := by
    rw [← hθ, ← Subgroup.subgroupOf_sup hKL hθL, ← h, Subgroup.subgroupOf_self]
  have hker : (aschbacherSolvableCore 3 L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) =
      ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have := congrArg (Subgroup.map (QuotientGroup.mk' (aschbacherSolvableCore 3 L))) htop
  rw [Subgroup.map_sup, hker, sup_bot_eq, ← MonoidHom.range_eq_map,
    QuotientGroup.range_mk'] at this
  exact this

end Item87Proof


@[expose] def KF84Field : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n →
    KFacts.InducesStdKind (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G))) a
      .field

@[expose] def Pair84Gamma : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n →
    ∀ (e : G) (Le : Subgroup G), PairRel A e Le b X → e ∈ gammaSet A X

@[expose] def KF84Proper : Prop :=
  ∀ (X : Type) [Group X] (m : ℕ), 1 ≤ m →
    (IsGammaTypeRee X m → ¬ IsoSUThree X (2 ^ (3 * m))) ∧
      (IsGammaTypeL2 X m → ¬ Nonempty (X ≃* projSL 2 (GaloisField 2 (3 * m))))

theorem pair84A_of (h418 : Item418Theta) (hF : KF84Field) : Pair84A := by
  intro G _ _ A c L a b X n h
  have hG : TheoremFourHyp G := h.toTheoremFourHyp
  have hAel := h.mem_partTwoF.1
  have hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAel.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  obtain ⟨hbA, hb1, hn, -⟩ := Item87Proof.isGammaIndex_cases h.isGammaIndex
  have hb3 : b ^ 3 = 1 := hAel.2 b hbA
  have ha3 : a ^ 3 = 1 := hAel.2 a h.a_mem
  have hc3 : c ^ 3 = 1 := hAel.2 c h.mem_A
  have haC : a ∈ Subgroup.centralizer ({b} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm a h.a_mem b hbA)
  have hcC : c ∈ Subgroup.centralizer ({b} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm c h.mem_A b hbA)
  have hX : X ∈ thetaComponentsAt 3 b := h.pairRel.2.2.1
  have hXb : X ≤ Subgroup.centralizer ({b} : Set G) := (PartOne.mem_thetaComponentsAt_iff.mp hX).1
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    (PartOne.mem_thetaComponentsAt_iff.mp h.mem_thetaComponentsAt).1
  obtain ⟨hKmem, htype, -⟩ :=
    Item87Proof.residual_of_isGammaIndex h.mem_thetaComponentsAt h.isGammaIndex
  set K := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) with hK
  have hKX : K ≤ X := h.pairRel.2.2.2.1
  have hKc : K ≤ Subgroup.centralizer ({c} : Set G) :=
    (Item87Proof.residual_le _).trans (inf_le_left.trans hLc)
  have hK' : K ∈ thetaComponentsIn (X ⊓ Subgroup.centralizer {c}) := by
    obtain ⟨-, hK''⟩ := mem_thetaComponentsIn_iff.mp hKmem
    refine mem_thetaComponentsIn_iff.mpr ⟨le_inf hKX hKc, ?_⟩
    exact PartOne.subgroupOf_mem_thetaComponents_of_le Nat.prime_three (le_inf hKX hKc)
      (le_inf inf_le_right (inf_le_left.trans hXb)) hK''
  have hout : Sec4.InducesOuterTheta a L := by
    rcases h.inducesStdKind with h' | h'
    · exact KFacts.InducesStdKind.inducesOuterTheta L h' (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta L h' (by decide)
  have hac : a ∉ Subgroup.zpowers c := Item87Proof.not_mem_zpowers_of_inducesOuterTheta hLc hout
  exact (Item87Proof.item418_centralizer h418 hG hb3 hb1 haC hcC ha3 hc3
    (hcomm a h.a_mem c h.mem_A) h.ne_one hac hX hK' hn htype (hF G A c L a b X n h)).1

theorem pair84Sym_of (hΓ : Pair84Gamma) (hP : KF84Proper) : Pair84Sym := by
  intro G _ _ A c L a b X n h e Le hrel
  obtain ⟨m', hem'⟩ := hΓ G A c L a b X n h e Le hrel
  obtain ⟨hΩe, ⟨m, hbm⟩, hX, hKX, -⟩ := hrel
  have hLe : Le ∈ thetaComponentsAt 3 e := hΩe.2.2.1
  have hLeC : Le ≤ Subgroup.centralizer ({e} : Set G) :=
    (PartOne.mem_thetaComponentsAt_iff.mp hLe).1
  obtain ⟨hKe, -, hKe1⟩ := Item87Proof.residual_of_isGammaIndex hLe hbm
  obtain ⟨hKb, -, -⟩ := Item87Proof.residual_of_isGammaIndex hX hem'
  set Ke := inSubgroup perfectResidual (Le ⊓ Subgroup.centralizer ({b} : Set G)) with hKedef
  set Kb := inSubgroup perfectResidual (X ⊓ Subgroup.centralizer ({e} : Set G)) with hKbdef
  have hKeLe : Ke ≤ Le := (Item87Proof.residual_le _).trans inf_le_left
  have hKeKb : Ke ≤ Kb :=
    KFacts.le_inSubgroup_perfectResidual (Item87Proof.isPerfect_residual _)
      (le_inf hKX (hKeLe.trans hLeC))
  have hKb' : Kb ∈ thetaComponentsIn (Subgroup.centralizer {e} ⊓ Subgroup.centralizer {b}) := by
    rwa [inf_comm] at hKb
  have heq : Ke = Kb := Sec6.eq_of_mem_thetaComponentsIn_of_le hKe hKb'
    (Item87Proof.isPerfect_residual _) hKe1 le_rfl hKeKb
  refine ⟨h.mem_pairOmega, ⟨m', hem'⟩, hLe, ?_, ?_⟩
  · show Kb ≤ Le
    rw [← heq]
    exact hKeLe
  · show Le ≠ Kb ⊔ inSubgroup (aschbacherSolvableCore 3) Le
    rw [← heq]
    intro hsup
    have htop := Item87Proof.imageModTheta_eq_top_of_eq_sup hKeLe hsup
    let ι : Le ⧸ aschbacherSolvableCore 3 Le ≃* imageModTheta Le Ke :=
      Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop.symm)
    obtain ⟨-, -, hm, hcases⟩ := Item87Proof.isGammaIndex_cases hbm
    rcases hcases with ⟨hRee, F, hF, hFf, hFc, ⟨φ⟩⟩ | ⟨hL2, ⟨φ⟩⟩
    · exact (hP _ m hm).1 hRee ⟨F, hF, hFf, hFc, ⟨ι.trans φ⟩⟩
    · exact (hP _ m hm).2 hL2 ⟨ι.trans φ⟩

end CFSG.RankThree.PartTwo.Sec8
