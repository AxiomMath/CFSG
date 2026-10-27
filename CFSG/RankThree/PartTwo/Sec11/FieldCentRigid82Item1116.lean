module

public import CFSG.RankThree.PartTwo.Sec11.FieldCentRigid82
public import CFSG.RankThree.PartTwo.Sec11.Item1116NoFifteen
public import CFSG.RankThree.PartTwo.Sec11.SkeletonClosed

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Main

variable {G : Type} [Group G] [Finite G]

theorem Sec11Data.hyp81_swap (h118 : Item118) {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
    {R Y : Subgroup G} {d x s r g : G} (h : Sec11Data G A c L a R Y d x s r g)
    (hf : KFacts.InducesStdKind Y c .field) : Sec8.Hyp81 G A a Y c where
  toPartTwoStanding := h.toPartTwoStanding
  mem_partTwoF := h.mem_partTwoF
  mem_A := h.a_mem
  ne_one := h.a_ne_one
  mem_thetaComponentsAt := h.mem_thetaComponentsAt_Y
  sectionCentralizer_eq := (h118 G A c L a R Y h.toSec11Std d g h.inf_eq h.closure_eq h.g_mem.2
    h.g_not_mem h.conj_mem).2.2
  a_mem := h.mem_A
  a_ne_one := h.ne_one
  inducesStdKind := Or.inl hf
  exists_invariant_two := fun h27 => absurd h.card_eq (Nat.ne_of_gt h27)
  partTwoE_eq := h.partTwoE_eq

theorem Sec11Data.isList82One_of_field (h82 : Sec8.Item82One) (h118 : Item118) {A : Subgroup G}
    {c : G} {L : Subgroup G} {a : G} {R Y : Subgroup G} {d x s r g : G}
    (h : Sec11Data G A c L a R Y d x s r g) (hf : KFacts.InducesStdKind Y c .field) :
    Sec8.IsList82One (Y ⧸ aschbacherSolvableCore 3 Y) :=
  h82 G A a Y c (h.hyp81_swap h118 hf) h.card_eq

theorem rank3II_11_13_1_of_rigid (h45 : Sec4.Item4_5) {A : Subgroup G} {c : G} {L : Subgroup G}
    {a : G} {R Y : Subgroup G} {d x s r g : G} (h : Sec11Data G A c L a R Y d x s r g)
    (hf : KFacts.InducesStdKind Y c .field)
    (hrig : ∀ t : G, t ∈ Subgroup.normalizer (Y : Set G) → (∃ k : ℕ, t ^ 3 ^ k = 1) →
      t * c = c * t → (∀ k ∈ sec11K L a, t * k * t⁻¹ * k⁻¹ ∈
        inSubgroup (aschbacherSolvableCore 3) (sec11K L a)) →
      ∃ i : ℕ, t * c ^ i ∈ Sec4.thetaQuotCentralizer Y) :
    Subgroup.zpowers c = Subgroup.zpowers s ⊓ Subgroup.centralizer {a} := by
  have hAe := h.mem_partTwoF.1
  have hcs := h.c_mem_zpowers_s
  have hca : c ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hAe.1.is_comm.comm ⟨c, h.mem_A⟩ ⟨a, h.a_mem⟩))
  apply le_antisymm
  · exact Subgroup.zpowers_le.mpr ⟨hcs, hca⟩
  rintro t ⟨hts, hta⟩
  have htR : t ∈ R := Subgroup.zpowers_le.mpr (Item1116Proof.mem_R h).2.2 hts
  obtain ⟨hRc, hRL⟩ := Item1116Proof.le_centralizer_and_normalizer h45 h
  have htc : t * c = c * t := Subgroup.mem_centralizer_singleton_iff.mp (hRc htR)
  have hta' : t * a = a * t := Subgroup.mem_centralizer_singleton_iff.mp hta
  have htC : t ∈ Sec4.thetaQuotCentralizer L := by
    rw [← h.inf_centralizer_eq] at hts
    exact hts.2
  obtain ⟨-, -, hd1⟩ := h.toSec11Std.not_mem_facts h.inf_eq h.closure_eq
  have hdK := h.toSec11Std.d_mem_sec11K h.inf_eq
  have hK1 : sec11K L a ≠ ⊥ := fun hb => hd1 (by rw [hb, Subgroup.mem_bot] at hdK; exact hdK)
  have htY := h.toSec11Std.mem_normalizer_Y hK1 (hRL htR) hta'
  obtain ⟨i, hi⟩ := hrig t htY (Item1116Proof.exists_pow_eq_one_of_mem h htR) htc
    (Item1116Proof.commutator_mem_theta_sec11K (hRL htR) hta' htC)
  have hu : t * c ^ i ∈ Subgroup.zpowers s := Subgroup.mul_mem _ hts (Subgroup.pow_mem _ hcs i)
  have ht : t = (c ^ i)⁻¹ := eq_inv_of_mul_eq_one_left (eq_one_of_mem_zpowers_s h hf hu hi)
  rw [ht]
  exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers c) i)

theorem rank3II_11_13_1_of_item82 (h82 : Sec8.Item82One) (h118 : Item118) (h45 : Sec4.Item4_5)
    {A : Subgroup G} {c : G} {L : Subgroup G} {a : G} {R Y : Subgroup G} {d x s r g : G}
    (h : Sec11Data G A c L a R Y d x s r g) (hf : KFacts.InducesStdKind Y c .field) :
    Subgroup.zpowers c = Subgroup.zpowers s ⊓ Subgroup.centralizer {a} :=
  rank3II_11_13_1_of_rigid h45 h hf fun t htY ht3 htc htK =>
    fieldCentRigid82 G Y (sec11K L a) c t hf (h.isList82One_of_field h82 h118 hf)
      (h.mem_partTwoF.1.2 c h.mem_A) (mem_thetaComponentsIn_sec11K_inf h.toSec11Std)
      (kType119 G A c L a R Y h.toSec11Std d h.inf_eq h.closure_eq) htY ht3 htc htK

theorem item11131_of_item82 (h82 : Sec8.Item82One) (h118 : Item118) (h45 : Sec4.Item4_5) :
    Item11131 :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ h hf => rank3II_11_13_1_of_item82 h82 h118 h45 h hf

theorem item1116_of_item82 (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (h82 : Sec8.Item82One) (h118 : Item118) (h119 : Item119) (hCB : CentBound119) : Item1116 :=
  item1116_of_item11131 h45 h113 h117 (item11131_of_item82 h82 h118 h45) h118 h119 hCB

theorem item1134_of_steps_data_item82 (h812 : Sec8.Item812) (h1016 : Sec10.Item1016)
    (h97 : Sec9.Item97) (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h113 : Item113)
    (h117 : Item117) (h82 : Sec8.Item82One) (h118 : Item118) (h119 : Item119)
    (hCB : CentBound119) (h1117 : Item1117) (hset : SetUp1118) (h1119 : Item1119)
    (h1123 : Item1123) (hinv : Inverter1118) (hch : Choose1128) (h1132 : Item1132) :
    Item1134 :=
  item1134_of_steps_data h812 h1016 h97 h45 h48 h113 h117 h119
    (item1116_of_item82 h45 h113 h117 h82 h118 h119 hCB) h1117 hset h1119 h1123 hinv hch h1132

end Main

end CFSG.RankThree.PartTwo.Sec11
