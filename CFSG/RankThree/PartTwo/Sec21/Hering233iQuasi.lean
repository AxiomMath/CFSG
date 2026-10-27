module

public import CFSG.RankThree.PartTwo.Sec21.Hering233iCore
public import CFSG.RankThree.PartTwo.Sec21.Hering233iE16
public import CFSG.RankThree.PartTwo.Sec6.Item612Local
import CFSG.RankThree.PartTwo.Sec6.Item612Core
import CFSG.RankThree.PartTwo.Sec6.Item63
import CFSG.LocalAnalysis.SignalizerFunctor.TwoStageSylowNormalizers

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering233i

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (localRank)
open scoped commutatorElement

variable {G : Type} [Group G]

theorem pCore_two_le_center_of_act [Finite G] {A : Subgroup G} (hAS : A ∈ partTwoS G) {c : G}
    (hcA : c ∈ A) (hc1 : c ≠ 1) {L : Subgroup G} (hLc : L ∈ thetaComponentsAt 3 c)
    (hAL : A ≤ Subgroup.normalizer (L : Set G))
    (hact : ∃ a : G, ∃ ha : a ∈ A, ∃ l : L,
      (⟨⁅(l : G), a⁆, Item21EarlyProof.commutatorElement_mem (hAL ha) l.2⟩ : L) ∉
        Item21EarlyProof.centerPre (aschbacherSolvableCore 3 L)) :
    CFSG.pCore 2 L ≤ Subgroup.center L := by
  have hLp : Group.IsPerfect L := Sec6.isPerfect_of_mem_thetaComponentsAt hLc
  have hLq : IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L) :=
    Sec6.isQuasisimple_of_mem_thetaComponentsAt hLc
  obtain ⟨hTs, -, -, -, -, -, hpT⟩ := solvable_prime_complement_core_characterization
    (H := L) Nat.prime_three
  set T := aschbacherSolvableCore 3 L with hT
  set Q := CFSG.pCore 2 L with hQ
  set QG := Q.map L.subtype with hQG
  have hQT : Q ≤ T := hpT 2 Nat.prime_two (by norm_num)
  have hQ2 : IsPGroup 2 QG := CFSG.pCore_isPGroup.map _
  have hAQ : A ≤ Subgroup.normalizer (QG : Set G) :=
    hAL.trans (SignalizerFunctor.Helpers.normalizer_le_normalizer_characteristic L Q)
  have hQθ : QG ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({c} : Set G)) :=
    (Subgroup.map_mono hQT).trans (theta_le_theta_centralizer hLc)
  have hcomm : ⁅QG, A⁆ = ⊥ :=
    Sec6.commutator_eq_bot_of_mem_partTwoS hAS hcA hc1 le_rfl hQθ hQ2 hAQ
  have hLQ : L ≤ Subgroup.normalizer (QG : Set G) := Sec6.le_normalizer_map_subtype Q
  have h3 : ⁅⁅L, A⁆, QG⁆ = ⊥ := by
    refine Subgroup.commutator_commutator_eq_bot_of_rotate ?_ ?_
    · rw [Subgroup.commutator_comm A QG, hcomm, Subgroup.commutator_bot_left]
    · exact eq_bot_iff.mpr ((Subgroup.commutator_mono
        (Subgroup.le_normalizer_iff_commutator_le_left.mp hLQ) le_rfl).trans hcomm.le)
  have hLAQ : ⁅L, A⁆ ≤ Subgroup.centralizer (QG : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3
  set C := Subgroup.centralizer (Q : Set L) with hC
  have hCn : C.Normal := Subgroup.normal_centralizer
  have hLAC : ∀ (l : L) (a : G) (ha : a ∈ A),
      (⟨⁅(l : G), a⁆, Item21EarlyProof.commutatorElement_mem (hAL ha) l.2⟩ : L) ∈ C := by
    intro l a ha
    rw [hC, Subgroup.mem_centralizer_iff]
    intro q hq
    apply Subtype.ext
    have hx : ⁅(l : G), a⁆ ∈ ⁅L, A⁆ := Subgroup.commutator_mem_commutator l.2 ha
    have := Subgroup.mem_centralizer_iff.mp (hLAQ hx) (q : G) ⟨q, hq, rfl⟩
    simpa using this
  set K₀ := Item21EarlyProof.centerPre T with hK₀
  have hK₀s : Group.IsSolvable K₀ := Item21EarlyProof.isSolvable_centerPre T hTs
  have : IsSimpleGroup ((L ⧸ T) ⧸ Subgroup.center (L ⧸ T)) := hLq.2.1
  have : IsSimpleGroup (L ⧸ K₀) := (Item21EarlyProof.centerPreEquiv T).isSimpleGroup
  have hCK : ¬ C ≤ K₀ := by
    intro hCK
    obtain ⟨a, ha, l, hl⟩ := hact
    exact hl (hCK (hLAC l a ha))
  have hCtop : C = ⊤ := Sec4.Census.eq_top_of_not_le hK₀s hCK
  intro q hq
  rw [Subgroup.mem_center_iff]
  intro l
  have hl : l ∈ C := hCtop ▸ Subgroup.mem_top l
  exact (Subgroup.mem_centralizer_iff.mp hl q hq).symm

theorem exists_act_of_simple [Finite G] {A L K : Subgroup G}
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (hKL : K ≤ L) [IsSimpleGroup K]
    (hKnc : ∃ x ∈ K, ∃ y ∈ K, x * y ≠ y * x) {a : G} (haA : a ∈ A) (haK : a ∈ K)
    (ha1 : a ≠ 1) :
    ∃ a : G, ∃ ha : a ∈ A, ∃ l : L,
      (⟨⁅(l : G), a⁆, Item21EarlyProof.commutatorElement_mem (hAL ha) l.2⟩ : L) ∉
        Item21EarlyProof.centerPre (aschbacherSolvableCore 3 L) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hTs, -⟩ := solvable_prime_complement_core_characterization (H := L) Nat.prime_three
  set T := aschbacherSolvableCore 3 L with hT
  set K₀ := Item21EarlyProof.centerPre T with hK₀
  have hK₀s : Group.IsSolvable K₀ := Item21EarlyProof.isSolvable_centerPre T hTs
  set K₀' : Subgroup G := K₀.map L.subtype with hK₀'
  have hK₀'s : Group.IsSolvable K₀' :=
    Group.isSolvable_of_surjective (f := (K₀.equivMapOfInjective L.subtype
      L.subtype_injective).toMonoidHom) (MulEquiv.surjective _)
  have hKN : K ≤ Subgroup.normalizer (K₀' : Set G) := hKL.trans (Sec6.le_normalizer_map_subtype K₀)
  have hbot : K ⊓ K₀' = ⊥ := inf_eq_bot_of_simple hKnc hKN hK₀'s
  have hcomm : ∀ l ∈ K, l * a = a * l := by
    intro l hl
    have h1 : ⁅l, a⁆ ∈ K ⊓ K₀' := by
      refine ⟨?_, ?_⟩
      · rw [commutatorElement_def]
        exact K.mul_mem (K.mul_mem (K.mul_mem hl haK) (K.inv_mem hl)) (K.inv_mem haK)
      · exact ⟨_, hcon a haA ⟨l, hKL hl⟩, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  have hzc : (⟨a, haK⟩ : K) ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcomm g g.2)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K) with hc | hc
  · rw [hc, Subgroup.mem_bot] at hzc
    exact ha1 (congrArg Subtype.val hzc)
  · obtain ⟨x, hx, y, hy, hxy⟩ := hKnc
    have : (⟨y, hy⟩ : K) ∈ Subgroup.center K := by rw [hc]; exact Subgroup.mem_top _
    exact hxy (congrArg Subtype.val (Subgroup.mem_center_iff.mp this ⟨x, hx⟩))

open Item21EarlyProof Item21Early2Proof in
theorem isQuasisimple_of_e16 [Finite G] (h44 : Sec4.Item4_4)
    (hG : TheoremFourHyp G) {A : Subgroup G} (hAS : A ∈ partTwoS G) {b : G} (hbA : b ∈ A)
    (hb1 : b ≠ 1) {X₀ : Subgroup G} (hX₀ : X₀ ∈ thetaComponentsAt 3 b)
    (hAX₀ : A ≤ Subgroup.normalizer (X₀ : Set G)) {K : Subgroup G} (hKX₀ : K ≤ X₀)
    [IsSimpleGroup K] (hKnc : ∃ x ∈ K, ∃ y ∈ K, x * y ≠ y * x) {u v : G} (hu : u ∈ K)
    (hv : v ∈ K) (hu1 : u ≠ 1) (hv1 : v ≠ 1) (huv : u ≠ v) (hu2 : u * u = 1)
    (hv2 : v * v = 1) {a : G} (haA : a ∈ A) (haK : a ∈ K) (ha1 : a ≠ 1) {E : Subgroup G}
    (hEc : ∀ x y : E, x * y = y * x) (hE2 : ∀ x ∈ E, x ^ 2 = 1) (hE16 : Nat.card E = 2 ^ 4)
    (hEX₀ : E ≤ Subgroup.normalizer (X₀ : Set G)) : IsQuasisimple X₀ := by
  have hLp : Group.IsPerfect X₀ := Sec6.isPerfect_of_mem_thetaComponentsAt hX₀
  have hLq : IsQuasisimple (X₀ ⧸ aschbacherSolvableCore 3 X₀) :=
    Sec6.isQuasisimple_of_mem_thetaComponentsAt hX₀
  have hX₀C : X₀ ≤ Subgroup.centralizer ({b} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hX₀
  have hL4 : SectionFourHyp X₀ := by
    have hne : X₀ ≠ ⊤ := fun h =>
      Sec6.centralizer_ne_top_of_ne_one hG hb1 (top_le_iff.mp (h ▸ hX₀C))
    exact hG.sectionFourHyp hne
  have hact := exists_act_of_simple hAX₀ hKX₀ hKnc haA haK ha1
  have hO2 := pCore_two_le_center_of_act hAS hbA hb1 hX₀ hAX₀ hact
  obtain ⟨hTs, -, hT3, -⟩ := solvable_prime_complement_core_characterization (H := X₀)
    Nat.prime_three
  set T := aschbacherSolvableCore 3 X₀ with hT
  haveI : IsSimpleGroup ((X₀ ⧸ T) ⧸ Subgroup.center (X₀ ⧸ T)) := hLq.2.1
  haveI : IsSimpleGroup (X₀ ⧸ centerPre T) := (centerPreEquiv T).isSimpleGroup
  have hO3 : CFSG.pCore 3 X₀ ≤ Subgroup.center X₀ := pCore_three_le_center T hT3
  let eK : K.subgroupOf X₀ ≃* K := Subgroup.subgroupOfEquivOfLe hKX₀
  haveI : IsSimpleGroup (K.subgroupOf X₀) := eK.isSimpleGroup
  let lift : ∀ {x : G}, x ∈ K → X₀ := fun {x} hx => ⟨x, hKX₀ hx⟩
  have hlift : ∀ {x : G} (hx : x ∈ K), lift hx ∈ K.subgroupOf X₀ := fun hx =>
    Subgroup.mem_subgroupOf.mpr hx
  have hne1 : ∀ {x : G} (hx : x ∈ K), x ≠ 1 → lift hx ≠ 1 := fun hx hx1 h =>
    hx1 (congrArg Subtype.val h)
  obtain ⟨x, hx, y, hy, hxy⟩ := hKnc
  refine isQuasisimple_of_item44 h44 hL4 hLq hO2 (S := K.subgroupOf X₀)
    ⟨lift hx, hlift hx, lift hy, hlift hy, fun h => hxy (congrArg Subtype.val h)⟩
    (u := lift hu) (v := lift hv) (hlift hu) (hlift hv) (hne1 hu hu1) (hne1 hv hv1)
    (fun h => huv (congrArg Subtype.val h))
    (Subtype.ext (by simpa using hu2)) (Subtype.ext (by simpa using hv2)) ?_
  intro hO2' hQ p hp hpS
  exact linearOutcome_of_e16 hG.localRank_lt (isSolvable_centerPre T hTs) hO2' hO3 hEc hE2 hE16
    hEX₀ p hp hpS

end CFSG.RankThree.PartTwo.Sec21.Hering233i
