module

public import CFSG.RankThree.PartTwo.Sec14.Item145Bot
import CFSG.RankThree.PartTwo.Sec14.Item14Hyperplanes
import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
import CFSG.Sporadic.J2

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo.Sec13 CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem isQuasisimple_nativeJ2 (hJ2 : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2)
    (hJ2c : Subgroup.center CFSG.Blueprint.NativeSporadic.J2 = ⊥) :
    CFSG.IsQuasisimple CFSG.Blueprint.NativeSporadic.J2 := by
  refine (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup ?_).1
  by_contra h
  push Not at h
  obtain ⟨x, hx⟩ := exists_ne (1 : CFSG.Blueprint.NativeSporadic.J2)
  have hxc : x ∈ Subgroup.center CFSG.Blueprint.NativeSporadic.J2 :=
    Subgroup.mem_center_iff.mpr fun g => h g x
  rw [hJ2c] at hxc
  exact hx (Subgroup.mem_bot.mp hxc)

theorem isQuasisimple_of_mulEquiv_nativeJ2 {X : Type*} [Group X]
    (hJ2 : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2)
    (hJ2c : Subgroup.center CFSG.Blueprint.NativeSporadic.J2 = ⊥)
    (e : X ≃* CFSG.Blueprint.NativeSporadic.J2) : CFSG.IsQuasisimple X :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm (isQuasisimple_nativeJ2 hJ2 hJ2c)

theorem ncard_omegaA_le_twelve' (h134 : Item134)
    (hJ2 : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2) (h48 : Sec4.Item4_8)
    (h415 : Sec4.Item4_15)
    (hJ2c : Subgroup.center CFSG.Blueprint.NativeSporadic.J2 = ⊥) {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L) {B L' : Subgroup G} {b d : G} (hc : IsLBConfig A B b d L')
    (hB : IsHyperplane A B) : (omegaA A).ncard ≤ 12 := by
  have hA : CFSG.RankThree.PartTwo.Late.IsE27 A := h.isE27
  obtain ⟨hb1, hd1⟩ := hc.ne_one hB hA
  obtain ⟨hBbd, hbΩ, hLb, ⟨e⟩, hdL, S, hdS, hSd⟩ := hc
  have hbA : b ∈ A := hB.1 (hBbd ▸ Subgroup.subset_closure (Set.mem_insert b {d}))
  have hdA : d ∈ A := hB.1 (hBbd ▸ Subgroup.subset_closure (Set.mem_insert_of_mem b rfl))
  have hL'mem : L' ∈ lA A b := hLb ▸ Set.mem_singleton L'
  have hdata : Sec13Data G A b L' :=
    { h.toSec13Data with zpowers_mem_omegaA := hbΩ, mem_lA := hL'mem }
  have hc0 : Subgroup.center (↥L' ⧸ CFSG.pCore 2 ↥L') = ⊥ := by
    have hmap := Subgroup.map_center_eq e
    rw [hJ2c] at hmap
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hmap
  have hq := isQuasisimple_of_mulEquiv_nativeJ2 hJ2 hJ2c e
  have hθ := aschbacherSolvableCore_eq_pCore_two hq hc0
  have hJ2θ : Nonempty (↥L' ⧸ LocalRank.aschbacherSolvableCore 3 ↥L' ≃*
      CFSG.Blueprint.NativeSporadic.J2) :=
    ⟨(QuotientGroup.quotientMulEquivOfEq hθ).trans e⟩
  have hS := center_sylow_eq_zpowers_of_j2 h415 ⟨e⟩ hdL hd1 S hdS hSd
  have hG4 : SectionFourHyp ↥(Subgroup.centralizer ({d} : Set G)) :=
    h.toTheoremFourHyp.sectionFourHyp
      (centralizer_singleton_ne_top h.isSimpleGroup h.nonabelian hd1)
  have hJq := residual_inf_centralizer_quasisimple h415 ⟨e⟩ hdL hd1 ⟨S, hdS, hSd⟩
  obtain ⟨K, hK, hJK⟩ :=
    exists_mem_thetaComponentsAt_le_residual h48 hG4 hA hbA hdA hb1 hL'mem.1 hJq
  rcases h134 G A b L' hdata hJ2θ d hdA hd1 ⟨_, hS⟩ K hK hJK with
    ⟨-, -, h1⟩ | ⟨-, -, -, -, -, -, h2⟩ | ⟨-, -, -, h3⟩
  · rw [h1, Set.ncard_singleton]
    norm_num
  · rcases h2 with ⟨-, h⟩ | ⟨I, -, -, -, a, -, -, -, h, -⟩ <;> omega
  · omega

theorem exists_isHyperplane_lB_eq_bot' (h134 : Item134)
    (hJ2 : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2) (h48 : Sec4.Item4_8)
    (h415 : Sec4.Item4_15)
    (hJ2c : Subgroup.center CFSG.Blueprint.NativeSporadic.J2 = ⊥) {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L) : ∃ B, IsHyperplane A B ∧ lB A B = ⊥ := by
  have hA : CFSG.RankThree.PartTwo.Late.IsE27 A := h.isE27
  by_contra hall
  push Not at hall
  have hcfg : ∀ B, IsHyperplane A B → ∃ b d L', IsLBConfig A B b d L' := fun B hB => by
    by_contra hno
    push Not at hno
    exact hall B hB (lB_eq_bot hno)
  choose! bB dB LB' hcfgB using hcfg
  obtain ⟨f, -, hf⟩ := exists_hyperplanes_thirteen hA
  have h12 := ncard_omegaA_le_twelve' h134 hJ2 h48 h415 hJ2c h (hcfgB (f 0) (hf 0)) (hf 0)
  refine false_of_injOn_hyperplanes hA h12 (fun B => Subgroup.zpowers (bB B))
    (fun B hB => (hcfgB B hB).2.1) ?_
  intro B B' hB hB' heq
  exact IsLBConfig.eq_of_zpowers_eq h415 hA (hcfgB B hB) (hcfgB B' hB') hB hB' heq

theorem forall_exists_isHyperplane_lB_eq_bot (h134 : Item134)
    (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec14Std G A c L → ∃ B, IsHyperplane A B ∧ lB A B = ⊥ :=
  fun _ _ _ _ _ _ h => exists_isHyperplane_lB_eq_bot' h134 CFSG.Sporadic.J2.isSimpleGroup_J2 h48
    h415 (KFacts.KS14.center_nativeJ2_eq_bot h415) h

theorem rank3II_14_5_of' (h134 : Item134)
    (hJ2 : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2) (h48 : Sec4.Item4_8)
    (h415 : Sec4.Item4_15)
    (hJ2c : Subgroup.center CFSG.Blueprint.NativeSporadic.J2 = ⊥) {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L) {Y : Subgroup G} (hY : A ≤ Subgroup.normalizer (Y : Set G)) :
    delta A (lB A) Y =
        deltaZero A (lB A) Y ⊔ (pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊓ Y) ∧
      deltaZero A (lB A) Y = ⁅delta A (lB A) Y, A⁆ ∧
      delta A (lB A) Y ≤ Subgroup.normalizer (deltaZero A (lB A) Y : Set G) :=
  rank3II_14_5_lB h.isE27 (exists_isHyperplane_lB_eq_bot' h134 hJ2 h48 h415 hJ2c h) hY

theorem rank3II_15_1_of' (h134 : Item134)
    (hJ2 : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2) (h48 : Sec4.Item4_8)
    (h415 : Sec4.Item4_15)
    (hJ2c : Subgroup.center CFSG.Blueprint.NativeSporadic.J2 = ⊥) {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L) {Y : Subgroup G} (hY : Y ∈ Sec15.scriptY4 A (lB A)) :
    Y = deltaZero A (lB A) Y :=
  rank3II_15_1_lB h.isE27 (exists_isHyperplane_lB_eq_bot' h134 hJ2 h48 h415 hJ2c h) hY

theorem rank3II_14_9_lB_of' (h134 : Item134)
    (hJ2 : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2) (h48 : Sec4.Item4_8)
    (h415 : Sec4.Item4_15)
    (hJ2c : Subgroup.center CFSG.Blueprint.NativeSporadic.J2 = ⊥) {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L) (h147 : Item147 A (lB A)) (h148 : Item148Normal A (lB A)) :
    Item149 A (lB A) :=
  rank3II_14_9_of h.isE27 (isNaturalFamily_lB A)
    (exists_isHyperplane_lB_eq_bot' h134 hJ2 h48 h415 hJ2c h) h147 h148

end CFSG.RankThree.PartTwo.Sec14
