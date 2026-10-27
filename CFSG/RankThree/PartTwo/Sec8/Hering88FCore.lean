module

public import CFSG.RankThree.PartTwo.Sec8.Hering88EM1
public import CFSG.RankThree.PartTwo.Sec8.Hering88FSylow
public import CFSG.RankThree.PartTwo.Sec8.Hering88FCoprime
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofAssembly
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts3ProofPairNL
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.RankThree.PartTwo.Sec8.Hering88CEng
public import CFSG.RankThree.PartTwo.Sec8.Item86ResProofOrders
public import CFSG.RankThree.PartTwo.Sec8.Item87Res2ProofLink

public section

namespace CFSG.RankThree.PartTwo.Sec8

namespace Hering88F

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def ClassBDichotomy {G : Type} [Group G] [Finite G] (Y : Subgroup G) (c d : G)
    (m : ℕ) : Prop :=
  Nonempty (imageModTheta Y (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G))) ≃*
      projSL 2 (GaloisField 2 (3 * m))) ∨
    ∃ z ∈ inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers c) Y ⊓
        barCentralizer (Subgroup.zpowers d) Y),
      z ≠ 1 ∧ z ^ 3 = 1 ∧ ∀ y ∈ inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers c) Y ⊓
        barCentralizer (Subgroup.zpowers d) Y), z * y = y * z

section Core


theorem not_isUnitaryTwo_three_of_two_le {X : Type} [Group X] {n : ℕ} (hn : 2 ≤ n)
    (hΓ : IsGammaType X n) : ¬ IsUnitaryTwo X 3 := by
  intro hU
  have hU' : Item86ResProof.UnitarySig X 3 := by
    rcases hU with he | hS
    · obtain ⟨e⟩ := he
      exact Item86ResProof.unitarySig_of_projSU (by norm_num) e
    · exact Item86ResProof.unitarySig_of_isoSUThree (by norm_num) hS
  rcases Item86ResProof.sig_of_isGammaType (by omega) hΓ with hs | hs | hs | hs | hs <;>
  · have := Item86ResProof.two_eq hs.profile hU'.profile
    omega

theorem inSubgroup_perfectResidual_eq_of_isoGTwoEven {Q : Type} [Group Q] [Finite Q]
    {R : Subgroup Q} {m : ℕ} (hm : 2 ≤ m) (h : IsoGTwoEven R m) :
    inSubgroup perfectResidual R = R := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  have hK3 : 3 ≤ Nat.card K := by
    rw [hK]
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hq := CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card K hK3
  have hqR : IsQuasisimple R := LocalCores.isQuasisimple_of_mulEquiv e.symm hq
  haveI : Group.IsPerfect R := hqR.1
  exact inSubgroup_perfectResidual_of_isPerfect (R := R) inferInstance

theorem classB_core_c (h45 : Sec4.Item4_5) (hF : KF84Field)
    {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a b : G}
    {X : Subgroup G} {n : ℕ} (h : Sec8Pair G A c L a b X n) (hn2 : 2 ≤ n)
    (hKL2 : Nonempty (imageModTheta L (inSubgroup perfectResidual
      (L ⊓ Subgroup.centralizer ({b} : Set G))) ≃* projSL 2 (GaloisField 2 (3 * n))))
    {Y : Subgroup G} (hY : Y ∈ thetaComponentsAt 3 a) (hIJ : sec8I L a ⊔ sec8J X a ≤ Y)
    (hcN : c ∈ Subgroup.normalizer (Y : Set G)) {m : ℕ} (hm2 : 2 ≤ m)
    (hG2 : IsoGTwoEven (barCentralizer (Subgroup.zpowers c) Y) m)
    {d : G} (hdcl : d ∈ Subgroup.closure ({c, b} : Set G)) (hdc : d ∉ Subgroup.zpowers c)
    (hdA : d ∈ A) (hd3 : d ^ 3 = 1) (hdN : d ∈ Subgroup.normalizer (Y : Set G))
    (hdich : ClassBDichotomy Y c d m) :
    Nonempty (imageModTheta Y (inSubgroup perfectResidual
      (Y ⊓ Subgroup.centralizer ({d} : Set G))) ≃* projSL 2 (GaloisField 2 (3 * m))) := by
  rcases hdich with hL | ⟨z, hz, hz1, hz3, hzc⟩
  · exact hL
  exfalso
  obtain ⟨hAc, hA3⟩ := Hering88C.pair_commute_pow_three h
  have hAel := h.mem_partTwoF.1
  obtain ⟨hbA, hb1, hn1, -⟩ := Item87Proof.isGammaIndex_cases h.isGammaIndex
  have ha3 : a ^ 3 = 1 := hA3 a h.a_mem
  have hc3 : c ^ 3 = 1 := hA3 c h.mem_A
  have hAp : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hA3 g g.2)⟩
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    (PartOne.mem_thetaComponentsAt_iff.mp h.mem_thetaComponentsAt).1
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    Sec11.le_normalizer_of_isPGroup_of_le_centralizer h45 h.toTheoremFourHyp hc3 h.ne_one hAp
      (fun u hu => Subgroup.mem_centralizer_singleton_iff.mpr (hAc u hu c h.mem_A)) L
      h.mem_thetaComponentsAt
  have hUn : ¬ IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) 3 :=
    not_isUnitaryTwo_three_of_two_le hn2 (Item87Proof.isGammaType_of_isGammaIndex h.isGammaIndex)
  have hIdef : sec8I L a = inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({a} : Set G)) := by
    simp only [sec8I, hUn, ↓reduceIte]
  set K := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) with hK
  have hKL : K ≤ L := (Item87Proof.residual_le _).trans inf_le_left
  have hKc : K ≤ Subgroup.centralizer ({c} : Set G) := hKL.trans hLc
  have hT0 : inSubgroup perfectResidual (K ⊓ Subgroup.centralizer ({a} : Set G)) ≠ ⊥ := by
    refine Item87Res2Proof.residual_centralizer_ne_bot_of_field hn2 ?_ ha3 (hF G A c L a b X n h)
    exact Or.inr (Item8KFacts3.nonempty_quot_projSL_of_data (by omega) hKL2)
  have hT0I : inSubgroup perfectResidual (K ⊓ Subgroup.centralizer ({a} : Set G)) ≤ sec8I L a := by
    rw [hIdef]
    refine KFacts.le_inSubgroup_perfectResidual (Item87Proof.isPerfect_residual _)
      (le_inf ((Item87Proof.residual_le _).trans (inf_le_left.trans hKL))
        ((Item87Proof.residual_le _).trans inf_le_right))
  have hI : sec8I L a ≠ ⊥ := fun hbot => hT0 (le_bot_iff.mp (hbot ▸ hT0I))
  have hIY : sec8I L a ≤ Y := le_sup_left.trans hIJ
  have hM1 := Hering88E.imageModTheta_sec8I_eq_perfectResidual_of_isoGTwoEven kF87Cent_holds h hUn
    hI hY hIY hcN hm2 hG2
  rw [inSubgroup_perfectResidual_eq_of_isoGTwoEven hm2 hG2] at hM1
  have hdL : d ∈ Subgroup.normalizer (L : Set G) := hAL hdA
  have hda : d ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hAc d hdA a h.a_mem)
  have hdI : d ∈ Subgroup.normalizer (sec8I L a : Set G) := by
    rw [hIdef]
    exact CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual
      _ (Subgroup.inf_normalizer_le_normalizer_inf ⟨hdL, Subgroup.le_normalizer hda⟩)
  set T := inSubgroup perfectResidual (sec8I L a ⊓ Subgroup.centralizer ({d} : Set G)) with hT
  have hTI : T ≤ sec8I L a ⊓ Subgroup.centralizer ({d} : Set G) := Item87Proof.residual_le _
  have hTY : T ≤ Y := hTI.trans (inf_le_left.trans hIY)
  have hTeq : imageModTheta Y T = inSubgroup perfectResidual
      (barCentralizer (Subgroup.zpowers c) Y ⊓ barCentralizer (Subgroup.zpowers d) Y) := by
    rw [hT, imageModTheta_residual_inf_centralizer_eq hIY hdN hdI hd3, hM1]
  have hCdc : Subgroup.centralizer ({d} : Set G) ⊓ Subgroup.centralizer {c} ≤
      Subgroup.centralizer {c} ⊓ Subgroup.centralizer {b} :=
    Item87Proof.inf_centralizer_le_of_mem_closure hAel h.mem_A hbA hdcl h.ne_one hdc
  have hIL : sec8I L a ≤ L := by
    rw [hIdef]
    exact (Item87Proof.residual_le _).trans inf_le_left
  have hIcd : sec8I L a ⊓ Subgroup.centralizer ({d} : Set G) ≤
      L ⊓ Subgroup.centralizer ({b} : Set G) := by
    intro w hw
    have hwL : w ∈ L := hIL hw.1
    have hwcb : w ∈ Subgroup.centralizer {c} ⊓ Subgroup.centralizer {b} :=
      hCdc ⟨hw.2, hLc hwL⟩
    exact ⟨hwL, hwcb.2⟩
  have hTK : T ≤ K := KFacts.le_inSubgroup_perfectResidual (Item87Proof.isPerfect_residual _)
    (hTI.trans hIcd)
  obtain ⟨e⟩ := hKL2
  have hTcomm : ∀ P : Subgroup G, P ≤ T → IsPGroup 3 P → ∀ u ∈ P, ∀ v ∈ P, u * v = v * u :=
    fun P hPT hP => commute_of_isPGroup_of_imageModTheta hKL (by omega) e (hPT.trans hTK) hP
  exact false_of_central_three_of_eq hTY hTcomm hTeq (Item87Proof.isPerfect_residual _) hz hz1 hz3
    hzc

end Core

end Hering88F

end CFSG.RankThree.PartTwo.Sec8
