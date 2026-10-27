module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight8xKLeaves2Holds
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.List880Center
public import CFSG.RankThree.PartTwo.KFacts.KS14HJNative
import CFSG.Adapters.LieModelSmallOrders
import CFSG.Adapters.LieModelTorusRank
import CFSG.LocalAnalysis.UniquenessCase.UC22S218P
import CFSG.LocalAnalysis.UniquenessCase.UC6N588D4
import CFSG.LocalAnalysis.UniquenessCase.UC22S218U5
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenTenPiCV
import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.HSThree
import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuThree
import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4ThreeClass
import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4CentCE
import CFSG.RankThree.PartTwo.Sec8.Item84KFacts4ProofSp4
import CFSG.LocalAnalysis.UniquenessCase.Lie.Shared
import CFSG.LocalAnalysis.UniquenessCase.UC22S218U5Cov
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimOrders
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterIdxLinear
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterIdxUnitary
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterIdxClassical
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterIdxTriality
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterIdxExc
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterIdxExcTwisted
import CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.ExcFG
public import CFSG.Foundations.SteinbergCADefinitionNodes
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInputs
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M2Gens
public import CFSG.RankThree.Native.HSMcLSmallData
public import CFSG.Sporadic.Schreier.RuDefs

@[expose] public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.OuterAutomorphisms renaming inner → Inn, equivalence → outerCongr
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSpor IsSp4 IsG2 IsAlt)
open CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan
  (center_eq_bot_of_isSimpleGroup_of_not_prime_card)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08
  (List880 IsA6Z3 IsA7Z3 IsM22Z3 IsSU5 IsMathieu IsG2Der IsSU5Four)

theorem l2cr_exists_sylow_coe_eq {X : Type} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] {S : Subgroup X} (hS : IsSylowOf p S ⊤) :
    ∃ P : Sylow p X, (P : Subgroup X) = S := by
  obtain ⟨-, hS3, hdvd⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hS
  rw [Subgroup.relIndex_top_right] at hdvd
  exact ⟨hS3.toSylow hdvd, rfl⟩

theorem isA6Z3_of_perfect_of_isTripleCover {C : Type} [Group C] (hC : Group.IsPerfect C)
    (h : CFSG.RankThree.PartTwo.Sec4.IsTripleCover C (alternatingGroup (Fin 6))) :
    IsA6Z3 C := by
  obtain ⟨hc, ⟨e⟩⟩ := h
  have hs : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by norm_num)
  have hsC : IsSimpleGroup (C ⧸ center C) := MulEquiv.isSimpleGroup e
  refine ⟨⟨hC, hsC, ?_⟩, hc, ⟨e⟩⟩
  by_contra hne
  have hcomm : ∀ a b : C ⧸ center C, a * b = b * a := fun a b => by
    by_contra h
    exact hne ⟨a, b, h⟩
  have hbot := CFSG.RankThree.PartTwo.Sec14.center_eq_bot_of_mulEquiv_alternating_six e
  have htop : center (C ⧸ center C) = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    rw [Subgroup.mem_center_iff]
    exact fun y => hcomm y x
  have hnt : Nontrivial (C ⧸ center C) :=
    e.toEquiv.nontrivial_congr.mpr hs.toNontrivial
  rw [htop] at hbot
  exact bot_ne_top hbot.symm

theorem j2CentralizerThreeA_holds :
    J2CentralizerThreeA := by
  intro X _ _ hX S hS
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, rfl⟩ := l2cr_exists_sylow_coe_eq hS
  have hX' : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2) := hX
  obtain ⟨hZ3, -, -⟩ := CFSG.RankThree.PartTwo.Sec14.j2_sylow_facts
    CFSG.RankThree.PartTwo.Sec4.Sporadic.rank3II_4_15 hX' P
  set Z : Subgroup X := (P : Subgroup X) ⊓ centralizer ((P : Subgroup X) : Set X) with hZ
  obtain ⟨⟨z, hzZ⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (fun h : Z = ⊥ => by rw [h, Subgroup.card_bot] at hZ3; exact absurd hZ3 (by norm_num))
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hzP : z ∈ (P : Subgroup X) := hzZ.1
  have hzc : ∃ P' : Sylow 3 X, z ∈ (P' : Subgroup X) ∧
      (P' : Subgroup X) ≤ centralizer ({z} : Set X) :=
    ⟨P, hzP, fun y hy => mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp hzZ.2 y hy)⟩
  have hgen : zpowers z = Z :=
    CFSG.RankThree.PartTwo.Sec14.j2_zpowers_eq
      CFSG.RankThree.PartTwo.Sec4.Sporadic.rank3II_4_15 hX' P hz1' hzP hzc
  have hcent : centralizer ((ZOf (P : Subgroup X) : Subgroup X) : Set X) =
      centralizer ({z} : Set X) := by
    rw [ZOf, ← hZ, ← hgen, zpowers_eq_closure, centralizer_closure]
  rw [hcent]
  exact isA6Z3_of_perfect_of_isTripleCover
    (CFSG.RankThree.PartTwo.KFacts.KS14.Native.j2_centralizer_isPerfect hX' hz1' hzc)
    (CFSG.RankThree.PartTwo.KFacts.KS14.Native.j2_centralizer_isTripleCover hX' hz1' hzc)


theorem l2cr_map_conj_map_conj {X : Type} [Group X] (H : Subgroup X) (g h : X) :
    (H.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      H.map (MulAut.conj (g * h)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem l2cr_map_conj_one {X : Type} [Group X] (H : Subgroup X) :
    H.map (MulAut.conj (1 : X)).toMonoidHom = H := by
  ext x
  simp [Subgroup.mem_map]

theorem l2cr_exists_map_conj_le_sylow {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (P : Sylow p X) {B : Subgroup X} (hB : IsPGroup p B) :
    ∃ g : X, B.map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup X) := by
  obtain ⟨Q, hBQ⟩ := hB.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X Q P
  refine ⟨g, ?_⟩
  rw [← hg, CFSG.RankThree.PartTwo.Sec14.coe_sylow_smul_eq_map]
  exact Subgroup.map_mono hBQ


section L2J2Aux

open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2
open CFSG.RankThree.Asc83Table

private theorem l2j2_GJ_nonCentral_conj
    {B B' : Subgroup GJ} (hB : B ≤ P3) (hB' : B' ≤ P3)
    (hB3 : Nat.card B = 3) (hB'3 : Nat.card B' = 3) (hBZ : B ≠ ZOf P3) (hB'Z : B' ≠ ZOf P3) :
    ∃ g : GJ, B' = B.map (MulAut.conj g).toMonoidHom := by
  have hZeq : ZOf P3 = Subgroup.zpowers zJ := by
    rw [ZOf, inf_centralizer_P3, z_eq]
  have hzJ3 : Nat.card (Subgroup.zpowers zJ) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime z_cube zJ_ne_one]
  have hmain : ∀ B : Subgroup GJ, B ≤ P3 → Nat.card B = 3 → B ≠ ZOf P3 →
      ∃ g : GJ, B = (Subgroup.zpowers xJ).map (MulAut.conj g).toMonoidHom := by
    intro B hB hB3 hBZ
    have hBZ' : Subgroup.zpowers zJ ≠ B := by
      intro h
      exact hBZ (h.symm.trans hZeq.symm)
    obtain ⟨b, hbB, hbZb⟩ := Set.not_subset.mp (fun h : B ≤ Subgroup.zpowers zJ =>
      have h1 : B = Subgroup.zpowers zJ :=
        Subgroup.eq_of_le_of_card_ge h (by rw [hB3, hzJ3])
      hBZ' h1.symm)
    have hb1 : b ≠ 1 := fun h => hbZb (by rw [h]; exact one_mem _)
    have hdvdB : orderOf (⟨b, hbB⟩ : B) ∣ 3 := by
      rw [← hB3]
      exact orderOf_dvd_natCard _
    have hb3 : b ^ 3 = 1 := by
      have hdvd : orderOf b ∣ 3 :=
        Subgroup.orderOf_coe (⟨b, hbB⟩ : B) ▸ hdvdB
      exact (orderOf_dvd_iff_pow_eq_one).mp hdvd
    have hB_eq : B = Subgroup.zpowers b :=
      (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hbB)
        (by rw [hB3, Nat.card_zpowers, orderOf_eq_prime hb3 hb1])).symm
    have hzJb : zJ ∉ Subgroup.zpowers b := by
      rw [← hB_eq]
      intro hz
      have h1 : Subgroup.zpowers zJ = B :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hz) (by rw [hB3, hzJ3])
      exact hBZ' h1
    have hbz : Commute b zJ := by
      have hzZ : zJ ∈ ZOf P3 := by rw [hZeq]; exact Subgroup.mem_zpowers zJ
      have hzC : zJ ∈ Subgroup.centralizer (P3 : Set GJ) := (Subgroup.mem_inf.mp hzZ).2
      exact Subgroup.mem_centralizer_iff.mp hzC b (hB hbB)
    have hA9 : Nat.card ↥(B ⊔ ZOf P3) = 9 := by
      have hsup : B ⊔ ZOf P3 = Subgroup.closure ({b, zJ} : Set GJ) := by
        rw [hB_eq, hZeq, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
          ← Subgroup.closure_union, Set.singleton_union]
      rw [hsup]
      exact CFSG.RankThree.Asc83Table.card_closure_pair_eq_nine hb3 z_cube hbz hb1 hzJb
    have hAP : B ⊔ ZOf P3 ≤ P3 := sup_le hB inf_le_left
    have hE : E0 ∈ {C : Subgroup GJ | C ≤ P3 ∧ Nat.card C = 9} :=
      ⟨E0_le_P3, (ex27Basis x_cube y_cube z_comm_x z_comm_y z_ne_one 0).card⟩
    have hA : (B ⊔ ZOf P3) ∈ {C : Subgroup GJ | C ≤ P3 ∧ Nat.card C = 9} := ⟨hAP, hA9⟩
    obtain ⟨n, hn, hnA⟩ := delta_transitive E0 hE (B ⊔ ZOf P3) hA
    have hE0 : conjugate (conjugate E0 n) n⁻¹ = E0 := by
      rw [conjugate_conjugate, mul_inv_cancel, conjugate, inv_one, l2cr_map_conj_one]
    have hB₁3 : Nat.card (B.map (MulAut.conj n).toMonoidHom) = 3 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj n).injective, hB3]
    have hB₁_le : B.map (MulAut.conj n).toMonoidHom ≤ E0 := by
      have h : conjugate B n⁻¹ ≤ conjugate (B ⊔ ZOf P3) n⁻¹ := by
        rw [conjugate, conjugate]
        exact Subgroup.map_mono le_sup_left
      rw [hnA, hE0, conjugate, inv_inv] at h
      exact h
    have hB₁Z : B.map (MulAut.conj n).toMonoidHom ≠ ZOf P3 := by
      intro h
      apply hBZ
      have h1 : B = conjugate (ZOf P3) n := by
        have hc := congrArg (fun C : Subgroup GJ =>
          C.map (MulAut.conj n⁻¹).toMonoidHom) h
        rw [l2cr_map_conj_map_conj] at hc
        rw [inv_mul_cancel, l2cr_map_conj_one] at hc
        exact hc
      have hconj_le : conjugate (ZOf P3) n ≤ P3 := by
        rw [conjugate]
        calc (ZOf P3).map (MulAut.conj n⁻¹).toMonoidHom
            ≤ P3.map (MulAut.conj n⁻¹).toMonoidHom := Subgroup.map_mono inf_le_left
          _ = P3 := Subgroup.mem_normalizer_iff_map_conj_eq.mp (inv_mem hn)
      have hweak := weaklyClosed n (by rwa [hZeq] at hconj_le)
      exact h1.trans (by rwa [← hZeq] at hweak)
    have hB₁Z' : B.map (MulAut.conj n).toMonoidHom ≠ Subgroup.zpowers zJ := by
      rwa [hZeq] at hB₁Z
    obtain ⟨a, haB₁, haZ⟩ := Set.not_subset.mp (fun h : B.map (MulAut.conj n).toMonoidHom ≤
      Subgroup.zpowers zJ =>
      have h1 : B.map (MulAut.conj n).toMonoidHom = Subgroup.zpowers zJ :=
        Subgroup.eq_of_le_of_card_ge h (by rw [hB₁3, hzJ3])
      hB₁Z' h1)
    have ha1 : a ≠ 1 := fun h => haZ (by rw [h]; exact one_mem _)
    have hdvdA : orderOf (⟨a, haB₁⟩ : B.map (MulAut.conj n).toMonoidHom) ∣ 3 := by
      rw [← hB₁3]
      exact orderOf_dvd_natCard _
    have ha3 : a ^ 3 = 1 := by
      have hdvd : orderOf a ∣ 3 :=
        Subgroup.orderOf_coe (⟨a, haB₁⟩ : B.map (MulAut.conj n).toMonoidHom) ▸ hdvdA
      exact (orderOf_dvd_iff_pow_eq_one).mp hdvd
    have hB₁_eq : B.map (MulAut.conj n).toMonoidHom = Subgroup.zpowers a :=
      (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr haB₁)
        (by rw [hB₁3, Nat.card_zpowers, orderOf_eq_prime ha3 ha1])).symm
    have haE0 : a ∈ E0 := hB₁_le (hB₁_eq ▸ Subgroup.mem_zpowers a)
    obtain ⟨k, hk⟩ := zpowers_eq_a haE0 haZ
    have hck : (Subgroup.zpowers xJ).map (MulAut.conj (cJ k)).toMonoidHom =
        Subgroup.zpowers (aJ k) := by
      rw [MonoidHom.map_zpowers]
      change Subgroup.zpowers ((MulAut.conj (cJ k)) xJ) = Subgroup.zpowers (aJ k)
      rw [MulAut.conj_apply, (c_spec k).2]
    refine ⟨n⁻¹ * cJ k, ?_⟩
    calc B = (B.map (MulAut.conj n).toMonoidHom).map (MulAut.conj n⁻¹).toMonoidHom := by
          rw [l2cr_map_conj_map_conj, inv_mul_cancel, l2cr_map_conj_one]
      _ = ((Subgroup.zpowers xJ).map (MulAut.conj (cJ k)).toMonoidHom).map
            (MulAut.conj n⁻¹).toMonoidHom := by rw [hB₁_eq, hk, hck]
      _ = (Subgroup.zpowers xJ).map (MulAut.conj (n⁻¹ * cJ k)).toMonoidHom := by
          rw [l2cr_map_conj_map_conj]
  obtain ⟨g, hg⟩ := hmain B hB hB3 hBZ
  obtain ⟨g', hg'⟩ := hmain B' hB' hB'3 hB'Z
  refine ⟨g' * g⁻¹, ?_⟩
  rw [hg, hg', l2cr_map_conj_map_conj, show (g' * g⁻¹) * g = g' by group]

private theorem l2j2_nonCentral_conj_aux
    {X : Type} [Group X] [Finite X] (hX : IsSpor X .J2) {S : Subgroup X}
    (hS : IsSylowOf 3 S ⊤) {B B' : Subgroup X} (hB : B ≤ S) (hB' : B' ≤ S)
    (hB3 : Nat.card B = 3) (hB'3 : Nat.card B' = 3) (hBZ : B ≠ ZOf S) (hB'Z : B' ≠ ZOf S) :
    ∃ g : X, B' = B.map (MulAut.conj g).toMonoidHom := by
  let Q : ∀ (G : Type) [Group G], Subgroup G → Prop := fun G _ P =>
    ∀ B B' : Subgroup G, B ≤ P → B' ≤ P → Nat.card B = 3 → Nat.card B' = 3 →
      B ≠ ZOf P → B' ≠ ZOf P → ∃ g : G, B' = B.map (MulAut.conj g).toMonoidHom
  have hQ : ∀ (G G' : Type) [Group G] [Group G'] (φ : G ≃* G') (P : Subgroup G),
      Q G P → Q G' (P.map φ.toMonoidHom) := by
    intro G G' _ _ φ P hP B₂ B₂' hB₂ hB₂' hB₂3 hB₂'3 hB₂Z hB₂'Z
    set B₁ : Subgroup G := B₂.map φ.symm.toMonoidHom with hB₁
    set B₁' : Subgroup G := B₂'.map φ.symm.toMonoidHom with hB₁'
    have hB₁P : B₁ ≤ P := by
      rw [hB₁]
      calc (B₂.map φ.symm.toMonoidHom) ≤ (P.map φ.toMonoidHom).map φ.symm.toMonoidHom :=
            Subgroup.map_mono hB₂
        _ = P := CFSG.RankThree.PartTwo.Sec4.Sporadic.map_symm_map φ P
    have hB₁'P : B₁' ≤ P := by
      rw [hB₁']
      calc (B₂'.map φ.symm.toMonoidHom) ≤ (P.map φ.toMonoidHom).map φ.symm.toMonoidHom :=
            Subgroup.map_mono hB₂'
        _ = P := CFSG.RankThree.PartTwo.Sec4.Sporadic.map_symm_map φ P
    have hB₁3 : Nat.card B₁ = 3 := by
      rw [hB₁, Subgroup.card_map_of_injective φ.symm.injective, hB₂3]
    have hB₁'3 : Nat.card B₁' = 3 := by
      rw [hB₁', Subgroup.card_map_of_injective φ.symm.injective, hB₂'3]
    have hZmap : ZOf (P.map φ.toMonoidHom) = (ZOf P).map φ.toMonoidHom := by
      rw [ZOf, ZOf, CFSG.RankThree.PartTwo.Sec4.Sporadic.map_inf_centralizer]
    have hB₁Z : B₁ ≠ ZOf P := by
      intro hh
      apply hB₂Z
      rw [← CFSG.RankThree.PartTwo.Sec4.Sporadic.map_map_symm φ B₂, ← hB₁, hh, hZmap]
    have hB₁'Z : B₁' ≠ ZOf P := by
      intro hh
      apply hB₂'Z
      rw [← CFSG.RankThree.PartTwo.Sec4.Sporadic.map_map_symm φ B₂', ← hB₁', hh, hZmap]
    obtain ⟨g, hg⟩ := hP B₁ B₁' hB₁P hB₁'P hB₁3 hB₁'3 hB₁Z hB₁'Z
    refine ⟨φ g, ?_⟩
    have hcomp : (φ.toMonoidHom).comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj (φ g)).toMonoidHom.comp φ.toMonoidHom := by
      ext x
      simp [MulAut.conj_apply]
    have hB₁map : B₁.map φ.toMonoidHom = B₂ := by
      rw [hB₁, CFSG.RankThree.PartTwo.Sec4.Sporadic.map_map_symm φ B₂]
    calc B₂' = B₁'.map φ.toMonoidHom := by
          rw [hB₁', CFSG.RankThree.PartTwo.Sec4.Sporadic.map_map_symm φ B₂']
      _ = (B₁.map (MulAut.conj g).toMonoidHom).map φ.toMonoidHom := by rw [hg]
      _ = B₁.map ((φ.toMonoidHom).comp (MulAut.conj g).toMonoidHom) :=
            Subgroup.map_map B₁ φ.toMonoidHom (MulAut.conj g).toMonoidHom
      _ = B₁.map ((MulAut.conj (φ g)).toMonoidHom.comp φ.toMonoidHom) := by rw [hcomp]
      _ = (B₁.map φ.toMonoidHom).map (MulAut.conj (φ g)).toMonoidHom :=
            (Subgroup.map_map B₁ (MulAut.conj (φ g)).toMonoidHom φ.toMonoidHom).symm
      _ = B₂.map (MulAut.conj (φ g)).toMonoidHom := by rw [hB₁map]
  have h0 : Q GJ P3 := fun B B' hB hB' hB3 hB'3 hBZ hB'Z =>
    l2j2_GJ_nonCentral_conj hB hB' hB3 hB'3 hBZ hB'Z
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, rfl⟩ := l2cr_exists_sylow_coe_eq hS
  have hres := forall_sylow_of_P3 Q hQ h0 X hX P
  exact hres B B' hB hB' hB3 hB'3 hBZ hB'Z

end L2J2Aux


theorem j2ThreeClasses_nonCentral_conj
    {X : Type} [Group X] [Finite X] (hX : IsSpor X .J2) {S : Subgroup X}
    (hS : IsSylowOf 3 S ⊤) {B B' : Subgroup X} (hB : B ≤ S) (hB' : B' ≤ S)
    (hB3 : Nat.card B = 3) (hB'3 : Nat.card B' = 3) (hBZ : B ≠ ZOf S) (hB'Z : B' ≠ ZOf S) :
    ∃ g : X, B' = B.map (MulAut.conj g).toMonoidHom := by
  exact l2j2_nonCentral_conj_aux hX hS hB hB' hB3 hB'3 hBZ hB'Z

theorem j2ThreeClasses_holds :
    J2ThreeClasses := by
  intro X _ _ hX S hS
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, rfl⟩ := l2cr_exists_sylow_coe_eq hS
  have hX' : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2) := hX
  obtain ⟨hZ3, hweak, hext⟩ := CFSG.RankThree.PartTwo.Sec14.j2_sylow_facts
    CFSG.RankThree.PartTwo.Sec4.Sporadic.rank3II_4_15 hX' P
  obtain ⟨⟨hHeis, -⟩, -, -, h4, -⟩ :=
    CFSG.RankThree.PartTwo.Sec4.Sporadic.rank3II_4_15 X hX' P _ rfl _ rfl
  change Nat.card ↥(ZOf (P : Subgroup X)) = 3 at hZ3
  have hweak0 : ∀ g : X, CFSG.conjugate (ZOf (P : Subgroup X)) g ≤ (P : Subgroup X) →
      CFSG.conjugate (ZOf (P : Subgroup X)) g = ZOf (P : Subgroup X) := hweak
  have hext0 : CFSG.RankThree.PartTwo.Sec4.IsExtOf
      (centralizer ((ZOf (P : Subgroup X) : Subgroup X) : Set X)) (alternatingGroup (Fin 6))
      (Multiplicative (ZMod 3)) := hext
  have hweak' : ∀ B : Subgroup X, B ≤ (P : Subgroup X) →
      B ∈ MConjSet (⊤ : Subgroup X) (ZOf (P : Subgroup X)) → B = ZOf (P : Subgroup X) := by
    rintro B hB ⟨g, -, rfl⟩
    have e1 : CFSG.conjugate (ZOf (P : Subgroup X)) g⁻¹ =
        (ZOf (P : Subgroup X)).map (MulAut.conj g).toMonoidHom := by
      unfold CFSG.conjugate
      rw [inv_inv]
    have h1 : CFSG.conjugate (ZOf (P : Subgroup X)) g⁻¹ ≤ (P : Subgroup X) := by
      rw [e1]
      exact hB
    have h2 := hweak0 g⁻¹ h1
    rw [e1] at h2
    exact h2
  have h27 : Nat.card (P : Subgroup X) = 27 := hHeis.2.1
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥(P : Subgroup X)) 3 (n := 2)
    (by rw [h27]; norm_num)
  set E : Subgroup X := K.map (P : Subgroup X).subtype with hEdef
  have hE9 : Nat.card E = 9 := by
    rw [hEdef, Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hK]
    norm_num
  have hEP : E ≤ (P : Subgroup X) := Subgroup.map_subtype_le K
  have hnle : ¬ E ≤ ZOf (P : Subgroup X) := fun h => by
    have := Subgroup.card_le_of_le h
    rw [hE9, hZ3] at this
    omega
  obtain ⟨a, haE, haZ⟩ := Set.not_subset.mp hnle
  have haP : a ∈ (P : Subgroup X) := hEP haE
  have ha1 : a ≠ 1 := fun h => haZ (h ▸ one_mem _)
  have ha3 : a ^ 3 = 1 := by
    have h := Monoid.pow_exponent_eq_one (⟨a, haP⟩ : ↥(P : Subgroup X))
    rw [hHeis.2.2] at h
    exact congrArg Subtype.val h
  have hao : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  have hAP : zpowers a ≤ (P : Subgroup X) := Subgroup.zpowers_le.mpr haP
  have hA3 : Nat.card (zpowers a) = 3 := by rw [Nat.card_zpowers, hao]
  have hAnot : zpowers a ∉ MConjSet (⊤ : Subgroup X) (ZOf (P : Subgroup X)) := fun h =>
    haZ ((hweak' _ hAP h) ▸ mem_zpowers a)
  have hAZ : zpowers a ≠ ZOf (P : Subgroup X) := fun h => haZ (h ▸ mem_zpowers a)
  have hclass : ∀ B : Subgroup X, Nat.card B = 3 →
      B ∈ MConjSet (⊤ : Subgroup X) (ZOf (P : Subgroup X)) ∨
        B ∈ MConjSet (⊤ : Subgroup X) (zpowers a) := by
    intro B hB3
    have hBp : IsPGroup 3 B := IsPGroup.of_card (n := 1) (by rw [hB3, pow_one])
    obtain ⟨g, hg⟩ := l2cr_exists_map_conj_le_sylow P hBp
    have hB₁3 : Nat.card (B.map (MulAut.conj g).toMonoidHom) = 3 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hB3]
    have hBback : B = (B.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom := by
      rw [l2cr_map_conj_map_conj, inv_mul_cancel, l2cr_map_conj_one]
    by_cases hB₁Z : B.map (MulAut.conj g).toMonoidHom = ZOf (P : Subgroup X)
    · left
      exact ⟨g⁻¹, mem_top _, by rw [hBback, hB₁Z]⟩
    · right
      obtain ⟨h, hh⟩ := j2ThreeClasses_nonCentral_conj hX hS hAP hg hA3 hB₁3 hAZ hB₁Z
      exact ⟨g⁻¹ * h, mem_top _, by rw [hBback, hh, l2cr_map_conj_map_conj]⟩
  have hnormA : Nat.card (normalizer ((zpowers a : Subgroup X) : Set X)) = 72 := by
    obtain ⟨-, ⟨e⟩, -⟩ := h4 E ⟨hEP, hE9⟩ a haE haZ
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_eq_fintype_card (α := Equiv.Perm (Fin 3)),
      Fintype.card_perm, Fintype.card_fin,
      CFSG.Alternating.Multipliers.nat_card_alternatingGroup_fin 2]
    norm_num [Nat.factorial]
  have hnormZ : 360 ≤ Nat.card (normalizer ((ZOf (P : Subgroup X) : Subgroup X) : Set X)) := by
    obtain ⟨N, hN, -, ⟨eQ⟩⟩ := hext0
    have h1 : Nat.card (↥(centralizer ((ZOf (P : Subgroup X) : Subgroup X) : Set X)) ⧸ N) =
        360 := by
      rw [Nat.card_congr eQ.toEquiv]
      exact CFSG.RankThree.PartTwo.KFacts.KS14.card_alternatingGroup_six
    have h2 := Nat.card_le_card_of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
    have h3 := Subgroup.card_le_of_le
      (Subgroup.centralizer_le_normalizer ((ZOf (P : Subgroup X) : Subgroup X) : Set X))
    omega
  refine ⟨hZ3, ⟨zpowers a, hAP, hA3, hAnot, hclass⟩, ?_, hweak'⟩
  intro α
  rcases hclass ((ZOf (P : Subgroup X)).map α.toMonoidHom)
    (by rw [Subgroup.card_map_of_injective α.injective, hZ3]) with h | ⟨g, -, hg⟩
  · exact h
  · exfalso
    have e1 : Nat.card (normalizer (((ZOf (P : Subgroup X)).map α.toMonoidHom : Subgroup X) :
        Set X)) = Nat.card (normalizer ((ZOf (P : Subgroup X) : Subgroup X) : Set X)) := by
      rw [← map_equiv_normalizer_eq (ZOf (P : Subgroup X)) α,
        Subgroup.card_map_of_injective α.injective]
    have e2 : Nat.card (normalizer (((zpowers a).map (MulAut.conj g).toMonoidHom : Subgroup X) :
        Set X)) = Nat.card (normalizer ((zpowers a : Subgroup X) : Set X)) := by
      rw [← map_equiv_normalizer_eq (zpowers a) (MulAut.conj g),
        Subgroup.card_map_of_injective (MulAut.conj g).injective]
    rw [hg] at e1
    omega

theorem l2pri_pRank_le_one_of_order {X : Type} [Group X] [Finite X] {N q : ℕ} {S : Finset ℕ}
    (hN : Nat.card X = N) (hN0 : N ≠ 0) (hS : N.primeFactors = S)
    (hsq : ∀ r ∈ S, 5 ≤ r → r ≠ q → ¬ r ^ 2 ∣ N) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ≠ q) : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 1 := by
  refine CFSG.GroupTheory.pRank_le_of_not_dvd_pow_succ hp ?_
  rw [Subgroup.card_top, hN]
  intro hdvd
  have hdvd' : p ^ 2 ∣ N := by simpa using hdvd
  have hmem : p ∈ N.primeFactors :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p two_ne_zero).trans hdvd', hN0⟩
  rw [hS] at hmem
  exact hsq p hmem hp5 hpq hdvd'

theorem l2pri_spor {X : Type} [Group X] [Finite X] {N q : ℕ} {S : Finset ℕ}
    (hN : Nat.card X = N) (hN0 : N ≠ 0) (hS : N.primeFactors = S)
    (hsq : ∀ r ∈ S, 5 ≤ r → r ≠ q → ¬ r ^ 2 ∣ N)
    (hle : CFSG.Open.pRank q (⊤ : Subgroup X) ≤ 2) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpr : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X)) :
    p = q ∧ CFSG.Open.pRank p (⊤ : Subgroup X) = 2 := by
  by_cases hpq : p = q
  · subst hpq
    exact ⟨rfl, le_antisymm hle hpr⟩
  · have := l2pri_pRank_le_one_of_order hN hN0 hS hsq hp hp5 hpq
    omega

theorem l2pri_pRank_le_two_of_cubic {M : Type} [Group M] [Finite M] {p : ℕ} (hp : p.Prime)
    (hord : ¬ p ^ 4 ∣ Nat.card M) {x y : M} (hxy : ¬ Commute x y)
    (hcard : Nat.card (Subgroup.closure ({x, y} : Set M)) = p ^ 3) :
    CFSG.Open.pRank p (⊤ : Subgroup M) ≤ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra hlt
  have h3 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup M) := by omega
  have hsyl : ∀ (R : Sylow p M) (F : Subgroup M), F ≤ (R : Subgroup M) → Nat.card F = p ^ 3 →
      F = (R : Subgroup M) := by
    intro R F hFR hF
    obtain ⟨m, hm⟩ := IsPGroup.exists_card_eq (G := ↥(R : Subgroup M)) R.isPGroup'
    have h1 : p ^ 3 ∣ p ^ m := by
      rw [← hm, ← hF]
      exact Subgroup.card_dvd_of_le hFR
    have h2 : 3 ≤ m := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp h1
    have h4 : m ≤ 3 := by
      by_contra hm4
      apply hord
      have : p ^ 4 ∣ p ^ m := pow_dvd_pow p (by omega)
      rw [← hm] at this
      exact this.trans (Subgroup.card_subgroup_dvd_card _)
    exact Subgroup.eq_of_le_of_card_ge hFR (by rw [hm, le_antisymm h4 h2, hF])
  obtain ⟨P⟩ : Nonempty (Sylow p M) := inferInstance
  obtain ⟨E, hEP, hE, hEcard⟩ :=
    CFSG.AGLEmbedding.exists_elem_le_sylow_of_le_pRank (p := p) (k := 3) h3 P
  have hEP' : E = (P : Subgroup M) := hsyl P E hEP hEcard
  obtain ⟨Q, hKQ⟩ :=
    (IsPGroup.of_card hcard : IsPGroup p (Subgroup.closure ({x, y} : Set M))).exists_le_sylow
  have hKQ' : Subgroup.closure ({x, y} : Set M) = (Q : Subgroup M) := hsyl Q _ hKQ hcard
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M Q P
  have hmap : (Q : Subgroup M).map (MulAut.conj g).toMonoidHom = (P : Subgroup M) := by
    rw [← CFSG.RankThree.PartTwo.Sec14.coe_sylow_smul_eq_map, hg]
  have hxQ : x ∈ (Q : Subgroup M) := by
    rw [← hKQ']
    exact Subgroup.subset_closure (by simp)
  have hyQ : y ∈ (Q : Subgroup M) := by
    rw [← hKQ']
    exact Subgroup.subset_closure (by simp)
  have hxE : g * x * g⁻¹ ∈ E := by
    rw [hEP', ← hmap]
    exact ⟨x, hxQ, by simp [MulAut.conj_apply]⟩
  have hyE : g * y * g⁻¹ ∈ E := by
    rw [hEP', ← hmap]
    exact ⟨y, hyQ, by simp [MulAut.conj_apply]⟩
  have h := congrArg Subtype.val
    (hE.1.is_comm.comm ⟨g * x * g⁻¹, hxE⟩ ⟨g * y * g⁻¹, hyE⟩)
  have h2 : g * (x * y) * g⁻¹ = g * (y * x) * g⁻¹ := by
    have e1 : g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
    have e2 : g * (y * x) * g⁻¹ = g * y * g⁻¹ * (g * x * g⁻¹) := by group
    rw [e1, e2]
    exact h
  exact hxy (mul_left_cancel (mul_right_cancel h2))

theorem l2pri_hs_five_le_two
    {X : Type} [Group X] [Finite X] (h : IsSpor X .HS) :
    CFSG.Open.pRank 5 (⊤ : Subgroup X) ≤ 2 := by
  obtain ⟨e⟩ := h
  have : Finite (CFSG.Blueprint.NativeSporadic.Carrier .HS) := Finite.of_equiv X e.toEquiv
  obtain ⟨x, y, -, -, -, hz, -, -, hc, -⟩ := CFSG.SectionRank.HS_sylow5_cubic_witness
  have h2c : CFSG.Open.pRank 5 (⊤ : Subgroup (CFSG.Blueprint.NativeSporadic.Carrier .HS)) ≤ 2 :=
    l2pri_pRank_le_two_of_cubic Nat.prime_five
      (by
        change ¬ 5 ^ 4 ∣ Nat.card CFSG.Blueprint.NativeSporadic.HS
        rw [CFSG.Sporadic.HS.card_HS]
        norm_num)
      (fun hcomm => hz (commutatorElement_eq_one_iff_mul_comm.mpr hcomm.eq)) hc
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 5) (by norm_num) e]
  exact h2c

theorem l2pri_ru_five_le_two
    {X : Type} [Group X] [Finite X] (h : IsSpor X .Ru) :
    CFSG.Open.pRank 5 (⊤ : Subgroup X) ≤ 2 := by
  obtain ⟨e⟩ := h
  have : Finite (CFSG.Blueprint.NativeSporadic.Carrier .Ru) := Finite.of_equiv X e.toEquiv
  obtain ⟨x, y, -, -, -, hz, -, -, hc, -⟩ := CFSG.SectionRank.Ru_sylow5_cubic_witness
  have h2c : CFSG.Open.pRank 5 (⊤ : Subgroup (CFSG.Blueprint.NativeSporadic.Carrier .Ru)) ≤ 2 :=
    l2pri_pRank_le_two_of_cubic Nat.prime_five
      (by
        change ¬ 5 ^ 4 ∣ Nat.card CFSG.Blueprint.NativeSporadic.Ru
        rw [CFSG.Sporadic.Ru.card_Ru]
        norm_num)
      (fun hcomm => hz (commutatorElement_eq_one_iff_mul_comm.mpr hcomm.eq)) hc
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 5) (by norm_num) e]
  exact h2c

theorem l2pri_j4_eleven_le_two
    {X : Type} [Group X] [Finite X] (h : IsSpor X .J4) :
    CFSG.Open.pRank 11 (⊤ : Subgroup X) ≤ 2 := by
  obtain ⟨e⟩ := h
  have : Finite (CFSG.Blueprint.NativeSporadic.Carrier .J4) := Finite.of_equiv X e.toEquiv
  obtain ⟨x, y, -, -, -, hz, -, -, hc, -⟩ := CFSG.SectionRank.J4_sylow11_cubic_witness
  have h2c : CFSG.Open.pRank 11 (⊤ : Subgroup (CFSG.Blueprint.NativeSporadic.Carrier .J4)) ≤ 2 :=
    l2pri_pRank_le_two_of_cubic (by norm_num)
      (by
        change ¬ 11 ^ 4 ∣ Nat.card CFSG.Blueprint.NativeSporadic.J4
        rw [CFSG.Sporadic.J4.card_J4]
        norm_num)
      (fun hcomm => hz (commutatorElement_eq_one_iff_mul_comm.mpr hcomm.eq)) hc
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 11) (by norm_num) e]
  exact h2c

theorem l2pri_hs
    {X : Type} [Group X] [Finite X] (h : IsSpor X .HS) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpr : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X)) :
    p = 5 ∧ CFSG.Open.pRank p (⊤ : Subgroup X) = 2 := by
  have hcard : Nat.card X = 44352000 := by
    obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.HS.card_HS
  exact l2pri_spor (N := 44352000) (q := 5) (S := {2, 3, 5, 7, 11}) hcard (by norm_num)
    (by decide +kernel) (by decide +kernel) (l2pri_hs_five_le_two h) hp hp5 hpr

theorem l2pri_ru
    {X : Type} [Group X] [Finite X] (h : IsSpor X .Ru) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpr : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X)) :
    p = 5 ∧ CFSG.Open.pRank p (⊤ : Subgroup X) = 2 := by
  have hcard : Nat.card X = 145926144000 := by
    obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Ru.card_Ru
  exact l2pri_spor (N := 145926144000) (q := 5) (S := {2, 3, 5, 7, 13, 29}) hcard (by norm_num)
    (by decide +kernel) (by decide +kernel) (l2pri_ru_five_le_two h) hp hp5 hpr

theorem l2pri_j4
    {X : Type} [Group X] [Finite X] (h : IsSpor X .J4) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpr : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X)) :
    p = 11 ∧ CFSG.Open.pRank p (⊤ : Subgroup X) = 2 := by
  have hcard : Nat.card X = 86775571046077562880 := by
    obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.J4.card_J4
  exact l2pri_spor (N := 86775571046077562880) (q := 11)
    (S := {2, 3, 5, 7, 11, 23, 29, 31, 37, 43}) hcard (by norm_num)
    (by decide +kernel) (by decide +kernel) (l2pri_j4_eleven_le_two h) hp hp5 hpr

theorem l2pri_not_cover {X : Type} [Group X] [Finite X]
    (h : IsA6Z3 X ∨ IsA7Z3 X ∨ IsM22Z3 X) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 1 := by
  rcases h with ⟨-, hc, ha⟩ | ⟨-, hc, ha⟩ | ⟨-, hc, ha⟩
  · have hq : Nat.card (X ⧸ center X) = 360 := by
      have := CFSG.LocalAnalysis.UniquenessCase.UC6.N588.card_of_isAlt (by norm_num) ha
      rw [this]
      norm_num [Nat.factorial]
    have hX : Nat.card X = 1080 := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center X), hq, hc]
    exact l2pri_pRank_le_one_of_order (N := 1080) (q := 1) (S := {2, 3, 5}) hX (by norm_num)
      (by decide +kernel) (by decide +kernel) hp hp5 hp.ne_one
  · have hq : Nat.card (X ⧸ center X) = 2520 := by
      have := CFSG.LocalAnalysis.UniquenessCase.UC6.N588.card_of_isAlt (by norm_num) ha
      rw [this]
      norm_num [Nat.factorial]
    have hX : Nat.card X = 7560 := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center X), hq, hc]
    exact l2pri_pRank_le_one_of_order (N := 7560) (q := 1) (S := {2, 3, 5, 7}) hX (by norm_num)
      (by decide +kernel) (by decide +kernel) hp hp5 hp.ne_one
  · have hq : Nat.card (X ⧸ center X) = 443520 := by
      obtain ⟨e⟩ := ha
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.Mathieu.card_M22
    have hX : Nat.card X = 1330560 := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center X), hq, hc]
    exact l2pri_pRank_le_one_of_order (N := 1330560) (q := 1) (S := {2, 3, 5, 7, 11}) hX
      (by norm_num) (by decide +kernel) (by decide +kernel) hp hp5 hp.ne_one

theorem l2pri_mathieu
    {X : Type} [Group X] [Finite X] (h : IsMathieu X) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 1 := by
  rcases h with h | h | h | h | h
  · obtain ⟨e⟩ := h
    exact l2pri_pRank_le_one_of_order (N := 7920) (q := 1) (S := {2, 3, 5, 11})
      (by rw [Nat.card_congr e.toEquiv]; exact CFSG.Sporadic.Mathieu.card_M11) (by norm_num)
      (by decide +kernel) (by decide +kernel) hp hp5 hp.ne_one
  · obtain ⟨e⟩ := h
    exact l2pri_pRank_le_one_of_order (N := 95040) (q := 1) (S := {2, 3, 5, 11})
      (by rw [Nat.card_congr e.toEquiv]; exact CFSG.Sporadic.Mathieu.card_M12) (by norm_num)
      (by decide +kernel) (by decide +kernel) hp hp5 hp.ne_one
  · obtain ⟨e⟩ := h
    exact l2pri_pRank_le_one_of_order (N := 443520) (q := 1) (S := {2, 3, 5, 7, 11})
      (by rw [Nat.card_congr e.toEquiv]; exact CFSG.Sporadic.Mathieu.card_M22) (by norm_num)
      (by decide +kernel) (by decide +kernel) hp hp5 hp.ne_one
  · obtain ⟨e⟩ := h
    exact l2pri_pRank_le_one_of_order (N := 10200960) (q := 1) (S := {2, 3, 5, 7, 11, 23})
      (by rw [Nat.card_congr e.toEquiv]; exact CFSG.RankThree.PartOne.CTP.card_M23)
      (by norm_num) (by decide +kernel) (by decide +kernel) hp hp5 hp.ne_one
  · obtain ⟨e⟩ := h
    exact l2pri_pRank_le_one_of_order (N := 244823040) (q := 1) (S := {2, 3, 5, 7, 11, 23})
      (by rw [Nat.card_congr e.toEquiv]; exact CFSG.Sporadic.Mathieu.card_M24) (by norm_num)
      (by decide +kernel) (by decide +kernel) hp hp5 hp.ne_one

theorem l2pri_alt {X : Type} [Group X] [Finite X] {n : ℕ} (hn : n = 6 ∨ n = 7 ∨ n = 8)
    (h : IsAlt X n) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 1 := by
  have hc := CFSG.LocalAnalysis.UniquenessCase.UC6.N588.card_of_isAlt (by omega) h
  rcases hn with rfl | rfl | rfl
  · exact l2pri_pRank_le_one_of_order (N := 360) (q := 1) (S := {2, 3, 5})
      (by rw [hc]; norm_num [Nat.factorial]) (by norm_num) (by decide +kernel)
      (by decide +kernel) hp hp5 hp.ne_one
  · exact l2pri_pRank_le_one_of_order (N := 2520) (q := 1) (S := {2, 3, 5, 7})
      (by rw [hc]; norm_num [Nat.factorial]) (by norm_num) (by decide +kernel)
      (by decide +kernel) hp hp5 hp.ne_one
  · exact l2pri_pRank_le_one_of_order (N := 20160) (q := 1) (S := {2, 3, 5, 7})
      (by rw [hc]; norm_num [Nat.factorial]) (by norm_num) (by decide +kernel)
      (by decide +kernel) hp hp5 hp.ne_one

theorem l2pri_psl52 {X : Type} [Group X] [Finite X] (h : LieModel X .PSL 5 2 1) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 1 :=
  l2pri_pRank_le_one_of_order (N := 9999360) (q := 1) (S := {2, 3, 5, 7, 31})
    (CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_five_two
      (LieModel.statedClassicalModel h (by decide)))
    (by norm_num) (by decide +kernel) (by decide +kernel) hp hp5 hp.ne_one

theorem l2pri_psl33 {X : Type} [Group X] [Finite X] (h : LieModel X .PSL 3 3 1) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 1 :=
  l2pri_pRank_le_one_of_order (N := 5616) (q := 1) (S := {2, 3, 13})
    (CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_three
      (LieModel.statedClassicalModel h (by decide)))
    (by norm_num) (by decide +kernel) (by decide +kernel) hp hp5 hp.ne_one

theorem l2pri_psu33 {X : Type} [Group X] [Finite X] (h : LieModel X .PSU 3 3 1) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 1 :=
  l2pri_pRank_le_one_of_order (N := 6048) (q := 1) (S := {2, 3, 7})
    (CFSG.Blueprint.LieModel.card_psu_three_three h) (by norm_num) (by decide +kernel)
    (by decide +kernel) hp hp5 hp.ne_one

theorem l2pri_sp4 {X : Type} [Group X] [Finite X] {n : ℕ} (hX : IsSp4 X n) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpr : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X)) :
    1 < n ∧ 2 ^ (2 * n) ≡ 1 [MOD p] ∧ CFSG.Open.pRank p (⊤ : Subgroup X) = 2 := by
  have hp2 : p ≠ 2 := by omega
  have hn : 2 ≤ n := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22a_two_le_of_isSp4 hX
  refine ⟨hn, ?_, le_antisymm
    (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p218d_pRank_le_two_sp4 hX hp hp2) hpr⟩
  have hd : p ∣ (2 ^ n) ^ 2 - 1 := by
    by_contra hnd
    have := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22s218p_pRank_le_one_sp4 hX hp hp2 hnd
    omega
  have h1 : 1 ≤ 2 ^ (2 * n) := Nat.one_le_two_pow
  have h2 : (2 ^ n) ^ 2 = 2 ^ (2 * n) := by rw [← pow_mul, mul_comm]
  rw [h2] at hd
  exact ((Nat.modEq_iff_dvd' h1).2 hd).symm

theorem l2pri_g2
    {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 2 ≤ n) (hX : IsG2 X n) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpr : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X)) :
    2 ^ (2 * n) ≡ 1 [MOD p] ∧ CFSG.Open.pRank p (⊤ : Subgroup X) = 2 := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18.exists_adjoint_of_isG2 hX
  let := hKf
  let := hKfin
  have : Fintype K := Fintype.ofFinite K
  have hKcard' : Fintype.card K = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact hKcard
  have hrank := CFSG.LocalAnalysis.RankThreeUC.S15.pRank_adjointG2_eq K hKcard' hn hp hp2
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e, hrank, hKcard'] at hpr ⊢
  have hES : CFSG.LocalAnalysis.RankThreeUC.S15.eS (2 ^ n) p = 1 := by
    by_contra hne
    unfold CFSG.LocalAnalysis.RankThreeUC.S15.rkG2 at hpr
    split_ifs at hpr <;> omega
  have hdvd := (CFSG.LocalAnalysis.RankThreeUC.S15.eS_eq_one_iff Nat.one_le_two_pow).1 hES
  refine ⟨?_, CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20v_rkG2_of_eS hES⟩
  have h1 : 1 ≤ 2 ^ (2 * n) := Nat.one_le_two_pow
  have h2 : (2 ^ n) ^ 2 = 2 ^ (2 * n) := by rw [← pow_mul, mul_comm]
  rw [h2] at hdvd
  exact ((Nat.modEq_iff_dvd' h1).2 hdvd).symm

theorem l2pri_su5 (hGA : CFSG.Open.GriessAllModelsStatement) {X : Type} [Group X] [Finite X]
    {n : ℕ} (hX : IsSU5 X n) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpr : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X)) :
    p ∣ 2 ^ n + 1 ∨ (2 ^ n ≡ 1 [MOD p] ∧ CFSG.Open.pRank p (⊤ : Subgroup X) = 2) := by
  by_cases hd : p ∣ 2 ^ n + 1
  · exact Or.inl hd
  right
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨hq, hU⟩ := hX
  have hmod : CFSG.Open.StatedClassicalModel (X ⧸ Subgroup.center X) .PSU 5 2 n :=
    LieModel.statedClassicalModel hU (by decide)
  have hdvd := CFSG.RankThree.PartOne.card_center_dvd_of_model hGA hq hmod
  have hgen : CFSG.Blueprint.Multiplier.genericOrders .PSU 5 2 n =
      (Nat.gcd 5 (2 ^ n + 1), 1) := rfl
  have hexc : CFSG.Blueprint.Multiplier.exceptionalOrders .PSU 5 2 n = (1, 1) := by
    unfold CFSG.Blueprint.Multiplier.exceptionalOrders
    simp
  rw [hgen, hexc] at hdvd
  have hdvd' : Nat.card (Subgroup.center X) ∣ Nat.gcd 5 (2 ^ n + 1) := by simpa using hdvd
  have hZp : ¬ p ∣ Nat.card (Subgroup.center X) := fun h =>
    hd (h.trans (hdvd'.trans (Nat.gcd_dvd_right 5 (2 ^ n + 1))))
  have hqt : CFSG.Open.pRank p (⊤ : Subgroup (X ⧸ Subgroup.center X)) =
      CFSG.Open.pRank p (⊤ : Subgroup X) :=
    CFSG.SectionRank.pRank_quotient_eq (Subgroup.center X) hZp
  rw [← hqt] at hpr ⊢
  rw [CFSG.LocalAnalysis.UniquenessCase.UC22.uc22s218_u5_pRank_eq_div hU hp hp2 hd] at hpr ⊢
  obtain ⟨o, ho⟩ : ∃ o, orderOf (-((2 ^ n : ℕ) : ZMod p)) = o := ⟨_, rfl⟩
  rw [ho] at hpr ⊢
  have ho_pos : 0 < o := by
    rcases Nat.eq_zero_or_pos o with h0 | h0
    · rw [h0] at hpr
      simp at hpr
    · exact h0
  have ho_le : o ≤ 2 := by
    by_contra hlt
    have h3 : 3 ≤ o := by omega
    have := Nat.div_le_div_left (a := 5) h3 (by norm_num : 0 < 3)
    omega
  have ho_ne1 : o ≠ 1 := by
    intro h1o
    have h1 : -((2 ^ n : ℕ) : ZMod p) = 1 := orderOf_eq_one_iff.mp (ho.trans h1o)
    apply hd
    have h0 : (((2 ^ n + 1 : ℕ)) : ZMod p) = 0 := by
      rw [Nat.cast_add, Nat.cast_one]
      linear_combination -h1
    exact (ZMod.natCast_eq_zero_iff _ _).1 h0
  have ho2 : o = 2 := by omega
  have hsq : (-((2 ^ n : ℕ) : ZMod p)) ^ 2 = 1 := by
    have := pow_orderOf_eq_one (-((2 ^ n : ℕ) : ZMod p))
    rwa [ho, ho2] at this
  have hfac : (-((2 ^ n : ℕ) : ZMod p) - 1) * (-((2 ^ n : ℕ) : ZMod p) + 1) = 0 := by
    linear_combination hsq
  rcases mul_eq_zero.mp hfac with h1 | h1
  · exfalso
    have : -((2 ^ n : ℕ) : ZMod p) = 1 := by linear_combination h1
    have := orderOf_eq_one_iff.mpr this
    omega
  · refine ⟨?_, by rw [ho2]⟩
    have h2 : ((2 ^ n : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
      rw [Nat.cast_one]
      linear_combination -h1
    exact (ZMod.natCast_eq_natCast_iff _ _ _).1 h2

theorem list880PRankInspection_holds :
    List880PRankInspection := by
  have hGA : CFSG.Open.GriessAllModelsStatement :=
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  intro X _ _ hX p hp hp5 hpr
  have hnc : ¬ (IsA6Z3 X ∨ IsA7Z3 X ∨ IsM22Z3 X) := fun h => by
    have := l2pri_not_cover h hp hp5
    omega
  refine ⟨hnc, ?_⟩
  unfold List880 at hX
  rcases hX with hM | hJ2 | hHS | hRu | hJ4 | h6 | h7 | h22 | hA6 | hA7 | hA8 | hL5 | hL3 |
    ⟨n, hsp⟩ | ⟨n, hg⟩ | ⟨m, -, hsu⟩ | hsuf
  · have := l2pri_mathieu hM hp hp5
    omega
  · obtain ⟨h5, hne⟩ := j2FivePRank_holds X hJ2
    have hp5' : p = 5 := by
      by_contra hne'
      have := hne p hp hp5 hne'
      omega
    subst hp5'
    exact Or.inl ⟨Or.inl hJ2, rfl, h5⟩
  · obtain ⟨hp5', hr⟩ := l2pri_hs hHS hp hp5 hpr
    exact Or.inl ⟨Or.inr (Or.inl hHS), hp5', hr⟩
  · obtain ⟨hp5', hr⟩ := l2pri_ru hRu hp hp5 hpr
    exact Or.inl ⟨Or.inr (Or.inr hRu), hp5', hr⟩
  · obtain ⟨hp11, hr⟩ := l2pri_j4 hJ4 hp hp5 hpr
    exact Or.inr (Or.inl ⟨hJ4, hp11, hr⟩)
  · exact absurd (Or.inl h6) hnc
  · exact absurd (Or.inr (Or.inl h7)) hnc
  · exact absurd (Or.inr (Or.inr h22)) hnc
  · have := l2pri_alt (Or.inl rfl) hA6 hp hp5
    omega
  · have := l2pri_alt (Or.inr (Or.inl rfl)) hA7 hp hp5
    omega
  · have := l2pri_alt (Or.inr (Or.inr rfl)) hA8 hp hp5
    omega
  · have := l2pri_psl52 hL5 hp hp5
    omega
  · have := l2pri_psl33 hL3 hp hp5
    omega
  · obtain ⟨hn, hc, hr⟩ := l2pri_sp4 hsp hp hp5 hpr
    exact Or.inr (Or.inr (Or.inl ⟨n, hn, Or.inl hsp, hc, hr⟩))
  · rcases hg with ⟨-, hu⟩ | ⟨hn2, hg2⟩
    · have := l2pri_psu33 hu hp hp5
      omega
    · obtain ⟨hc, hr⟩ := l2pri_g2 hn2 hg2 hp hp5 hpr
      exact Or.inr (Or.inr (Or.inl ⟨n, hn2, Or.inr hg2, hc, hr⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨m, hsu, l2pri_su5 hGA hsu hp hp5 hpr⟩))
  · obtain ⟨hsu2, -⟩ := hsuf
    exact Or.inr (Or.inr (Or.inr ⟨2, hsu2, l2pri_su5 hGA hsu2 hp hp5 hpr⟩))

theorem l2cr_pRank_pos {H : Type} [Group H] [Finite H] {p : ℕ} (hp : p.Prime) {C : Subgroup H}
    {z : H} (hz : orderOf z = p) (hzC : z ∈ C) : 0 < CFSG.Open.pRank p C := by
  have hz' : z ^ p = 1 := by
    rw [← hz]
    exact pow_orderOf_eq_one z
  have hE := isElemAbelian_zpowers (p := p) hz'
  have hcard : Nat.card (Subgroup.zpowers z) = p ^ 1 := by
    rw [Nat.card_zpowers, hz, pow_one]
  exact CFSG.SectionRank.le_pRank hp.one_lt (Subgroup.zpowers_le.mpr hzC) hE hcard

theorem l2cr_pRank_two {H : Type} [Group H] [Finite H] {p : ℕ} (hp : p.Prime) {C : Subgroup H}
    {u v : H} (hu : orderOf u = p) (hv : orderOf v = p) (huv : Commute u v)
    (hvu : v ∉ Subgroup.zpowers u) (huC : u ∈ C) (hvC : v ∈ C) :
    2 ≤ CFSG.Open.pRank p C := by
  obtain ⟨hab, hcard⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.RankOne.elemAbelian_pair hp hu hv hvu huv.eq
  exact CFSG.SectionRank.le_pRank hp.one_lt
    (sup_le (Subgroup.zpowers_le.mpr huC) (Subgroup.zpowers_le.mpr hvC)) hab hcard

theorem l2cr_pRank_map_le {X H : Type} [Group X] [Finite X] [Group H] [Finite H] (ι : X →* H)
    (hinj : Function.Injective ι) {p : ℕ} (hp : p.Prime) {K : Subgroup X} {C : Subgroup H}
    (h : K.map ι ≤ C) : CFSG.Open.pRank p K ≤ CFSG.Open.pRank p C :=
  (CFSG.SectionRank.pRank_le_map hp.one_lt ι hinj K).trans
    (CFSG.SectionRank.pRank_mono hp.one_lt h)

theorem l2cr_lift {X H : Type} [Group X] [Finite X] [Group H] [Finite H] (ι : X →* H)
    (hinj : Function.Injective ι) {p : ℕ} (hp : p.Prime) {S : Subgroup X}
    (hA : 0 < CFSG.Open.pRank p (centralizer (S : Set X)))
    (hB : ∀ e ∈ S, orderOf e = 3 → 2 ≤ CFSG.Open.pRank p (centralizer ({e} : Set X))) :
    0 < CFSG.Open.pRank p (centralizer ((ι '' (S : Set X) : Set H))) ∧
      ∀ e ∈ S, orderOf e = 3 → 2 ≤ CFSG.Open.pRank p (centralizer ({ι e} : Set H)) := by
  refine ⟨lt_of_lt_of_le hA (l2cr_pRank_map_le ι hinj hp ?_), fun e he he3 => ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hy x hx]
  · refine le_trans (hB e he he3) (l2cr_pRank_map_le ι hinj hp ?_)
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ rfl
    have := Subgroup.mem_centralizer_iff.mp hy e rfl
    rw [← map_mul, ← map_mul, this]

theorem l2cr_ranks_of_elements {X H : Type} [Group X] [Finite X] [Group H] [Finite H]
    (ι : X →* H) {p : ℕ} (hp : p.Prime) {S : Subgroup X}
    (hA : ∃ z : H, orderOf z = p ∧ ∀ x ∈ S, Commute z (ι x))
    (hB : ∀ e ∈ S, orderOf e = 3 → ∃ u v : H, orderOf u = p ∧ orderOf v = p ∧ Commute u v ∧
        v ∉ Subgroup.zpowers u ∧ Commute u (ι e) ∧ Commute v (ι e)) :
    0 < CFSG.Open.pRank p (centralizer ((ι '' (S : Set X) : Set H))) ∧
      ∀ e ∈ S, orderOf e = 3 → 2 ≤ CFSG.Open.pRank p (centralizer ({ι e} : Set H)) := by
  obtain ⟨z, hz, hzc⟩ := hA
  refine ⟨l2cr_pRank_pos hp hz ?_, fun e he he3 => ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    exact (hzc x hx).symm.eq
  · obtain ⟨u, v, hu, hv, huv, hvu, hue, hve⟩ := hB e he he3
    exact l2cr_pRank_two hp hu hv huv hvu (Subgroup.mem_centralizer_singleton_iff.mpr hue.eq)
      (Subgroup.mem_centralizer_singleton_iff.mpr hve.eq)

theorem l2cr_not_mem_zpowers {X H : Type} [Group X] [Group H] (ι : X →* H)
    (hinj : Function.Injective ι) (hZ : Subgroup.center X = ⊥) {p : ℕ} (hp : p.Prime) {z : H}
    (hz : orderOf z = p) (hc : ∀ x : X, Commute z (ι x)) (y : X) :
    z ∉ Subgroup.zpowers (ι y) := by
  intro hmem
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hzι : z = ι (y ^ n) := by
    rw [map_zpow]
    exact hn.symm
  have hcen : y ^ n ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply hinj
    rw [map_mul, map_mul, ← hzι]
    exact (hc g).eq.symm
  rw [hZ, Subgroup.mem_bot] at hcen
  rw [hzι, hcen, map_one, orderOf_one] at hz
  exact hp.one_lt.ne hz

theorem l2cr_of_centralizing {X H : Type} [Group X] [Finite X] [Group H] [Finite H] (ι : X →* H)
    (hinj : Function.Injective ι) (hZ : Subgroup.center X = ⊥) {p : ℕ} (hp : p.Prime)
    {S : Subgroup X} (hz : ∃ z : H, orderOf z = p ∧ ∀ x : X, Commute z (ι x))
    (hy : ∀ e ∈ S, orderOf e = 3 → ∃ y : X, orderOf y = p ∧ Commute y e) :
    0 < CFSG.Open.pRank p (centralizer ((ι '' (S : Set X) : Set H))) ∧
      ∀ e ∈ S, orderOf e = 3 → 2 ≤ CFSG.Open.pRank p (centralizer ({ι e} : Set H)) := by
  obtain ⟨z, hzo, hzc⟩ := hz
  refine l2cr_ranks_of_elements ι hp ⟨z, hzo, fun x _ => hzc x⟩ fun e he he3 => ?_
  obtain ⟨y, hyo, hye⟩ := hy e he he3
  refine ⟨ι y, z, ?_, hzo, (hzc y).symm, l2cr_not_mem_zpowers ι hinj hZ hp hzo hzc y,
    hye.map ι, hzc e⟩
  rw [orderOf_injective ι hinj y, hyo]

theorem l2cr_of_outer {X H : Type} [Group X] [Finite X] [Group H] [Finite H] (ι : X →* H)
    (hinj : Function.Injective ι) {p : ℕ} (hp : p.Prime) {S : Subgroup X} {s : H}
    (hs : orderOf s = p) (hsR : s ∉ ι.range) (hsc : ∀ x ∈ S, Commute s (ι x))
    (hy : ∀ e ∈ S, orderOf e = 3 →
      ∃ y : X, orderOf y = p ∧ Commute y e ∧ Commute (ι y) s) :
    0 < CFSG.Open.pRank p (centralizer ((ι '' (S : Set X) : Set H))) ∧
      ∀ e ∈ S, orderOf e = 3 → 2 ≤ CFSG.Open.pRank p (centralizer ({ι e} : Set H)) := by
  refine l2cr_ranks_of_elements ι hp ⟨s, hs, hsc⟩ fun e he he3 => ?_
  obtain ⟨y, hyo, hye, hys⟩ := hy e he he3
  refine ⟨ι y, s, ?_, hs, hys, ?_, hye.map ι, hsc e he⟩
  · rw [orderOf_injective ι hinj y, hyo]
  · intro hmem
    have hle : Subgroup.zpowers (ι y) ≤ ι.range :=
      Subgroup.zpowers_le.mpr (MonoidHom.mem_range.mpr ⟨y, rfl⟩)
    exact hsR (hle hmem)

theorem l2cr_exists_action {X H : Type} [Group X] [Group H] (ι : X →* H)
    (hinj : Function.Injective ι) (hN : ι.range.Normal) :
    ∃ φ : H →* MulAut X, ∀ (h : H) (x : X), ι (φ h x) = h * ι x * h⁻¹ := by
  have := hN
  let e : X ≃* ι.range := MonoidHom.ofInjective hinj
  let φ : H →* MulAut X :=
    (MulAut.congr e.symm).toMonoidHom.comp (MulAut.conjNormal (H := ι.range))
  refine ⟨φ, fun h x => ?_⟩
  have h1 : (e (φ h x) : H) = h * (e x : H) * h⁻¹ := by
    have h2 : e (φ h x) = (MulAut.conjNormal (H := ι.range) h) (e x) := by
      show e (e.symm ((MulAut.conjNormal (H := ι.range) h) (e x))) = _
      exact e.apply_symm_apply _
    rw [h2]
    rfl
  exact h1

theorem l2cr_centralizing_of_aut_rank {X H : Type} [Group X] [Finite X] [Group H] [Finite H]
    (ι : X →* H) (hinj : Function.Injective ι) (hN : ι.range.Normal) {p : ℕ} (hp : p.Prime)
    {k : ℕ} (hA : CFSG.Open.pRank p (⊤ : Subgroup (MulAut X)) ≤ k)
    (hH : k + 1 ≤ CFSG.Open.pRank p (⊤ : Subgroup H)) :
    ∃ z : H, orderOf z = p ∧ ∀ x : X, Commute z (ι x) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨φ, hφ⟩ := l2cr_exists_action ι hinj hN
  by_contra hno0
  have hno : ∀ z : H, orderOf z = p → ∃ x : X, ¬ Commute z (ι x) := by
    intro z hz
    by_contra hcon
    exact hno0 ⟨z, hz, fun x => by
      by_contra hx
      exact hcon ⟨x, hx⟩⟩
  have h1 := CFSG.AGLEmbedding.pRank_le_pRank_inf_ker_add_pRank_map hp φ ⊤
  have h2 : CFSG.Open.pRank p ((⊤ : Subgroup H) ⊓ φ.ker) = 0 := by
    by_contra hne
    obtain ⟨E, hEK, hE, hEc⟩ :=
      CFSG.SectionRank.exists_pRank hp.one_lt ((⊤ : Subgroup H) ⊓ φ.ker)
    have hdvd : p ∣ Nat.card E := by
      rw [hEc]
      exact dvd_pow_self p hne
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥E) p hdvd
    have hgo : orderOf (g : H) = p := by rw [Subgroup.orderOf_coe, hg]
    have hgk : φ (g : H) = 1 := (hEK g.2).2
    obtain ⟨x, hx⟩ := hno (g : H) hgo
    apply hx
    have h3 := hφ (g : H) x
    rw [hgk] at h3
    change ι x = _ at h3
    exact (show (g : H) * ι x = ι x * g from by
      calc (g : H) * ι x = (g : H) * ι x * (g : H)⁻¹ * g := by group
        _ = ι x * g := by rw [← h3])
  have h3 : CFSG.Open.pRank p ((⊤ : Subgroup H).map φ) ≤ k :=
    (CFSG.SectionRank.pRank_mono hp.one_lt le_top).trans hA
  have h4 : CFSG.Open.pRank p (⊤ : Subgroup H) =
      CFSG.Open.pRank p ((⊤ : Subgroup H)) := rfl
  omega

theorem l2cr_conj_injective {X : Type} [Group X] (hZ : Subgroup.center X = ⊥) :
    Function.Injective (MulAut.conj : X →* MulAut X) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  have hc : g ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro x
    have h := congrArg (fun f : MulAut X => f x) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    calc x * g = g * x * g⁻¹ * g := by rw [h]
      _ = g * x := by group
  rw [hZ] at hc
  exact hc

theorem l2cr_isPGroup_le_inner {X : Type} [Group X] {p : ℕ} (hp : p.Prime)
    (hout : ¬ p ∣ Nat.card (Outer X)) {E : Subgroup (MulAut X)}
    (hE : IsPGroup p E) : E ≤ Inn X := by
  intro g hg
  obtain ⟨k, hk⟩ := hE ⟨g, hg⟩
  have hgk : g ^ p ^ k = 1 := by
    have := congrArg (fun z : E => (z : MulAut X)) hk
    simpa using this
  have h1 : orderOf (QuotientGroup.mk g : Outer X) ∣ p ^ k :=
    orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hgk, QuotientGroup.mk_one])
  have h2 : orderOf (QuotientGroup.mk g : Outer X) ∣
      Nat.card (Outer X) := orderOf_dvd_natCard _
  have hcop : Nat.Coprime (p ^ k) (Nat.card (Outer X)) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hout)
  have h3 : orderOf (QuotientGroup.mk g : Outer X) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop h1 h2
  exact (QuotientGroup.eq_one_iff g).1 (orderOf_eq_one_iff.1 h3)

theorem l2cr_pRank_aut_le {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hZ : Subgroup.center X = ⊥)
    (hin : ∀ E : Subgroup (MulAut X), IsPGroup p E → E ≤ Inn X) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut X)) ≤ CFSG.Open.pRank p (⊤ : Subgroup X) := by
  have : Finite (MulAut X) := DFunLike.finite _
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨E, -, hE, hEc⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup (MulAut X))
  have hEp : IsPGroup p E := IsPGroup.of_card hEc
  have h1 : CFSG.Open.pRank p (⊤ : Subgroup (MulAut X)) ≤ CFSG.Open.pRank p E :=
    CFSG.SectionRank.le_pRank hp.one_lt le_rfl hE hEc
  have h2 := CFSG.SectionRank.pRank_mono hp.one_lt (hin E hEp)
  have h3 := CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective p hp
    (MulAut.conj : X →* MulAut X) (l2cr_conj_injective hZ) ⊤
  rw [Subgroup.map_top] at h3
  exact h1.trans (h2.trans h3.le)

theorem l2cr_center_bot_hs {X : Type} [Group X] (h : IsSpor X .HS) :
    Subgroup.center X = ⊥ := by
  obtain ⟨e⟩ := h
  have : IsSimpleGroup CFSG.Blueprint.NativeSporadic.HS := CFSG.Sporadic.HS.isSimpleGroup_HS
  have hcard : ¬ (Nat.card CFSG.Blueprint.NativeSporadic.HS).Prime := by
    rw [CFSG.Sporadic.HS.card_HS]
    norm_num
  have hZ : Subgroup.center (CFSG.Blueprint.NativeSporadic.Carrier .HS) = ⊥ := by
    change Subgroup.center CFSG.Blueprint.NativeSporadic.HS = ⊥
    exact center_eq_bot_of_isSimpleGroup_of_not_prime_card hcard
  exact CFSG.ABGLocalTools.center_eq_bot_of_mulEquiv e hZ

theorem l2cr_center_bot_ru {X : Type} [Group X] (h : IsSpor X .Ru) :
    Subgroup.center X = ⊥ := by
  obtain ⟨e⟩ := h
  have : IsSimpleGroup CFSG.Blueprint.NativeSporadic.Ru := CFSG.Sporadic.Ru.isSimpleGroup_Ru
  have hcard : ¬ (Nat.card CFSG.Blueprint.NativeSporadic.Ru).Prime := by
    rw [CFSG.Sporadic.Ru.card_Ru]
    norm_num
  have hZ : Subgroup.center (CFSG.Blueprint.NativeSporadic.Carrier .Ru) = ⊥ := by
    change Subgroup.center CFSG.Blueprint.NativeSporadic.Ru = ⊥
    exact center_eq_bot_of_isSimpleGroup_of_not_prime_card hcard
  exact CFSG.ABGLocalTools.center_eq_bot_of_mulEquiv e hZ

theorem l2cr_center_bot_j4 {X : Type} [Group X] (h : IsSpor X .J4) :
    Subgroup.center X = ⊥ := by
  obtain ⟨e⟩ := h
  have : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J4 := CFSG.Sporadic.J4.isSimpleGroup_J4
  have hcard : ¬ (Nat.card CFSG.Blueprint.NativeSporadic.J4).Prime := by
    rw [CFSG.Sporadic.J4.card_J4]
    norm_num
  have hZ : Subgroup.center (CFSG.Blueprint.NativeSporadic.Carrier .J4) = ⊥ := by
    change Subgroup.center CFSG.Blueprint.NativeSporadic.J4 = ⊥
    exact center_eq_bot_of_isSimpleGroup_of_not_prime_card hcard
  exact CFSG.ABGLocalTools.center_eq_bot_of_mulEquiv e hZ

theorem l2cr_aut_inner_hs
    {X : Type} [Group X] [Finite X] (h : IsSpor X .HS) :
    ∀ E : Subgroup (MulAut X), IsPGroup 5 E → E ≤ Inn X := by
  obtain ⟨e⟩ := h
  have hle : Nat.card (Outer CFSG.Blueprint.NativeSporadic.HS) ≤ 2 :=
    CFSG.Sporadic.Schreier.HS_outer_card_le_two.1
  have hcard : Nat.card (Outer X) =
      Nat.card (Outer CFSG.Blueprint.NativeSporadic.HS) :=
    Nat.card_congr (outerCongr e).toEquiv
  have : Finite (MulAut X) := DFunLike.finite _
  have : Finite (Outer X) :=
    Finite.of_surjective (QuotientGroup.mk' (Inn X))
      (QuotientGroup.mk'_surjective _)
  have hpos : 0 < Nat.card (Outer X) := Nat.card_pos
  refine fun E hE => l2cr_isPGroup_le_inner Nat.prime_five (fun hd => ?_) hE
  have := Nat.le_of_dvd hpos hd
  omega

theorem l2cr_aut_inner_ru
    {X : Type} [Group X] [Finite X]
    (h : IsSpor X .Ru) :
    ∀ E : Subgroup (MulAut X), IsPGroup 5 E → E ≤ Inn X := by
  obtain ⟨e⟩ := h
  have e' : X ≃* ↥CFSG.Sporadic.RuSchreier.ruP := e.trans CFSG.Sporadic.RuSchreier.ruEquivP
  have hcard : Nat.card (Outer X) = 1 := by
    rw [Nat.card_congr (outerCongr e').toEquiv]
    exact CFSG.Sporadic.RuSchreier.card_outer_ruP
  exact fun E hE => l2cr_isPGroup_le_inner Nat.prime_five (by rw [hcard]; norm_num) hE

theorem l2cr_aut_inner_j4
    {X : Type} [Group X]
    (h : IsSpor X .J4) :
    ∀ E : Subgroup (MulAut X), IsPGroup 11 E → E ≤ Inn X :=
  (CFSG.Sporadic.J4Schreier.R3E_J4_outer_automorphism_group_no_large_primes h).2 11
    (by norm_num) (by norm_num)

theorem l2cr_aut_sporadic
    {X : Type} [Group X] [Finite X] {p : ℕ}
    (hX : (IsSpor X .HS ∧ p = 5) ∨ (IsSpor X .Ru ∧ p = 5) ∨ (IsSpor X .J4 ∧ p = 11)) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut X)) ≤ 2 := by
  rcases hX with ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩
  · exact (l2cr_pRank_aut_le Nat.prime_five (l2cr_center_bot_hs h)
      (l2cr_aut_inner_hs h)).trans (l2pri_hs_five_le_two h)
  · exact (l2cr_pRank_aut_le Nat.prime_five (l2cr_center_bot_ru h)
      (l2cr_aut_inner_ru h)).trans (l2pri_ru_five_le_two h)
  · exact (l2cr_pRank_aut_le (by norm_num) (l2cr_center_bot_j4 h)
      (l2cr_aut_inner_j4 h)).trans (l2pri_j4_eleven_le_two h)

theorem l2cr_exists_commute_of_conj {G : Type} [Group G] {q : ℕ} {a b : G} (g : G)
    (hg : g * b * g⁻¹ = a) (ha : ∃ y : G, orderOf y = q ∧ Commute y a) :
    ∃ y : G, orderOf y = q ∧ Commute y b := by
  obtain ⟨y₀, hy₀o, hy₀c⟩ := ha
  have h2 : (MulAut.conj g⁻¹) y₀ = g⁻¹ * y₀ * g := by simp
  have hb' : (MulAut.conj g⁻¹) a = b := by
    rw [MulAut.conj_apply, ← hg]
    group
  refine ⟨g⁻¹ * y₀ * g, ?_, ?_⟩
  · rw [← h2, MulEquiv.orderOf_eq]
    exact hy₀o
  · have h1 := hy₀c.map (MulAut.conj g⁻¹)
    rw [h2, hb'] at h1
    exact h1

theorem l2cr_three_cent_of_mulEquiv {X Y : Type} [Group X] [Group Y] (ψ : X ≃* Y) {q : ℕ}
    (hY : ∀ b : Y, orderOf b = 3 → ∃ y : Y, orderOf y = q ∧ Commute y b)
    {e : X} (he : orderOf e = 3) : ∃ y : X, orderOf y = q ∧ Commute y e := by
  obtain ⟨y, hyo, hyc⟩ := hY (ψ e) (by rw [MulEquiv.orderOf_eq]; exact he)
  refine ⟨ψ.symm y, by rw [MulEquiv.orderOf_eq]; exact hyo, ?_⟩
  have h := hyc.map ψ.symm
  rwa [MulEquiv.symm_apply_apply] at h

theorem l2cr_exists_of_card {G : Type} [Group G] [Finite G] {a : G} {S : Subgroup G} {q N : ℕ}
    [Fact q.Prime] (hq : q ∣ N)
    (hcard : Nat.card ↥(S ⊓ Subgroup.centralizer ({a} : Set G)) = N) :
    ∃ y : G, y ∈ S ∧ orderOf y = q ∧ Commute y a := by
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(S ⊓ Subgroup.centralizer ({a} : Set G))) q (by rw [hcard]; exact hq)
  obtain ⟨hyS, hyC⟩ := Subgroup.mem_inf.1 y.2
  exact ⟨(y : G), hyS, by rw [Subgroup.orderOf_coe]; exact hy,
    Subgroup.mem_centralizer_singleton_iff.mp hyC⟩

theorem l2cr_three_cent_of_conj_card {G : Type} [Group G] [Finite G] {c : G} {M : Subgroup G}
    {q N : ℕ} [Fact q.Prime] (hq : q ∣ N)
    (hconj : ∀ b : G, b ^ 3 = 1 → b ≠ 1 → ∃ g : G, g * b * g⁻¹ = c)
    (hcard : Nat.card ↥(M ⊓ Subgroup.centralizer ({c} : Set G)) = N)
    (b : G) (hb : orderOf b = 3) : ∃ y : G, orderOf y = q ∧ Commute y b := by
  have hb3 : b ^ 3 = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
  have hb1 : b ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hb
    omega
  obtain ⟨g, hg⟩ := hconj b hb3 hb1
  refine l2cr_exists_commute_of_conj g hg ?_
  obtain ⟨y, -, hyo, hyc⟩ := l2cr_exists_of_card hq hcard
  exact ⟨y, hyo, hyc⟩

theorem l2cr_hs100_three_cent
    (b : CFSG.RankThree.Native.hs100P) (hb : orderOf b = 3) :
    ∃ y : CFSG.RankThree.Native.hs100P, orderOf y = 5 ∧ Commute y b := by
  have hb3 : b ^ 3 = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
  have hb1 : b ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hb
    omega
  obtain ⟨g, hg⟩ := CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.exists_conj_hsXp b hb3 hb1
  refine l2cr_exists_commute_of_conj g hg ?_
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hcard : Nat.card ↥(CFSG.RankThree.Native.hs100P ⊓ Subgroup.centralizer
      ({CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.hsXperm} : Set (Equiv.Perm (Fin 100)))) = 360 := by
    rw [inf_comm, ← CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.closure_hsGs_eq]
    exact CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.hsCent_enum.2.1
  obtain ⟨y, hyS, hyo, hyc⟩ := l2cr_exists_of_card (q := 5) (N := 360) (by norm_num) hcard
  exact ⟨⟨y, hyS⟩, by rw [Subgroup.orderOf_mk]; exact hyo, Subtype.ext hyc.eq⟩

theorem l2cr_three_cent_hs
    {X : Type} [Group X] [Finite X] (h : IsSpor X .HS) {e : X} (he : orderOf e = 3) :
    ∃ y : X, orderOf y = 5 ∧ Commute y e := by
  obtain ⟨φ⟩ := h
  exact l2cr_three_cent_of_mulEquiv (φ.trans CFSG.RankThree.Native.hs100Equiv)
    (fun b hb => l2cr_hs100_three_cent b hb) he

theorem l2cr_three_cent_ru
    {X : Type} [Group X] [Finite X]
    (h : IsSpor X .Ru) {e : X} (he : orderOf e = 3) : ∃ y : X, orderOf y = 5 ∧ Commute y e := by
  have hcard := (CFSG.EvenSporadicStandard.RuStd.S2.ruThreeFacts_of_isSporadic h).card e he
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨y, -, hyo, hyc⟩ := l2cr_exists_of_card (S := ⊤) (a := e) (q := 5) (N := 2160)
    (by norm_num) (by rw [top_inf_eq]; exact hcard)
  exact ⟨y, hyo, hyc⟩

theorem l2cr_three_cent_j4
    {X : Type} [Group X] [Finite X] (h : IsSpor X .J4) {e : X} (he : orderOf e = 3) :
    ∃ y : X, orderOf y = 11 ∧ Commute y e := by
  obtain ⟨φ⟩ := h
  have hF : CFSG.Sporadic.J4.J4Facts := CFSG.Sporadic.J4.j4Facts
  have ψ : X ≃* ↥CFSG.Sporadic.J4.J := φ.trans (CFSG.Sporadic.J4.seedEquiv hF.mat)
  have hfin : Finite ↥CFSG.Sporadic.J4.J := Finite.of_equiv X ψ.toEquiv
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  exact @l2cr_three_cent_of_mulEquiv X ↥CFSG.Sporadic.J4.J _ (Subgroup.toGroup _) ψ 11
    (@l2cr_three_cent_of_conj_card ↥CFSG.Sporadic.J4.J (Subgroup.toGroup _) hfin
      CFSG.Quasithin.J4M2.cE CFSG.Quasithin.J4M2.M2 11 2661120 _ (by norm_num)
      CFSG.AGLEmbeddingD2.Wilson.NormalizerAction.exists_conj_cE_of_orderThree
      (CFSG.AGLEmbeddingD2.Wilson.NormalizerAction.card_centralizer_cE_M2 hF)) e he

theorem l2cr_sporadic
    {X H : Type} [Group X] [Finite X] [Group H] [Finite H]
    (ι : X →* H) (hinj : Function.Injective ι) (hN : ι.range.Normal) {p : ℕ}
    (hX : (IsSpor X .HS ∧ p = 5) ∨ (IsSpor X .Ru ∧ p = 5) ∨ (IsSpor X .J4 ∧ p = 11))
    (hp : p.Prime) (hH : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup H)) (S : Subgroup X) :
    0 < CFSG.Open.pRank p (centralizer ((ι '' (S : Set X) : Set H))) ∧
      ∀ e ∈ S, orderOf e = 3 → 2 ≤ CFSG.Open.pRank p (centralizer ({ι e} : Set H)) := by
  have hZ : Subgroup.center X = ⊥ := by
    rcases hX with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact l2cr_center_bot_hs h
    · exact l2cr_center_bot_ru h
    · exact l2cr_center_bot_j4 h
  refine l2cr_of_centralizing ι hinj hZ hp
    (l2cr_centralizing_of_aut_rank ι hinj hN hp (k := 2) (l2cr_aut_sporadic hX) hH)
    (fun e _ he => ?_)
  rcases hX with ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩
  · exact l2cr_three_cent_hs h he
  · exact l2cr_three_cent_ru h he
  · exact l2cr_three_cent_j4 h he

open scoped Pointwise in
theorem l2cr_fixed_pelement {C : Type} [Group C] [Finite C] {p : ℕ} (hp : p.Prime)
    (hC : p ∣ Nat.card C) (τ : MulAut C) (hτ : τ ^ p = 1) :
    ∃ y : C, orderOf y = p ∧ τ y = y := by
  have : Fact p.Prime := ⟨hp⟩
  classical
  have hstab : ∃ P : Sylow p C, τ • P = P := by
    have : Fintype (Sylow p C) := Fintype.ofFinite _
    let f : Function.End (Sylow p C) := fun P => τ • P
    have hf : f ^ p ^ 1 = 1 := by
      funext P
      rw [pow_one]
      show (fun P : Sylow p C => τ • P)^[p] P = P
      rw [smul_iterate, hτ]
      exact one_smul (MulAut C) P
    have h1 := Equiv.Perm.card_fixedPoints_modEq hf
    have h2 : Nat.card (Sylow p C) ≡ 1 [MOD p] := card_sylow_modEq_one p C
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at h1
    by_contra hne
    have h0 : Nat.card (Function.fixedPoints f) = 0 := by
      rw [Nat.card_eq_zero]
      left
      constructor
      rintro ⟨P, hP⟩
      exact hne ⟨P, hP⟩
    rw [h0] at h1
    have h3 : 1 ≡ 0 [MOD p] := h2.symm.trans h1
    exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.modEq_zero_iff_dvd).1 h3))
  obtain ⟨P, hP⟩ := hstab
  have hmem : ∀ x ∈ (P : Subgroup C), τ x ∈ (P : Subgroup C) := by
    intro x hx
    have h1 : τ x ∈ τ • (P : Subgroup C) :=
      (Subgroup.mem_smul_pointwise_iff_exists _ _ _).2 ⟨x, hx, rfl⟩
    have h2 : ((τ • P : Sylow p C) : Subgroup C) = τ • (P : Subgroup C) := rfl
    rw [← h2, hP] at h1
    exact h1
  have : Fintype (P : Subgroup C) := Fintype.ofFinite _
  let g : Function.End (P : Subgroup C) := fun x => ⟨τ x, hmem x x.2⟩
  have hgpow : ∀ (n : ℕ) (x : (P : Subgroup C)), ((g ^ n) x : C) = (τ ^ n) x := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [pow_succ', pow_succ']
      exact congrArg τ (ih x)
  have hg : g ^ p ^ 1 = 1 := by
    funext x
    apply Subtype.ext
    rw [pow_one, hgpow, hτ]
    rfl
  have h4 := Equiv.Perm.card_fixedPoints_modEq hg
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at h4
  have hPcard : p ∣ Nat.card (P : Subgroup C) := by
    rw [Sylow.card_eq_multiplicity]
    exact dvd_pow_self p ((Nat.Prime.factorization_pos_of_dvd hp Nat.card_pos.ne' hC).ne')
  have h5 : p ∣ Nat.card (Function.fixedPoints g) :=
    (Nat.modEq_zero_iff_dvd).1 (h4.symm.trans ((Nat.modEq_zero_iff_dvd).2 hPcard))
  have hone : (1 : (P : Subgroup C)) ∈ Function.fixedPoints g := Subtype.ext (map_one τ)
  have h6 : 1 < Nat.card (Function.fixedPoints g) := by
    have h7 : 0 < Nat.card (Function.fixedPoints g) :=
      Nat.card_pos_iff.2 ⟨⟨⟨1, hone⟩⟩, inferInstance⟩
    have h8 := Nat.le_of_dvd h7 h5
    have := hp.two_le
    omega
  have : Nontrivial (Function.fixedPoints g) := Finite.one_lt_card_iff_nontrivial.1 h6
  obtain ⟨⟨z, hz⟩, hz1⟩ := exists_ne (⟨1, hone⟩ : Function.fixedPoints g)
  have hzne : (z : C) ≠ 1 := fun h => hz1 (Subtype.ext (Subtype.ext h))
  have hzτ : τ (z : C) = z := congrArg Subtype.val hz
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 P.isPGroup') z
  have hk1 : k ≠ 0 := by
    rintro rfl
    exact hzne (orderOf_eq_one_iff.1 (by rw [Subgroup.orderOf_coe, hk]; simp))
  have hpz : p ∣ orderOf (z : C) := by
    rw [Subgroup.orderOf_coe, hk]
    exact dvd_pow_self p hk1
  have hpz' : p ∣ Nat.card (Subgroup.zpowers (z : C)) := by
    rw [Nat.card_zpowers]
    exact hpz
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.zpowers (z : C)) p hpz'
  refine ⟨(y : C), by rw [Subgroup.orderOf_coe]; exact hy, ?_⟩
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 y.2
  rw [← hm, map_zpow, hzτ]

theorem l2cr_fixed_pelement_sub {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {C : Subgroup X} (hC : p ∣ Nat.card C) (τ : MulAut X) (hτ : τ ^ p = 1)
    (hst : ∀ y ∈ C, τ y ∈ C) : ∃ y ∈ C, orderOf y = p ∧ τ y = y := by
  let f : C →* C := (τ.toMonoidHom.comp C.subtype).codRestrict C (fun x => hst x x.2)
  have hf : Function.Injective f := fun a b h => Subtype.ext (τ.injective (congrArg Subtype.val h))
  let τC : MulAut C := MulEquiv.ofBijective f ⟨hf, Finite.injective_iff_surjective.1 hf⟩
  have hpow : ∀ (n : ℕ) (x : C), ((τC ^ n) x : X) = (τ ^ n) x := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [pow_succ', pow_succ']
      exact congrArg τ (ih x)
  have hτC : τC ^ p = 1 := by
    ext x
    rw [hpow, hτ]
    rfl
  obtain ⟨y, hyo, hyτ⟩ := l2cr_fixed_pelement hp hC τC hτC
  exact ⟨y, y.2, by rw [Subgroup.orderOf_coe]; exact hyo, congrArg Subtype.val hyτ⟩

theorem l2cr_pRank_range_le {X H : Type} [Group X] [Finite X] [Group H] [Finite H]
    (ι : X →* H) (hinj : Function.Injective ι) {p : ℕ} (hp : p.Prime) :
    CFSG.Open.pRank p ι.range ≤ CFSG.Open.pRank p (⊤ : Subgroup X) := by
  have h := CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective p hp ι hinj ⊤
  rw [Subgroup.map_top] at h
  exact h.le

theorem l2cr_outer_element {X H : Type} [Group X] [Finite X] [Group H] [Finite H] (ι : X →* H)
    (hinj : Function.Injective ι) (hZ : Subgroup.center X = ⊥) {p : ℕ} (hp : p.Prime)
    (hX2 : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 2)
    (hH : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup H))
    (hno : ¬ ∃ z : H, orderOf z = p ∧ ∀ x : X, Commute z (ι x)) {φ : H →* MulAut X}
    (hφ : ∀ (h : H) (x : X), ι (φ h x) = h * ι x * h⁻¹) :
    ∃ t : H, orderOf t = p ∧ t ∉ ι.range ∧ orderOf (φ t) = p ∧ φ t ∉ Inn X := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨E, -, hE, hEc⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup H)
  have hEnot : ¬ E ≤ ι.range := by
    intro hle
    have h1 : CFSG.Open.pRank p (⊤ : Subgroup H) ≤ CFSG.Open.pRank p ι.range :=
      CFSG.SectionRank.le_pRank hp.one_lt hle hE hEc
    have h2 := l2cr_pRank_range_le ι hinj hp
    omega
  obtain ⟨t, htE, htR⟩ := Set.not_subset.mp hEnot
  have ht1 : t ≠ 1 := fun h => htR (h ▸ one_mem _)
  have htp : t ^ p = 1 := hE.2 t htE
  have hto : orderOf t = p := orderOf_eq_prime htp ht1
  have hφt : orderOf (φ t) = p := by
    have h1 : (φ t) ^ p = 1 := by rw [← map_pow, htp, map_one]
    refine orderOf_eq_prime h1 fun h => hno ⟨t, hto, fun x => ?_⟩
    have h2 := hφ t x
    rw [h, MulAut.one_apply] at h2
    show t * ι x = ι x * t
    calc t * ι x = t * ι x * t⁻¹ * t := by group
      _ = ι x * t := by rw [← h2]
  refine ⟨t, hto, htR, hφt, ?_⟩
  rintro ⟨a, ha⟩
  have hcomm : ∀ x : X, Commute ((ι a)⁻¹ * t) (ι x) := by
    intro x
    have h2 : ι a * ι x * (ι a)⁻¹ = t * ι x * t⁻¹ := by
      have h1 := hφ t x
      rw [← ha, MulAut.conj_apply, map_mul, map_mul, map_inv] at h1
      exact h1
    show (ι a)⁻¹ * t * ι x = ι x * ((ι a)⁻¹ * t)
    calc (ι a)⁻¹ * t * ι x = (ι a)⁻¹ * (t * ι x * t⁻¹) * t := by group
      _ = (ι a)⁻¹ * (ι a * ι x * (ι a)⁻¹) * t := by rw [h2]
      _ = ι x * ((ι a)⁻¹ * t) := by group
  set s1 : H := (ι a)⁻¹ * t with hs1
  have hts : t = ι a * s1 := by rw [hs1]; group
  have hpow : (ι a) ^ p * s1 ^ p = 1 := by
    rw [← ((hcomm a).symm).mul_pow, ← hts, htp]
  have h3 : a ^ p ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply hinj
    rw [map_mul, map_mul, map_pow, eq_inv_of_mul_eq_one_left hpow]
    exact (((hcomm y).pow_left p).inv_left.eq).symm
  rw [hZ, Subgroup.mem_bot] at h3
  have h5 : (ι a) ^ p = 1 := by rw [← map_pow, h3, map_one]
  have h6 : s1 ^ p = 1 := by rw [h5, one_mul] at hpow; exact hpow
  by_cases hs : s1 = 1
  · apply htR
    rw [hts, hs, mul_one]
    exact ⟨a, rfl⟩
  · exact hno ⟨s1, orderOf_eq_prime h6 hs, hcomm⟩

theorem l2cr_of_fixed {X H : Type} [Group X] [Finite X] [Group H] [Finite H] (ι : X →* H)
    (hinj : Function.Injective ι) (hN : ι.range.Normal) (hZ : Subgroup.center X = ⊥) {p : ℕ}
    (hp : p.Prime) (hX2 : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 2)
    (hH : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup H))
    (hno : ¬ ∃ z : H, orderOf z = p ∧ ∀ x : X, Commute z (ι x)) {S : Subgroup X}
    (hfix : ∀ σ : MulAut X, orderOf σ = p → σ ∉ Inn X →
      ∃ g : X, ∀ x ∈ S, σ (g * x * g⁻¹) = g * x * g⁻¹)
    (hd1 : ∀ e : X, orderOf e = 3 → ∃ y : X, orderOf y = p ∧ Commute y e) :
    ∃ s : H, orderOf s = p ∧ s ∉ ι.range ∧ (∀ x ∈ S, Commute s (ι x)) ∧
      ∀ e ∈ S, orderOf e = 3 → ∃ y : X, orderOf y = p ∧ Commute y e ∧ Commute (ι y) s := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨φ, hφ⟩ := l2cr_exists_action ι hinj hN
  obtain ⟨t, hto, htR, hφo, hφi⟩ := l2cr_outer_element ι hinj hZ hp hX2 hH hno hφ
  obtain ⟨g, hg⟩ := hfix (φ t) hφo hφi
  set s : H := (ι g)⁻¹ * t * ι g with hs
  have hso : orderOf s = p := by
    have hsconj : s = (MulAut.conj (ι g)⁻¹).toMonoidHom t := by
      simp [hs]
    rw [hsconj, orderOf_injective _ (MulAut.conj (ι g)⁻¹).injective, hto]
  have hsR : s ∉ ι.range := by
    rintro ⟨b, hb⟩
    apply htR
    refine ⟨g * b * g⁻¹, ?_⟩
    rw [map_mul, map_mul, map_inv, hb, hs]
    group
  have hsc : ∀ x ∈ S, Commute s (ι x) := by
    intro x hx
    have h2 := hφ t (g * x * g⁻¹)
    rw [hg x hx, map_mul, map_mul, map_inv] at h2
    show s * ι x = ι x * s
    rw [hs]
    calc (ι g)⁻¹ * t * ι g * ι x
        = (ι g)⁻¹ * (t * (ι g * ι x * (ι g)⁻¹) * t⁻¹) * t * ι g := by group
      _ = (ι g)⁻¹ * (ι g * ι x * (ι g)⁻¹) * t * ι g := by rw [← h2]
      _ = ι x * ((ι g)⁻¹ * t * ι g) := by group
  refine ⟨s, hso, hsR, hsc, fun e he he3 => ?_⟩
  set τ : MulAut X := φ s with hτ
  have hτp : τ ^ p = 1 := by rw [hτ, ← map_pow, ← hso, pow_orderOf_eq_one, map_one]
  have hτe : τ e = e := by
    apply hinj
    rw [hτ, hφ s e]
    calc s * ι e * s⁻¹ = ι e * s * s⁻¹ := by rw [(hsc e he).eq]
      _ = ι e := by group
  have hst : ∀ y ∈ Subgroup.centralizer ({e} : Set X),
      τ y ∈ Subgroup.centralizer ({e} : Set X) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    have h1 : τ (y * e) = τ (e * y) := by rw [hy]
    rw [map_mul, map_mul, hτe] at h1
    exact h1
  obtain ⟨y0, hy0o, hy0c⟩ := hd1 e he3
  have hpC : p ∣ Nat.card (Subgroup.centralizer ({e} : Set X)) := by
    have hy0C : y0 ∈ Subgroup.centralizer ({e} : Set X) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hy0c.eq
    have h1 := orderOf_dvd_natCard (⟨y0, hy0C⟩ : Subgroup.centralizer ({e} : Set X))
    rwa [Subgroup.orderOf_mk, hy0o] at h1
  obtain ⟨y, hyC, hyo, hyτ⟩ := l2cr_fixed_pelement_sub hp hpC τ hτp hst
  have hye : Commute y e := Subgroup.mem_centralizer_singleton_iff.mp hyC
  have hys : Commute (ι y) s := by
    have h1 := hφ s y
    rw [← hτ, hyτ] at h1
    show ι y * s = s * ι y
    calc ι y * s = (s * ι y * s⁻¹) * s := by rw [← h1]
      _ = s * ι y := by group
  exact ⟨y, hyo, hye, hys⟩

theorem l2cr_d1_sp4 {X : Type} [Group X] [Finite X] {n : ℕ} (hX : IsSp4 X n) {p : ℕ}
    (hp : p.Prime) (hc : 2 ^ (2 * n) ≡ 1 [MOD p]) {e : X} (he : orderOf e = 3) :
    ∃ y : X, orderOf y = p ∧ Commute y e := by
  obtain ⟨-, K, hfield, hfinite, hK, ⟨φ⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide)
  let := hfield
  let := hfinite
  have : CharP K 2 := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwlie_charP_two hK
  have hn : 2 ≤ n := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22a_two_le_of_isSp4 hX
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  set g : StatedProj (StatedSp 2 K) := φ e with hg
  have hg3 : orderOf g = 3 := by rw [hg, MulEquiv.orderOf_eq, he]
  obtain ⟨ι⟩ :=
    CFSG.RankThree.PartTwo.Sec8.Item84KFacts4.kF84Sp4ThreeCent_holds K hK4 g hg3
  have hS_le : inSubgroup perfectResidual
      (Subgroup.centralizer ({g} : Set (StatedProj (StatedSp 2 K)))) ≤
      Subgroup.centralizer ({g} : Set (StatedProj (StatedSp 2 K))) :=
    Subgroup.map_subtype_le _
  have hcard : Nat.card ↥(inSubgroup perfectResidual
      (Subgroup.centralizer ({g} : Set (StatedProj (StatedSp 2 K)))) ⊓
      Subgroup.centralizer ({g} : Set (StatedProj (StatedSp 2 K)))) =
      Nat.card K * (Nat.card K ^ 2 - 1) := by
    rw [inf_eq_left.mpr hS_le, Nat.card_congr ι.toEquiv,
      CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
  have hpSL : p ∣ Nat.card K * (Nat.card K ^ 2 - 1) := by
    have hd : p ∣ 2 ^ (2 * n) - 1 :=
      (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp hc.symm
    have heq : Nat.card K ^ 2 - 1 = 2 ^ (2 * n) - 1 := by
      rw [hK, ← pow_mul, mul_comm]
    rw [heq]
    exact hd.mul_left _
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, -, hyo, hyc⟩ :=
    l2cr_exists_of_card (S := inSubgroup perfectResidual
      (Subgroup.centralizer ({g} : Set (StatedProj (StatedSp 2 K)))))
      (a := g) (q := p) (N := Nat.card K * (Nat.card K ^ 2 - 1)) hpSL hcard
  refine ⟨φ.symm y, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq]
    exact hyo
  · have h := hyc.map φ.symm
    rwa [hg, MulEquiv.symm_apply_apply] at h

theorem l2cr_d1_g2
    {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 2 ≤ n) (hX : IsG2 X n) {p : ℕ}
    (hp : p.Prime) (hc : 2 ^ (2 * n) ≡ 1 [MOD p]) {e : X} (he : orderOf e = 3) :
    ∃ y : X, orderOf y = p ∧ Commute y e := by
  obtain ⟨K, hKf, hKfin, hKcard, ⟨φ⟩⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18.exists_adjoint_of_isG2 hX
  have hKring : ringChar K ≠ 3 := by
    intro h3
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨m, -, hm⟩ := FiniteField.card (K := K) (ringChar K)
    rw [← Nat.card_eq_fintype_card, hKcard, h3] at hm
    have h3dvd : 3 ∣ 2 ^ n := by
      rw [hm]
      exact dvd_pow_self 3 m.ne_zero
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3dvd
    omega
  have hK4 : 4 ≤ Nat.card K := by
    rw [hKcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have : Fact p.Prime := ⟨hp⟩
  have hfin : Finite (CFSG.Blueprint.Chevalley.adjointGroup .G2 K) :=
    Finite.of_equiv X φ.toEquiv
  have hp1 : p ∣ Nat.card K ^ 2 - 1 := by
    have h1 : p ∣ 2 ^ (2 * n) - 1 := (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp hc.symm
    rw [hKcard, ← pow_mul, mul_comm]
    exact h1
  have hS : ∃ s : ↥(CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.g2ShortSL2 K), orderOf s = p := by
    obtain ⟨eS⟩ := CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.nonempty_mulEquiv_g2ShortSL2 (K := K)
    refine exists_prime_orderOf_dvd_card' p ?_
    rw [← Nat.card_congr eS.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
    exact Dvd.dvd.mul_left hp1 _
  have hM : ∃ m : ↥(CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.g2LongSL2 K), orderOf m = p := by
    obtain ⟨eM⟩ := CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.nonempty_mulEquiv_g2LongSL2 (K := K)
    refine exists_prime_orderOf_dvd_card' p ?_
    rw [← Nat.card_congr eM.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
    exact Dvd.dvd.mul_left hp1 _
  refine l2cr_three_cent_of_mulEquiv φ (fun b hb => ?_) he
  have hb3 : b ^ 3 = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
  have hb1 : b ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hb
    omega
  obtain ⟨g, hg⟩ :=
    CFSG.RankThree.PartTwo.Sec11.KS11Lie7Proof.g2ThreeConjSL2_holds K hKring hK4 b hb3 hb1
  refine l2cr_exists_commute_of_conj g rfl ?_
  rcases hg with hs | hm
  · obtain ⟨m, hmo⟩ := hM
    exact ⟨(m : CFSG.Blueprint.Chevalley.adjointGroup .G2 K),
      by rw [Subgroup.orderOf_coe]; exact hmo,
      (CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.g2Short_commute_g2Long hs m.2).symm⟩
  · obtain ⟨s, hso⟩ := hS
    exact ⟨(s : CFSG.Blueprint.Chevalley.adjointGroup .G2 K),
      by rw [Subgroup.orderOf_coe]; exact hso,
      CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.g2Short_commute_g2Long s.2 hm⟩

private def l2cr_ofs_N (m : ℕ) : ℕ :=
  (2 ^ m) ^ 4 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1))

private theorem l2cr_ofs_N_val (m : ℕ) (hm : m ≠ 0) :
    padicValNat 3 (l2cr_ofs_N m) = 2 + 2 * padicValNat 3 m := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hm2 : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr hm)
  have hm1 : 1 < 2 ^ m := by omega
  have hA : (2 ^ m) ^ 4 ≠ 0 := pow_ne_zero _ (by positivity)
  have hB : (2 ^ m) ^ 2 - 1 ≠ 0 := by
    have : 1 < (2 ^ m) ^ 2 := Nat.one_lt_pow (by norm_num) hm1
    omega
  have hC : (2 ^ m) ^ 4 - 1 ≠ 0 := by
    have : 1 < (2 ^ m) ^ 4 := Nat.one_lt_pow (by norm_num) hm1
    omega
  have hsq : (2 ^ m) ^ 2 = 4 ^ m := by
    rw [← pow_mul, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm m 2]
  have hquad : (2 ^ m) ^ 4 = 16 ^ m := by
    rw [← pow_mul, show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul, mul_comm m 4]
  have hvA : padicValNat 3 ((2 ^ m) ^ 4) = 0 := by
    rw [padicValNat.pow, padicValNat.pow,
      padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 2)]
    ring
  have hLTE4 : padicValNat 3 ((2 ^ m) ^ 2 - 1) = 1 + padicValNat 3 m := by
    rw [hsq]
    have h := padicValNat.pow_sub_pow (p := 3) (by decide : Odd 3) (by norm_num : 1 < 4)
      (by norm_num : 3 ∣ 4 - 1) (by norm_num : ¬ 3 ∣ 4) (n := m) hm
    rwa [one_pow, show 4 - 1 = 3 by norm_num, padicValNat.self (by norm_num : 1 < 3)] at h
  have hLTE16 : padicValNat 3 ((2 ^ m) ^ 4 - 1) = 1 + padicValNat 3 m := by
    rw [hquad]
    have h := padicValNat.pow_sub_pow (p := 3) (by decide : Odd 3) (by norm_num : 1 < 16)
      (by norm_num : 3 ∣ 16 - 1) (by norm_num : ¬ 3 ∣ 16) (n := m) hm
    rw [one_pow, show 16 - 1 = 15 by norm_num, show (15 : ℕ) = 3 * 5 by norm_num,
      padicValNat.mul (by norm_num) (by norm_num),
      padicValNat.self (by norm_num : 1 < 3),
      padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 5), add_zero] at h
    exact h
  rw [l2cr_ofs_N, padicValNat.mul hA (mul_ne_zero hB hC), padicValNat.mul hB hC,
    hvA, hLTE4, hLTE16]
  ring

private theorem l2cr_ofs_padicValNat_div {p n : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hn : n ≠ 0)
    (hdvd : p ∣ n) : padicValNat 3 (n / p) = padicValNat 3 n := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp_le : p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd
  have hnp : n / p ≠ 0 := (Nat.div_pos hp_le hp.pos).ne'
  have h : n / p * p = n := Nat.div_mul_cancel hdvd
  have hp0 : padicValNat 3 p = 0 :=
    padicValNat.eq_zero_of_not_dvd
      (fun h3 => hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3).symm)
  calc padicValNat 3 (n / p)
      = padicValNat 3 (n / p) + padicValNat 3 p := by rw [hp0, add_zero]
    _ = padicValNat 3 (n / p * p) := by rw [padicValNat.mul hnp hp.pos.ne']
    _ = padicValNat 3 n := by rw [h]

private theorem l2cr_ofs_N_factorization {p n : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hn : n ≠ 0)
    (hdvd : p ∣ n) :
    (l2cr_ofs_N n).factorization 3 = (l2cr_ofs_N (n / p)).factorization 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp_le : p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd
  have hnp : n / p ≠ 0 := (Nat.div_pos hp_le hp.pos).ne'
  rw [Nat.factorization_def _ Nat.prime_three, Nat.factorization_def _ Nat.prime_three,
    l2cr_ofs_N_val n hn, l2cr_ofs_N_val (n / p) hnp,
    l2cr_ofs_padicValNat_div hp hp3 hn hdvd]

private theorem l2cr_ofs_card_proj {L : Type} [Field L] [Finite L] {m : ℕ}
    (hL : Nat.card L = 2 ^ m) :
    Nat.card (StatedProj (StatedSp 2 L)) = l2cr_ofs_N m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype L := Fintype.ofFinite L
  have : CharP L 2 := by
    apply charP_of_card_eq_prime_pow (p := 2) (f := m)
    rw [← Nat.card_eq_fintype_card]
    exact hL
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSp_of_charTwo (K := L) 2, hL]
  simp [l2cr_ofs_N, Finset.prod_Icc_succ_top]

theorem l2cr_sp4_outer_fixed
    {X : Type} [Group X] [Finite X] {n : ℕ} (hX : IsSp4 X n) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hc : 2 ^ (2 * n) ≡ 1 [MOD p]) {σ : MulAut X}
    (hσ : orderOf σ = p) (hout : σ ∉ Inn X) {S : Subgroup X} (hS : IsSylowOf 3 S ⊤) :
    ∃ g : X, ∀ x ∈ S, σ (g * x * g⁻¹) = g * x * g⁻¹ := by
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, K, hKf, hKfin, hKcard, ⟨e⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide)
  have : Fintype K := Fintype.ofFinite K
  let he : X ≃* StatedProj (StatedSp 2 K) := e
  have : Finite (StatedProj (StatedSp 2 K)) :=
    Finite.of_injective he.symm he.symm.injective
  have hn : 2 ≤ n := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22a_two_le_of_isSp4 hX
  have hn0 : n ≠ 0 := by omega
  have hf : 1 ≤ n := by omega
  let α : MulAut (StatedProj (StatedSp 2 K)) := MulAut.congr he σ
  have hαord : orderOf α = p :=
    (orderOf_injective (MulAut.congr he).toMonoidHom (MulAut.congr he).injective σ).trans hσ
  have hαp : α ^ p = 1 := by rw [← hαord]; exact pow_orderOf_eq_one α
  have hαinn : α ∉ Inn (StatedProj (StatedSp 2 K)) := by
    intro h
    have hmem : MulAut.congr he σ ∈ (Inn X).map (MulAut.congr he).toMonoidHom := by
      rwa [CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr he]
    obtain ⟨β, hβ, hβeq⟩ := hmem
    have hβσ : β = σ := (MulAut.congr he).injective hβeq
    exact hout (hβσ ▸ hβ)
  obtain ⟨-, -, -, -, -, -, -, hidx, hrel, hdesc⟩ :=
    CFSG.RankThree.Classical.SteinbergBY.symplectic_prime_semilinear_field_descent
      (ℓ := 2) (f := n) (r := 2) Nat.prime_two hf (le_refl 2) hKcard
  have hidx' :
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spSemilinearAutGroup 2 K).index ≤ 2 :=
    Nat.le_of_dvd (by norm_num) hidx
  have hαE : α ∈ CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spSemilinearAutGroup 2 K :=
    CFSG.RankThree.PartOne.OutStructure.mem_of_pow_mem_of_index_le_two _
      hidx' (hp.odd_of_ne_two hp2) (by rw [hαp]; exact Subgroup.one_mem _)
  have hcop : Nat.gcd 2 (2 ^ n - 1) = 1 := by
    have h1 : (2 : ℕ) ^ n % 2 = 0 := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hf
      rw [pow_add]; simp
    have h2 : 1 ≤ (2 : ℕ) ^ n := Nat.one_le_two_pow
    exact Nat.coprime_two_left.mpr (by rw [Nat.odd_iff]; omega)
  have hαD : α ∉ CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spLinearAutGroup 2 K := by
    intro h
    apply hαinn
    have hrel1 : (Inn (StatedProj (StatedSp 2 K))).relIndex
        (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spLinearAutGroup 2 K) = 1 := by
      rw [hcop, Nat.dvd_one] at hrel
      exact hrel
    exact Subgroup.relIndex_eq_one.mp hrel1 h
  obtain ⟨hpn, τ, hτord, -, h, -, hαeq⟩ := hdesc p hp α hαE hαD hαord
  obtain ⟨-, hcardDescent, -, -, hinj, hfixiff, -, -, -, -, -, -, -, -⟩ :=
    CFSG.RankThree.CASymplecticSubfield.symplectic_prime_subfield_fixed_group_and_full_centralizer
      (K := K) Nat.prime_two hp (by omega : 3 < p) hp2 hf (le_refl 2) hKcard τ hτord
  have hcardP : Nat.card (StatedProj (StatedSp 2 K)) = l2cr_ofs_N n :=
    l2cr_ofs_card_proj hKcard
  let H₀ : Subgroup (StatedProj (StatedSp 2 K)) :=
    CFSG.RankThree.CASymplecticSubfield.subfieldFixedGroup K 2 τ
  have : Finite (CFSG.ComponentClassification.UnbalancedCatalog.descentField τ) :=
    Subtype.finite
  have hcardH : Nat.card H₀ = l2cr_ofs_N (n / p) := by
    let eH : StatedProj (StatedSp 2
        (CFSG.ComponentClassification.UnbalancedCatalog.descentField τ)) ≃* H₀ :=
      MonoidHom.ofInjective hinj
    rw [← Nat.card_congr eH.toEquiv]
    exact l2cr_ofs_card_proj hcardDescent
  let A : Subgroup (StatedProj (StatedSp 2 K)) := H₀.map h.toMonoidHom
  have hAcard : Nat.card A = Nat.card H₀ := Subgroup.card_map_of_injective h.injective
  have hAcard3 : (Nat.card A).factorization 3 =
      (Nat.card (StatedProj (StatedSp 2 K))).factorization 3 := by
    rw [hAcard, hcardH, hcardP]
    exact (l2cr_ofs_N_factorization hp hp3 hn0 hpn).symm
  have hφfix : ∀ y ∈ H₀,
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldAut 2 K τ) y = y :=
    fun y hy => (hfixiff y).mp hy
  have hAfix : ∀ x ∈ A, α x = x := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [hαeq]
    show h ((CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldAut 2 K τ)
      (h⁻¹ (h y))) = h y
    rw [MulAut.inv_apply, MulEquiv.symm_apply_apply, hφfix y hy]
  let Q_A : Sylow 3 A := Sylow.nonempty.some
  have hQA : Nat.card (Q_A : Subgroup A) = 3 ^ (Nat.card A).factorization 3 :=
    Sylow.card_eq_multiplicity Q_A
  let R : Subgroup (StatedProj (StatedSp 2 K)) := (Q_A : Subgroup A).map A.subtype
  have hRcard : Nat.card R =
      3 ^ (Nat.card (StatedProj (StatedSp 2 K))).factorization 3 := by
    rw [show Nat.card R = Nat.card (Q_A : Subgroup A) from
      Subgroup.card_map_of_injective A.subtype_injective, hQA, hAcard3]
  let Q_P : Sylow 3 (StatedProj (StatedSp 2 K)) := Sylow.ofCard R hRcard
  have hQP : (Q_P : Subgroup (StatedProj (StatedSp 2 K))) = R := Sylow.coe_ofCard R hRcard
  have hfixR : ∀ x ∈ R, α x = x := by
    intro x hx
    obtain ⟨q, -, rfl⟩ := hx
    exact hAfix q q.2
  let R_X : Subgroup X := R.map he.symm.toMonoidHom
  have hcardXP : Nat.card X = Nat.card (StatedProj (StatedSp 2 K)) :=
    Nat.card_congr he.toEquiv
  have hRXcard : Nat.card R_X = 3 ^ (Nat.card X).factorization 3 := by
    rw [show Nat.card R_X = Nat.card R from
      Subgroup.card_map_of_injective he.symm.injective, hRcard, ← hcardXP]
  have hαhe : ∀ y : X, α (he y) = he (σ y) := by
    intro y
    show (MulAut.congr he σ) (he y) = he (σ y)
    rw [MulAut.congr_apply]
    simp
  have hσconj : ∀ r : StatedProj (StatedSp 2 K), σ (he.symm r) = he.symm (α r) := by
    intro r
    have h1 := congrArg he.symm (hαhe (he.symm r))
    simp only [MulEquiv.symm_apply_apply, he.apply_symm_apply] at h1
    exact h1.symm
  have hfixRX : ∀ x ∈ R_X, σ x = x := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := hx
    change σ (he.symm r) = he.symm r
    rw [hσconj r, hfixR r hr]
  obtain ⟨Q_S, hQS⟩ := l2cr_exists_sylow_coe_eq hS
  let Q_RX : Sylow 3 X := Sylow.ofCard R_X hRXcard
  have hQRX : (Q_RX : Subgroup X) = R_X := Sylow.coe_ofCard R_X hRXcard
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X Q_S Q_RX
  refine ⟨g, fun x hx => ?_⟩
  have hmap : S.map (MulAut.conj g).toMonoidHom = R_X := by
    have h2 := congrArg (fun Q : Sylow 3 X => (Q : Subgroup X)) hg
    rw [CFSG.RankThree.PartTwo.Sec14.coe_sylow_smul_eq_map Q_S g, hQS, hQRX] at h2
    exact h2
  have hxR : g * x * g⁻¹ ∈ R_X := by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hx
  exact hfixRX (g * x * g⁻¹) hxR

private theorem l2cr_ofg_lte4 (m : ℕ) (hm : m ≠ 0) :
    (4 ^ m - 1).factorization 3 = 1 + m.factorization 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hodd : Odd 3 := by decide
  rw [Nat.factorization_def _ Nat.prime_three]
  have h := padicValNat.pow_sub_pow (p := 3) (x := 4) (y := 1) hodd (by norm_num) (by norm_num)
      (by norm_num) hm
  simp only [one_pow] at h
  rw [show (4:ℕ) - 1 = 3 by norm_num, padicValNat_self] at h
  rw [← Nat.factorization_def m Nat.prime_three] at h
  exact h

private theorem l2cr_ofg_fact3_three_mul (m : ℕ) (hm : m ≠ 0) :
    (3 * m).factorization 3 = 1 + m.factorization 3 := by
  rw [Nat.factorization_mul (by norm_num) hm, Finsupp.add_apply,
    Nat.Prime.factorization_self Nat.prime_three]

private theorem l2cr_ofg_fact3_ordG2 (m : ℕ) (hm : 1 ≤ m) :
    (ordG2 (2 ^ m)).factorization 3 = 3 + 2 * m.factorization 3 := by
  rw [CFSG.Open.ordG2]
  have hm0 : m ≠ 0 := by omega
  have h3m : 3 * m ≠ 0 := by positivity
  have hp6 : (2 ^ m) ^ 6 = 4 ^ (3 * m) := by
    rw [show (4:ℕ) = 2^2 by norm_num, ← pow_mul, ← pow_mul]
    congr 1
    ring
  have hp2 : (2 ^ m) ^ 2 = 4 ^ m := by
    rw [show (4:ℕ) = 2^2 by norm_num, ← pow_mul, ← pow_mul]
    congr 1
    ring
  rw [hp6, hp2]
  have h1 : 4 ^ (3 * m) ≠ 0 := by positivity
  have h2 : 4 ^ (3 * m) - 1 ≠ 0 := by
    have : 1 < 4 ^ (3 * m) := Nat.one_lt_pow h3m (by norm_num)
    omega
  have h3 : 4 ^ m - 1 ≠ 0 := by
    have : 1 < 4 ^ m := Nat.one_lt_pow hm0 (by norm_num)
    omega
  rw [Nat.factorization_mul (mul_ne_zero h1 h2) h3, Nat.factorization_mul h1 h2,
    Finsupp.add_apply, Finsupp.add_apply, l2cr_ofg_lte4 (3 * m) h3m, l2cr_ofg_lte4 m hm0,
    l2cr_ofg_fact3_three_mul m hm0]
  have h4 : (4 ^ (3 * m)).factorization 3 = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    intro h
    have : 3 ∣ 4 := Nat.prime_three.dvd_of_dvd_pow h
    omega
  rw [h4]
  ring

private theorem l2cr_ofg_fact3_six048 : (6048 : ℕ).factorization 3 = 3 := by
  have h : (6048:ℕ) = 3^3 * 224 := by norm_num
  rw [h, Nat.factorization_mul (a := 3^3) (b := 224) (by norm_num) (by norm_num),
    Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd (p := 3) (n := 224) (by norm_num),
    add_zero]
  rw [Nat.Prime.factorization_pow (p := 3) (k := 3) Nat.prime_three]
  simp

private theorem l2cr_ofg_commutator_le_inner_of_outerComm {G : Type} [Group G]
    (h : CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.OuterComm G) :
    commutator (MulAut G) ≤ Inn G := by
  change ⁅(⊤ : Subgroup (MulAut G)), ⊤⁆ ≤ Inn G
  rw [Subgroup.commutator_le]
  intro γ _ α _
  exact h γ α

private theorem l2cr_ofg_sameShape_G2 {q : TauCeti.PrimePower} {e : TauCeti.LieTypeIndex}
    (h : CFSG.LocalAnalysis.GLTheoremA.KD264Lie.sameShape (.G2 q) e) :
    ∃ q' : TauCeti.PrimePower, e = .G2 q' := by
  cases e <;> simp only [CFSG.LocalAnalysis.GLTheoremA.KD264Lie.sameShape] at h
  exact ⟨_, rfl⟩

private theorem l2cr_ofg_subRel_G2
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {q : TauCeti.PrimePower} (hq : q.p = 2) {e : TauCeti.LieTypeIndex} (hev : e.Valid)
    (h : CFSG.LocalAnalysis.GLTheoremA.KD264Lie.subRel p (.G2 q) e) :
    (Nat.card (CFSG.AGLEmbedding.CatGroup ⟨e, hev⟩)).factorization 3 =
      3 + 2 * q.exponent.factorization 3 := by
  rcases h with ⟨hs, hf⟩ | h2 | h3 | h4 | h5 | h6 | h7
  · obtain ⟨q', rfl⟩ := l2cr_ofg_sameShape_G2 hs
    have hcard : q'.card ^ p = q.card := hf
    have hqcard : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hq]
    have hq'p : q'.p = 2 := by
      have hdvd : q'.p ∣ 2 ^ q.exponent := by
        have h1 : q'.card ∣ 2 ^ q.exponent := by
          rw [← hqcard, ← hcard]
          exact dvd_pow_self _ hp.ne_zero
        rw [TauCeti.PrimePower.card_def] at h1
        exact (dvd_pow_self q'.p (Nat.ne_of_gt q'.exponent_pos)).trans h1
      exact (Nat.prime_dvd_prime_iff_eq q'.prime_p Nat.prime_two).1
        (q'.prime_p.dvd_of_dvd_pow hdvd)
    have h2' : q'.card ^ p = 2 ^ (q'.exponent * p) := by
      rw [TauCeti.PrimePower.card_def, hq'p, pow_mul]
    have hexp : q'.exponent * p = q.exponent :=
      Nat.pow_right_injective (by norm_num : 2 ≤ 2)
        (show (2:ℕ) ^ (q'.exponent * p) = 2 ^ q.exponent by rw [← h2', hcard, hqcard])
    have hord : Nat.card (CFSG.AGLEmbedding.CatGroup ⟨.G2 q', hev⟩) = ordG2 (2 ^ q'.exponent) :=
      CFSG.AGLEmbedding.card_catGroup_G2_even (d := ⟨.G2 q', hev⟩) hq'p rfl
    rw [hord, l2cr_ofg_fact3_ordG2 q'.exponent (Nat.pos_of_ne_zero q'.exponent_pos.ne')]
    congr 1
    rw [← hexp, Nat.factorization_mul (a := q'.exponent) (b := p) q'.exponent_pos.ne' hp.ne_zero,
      Finsupp.add_apply]
    have hp3 : p ≠ 3 := by omega
    rw [Nat.factorization_eq_zero_of_not_dvd (p := 3) (n := p)
      (by rintro ⟨k, hk⟩; exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
        ⟨k, hk⟩).symm), add_zero]
  · rcases h2 with ⟨⟨q2, hd2⟩, -⟩
    exact absurd hd2 (by simp)
  · rcases h3 with ⟨-, ⟨q3, hd3⟩, -⟩
    exact absurd hd3 (by simp)
  · rcases h4 with ⟨⟨q3, he3, hq3card⟩, -, hf4⟩
    subst he3
    have hq_exp : q.exponent = p := by
      have h1 : q.card = 2 ^ p := hf4
      rw [TauCeti.PrimePower.card_def, hq] at h1
      exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) h1
    have hord : Nat.card (CFSG.AGLEmbedding.CatGroup ⟨.twistedA 2 q3, hev⟩) =
        ordTwistedA 2 (q3.p ^ q3.exponent) :=
      CFSG.AGLEmbedding.card_catGroup_twistedA (d := ⟨.twistedA 2 q3, hev⟩) (r := 2)
        (q := q3) rfl
    rw [hord, show q3.p ^ q3.exponent = 3 by
      rw [← TauCeti.PrimePower.card_def]; exact hq3card,
      show ordTwistedA 2 3 = 6048 by decide +kernel, l2cr_ofg_fact3_six048]
    have hp3 : p ≠ 3 := by omega
    rw [hq_exp, Nat.factorization_eq_zero_of_not_dvd (p := 3) (n := p)
      (by rintro ⟨k, hk⟩; exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
        ⟨k, hk⟩).symm)]
  · rcases h5 with ⟨-, ⟨q5, hd5⟩, -⟩
    exact absurd hd5 (by simp)
  · rcases h6 with ⟨-, ⟨k6, hd6⟩, -⟩
    exact absurd hd6 (by simp)
  · rcases h7 with ⟨-, ⟨k7, hd7⟩, -⟩
    exact absurd hd7 (by simp)

private theorem l2cr_ofg_subRelC_G2_three
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {q : TauCeti.PrimePower} (hq : q.p = 2) {i : TauCeti.CFSGIndex}
    (h : CFSG.LocalAnalysis.GLTheoremA.KD264Lie.subRelC p (.G2 q) i) :
    (Nat.card i.Group).factorization 3 = 3 + 2 * q.exponent.factorization 3 := by
  rcases i with pc | alt | eli | spo
  · simp only [CFSG.LocalAnalysis.GLTheoremA.KD264Lie.subRelC] at h
  · simp only [CFSG.LocalAnalysis.GLTheoremA.KD264Lie.subRelC] at h
    rcases h with ⟨-, h5a, -⟩ | ⟨-, h6a⟩ | ⟨-, h8a, -⟩
    · rcases h5a with ⟨q1, hq1⟩
      exact absurd hq1 (by simp)
    · rcases h6a with ⟨⟨q1, hq1⟩, -⟩ | ⟨⟨q1, hq1⟩, -⟩ <;> exact absurd hq1 (by simp)
    · rcases h8a with ⟨q1, hq1⟩
      exact absurd hq1 (by simp)
  · exact l2cr_ofg_subRel_G2 hp hp5 hq eli.2
      (by simpa only [CFSG.LocalAnalysis.GLTheoremA.KD264Lie.subRelC] using h)
  · simp only [CFSG.LocalAnalysis.GLTheoremA.KD264Lie.subRelC] at h

theorem l2cr_g2_outer_fixed
    {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 2 ≤ n) (hX : IsG2 X n) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hc : 2 ^ (2 * n) ≡ 1 [MOD p]) {σ : MulAut X}
    (hσ : orderOf σ = p) (hout : σ ∉ Inn X) {S : Subgroup X} (hS : IsSylowOf 3 S ⊤) :
    ∃ g : X, ∀ x ∈ S, σ (g * x * g⁻¹) = g * x * g⁻¹ := by
  classical
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e0⟩⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18.exists_adjoint_of_isG2 hX
  have hK3 : 3 ≤ Nat.card K := by
    rw [hKcard]
    calc 3 ≤ 4 := by norm_num
      _ = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  let q : TauCeti.PrimePower := ⟨2, n, Nat.prime_two, by omega⟩
  have hqcard : q.card = 2 ^ n := by rw [TauCeti.PrimePower.card_def]
  have hq2 : q.p = 2 := rfl
  have hv : (TauCeti.LieTypeIndex.G2 q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff]
    refine ⟨?_, ?_⟩
    · rw [TauCeti.LieTypeIndex.inStandardRange_iff]
      show 3 ≤ q.card
      rw [hqcard]
      calc 3 ≤ 4 := by norm_num
        _ = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    · rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
      simp
  let d : TauCeti.ValidLieTypeIndex := ⟨TauCeti.LieTypeIndex.G2 q, hv⟩
  let C := (TauCeti.CFSGIndex.lie d).Group
  obtain ⟨e1⟩ := CFSG.Adapters.CatalogueFieldBridges.nonempty_adjointGroup_catEquiv
    (τ := .G2) (c := TauCeti.LieTypeIndex.G2)
    (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).g2 (q := q) hv (k := K)
    (by rw [hKcard, hqcard])
  let E : X ≃* C := e0.trans e1
  have : Finite C := Finite.of_equiv X E.toEquiv
  let β : MulAut C := MulAut.congr E σ
  have hβp : β ^ p = 1 := by
    change (MulAut.congr E σ) ^ p = 1
    rw [← map_pow, show σ ^ p = 1 by rw [← hσ]; exact pow_orderOf_eq_one σ, map_one]
  have hβinner : β ∉ Inn C := by
    intro hβ
    have hmem : β ∈ (Inn X).map (MulAut.congr E).toMonoidHom := by
      rw [CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr E]
      exact hβ
    rcases Subgroup.mem_map.mp hmem with ⟨γ, hγ, hγβ⟩
    have hγσ : γ = σ := by
      refine (MulAut.congr E).injective ?_
      show (MulAut.congr E).toMonoidHom γ = (MulAut.congr E) σ
      simpa only [β] using hγβ
    exact hout (hγσ ▸ hγ)
  have hab : commutator (MulAut C) ≤ Inn C :=
    l2cr_ofg_commutator_le_inner_of_outerComm
      (CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.OuterComm.of_mulEquiv e1.symm
        (CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.outerComm_adjoint_G2 K hK3))
  have hnd : β ∉ CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived C := by
    show β ∉ Inn C ⊔ commutator (MulAut C)
    rw [sup_eq_left.mpr hab]
    exact hβinner
  have hpdvdK : p ∣ (2 ^ n) ^ 2 - 1 := by
    have h1 : p ∣ 2 ^ (2 * n) - 1 := (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp hc.symm
    have he : (2 ^ n) ^ 2 = 2 ^ (2 * n) := by rw [← pow_mul, Nat.mul_comm]
    rwa [he]
  have hdvd_ord : (2 ^ n) ^ 2 - 1 ∣ ordG2 (2 ^ n) := by
    refine ⟨(2 ^ n) ^ 6 * ((2 ^ n) ^ 6 - 1), ?_⟩
    rw [CFSG.Open.ordG2]
    ring
  have hXcard : Nat.card X = ordG2 (2 ^ n) := by
    rw [Nat.card_congr e0.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2,
      hKcard]
  have hCX : Nat.card C = Nat.card X := (Nat.card_congr E.toEquiv).symm
  have hdvd : p ∣ Nat.card C := by
    rw [hCX, hXcard]
    exact hpdvdK.trans hdvd_ord
  have hchar : p ≠ d.1.characteristic := by
    change p ≠ (TauCeti.LieTypeIndex.G2 q).characteristic
    rw [TauCeti.LieTypeIndex.characteristic_G2, hq2]
    omega
  have h3 : ¬ (p = 3 ∧
      ((∃ q' : TauCeti.PrimePower, (d.1 = .A 1 q' ∨ d.1 = .twistedA 2 q') ∧ q'.card = 8) ∨
        (∃ q' : TauCeti.PrimePower, d.1 = .trialityD4 q'))) := by
    rintro ⟨hp3, -⟩
    omega
  have h5 : ¬ (p = 5 ∧ d.1 = .suzuki 2) := by
    rintro ⟨-, hd5⟩
    dsimp only [d] at hd5
    cases hd5
  obtain ⟨J', hJ'comp, hpJ', i, ⟨eJ'⟩, hsub⟩ :=
    GLTheoremA.KD264Lie.kd264OuterIdx_of_families GLTheoremA.KD264Lie.lieOuterIdx_linear
        GLTheoremA.KD264Lie.lieOuterIdx_unitary GLTheoremA.KD264Lie.lieOuterIdx_classicalBCD
        GLTheoremA.KD264Lie.lieOuterIdx_triality GLTheoremA.KD264Lie.lieOuterIdx_excUntwisted
        GLTheoremA.KD264Lie.lieOuterIdx_excTwisted d p hp (by omega) hchar hdvd
      h3 h5 β hβp hnd
  have hJ'le : J' ≤ CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β := hJ'comp.1
  have hC3 : (Nat.card C).factorization 3 = 3 + 2 * n.factorization 3 := by
    have hcard : Nat.card C = ordG2 (2 ^ n) := hCX.trans hXcard
    rw [hcard]
    simpa only [q] using l2cr_ofg_fact3_ordG2 n (by omega)
  have hi3 : (Nat.card i.Group).factorization 3 = 3 + 2 * n.factorization 3 := by
    have h := l2cr_ofg_subRelC_G2_three hp hp5 hq2 (i := i) (by simpa only [d] using hsub)
    simpa only [q] using h
  have hJ'3 : (Nat.card J').factorization 3 = (Nat.card C).factorization 3 := by
    refine le_antisymm ?_ ?_
    · have hdvd : Nat.card ↥J' ∣ Nat.card C := Subgroup.card_subgroup_dvd_card J'
      obtain ⟨k, hk⟩ := hdvd
      have hk0 : k ≠ 0 := by rintro rfl; rw [mul_zero] at hk; exact Nat.card_pos.ne' hk
      rw [hk, Nat.factorization_mul (Nat.card_pos.ne') hk0, Finsupp.add_apply]
      exact Nat.le_add_right _ _
    · have hprod : Nat.card J' =
          Nat.card (↥J' ⧸ Subgroup.center ↥J') * Nat.card (Subgroup.center ↥J') :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥J')
      have hq : Nat.card (↥J' ⧸ Subgroup.center ↥J') = Nat.card i.Group :=
        Nat.card_congr eJ'.toEquiv
      rw [hprod, Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne'),
        Finsupp.add_apply, hq, hC3, hi3]
      exact Nat.le_add_right _ _
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Pj⟩ : Nonempty (Sylow 3 ↥J') := inferInstance
  let P' : Sylow 3 C := Sylow.ofCard ((Pj : Subgroup ↥J').map J'.subtype) (by
    rw [Subgroup.card_map_of_injective J'.subtype_injective, Sylow.card_eq_multiplicity, hJ'3])
  have hP'le : (P' : Subgroup C) ≤ J' := by
    rw [Sylow.coe_ofCard]
    exact Subgroup.map_subtype_le _
  have hP'fix : (P' : Subgroup C) ≤ CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β := hP'le.trans hJ'le
  obtain ⟨g', hg'⟩ := l2cr_exists_map_conj_le_sylow P'
    (hS.isPGroup.map E.toMonoidHom)
  refine ⟨E.symm g', fun x hx => ?_⟩
  have hx' : E x ∈ S.map E.toMonoidHom := ⟨x, hx, rfl⟩
  have hmem : (MulAut.conj g') (E x) ∈ (P' : Subgroup C) :=
    hg' (Subgroup.mem_map_of_mem _ hx')
  have hfix : β ((MulAut.conj g') (E x)) = (MulAut.conj g') (E x) := hP'fix hmem
  have hconj : (MulAut.conj g') (E x) = E (E.symm g' * x * (E.symm g')⁻¹) := by
    simp only [MulAut.conj_apply, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have hβE : β (E (E.symm g' * x * (E.symm g')⁻¹)) =
      E (σ (E.symm g' * x * (E.symm g')⁻¹)) := by
    change (MulAut.congr E σ) (E _) = E (σ _)
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [hconj, hβE] at hfix
  exact E.injective hfix

theorem l2cr_sp4
    {X H : Type} [Group X] [Finite X] [Group H] [Finite H] (ι : X →* H)
    (hinj : Function.Injective ι) (hN : ι.range.Normal) {n : ℕ} (hX : IsSp4 X n) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hc : 2 ^ (2 * n) ≡ 1 [MOD p])
    (hX2 : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 2)
    (hH : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup H)) {S : Subgroup X} (hS : IsSylowOf 3 S ⊤) :
    0 < CFSG.Open.pRank p (centralizer ((ι '' (S : Set X) : Set H))) ∧
      ∀ e ∈ S, orderOf e = 3 → 2 ≤ CFSG.Open.pRank p (centralizer ({ι e} : Set H)) := by
  have hZ := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p218d_center_eq_bot_sp4 hX
  by_cases hz : ∃ z : H, orderOf z = p ∧ ∀ x : X, Commute z (ι x)
  · exact l2cr_of_centralizing ι hinj hZ hp hz (fun e _ he => l2cr_d1_sp4 hX hp hc he)
  · obtain ⟨s, hs, hsR, hsc, hy⟩ := l2cr_of_fixed ι hinj hN hZ hp hX2 hH hz
      (fun σ hσ hout => l2cr_sp4_outer_fixed hX hp hp5 hc hσ hout hS)
      (fun e he => l2cr_d1_sp4 hX hp hc he)
    exact l2cr_of_outer ι hinj hp hs hsR hsc hy

theorem l2cr_g2
    {X H : Type} [Group X] [Finite X] [Group H] [Finite H] (ι : X →* H)
    (hinj : Function.Injective ι) (hN : ι.range.Normal) {n : ℕ} (hn : 2 ≤ n) (hX : IsG2 X n)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hc : 2 ^ (2 * n) ≡ 1 [MOD p])
    (hX2 : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 2)
    (hH : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup H)) {S : Subgroup X} (hS : IsSylowOf 3 S ⊤) :
    0 < CFSG.Open.pRank p (centralizer ((ι '' (S : Set X) : Set H))) ∧
      ∀ e ∈ S, orderOf e = 3 → 2 ≤ CFSG.Open.pRank p (centralizer ({ι e} : Set H)) := by
  have hZ := CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18.center_eq_bot_of_isG2 hX
  by_cases hz : ∃ z : H, orderOf z = p ∧ ∀ x : X, Commute z (ι x)
  · exact l2cr_of_centralizing ι hinj hZ hp hz (fun e _ he => l2cr_d1_g2 hn hX hp hc he)
  · obtain ⟨s, hs, hsR, hsc, hy⟩ := l2cr_of_fixed ι hinj hN hZ hp hX2 hH hz
      (fun σ hσ hout => l2cr_g2_outer_fixed hn hX hp hp5 hc hσ hout hS)
      (fun e he => l2cr_d1_g2 hn hX hp hc he)
    exact l2cr_of_outer ι hinj hp hs hsR hsc hy

section Torus

open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial
open Matrix
open CFSG.RankThree.CentralLiftU (tcoord coe_tcoord coe_tcoord_of_diag hypSU_eq_of_diag
  mem_hypTorus_of_diag)
open CFSG.Quasithin.H13.Sec53F.Unit (hypTorus_comm hypSU_ext')

private noncomputable def l2cr_su5t_coord {m : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 m K) : ↥(hypTorus h 2 1) →* Kˣ × Kˣ :=
  (tcoord (r := 2) (ε := 1) h 0).prod (tcoord (r := 2) (ε := 1) h 1)

private theorem l2cr_su5t_coord_eq {m : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 m K) {t : ↥(hypTorus h 2 1)} {a : Fin 2 → Kˣ} {d : Fin 1 → Kˣ}
    (hm : (((t : ↥(hypSU h 2 1)) : GL (HypIndex 2 1) K) :
      Matrix (HypIndex 2 1) (HypIndex 2 1) K) = diagonal (torusEntries h a d)) :
    l2cr_su5t_coord h t = (a 0, a 1) := by
  refine Prod.ext ?_ ?_
  · rw [show (l2cr_su5t_coord h t).1 = tcoord h 0 t from rfl]
    exact Units.ext (coe_tcoord_of_diag h 0 hm)
  · rw [show (l2cr_su5t_coord h t).2 = tcoord h 1 t from rfl]
    exact Units.ext (coe_tcoord_of_diag h 1 hm)

private theorem l2cr_su5t_torus_d {m : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 m K) {a : Fin 2 → Kˣ} {d : Fin 1 → Kˣ}
    (hp : torusRatio h a d = 1) (k : Fin 1) :
    (d k : K) = (∏ i, (a i : K) / h.bar (a i))⁻¹ := by
  rw [torusRatio] at hp
  have := eq_inv_of_mul_eq_one_right hp
  rw [Fin.prod_univ_one] at this
  rw [Fin.fin_one_eq_zero k]
  exact this

private theorem l2cr_su5t_coord_injective {m : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 m K) : Function.Injective (l2cr_su5t_coord h) := by
  intro t t' htt'
  obtain ⟨a, d, -, hp, hm⟩ := t.2
  obtain ⟨a', d', -, hp', hm'⟩ := t'.2
  rw [l2cr_su5t_coord_eq h hm, l2cr_su5t_coord_eq h hm'] at htt'
  have haa : a = a' := by
    funext i
    fin_cases i
    · exact (Prod.mk.inj htt').1
    · exact (Prod.mk.inj htt').2
  refine Subtype.ext (hypSU_eq_of_diag h hm hm' (fun x => ?_) (fun k => ?_))
  · simp only [torusEntries, haa]
  · simp only [torusEntries]
    rw [l2cr_su5t_torus_d h hp k, l2cr_su5t_torus_d h hp' k, haa]

private theorem l2cr_su5t_coord_surjective {m : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 m K) : Function.Surjective (l2cr_su5t_coord h) := by
  rintro ⟨u, v⟩
  have hbb : ∀ x : K, h.bar (h.bar x) = x := h.bar_bar
  have hu : (u : K) ≠ 0 := u.ne_zero
  have hv : (v : K) ≠ 0 := v.ne_zero
  have hu' : h.bar (u : K) ≠ 0 := by simp [hu]
  have hv' : h.bar (v : K) ≠ 0 := by simp [hv]
  let a : Fin 2 → Kˣ := ![u, v]
  let d : Fin 1 → Kˣ := fun _ => Units.map (h.bar : K →* K) (u * v) * (u * v)⁻¹
  have hd : ∀ k, h.norm (d k : K) = 1 := by
    intro k
    simp only [d, UnitaryFieldData.norm, Units.val_mul, Units.coe_map, MonoidHom.coe_ofClass,
      Units.val_inv_eq_inv_val, map_mul, map_inv₀, hbb]
    field_simp
  have hp : torusRatio h a d = 1 := by
    rw [torusRatio, Fin.prod_univ_two, Fin.prod_univ_one]
    simp only [a, d, Matrix.cons_val_zero, Matrix.cons_val_one, Units.val_mul, Units.coe_map,
      MonoidHom.coe_ofClass, Units.val_inv_eq_inv_val, map_mul]
    field_simp
  obtain ⟨g, hg, hm⟩ := torusMat_mem_hypSU h a hd hp
  refine ⟨⟨g, hg⟩, ?_⟩
  rw [l2cr_su5t_coord_eq h hm]
  rfl

private noncomputable def l2cr_su5t_torusEquiv {m : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 m K) : ↥(hypTorus h 2 1) ≃* Kˣ × Kˣ :=
  MulEquiv.ofBijective (l2cr_su5t_coord h)
    ⟨l2cr_su5t_coord_injective h, l2cr_su5t_coord_surjective h⟩

private theorem l2cr_su5t_card_torus {m : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 m K) :
    Nat.card ↥(hypTorus h 2 1) = (2 ^ (2 * m) - 1) ^ 2 := by
  have := h.finite
  rw [Nat.card_congr (l2cr_su5t_torusEquiv h).toEquiv, Nat.card_prod, Nat.card_units, h.card, sq]

private def l2cr_su5t_cofactor (m : ℕ) : ℕ :=
  (2 ^ m) ^ 10 * ((2 ^ m) ^ 3 + 1) * ((2 ^ m) ^ 2 + 1) * ((2 ^ m) ^ 5 + 1)

private theorem l2cr_su5t_card_hypSU {m : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 m K) :
    Nat.card (hypSU h 2 1) = (2 ^ (2 * m) - 1) ^ 2 * l2cr_su5t_cofactor m := by
  have h1 := (card_hypSU h (r := 2) (ε := 1) (by norm_num)).1
  have hX1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hpow : (2 : ℕ) ^ (2 * m) = (2 ^ m) ^ 2 := by rw [← pow_mul, mul_comm]
  rw [hpow]
  unfold l2cr_su5t_cofactor
  generalize 2 ^ m = X at h1 hX1 ⊢
  have h2 : 1 ≤ X ^ 2 := Nat.one_le_pow _ _ hX1
  rw [show Finset.Icc 2 (2 * 2 + 1) = {2, 3, 4, 5} by decide, Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton] at h1
  zify [h2]
  rw [h1]
  norm_num
  ring

private theorem l2cr_su5t_three_not_dvd_cofactor {m : ℕ} (hm2 : Even m) :
    ¬ 3 ∣ l2cr_su5t_cofactor m := by
  obtain ⟨k, rfl⟩ := hm2
  have h4 : (2 : ZMod 3) ^ 2 = 1 := by decide
  have h2 : (2 : ZMod 3) ^ (k + k) = 1 := by
    rw [show k + k = 2 * k by ring, pow_mul, h4, one_pow]
  have hval : ((l2cr_su5t_cofactor (k + k) : ℕ) : ZMod 3) = 2 := by
    unfold l2cr_su5t_cofactor
    push_cast
    rw [h2]
    decide
  intro hdvd
  have h0 := (ZMod.natCast_eq_zero_iff _ 3).2 hdvd
  rw [hval] at h0
  exact absurd h0 (by decide)

private theorem l2cr_su5t_sylow_three {m : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 m K) (hm2 : Even m) :
    ∃ S : Subgroup (hypSU h 2 1), IsSylowOf 3 S ⊤ ∧ S ≤ hypTorus h 2 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcardSU := l2cr_su5t_card_hypSU h
  have h3C := l2cr_su5t_three_not_dvd_cofactor hm2
  have hneC : l2cr_su5t_cofactor m ≠ 0 := by
    unfold l2cr_su5t_cofactor
    positivity
  have hneA : (2 ^ (2 * m) - 1) ^ 2 ≠ 0 := by
    have hm1 : 1 ≤ m := h.one_le
    have h1 : 2 ^ 2 ≤ 2 ^ (2 * m) :=
      pow_le_pow_right' (by norm_num : (1 : ℕ) ≤ 2) (by omega)
    exact pow_ne_zero 2 (by omega)
  have hfac : (Nat.card ↥(hypTorus h 2 1)).factorization 3 =
      (Nat.card (hypSU h 2 1)).factorization 3 := by
    rw [l2cr_su5t_card_torus h, hcardSU]
    rw [Nat.factorization_mul hneA hneC, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd h3C, add_zero]
  let P : Sylow 3 ↥(hypTorus h 2 1) := default
  refine ⟨(P : Subgroup ↥(hypTorus h 2 1)).map (hypTorus h 2 1).subtype, ?_,
    Subgroup.map_subtype_le _⟩
  refine CFSG.ABGLocalTools.isSylowOf_of_card le_top ?_
  rw [Subgroup.card_map_of_injective (hypTorus h 2 1).subtype_injective,
    Sylow.card_eq_multiplicity, hfac, Subgroup.card_top]

private theorem l2cr_su5t_torus_elemAbelian {m : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 m K) {p : ℕ} (hp : p.Prime) {ζ : Kˣ} (hζ : orderOf ζ = p) :
    ∃ E : Subgroup (hypSU h 2 1), E ≤ hypTorus h 2 1 ∧ IsElemAbelian p E ∧
      Nat.card E = p ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨t₁, ht₁⟩ := l2cr_su5t_coord_surjective h (ζ, 1)
  obtain ⟨t₂, ht₂⟩ := l2cr_su5t_coord_surjective h (1, ζ)
  have ht₁T : (t₁ : hypSU h 2 1) ∈ hypTorus h 2 1 := t₁.2
  have ht₂T : (t₂ : hypSU h 2 1) ∈ hypTorus h 2 1 := t₂.2
  have ho₁ : orderOf (t₁ : hypSU h 2 1) = p := by
    change orderOf ((hypTorus h 2 1).subtype t₁) = p
    rw [orderOf_injective (hypTorus h 2 1).subtype (hypTorus h 2 1).subtype_injective t₁]
    rw [← orderOf_injective (l2cr_su5t_coord h) (l2cr_su5t_coord_injective h) t₁, ht₁,
      Prod.orderOf]
    simp [hζ]
  have ho₂ : orderOf (t₂ : hypSU h 2 1) = p := by
    change orderOf ((hypTorus h 2 1).subtype t₂) = p
    rw [orderOf_injective (hypTorus h 2 1).subtype (hypTorus h 2 1).subtype_injective t₂]
    rw [← orderOf_injective (l2cr_su5t_coord h) (l2cr_su5t_coord_injective h) t₂, ht₂,
      Prod.orderOf]
    simp [hζ]
  have hinf : Subgroup.zpowers (t₁ : hypSU h 2 1) ⊓
      Subgroup.zpowers (t₂ : hypSU h 2 1) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hx1
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hx2
    have hsub : (t₁ ^ i : ↥(hypTorus h 2 1)) = t₂ ^ j := by
      apply Subtype.ext
      rw [Subgroup.coe_zpow, Subgroup.coe_zpow, hi, hj]
    have hc := congrArg (l2cr_su5t_coord h) hsub
    rw [map_zpow, map_zpow, ht₁, ht₂] at hc
    have hζi : ζ ^ i = 1 := by
      have := congrArg Prod.fst hc
      simpa using this
    have hpi : (p : ℤ) ∣ i := by
      rw [← hζ]
      exact orderOf_dvd_iff_zpow_eq_one.mpr hζi
    obtain ⟨k, hk⟩ := hpi
    have hz : (t₁ : hypSU h 2 1) ^ i = 1 := by
      rw [hk, _root_.zpow_mul]
      have hp1 : (t₁ : hypSU h 2 1) ^ (p : ℤ) = 1 := by
        rw [zpow_natCast, ← ho₁]
        exact pow_orderOf_eq_one _
      rw [hp1, _root_.one_zpow]
    rw [← hi, hz]
  let A := ↥(Subgroup.zpowers (t₁ : hypSU h 2 1)) ×
    ↥(Subgroup.zpowers (t₂ : hypSU h 2 1))
  let f : A →* hypSU h 2 1 :=
    { toFun := fun x => (x.1 : hypSU h 2 1) * (x.2 : hypSU h 2 1)
      map_one' := by simp
      map_mul' := fun x y => by
        have hx2T : ((x.2 : ↥(Subgroup.zpowers (t₂ : hypSU h 2 1))) : hypSU h 2 1) ∈
            hypTorus h 2 1 := Subgroup.zpowers_le.mpr ht₂T x.2.2
        have hy1T : ((y.1 : ↥(Subgroup.zpowers (t₁ : hypSU h 2 1))) : hypSU h 2 1) ∈
            hypTorus h 2 1 := Subgroup.zpowers_le.mpr ht₁T y.1.2
        have hc := hypTorus_comm h hx2T hy1T
        change ((x.1 : hypSU h 2 1) * (y.1 : hypSU h 2 1)) *
              ((x.2 : hypSU h 2 1) * (y.2 : hypSU h 2 1)) =
            ((x.1 : hypSU h 2 1) * (x.2 : hypSU h 2 1)) *
              ((y.1 : hypSU h 2 1) * (y.2 : hypSU h 2 1))
        calc ((x.1 : hypSU h 2 1) * (y.1 : hypSU h 2 1)) *
              ((x.2 : hypSU h 2 1) * (y.2 : hypSU h 2 1))
            = (x.1 : hypSU h 2 1) * ((y.1 : hypSU h 2 1) *
                ((x.2 : hypSU h 2 1) * (y.2 : hypSU h 2 1))) := by group
          _ = (x.1 : hypSU h 2 1) * (((y.1 : hypSU h 2 1) * (x.2 : hypSU h 2 1)) *
                (y.2 : hypSU h 2 1)) := by group
          _ = (x.1 : hypSU h 2 1) * (((x.2 : hypSU h 2 1) * (y.1 : hypSU h 2 1)) *
                (y.2 : hypSU h 2 1)) := by rw [← hc]
          _ = ((x.1 : hypSU h 2 1) * (x.2 : hypSU h 2 1)) *
                ((y.1 : hypSU h 2 1) * (y.2 : hypSU h 2 1)) := by group }
  have hcomm : ∀ a b : A, a * b = b * a := by
    intro a b
    apply Prod.ext
    · apply Subtype.ext
      exact hypTorus_comm h (Subgroup.zpowers_le.mpr ht₁T a.1.2)
        (Subgroup.zpowers_le.mpr ht₁T b.1.2)
    · apply Subtype.ext
      exact hypTorus_comm h (Subgroup.zpowers_le.mpr ht₂T a.2.2)
        (Subgroup.zpowers_le.mpr ht₂T b.2.2)
  have hpow : ∀ a : A, a ^ p = 1 := by
    intro a
    apply Prod.ext
    · apply Subtype.ext
      change (a.1 : hypSU h 2 1) ^ p = 1
      have hd := orderOf_dvd_of_mem_zpowers (x := (t₁ : hypSU h 2 1)) a.1.2
      rw [ho₁] at hd
      exact orderOf_dvd_iff_pow_eq_one.mp hd
    · apply Subtype.ext
      change (a.2 : hypSU h 2 1) ^ p = 1
      have hd := orderOf_dvd_of_mem_zpowers (x := (t₂ : hypSU h 2 1)) a.2.2
      rw [ho₂] at hd
      exact orderOf_dvd_iff_pow_eq_one.mp hd
  have hA : Nat.card A = p ^ 2 := by
    rw [Nat.card_prod, Nat.card_zpowers, Nat.card_zpowers, ho₁, ho₂, ← pow_two]
  have hker : ∀ x : A, f x = 1 → x = 1 := by
    intro x hx
    have hx1 : (x.1 : hypSU h 2 1) = ((x.2 : hypSU h 2 1))⁻¹ := by
      have hh := congrArg (fun z : hypSU h 2 1 => (x.1 : hypSU h 2 1)⁻¹ * z) hx
      simp only [f, MonoidHom.coe_mk, OneHom.coe_mk, mul_one] at hh
      have h2 : (x.2 : hypSU h 2 1) = (x.1 : hypSU h 2 1)⁻¹ := by
        simpa [mul_assoc] using hh
      rw [h2, inv_inv]
    have hmem : (x.1 : hypSU h 2 1) ∈ Subgroup.zpowers (t₁ : hypSU h 2 1) ⊓
        Subgroup.zpowers (t₂ : hypSU h 2 1) :=
      ⟨x.1.2, by rw [hx1]; exact (Subgroup.zpowers (t₂ : hypSU h 2 1)).inv_mem x.2.2⟩
    rw [hinf, Subgroup.mem_bot] at hmem
    have hx2 : (x.2 : hypSU h 2 1) = 1 := by
      rw [← _root_.inv_inj, ← hx1, hmem, inv_one]
    exact Prod.ext (Subtype.ext hmem) (Subtype.ext hx2)
  have hf : Function.Injective f := by
    intro x y hxy
    have hxy' : f (x * y⁻¹) = 1 := by
      rw [map_mul, map_inv, hxy, mul_inv_cancel]
    have h1 := hker (x * y⁻¹) hxy'
    rwa [mul_inv_eq_one] at h1
  refine ⟨f.range, ?_, ?_, ?_⟩
  · rintro x ⟨a, ha⟩
    rw [← ha]
    exact mul_mem (Subgroup.zpowers_le.mpr ht₁T a.1.2)
      (Subgroup.zpowers_le.mpr ht₂T a.2.2)
  · refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a', ha'⟩ := MonoidHom.mem_range.1 a.2
      obtain ⟨b', hb'⟩ := MonoidHom.mem_range.1 b.2
      apply Subtype.ext
      change (a : hypSU h 2 1) * b = b * a
      rw [← ha', ← hb', ← map_mul, ← map_mul, hcomm]
    · obtain ⟨a, rfl⟩ := MonoidHom.mem_range.1 hx
      rw [← map_pow, hpow, map_one]
  · rw [← hA]
    exact (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm

private theorem l2cr_su5t_torus_pRank {m : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 m K) {p : ℕ} (hp : p.Prime) {ζ : Kˣ} (hζ : orderOf ζ = p) :
    2 ≤ CFSG.Open.pRank p (hypTorus h 2 1) := by
  obtain ⟨E, hET, hEab, hEcard⟩ := l2cr_su5t_torus_elemAbelian h hp hζ
  exact CFSG.SectionRank.le_pRank hp.one_lt hET hEab hEcard

private theorem l2cr_su5t_card_map_mul_card_inf_ker {G H : Type*} [Group G] [Group H]
    [Finite G] (f : G →* H) (E : Subgroup G) :
    Nat.card ↥(E.map f) * Nat.card ↥(E ⊓ f.ker) = Nat.card ↥E := by
  have hsub : (E ⊓ f.ker).subgroupOf E = (f.ker).subgroupOf E := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
  have h1 : Nat.card ↥(E.map f) = Nat.card (↥E ⧸ (f.subgroupMap E).ker) :=
    (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
      (φ := f.subgroupMap E) (MonoidHom.subgroupMap_surjective f E)).toEquiv).symm
  have h2 : Nat.card ↥(E ⊓ f.ker) = Nat.card ↥((E ⊓ f.ker).subgroupOf E) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).symm
  rw [h1, h2, Subgroup.ker_subgroupMap, hsub]
  exact (Subgroup.card_eq_card_quotient_mul_card_subgroup ((f.ker).subgroupOf E)).symm

private theorem l2cr_su5t_coord_fst_eq_snd_of_mem_scalars {m : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 m K) {s : ↥(hypTorus h 2 1)}
    (hs : (s : hypSU h 2 1) ∈ hypScalars h 2 1) :
    (l2cr_su5t_coord h s).1 = (l2cr_su5t_coord h s).2 := by
  obtain ⟨c, -, -, hc⟩ := mem_normOneScalars.1 hs
  have h1 : (((s : hypSU h 2 1) : GL (HypIndex 2 1) K) :
      Matrix (HypIndex 2 1) (HypIndex 2 1) K) (.inl 0) (.inl 0) = (c : K) := by
    rw [hc]
    simp [GeneralLinearGroup.coe_scalar]
  have h2 : (((s : hypSU h 2 1) : GL (HypIndex 2 1) K) :
      Matrix (HypIndex 2 1) (HypIndex 2 1) K) (.inl 1) (.inl 1) = (c : K) := by
    rw [hc]
    simp [GeneralLinearGroup.coe_scalar]
  apply Units.ext
  rw [show (l2cr_su5t_coord h s).1 = tcoord h 0 s from rfl,
    show (l2cr_su5t_coord h s).2 = tcoord h 1 s from rfl, coe_tcoord, coe_tcoord, h1, h2]

private theorem l2cr_su5t_scalars_le_torus {m : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 m K) : hypScalars h 2 1 ≤ hypTorus h 2 1 := by
  intro z hz
  obtain ⟨c, -, -, hg⟩ := mem_normOneScalars.1 hz
  refine mem_hypTorus_of_diag h (q := fun _ => (c : K)) ?_
  rw [hg]
  ext i j
  simp [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply]

end Torus

open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial
open Matrix
open CFSG.RankThree.CentralLiftU (tcoord coe_tcoord coe_tcoord_of_diag hypSU_eq_of_diag
  mem_hypTorus_of_diag)
open CFSG.Quasithin.H13.Sec53F.Unit (hypTorus_comm hypSU_ext')

private theorem l2cr_su5t_pRank_map_of_elemAbelian {m : ℕ} {K : Type} [Field K]
    {X : Type} [Group X] [Finite X] (h : UnitaryFieldData 2 m K)
    {p : ℕ} (hp : p.Prime) (α : hypSU h 2 1 →* X)
    {E : Subgroup (hypSU h 2 1)} (hET : E ≤ hypTorus h 2 1)
    (hEab : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 2)
    (hEker : E ⊓ α.ker = ⊥) :
    2 ≤ CFSG.Open.pRank p ((hypTorus h 2 1).map α) := by
  have hcard : Nat.card ↥(E.map α) = p ^ 2 := by
    have hh := l2cr_su5t_card_map_mul_card_inf_ker α E
    rw [hEker, Subgroup.card_bot, mul_one, hEcard] at hh
    exact hh
  exact CFSG.SectionRank.le_pRank hp.one_lt (Subgroup.map_mono hET)
    (CFSG.SectionRank.isElemAbelian_map hEab α) hcard

private theorem l2cr_su5t_inf_ker_bot {m : ℕ} {K : Type} [Field K]
    {X : Type} [Group X] [Finite X] (h : UnitaryFieldData 2 m K) {p : ℕ} (hp : p.Prime)
    (α : hypSU h 2 1 →* X)
    {E : Subgroup (hypSU h 2 1)} (hEcard : Nat.card E = p ^ 2) (hp5 : p ≠ 5)
    (hker : Nat.card α.ker ∣ 5) : E ⊓ α.ker = ⊥ := by
  have h1 : Nat.card ↥(E ⊓ α.ker) ∣ p ^ 2 :=
    Nat.dvd_trans (Subgroup.card_dvd_of_le (show E ⊓ α.ker ≤ E from inf_le_left))
      (by rw [← hEcard])
  have h2 : Nat.card ↥(E ⊓ α.ker) ∣ 5 := (Subgroup.card_dvd_of_le inf_le_right).trans hker
  have hcop : Nat.Coprime (p ^ 2) 5 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 5)]
    exact fun hd => hp5 ((Nat.prime_dvd_prime_iff_eq (by norm_num : Nat.Prime 5) hp).1
      (Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) hd)).symm
  have hcard : Nat.card ↥(E ⊓ α.ker) = 1 := by
    have hg : Nat.card ↥(E ⊓ α.ker) ∣ Nat.gcd (p ^ 2) 5 := Nat.dvd_gcd h1 h2
    rw [hcop.gcd_eq_one] at hg
    exact Nat.dvd_one.1 hg
  have hbot : E ⊓ α.ker = ⊥ := Subgroup.card_eq_one.1 hcard
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  exact Subgroup.mem_bot.1 (hbot ▸ hx)

private theorem l2cr_su5t_coord_of_scalar {m : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 m K) {z : ↥(hypTorus h 2 1)} {c : Kˣ}
    (hsc : ((z : hypSU h 2 1) : GL (HypIndex 2 1) K) =
      GeneralLinearGroup.scalar (HypIndex 2 1) c) :
    l2cr_su5t_torusEquiv h z = (c, c) := by
  have h1 : ((tcoord (r := 2) (ε := 1) h 0 z : Kˣ) : K) = (c : K) := by
    rw [coe_tcoord, hsc]
    simp [GeneralLinearGroup.coe_scalar]
  have h2 : ((tcoord (r := 2) (ε := 1) h 1 z : Kˣ) : K) = (c : K) := by
    rw [coe_tcoord, hsc]
    simp [GeneralLinearGroup.coe_scalar]
  refine Prod.ext ?_ ?_
  · rw [show (l2cr_su5t_torusEquiv h z).1 = tcoord h 0 z from rfl]
    exact Units.ext h1
  · rw [show (l2cr_su5t_torusEquiv h z).2 = tcoord h 1 z from rfl]
    exact Units.ext h2

private theorem l2cr_su5t_exists_coord_of_mem_scalars {m : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 m K) {z : ↥(hypTorus h 2 1)}
    (hz : (z : hypSU h 2 1) ∈ hypScalars h 2 1) :
    ∃ c : Kˣ, c ^ 5 = 1 ∧ l2cr_su5t_torusEquiv h z = (c, c) := by
  obtain ⟨c, -, hc5, hsc⟩ := mem_normOneScalars.1 hz
  exact ⟨c, hc5, l2cr_su5t_coord_of_scalar h hsc⟩

private theorem l2cr_su5t_mem_scalars_of_coord {m : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 m K) {c : Kˣ} (hc5 : c ^ 5 = 1)
    (hcb : h.bar (c : K) = (c : K)⁻¹) :
    (((l2cr_su5t_torusEquiv h).symm (c, c) : ↥(hypTorus h 2 1)) : hypSU h 2 1) ∈
      hypScalars h 2 1 := by
  have hc5' : (c : K) ^ 5 = 1 := by rw [← Units.val_pow_eq_pow_val, hc5, Units.val_one]
  have hd : ∀ k : Fin 1, h.norm ((![c] : Fin 1 → Kˣ) k : K) = 1 := by
    intro k
    fin_cases k
    rw [UnitaryFieldData.norm, Matrix.cons_val_fin_one, hcb]
    exact mul_inv_cancel₀ c.ne_zero
  have hp : torusRatio h ![c, c] ![c] = 1 := by
    rw [torusRatio, Fin.prod_univ_two, Fin.prod_univ_one]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hcb, div_inv_eq_mul]
    rw [show (c : K) * c * (c * c) * c = (c : K) ^ 5 by ring, hc5']
  obtain ⟨g, hg, hgm⟩ := torusMat_mem_hypSU h ![c, c] hd hp
  have hgc : l2cr_su5t_torusEquiv h ⟨g, hg⟩ = (c, c) := by
    change l2cr_su5t_coord h ⟨g, hg⟩ = (c, c)
    rw [l2cr_su5t_coord_eq h hgm]
    simp
  have heq : (l2cr_su5t_torusEquiv h).symm (c, c) = ⟨g, hg⟩ := by
    apply (l2cr_su5t_torusEquiv h).injective
    rw [hgc]
    simp
  rw [heq]
  refine mem_normOneScalars.2 ⟨c, ?_, hc5, ?_⟩
  · rw [UnitaryFieldData.norm, hcb]
    exact mul_inv_cancel₀ c.ne_zero
  · apply Units.ext
    have hte : torusEntries h ![c, c] ![c] = fun _ => (c : K) := by
      funext i
      rcases i with i | k | i
      · fin_cases i
        all_goals simp [torusEntries]
      · fin_cases k
        all_goals simp [torusEntries]
      · fin_cases i
        all_goals simp [torusEntries, hcb]
    change ((g : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) =
      ((GeneralLinearGroup.scalar (HypIndex 2 1) c : GL (HypIndex 2 1) K) :
        Matrix (HypIndex 2 1) (HypIndex 2 1) K)
    rw [GeneralLinearGroup.coe_scalar, hgm, hte, Matrix.scalar_apply]

private theorem l2cr_su5t_pRank_five {m : ℕ} {K : Type} [Field K]
    {X : Type} [Group X] [Finite X] (h : UnitaryFieldData 2 m K) (α : hypSU h 2 1 →* X)
    (hker : α.ker = hypScalars h 2 1) (h25 : 25 ∣ 2 ^ m + 1) :
    2 ≤ CFSG.Open.pRank 5 ((hypTorus h 2 1).map α) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Finite K := h.finite
  have h5 : 5 ∣ 2 ^ m + 1 := dvd_trans (by norm_num : 5 ∣ 25) h25
  have h25N : 25 ∣ Nat.card Kˣ := by
    rw [Nat.card_units, h.card]
    have h1 : 2 ^ (2 * m) - 1 = (2 ^ m - 1) * (2 ^ m + 1) := by
      rw [show 2 ^ (2 * m) = (2 ^ m) ^ 2 by rw [← pow_mul, mul_comm]]
      simpa [mul_comm] using Nat.sq_sub_sq (2 ^ m) 1
    rw [h1]
    exact h25.mul_left _
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hgord : orderOf g = Nat.card Kˣ := orderOf_eq_card_of_forall_mem_zpowers hg
  let k := Nat.card Kˣ / 25
  have hk0 : k ≠ 0 := by
    rintro h0
    have hN : Nat.card Kˣ = 25 * k := (Nat.mul_div_cancel' h25N).symm
    rw [h0, mul_zero] at hN
    exact Nat.card_pos.ne' hN
  let w : Kˣ := g ^ k
  have hword : orderOf w = 25 := by
    rw [orderOf_pow_of_dvd hk0 (by rw [hgord]; exact Nat.div_dvd_of_dvd h25N), hgord]
    rw [show Nat.card Kˣ = 25 * k from (Nat.mul_div_cancel' h25N).symm, mul_comm 25 k]
    exact Nat.mul_div_cancel_left 25 (Nat.pos_of_ne_zero hk0)
  have hw5ord : orderOf (w ^ 5) = 5 := by
    rw [orderOf_pow_of_dvd (by norm_num : (5 : ℕ) ≠ 0)
      (by rw [hword]; norm_num), hword]
  have hw25 : (w ^ 5) ^ 5 = 1 := by
    rw [← pow_mul, show 5 * 5 = 25 by norm_num, ← hword]
    exact pow_orderOf_eq_one w
  have hwb : h.bar ((w ^ 5 : Kˣ) : K) = (((w ^ 5 : Kˣ) : K))⁻¹ := by
    rw [UnitaryFieldData.bar_apply]
    have hc5' : (((w ^ 5 : Kˣ) : K)) ^ 5 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hw25, Units.val_one]
    obtain ⟨k', hk'⟩ := h5
    have h1 : (((w ^ 5 : Kˣ) : K)) ^ (2 ^ m) * ((w ^ 5 : Kˣ) : K) = 1 := by
      rw [← pow_succ, hk', pow_mul, hc5', one_pow]
    exact eq_inv_of_mul_eq_one_left h1
  let e := l2cr_su5t_torusEquiv h
  let Zc := (hypScalars h 2 1).subgroupOf (hypTorus h 2 1)
  have hZc_card : Nat.card Zc = 5 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (l2cr_su5t_scalars_le_torus h)).toEquiv,
      card_hypScalars h (by norm_num)]
    exact Nat.gcd_eq_left h5
  have hmapcard : Nat.card ↥(Zc.map e.toMonoidHom) = 5 := by
    rw [Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, hZc_card]
  have hZc_coord : ∀ z ∈ Zc, ∃ c : Kˣ, c ^ 5 = 1 ∧ e z = (c, c) := fun z hz =>
    l2cr_su5t_exists_coord_of_mem_scalars h (Subgroup.mem_subgroupOf.1 hz)
  have hw5Z : e.symm (w ^ 5, w ^ 5) ∈ Zc :=
    Subgroup.mem_subgroupOf.2 (l2cr_su5t_mem_scalars_of_coord h hw25 hwb)
  have hEdiag : ∀ x ∈ Zc.map e.toMonoidHom, x.1 = x.2 := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨c, -, hc⟩ := hZc_coord z hz
    change (e z).1 = (e z).2
    rw [hc]
  let t₁ : ↥(hypTorus h 2 1) := e.symm (w, w)
  let t₂ : ↥(hypTorus h 2 1) := e.symm (w ^ 5, 1)
  have ht₁ : (t₁ : hypSU h 2 1) ∈ hypTorus h 2 1 := t₁.2
  have ht₂ : (t₂ : hypSU h 2 1) ∈ hypTorus h 2 1 := t₂.2
  have ht₁5 : (t₁ : hypSU h 2 1) ^ 5 ∈ α.ker := by
    rw [hker]
    have h1 : (t₁ : hypSU h 2 1) ^ 5 = e.symm (w ^ 5, w ^ 5) := by
      rw [show (t₁ : hypSU h 2 1) = (e.symm (w, w) : ↥(hypTorus h 2 1)) from rfl,
        ← Subgroup.coe_pow, ← map_pow]
      simp
    rw [h1]
    exact Subgroup.mem_subgroupOf.1 hw5Z
  have ht₂5 : (t₂ : hypSU h 2 1) ^ 5 ∈ α.ker := by
    rw [hker]
    have h3 : t₂ ^ 5 = 1 := by
      have h2 : (w ^ 5, (1 : Kˣ)) ^ 5 = (1, 1) := by
        refine Prod.ext ?_ ?_
        · rw [Prod.pow_fst]
          exact hw25
        · rw [Prod.pow_snd]
          simp
      rw [show t₂ = e.symm (w ^ 5, 1) from rfl, ← map_pow, congrArg e.symm h2]
      exact map_one e.symm
    rw [← Subgroup.coe_pow, h3]
    exact Subgroup.one_mem _
  let u₁ : X := α (t₁ : hypSU h 2 1)
  let u₂ : X := α (t₂ : hypSU h 2 1)
  have hu₁5 : u₁ ^ 5 = 1 := by
    have h1 : u₁ = α (t₁ : hypSU h 2 1) := rfl
    rw [h1, ← map_pow]
    exact MonoidHom.mem_ker.1 ht₁5
  have hu₂5 : u₂ ^ 5 = 1 := by
    have h1 : u₂ = α (t₂ : hypSU h 2 1) := rfl
    rw [h1, ← map_pow]
    exact MonoidHom.mem_ker.1 ht₂5
  have hu₁ne : u₁ ≠ 1 := by
    intro h1
    have hmem : (t₁ : hypSU h 2 1) ∈ α.ker := MonoidHom.mem_ker.2 h1
    rw [hker] at hmem
    have hz1 : t₁ ∈ Zc := Subgroup.mem_subgroupOf.2 hmem
    obtain ⟨c, hc5, hc⟩ := hZc_coord t₁ hz1
    have het : e t₁ = (w, w) := by
      rw [show t₁ = e.symm (w, w) from rfl]
      exact e.apply_symm_apply _
    have hwc : w = c := congrArg Prod.fst (het.symm.trans hc)
    have hw5eq : w ^ 5 = 1 := by rw [hwc, hc5]
    have hdvd : orderOf w ∣ 5 := orderOf_dvd_iff_pow_eq_one.mpr hw5eq
    rw [hword] at hdvd
    norm_num at hdvd
  have hu₂ne : u₂ ≠ 1 := by
    intro h1
    have hmem : (t₂ : hypSU h 2 1) ∈ α.ker := MonoidHom.mem_ker.2 h1
    rw [hker] at hmem
    have hz2 : t₂ ∈ Zc := Subgroup.mem_subgroupOf.2 hmem
    have h2 : (w ^ 5, 1) ∈ Zc.map e.toMonoidHom := by
      refine Subgroup.mem_map.2 ⟨t₂, hz2, ?_⟩
      rw [show t₂ = e.symm (w ^ 5, 1) from rfl]
      exact e.apply_symm_apply _
    have h4 := hEdiag (w ^ 5, 1) h2
    simp at h4
    have hdvd : orderOf w ∣ 5 := orderOf_dvd_iff_pow_eq_one.mpr h4
    rw [hword] at hdvd
    norm_num at hdvd
  have hu₁ord : orderOf u₁ = 5 := orderOf_eq_prime hu₁5 hu₁ne
  have hu₂ord : orderOf u₂ = 5 := orderOf_eq_prime hu₂5 hu₂ne
  have hind : Subgroup.zpowers u₁ ⊓ Subgroup.zpowers u₂ = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.1 hy
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hy1
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hy2
    have hsub : u₁ ^ i = u₂ ^ j := hi.trans hj.symm
    have hmem : (t₁ : hypSU h 2 1) ^ i * (t₂ : hypSU h 2 1) ^ (-j) ∈ α.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_zpow, map_zpow]
      change u₁ ^ i * u₂ ^ (-j) = 1
      rw [hsub]
      simp
    rw [hker] at hmem
    have hzT : (t₁ : hypSU h 2 1) ^ i * (t₂ : hypSU h 2 1) ^ (-j) ∈ hypTorus h 2 1 :=
      l2cr_su5t_scalars_le_torus h hmem
    let z : ↥(hypTorus h 2 1) :=
      ⟨(t₁ : hypSU h 2 1) ^ i * (t₂ : hypSU h 2 1) ^ (-j), hzT⟩
    have hz : z ∈ Zc := Subgroup.mem_subgroupOf.2 hmem
    obtain ⟨c, hc5, hc⟩ := hZc_coord z hz
    have hco : (w ^ i * (w ^ 5) ^ (-j), w ^ i) = (c, c) := by
      have hz' : z = t₁ ^ i * t₂ ^ (-j) := by
        apply Subtype.ext
        rfl
      have het₁ : e t₁ = (w, w) := by
        rw [show t₁ = e.symm (w, w) from rfl]
        exact e.apply_symm_apply _
      have het₂ : e t₂ = (w ^ 5, 1) := by
        rw [show t₂ = e.symm (w ^ 5, 1) from rfl]
        exact e.apply_symm_apply _
      have h1 : e z = (w ^ i * (w ^ 5) ^ (-j), w ^ i) := by
        rw [hz', map_mul, map_zpow, map_zpow, het₁, het₂]
        simp
      rw [← h1]
      exact hc
    simp only [Prod.mk.injEq] at hco
    have hw5j : (w ^ 5) ^ (-j) = 1 := by
      have hh : w ^ i * (w ^ 5) ^ (-j) = w ^ i * 1 := by
        rw [mul_one]
        exact hco.1.trans hco.2.symm
      exact mul_left_cancel hh
    have h5j : (5 : ℤ) ∣ j := by
      have hh : (5 : ℤ) ∣ -j := by
        have := orderOf_dvd_iff_zpow_eq_one.mpr hw5j
        rwa [hw5ord] at this
      exact dvd_neg.mp hh
    have h5i : (5 : ℤ) ∣ i := by
      have hwi5 : (w ^ i) ^ (5 : ℤ) = 1 := by
        rw [hco.2]
        exact hc5
      have hh : ((orderOf w : ℕ) : ℤ) ∣ i * 5 := by
        rw [orderOf_dvd_iff_zpow_eq_one, _root_.zpow_mul]
        exact hwi5
      rw [hword] at hh
      norm_num at hh
      have hh' : (5 : ℤ) * 5 ∣ 5 * i := by
        rw [mul_comm 5 i]
        exact hh
      exact (mul_dvd_mul_iff_left (by norm_num : (5 : ℤ) ≠ 0)).1 hh'
    have hui : u₁ ^ i = 1 := by
      rw [← orderOf_dvd_iff_zpow_eq_one, hu₁ord]
      exact h5i
    rw [← hi, hui]
  let A := ↥(Subgroup.zpowers u₁) × ↥(Subgroup.zpowers u₂)
  let f : A →* X :=
    { toFun := fun x => (x.1 : X) * (x.2 : X)
      map_one' := by simp
      map_mul' := fun x y => by
        have hx2 : ((x.2 : ↥(Subgroup.zpowers u₂)) : X) * ((y.1 : ↥(Subgroup.zpowers u₁)) : X) =
            ((y.1 : ↥(Subgroup.zpowers u₁)) : X) * ((x.2 : ↥(Subgroup.zpowers u₂)) : X) := by
          have hc : Commute u₁ u₂ := by
            have h1 : u₁ = α (t₁ : hypSU h 2 1) := rfl
            have h2 : u₂ = α (t₂ : hypSU h 2 1) := rfl
            rw [h1, h2, Commute, SemiconjBy]
            simpa only [map_mul] using congrArg α (hypTorus_comm h ht₁ ht₂)
          obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 x.2.2
          obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 y.1.2
          rw [← hn, ← hm]
          exact (hc.symm.zpow_zpow n m).eq
        change ((x.1 : X) * (y.1 : X)) * ((x.2 : X) * (y.2 : X)) =
            ((x.1 : X) * (x.2 : X)) * ((y.1 : X) * (y.2 : X))
        calc ((x.1 : X) * (y.1 : X)) * ((x.2 : X) * (y.2 : X))
            = (x.1 : X) * ((y.1 : X) * ((x.2 : X) * (y.2 : X))) := by group
          _ = (x.1 : X) * (((y.1 : X) * (x.2 : X)) * (y.2 : X)) := by group
          _ = (x.1 : X) * (((x.2 : X) * (y.1 : X)) * (y.2 : X)) := by rw [← hx2]
          _ = ((x.1 : X) * (x.2 : X)) * ((y.1 : X) * (y.2 : X)) := by group }
  have hpow : ∀ a : A, a ^ 5 = 1 := by
    intro a
    apply Prod.ext
    · apply Subtype.ext
      change ((a.1 : X)) ^ 5 = 1
      have hd := orderOf_dvd_of_mem_zpowers (x := u₁) a.1.2
      rw [hu₁ord] at hd
      exact orderOf_dvd_iff_pow_eq_one.mp hd
    · apply Subtype.ext
      change ((a.2 : X)) ^ 5 = 1
      have hd := orderOf_dvd_of_mem_zpowers (x := u₂) a.2.2
      rw [hu₂ord] at hd
      exact orderOf_dvd_iff_pow_eq_one.mp hd
  have hA : Nat.card A = 5 ^ 2 := by
    rw [Nat.card_prod, Nat.card_zpowers, Nat.card_zpowers, hu₁ord, hu₂ord, ← pow_two]
  have hkerf : ∀ x : A, f x = 1 → x = 1 := by
    intro x hx
    have hx1 : (x.1 : X) = ((x.2 : X))⁻¹ := by
      have hh := congrArg (fun z : X => (x.1 : X)⁻¹ * z) hx
      simp only [f, MonoidHom.coe_mk, OneHom.coe_mk, mul_one] at hh
      have h2 : (x.2 : X) = (x.1 : X)⁻¹ := by simpa [mul_assoc] using hh
      rw [h2, inv_inv]
    have hmem : (x.1 : X) ∈ Subgroup.zpowers u₁ ⊓ Subgroup.zpowers u₂ :=
      ⟨x.1.2, by rw [hx1]; exact (Subgroup.zpowers u₂).inv_mem x.2.2⟩
    rw [hind, Subgroup.mem_bot] at hmem
    have hx2 : (x.2 : X) = 1 := by rw [← _root_.inv_inj, ← hx1, hmem, inv_one]
    exact Prod.ext (Subtype.ext hmem) (Subtype.ext hx2)
  have hf : Function.Injective f := by
    intro x y hxy
    have hxy' : f (x * y⁻¹) = 1 := by rw [map_mul, map_inv, hxy, mul_inv_cancel]
    have h1 := hkerf (x * y⁻¹) hxy'
    rwa [mul_inv_eq_one] at h1
  have hu₁mem : u₁ ∈ (hypTorus h 2 1).map α :=
    Subgroup.mem_map.2 ⟨t₁, ht₁, by rw [show u₁ = α (t₁ : hypSU h 2 1) from rfl]⟩
  have hu₂mem : u₂ ∈ (hypTorus h 2 1).map α :=
    Subgroup.mem_map.2 ⟨t₂, ht₂, by rw [show u₂ = α (t₂ : hypSU h 2 1) from rfl]⟩
  have hfr : f.range ≤ (hypTorus h 2 1).map α := by
    rintro _ ⟨a, rfl⟩
    exact mul_mem (Subgroup.zpowers_le.mpr hu₁mem a.1.2)
      (Subgroup.zpowers_le.mpr hu₂mem a.2.2)
  have hcommA : ∀ a b : A, a * b = b * a := by
    intro a b
    apply Prod.ext
    · apply Subtype.ext
      change (a.1 : X) * (b.1 : X) = (b.1 : X) * (a.1 : X)
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 a.1.2
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 b.1.2
      rw [← hm, ← hn, zpow_mul_comm]
    · apply Subtype.ext
      change (a.2 : X) * (b.2 : X) = (b.2 : X) * (a.2 : X)
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 a.2.2
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 b.2.2
      rw [← hm, ← hn, zpow_mul_comm]
  exact CFSG.SectionRank.le_pRank_of_injective (by norm_num : 1 < 5) hcommA hpow hA f hf hfr

theorem l2cr_su5_torus
    {X : Type} [Group X] [Finite X] {m : ℕ} (hX : IsSU5 X m)
    (hm2 : Even m) (hm : 2 < m ∨ Nat.card (Subgroup.center X) ≠ 1) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpd : p ∣ 2 ^ (2 * m) - 1) (hexc : ¬ List880CRExc X p) :
    ∃ A : Subgroup X, (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ 2 ≤ CFSG.Open.pRank p A ∧
      ∃ S₀ : Subgroup X, IsSylowOf 3 S₀ ⊤ ∧ S₀ ≤ A := by
  have hp5' : 5 ≤ p := hp5
  have hq : CFSG.Open.IsQuasisimple X :=
    ((CFSG.Foundations.SteinbergCA.quasisimple_iff X).2.2.1).1 hX.1
  obtain ⟨K, hK, h, α, hα, hαc⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22s218_u5_exists_cover hq hX.2
  have : Finite K := h.finite
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact p.Prime := ⟨hp⟩
  have hZcard : Nat.card (hypScalars h 2 1) = Nat.gcd 5 (2 ^ m + 1) :=
    card_hypScalars h (by norm_num)
  have hker_le : α.ker ≤ hypScalars h 2 1 := fun s hs =>
    (hαc s).1 (by rw [MonoidHom.mem_ker.1 hs]; exact Subgroup.one_mem _)
  have hker_dvd5 : Nat.card α.ker ∣ 5 :=
    (Subgroup.card_dvd_of_le hker_le).trans (hZcard ▸ Nat.gcd_dvd_left 5 _)
  have h3ker : ¬ 3 ∣ Nat.card α.ker := fun hd => by
    have : 3 ∣ 5 := hd.trans hker_dvd5
    omega
  obtain ⟨S₀', hS₀'syl, hS₀'T⟩ := l2cr_su5t_sylow_three h hm2
  have hS₀'ker : S₀' ⊓ α.ker = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxS, hxK⟩ := hx
    obtain ⟨k, hk⟩ := hS₀'syl.isPGroup.exists_orderOf_eq_pow ⟨x, hxS⟩
    rw [← Subgroup.orderOf_coe] at hk
    have hdvd : orderOf x ∣ Nat.card α.ker := by
      have hh := orderOf_dvd_natCard (⟨x, hxK⟩ : α.ker)
      rwa [← Subgroup.orderOf_coe] at hh
    rw [hk] at hdvd
    have hk0 : k = 0 := by
      by_contra hk0
      exact h3ker ((dvd_pow_self 3 hk0).trans hdvd)
    rw [hk0, pow_zero] at hk
    exact orderOf_eq_one_iff.mp hk
  have hS₀card : Nat.card ↥(S₀'.map α) = Nat.card ↥S₀' := by
    have hh := l2cr_su5t_card_map_mul_card_inf_ker α S₀'
    rw [hS₀'ker, Subgroup.card_bot, mul_one] at hh
    exact hh
  have hquot : Nat.card X = Nat.card (hypSU h 2 1 ⧸ α.ker) :=
    (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective (φ := α) hα).toEquiv).symm
  have hmul : Nat.card X * Nat.card α.ker = Nat.card (hypSU h 2 1) := by
    rw [hquot]
    exact (Subgroup.card_eq_card_quotient_mul_card_subgroup α.ker).symm
  have hfacX : (Nat.card (hypSU h 2 1)).factorization 3 = (Nat.card X).factorization 3 := by
    rw [← hmul, Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne'), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd h3ker, add_zero]
  have hS₀syl : IsSylowOf 3 (S₀'.map α) ⊤ := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card le_top ?_
    rw [hS₀card, CFSG.ABGLocalTools.IsSylowOf.card_eq hS₀'syl, Subgroup.card_top,
      Subgroup.card_top, hfacX]
  have hpK : p ∣ Nat.card Kˣ := by
    rw [Nat.card_units, h.card]
    exact hpd
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p hpK
  have hrank : 2 ≤ CFSG.Open.pRank p ((hypTorus h 2 1).map α) := by
    by_cases hp5' : p = 5
    · by_cases hinj : Function.Injective α
      · rw [CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective p hp _ hinj]
        exact l2cr_su5t_torus_pRank h hp hζ
      ·
        have hker_ne : α.ker ≠ ⊥ := fun hb => hinj ((MonoidHom.ker_eq_bot_iff α).1 hb)
        have hker1 : Nat.card α.ker ≠ 1 := fun h1 => hker_ne (Subgroup.card_eq_one.1 h1)
        have hker5 : Nat.card α.ker = 5 :=
          ((Nat.dvd_prime (by norm_num)).1 hker_dvd5).resolve_left hker1
        have h5q : 5 ∣ 2 ^ m + 1 := by
          have h1 : Nat.card α.ker ∣ Nat.gcd 5 (2 ^ m + 1) := by
            rw [← hZcard]; exact Subgroup.card_dvd_of_le hker_le
          rw [hker5] at h1
          exact h1.trans (Nat.gcd_dvd_right 5 _)
        have hkereq : α.ker = hypScalars h 2 1 :=
          le_antisymm hker_le
            (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22s218_u5_scalars_le_ker h α hαc h5q hinj)
        by_cases h25 : 25 ∣ 2 ^ m + 1
        · rw [hp5']
          exact l2cr_su5t_pRank_five h α hkereq h25
        · exfalso
          have hZ : Subgroup.center X = ⊥ :=
            CFSG.LocalAnalysis.UniquenessCase.UC22.uc22s218_u5_center_eq_bot h α hα hαc h5q hinj
          have hZcard1 : Nat.card (Subgroup.center X) = 1 := by rw [hZ, Subgroup.card_bot]
          rcases hm with hm2' | hZne
          · exact hexc ⟨hp5', m, hm2', hX, hZcard1, h5q, h25⟩
          · exact hZne hZcard1
    · obtain ⟨E, hET, hEab, hEcard⟩ := l2cr_su5t_torus_elemAbelian h hp hζ
      exact l2cr_su5t_pRank_map_of_elemAbelian h hp α hET hEab hEcard
        (l2cr_su5t_inf_ker_bot h hp α hEcard hp5' hker_dvd5)
  refine ⟨(hypTorus h 2 1).map α, ?_, hrank, S₀'.map α, hS₀syl, Subgroup.map_mono hS₀'T⟩
  rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
  rw [← map_mul, ← map_mul, hypTorus_comm h hs ht]

theorem l2cr_su5_dvd (hGA : CFSG.Open.GriessAllModelsStatement) {X : Type} [Group X] [Finite X]
    {m : ℕ} (hX : IsSU5 X m) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpr : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X)) : p ∣ 2 ^ (2 * m) - 1 := by
  have hsq : 2 ^ (2 * m) - 1 = (2 ^ m + 1) * (2 ^ m - 1) := by
    have h1 : 2 ^ (2 * m) = (2 ^ m) ^ 2 := by rw [← pow_mul, mul_comm]
    rw [h1]
    have := Nat.sq_sub_sq (2 ^ m) 1
    simpa using this
  rw [hsq]
  rcases l2pri_su5 hGA hX hp hp5 hpr with h | ⟨h, -⟩
  · exact h.mul_right _
  · exact ((Nat.modEq_iff_dvd' Nat.one_le_two_pow).1 h.symm).mul_left _

theorem l2cr_su5 (hGA : CFSG.Open.GriessAllModelsStatement)
    {X : Type} [Group X] [Finite X]
    {m : ℕ} (hX : IsSU5 X m) (hm : 2 < m ∨ Nat.card (Subgroup.center X) ≠ 1)
    (h3 : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 2) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpr : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X)) (hexc : ¬ List880CRExc X p) {S : Subgroup X}
    (hS : IsSylowOf 3 S ⊤) :
    0 < CFSG.Open.pRank p (centralizer (S : Set X)) ∧
      ∀ e ∈ S, orderOf e = 3 → 2 ≤ CFSG.Open.pRank p (centralizer ({e} : Set X)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center X) := not_three_dvd_center_of_isSU5 hGA hX
  have hm2 : Even m := by
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    have h3d : 3 ∣ 2 ^ m + 1 := by
      have := Odd.nat_add_dvd_pow_add_pow 2 1 hodd
      simpa using this
    have hge : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (X ⧸ Subgroup.center X)) :=
      CFSG.Blueprint.LieModel.le_pRank_psu_of_dvd hX.2 Nat.prime_three h3d (by norm_num)
        (Or.inl (by norm_num))
    rw [CFSG.SectionRank.pRank_quotient_eq (Subgroup.center X) hZ3, h3] at hge
    omega
  obtain ⟨A, hAab, hAr, S₀, hS₀, hS₀A⟩ :=
    l2cr_su5_torus hX hm2 hm hp hp5 (l2cr_su5_dvd hGA hX hp hp5 hpr) hexc
  obtain ⟨P₀, hP₀⟩ := l2cr_exists_sylow_coe_eq hS₀
  obtain ⟨-, hS3, -⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hS
  obtain ⟨g, hg⟩ := l2cr_exists_map_conj_le_sylow P₀ hS3
  rw [hP₀] at hg
  set A' : Subgroup X := A.map (MulAut.conj g⁻¹).toMonoidHom with hA'
  have hSA : ∀ x ∈ S, x ∈ A' := by
    intro x hx
    have hxA : g * x * g⁻¹ ∈ A := hS₀A (hg ⟨x, hx, by simp [MulAut.conj_apply]⟩)
    exact ⟨g * x * g⁻¹, hxA, by simp; group⟩
  have hA'ab : ∀ a ∈ A', ∀ b ∈ A', a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hAab a ha b hb]
  have hr' : 2 ≤ CFSG.Open.pRank p A' := by
    rw [hA', CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective p hp _
      (MulAut.conj g⁻¹).injective]
    exact hAr
  refine ⟨lt_of_lt_of_le (by norm_num)
    (hr'.trans (CFSG.SectionRank.pRank_mono hp.one_lt (fun a ha => ?_))), fun e he he3 => ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hA'ab x (hSA x hx) a ha
  · refine hr'.trans (CFSG.SectionRank.pRank_mono hp.one_lt (fun a ha => ?_))
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hA'ab x (hSA x he) a ha

theorem list880CentralizerRanks_holds :
    List880CentralizerRanks := by
  have hGA : CFSG.Open.GriessAllModelsStatement :=
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  intro X H _ _ _ _ ι hinj hnorm hL hJ2 h3 p hp hp5 hpr hH hexc S hS
  unfold List880 at hL
  rcases hL with hM | hJ2' | hHS | hRu | hJ4 | h6 | h7 | h22 | hA6 | hA7 | hA8 | hL5 | hL3 |
    ⟨n, hsp⟩ | ⟨n, hg⟩ | ⟨m, hm, hsu⟩ | hsuf
  · exfalso
    have := l2pri_mathieu hM hp hp5
    omega
  · exact absurd hJ2' hJ2
  · obtain ⟨hp5', -⟩ := l2pri_hs hHS hp hp5 hpr
    subst hp5'
    exact l2cr_sporadic ι hinj hnorm (Or.inl ⟨hHS, rfl⟩) hp hH S
  · obtain ⟨hp5', -⟩ := l2pri_ru hRu hp hp5 hpr
    subst hp5'
    exact l2cr_sporadic ι hinj hnorm (Or.inr (Or.inl ⟨hRu, rfl⟩)) hp hH S
  · obtain ⟨hp11, -⟩ := l2pri_j4 hJ4 hp hp5 hpr
    subst hp11
    exact l2cr_sporadic ι hinj hnorm (Or.inr (Or.inr ⟨hJ4, rfl⟩)) hp hH S
  · exfalso
    have := l2pri_not_cover (Or.inl h6) hp hp5
    omega
  · exfalso
    have := l2pri_not_cover (Or.inr (Or.inl h7)) hp hp5
    omega
  · exfalso
    have := l2pri_not_cover (Or.inr (Or.inr h22)) hp hp5
    omega
  · exfalso
    have := l2pri_alt (Or.inl rfl) hA6 hp hp5
    omega
  · exfalso
    have := l2pri_alt (Or.inr (Or.inl rfl)) hA7 hp hp5
    omega
  · exfalso
    have := l2pri_alt (Or.inr (Or.inr rfl)) hA8 hp hp5
    omega
  · exfalso
    have := l2pri_psl52 hL5 hp hp5
    omega
  · exfalso
    have := l2pri_psl33 hL3 hp hp5
    omega
  · obtain ⟨-, hc, hr2⟩ := l2pri_sp4 hsp hp hp5 hpr
    exact l2cr_sp4 ι hinj hnorm hsp hp hp5 hc hr2.le hH hS
  · rcases hg with ⟨-, hu⟩ | ⟨hn2, hg2⟩
    · exfalso
      have := l2pri_psu33 hu hp hp5
      omega
    · obtain ⟨hc, hr2⟩ := l2pri_g2 hn2 hg2 hp hp5 hpr
      exact l2cr_g2 ι hinj hnorm hn2 hg2 hp hp5 hc hr2.le hH hS
  · obtain ⟨hA, hB⟩ := l2cr_su5 hGA hsu (Or.inl hm) h3 hp hp5 hpr hexc hS
    exact l2cr_lift ι hinj hp hA hB
  · obtain ⟨hsu2, hZ5⟩ := hsuf
    obtain ⟨hA, hB⟩ := l2cr_su5 hGA hsu2 (Or.inr (by rw [hZ5]; norm_num)) h3 hp hp5 hpr hexc hS
    exact l2cr_lift ι hinj hp hA hB

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
