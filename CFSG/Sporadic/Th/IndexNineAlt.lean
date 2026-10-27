module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicPermutesPackage
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoSetupSylow
public import CFSG.Mathlib.Decide.Bounded
public import CFSG.Sporadic.Schreier.J4SSylow
public import CFSG.GH74.SmallRanks.AltM11
public import CFSG.GH74.Statements
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.JOneRoute
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.NonSquare
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankBound
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.Remaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.IsolatedSubgroup
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoStatements
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.WalterRoute
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.TheoremC
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.InnerCoverBase
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalFamily
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearStrong
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.Hyp
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicPermutesCover
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Quasithin.Background.A1cA132Action
public import CFSG.Quasithin.Background.A1cA133Three
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.Background.E3
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.Quasithin.Background.E3Uniq
public import CFSG.Quasithin.Background.E4Solv
public import CFSG.Quasithin.Background.F6Amalgams
public import CFSG.Quasithin.Background.F6SolvableQuotient
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.HFF
public import CFSG.Quasithin.Background.HPairBridge
public import CFSG.Quasithin.Background.HSL3Inner
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4OutBase
public import CFSG.Quasithin.EmptyFaithful.S14110
public import CFSG.Quasithin.EmptyFaithful.S14117
public import CFSG.Quasithin.EmptyFaithful.S143Pre
public import CFSG.Quasithin.EmptyFaithful.S153Baum
public import CFSG.Quasithin.EmptyFaithful.S153Nine
public import CFSG.Quasithin.EmptyFaithful.T1531Close2
public import CFSG.Quasithin.EmptyFaithful.T1531In66b
public import CFSG.Quasithin.EmptyFaithfulMultiple.InputB19Proof
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import CFSG.Quasithin.Vol2.Ch4Sec1Lem415
public import CFSG.Quasithin.Vol2.Ch4Sec4Lem445
public import CFSG.Sporadic.Schreier.J4SCommGenBase1
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9

public section

namespace CFSG.Sporadic.Th

open scoped CFSG.Decide.Bounded
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

namespace IndexNineA9

@[expose] def mpoint (p : Fin 9) : Fin 9 := if p = 0 then 1 else 0

abbrev IsPart (x : Fin 9 × Finset (Fin 9)) : Prop :=
  x.1 ∉ x.2 ∧ x.2.card = 4 ∧ mpoint x.1 ∈ x.2

abbrev Part := {x : Fin 9 × Finset (Fin 9) // IsPart x}

@[expose] def q (i : Fin 4) : Fin 9 := ⟨i.val, by omega⟩

@[expose] def B0 : Finset (Fin 9) := Finset.univ.image q

theorem B0_eq : B0 = {0, 1, 2, 3} := by decide

@[expose] def part0 : Part := ⟨(8, B0), by simp [IsPart, mpoint, B0_eq]⟩

@[expose] def canonBlock (p : Fin 9) (B : Finset (Fin 9)) : Finset (Fin 9) :=
  if mpoint p ∈ B then B else Finset.univ \ insert p B

@[expose] def canon (x : Fin 9 × Finset (Fin 9)) : Fin 9 × Finset (Fin 9) :=
  (x.1, canonBlock x.1 x.2)

@[expose] def actPair (g : Equiv.Perm (Fin 9)) (x : Fin 9 × Finset (Fin 9)) :
    Fin 9 × Finset (Fin 9) :=
  canon (g x.1, x.2.image g)

theorem mpoint_ne (p : Fin 9) : mpoint p ≠ p := by
  unfold mpoint
  split_ifs with h
  · rw [h]; exact one_ne_zero
  · exact fun h0 => h h0.symm

theorem mem_diff_insert {x p : Fin 9} {B : Finset (Fin 9)} :
    x ∈ (Finset.univ \ insert p B : Finset (Fin 9)) ↔ x ≠ p ∧ x ∉ B := by
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert]
  tauto

theorem sdiff_insert_self {p : Fin 9} {B : Finset (Fin 9)} (hp : p ∉ B) :
    (Finset.univ : Finset (Fin 9)) \ insert p (Finset.univ \ insert p B) = B := by
  ext x
  simp only [mem_diff_insert]
  constructor
  · rintro ⟨hxp, hx⟩
    by_contra hxB
    exact hx ⟨hxp, hxB⟩
  · intro hx
    exact ⟨fun h => hp (h ▸ hx), fun hx' => hx'.2 hx⟩

theorem isPart_canon {p : Fin 9} {B : Finset (Fin 9)} (hp : p ∉ B) (hB : B.card = 4) :
    IsPart (p, canonBlock p B) := by
  by_cases h : mpoint p ∈ B
  · have hB' : canonBlock p B = B := by simp [canonBlock, h]
    refine ⟨?_, ?_, ?_⟩
    · rw [hB']; exact hp
    · rw [hB']; exact hB
    · rw [hB']; exact h
  · have hD : canonBlock p B = Finset.univ \ insert p B := by simp [canonBlock, h]
    have hins : (insert p B).card = 5 := by
      rw [Finset.card_insert_of_notMem hp, hB]
    have hcard : (Finset.univ \ insert p B : Finset (Fin 9)).card = 4 := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, hins]
      norm_num
    refine ⟨?_, ?_, ?_⟩
    · rw [hD]
      exact fun hc => (mem_diff_insert.mp hc).1 rfl
    · rw [hD]; exact hcard
    · rw [hD, mem_diff_insert]
      exact ⟨mpoint_ne p, h⟩

theorem canon_compl {p : Fin 9} {B : Finset (Fin 9)} (hp : p ∉ B) (hB : B.card = 4) :
    canonBlock p (Finset.univ \ insert p B) = canonBlock p B := by
  by_cases h : mpoint p ∈ B
  · have hm : mpoint p ∉ (Finset.univ \ insert p B : Finset (Fin 9)) :=
      fun hc => (mem_diff_insert.mp hc).2 h
    simp only [canonBlock, h, hm, if_true, if_false]
    exact sdiff_insert_self hp
  · have hm : mpoint p ∈ (Finset.univ \ insert p B : Finset (Fin 9)) := by
      rw [mem_diff_insert]
      exact ⟨mpoint_ne p, h⟩
    simp only [canonBlock, h, hm, if_false, if_true]

theorem image_diff_insert (g : Equiv.Perm (Fin 9)) (p : Fin 9) (B : Finset (Fin 9)) :
    (Finset.univ \ insert p B : Finset (Fin 9)).image g =
      Finset.univ \ insert (g p) (B.image g) := by
  ext y
  simp only [Finset.mem_image, mem_diff_insert]
  constructor
  · rintro ⟨x, ⟨hxp, hxB⟩, rfl⟩
    refine ⟨fun h => hxp (g.injective h), ?_⟩
    intro hy
    obtain ⟨b, hb, hgb⟩ := hy
    exact hxB (g.injective hgb ▸ hb)
  · rintro ⟨hyp, hyB⟩
    refine ⟨g.symm y, ⟨?_, ?_⟩, g.apply_symm_apply y⟩
    · intro h; exact hyp (by simpa using congrArg g h)
    · intro h
      exact hyB ⟨g.symm y, h, g.apply_symm_apply y⟩

theorem canon_image (g : Equiv.Perm (Fin 9)) {p : Fin 9} {B : Finset (Fin 9)}
    (hp : p ∉ B) (hB : B.card = 4) :
    canonBlock (g p) ((canonBlock p B).image g) = canonBlock (g p) (B.image g) := by
  have hp' : g p ∉ B.image g := by
    intro hmem
    obtain ⟨b, hb, hgb⟩ := Finset.mem_image.1 hmem
    exact hp (g.injective hgb ▸ hb)
  have hcard : (B.image g).card = 4 := by
    rw [Finset.card_image_of_injective B g.injective]
    exact hB
  by_cases h : mpoint p ∈ B
  · rw [show canonBlock p B = B by simp [canonBlock, h]]
  · have hD : canonBlock p B = Finset.univ \ insert p B := by simp [canonBlock, h]
    rw [hD, image_diff_insert]
    exact canon_compl hp' hcard

theorem actPair_one {p : Fin 9} {B : Finset (Fin 9)} (h : mpoint p ∈ B) :
    actPair 1 (p, B) = (p, B) := by
  simp only [actPair, canon, Equiv.Perm.coe_one, id_eq, Finset.image_id, canonBlock, h,
    if_true]

theorem actPair_mem {g : Equiv.Perm (Fin 9)} {p : Fin 9} {B : Finset (Fin 9)}
    (hp : p ∉ B) (hB : B.card = 4) :
    IsPart (actPair g (p, B)) := by
  have hp' : g p ∉ B.image g := by
    intro hmem
    obtain ⟨b, hb, hgb⟩ := Finset.mem_image.1 hmem
    exact hp (g.injective hgb ▸ hb)
  have hcard : (B.image g).card = 4 := by
    rw [Finset.card_image_of_injective B g.injective]
    exact hB
  exact isPart_canon hp' hcard

theorem actPair_mul (g h : Equiv.Perm (Fin 9)) (p : Fin 9) (B : Finset (Fin 9))
    (hp : p ∉ B) (hB : B.card = 4) :
    actPair g (actPair h (p, B)) = actPair (g * h) (p, B) := by
  have hp' : h p ∉ B.image h := by
    intro hmem
    obtain ⟨b, hb, hgb⟩ := Finset.mem_image.1 hmem
    exact hp (h.injective hgb ▸ hb)
  have hcard : (B.image h).card = 4 := by
    rw [Finset.card_image_of_injective B h.injective]
    exact hB
  have himg : (B.image (g * h) : Finset (Fin 9)) = (B.image h).image g := by
    simp [Equiv.Perm.coe_mul, Finset.image_image]
  simp only [actPair, canon]
  rw [himg, canon_image g hp' hcard]
  rfl

instance : MulAction (Equiv.Perm (Fin 9)) Part where
  smul g x := ⟨actPair g x.1, actPair_mem x.2.1 x.2.2.1⟩
  one_smul x := Subtype.ext (actPair_one x.2.2.2)
  mul_smul g h x := Subtype.ext (actPair_mul g h x.1.1 x.1.2 x.2.1 x.2.2.1).symm

abbrev Alt := alternatingGroup (Fin 9)

instance : MulAction Alt Part where
  smul g x := (g : Equiv.Perm (Fin 9)) • x
  one_smul x := one_smul (Equiv.Perm (Fin 9)) x
  mul_smul g h x := mul_smul (g : Equiv.Perm (Fin 9)) (h : Equiv.Perm (Fin 9)) x

theorem part_ext {x y : Part} (h : x.1 = y.1) : x = y := Subtype.ext h

theorem card_Part : Nat.card Part = 315 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

@[expose] def srcEmb : (Fin 4 ⊕ Fin 4) ⊕ Fin 1 → Fin 9
  | Sum.inl (Sum.inl i) => q i
  | Sum.inl (Sum.inr i) => ⟨i.val + 4, by omega⟩
  | Sum.inr _ => 8

@[expose] def tgtEmb (p : Fin 9) (B D : Finset (Fin 9)) (eB : ↥B ≃ Fin 4) (eD : ↥D ≃ Fin 4) :
    (Fin 4 ⊕ Fin 4) ⊕ Fin 1 → Fin 9
  | Sum.inl (Sum.inl i) => ((eB.symm i : ↥B) : Fin 9)
  | Sum.inl (Sum.inr i) => ((eD.symm i : ↥D) : Fin 9)
  | Sum.inr _ => p

theorem A9_transitive (x : Part) : ∃ g : Alt, g • part0 = x := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨p, B⟩ := x
  have hp : p ∉ B := hx.1
  have hB : B.card = 4 := hx.2.1
  have hm : mpoint p ∈ B := hx.2.2
  let D : Finset (Fin 9) := Finset.univ \ insert p B
  have hpD : p ∉ D := by simp [D]
  have hins : (insert p B).card = 5 := by
    rw [Finset.card_insert_of_notMem hp, hB]
  have hD : D.card = 4 := by
    show (Finset.univ \ insert p B : Finset (Fin 9)).card = 4
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, hins]
    norm_num
  have hBD' : ∀ a ∈ B, a ∉ D := by
    intro a ha haD
    exact (Finset.mem_sdiff.1 haD).2 (Finset.mem_insert_of_mem ha)
  let eB : ↥B ≃ Fin 4 := Finset.equivFinOfCardEq hB
  let eD : ↥D ≃ Fin 4 := Finset.equivFinOfCardEq hD
  let f : (Fin 4 ⊕ Fin 4) ⊕ Fin 1 → Fin 9 := srcEmb
  let g : (Fin 4 ⊕ Fin 4) ⊕ Fin 1 → Fin 9 := tgtEmb p B D eB eD
  have hf : Function.Injective f := by decide
  have hg : Function.Injective g := by
    intro a b hab
    rcases a with ((i | i) | s) <;> rcases b with ((j | j) | t)
    · change ((eB.symm i : ↥B) : Fin 9) = ((eB.symm j : ↥B) : Fin 9) at hab
      exact congrArg (Sum.inl ∘ Sum.inl) (eB.symm.injective (Subtype.ext hab))
    · change ((eB.symm i : ↥B) : Fin 9) = ((eD.symm j : ↥D) : Fin 9) at hab
      exfalso
      exact (hBD' _ (eB.symm i).2) (hab ▸ (eD.symm j).2)
    · change ((eB.symm i : ↥B) : Fin 9) = p at hab
      exfalso
      exact hp (hab ▸ (eB.symm i).2)
    · change ((eD.symm i : ↥D) : Fin 9) = ((eB.symm j : ↥B) : Fin 9) at hab
      exfalso
      exact (hBD' _ (eB.symm j).2) (hab.symm ▸ (eD.symm i).2)
    · change ((eD.symm i : ↥D) : Fin 9) = ((eD.symm j : ↥D) : Fin 9) at hab
      exact congrArg (Sum.inl ∘ Sum.inr) (eD.symm.injective (Subtype.ext hab))
    · change ((eD.symm i : ↥D) : Fin 9) = p at hab
      exfalso
      exact hpD (hab ▸ (eD.symm i).2)
    · change p = ((eB.symm j : ↥B) : Fin 9) at hab
      exfalso
      exact hp (hab.symm ▸ (eB.symm j).2)
    · change p = ((eD.symm j : ↥D) : Fin 9) at hab
      exfalso
      exact hpD (hab.symm ▸ (eD.symm j).2)
    · exact congrArg Sum.inr (Subsingleton.elim s t)
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  have hσ8 : σ 8 = p := by
    have := hσ (Sum.inr (0 : Fin 1))
    rw [show f (Sum.inr (0 : Fin 1)) = 8 from rfl,
      show g (Sum.inr (0 : Fin 1)) = p from rfl] at this
    exact this
  have hσi : ∀ i : Fin 4, σ (q i) = ((eB.symm i : ↥B) : Fin 9) := by
    intro i
    have := hσ (Sum.inl (Sum.inl i))
    rw [show f (Sum.inl (Sum.inl i)) = q i from rfl,
      show g (Sum.inl (Sum.inl i)) = ((eB.symm i : ↥B) : Fin 9) from rfl] at this
    exact this
  have hσB : (B0.image σ) = B := by
    have h1 : B0.image σ =
        Finset.univ.image (fun i : Fin 4 => σ (q i)) := by
      rw [B0, Finset.image_image]
      rfl
    rw [h1]
    have h2 : (fun i : Fin 4 => σ (q i)) = fun i => ((eB.symm i : ↥B) : Fin 9) := by
      funext i; exact hσi i
    rw [h2]
    ext y
    constructor
    · intro hy
      rw [Finset.mem_image] at hy
      obtain ⟨i, -, rfl⟩ := hy
      exact (eB.symm i).2
    · intro hy
      rw [Finset.mem_image]
      exact ⟨eB ⟨y, hy⟩, Finset.mem_univ _, by simp⟩
  have hact : actPair σ (part0 : Part).1 = (p, B) := by
    simp only [part0, actPair, canon, hσ8, hσB]
    rw [show canonBlock p B = B by simp [canonBlock, hm]]
  by_cases hsign : Equiv.Perm.sign σ = 1
  · exact ⟨⟨σ, Equiv.Perm.mem_alternatingGroup.mpr hsign⟩, part_ext hact⟩
  · refine ⟨⟨σ * Equiv.swap 0 1, ?_⟩, ?_⟩
    · rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul,
        Equiv.Perm.sign_swap (by decide)]
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
      · exact absurd h hsign
      · rw [h]; decide
    · have hτ : (Equiv.swap (0 : Fin 9) 1 : Equiv.Perm (Fin 9)) • part0 = part0 := by
        apply part_ext
        change actPair (Equiv.swap (0 : Fin 9) 1) (8, B0) = (8, B0)
        simp only [actPair, canon]
        rw [show (Equiv.swap (0 : Fin 9) 1) 8 = 8 from by decide,
          show B0.image (Equiv.swap (0 : Fin 9) 1) = B0 from by decide,
          show canonBlock 8 B0 = B0 by simp [canonBlock, B0_eq, mpoint]]
      show ((σ * Equiv.swap (0 : Fin 9) 1 : Equiv.Perm (Fin 9)) • part0) = ⟨(p, B), hx⟩
      calc (σ * Equiv.swap (0 : Fin 9) 1 : Equiv.Perm (Fin 9)) • part0
          = σ • ((Equiv.swap (0 : Fin 9) 1 : Equiv.Perm (Fin 9)) • part0) :=
              mul_smul _ _ _
        _ = σ • part0 := by rw [hτ]
        _ = ⟨(p, B), hx⟩ := part_ext hact

@[expose] def uGens : List (Equiv.Perm (Fin 9)) :=
  [Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.swap 0 1 * Equiv.swap 4 5,
   Equiv.swap 0 1 * Equiv.swap 6 7, Equiv.swap 0 2 * Equiv.swap 1 3,
   Equiv.swap 4 5 * Equiv.swap 6 7,
   Equiv.swap 0 4 * Equiv.swap 1 5 * Equiv.swap 2 6 * Equiv.swap 3 7]

@[expose] def uWords : List (List Nat) :=
      [
      [],
      [0],
      [1],
      [2],
      [3],
      [4],
      [5],
      [0, 1],
      [0, 2],
      [0, 3],
      [0, 4],
      [0, 5],
      [1, 3],
      [1, 5],
      [2, 3],
      [2, 5],
      [3, 1],
      [3, 2],
      [3, 4],
      [3, 5],
      [4, 5],
      [5, 2],
      [5, 3],
      [0, 2, 5],
      [0, 3, 4],
      [0, 3, 5],
      [0, 4, 5],
      [0, 5, 3],
      [1, 3, 5],
      [1, 5, 3],
      [2, 3, 5],
      [2, 5, 3],
      [3, 1, 5],
      [3, 2, 5],
      [3, 4, 5],
      [3, 5, 3],
      [4, 5, 3],
      [5, 2, 3],
      [5, 3, 2],
      [5, 3, 5],
      [0, 3, 4, 5],
      [0, 3, 5, 3],
      [0, 4, 5, 3],
      [0, 5, 3, 5],
      [1, 3, 5, 3],
      [1, 5, 3, 5],
      [2, 3, 5, 3],
      [2, 5, 3, 5],
      [3, 1, 5, 3],
      [3, 2, 5, 3],
      [3, 4, 5, 3],
      [3, 5, 3, 5],
      [4, 5, 3, 5],
      [5, 2, 3, 5],
      [5, 3, 2, 5],
      [0, 3, 4, 5, 3],
      [0, 3, 5, 3, 5],
      [0, 4, 5, 3, 5],
      [1, 3, 5, 3, 5],
      [2, 3, 5, 3, 5],
      [3, 1, 5, 3, 5],
      [3, 2, 5, 3, 5],
      [3, 4, 5, 3, 5],
      [0, 3, 4, 5, 3, 5]
    ]

@[expose] def evalWord (w : List Nat) : Equiv.Perm (Fin 9) :=
  w.foldr (fun i acc => uGens.getD i 1 * acc) 1

@[expose] def uList : List (Equiv.Perm (Fin 9)) := uWords.map evalWord

theorem uList_length : uList.length = 64 := by decide +kernel

theorem uList_nodup : uList.Nodup := by decide +kernel

theorem uGens_mem : ∀ g ∈ uGens, g ∈ uList := by decide +kernel

theorem uList_left : ∀ x ∈ uList, ∀ g ∈ uGens, g * x ∈ uList := by decide +kernel

theorem uGens_inv : ∀ g ∈ uGens, g * g = 1 := by decide +kernel

theorem uGens_sign : ∀ g ∈ uGens, Equiv.Perm.sign g = 1 := by decide +kernel

theorem uGens_even : ∀ g ∈ uGens, g ∈ Alt := fun g hg =>
  Equiv.Perm.mem_alternatingGroup.mpr (uGens_sign g hg)

theorem uList_fix : ∀ x ∈ uList, actPair x (part0 : Part).1 = part0.1 := by decide +kernel

@[expose] def validFinset : Finset (Fin 9 × Finset (Fin 9)) := Finset.univ.filter IsPart

theorem uniqueCheck : ∀ x ∈ validFinset, (∀ g ∈ uGens, actPair g x = x) → x = part0.1 := by
  decide +kernel

theorem mem_uGens_getD (i : Nat) : uGens.getD i 1 = 1 ∨ uGens.getD i 1 ∈ uGens := by
  by_cases h : i < uGens.length
  · right
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
    exact List.getElem_mem h
  · left
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.not_lt.1 h)]
    rfl

@[expose] def U : Subgroup (Equiv.Perm (Fin 9)) :=
  Subgroup.closure {g : Equiv.Perm (Fin 9) | g ∈ uGens}

theorem evalWord_mem_U (w : List Nat) : evalWord w ∈ U := by
  induction w with
  | nil => exact U.one_mem
  | cons i w ih =>
    rw [show evalWord (i :: w) = uGens.getD i 1 * evalWord w from rfl]
    rcases mem_uGens_getD i with h | h
    · rw [h, one_mul]; exact ih
    · exact U.mul_mem (Subgroup.subset_closure h) ih

theorem uList_mem_U : ∀ x ∈ uList, x ∈ U := by
  intro x hx
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx
  exact evalWord_mem_U w

theorem evalWord_mem_uList (w : List Nat) : evalWord w ∈ uList := by
  induction w with
  | nil => exact List.mem_map.2 ⟨[], by simp [uWords], by simp [evalWord]⟩
  | cons i w ih =>
    rw [show evalWord (i :: w) = uGens.getD i 1 * evalWord w from rfl]
    rcases mem_uGens_getD i with h | h
    · rw [h, one_mul]; exact ih
    · exact uList_left _ ih _ h

theorem evalWord_concat (w1 w2 : List Nat) : evalWord (w1 ++ w2) = evalWord w1 * evalWord w2 := by
  induction w1 with
  | nil => simp [evalWord]
  | cons a l ih =>
    rw [List.cons_append,
      show evalWord (a :: (l ++ w2)) = uGens.getD a 1 * evalWord (l ++ w2) from rfl, ih,
      show evalWord (a :: l) = uGens.getD a 1 * evalWord l from rfl, mul_assoc]

theorem evalWord_append (w : List Nat) (i : Nat) :
    evalWord (w ++ [i]) = evalWord w * uGens.getD i 1 := by
  rw [evalWord_concat]
  rfl

theorem evalWord_reverse (w : List Nat) : evalWord w.reverse = (evalWord w)⁻¹ := by
  induction w with
  | nil => simp [evalWord]
  | cons i w ih =>
    rw [List.reverse_cons, evalWord_append, ih,
      show evalWord (i :: w) = uGens.getD i 1 * evalWord w from rfl, mul_inv_rev]
    rcases mem_uGens_getD i with h | h
    · rw [h, inv_one, mul_one]
    · have hg : (uGens.getD i 1)⁻¹ = uGens.getD i 1 :=
        inv_eq_of_mul_eq_one_right (uGens_inv _ h)
      rw [hg]

theorem uList_inv : ∀ x ∈ uList, x⁻¹ ∈ uList := by
  intro x hx
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx
  rw [← evalWord_reverse]
  exact evalWord_mem_uList _

theorem uList_mul : ∀ x ∈ uList, ∀ y ∈ uList, x * y ∈ uList := by
  intro x hx y hy
  obtain ⟨wx, -, rfl⟩ := List.mem_map.1 hx
  obtain ⟨wy, -, rfl⟩ := List.mem_map.1 hy
  rw [← evalWord_concat]
  exact evalWord_mem_uList _

theorem U_eq_uList : (U : Set (Equiv.Perm (Fin 9))) = {x | x ∈ uList} := by
  apply Set.Subset.antisymm
  · intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy => exact uGens_mem y hy
    | one => exact evalWord_mem_uList []
    | mul x y _ _ hx hy => exact uList_mul x hx y hy
    | inv x _ hx => exact uList_inv x hx
  · intro x hx
    exact uList_mem_U x hx

theorem card_U : Nat.card U = 64 := by
  have hset : (U : Set (Equiv.Perm (Fin 9))) = {x | x ∈ uList} := U_eq_uList
  calc Nat.card U = Nat.card {x // x ∈ uList} :=
        Nat.card_congr (Equiv.subtypeEquivRight (fun x => by
      change x ∈ (U : Set (Equiv.Perm (Fin 9))) ↔ x ∈ uList
      rw [hset]
      exact Iff.rfl))
    _ = uList.length := by
        rw [← Nat.card_congr (List.Nodup.getEquiv uList uList_nodup), Nat.card_fin]
    _ = 64 := uList_length

theorem U_le_Alt : U ≤ Alt := by
  rw [U, Subgroup.closure_le]
  intro g hg
  exact uGens_even g hg

@[expose] def Ubar : Subgroup Alt := U.subgroupOf Alt

theorem card_Ubar : Nat.card Ubar = 64 := by
  rw [Ubar]
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe U_le_Alt).toEquiv]
  exact card_U

theorem card_Alt : Nat.card Alt = 181440 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem isPGroup_Ubar : IsPGroup 2 Ubar :=
  IsPGroup.of_card (n := 6) (by rw [card_Ubar]; norm_num)

theorem isSylowTwoOf_Ubar : CFSG.QuasithinUnique.IsSylowTwoOf Ubar ⊤ := by
  refine ⟨le_top, isPGroup_Ubar, ?_⟩
  have hc : Nat.card (Ubar.subgroupOf ⊤) = Nat.card Ubar :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_top : Ubar ≤ ⊤)).toEquiv
  have hmul : Nat.card (Ubar.subgroupOf ⊤) * (Ubar.subgroupOf ⊤).index =
      Nat.card (⊤ : Subgroup Alt) := Subgroup.card_mul_index (H := Ubar.subgroupOf ⊤)
  rw [Subgroup.card_top, card_Alt, hc, card_Ubar] at hmul
  have hidx : (Ubar.subgroupOf ⊤).index = 2835 := by omega
  rw [hidx]
  norm_num

theorem Ubar_fix : ∀ u ∈ Ubar, u • part0 = part0 := by
  intro u hu
  have hu' : (u : Equiv.Perm (Fin 9)) ∈ uList := by
    have h : (u : Equiv.Perm (Fin 9)) ∈ (U : Set (Equiv.Perm (Fin 9))) := hu
    rwa [U_eq_uList] at h
  exact part_ext (uList_fix _ hu')

theorem Ubar_unique : ∀ d : Alt, (∀ u ∈ Ubar, u • (d • part0) = d • part0) → d • part0 = part0 := by
  intro d hd
  set y : Part := d • part0 with hy
  have hvalid : y.1 ∈ validFinset := by
    rw [validFinset, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, y.2⟩
  have hgens : ∀ g ∈ uGens, actPair g y.1 = y.1 := by
    intro g hg
    have hgA : g ∈ Alt := uGens_even g hg
    have hgU : g ∈ U := Subgroup.subset_closure hg
    have hgUbar : (⟨g, hgA⟩ : Alt) ∈ Ubar := hgU
    have h := congrArg Subtype.val (hd ⟨g, hgA⟩ hgUbar)
    change actPair g (y : Part).1 = (y : Part).1 at h
    exact h
  have hy0 : y.1 = part0.1 := uniqueCheck y.1 hvalid hgens
  exact part_ext hy0

@[expose] def three012 : Equiv.Perm (Fin 9) := Equiv.swap 0 1 * Equiv.swap 1 2

@[expose] def three456 : Equiv.Perm (Fin 9) := Equiv.swap 4 5 * Equiv.swap 5 6

theorem sign_three012 : Equiv.Perm.sign three012 = 1 := by decide

theorem sign_three456 : Equiv.Perm.sign three456 = 1 := by decide

@[expose] def xAlt : Alt := ⟨three012, by rw [Equiv.Perm.mem_alternatingGroup]; exact sign_three012⟩

@[expose] def yAlt : Alt := ⟨three456, by rw [Equiv.Perm.mem_alternatingGroup]; exact sign_three456⟩

theorem xAlt_fix : xAlt • part0 = part0 := by
  apply part_ext
  change actPair three012 (part0 : Part).1 = part0.1
  decide +kernel

theorem yAlt_fix : yAlt • part0 = part0 := by
  apply part_ext
  change actPair three456 (part0 : Part).1 = part0.1
  decide +kernel

theorem xAlt_pow : xAlt ^ 3 = 1 := by
  apply Subtype.ext
  decide

theorem yAlt_pow : yAlt ^ 3 = 1 := by
  apply Subtype.ext
  decide

theorem xAlt_mul_yAlt : xAlt * yAlt = yAlt * xAlt := by
  apply Subtype.ext
  decide

theorem xAlt_ne_one : xAlt ≠ 1 := by
  intro h
  have := congrArg Subtype.val h
  exact absurd this (by decide)

theorem orderOf_xAlt : orderOf xAlt = 3 := orderOf_eq_prime xAlt_pow xAlt_ne_one

theorem yAlt_not_zpowers : yAlt ∉ Subgroup.zpowers xAlt := by
  intro h
  rcases CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.eq_one_or_eq_or_eq_inv_of_mem_zpowers
    orderOf_xAlt h with h1 | h1 | h1
  · exact absurd (congrArg Subtype.val h1) (by decide)
  · exact absurd (congrArg Subtype.val h1) (by decide)
  · exact absurd (congrArg Subtype.val h1) (by decide)

theorem card_stabilizer : Nat.card (MulAction.stabilizer Alt part0) = 9 * Nat.card Ubar := by
  have horbit : MulAction.orbit Alt part0 = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro z
    obtain ⟨g, hg⟩ := A9_transitive z
    exact MulAction.mem_orbit_iff.mpr ⟨g, hg⟩
  have horbitncard : (MulAction.orbit Alt part0).ncard = 315 := by
    rw [horbit, Set.ncard_univ]
    exact card_Part
  have hmul : Nat.card (MulAction.stabilizer Alt part0) *
      (MulAction.stabilizer Alt part0).index = Nat.card Alt := Subgroup.card_mul_index _
  have hidx : (MulAction.stabilizer Alt part0).index = 315 := by
    rw [MulAction.index_stabilizer]
    exact horbitncard
  have hmul2 : Nat.card (MulAction.stabilizer Alt part0) * 315 = 181440 := by
    calc Nat.card (MulAction.stabilizer Alt part0) * 315
        = Nat.card (MulAction.stabilizer Alt part0) *
            (MulAction.stabilizer Alt part0).index :=
          congrArg (fun n => Nat.card (MulAction.stabilizer Alt part0) * n) hidx.symm
      _ = Nat.card Alt := hmul
      _ = 181440 := card_Alt
  have hstab : Nat.card (MulAction.stabilizer Alt part0) = 576 := by
    refine Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 315) ?_
    rw [hmul2]
  have h9 : 9 * Nat.card Ubar = 576 := by
    have := congrArg (fun n => 9 * n) card_Ubar
    simpa using this
  rw [hstab, h9]

theorem innerIndexNinePackage_A9 : InnerIndexNinePackage Alt :=
  innerIndexNinePackage_of_unique_fixed (Δ := Alt) (X := Part) (U := Ubar) (x₀ := part0)
    isSylowTwoOf_Ubar Ubar_fix Ubar_unique card_stabilizer
    xAlt_fix yAlt_fix xAlt_pow yAlt_pow xAlt_mul_yAlt xAlt_ne_one yAlt_not_zpowers

end IndexNineA9

end CFSG.Sporadic.Th

