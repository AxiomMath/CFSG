module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.Defs
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.AltTenPerm
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsIdent
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentAltTen
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFamAltAut
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvableBorel
import CFSG.LocalAnalysis.UniquenessCase.UC6K35Red2
import CFSG.RankThree.PartOne.S12.Sec1511SPEFStar
import CFSG.RankThree.PartOne.CTP.OutEmbed
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingOutsideSix
import CFSG.GroupTheory.ABGLocalTools.PStabilityQDickson
import CFSG.LocalAnalysis.AGLEmbeddingD2.AltPerm
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFamAltPerm
import CFSG.LocalAnalysis.AGLEmbedding.OneLieReduced
public import CFSG.Assembly.QuasithinDefs
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
import CFSG.LieType.SeitzGeneration.Lift
import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallShape
import CFSG.LocalAnalysis.AGLEmbedding.ReeFacts
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
import CFSG.LocalAnalysis.AGLEmbedding.UnitaryFacts
import CFSG.LocalAnalysis.UniquenessCase.UCKInputs
import CFSG.RankThree.PartOne.CTP.StrongPClassification

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive

open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open Equiv Equiv.Perm
open CFSG.ComponentClassification.CatalogueSchreierAlternating
  (outer_card_dvd_two_of_equiv_outside_six)

variable {X : Type} [Group X] [Finite X]

theorem card_quotient_dvd_two_of_equiv_alternating {K : Subgroup X} [K.Normal]
    (hKC : Subgroup.centralizer (K : Set X) = ⊥)
    {n : ℕ} (hn : 7 ≤ n) (e : ↥K ≃* alternatingGroup (Fin n)) :
    Nat.card (X ⧸ K) ∣ 2 := by
  have hout : Nat.card (Outer ↥K) ∣ 2 :=
    outer_card_dvd_two_of_equiv_outside_six (n := n) (Or.inr hn) e
  have hQle : Nat.card (X ⧸ K) ≤ Nat.card (Outer ↥K) :=
    CFSG.RankThree.PartOne.CTP.card_quotient_le_outer K hKC
  have h1 : Nat.card (X ⧸ K) ≤ 2 :=
    hQle.trans (Nat.le_of_dvd (by norm_num) hout)
  have hpos : 0 < Nat.card (X ⧸ K) := Nat.card_pos
  have h2 : Nat.card (X ⧸ K) = 1 ∨ Nat.card (X ⧸ K) = 2 := by omega
  rcases h2 with h2 | h2 <;> rw [h2] <;> norm_num

structure AltTenSetup (X : Type*) [Group X] [Finite X] (N : Subgroup X) where
  hN : IsStronglyPEmbedded 5 N
  K : Subgroup X
  hKdef : K = CFSG.generalizedFitting X
  hKn : K.Normal
  P : Sylow 5 X
  hPN : (P : Subgroup X) ≤ N
  T : Sylow 5 ↥K
  hT : (T : Subgroup ↥K) = ((P : Subgroup X) ⊓ K).subgroupOf K
  hTN : (T : Subgroup ↥K) ≤ N.subgroupOf K
  hKC : Subgroup.centralizer (K : Set X) = ⊥
  e : ↥K ≃* alternatingGroup (Fin 10)
  S : Sylow 5 (alternatingGroup (Fin 10))
  hScoe : (S : Subgroup (alternatingGroup (Fin 10))) =
      (T : Subgroup ↥K).map e.toMonoidHom
  hNW : Subgroup.normalizer
      ((S : Subgroup (alternatingGroup (Fin 10))) :
        Set (alternatingGroup (Fin 10))) ≤ (N.subgroupOf K).map e.toMonoidHom
  hWne : (N.subgroupOf K).map e.toMonoidHom ≠ ⊤
  B : Finset (Fin 10)
  hBcard : B.card = 5
  hBS : ∀ s ∈ (S : Subgroup (alternatingGroup (Fin 10))), ∀ i ∈ B,
      (s : Perm (Fin 10)) i ∈ B
  hBover : ∀ Y : Subgroup (alternatingGroup (Fin 10)),
      Subgroup.normalizer
        ((S : Subgroup (alternatingGroup (Fin 10))) :
          Set (alternatingGroup (Fin 10))) ≤ Y →
      Y ≠ ⊤ → ∀ y ∈ Y,
        (∀ i ∈ B, (y : Perm (Fin 10)) i ∈ B) ∨
          ∀ i ∈ B, (y : Perm (Fin 10)) i ∉ B

theorem exists_altTen_setup (hO : CFSG.pPrimeCore 5 X = ⊥)
    {N : Subgroup X} (hN : IsStronglyPEmbedded 5 N)
    (e : ↥(CFSG.generalizedFitting X) ≃* alternatingGroup (Fin 10)) :
    Nonempty (AltTenSetup X N) := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let K : Subgroup X := CFSG.generalizedFitting X
  obtain ⟨hKs, -, hKn, hKC⟩ :=
    CFSG.RankThree.PartOne.Sec1511.spe_fstar Nat.prime_five hO hN
  haveI : K.Normal := hKn
  haveI : IsSimpleGroup ↥K := hKs
  have hK1 : K ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot K).1 inferInstance
  obtain ⟨P, hPN, hPK, T, hT, -⟩ :=
    exists_sylow_glbCore_ne_top_of_isStronglyPEmbedded (K := K) hO hK1 hN
  have hTN : (T : Subgroup ↥K) ≤ N.subgroupOf K := by
    rw [hT]
    intro t ht
    exact Subgroup.mem_subgroupOf.2 (hPN (Subgroup.mem_subgroupOf.1 ht).1)
  have hQdvd : Nat.card (X ⧸ K) ∣ 2 :=
    card_quotient_dvd_two_of_equiv_alternating hKC (by norm_num) e
  let S : Sylow 5 (alternatingGroup (Fin 10)) :=
    Sylow.mapSurjective (f := e.toMonoidHom) e.surjective T
  have hScoe : (S : Subgroup (alternatingGroup (Fin 10))) =
      (T : Subgroup ↥K).map e.toMonoidHom :=
    Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective T
  have hNW : Subgroup.normalizer
      ((S : Subgroup (alternatingGroup (Fin 10))) :
        Set (alternatingGroup (Fin 10))) ≤ (N.subgroupOf K).map e.toMonoidHom := by
    rw [hScoe, ← Subgroup.map_equiv_normalizer_eq (T : Subgroup ↥K) e]
    exact Subgroup.map_mono (by
      rw [hT]
      exact normalizer_subgroupOf_le_of_isStronglyPEmbedded hN hPK
        (P.isPGroup'.to_le inf_le_left) (inf_le_left.trans hPN) inf_le_right)
  have hne : N.subgroupOf K ≠ ⊤ := fun h =>
    CFSG.LocalAnalysis.UniquenessCase.UCK.not_le_of_isStronglyPEmbedded hN P hPN hPK T hT
      (Subgroup.subgroupOf_eq_top.mp h)
  have hWne : (N.subgroupOf K).map e.toMonoidHom ≠ ⊤ :=
    CFSG.KCore.map_ne_top_of_injective e.injective hne
  obtain ⟨B, hBcard, hBS, -, hBover⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.kFactAltTenOvergroup_holds S
  exact ⟨hN, K, rfl, hKn, P, hPN, T, hT, hTN, hKC, e, S, hScoe, hNW, hWne, B,
    hBcard, hBS, hBover⟩

private theorem cycle_support_eq_or_compl {a : Perm (Fin 10)} {O B : Finset (Fin 10)}
    (ha : a.IsCycle) (hO : O.card = 5) (hB : B.card = 5)
    (hmoves : ∀ x, a x ≠ x ↔ x ∈ O) (hBstable : ∀ x ∈ B, a x ∈ B) :
    O = B ∨ O = Bᶜ := by
  classical
  have hBc : Bᶜ.card = 5 := by
    rw [Finset.card_compl, Fintype.card_fin, hB]
  by_cases hne : (O ∩ B).Nonempty
  · left
    obtain ⟨x, hx⟩ := hne
    obtain ⟨hxO, hxB⟩ := Finset.mem_inter.1 hx
    refine Finset.eq_of_subset_of_card_le ?_ (by rw [hB, hO])
    intro y hy
    have hy1 : a y ≠ y := (hmoves y).2 hy
    have hx1 : a x ≠ x := (hmoves x).2 hxO
    obtain ⟨n, hn⟩ := (ha.sameCycle hx1 hy1).exists_nat_pow_eq
    rw [← hn]
    have hpow : ∀ n : ℕ, (a ^ n) x ∈ B := by
      intro n
      induction n with
      | zero => simpa using hxB
      | succ n ih => rw [pow_succ']; exact hBstable _ ih
    exact hpow n
  · right
    have hsub : O ⊆ Bᶜ := by
      intro y hy
      rw [Finset.mem_compl]
      intro hyB
      exact hne ⟨y, Finset.mem_inter.2 ⟨hy, hyB⟩⟩
    exact Finset.eq_of_subset_of_card_le hsub (by rw [hBc, hO])

private theorem exists_mem_sylow_fixing_blocks
    (S : Sylow 5 (alternatingGroup (Fin 10))) {B : Finset (Fin 10)}
    (hBcard : B.card = 5)
    (hBS : ∀ s ∈ (S : Subgroup (alternatingGroup (Fin 10))), ∀ i ∈ B,
      (s : Perm (Fin 10)) i ∈ B) :
    (∃ s ∈ (S : Subgroup (alternatingGroup (Fin 10))), s ≠ 1 ∧
        ∀ i ∉ B, (s : Perm (Fin 10)) i = i) ∧
    (∃ s ∈ (S : Subgroup (alternatingGroup (Fin 10))), s ≠ 1 ∧
        ∀ i ∈ B, (s : Perm (Fin 10)) i = i) := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let E : Subgroup (Perm (Fin 10)) :=
    (S : Subgroup (alternatingGroup (Fin 10))).map (alternatingGroup (Fin 10)).subtype
  obtain ⟨hEab, hEcard⟩ :=
    CFSG.AGLEmbedding.KFactProofs.SmallIdent.isElemAbelian_map_sylow
      (K := alternatingGroup (Fin 10)) (p := 5) Nat.prime_five (by norm_num)
      (MulEquiv.refl (alternatingGroup (Fin 10))) S
  obtain ⟨a₁, ha₁E, a₂, ha₂E, O₁, O₂, hO1card, hO2card, hOdisj, ha1moves, ha2moves⟩ :=
    CFSG.AGLEmbeddingD2.exists_cycles_of_isElemAbelian Nat.prime_five (by norm_num)
      (by norm_num : 10 < 3 * 5) hEab hEcard
  obtain ⟨s₁, hs₁S, hs₁val⟩ := Subgroup.mem_map.1 ha₁E
  obtain ⟨s₂, hs₂S, hs₂val⟩ := Subgroup.mem_map.1 ha₂E
  have hs₁moves : ∀ x, (s₁ : Perm (Fin 10)) x ≠ x ↔ x ∈ O₁ := fun x => by
    rw [show (s₁ : Perm (Fin 10)) = a₁ from hs₁val]; exact ha1moves x
  have hs₂moves : ∀ x, (s₂ : Perm (Fin 10)) x ≠ x ↔ x ∈ O₂ := fun x => by
    rw [show (s₂ : Perm (Fin 10)) = a₂ from hs₂val]; exact ha2moves x
  have hs₁fix : ∀ x ∉ O₁, (s₁ : Perm (Fin 10)) x = x := fun x hx => by
    by_contra h; exact hx ((hs₁moves x).1 h)
  have hs₂fix : ∀ x ∉ O₂, (s₂ : Perm (Fin 10)) x = x := fun x hx => by
    by_contra h; exact hx ((hs₂moves x).1 h)
  have hs₁ne : s₁ ≠ 1 := by
    intro h
    obtain ⟨x, hx⟩ := Finset.card_pos.1 (by rw [hO1card]; norm_num)
    exact (hs₁moves x).2 hx (by rw [h]; rfl)
  have hs₂ne : s₂ ≠ 1 := by
    intro h
    obtain ⟨x, hx⟩ := Finset.card_pos.1 (by rw [hO2card]; norm_num)
    exact (hs₂moves x).2 hx (by rw [h]; rfl)
  have hs₁cycle : (s₁ : Perm (Fin 10)).IsCycle :=
    CFSG.AGLEmbedding.KFactProofs.SmallIdent.isCycle_of_moves Nat.prime_five
      (by rw [show (s₁ : Perm (Fin 10)) = a₁ from hs₁val]; exact hEab.2 a₁ ha₁E)
      hO1card hs₁moves
  have hs₂cycle : (s₂ : Perm (Fin 10)).IsCycle :=
    CFSG.AGLEmbedding.KFactProofs.SmallIdent.isCycle_of_moves Nat.prime_five
      (by rw [show (s₂ : Perm (Fin 10)) = a₂ from hs₂val]; exact hEab.2 a₂ ha₂E)
      hO2card hs₂moves
  have hO1B := cycle_support_eq_or_compl hs₁cycle hO1card hBcard hs₁moves
    (fun i hi => hBS s₁ hs₁S i hi)
  have hBc : Bᶜ.card = 5 := by
    rw [Finset.card_compl, Fintype.card_fin, hBcard]
  rcases hO1B with h1 | h1
  · have h2 : O₂ = Bᶜ := by
      refine Finset.eq_of_subset_of_card_le ?_ (by rw [hBc, hO2card])
      intro x hx
      rw [Finset.mem_compl]
      intro hxB
      exact Finset.disjoint_left.1 hOdisj (by rw [h1]; exact hxB) hx
    exact ⟨⟨s₁, hs₁S, hs₁ne, fun i hi => hs₁fix i (by rw [h1]; exact hi)⟩,
      ⟨s₂, hs₂S, hs₂ne, fun i hi => hs₂fix i (by rw [h2]; simpa using hi)⟩⟩
  · have h2 : O₂ = B := by
      refine Finset.eq_of_subset_of_card_le ?_ (by rw [hBcard, hO2card])
      intro x hx
      by_contra hxB
      exact Finset.disjoint_left.1 hOdisj (by rw [h1]; simpa using hxB) hx
    exact ⟨⟨s₂, hs₂S, hs₂ne, fun i hi => hs₂fix i (by rw [h2]; exact hi)⟩,
      ⟨s₁, hs₁S, hs₁ne, fun i hi => hs₁fix i (by rw [h1]; simpa using hi)⟩⟩

private theorem mem_map_of_commute (N : Subgroup X) (D : AltTenSetup X N)
    {s : alternatingGroup (Fin 10)} (hsS : s ∈ (D.S : Subgroup (alternatingGroup (Fin 10))))
    (hs1 : s ≠ 1) {g : alternatingGroup (Fin 10)} (hcomm : g * s = s * g) :
    g ∈ (N.subgroupOf D.K).map D.e.toMonoidHom := by
  classical
  have hsS' : s ∈ (D.T : Subgroup ↥D.K).map D.e.toMonoidHom := D.hScoe ▸ hsS
  obtain ⟨t, htT, htval⟩ := Subgroup.mem_map.1 hsS'
  have htP : ((t : ↥D.K) : X) ∈ (D.P : Subgroup X) := by
    have htPK : t ∈ ((D.P : Subgroup X) ⊓ D.K).subgroupOf D.K := by
      rw [← D.hT]; exact htT
    exact (Subgroup.mem_subgroupOf.1 htPK).1
  let U : Subgroup X := Subgroup.zpowers ((t : ↥D.K) : X)
  have hUleP : U ≤ (D.P : Subgroup X) := Subgroup.zpowers_le.2 htP
  have hUp : IsPGroup 5 U := D.P.isPGroup'.to_le hUleP
  have hUN : U ≤ N := hUleP.trans D.hPN
  have ht1 : t ≠ 1 := by
    intro h
    apply hs1
    rw [← htval, h, map_one]
  have hUne : U ≠ ⊥ := by
    rw [Ne, Subgroup.zpowers_eq_bot]
    exact fun h => ht1 (Subtype.ext h)
  have hC_le : Subgroup.centralizer ({((t : ↥D.K) : X)} : Set X) ≤ N :=
    (CFSG.RankThree.PartOne.StrongP.centralizer_singleton_le_normalizer_zpowers _).trans
      (D.hN.normalizer_le hUne hUp hUN)
  have hcommK : D.e.symm g * t = t * D.e.symm g := by
    apply D.e.injective
    rw [map_mul, map_mul, show D.e t = s from htval, D.e.apply_symm_apply]
    exact hcomm
  have hcommX : ((D.e.symm g : ↥D.K) : X) * ((t : ↥D.K) : X) =
      ((t : ↥D.K) : X) * ((D.e.symm g : ↥D.K) : X) :=
    congrArg (fun z : ↥D.K => (z : X)) hcommK
  have hmemN : ((D.e.symm g : ↥D.K) : X) ∈ N :=
    hC_le (Subgroup.mem_centralizer_singleton_iff.2 hcommX)
  exact Subgroup.mem_map.2 ⟨D.e.symm g, Subgroup.mem_subgroupOf.2 hmemN,
    D.e.apply_symm_apply g⟩

private theorem mem_map_of_fixes_support (N : Subgroup X) (D : AltTenSetup X N)
    {s : alternatingGroup (Fin 10)} (hsS : s ∈ (D.S : Subgroup (alternatingGroup (Fin 10))))
    (hs1 : s ≠ 1) {O : Finset (Fin 10)}
    (hsO : ∀ x ∉ O, (s : Perm (Fin 10)) x = x)
    {g : alternatingGroup (Fin 10)} (hgO : ∀ i ∈ O, (g : Perm (Fin 10)) i = i) :
    g ∈ (N.subgroupOf D.K).map D.e.toMonoidHom := by
  have hdisj : (g : Perm (Fin 10)).Disjoint (s : Perm (Fin 10)) := by
    intro x
    by_cases hx : x ∈ O
    · exact Or.inl (hgO x hx)
    · exact Or.inr (hsO x hx)
  exact mem_map_of_commute N D hsS hs1 (Subtype.ext hdisj.commute.eq)

private theorem image_core_eq_bot (q : ℕ) (N : Subgroup X) (D : AltTenSetup X N)
    (hfixB : ∀ g : alternatingGroup (Fin 10), (∀ i ∉ D.B, (g : Perm (Fin 10)) i = i) →
      g ∈ (N.subgroupOf D.K).map D.e.toMonoidHom)
    (hfixBc : ∀ g : alternatingGroup (Fin 10), (∀ i ∈ D.B, (g : Perm (Fin 10)) i = i) →
      g ∈ (N.subgroupOf D.K).map D.e.toMonoidHom)
    (Y : Subgroup X) (hYN : Y ≤ N)
    (hconjY : ∀ n ∈ N, ∀ y ∈ Y, n * y * n⁻¹ ∈ Y)
    (hYcop : Nat.Coprime q (Nat.card Y))
    (hperm : ∀ Q : Subgroup (alternatingGroup (Fin 10)), Nat.Coprime (Nat.card Q) q →
      (∀ σ ∈ Q, (∀ i ∈ D.B, (σ : Perm (Fin 10)) i ∈ D.B) ∨
        ∀ i ∈ D.B, (σ : Perm (Fin 10)) i ∉ D.B) →
      (∀ g : alternatingGroup (Fin 10), ((∀ i ∉ D.B, (g : Perm (Fin 10)) i = i) ∨
        ∀ i ∈ D.B, (g : Perm (Fin 10)) i = i) → ∀ σ ∈ Q, g * σ * g⁻¹ ∈ Q) → Q = ⊥) :
    ((Y ⊓ D.K).subgroupOf D.K).map D.e.toMonoidHom = ⊥ := by
  classical
  let W : Subgroup (alternatingGroup (Fin 10)) := (N.subgroupOf D.K).map D.e.toMonoidHom
  let Q : Subgroup (alternatingGroup (Fin 10)) :=
    ((Y ⊓ D.K).subgroupOf D.K).map D.e.toMonoidHom
  have hQleW : Q ≤ W := by
    intro q hq
    obtain ⟨y, hyYK, rfl⟩ := Subgroup.mem_map.1 hq
    have hyY : (y : X) ∈ Y := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hyYK)).1
    exact Subgroup.mem_map.2 ⟨y, Subgroup.mem_subgroupOf.2 (hYN hyY), rfl⟩
  have hconjQ : ∀ w ∈ W, ∀ q ∈ Q, w * q * w⁻¹ ∈ Q := by
    intro w hw q hq
    obtain ⟨y, hyYK, rfl⟩ := Subgroup.mem_map.1 hq
    obtain ⟨n, hnW, rfl⟩ := Subgroup.mem_map.1 hw
    have hnN : (n : X) ∈ N := Subgroup.mem_subgroupOf.1 hnW
    have hyY : (y : X) ∈ Y := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hyYK)).1
    let z : ↥D.K := (n : ↥D.K) * (y : ↥D.K) * (n : ↥D.K)⁻¹
    have hzY : (z : X) ∈ Y := by
      have h := hconjY ((n : ↥D.K) : X) hnN ((y : ↥D.K) : X) hyY
      simpa [z] using h
    refine Subgroup.mem_map.2 ⟨z, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_inf.2 ⟨hzY, z.2⟩
    · simp [z, map_mul, map_inv]
  have hQnorm : W ≤ Subgroup.normalizer (Q : Set (alternatingGroup (Fin 10))) := by
    intro w hw
    rw [Subgroup.mem_normalizer_iff]
    intro q
    exact ⟨hconjQ w hw q, fun hq => by
      have := hconjQ w⁻¹ (W.inv_mem hw) (w * q * w⁻¹) hq
      simpa [mul_assoc] using this⟩
  have hQcard : Nat.card ↥Q = Nat.card ↥(Y ⊓ D.K) := by
    change Nat.card ↥(((Y ⊓ D.K).subgroupOf D.K).map D.e.toMonoidHom) = _
    rw [Subgroup.card_map_of_injective D.e.injective]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := Y ⊓ D.K) (K := D.K) inf_le_right).toEquiv
  have hQcoprime : Nat.Coprime (Nat.card Q) q := by
    rw [hQcard]
    exact (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hYcop).symm
  have hQB : ∀ σ ∈ Q, (∀ i ∈ D.B, (σ : Perm (Fin 10)) i ∈ D.B) ∨
      ∀ i ∈ D.B, (σ : Perm (Fin 10)) i ∉ D.B := by
    intro σ hσ
    exact D.hBover W D.hNW D.hWne σ (hQleW hσ)
  have hnorm : ∀ g : alternatingGroup (Fin 10),
      ((∀ i ∉ D.B, (g : Perm (Fin 10)) i = i) ∨
        ∀ i ∈ D.B, (g : Perm (Fin 10)) i = i) →
      ∀ σ ∈ Q, g * σ * g⁻¹ ∈ Q := by
    intro g hg σ hσ
    have hgW : g ∈ W := hg.elim (hfixB g) (hfixBc g)
    exact (Subgroup.mem_normalizer_iff.1 (hQnorm hgW) σ).1 hσ
  exact hperm Q hQcoprime hQB hnorm

private theorem inf_core_eq_bot {N : Subgroup X} (D : AltTenSetup X N)
    {Y : Subgroup X}
    (hQ : ((Y ⊓ D.K).subgroupOf D.K).map D.e.toMonoidHom = ⊥) :
    Y ⊓ D.K = ⊥ := by
  have hYK : (Y ⊓ D.K).subgroupOf D.K = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective (H := (Y ⊓ D.K).subgroupOf D.K)
      (f := D.e.toMonoidHom) D.e.injective).1 hQ
  rw [eq_bot_iff]
  intro z hz
  have hzK : (⟨z, hz.2⟩ : ↥D.K) ∈ (Y ⊓ D.K).subgroupOf D.K :=
    Subgroup.mem_subgroupOf.2 hz
  rw [hYK] at hzK
  exact congrArg Subtype.val (Subgroup.mem_bot.1 hzK)

private theorem card_core_dvd_two {N : Subgroup X} (D : AltTenSetup X N) [D.K.Normal]
    (Y : Subgroup X) (hYinfK : Y ⊓ D.K = ⊥)
    (hQdvd : Nat.card (X ⧸ D.K) ∣ 2) :
    Nat.card Y = 1 ∨ Nat.card Y = 2 := by
  let f : ↥Y →* X ⧸ D.K := (QuotientGroup.mk' D.K).comp Y.subtype
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have hyq : ((y : X) : X ⧸ D.K) = 1 := by simpa [f] using hy
    have hyinf : (y : X) ∈ Y ⊓ D.K := ⟨y.2, (QuotientGroup.eq_one_iff (y : X)).1 hyq⟩
    rw [hYinfK] at hyinf
    exact Subtype.ext (Subgroup.mem_bot.1 hyinf)
  exact (Nat.dvd_prime Nat.prime_two).1 ((Subgroup.card_dvd_of_injective f hf).trans hQdvd)

private theorem pPrimeCore_le_center (q : ℕ) {N : Subgroup X}
    (hcard : Nat.card ↥(CFSG.pPrimeCore q ↥N) = 1 ∨
      Nat.card ↥(CFSG.pPrimeCore q ↥N) = 2) :
    CFSG.pPrimeCore q ↥N ≤ Subgroup.center ↥N := by
  rcases hcard with h1 | h2
  · have hbot : CFSG.pPrimeCore q ↥N = ⊥ := by
      rw [← Subgroup.card_eq_one, h1]
    rw [hbot]
    exact bot_le
  · exact CFSG.ABGLocalTools.le_center_of_normal_of_card_eq_two
      (CFSG.pPrimeCore_normal (p := q) (G := ↥N)) h2

private theorem core_centralizes_T (q : ℕ) (N : Subgroup X) (D : AltTenSetup X N)
    {Y : Subgroup X} (hY : Y = (CFSG.pPrimeCore q ↥N).map N.subtype)
    (hcenter : CFSG.pPrimeCore q ↥N ≤ Subgroup.center ↥N) :
    ∀ y ∈ Y, ∀ t ∈ (D.T : Subgroup ↥D.K),
      y * ((t : ↥D.K) : X) = ((t : ↥D.K) : X) * y := by
  intro y hy t ht
  rw [hY] at hy
  obtain ⟨y0, hy0, rfl⟩ := Subgroup.mem_map.1 hy
  have htN : ((t : ↥D.K) : X) ∈ N := Subgroup.mem_subgroupOf.1 (D.hTN ht)
  let t0 : ↥N := ⟨((t : ↥D.K) : X), htN⟩
  have h := congrArg N.subtype (Subgroup.mem_center_iff.1 (hcenter hy0) t0)
  simpa [t0] using h.symm

private theorem core_eq_bot (N : Subgroup X) (D : AltTenSetup X N) [D.K.Normal]
    {Y : Subgroup X} (hYN : Y ≤ N)
    (hcommT : ∀ y ∈ Y, ∀ t ∈ (D.T : Subgroup ↥D.K),
      y * ((t : ↥D.K) : X) = ((t : ↥D.K) : X) * y)
    (hYinfK : Y ⊓ D.K = ⊥) : Y = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  by_contra hy1
  have hfix : ∀ t ∈ (D.T : Subgroup ↥D.K),
      (MulAut.conjNormal (H := D.K) y) t = t := by
    intro t ht
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, hcommT y hy t ht]
    group
  have hf : MulAut.conjNormal (H := D.K) y ∈
      (MulAut.conj : ↥D.K →* MulAut ↥D.K).range :=
    (CFSG.AGLEmbedding.KFactProofs.SmallIdent.autFixInner_of_isAltTwoP_of_five_le
      Nat.prime_five (by norm_num) (K := ↥D.K) ⟨by simpa using D.e⟩ D.T)
      (MulAut.conjNormal (H := D.K) y) hfix
  obtain ⟨u, hu⟩ := hf
  have hcentral : ((u : ↥D.K) : X)⁻¹ * y ∈ Subgroup.centralizer (D.K : Set X) :=
    CFSG.AGLEmbedding.inv_mul_mem_centralizer_of_conjNormal_eq (K := D.K) hu.symm
  have huy : ((u : ↥D.K) : X) = y :=
    inv_mul_eq_one.mp (Subgroup.mem_bot.1 (by rw [← D.hKC]; exact hcentral))
  have hyK : y ∈ D.K := huy ▸ u.2
  have hyinf : y ∈ Y ⊓ D.K := ⟨hy, hyK⟩
  rw [hYinfK] at hyinf
  exact hy1 (Subgroup.mem_bot.1 hyinf)

private theorem mem_K_of_coprime_two {N : Subgroup X} (D : AltTenSetup X N) [D.K.Normal]
    (hQdvd : Nat.card (X ⧸ D.K) ∣ 2) {x : X}
    (hcop : Nat.Coprime (orderOf x) 2) : x ∈ D.K := by
  have h1 : orderOf ((QuotientGroup.mk' D.K) x) ∣ orderOf x := orderOf_map_dvd _ x
  have h2 : orderOf ((QuotientGroup.mk' D.K) x) ∣ 2 :=
    (orderOf_dvd_natCard _).trans hQdvd
  have h3 : orderOf ((QuotientGroup.mk' D.K) x) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop h1 h2
  have h4 : (QuotientGroup.mk' D.K) x = 1 := orderOf_eq_one_iff.1 h3
  simpa using (QuotientGroup.eq_one_iff x).1 h4

private theorem exists_order_five_in_zpowers {x : X} (hx1 : x ≠ 1)
    (hxp : IsPGroup 5 (Subgroup.zpowers x)) :
    ∃ a : ↥(Subgroup.zpowers x), orderOf a = 5 := by
  have hx5dvd : 5 ∣ Nat.card ↥(Subgroup.zpowers x) := by
    rcases hxp.card_eq_or_dvd with h | h
    · exfalso
      have hbot : Subgroup.zpowers x = ⊥ := Subgroup.card_eq_one.1 h
      rw [Subgroup.zpowers_eq_bot] at hbot
      exact hx1 hbot
    · exact h
  obtain ⟨a, haord⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(Subgroup.zpowers x)) 5 hx5dvd
  exact ⟨a, haord⟩

private theorem kiC_preserves (N : Subgroup X) (D : AltTenSetup X N) [D.K.Normal]
    (hQdvd : Nat.card (X ⧸ D.K) ∣ 2)
    {x y : X} (hxN : x ∈ N) (hyN : y ∈ N) (hx1 : x ≠ 1)
    (hxp : IsPGroup 5 (Subgroup.zpowers x))
    (hyr : (orderOf y).Prime) (hy2 : orderOf y ≠ 2) (hy5 : orderOf y ≠ 5)
    (hxy : x * y = y * x) :
    ∃ (yK : ↥D.K) (c : alternatingGroup (Fin 10)),
      (yK : X) = y ∧ c ^ 5 = 1 ∧ c ≠ 1 ∧ c * D.e yK = D.e yK * c ∧
      ¬ ((∀ i ∈ D.B, (c : Perm (Fin 10)) i ∈ D.B) ∨
          ∀ i ∈ D.B, (c : Perm (Fin 10)) i ∉ D.B) := by
  classical
  obtain ⟨k, hk⟩ := hxp.exists_orderOf_eq_pow ⟨x, Subgroup.mem_zpowers x⟩
  have hxpow : orderOf x = 5 ^ k := by simpa using hk
  have hcopx : Nat.Coprime (orderOf x) 2 := by
    rw [hxpow]; exact Nat.Coprime.pow_left k (by norm_num)
  have hxK : x ∈ D.K := mem_K_of_coprime_two D hQdvd hcopx
  have hyOdd : Odd (orderOf y) := hyr.odd_of_ne_two hy2
  have hyK : y ∈ D.K := mem_K_of_coprime_two D hQdvd (Odd.coprime_two_right hyOdd)
  let yK : ↥D.K := ⟨y, hyK⟩
  have hyW : D.e yK ∈ (N.subgroupOf D.K).map D.e.toMonoidHom :=
    Subgroup.mem_map.2 ⟨yK, Subgroup.mem_subgroupOf.2 hyN, rfl⟩
  have hypres := D.hBover _ D.hNW D.hWne (D.e yK) hyW
  obtain ⟨a, haord⟩ := exists_order_five_in_zpowers hx1 hxp
  have hapow : (a : X) ^ 5 = 1 := by
    have h := pow_orderOf_eq_one a
    rw [haord] at h
    simpa using congrArg Subtype.val h
  have hane : (a : X) ≠ 1 := by
    intro h
    have ha1 : a = 1 := Subtype.ext h
    rw [ha1, orderOf_one] at haord
    exact (Nat.prime_five).one_lt.ne haord
  have haN : (a : X) ∈ N := Subgroup.zpowers_le.2 hxN a.2
  have haK : (a : X) ∈ D.K := Subgroup.zpowers_le.2 hxK a.2
  have hay : (a : X) * y = y * (a : X) := by
    have hxcent : x ∈ Subgroup.centralizer ({y} : Set X) :=
      Subgroup.mem_centralizer_singleton_iff.2 hxy
    exact Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.zpowers_le.2 hxcent a.2)
  let aK : ↥D.K := ⟨(a : X), haK⟩
  have haKW : D.e aK ∈ (N.subgroupOf D.K).map D.e.toMonoidHom :=
    Subgroup.mem_map.2 ⟨aK, Subgroup.mem_subgroupOf.2 haN, rfl⟩
  have hapres := D.hBover _ D.hNW D.hWne (D.e aK) haKW
  have ha5e : (D.e aK) ^ 5 = 1 := by
    rw [← map_pow, show aK ^ 5 = 1 from Subtype.ext (by simpa using hapow)]
    exact map_one D.e
  have hae1 : D.e aK ≠ 1 := fun h =>
    hane (congrArg (fun z : ↥D.K => (z : X)) (D.e.injective (by simpa using h)))
  have hyeorder : orderOf (D.e yK) = orderOf y := by
    rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe yK]
  have hyecomm : D.e aK * D.e yK = D.e yK * D.e aK := by
    rw [← map_mul, ← map_mul]
    exact congrArg D.e (Subtype.ext hay)
  obtain ⟨c, hc5, hc1, hcy, hcpres⟩ :=
    AltTen.exists_five_commute_not_preserves D.hBcard hapres hypres ha5e hae1
      (by rw [hyeorder]; exact hyr) (by rw [hyeorder]; exact hy2)
      (by rw [hyeorder]; exact hy5) hyecomm
  exact ⟨yK, c, rfl, hc5, hc1, hcy, hcpres⟩

private theorem kiC_candidate (N : Subgroup X) (D : AltTenSetup X N)
    {y : X} {yK : ↥D.K} (hyK : (yK : X) = y)
    {c : alternatingGroup (Fin 10)} (hc5 : c ^ 5 = 1) (hc1 : c ≠ 1)
    (hcy : c * D.e yK = D.e yK * c)
    (hcpres : ¬ ((∀ i ∈ D.B, (c : Perm (Fin 10)) i ∈ D.B) ∨
      ∀ i ∈ D.B, (c : Perm (Fin 10)) i ∉ D.B)) :
    ∃ cK : ↥D.K, ((cK : ↥D.K) : X) * y = y * ((cK : ↥D.K) : X) ∧
      ((cK : ↥D.K) : X) ∉ N ∧ ((cK : ↥D.K) : X) ^ 5 = 1 := by
  let cK : ↥D.K := D.e.symm c
  have hcK5 : cK ^ 5 = 1 := by
    apply D.e.injective
    rw [map_pow, map_one, show D.e cK = c from D.e.apply_symm_apply c, hc5]
  have hcKne : cK ≠ 1 := fun h =>
    hc1 (by rw [← show D.e cK = c from D.e.apply_symm_apply c, h, map_one])
  have hcKpow : ((cK : ↥D.K) : X) ^ 5 = 1 := by
    simpa using congrArg (fun z : ↥D.K => (z : X)) hcK5
  have hcKyK : cK * yK = yK * cK := by
    apply D.e.injective
    rw [map_mul, map_mul, show D.e cK = c from D.e.apply_symm_apply c]
    exact hcy
  have hcKy : ((cK : ↥D.K) : X) * y = y * ((cK : ↥D.K) : X) := by
    have := congrArg (fun z : ↥D.K => (z : X)) hcKyK
    simpa [hyK] using this
  have hcKnotN : ((cK : ↥D.K) : X) ∉ N := by
    intro hcN
    have hcW : c ∈ (N.subgroupOf D.K).map D.e.toMonoidHom :=
      Subgroup.mem_map.2 ⟨cK, Subgroup.mem_subgroupOf.2 hcN, D.e.apply_symm_apply c⟩
    exact hcpres (D.hBover _ D.hNW D.hWne c hcW)
  exact ⟨cK, hcKy, hcKnotN, hcKpow⟩

theorem pPrimeCore_eq_bot_of_altTen {q : ℕ} [Fact q.Prime]
    (hO : CFSG.pPrimeCore 5 X = ⊥)
    {N : Subgroup X} (hN : IsStronglyPEmbedded 5 N)
    (e : ↥(CFSG.generalizedFitting X) ≃* alternatingGroup (Fin 10))
    (hperm : ∀ B : Finset (Fin 10), B.card = 5 → ∀ Q : Subgroup (alternatingGroup (Fin 10)),
      Nat.Coprime (Nat.card Q) q →
      (∀ σ ∈ Q, (∀ i ∈ B, (σ : Perm (Fin 10)) i ∈ B) ∨
        ∀ i ∈ B, (σ : Perm (Fin 10)) i ∉ B) →
      (∀ g : alternatingGroup (Fin 10), ((∀ i ∉ B, (g : Perm (Fin 10)) i = i) ∨
        ∀ i ∈ B, (g : Perm (Fin 10)) i = i) → ∀ σ ∈ Q, g * σ * g⁻¹ ∈ Q) → Q = ⊥) :
    CFSG.pPrimeCore q ↥N = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨D⟩ := exists_altTen_setup hO hN e
  haveI : D.K.Normal := D.hKn
  obtain ⟨⟨s₁, hs₁S, hs₁ne, hs₁fix⟩, ⟨s₂, hs₂S, hs₂ne, hs₂fix⟩⟩ :=
    exists_mem_sylow_fixing_blocks D.S D.hBcard D.hBS
  have hfixB : ∀ g : alternatingGroup (Fin 10), (∀ i ∉ D.B, (g : Perm (Fin 10)) i = i) →
      g ∈ (N.subgroupOf D.K).map D.e.toMonoidHom := by
    intro g hg
    exact mem_map_of_fixes_support N D hs₂S hs₂ne (O := D.Bᶜ)
      (fun x hx => hs₂fix x (by simpa using hx)) (fun i hi => hg i (by simpa using hi))
  have hfixBc : ∀ g : alternatingGroup (Fin 10), (∀ i ∈ D.B, (g : Perm (Fin 10)) i = i) →
      g ∈ (N.subgroupOf D.K).map D.e.toMonoidHom := by
    intro g hg
    exact mem_map_of_fixes_support N D hs₁S hs₁ne (O := D.B) hs₁fix hg
  let Y : Subgroup X := (CFSG.pPrimeCore q ↥N).map N.subtype
  have hYN : Y ≤ N := Subgroup.map_subtype_le _
  have hconjY : ∀ n ∈ N, ∀ y ∈ Y, n * y * n⁻¹ ∈ Y := by
    intro n hn y hy
    obtain ⟨y0, hy0, rfl⟩ := Subgroup.mem_map.1 hy
    exact Subgroup.mem_map.2 ⟨⟨n, hn⟩ * y0 * ⟨n, hn⟩⁻¹,
      (CFSG.pPrimeCore_normal (p := q) (G := ↥N)).conj_mem y0 hy0 ⟨n, hn⟩, by simp⟩
  have hYcop : Nat.Coprime q (Nat.card Y) := by
    rw [show Nat.card Y = Nat.card (CFSG.pPrimeCore q ↥N) from
      Subgroup.card_map_of_injective N.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card
  have hQbot := image_core_eq_bot q N D hfixB hfixBc Y hYN hconjY hYcop
    (hperm D.B D.hBcard)
  have hYinfK := inf_core_eq_bot D hQbot
  have hQdvd : Nat.card (X ⧸ D.K) ∣ 2 :=
    card_quotient_dvd_two_of_equiv_alternating D.hKC (by norm_num) D.e
  have hYcard := card_core_dvd_two D Y hYinfK hQdvd
  have hYcardCore : Nat.card ↥(CFSG.pPrimeCore q ↥N) = 1 ∨
      Nat.card ↥(CFSG.pPrimeCore q ↥N) = 2 := by
    rw [show Nat.card ↥(CFSG.pPrimeCore q ↥N) = Nat.card Y from
      (Subgroup.card_map_of_injective N.subtype_injective).symm]
    exact hYcard
  have hcenter := pPrimeCore_le_center q hYcardCore
  have hcommT := core_centralizes_T q N D rfl hcenter
  have hYbot := core_eq_bot N D hYN hcommT hYinfK
  have h := (Subgroup.map_eq_bot_iff_of_injective
      (H := CFSG.pPrimeCore q ↥N) (f := N.subtype) N.subtype_injective).1
  exact h (by simpa [Y] using hYbot)

theorem good_altTen (hO : CFSG.pPrimeCore 5 X = ⊥)
    {N : Subgroup X} (hN : IsStronglyPEmbedded 5 N)
    (e : ↥(CFSG.generalizedFitting X) ≃* alternatingGroup (Fin 10)) : Good 5 N := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  refine ⟨pPrimeCore_eq_bot_of_altTen (q := 5) hO hN e ?_, ?_⟩
  · intro B hB Q hQ hQB hnorm
    exact AltTen.eq_bot_of_normalized_by_alt_prod hB hQ hQB hnorm
  · obtain ⟨D⟩ := exists_altTen_setup hO hN e
    haveI : D.K.Normal := D.hKn
    have hQdvd : Nat.card (X ⧸ D.K) ∣ 2 :=
      card_quotient_dvd_two_of_equiv_alternating D.hKC (by norm_num) D.e
    intro x y hxN hyN hx1 hxp hyr hy2 hy5 hxy
    obtain ⟨yK, c, hyK, hc5, hc1, hcy, hcpres⟩ :=
      kiC_preserves N D hQdvd hxN hyN hx1 hxp hyr hy2 hy5 hxy
    obtain ⟨cK, hcKy, hcKN, hcKpow⟩ := kiC_candidate N D hyK hc5 hc1 hcy hcpres
    exact ⟨(cK : X), D.hKdef ▸ cK.2, hcKy,
      CFSG.RankThree.PartOne.StrongP.isPGroup_zpowers_of_pow_eq_one hcKpow, hcKN⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive
