module

public import CFSG.Quasithin.EmptyFaithful.S151S9TModel
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtCMaxCen
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatLat
public import CFSG.CharacterTheory.Blocks.BrauerInduction
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeOrderSylowColumn
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalComplementCharacterSpace
public import CFSG.Fischer.Pairs
public import CFSG.LieType.SteinbergBROddSylowCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7Iso
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122AProved
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPrimeCompatibility
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.A1cA132Action
public import CFSG.Quasithin.Background.A1cA133Three
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.B69Core
public import CFSG.Quasithin.Background.C1GNSolvConnect
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.E3
public import CFSG.Quasithin.Background.E3Nprime
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.Quasithin.Background.E3Uniq
public import CFSG.Quasithin.Background.E4Solv
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Sixteen
public import CFSG.Quasithin.Background.FFC7G
public import CFSG.Quasithin.Background.FFC8A
public import CFSG.Quasithin.Background.FLcAutMat
public import CFSG.Quasithin.Background.InternalSecB56B
public import CFSG.Quasithin.Background.InternalSecFF
public import CFSG.Quasithin.EmptyFaithful.FLcMLEGrp
public import CFSG.Quasithin.EmptyFaithful.S14110
public import CFSG.Quasithin.EmptyFaithful.S14117
public import CFSG.Quasithin.EmptyFaithful.S1421Defs
public import CFSG.Quasithin.EmptyFaithful.S151S8C2C
public import CFSG.Quasithin.EmptyFaithful.S151ZC
public import CFSG.Quasithin.EmptyFaithful.S151ZF
public import CFSG.Quasithin.EmptyFaithful.S151cA2
public import CFSG.Quasithin.EmptyFaithful.S151cCases
public import CFSG.Quasithin.EmptyFaithful.S152UGen
public import CFSG.Quasithin.EmptyFaithful.S153D44
public import CFSG.Quasithin.EmptyFaithful.S153Nine
public import CFSG.Quasithin.EmptyFaithful.T1515Top9
public import CFSG.Quasithin.H13.J4Core
public import CFSG.Quasithin.Vol2.Ch10SecA1012Three
public import CFSG.Quasithin.Vol2.Ch10SecA1012Two
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm311
public import CFSG.RankThree.Asc83Table.PermTables
public import CFSG.Sporadic.Schreier.J4SSylow
public import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.M22
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Transvection.Statement
public import CFSG.Walter.J1

public section

namespace CFSG.Quasithin.S151S9T

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.QuasithinUnique.Ch1.SporLat
  CFSG.QuasithinUnique.K1.SporadicPerm

section Table

variable {Γ : Type} [Group Γ] {n : ℕ} [MulAction Γ (Fin n)]

theorem tab_slpElts_getD (a b : Γ) (prog : List (ℕ × ℕ)) (hv : slpValidAux prog 2 = true) {i : ℕ}
    (hi : i < (slpTabsA (tab n a).toArray (tab n b).toArray prog).size) :
    (tab n ((slpElts a b prog).getD i 1)).toArray =
      (slpTabsA (tab n a).toArray (tab n b).toArray prog)[i]! := by
  have hinv := slp_foldl_inv (n := n) prog #[a, b] #[(tab n a).toArray, (tab n b).toArray]
    (by simp) (by
      intro j hj
      have hj' : j < 2 := by simpa using hj
      interval_cases j <;> simp) hv
  have hE : ∀ j < (slpTabsA (tab n a).toArray (tab n b).toArray prog).size,
      tab n ((slpElts a b prog).getD j 1) =
        ((slpTabsA (tab n a).toArray (tab n b).toArray prog)[j]!).toList := hinv.2
  rw [hE i hi, Array.toArray_toList]

end Table

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)] [FaithfulSMul Γ (Fin n)]
  {Lab : Type} [DecidableEq Lab] [Hashable Lab] [Inhabited Lab]

theorem centre_of_baseCertS (C : LatCtx Γ n Lab) (hk : 0 < C.k) (a b : Γ) (prog : List (ℕ × ℕ))
    (hv : slpValidAux prog 2 = true) (qp : List (ℕ × ℕ)) (zn gn gin hn hin : ℕ)
    (Ts : Array (List ℕ)) (par cl : Array ℕ) (k : ℕ)
    (hcert : BaseCertS n (List.range n)
      (slpTabsA (tab n a).toArray (tab n b).toArray prog) qp zn gn gin hn hin Ts par cl k)
    (hsg : C.sg = qp.map fun p => (slpElts a b prog).getD p.1 1) :
    ∃ z₀ : Γ, orderOf z₀ = 2 ∧ centerOf C.S = Subgroup.zpowers z₀ ∧
      (tab n z₀).toArray = (slpTabsA (tab n a).toArray (tab n b).toArray prog)[zn]! := by
  have hcen := cmax_center_of_baseCertS (n := n) (List.range n)
    (fun x hx => List.mem_range.mp hx) base_of_faithful a b prog hv qp zn gn gin hn hin Ts par cl k
    hcert
  rw [← hsg, C.hSeq] at hcen
  have hS2 : IsPGroup 2 ↥C.S := IsPGroup.of_card C.S_card
  have hnt : Nontrivial ↥C.S :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [C.S_card]; exact Nat.one_lt_two_pow hk.ne')
  obtain ⟨h2, hZ⟩ := cmax_center_eq_zpowers hS2 hnt hcen
  exact ⟨_, h2, hZ, tab_slpElts_getD a b prog hv hcert.2.1⟩

end CFSG.Quasithin.S151S9T
