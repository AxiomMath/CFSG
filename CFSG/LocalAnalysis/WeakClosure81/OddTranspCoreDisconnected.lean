module

public import CFSG.LocalAnalysis.WeakClosure81.OddTranspCoreSimple
public import CFSG.Fischer.Uniq.Graph
public import CFSG.Open.FusionDefs
import CFSG.LocalAnalysis.WeakClosure81.OddTranspCoreThreeTransp
import CFSG.GroupTheory.ThreeTranspositions.FischerResidual
import CFSG.Goldschmidt75.OddCore
import CFSG.Quasithin.Background.G116IIStruct
import CFSG.LocalAnalysis.EvenBN.Tits.I21LA6Aut
public import CFSG.Fischer.NoF25.Local
public import CFSG.Sporadic.FischerOddCore.Fi24AlmostSimple
public import CFSG.Sporadic.FischerOddCore.Fi24R2CompBase
public import CFSG.Sporadic.FischerOddCore.FischerOuterBasic
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public import CFSG.Sporadic.Th.Max3.Data
import CFSG.Certificates.Kernel.LocalCompTits.Span
import CFSG.ClassicalInvolution.Asc77.HypOmegaBasic
import CFSG.ClassicalInvolution.Asc77.Lemma310
import CFSG.ClassicalInvolution.Asc77.ThmEStatement
import CFSG.ClassicalInvolution.Asc77.WP1Section18
import CFSG.ClassicalInvolution.Balance.PassTwoFinal
import CFSG.ClassicalInvolution.Generic.InductionMain
import CFSG.ClassicalInvolution.Models.LinearFrames
import CFSG.ClassicalInvolution.Models.LinearPairs
import CFSG.ClassicalInvolution.Models.OrthogonalPairs
import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCLayer
import CFSG.ClassicalInvolution.Models.Transfer
import CFSG.ClassicalInvolution.Models.UnitaryPairs
import CFSG.ClassicalInvolution.RouteD.TypeAChain
import CFSG.Goldschmidt75.Basic
import CFSG.GroupTheory.SubgroupCardMul
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7Iso
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122AProved
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort
import CFSG.LocalAnalysis.WeakClosure81.EightThreeA
import CFSG.LocalAnalysis.WeakClosure81.SevenEleven
import CFSG.LocalAnalysis.WeakClosure81.SevenElevenW3
import CFSG.LocalAnalysis.WeakClosure81.SevenFiveTwo
import CFSG.LocalAnalysis.WeakClosure81.SixNine
import CFSG.LocalAnalysis.WeakClosure81.SixSix
import CFSG.Quasithin.Background.A3Structure318Red
import CFSG.Quasithin.Background.C2Inputs
import CFSG.Quasithin.Background.G10Local
import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
import CFSG.Quasithin.Vol2.Ch10SecA1011A
import CFSG.Quasithin.Vol2.Ch10SecABasicAut
import CFSG.RankThree.Asc83Table.PermTables
import CFSG.RankThree.PartOne.FIS.VRelation
import CFSG.RankThree.S4Free.Statement
import CFSG.Sporadic.Schreier.M11
import Certificates.Kernel.J4Count.FixCE
import Certificates.Kernel.J4Count.FixCPairBase1
import Certificates.Kernel.J4Count.KFactsBase
import TauCeti.GroupTheory.SpecificGroups.Dihedral.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81.CoreStar

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification CFSG.Open Subgroup

private theorem exists_two_ne {n : ℕ} (hn : 5 ≤ n) (a b c : Fin n) :
    ∃ x y : Fin n, x ≠ y ∧ x ≠ a ∧ x ≠ b ∧ x ≠ c ∧ y ≠ a ∧ y ≠ b ∧ y ≠ c := by
  classical
  have hcard : 1 < (Finset.univ \ {a, b, c}).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
    have := Finset.card_le_three (a := a) (b := b) (c := c)
    omega
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hcard
  simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
    true_and, not_or] at hx hy
  exact ⟨x, y, hxy, hx.1, hx.2.1, hx.2.2, hy.1, hy.2.1, hy.2.2⟩

theorem connected_commGraph_of_perm {G : Type} [Group G] {t : G} {n : ℕ} (hn : 5 ≤ n)
    (ψ : G ≃* Equiv.Perm (Fin n)) (ht : (ψ t).IsSwap) :
    (commGraph {x : G | IsConj t x}).Connected := by
  classical
  obtain ⟨a₀, b₀, hab₀, hψt⟩ := ht
  have hmem : ∀ p q : Fin n, p ≠ q → IsConj t (ψ.symm (Equiv.swap p q)) := fun p q hpq => by
    have h1 : IsConj (ψ t) (Equiv.swap p q) := by
      rw [hψt]; exact Equiv.Perm.isConj_swap hab₀ hpq
    simpa using ψ.symm.toMonoidHom.map_isConj h1
  have hswap : ∀ x : G, IsConj t x → ∃ p q : Fin n, p ≠ q ∧ ψ.symm (Equiv.swap p q) = x := by
    intro x hx
    obtain ⟨g, rfl⟩ := isConj_iff.mp hx
    refine ⟨ψ g a₀, ψ g b₀, (ψ g).injective.ne hab₀, ψ.injective ?_⟩
    rw [MulEquiv.apply_symm_apply, map_mul, map_mul, map_inv, hψt, Equiv.swap_apply_apply]
  let elt : ∀ p q : Fin n, p ≠ q → {x : G | IsConj t x} := fun p q hpq =>
    ⟨ψ.symm (Equiv.swap p q), hmem p q hpq⟩
  have hadj : ∀ {p q r s : Fin n} (hpq : p ≠ q) (hrs : r ≠ s), p ≠ r → p ≠ s → q ≠ r →
      q ≠ s → (commGraph {x : G | IsConj t x}).Adj (elt p q hpq) (elt r s hrs) := by
    intro p q r s hpq hrs hpr hps hqr hqs
    refine ⟨fun h => ?_, ?_⟩
    · have h' : Equiv.swap p q = Equiv.swap r s := ψ.symm.injective (congrArg Subtype.val h)
      have := congrArg (fun σ : Equiv.Perm (Fin n) => σ p) h'
      simp only [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hpr hps] at this
      exact hpq this.symm
    · change ψ.symm (Equiv.swap p q) * ψ.symm (Equiv.swap r s) =
        ψ.symm (Equiv.swap r s) * ψ.symm (Equiv.swap p q)
      rw [← map_mul, ← map_mul,
        CFSG.Permutation.SymmetricCoxeter.swap_mul_swap_comm hpr hps hqr hqs]
  have : Nonempty {x : G | IsConj t x} := ⟨⟨t, IsConj.refl t⟩⟩
  refine SimpleGraph.Connected.mk fun u v => ?_
  obtain ⟨p, q, hpq, hu⟩ := hswap u.1 u.2
  obtain ⟨r, s, hrs, hv⟩ := hswap v.1 v.2
  have hu' : u = elt p q hpq := Subtype.ext hu.symm
  have hv' : v = elt r s hrs := Subtype.ext hv.symm
  rw [hu', hv']
  by_cases hdisj : p ≠ r ∧ p ≠ s ∧ q ≠ r ∧ q ≠ s
  · exact (hadj hpq hrs hdisj.1 hdisj.2.1 hdisj.2.2.1 hdisj.2.2.2).reachable
  ·
    obtain ⟨x, y, hxy, hxp, hxq, hxw, hyp, hyq, hyw⟩ :=
      exists_two_ne hn p q (if r = p ∨ r = q then s else r)
    have hxr : x ≠ r ∧ x ≠ s ∧ y ≠ r ∧ y ≠ s := by
      by_cases hr : r = p ∨ r = q
      · rw [if_pos hr] at hxw hyw
        rcases hr with rfl | rfl
        · exact ⟨hxp, hxw, hyp, hyw⟩
        · exact ⟨hxq, hxw, hyq, hyw⟩
      · rw [if_neg hr] at hxw hyw
        have hs : s = p ∨ s = q := by
          by_contra hs
          push Not at hr hs
          exact hdisj ⟨hr.1.symm, hs.1.symm, hr.2.symm, hs.2.symm⟩
        rcases hs with rfl | rfl
        · exact ⟨hxw, hxp, hyw, hyp⟩
        · exact ⟨hxw, hxq, hyw, hyq⟩
    exact (hadj hpq hxy hxp.symm hyp.symm hxq.symm hyq.symm).reachable.trans
      (hadj hxy hrs hxr.1 hxr.2.1 hxr.2.2.1 hxr.2.2.2).reachable

theorem commutator_mem_of_alt {X : Type} [Group X] [Finite X] (N : Subgroup X) [N.Normal]
    {n : ℕ} (hn : 5 ≤ n) (e : ↥N ≃* alternatingGroup (Fin n))
    (hC : centralizer (N : Set X) = ⊥) : ∀ a b : X, a * b * a⁻¹ * b⁻¹ ∈ N := by
  rcases eq_or_ne n 6 with rfl | hn6
  · exact (CFSG.LocalAnalysis.EvenBN.Tits.I21L.A6_out N e hC).2
  by_cases hNtop : N = ⊤
  · intro a b
    rw [hNtop]
    exact mem_top _
  obtain ⟨φ⟩ := CFSG.Quasithin.G11.nonempty_mulEquiv_perm_of_normal_alt hn hn6 N e
    (fun c hc => by
      have : c ∈ centralizer (N : Set X) := mem_centralizer_iff.mpr fun h hh => (hc h hh).symm
      rw [hC] at this
      exact (mem_bot.mp this)) hNtop
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hcard : Nat.card X = 2 * Nat.card N := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card, two_mul_card_alternatingGroup]
  have hq2 : Nat.card (X ⧸ N) = 2 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [hcard] at h
    exact (Nat.eq_of_mul_eq_mul_right Nat.card_pos h).symm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcyc : IsCyclic (X ⧸ N) := isCyclic_of_prime_card hq2
  have hcomm : ∀ x y : X ⧸ N, x * y = y * x := fun x y => by
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp (hg x)
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp (hg y)
    exact (Commute.zpow_zpow_self g i j).eq
  intro a b
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
    QuotientGroup.mk_inv, QuotientGroup.mk_inv, hcomm (a : X ⧸ N) b]
  group

theorem hasCoreStar_of_not_connected
    {Y : Type} [Group Y] [Finite Y] {t : Y} (hP : Pair Y {x | IsConj t x})
    (hZ : Subgroup.center Y = ⊥) (h2 : ∀ N : Subgroup Y, N.Normal → IsPGroup 2 N → N = ⊥)
    (hO : fusionOddCore Y = ⊥) (hc : ¬ (commGraph {x : Y | IsConj t x}).Connected) :
    HasCoreStar Y t := by
  classical
  have ht : t ∈ {x : Y | IsConj t x} := IsConj.refl t
  have h3 : ∀ N : Subgroup Y, N.Normal → IsPGroup 3 N → N ≤ center Y := fun N hN hN3 => by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hN3
    have hodd : Odd (Nat.card N) := by rw [hk]; exact Odd.pow (by decide)
    have h : N ≤ fusionOddCore Y := CFSG.Goldschmidt75.le_oddCore hN hodd
    rw [hO] at h
    exact h.trans bot_le
  have : Finite (Y ⧸ center Y) := Finite.of_surjective _ QuotientGroup.mk_surjective
  set π := QuotientGroup.mk' (center Y) with hπ
  obtain ⟨N, hNn, hNbot, hNs, hNsol, hcent⟩ :=
    CFSG.GroupTheory.ThreeTranspositions.exists_minimalNormal_quotient_center hP h2 h3
  have hPq := CFSG.GroupTheory.ThreeTranspositions.pair_quot_center hP h2
  have hZq : center (Y ⧸ center Y) = ⊥ := Pair.center_quotient_center_eq_bot hP
  have hNle :=
    CFSG.GroupTheory.ThreeTranspositions.le_commutator_of_isSimpleGroup_of_not_isSolvable hNs hNsol
  have hOeq := CFSG.GroupTheory.ThreeTranspositions.pResidualOf_three_commutator_eq hPq hZq hNn
    hNbot hNs hNsol hNle
  have hquot := CFSG.GroupTheory.ThreeTranspositions.threeResidualQuot_eq_Kgrp hPq hZq hNn hNs
    hNbot hOeq ht
  have hclass := CFSG.GroupTheory.ThreeTranspositions.image_threeResidualClass hPq hZq hNn hNs
    hNbot ht hquot
  have hH := CFSG.GroupTheory.ThreeTranspositions.hyp_of_eq_Kgrp hPq hZq hNn hNs hNsol hNbot hcent
    ht hquot hclass
  set W := CFSG.GroupTheory.ThreeTranspositions.threeResidualQuot t with hW
  set C := CFSG.GroupTheory.ThreeTranspositions.threeResidualClass t with hC
  have hdπ : π t ∈ π '' {x : Y | IsConj t x} := ⟨t, ht, rfl⟩
  have hKsup : CFSG.RankThree.PartOne.FIS.Kgrp N (π t) = N ⊔ zpowers (π t) :=
    CFSG.RankThree.PartOne.FIS.closure_conjOrbit_eq hPq hZq hNn hNs hNbot hdπ
  have hWsup : W = N ⊔ zpowers (π t) := hquot.trans hKsup
  have htW : π t ∈ W := by rw [hWsup]; exact mem_sup_right (mem_zpowers _)
  have hNW : N ≤ W := by rw [hWsup]; exact le_sup_left
  set th : ↥W := ⟨π t, htW⟩ with hth
  have hthC : th ∈ C := ⟨1, one_mem _, by simp; rfl⟩
  have hCeq : C = {x | IsConj th x} := by
    obtain ⟨e₀, he₀⟩ := hH.pair.2.1
    have h1 : IsConj e₀ th := by rw [he₀] at hthC; exact hthC
    ext x
    rw [he₀]
    exact ⟨fun h => h1.symm.trans h, fun h => h1.trans h⟩
  have hPW : Pair ↥W {x | IsConj th x} := hCeq ▸ hH.pair
  rcases permOrStar_of_hyp hPW hH.center hH.simple with ⟨n, θ, hθ⟩ | hstar
  · exfalso
    have hn : 5 ≤ n := by
      by_contra hn
      apply hNsol
      have : Group.IsSolvable (Equiv.Perm (Fin n)) := Equiv.Perm.isSolvable (by simp; omega)
      have : Group.IsSolvable ↥W :=
        solvable_of_solvable_injective (f := θ.toMonoidHom) θ.injective
      exact solvable_of_solvable_injective (f := (Subgroup.subgroupOfEquivOfLe hNW).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hNW).symm.injective
    let L : Subgroup (Equiv.Perm (Fin n)) := (N.subgroupOf W).map θ.toMonoidHom
    have hLn : L.Normal := (hNn.subgroupOf W).map θ.toMonoidHom θ.surjective
    let eL : ↥N ≃* ↥L := (Subgroup.subgroupOfEquivOfLe hNW).symm.trans
      ((N.subgroupOf W).equivMapOfInjective θ.toMonoidHom θ.injective)
    have : Nontrivial ↥N := (Subgroup.nontrivial_iff_ne_bot N).mpr hNbot
    have : Nontrivial ↥L := eL.symm.toEquiv.nontrivial
    have := hNs
    have hsL : IsSimpleGroup ↥L := MulEquiv.isSimpleGroup eL.symm
    have hAL : alternatingGroup (Fin n) ≤ L :=
      Equiv.Perm.alternatingGroup_le_of_normal (by simp; omega) inferInstance
    have hLA : L = alternatingGroup (Fin n) := by
      have : ((alternatingGroup (Fin n)).subgroupOf L).Normal :=
        (alternatingGroup.normal (α := Fin n)).subgroupOf L
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
          ((alternatingGroup (Fin n)).subgroupOf L) with h | h
      · exfalso
        have hbot : alternatingGroup (Fin n) = ⊥ :=
          le_bot_iff.mp ((Subgroup.subgroupOf_eq_bot.mp h) le_rfl hAL)
        have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
        have hidx := alternatingGroup.index_eq_two (α := Fin n)
        rw [hbot, Subgroup.index_bot, Nat.card_perm, Nat.card_fin] at hidx
        have h5 := Nat.factorial_le hn
        rw [hidx] at h5
        exact absurd h5 (by decide)
      · exact le_antisymm (Subgroup.subgroupOf_eq_top.mp h) hAL
    let eN : ↥N ≃* alternatingGroup (Fin n) := eL.trans (MulEquiv.subgroupCongr hLA)
    have hab := commutator_mem_of_alt N hn eN hcent
    have hWtop : W = ⊤ := by
      rw [eq_top_iff, ← Pair.closure_eq hPq, closure_le]
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨g, rfl⟩ := isConj_iff.mp hx
      have hmem : π (g * t * g⁻¹) * (π t)⁻¹ ∈ N := by
        rw [map_mul, map_mul, map_inv]
        exact hab (π g) (π t)
      rw [SetLike.mem_coe, show π (g * t * g⁻¹) = π (g * t * g⁻¹) * (π t)⁻¹ * π t by group]
      exact W.mul_mem (hNW hmem) htW
    have hπinj : Function.Injective π :=
      (MonoidHom.ker_eq_bot_iff _).mp (by rw [hπ, QuotientGroup.ker_mk']; exact hZ)
    let πW : Y →* ↥W := π.codRestrict W fun y => by rw [hWtop]; exact mem_top _
    have hbij : Function.Bijective πW :=
      ⟨fun a b h => hπinj (congrArg Subtype.val h), fun w => by
        obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (center Y) w.1
        exact ⟨y, Subtype.ext hy⟩⟩
    let ψ : Y ≃* Equiv.Perm (Fin n) := (MulEquiv.ofBijective πW hbij).trans θ
    exact hc (connected_commGraph_of_perm hn ψ hθ)
  ·
    exact hasCoreStar_of_quotient hP (isPGroup_two_center_of_fusionOddCore hO)
      (hasCoreStar_map W.subtype Subtype.val_injective hstar)

end CFSG.LocalAnalysis.WeakClosure81.CoreStar
