module

import Lean
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSQ2CellsDefs
public import CFSG.LocalAnalysis.StandardType.GGNsq2NbrBlock
public import Certificates.Certificate1953
public import Certificates.Certificate1954
public import Certificates.Certificate2261
public import Certificates.Certificate2262
public import Certificates.Certificate2263
public import Certificates.Certificate2264
public import Certificates.Certificate2265
public import Certificates.Certificate2266
public import Certificates.Certificate2267
public import Certificates.Certificate2268
public import Certificates.Certificate2269
public import Certificates.Certificate2270
public import Certificates.Certificate3951
public import Certificates.Certificate8032
public import Certificates.Certificate8033
public import Certificates.Certificate8064
import CFSG.LocalAnalysis.StandardType.GGNsq2Block
import CFSG.LocalAnalysis.StandardType.GGStdUnitaryFourExcl
import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEsu
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieEsu
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosAdapter
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosFinal
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDiag
import CFSG.LocalAnalysis.StandardType.GGSecFiveNSCornerMain
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoAux
import CFSG.LocalAnalysis.StandardType.GGRCWeylCard
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsOrder

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

open scoped MatrixGroups

theorem ggNsq2Cov_of_esu
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hconf : GGConfig p B Bs x L D J) (hE : GGInnerDiagOnLabel ggRowP_ESU p Bs L)
    (h5 : ¬ GGInnerDiagOnLabel (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) p Bs L) :
    GGInnerDiagOnLabel (fun p lab => ggRowP_ESU p lab ∧
      ¬ (lab.n = 1 ∧ (lab.rank = 3 ∨ lab.rank = 5))) p Bs L := by
  have hQ : ¬ GGInnerDiagOnLabel (fun p lab =>
      ggRowP_ESU p lab ∧ lab.n = 1 ∧ (lab.rank = 3 ∨ lab.rank = 5)) p Bs L := by
    intro hlab
    have h35 : GGInnerDiagOnLabel
        (fun p lab => (ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 3) ∨
          (ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5)) p Bs L :=
      hlab.mono' fun lab hl => by
        obtain ⟨h1, h2, h3 | h3⟩ := hl
        exacts [Or.inl ⟨h1, h2, h3⟩, Or.inr ⟨h1, h2, h3⟩]
    rcases GGInnerDiagOnLabel.elim_or h35 with h3 | h5'
    · refine not_ggInnerDiagOnLabel_unitary_four hconf (h3.mono' fun lab hl => ?_)
      obtain ⟨⟨hlab', hdvd⟩, -, hr⟩ := hl
      refine ⟨?_, hr, hdvd⟩
      rcases hlab' with ⟨ht, -⟩ | ⟨ht, -⟩
      exacts [Or.inl ht, Or.inr ht]
    · exact h5 h5'
  have h' : GGInnerDiagOnLabel (fun p lab =>
      (ggRowP_ESU p lab ∧ lab.n = 1 ∧ (lab.rank = 3 ∨ lab.rank = 5)) ∨
      (ggRowP_ESU p lab ∧ ¬ (lab.n = 1 ∧ (lab.rank = 3 ∨ lab.rank = 5)))) p Bs L :=
    hE.mono' fun lab hl => (em (lab.n = 1 ∧ (lab.rank = 3 ∨ lab.rank = 5))).imp
      (fun h3 => ⟨hl, h3⟩) (fun h3 => ⟨hl, h3⟩)
  rcases GGInnerDiagOnLabel.elim_or h' with h | h
  · exact absurd h hQ
  · exact h

theorem ggNsq2Nbr_L_of_cov
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    {m : ℕ} {σ : Fin m ≃ ι} (hM : M = (CoxeterMatrix.A m).reindex σ)
    (hno6 : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6)
    (hcov : GGInnerDiagOnLabel (fun p lab => ggRowP_ESU p lab ∧
      ¬ (lab.n = 1 ∧ (lab.rank = 3 ∨ lab.rank = 5))) p Bs L)
    (hp3 : p = 3) {y : G} (hy : y ∈ Bs)
    (hJ : IsComponentOf J (L ⊓ Subgroup.centralizer ({y} : Set G))) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (f a : ℕ),
      Nat.card K = (2 ^ f) ^ 2 ∧ 2 ≤ f ∧ 3 ∣ 2 ^ f + 1 ∧ 2 ≤ a ∧
        Nonempty (↥J ⧸ Subgroup.center ↥J ≃* Su K 2 f a ⧸ Subgroup.center (Su K 2 f a)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hKf, hKfin, hKchar, f, n, ψ, hcard, hn, hker, hrange, hdvd, hacts, -⟩ :=
    ggNSLie_cover_of_esu hcov
  letI : Field K := hKf
  letI : Finite K := hKfin
  letI : CharP K 2 := hKchar
  have hloc : GGNSLocalHyp p B Bs K f n ψ :=
    ggNSLocalHyp_of_routeCfg hcfg (Or.inl rfl) hcard hn hker hrange hdvd hacts
  obtain ⟨c, hc⟩ := ggNSLocal_exists_diag ggSecFiveNSCornerInput_holds hloc
  have h'' := hloc.comp_conj c
  have hrange' : (ψ.comp (MulAut.conj c).toMonoidHom).range = L := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (MulAut.conj c).surjective,
      Subgroup.map_top, hrange]
  have hf2 : 2 ≤ f := by
    by_contra hf
    have hf1 : f = 1 := by
      have : 1 ≤ f := by
        by_contra h0
        have h0' : f = 0 := by omega
        subst h0'
        have : Nat.card K = 1 := by simpa using hcard
        have h1 : 1 < Nat.card K := Finite.one_lt_card
        omega
      omega
    subst hf1
    have hpos := ggNSDiag_position h'' hc
    rw [hrange'] at hpos
    unfold GGTableBPosSU at hpos
    obtain ⟨ε, hεrefl, hεblock⟩ := hpos
    let a0 : Fin n := ⟨0, by omega⟩
    let a1 : Fin n := ⟨1, by omega⟩
    have ha01 : a0 ≠ a1 := by
      intro h
      have := congrArg Fin.val h
      simp [a0, a1] at this
    let r : MulAut ↥Bs := ((ε (Equiv.swap a0 a1) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs)
    have hrA : r ∈ ggAutomizer L Bs := (ε (Equiv.swap a0 a1)).2
    have hrrefl : GGIsReflection p r := hεrefl a0 a1 ha01
    have hsix : Nat.card ↥(ggRankOneIn L Bs r) = 6 := by
      have hblk := hεblock a0 a1 ha01
      show Nat.card ↥(ggRankOneIn L Bs ((ε (Equiv.swap a0 a1) : ↥(ggAutomizer L Bs)) :
        MulAut ↥Bs)) = 6
      rw [hblk]
      exact card_ggSuPairBlock_map_zero_one (by omega) hcard h''.ker
    have hle3A : ∀ i j : Fin m, i ≠ j → (CoxeterMatrix.A m).M i j ≤ 3 := by
      intro i j hij
      simp only [CoxeterMatrix.A, Matrix.of_apply]
      split_ifs <;> omega
    have hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3 := by
      intro i j hij
      rw [hM, CoxeterMatrix.reindex_apply]
      exact hle3A _ _ (fun h => hij (σ.symm.injective h))
    have hrC : r ∈ ggCoxRefl M e :=
      ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres hle3
        (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl) hrA) hrrefl
    exact hno6 r hrA hrC hsix
  have h3 : 3 ∣ 2 ^ f + 1 := by simpa [hp3] using hdvd
  obtain ⟨g, hg, hgi⟩ := hc y hy
  have hJ' : IsComponentOf J ((ψ.comp (MulAut.conj c).toMonoidHom).range ⊓
      Subgroup.centralizer ({y} : Set G)) := by rwa [hrange']
  obtain ⟨a, ha2, -, -, -, hiso⟩ :=
    exists_isComponent_block_iso hcard Nat.prime_three h3 h''.ker hg hgi hJ'
  exact ⟨K, hKf, hKfin, hKchar, f, a, hcard, hf2, h3, ha2, hiso⟩

end CFSG.StandardType

end
