module

public import CFSG.LocalAnalysis.StandardType.GGExcReflTBWeylDatumOfWeyl
public import CFSG.LocalAnalysis.StandardType.GGKGPosTagWeyl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosDefs
public import CFSG.LocalAnalysis.StandardType.GGTBRowSpan
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwenty
import CFSG.LocalAnalysis.StandardType.GGWeylSimpleSystemsConj
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLFaithful
import CFSG.LocalAnalysis.StandardType.GGSecFiveRootRefl
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut
import CFSG.LocalAnalysis.StandardType.GGTableBBstar
import CFSG.LocalAnalysis.StandardType.GGRootInvolutionRank
import CFSG.LocalAnalysis.StandardType.GGResE6DepRank
import CFSG.LieType.Chevalley.WeylRoots
import TauCeti.LinearAlgebra.Matrix.Cartan.Classical
import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.RootSystem

section Tree

open CFSG.StandardType.SecFiveRootRefl

private theorem ggR1Da_key {ι : Type} {M : CoxeterMatrix ι} {n : ℕ} (e : Fin n ≃ ι)
    (M₀ : CoxeterMatrix (Fin n)) (C₀ : Matrix (Fin n) (Fin n) ℤ) (hMe : M = M₀.reindex e)
    (hC₀ : GGIntCartan M₀ C₀) (hT : CartanTree C₀) :
    ∃ C : Matrix ι ι ℤ, GGIntCartan M C ∧ CartanTree C :=
  ⟨Matrix.reindex e e C₀, hMe ▸ hC₀.reindex e, hT.reindex e⟩

theorem ggR1Da_exists_cartanTree {ι : Type} {M : CoxeterMatrix ι}
    (hM : GGIsWeylMatrix M) : ∃ C : Matrix ι ι ℤ, GGIntCartan M C ∧ CartanTree C := by
  rcases hM with ⟨n, e, hn, hMA | ⟨hn2, hMB⟩ | ⟨hn4, hMD⟩⟩ | ⟨e, hE6⟩ | ⟨e, hE7⟩ | ⟨e, hE8⟩ |
    ⟨e, hF4⟩ | ⟨e, hMG⟩
  · exact ggR1Da_key e _ _ hMA (ggIntCartan_A n) (cartanTree_A n hn)
  · exact ggR1Da_key e _ _ hMB (ggIntCartan_B n) (cartanTree_B n (by omega))
  · exact ggR1Da_key e _ _ hMD (ggIntCartan_D n) (cartanTree_D n hn4)
  · exact ggR1Da_key e _ _ hE6 ggIntCartan_E₆ (cartanTree_E 6 (by norm_num))
  · exact ggR1Da_key e _ _ hE7 ggIntCartan_E₇ (cartanTree_E 7 (by norm_num))
  · exact ggR1Da_key e _ _ hE8 ggIntCartan_E₈ (cartanTree_E 8 (by norm_num))
  · exact ggR1Da_key e _ _ hF4 ggIntCartan_F₄ cartanTree_F₄
  · exact ggR1Da_key e _ _ hMG ggIntCartan_G₂ S2MathFi1451.cartanTree_G₂

end Tree

private theorem ggR1Da_reindex_refl {ι : Type} (M : CoxeterMatrix ι) :
    M = M.reindex (Equiv.refl ι) := by
  apply CoxeterMatrix.ext
  ext i j
  rw [CoxeterMatrix.reindex_apply]
  simp

theorem ggR1_datum_of_tableBPos
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hHyp : GGCorFiveTwentyHyp p B Bs x L D J) {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* G}
    (ht : t = .PSL ∨ t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8)
    (hadm : StatedLieAdmissible t n 2 f) (h3 : 3 ≤ bnRank t n)
    (hpos : GGTableBPos p Bs L t n f ψ)
    (hdet : ∀ C : Matrix (Fin (ggU t n f).D.rank) (Fin (ggU t n f).D.rank) ℤ,
      GGIntCartan (coxeterMatrix (ggU t n f).D.isFiniteType) C → ((C.det : ℤ) : ZMod p) ≠ 0) :
    Nonempty (GGExcReflTBWeylDatum p Bs L J) := by
  classical
  obtain ⟨hMW, hlab⟩ := ggTag_weylMatrix ht hadm
  obtain ⟨C, hC, par, root, depth, hpar, hdepth⟩ := ggR1Da_exists_cartanTree hMW
  have hno6 : ∀ i j, (coxeterMatrix (ggU t n f).D.isFiniteType) i j ≠ 6 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [CoxeterMatrix.diagonal]
      norm_num
    · have := hlab i j hij
      omega
  have hcfg : GGConfig p B Bs x L D J := hHyp.1
  obtain ⟨hp, hBs, hxBs, hLx, -⟩ := hcfg.tableB_facts
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hNT : GGNoTransvection p Bs := hHyp.2.2.2.1
  obtain ⟨V, _, _, ⟨ιV⟩⟩ := exists_ggLinData (p := p) hBs
  obtain ⟨ε, hε, -, hcard⟩ := hpos
  have hW : GGWeylOfType p (coxeterMatrix (ggU t n f).D.isFiniteType) (ggAutomizer L Bs) :=
    ⟨ε, hε⟩
  have hspan := ggReflSpan_card_le_finrank_of_weylOfType hp2 hNT hC hno6 par root depth hpar
    hdepth (hdet C hC) hW ιV
  have hrank : (ggU t n f).D.rank = bnRank t n :=
    lieUniversal_rank_eq_bnRank t n 2 f Nat.prime_two hadm h3
  have hcardC : Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) = p := by
    rw [inf_centralizer_eq_zpowers_of_elemAbelian hp hBs hxBs hS.2.2.1 hLx hS.2.2.2.2,
      Nat.card_zpowers, orderOf_eq_prime (hBs.2 x hxBs) hS.2.2.1]
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ιV.toEquiv
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hcardV : Nat.card ↥Bs = p ^ Module.finrank (ZMod p) V := by
    rw [card_eq_of_ggLin ιV, Module.natCard_eq_pow_finrank (K := ZMod p) (V := V),
      Nat.card_zmod]
  have hpow : p ^ Module.finrank (ZMod p) V ≤ p ^ ((ggU t n f).D.rank + 1) := by
    rw [← hcardV, pow_succ]
    calc Nat.card ↥Bs
        ≤ p ^ (ggU t n f).D.rank * Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) := hcard
      _ = p ^ (ggU t n f).D.rank * p := by rw [hcardC]
  have hV : Module.finrank (ZMod p) V ≤ (ggU t n f).D.rank + 1 :=
    (Nat.pow_le_pow_iff_right hp.one_lt).mp hpow
  have hspan' : (ggU t n f).D.rank ≤
      Module.finrank (ZMod p) (ggReflSpan (p := p) Bs L ιV) := by
    simpa using hspan
  have h3' : 3 ≤ Fintype.card (Fin (ggU t n f).D.rank) := by
    rw [Fintype.card_fin, hrank]
    exact h3
  exact ggExcReflTBWeylDatum_of_weylOfType hp2 hNT hMW h3' hC hno6 par root depth hpar hdepth hW
    ιV (Or.inl (by omega))

theorem ggR1E8_det
    {p : ℕ} [Fact p.Prime] {n f : ℕ} (hadm : StatedLieAdmissible .E8 n 2 f) :
    ∀ C : Matrix (Fin (ggU .E8 n f).D.rank) (Fin (ggU .E8 n f).D.rank) ℤ,
      GGIntCartan (coxeterMatrix (ggU .E8 n f).D.isFiniteType) C → ((C.det : ℤ) : ZMod p) ≠ 0 := by
  change ∀ C : Matrix (Fin 8) (Fin 8) ℤ,
    GGIntCartan (coxeterMatrix (CFSG.LieType.Chevalley.isFiniteType_cartan .E8)) C →
      ((C.det : ℤ) : ZMod p) ≠ 0
  intro C hC
  have h1 : GGIntCartan CoxeterMatrix.E₈ (CartanMatrix.E 8) := ggIntCartan_E₈
  have hM : coxeterMatrix (CFSG.LieType.Chevalley.isFiniteType_cartan .E8) =
      CoxeterMatrix.E₈ := by
    refine coxeterMatrix_eq_of_ggIntCartan (CFSG.LieType.Chevalley.isFiniteType_cartan .E8) ?_
    rw [show CFSG.Blueprint.Chevalley.Tag.cartan .E8 = CartanMatrix.E 8 from
      CFSG.LieType.Chevalley.cartanE_eq 8]
    exact h1
  rw [hM] at hC
  have hle : ∀ i j : Fin 8, i ≠ j → CoxeterMatrix.E₈ i j ≤ 3 := fun i j hij =>
    GGIsWeylMatrixE.le_three (M := CoxeterMatrix.E₈)
      (Or.inr (Or.inr ⟨Equiv.refl _, ggR1Da_reindex_refl _⟩)) i j hij
  have hCE : C = CartanMatrix.E 8 := GGIntCartan.eq_of_le_three hC h1 hle
  subst hCE
  rw [CartanMatrix.E_det (by norm_num : 3 ≤ 8), show (9 : ℤ) - ((8 : ℕ) : ℤ) = 1 by norm_num]
  simp

end CFSG.StandardType

end
