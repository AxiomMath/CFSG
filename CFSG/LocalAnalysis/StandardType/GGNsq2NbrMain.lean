module

import Lean
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSQ2CellsDefs
public import CFSG.LocalAnalysis.StandardType.GGNsq2NbrX
public import CFSG.LocalAnalysis.StandardType.GGNsq2NbrL
public import CFSG.LocalAnalysis.StandardType.GGNsq2NbrOrd
import CFSG.LocalAnalysis.StandardType.GGNbrBalance
import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEsu
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrEnnola
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieEsuAux
import CFSG.ClassicalGroups.Unitary.Finite

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggNsq2Nbr_of_cov
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    {m : ℕ} {σ : Fin m ≃ ι} (hM : M = (CoxeterMatrix.A m).reindex σ)
    (hno6 : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6)
    (hcov : GGInnerDiagOnLabel (fun p lab => ggRowP_ESU p lab ∧
      ¬ (lab.n = 1 ∧ (lab.rank = 3 ∨ lab.rank = 5))) p Bs L)
    {X : Subgroup G} (hXnb : (∃ y : G, GGNbr p B x D J y X) ∧ ggAutomizer X Bs ≤ ggAutomizerJoin L Bs 𝒦)
    (hmark : GGInnerDiagOnLabel
      (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ (lab.rank = 3 ∨ lab.rank = 5)) p Bs X) : False := by
  classical
  obtain ⟨⟨y, hnbr⟩, -⟩ := hXnb
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hf, hfin, lab, m', θ, hK, h4m, hmrank, hSide, hdvd, hperf, hlab, hBsN, hbs⟩ :=
    ggNSLieN3A_esuCore hmark (fun p lab hl => hl.1)
  haveI : CharP K 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := lab.n) hK
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨-, hn1, hr35⟩ := hSide
  change n = 1 at hn1
  change m' = rank + 1 at hmrank
  subst hn1
  have hn : m' = 4 ∨ m' = 6 := by
    rcases hr35 with h | h
    · left
      have h' : rank = 3 := h
      omega
    · right
      have h' : rank = 5 := h
      omega
  obtain ⟨hp, -⟩ := ggRouteCfg_prime hcfg
  have hp3 : p = 3 := by
    have h3 : p ∣ 3 := by simpa using hdvd
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3
  have hconf : GGConfig p B Bs x L D J := hcfg.1.1
  have hpJ : p ∣ Nat.card J := hP G p B x L D J hconf.1 hconf.2.2
  have hJX : J ≤ X := le_of_ggNbr hLB hconf.1 hconf.2.2 hpJ hnbr
  have hcomp : IsComponentOf J (X ⊓ Subgroup.centralizer ({x} : Set G)) :=
    ggIsComponentOf_inf_centralizer_nbr hconf hnbr hJX
  have hSS : LargeEvenSStar p B x L := hconf.1.2.2.2.2.2.2.1
  have hDy : D = Subgroup.closure {x, y} := hnbr.2.1
  have hL : IsComponentOf L (Subgroup.centralizer ({x} : Set G)) := hSS.2.2.2.1
  have hJc : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) := hconf.2.2.1.2.2.2.2.2.1
  have hCD : Subgroup.centralizer (D : Set G) =
      Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G) := by
    rw [hDy, Subgroup.centralizer_closure]
    ext g
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  have hLD : L ⊓ Subgroup.centralizer (D : Set G) = L ⊓ Subgroup.centralizer ({y} : Set G) := by
    rw [hCD, ← inf_assoc, inf_eq_left.mpr hL.1]
  rw [hLD] at hJc
  have hy : y ∈ Bs := hconf.2.1.1 hnbr.1.2.1
  obtain ⟨-, a, ha4, ha5, ⟨e₁⟩⟩ := ggNsq2Nbr_X hcfg hnbr hK hdvd hn θ hperf hBsN hbs hcomp
  obtain ⟨K', hK'f, hK'fin, hK'c, f', a', hK', hf', h3', ha', ⟨e₂⟩⟩ :=
    ggNsq2Nbr_L_of_cov hcfg hpres hM hno6 hcov hp3 hy hJc
  letI : Field K' := hK'f
  letI : Finite K' := hK'fin
  letI : CharP K' 2 := hK'c
  exact not_nonempty_su_quot_equiv hK' hK h3' hf' ha' (by omega) ⟨e₂.symm.trans e₁⟩


theorem ggSecFiveNSQ2NbrInput_of_ennola
    (hEn : GGSecFiveNSEnnolaInput) (hL2 : GGSecFiveNSQ2LInput) : GGSecFiveNSQ2NbrInput := by
  intro hTB hWA hLB hP G _ _ p B Bs x L D J 𝒦 hcfg hns ι M e hpres hA hno6 X hXnb _ hmark
  obtain ⟨m, σ, hm5, hM⟩ := hA
  exact ggNsq2Nbr_of_cov hLB hP hcfg hpres hM hno6
    (ggNsq2Cov_of_esu hcfg.1.1 (ggX_esu_of_nonSplit hEn hcfg hns hpres ⟨m, σ, hm5, hM⟩ (Or.inl rfl) hns)
      (hL2 hTB hWA hLB hP G p B Bs x L D J 𝒦 hcfg hns ι M e hpres ⟨m, σ, hm5, hM⟩ hno6)) hXnb hmark

end CFSG.StandardType

end
